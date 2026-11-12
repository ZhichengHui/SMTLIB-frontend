//! Processing of SMT-LIB 2.6 scripts in the logics QF_UF, QF_BV and QF_UFBV: commands, name
//! resolution and sort checking, building an [`SmtProblem`], and printing the responses.
//!
//! Responses follow Section 4.1 and 4.2 of the reference: `success` only when `:print-success`
//! is true; `unsupported` for a command or input the front end does not handle; `(error "...")`
//! for an error, after which the script stops (`:error-behavior` `immediate-exit`). A command
//! whose omission would change the meaning of the rest of the script (for example `push`, or an
//! assertion with a quantifier) makes every later `check-sat` answer `unknown`.

use std::collections::HashMap;
use std::io::{self, Write};

use crate::lexer::{Token, is_simple_symbol};
use crate::problem::*;
use crate::sexp::{Sexp, read};

/// A sort, as the front end handles it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Sort {
    Bool,
    Bv(usize),
    U(usize),
}

impl Sort {
    pub fn to_smt(self) -> SmtSort {
        match self {
            Sort::Bool => SmtSort::Bool,
            Sort::Bv(w) => SmtSort::BitVec(w),
            Sort::U(i) => SmtSort::Uninterpreted(i),
        }
    }
}

enum Fail {
    Error(String),
    Unsupported,
}

type R<T> = Result<T, Fail>;

fn err<T>(m: impl Into<String>) -> R<T> {
    Err(Fail::Error(m.into()))
}

#[derive(Clone, Copy)]
enum Global {
    Fun(usize),
    Def(usize),
}

#[derive(Clone, Copy)]
enum Local {
    Param(usize, Sort),
    Let(usize, Sort),
}

/// The variables in scope: the parameters of the enclosing definition (all of them, in order)
/// and the bound names, innermost last.
struct Scope {
    params: Vec<Sort>,
    locals: Vec<(Vec<u8>, Local)>,
}

impl Scope {
    fn top() -> Self {
        Scope { params: Vec::new(), locals: Vec::new() }
    }

    fn param_terms(&self) -> Vec<SmtTerm> {
        (0..self.params.len()).map(SmtTerm::Param).collect()
    }
}

enum Resp {
    Success,
    Text(Vec<u8>),
    Exit,
}

/// The theory symbols of Core and of FixedSizeBitVectors/QF_BV; users may not declare them.
const THEORY_SYMBOLS: &[&str] = &[
    "true", "false", "not", "and", "or", "xor", "=>", "=", "distinct", "ite", "concat", "extract",
    "bvnot", "bvand", "bvor", "bvneg", "bvadd", "bvmul", "bvudiv", "bvurem", "bvshl", "bvlshr",
    "bvult", "bvnand", "bvnor", "bvxor", "bvxnor", "bvcomp", "bvsub", "bvsdiv", "bvsrem", "bvsmod",
    "bvashr", "repeat", "zero_extend", "sign_extend", "rotate_left", "rotate_right", "bvule",
    "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
];

pub struct Session<'a> {
    solve: &'a mut dyn FnMut(&SmtProblem) -> SmtAnswer,
    print_success: bool,
    logic_set: bool,
    uf: bool,
    bv: bool,
    sort_names: Vec<Vec<u8>>,
    sorts: HashMap<Vec<u8>, Sort>,
    globals: HashMap<Vec<u8>, Global>,
    fun_names: Vec<Vec<u8>>,
    fun_sigs: Vec<(Vec<Sort>, Sort)>,
    def_sigs: Vec<(Vec<Sort>, Sort)>,
    problem: SmtProblem,
    tainted: bool,
    model: Option<SmtModel>,
}

/// Runs the script `src`, calling `solve` at every `check-sat`, and writes the responses to `out`.
pub fn run(src: &[u8], solve: &mut dyn FnMut(&SmtProblem) -> SmtAnswer, out: &mut dyn Write) -> io::Result<()> {
    let cmds = match read(src) {
        Ok(c) => c,
        Err(e) => {
            out.write_all(&error_response(&e.message))?;
            return Ok(());
        }
    };
    let mut s = Session::new(solve);
    for c in &cmds {
        match s.command(c) {
            Ok(Resp::Success) => {
                if s.print_success {
                    out.write_all(b"success\n")?;
                }
            }
            Ok(Resp::Text(t)) => {
                out.write_all(&t)?;
                out.write_all(b"\n")?;
            }
            Ok(Resp::Exit) => break,
            Err(Fail::Unsupported) => out.write_all(b"unsupported\n")?,
            Err(Fail::Error(m)) => {
                if s.tainted {
                    // After an unsupported command, an error may come from what was skipped.
                    out.write_all(b"unsupported\n")?;
                } else {
                    out.write_all(&error_response(&m))?;
                    break;
                }
            }
        }
        out.flush()?;
    }
    out.flush()
}

fn error_response(m: &str) -> Vec<u8> {
    format!("(error \"{}\")\n", m.replace('"', "\"\"")).into_bytes()
}

fn shown(s: &Sexp) -> String {
    match s {
        Sexp::Atom(_, Token::Symbol(b)) => String::from_utf8_lossy(b).into_owned(),
        Sexp::Atom(_, t) => format!("{:?}", t),
        Sexp::List(o, _) => format!("the list at byte {}", o),
    }
}

fn symbol(s: &Sexp) -> R<Vec<u8>> {
    match s {
        Sexp::Atom(_, Token::Symbol(b)) => Ok(b.clone()),
        _ => err(format!("expected a symbol, got {}", shown(s))),
    }
}

fn numeral(s: &Sexp) -> R<usize> {
    match s {
        Sexp::Atom(_, Token::Numeral(d)) => d.parse().or_else(|_| err(format!("numeral {} is too large", d))),
        _ => err(format!("expected a numeral, got {}", shown(s))),
    }
}

fn list(s: &Sexp) -> R<&[Sexp]> {
    match s {
        Sexp::List(_, l) => Ok(l),
        _ => err(format!("expected a list, got {}", shown(s))),
    }
}

fn is_reserved(s: &Sexp, r: &str) -> bool {
    matches!(s, Sexp::Atom(_, Token::Reserved(x)) if *x == r)
}

fn arity(a: &[Sexp], n: usize, what: &str) -> R<()> {
    if a.len() == n { Ok(()) } else { err(format!("{} takes {} arguments", what, n)) }
}

fn checked(x: Option<usize>) -> R<usize> {
    x.ok_or_else(|| Fail::Error("width too large".into()))
}

/// The bits of a decimal numeral modulo `2^w`, least significant first.
fn decimal_bits(digits: &str, w: usize) -> Vec<bool> {
    let mut ds: Vec<u32> = digits.bytes().map(|c| (c - b'0') as u32).collect();
    let mut bits = Vec::with_capacity(w);
    for _ in 0..w {
        let mut rem = 0;
        for d in ds.iter_mut() {
            let cur = rem * 10 + *d;
            *d = cur / 2;
            rem = cur % 2;
        }
        bits.push(rem == 1);
    }
    bits
}

pub fn write_symbol(out: &mut Vec<u8>, name: &[u8]) {
    if is_simple_symbol(name) {
        out.extend_from_slice(name);
    } else {
        out.push(b'|');
        out.extend_from_slice(name);
        out.push(b'|');
    }
}

impl<'a> Session<'a> {
    fn new(solve: &'a mut dyn FnMut(&SmtProblem) -> SmtAnswer) -> Self {
        Session {
            solve,
            print_success: false,
            logic_set: false,
            uf: true,
            bv: true,
            sort_names: Vec::new(),
            sorts: HashMap::new(),
            globals: HashMap::new(),
            fun_names: Vec::new(),
            fun_sigs: Vec::new(),
            def_sigs: Vec::new(),
            problem: SmtProblem { num_sorts: 0, funs: Vec::new(), defs: Vec::new(), asserts: Vec::new() },
            tainted: false,
            model: None,
        }
    }

    fn unsupported<T>(&mut self, changes_state: bool) -> R<T> {
        if changes_state {
            self.tainted = true;
        }
        Err(Fail::Unsupported)
    }

    fn fresh(&self, name: &[u8]) -> R<()> {
        if self.globals.contains_key(name) || THEORY_SYMBOLS.iter().any(|t| t.as_bytes() == name) {
            return err(format!("symbol {} is already declared", String::from_utf8_lossy(name)));
        }
        Ok(())
    }

    fn command(&mut self, c: &Sexp) -> R<Resp> {
        let items = match c {
            Sexp::List(_, it) if !it.is_empty() => it,
            _ => return err(format!("expected a command, got {}", shown(c))),
        };
        let name = match &items[0] {
            Sexp::Atom(_, Token::Reserved(r)) => *r,
            _ => return err(format!("expected a command name, got {}", shown(&items[0]))),
        };
        let a = &items[1..];
        match name {
            "set-logic" => {
                arity(a, 1, name)?;
                if self.logic_set {
                    return err("the logic is already set");
                }
                let l = symbol(&a[0])?;
                let (uf, bv) = match l.as_slice() {
                    b"QF_UF" => (true, false),
                    b"QF_BV" => (false, true),
                    b"QF_UFBV" => (true, true),
                    _ => return self.unsupported(true),
                };
                self.logic_set = true;
                self.uf = uf;
                self.bv = bv;
                Ok(Resp::Success)
            }
            "set-option" => {
                let kw = match a.first() {
                    Some(Sexp::Atom(_, Token::Keyword(k))) => k.as_str(),
                    _ => return err("set-option takes an option"),
                };
                let flag = |v: Option<&Sexp>| match v {
                    Some(Sexp::Atom(_, Token::Symbol(b))) if b == b"true" => Ok(true),
                    Some(Sexp::Atom(_, Token::Symbol(b))) if b == b"false" => Ok(false),
                    _ => err(format!(":{} takes true or false", kw)),
                };
                match kw {
                    "print-success" => {
                        self.print_success = flag(a.get(1))?;
                        Ok(Resp::Success)
                    }
                    "produce-models" => {
                        flag(a.get(1))?;
                        Ok(Resp::Success)
                    }
                    _ => self.unsupported(false),
                }
            }
            "set-info" => Ok(Resp::Success),
            "declare-sort" => {
                arity(a, 2, name)?;
                if !self.uf {
                    return err("declare-sort is not in the logic");
                }
                let n = symbol(&a[0])?;
                if numeral(&a[1])? != 0 {
                    return self.unsupported(true);
                }
                if self.sorts.contains_key(&n) || n == b"Bool" {
                    return err("the sort is already declared");
                }
                let i = self.sort_names.len();
                self.sort_names.push(n.clone());
                self.sorts.insert(n, Sort::U(i));
                self.problem.num_sorts = self.sort_names.len();
                self.model = None;
                Ok(Resp::Success)
            }
            "define-sort" => {
                arity(a, 3, name)?;
                let n = symbol(&a[0])?;
                if !list(&a[1])?.is_empty() {
                    return self.unsupported(true);
                }
                if self.sorts.contains_key(&n) || n == b"Bool" {
                    return err("the sort is already declared");
                }
                let s = self.sort(&a[2])?;
                self.sorts.insert(n, s);
                Ok(Resp::Success)
            }
            "declare-const" => {
                arity(a, 2, name)?;
                let n = symbol(&a[0])?;
                let s = self.sort(&a[1])?;
                self.declare(n, Vec::new(), s)?;
                Ok(Resp::Success)
            }
            "declare-fun" => {
                arity(a, 3, name)?;
                let n = symbol(&a[0])?;
                let args = list(&a[1])?.iter().map(|s| self.sort(s)).collect::<R<Vec<_>>>()?;
                if !args.is_empty() && !self.uf {
                    return err("function symbols with arguments are not in the logic");
                }
                let s = self.sort(&a[2])?;
                self.declare(n, args, s)?;
                Ok(Resp::Success)
            }
            "define-fun" => {
                arity(a, 4, name)?;
                let n = symbol(&a[0])?;
                self.fresh(&n)?;
                let mut sc = Scope::top();
                for (k, p) in list(&a[1])?.iter().enumerate() {
                    let pv = list(p)?;
                    if pv.len() != 2 {
                        return err("a parameter is (symbol sort)");
                    }
                    let pn = symbol(&pv[0])?;
                    if sc.locals.iter().any(|(x, _)| *x == pn) {
                        return err("repeated parameter");
                    }
                    let ps = self.sort(&pv[1])?;
                    sc.params.push(ps);
                    sc.locals.push((pn, Local::Param(k, ps)));
                }
                let ret = self.sort(&a[2])?;
                let (body, bs) = self.term_or_taint(&mut sc, &a[3])?;
                if bs != ret {
                    return err("the body of the definition has the wrong sort");
                }
                let d = self.push_def(sc.params.clone(), ret, body);
                self.globals.insert(n, Global::Def(d));
                self.model = None;
                Ok(Resp::Success)
            }
            "assert" => {
                arity(a, 1, name)?;
                let mut sc = Scope::top();
                let (t, s) = self.term_or_taint(&mut sc, &a[0])?;
                if s != Sort::Bool {
                    return err("an assertion must be Boolean");
                }
                self.problem.asserts.push(t);
                self.model = None;
                Ok(Resp::Success)
            }
            "check-sat" => {
                arity(a, 0, name)?;
                self.model = None;
                if self.tainted {
                    return Ok(Resp::Text(b"unknown".to_vec()));
                }
                let r = match (self.solve)(&self.problem) {
                    SmtAnswer::Sat(m) => {
                        self.model = Some(m);
                        "sat"
                    }
                    SmtAnswer::Unsat => "unsat",
                    SmtAnswer::Unknown => "unknown",
                };
                Ok(Resp::Text(r.as_bytes().to_vec()))
            }
            "get-model" => {
                arity(a, 0, name)?;
                match &self.model {
                    Some(m) => match self.print_model(m) {
                        Ok(t) => Ok(Resp::Text(t)),
                        Err(e) => err(e),
                    },
                    None => err("no model is available"),
                }
            }
            "echo" => {
                arity(a, 1, name)?;
                match &a[0] {
                    Sexp::Atom(_, Token::String(s)) => {
                        let mut t = vec![b'"'];
                        for &c in s {
                            if c == b'"' {
                                t.push(b'"');
                            }
                            t.push(c);
                        }
                        t.push(b'"');
                        Ok(Resp::Text(t))
                    }
                    _ => err("echo takes a string"),
                }
            }
            "exit" => Ok(Resp::Exit),
            "push" | "pop" | "reset" | "reset-assertions" | "check-sat-assuming" | "define-fun-rec"
            | "define-funs-rec" | "declare-datatype" | "declare-datatypes" => self.unsupported(true),
            _ => self.unsupported(false),
        }
    }

    fn term_or_taint(&mut self, sc: &mut Scope, s: &Sexp) -> R<(SmtTerm, Sort)> {
        match self.term(sc, s) {
            Err(Fail::Unsupported) => self.unsupported(true),
            r => r,
        }
    }

    fn declare(&mut self, n: Vec<u8>, args: Vec<Sort>, ret: Sort) -> R<()> {
        self.fresh(&n)?;
        let i = self.fun_names.len();
        self.problem.funs.push(SmtFun { args: args.iter().map(|s| s.to_smt()).collect(), ret: ret.to_smt() });
        self.fun_sigs.push((args, ret));
        self.fun_names.push(n.clone());
        self.globals.insert(n, Global::Fun(i));
        self.model = None;
        Ok(())
    }

    fn push_def(&mut self, params: Vec<Sort>, ret: Sort, body: SmtTerm) -> usize {
        let d = self.problem.defs.len();
        self.problem.defs.push(SmtDef { params: params.iter().map(|s| s.to_smt()).collect(), ret: ret.to_smt(), body });
        self.def_sigs.push((params, ret));
        d
    }

    fn sort(&self, s: &Sexp) -> R<Sort> {
        match s {
            Sexp::Atom(_, Token::Symbol(b)) if b == b"Bool" => Ok(Sort::Bool),
            Sexp::Atom(_, Token::Symbol(b)) => match self.sorts.get(b) {
                Some(s) => Ok(*s),
                None => err(format!("unknown sort {}", String::from_utf8_lossy(b))),
            },
            Sexp::List(_, l) if l.len() == 3 && is_reserved(&l[0], "_") && symbol(&l[1]).ok().as_deref() == Some(b"BitVec") => {
                if !self.bv {
                    return err("bit-vector sorts are not in the logic");
                }
                let w = numeral(&l[2])?;
                if w == 0 {
                    return err("a bit-vector width must be at least 1");
                }
                Ok(Sort::Bv(w))
            }
            _ => err(format!("unknown sort {}", shown(s))),
        }
    }

    fn term(&mut self, sc: &mut Scope, s: &Sexp) -> R<(SmtTerm, Sort)> {
        match s {
            Sexp::Atom(_, Token::Binary(d)) => {
                if !self.bv {
                    return err("bit-vector constants are not in the logic");
                }
                let bits: Vec<bool> = d.bytes().rev().map(|c| c == b'1').collect();
                let w = bits.len();
                Ok((SmtTerm::BvConst(bits), Sort::Bv(w)))
            }
            Sexp::Atom(_, Token::Hexadecimal(d)) => {
                if !self.bv {
                    return err("bit-vector constants are not in the logic");
                }
                let mut bits = Vec::new();
                for c in d.chars().rev() {
                    let v = c.to_digit(16).expect("checked by the lexer");
                    for k in 0..4 {
                        bits.push((v >> k) & 1 == 1);
                    }
                }
                let w = bits.len();
                Ok((SmtTerm::BvConst(bits), Sort::Bv(w)))
            }
            Sexp::Atom(_, Token::Symbol(n)) => {
                if let Some(t) = self.local(sc, n) {
                    return Ok(t);
                }
                self.apply_symbol(n, Vec::new())
            }
            Sexp::Atom(..) => err(format!("unexpected {}", shown(s))),
            Sexp::List(_, l) if l.is_empty() => err("empty term"),
            Sexp::List(_, l) => {
                if is_reserved(&l[0], "_") {
                    return self.indexed_constant(l);
                }
                if is_reserved(&l[0], "as") {
                    if l.len() != 3 {
                        return err("as takes an identifier and a sort");
                    }
                    let (t, ts) = self.term(sc, &l[1])?;
                    if ts != self.sort(&l[2])? {
                        return err("the sort in as does not match");
                    }
                    return Ok((t, ts));
                }
                if is_reserved(&l[0], "let") {
                    return self.let_term(sc, l);
                }
                if is_reserved(&l[0], "!") {
                    return self.annotated(sc, l);
                }
                if is_reserved(&l[0], "forall") || is_reserved(&l[0], "exists") || is_reserved(&l[0], "match") {
                    return Err(Fail::Unsupported);
                }
                if l.len() < 2 {
                    return err("an application needs arguments");
                }
                let mut args = Vec::with_capacity(l.len() - 1);
                for x in &l[1..] {
                    args.push(self.term(sc, x)?);
                }
                match &l[0] {
                    Sexp::Atom(_, Token::Symbol(f)) => {
                        if self.local(sc, f).is_some() {
                            return err("a variable cannot be applied");
                        }
                        self.apply_symbol(f, args)
                    }
                    Sexp::List(_, h) if h.len() >= 3 && is_reserved(&h[0], "_") => self.apply_indexed(h, args),
                    Sexp::List(_, h) if h.len() == 3 && is_reserved(&h[0], "as") => {
                        let f = symbol(&h[1])?;
                        let (t, ts) = self.apply_symbol(&f, args)?;
                        if ts != self.sort(&h[2])? {
                            return err("the sort in as does not match");
                        }
                        Ok((t, ts))
                    }
                    h => err(format!("unexpected function {}", shown(h))),
                }
            }
        }
    }

    fn local(&self, sc: &Scope, n: &[u8]) -> Option<(SmtTerm, Sort)> {
        for (x, l) in sc.locals.iter().rev() {
            if x == n {
                return Some(match *l {
                    Local::Param(k, s) => (SmtTerm::Param(k), s),
                    Local::Let(d, s) => (SmtTerm::Def(d, sc.param_terms()), s),
                });
            }
        }
        None
    }

    fn let_term(&mut self, sc: &mut Scope, l: &[Sexp]) -> R<(SmtTerm, Sort)> {
        if l.len() != 3 {
            return err("let takes bindings and a term");
        }
        let binds = list(&l[1])?;
        if binds.is_empty() {
            return err("let needs a binding");
        }
        // The bindings are parallel: every bound term is in the outer scope.
        let mut new = Vec::with_capacity(binds.len());
        for b in binds {
            let bv = list(b)?;
            if bv.len() != 2 {
                return err("a binding is (symbol term)");
            }
            let n = symbol(&bv[0])?;
            if new.iter().any(|(x, _): &(Vec<u8>, Local)| *x == n) {
                return err("repeated variable in let");
            }
            let (t, s) = self.term(sc, &bv[1])?;
            let d = self.push_def(sc.params.clone(), s, t);
            new.push((n, Local::Let(d, s)));
        }
        let depth = sc.locals.len();
        sc.locals.extend(new);
        let r = self.term(sc, &l[2]);
        sc.locals.truncate(depth);
        r
    }

    fn annotated(&mut self, sc: &mut Scope, l: &[Sexp]) -> R<(SmtTerm, Sort)> {
        if l.len() < 3 {
            return err("! takes a term and attributes");
        }
        let (mut t, s) = self.term(sc, &l[1])?;
        let mut i = 2;
        while i < l.len() {
            let kw = match &l[i] {
                Sexp::Atom(_, Token::Keyword(k)) => k.clone(),
                x => return err(format!("expected an attribute, got {}", shown(x))),
            };
            i += 1;
            let value = if i < l.len() && !matches!(l[i], Sexp::Atom(_, Token::Keyword(_))) {
                i += 1;
                Some(&l[i - 1])
            } else {
                None
            };
            if kw == "named" {
                let n = symbol(value.ok_or_else(|| Fail::Error(":named takes a symbol".into()))?)?;
                if !sc.locals.is_empty() {
                    return err("a named term must be closed");
                }
                self.fresh(&n)?;
                let d = self.push_def(Vec::new(), s, t);
                self.globals.insert(n, Global::Def(d));
                t = SmtTerm::Def(d, Vec::new());
            }
        }
        Ok((t, s))
    }

    fn indexed_constant(&self, l: &[Sexp]) -> R<(SmtTerm, Sort)> {
        if let (3, Ok(f)) = (l.len(), symbol(&l[1])) {
            if let Some(d) = f.strip_prefix(b"bv") {
                if self.bv && !d.is_empty() && d.iter().all(u8::is_ascii_digit) {
                    let w = numeral(&l[2])?;
                    if w == 0 {
                        return err("a bit-vector width must be at least 1");
                    }
                    let digits = String::from_utf8(d.to_vec()).expect("digits");
                    return Ok((SmtTerm::BvConst(decimal_bits(&digits, w)), Sort::Bv(w)));
                }
            }
        }
        err("unknown indexed constant")
    }

    fn apply_symbol(&mut self, f: &[u8], args: Vec<(SmtTerm, Sort)>) -> R<(SmtTerm, Sort)> {
        if let Some(g) = self.globals.get(f).copied() {
            let (sig, ret, mk): (&Vec<Sort>, Sort, fn(usize, Vec<SmtTerm>) -> SmtTerm) = match g {
                Global::Fun(i) => (&self.fun_sigs[i].0, self.fun_sigs[i].1, SmtTerm::Fun),
                Global::Def(d) => (&self.def_sigs[d].0, self.def_sigs[d].1, SmtTerm::Def),
            };
            if sig.len() != args.len() || sig.iter().zip(&args).any(|(a, b)| *a != b.1) {
                return err(format!("ill-sorted application of {}", String::from_utf8_lossy(f)));
            }
            let idx = match g {
                Global::Fun(i) | Global::Def(i) => i,
            };
            return Ok((mk(idx, args.into_iter().map(|a| a.0).collect()), ret));
        }
        let name = std::str::from_utf8(f).unwrap_or("");
        let sorts: Vec<Sort> = args.iter().map(|a| a.1).collect();
        let n = sorts.len();
        let all_bool = sorts.iter().all(|s| *s == Sort::Bool);
        let same = sorts.windows(2).all(|p| p[0] == p[1]);
        let core = match name {
            "true" if n == 0 => return Ok((SmtTerm::BoolConst(true), Sort::Bool)),
            "false" if n == 0 => return Ok((SmtTerm::BoolConst(false), Sort::Bool)),
            "not" => Some((SmtOp::Not, n == 1 && all_bool, Sort::Bool)),
            "and" => Some((SmtOp::And, n >= 2 && all_bool, Sort::Bool)),
            "or" => Some((SmtOp::Or, n >= 2 && all_bool, Sort::Bool)),
            "xor" => Some((SmtOp::Xor, n >= 2 && all_bool, Sort::Bool)),
            "=>" => Some((SmtOp::Implies, n >= 2 && all_bool, Sort::Bool)),
            "=" => Some((SmtOp::Eq, n >= 2 && same, Sort::Bool)),
            "distinct" => Some((SmtOp::Distinct, n >= 2 && same, Sort::Bool)),
            "ite" => {
                let ok = n == 3 && sorts[0] == Sort::Bool && sorts[1] == sorts[2];
                Some((SmtOp::Ite, ok, if n == 3 { sorts[1] } else { Sort::Bool }))
            }
            _ => None,
        };
        if let Some((op, ok, ret)) = core {
            if !ok {
                return err(format!("ill-sorted application of {}", name));
            }
            return Ok((SmtTerm::App(op, args.into_iter().map(|a| a.0).collect()), ret));
        }
        if !self.bv {
            return err(format!("unknown function {}", String::from_utf8_lossy(f)));
        }
        let w = match sorts.first() {
            Some(Sort::Bv(w)) if sorts.iter().all(|s| matches!(s, Sort::Bv(_))) => *w,
            _ => return err(format!("unknown function or ill-sorted application: {}", String::from_utf8_lossy(f))),
        };
        let bin = n == 2 && same;
        let assoc = n >= 2 && same;
        let (op, ok, ret) = match name {
            "concat" => {
                let ret = if n == 2 { Sort::Bv(checked(w.checked_add(sorts[1].width()))?) } else { Sort::Bool };
                (SmtOp::Concat, n == 2, ret)
            }
            "bvnot" => (SmtOp::Bvnot, n == 1, Sort::Bv(w)),
            "bvneg" => (SmtOp::Bvneg, n == 1, Sort::Bv(w)),
            "bvand" => (SmtOp::Bvand, assoc, Sort::Bv(w)),
            "bvor" => (SmtOp::Bvor, assoc, Sort::Bv(w)),
            "bvadd" => (SmtOp::Bvadd, assoc, Sort::Bv(w)),
            "bvmul" => (SmtOp::Bvmul, assoc, Sort::Bv(w)),
            "bvudiv" => (SmtOp::Bvudiv, bin, Sort::Bv(w)),
            "bvurem" => (SmtOp::Bvurem, bin, Sort::Bv(w)),
            "bvshl" => (SmtOp::Bvshl, bin, Sort::Bv(w)),
            "bvlshr" => (SmtOp::Bvlshr, bin, Sort::Bv(w)),
            "bvult" => (SmtOp::Bvult, bin, Sort::Bool),
            "bvnand" => (SmtOp::Bvnand, bin, Sort::Bv(w)),
            "bvnor" => (SmtOp::Bvnor, bin, Sort::Bv(w)),
            "bvxor" => (SmtOp::Bvxor, bin, Sort::Bv(w)),
            "bvxnor" => (SmtOp::Bvxnor, bin, Sort::Bv(w)),
            "bvcomp" => (SmtOp::Bvcomp, bin, Sort::Bv(1)),
            "bvsub" => (SmtOp::Bvsub, bin, Sort::Bv(w)),
            "bvsdiv" => (SmtOp::Bvsdiv, bin, Sort::Bv(w)),
            "bvsrem" => (SmtOp::Bvsrem, bin, Sort::Bv(w)),
            "bvsmod" => (SmtOp::Bvsmod, bin, Sort::Bv(w)),
            "bvashr" => (SmtOp::Bvashr, bin, Sort::Bv(w)),
            "bvule" => (SmtOp::Bvule, bin, Sort::Bool),
            "bvugt" => (SmtOp::Bvugt, bin, Sort::Bool),
            "bvuge" => (SmtOp::Bvuge, bin, Sort::Bool),
            "bvslt" => (SmtOp::Bvslt, bin, Sort::Bool),
            "bvsle" => (SmtOp::Bvsle, bin, Sort::Bool),
            "bvsgt" => (SmtOp::Bvsgt, bin, Sort::Bool),
            "bvsge" => (SmtOp::Bvsge, bin, Sort::Bool),
            _ => return err(format!("unknown function {}", String::from_utf8_lossy(f))),
        };
        if !ok {
            return err(format!("ill-sorted application of {}", name));
        }
        Ok((SmtTerm::App(op, args.into_iter().map(|a| a.0).collect()), ret))
    }

    fn apply_indexed(&mut self, h: &[Sexp], mut args: Vec<(SmtTerm, Sort)>) -> R<(SmtTerm, Sort)> {
        if !self.bv {
            return err("indexed functions are not in the logic");
        }
        let f = symbol(&h[1])?;
        let idx = h[2..].iter().map(numeral).collect::<R<Vec<usize>>>()?;
        if args.len() != 1 {
            return err("an indexed bit-vector function takes one argument");
        }
        let w = match args[0].1 {
            Sort::Bv(w) => w,
            _ => return err("an indexed bit-vector function takes a bit-vector"),
        };
        let (op, ret) = match (f.as_slice(), idx.as_slice()) {
            (b"extract", [i, j]) => {
                if !(w > *i && i >= j) {
                    return err("extract indices out of range");
                }
                (SmtOp::Extract(*i, *j), Sort::Bv(i - j + 1))
            }
            (b"repeat", [i]) => {
                if *i == 0 {
                    return err("repeat needs an index of at least 1");
                }
                (SmtOp::Repeat(*i), Sort::Bv(checked(w.checked_mul(*i))?))
            }
            (b"zero_extend", [i]) => (SmtOp::ZeroExtend(*i), Sort::Bv(checked(w.checked_add(*i))?)),
            (b"sign_extend", [i]) => (SmtOp::SignExtend(*i), Sort::Bv(checked(w.checked_add(*i))?)),
            (b"rotate_left", [i]) => (SmtOp::RotateLeft(*i), Sort::Bv(w)),
            (b"rotate_right", [i]) => (SmtOp::RotateRight(*i), Sort::Bv(w)),
            _ => return err(format!("unknown indexed function {}", String::from_utf8_lossy(&f))),
        };
        let a = args.pop().expect("one argument").0;
        Ok((SmtTerm::App(op, vec![a]), ret))
    }

    /// The `get-model` response: a `define-fun` for every declared function symbol.
    fn print_model(&self, m: &SmtModel) -> Result<Vec<u8>, String> {
        if m.domains.len() != self.sort_names.len() || m.funs.len() != self.fun_names.len() {
            return Err("the solver returned a malformed model".into());
        }
        if m.domains.iter().any(|&d| d == 0) {
            return Err("the solver returned an empty domain".into());
        }
        let mut out = b"(\n".to_vec();
        for (i, name) in self.fun_names.iter().enumerate() {
            let (args, ret) = &self.fun_sigs[i];
            let interp = &m.funs[i];
            out.extend_from_slice(b"  (define-fun ");
            write_symbol(&mut out, name);
            out.extend_from_slice(b" (");
            for (k, s) in args.iter().enumerate() {
                if k > 0 {
                    out.push(b' ');
                }
                out.extend_from_slice(format!("(x{} ", k).as_bytes());
                self.write_sort(&mut out, *s);
                out.push(b')');
            }
            out.extend_from_slice(b") ");
            self.write_sort(&mut out, *ret);
            out.push(b' ');
            if args.is_empty() {
                // A constant: the first entry matches, if there is one.
                let v = interp.entries.first().map(|e| &e.val).unwrap_or(&interp.default);
                self.write_value(&mut out, m, v, *ret)?;
                out.extend_from_slice(b")\n");
                continue;
            }
            let mut closing = 0;
            for e in &interp.entries {
                if e.args.len() != args.len() {
                    return Err("the solver returned a malformed model".into());
                }
                out.extend_from_slice(b"(ite ");
                if args.len() > 1 {
                    out.extend_from_slice(b"(and");
                }
                for (k, (v, s)) in e.args.iter().zip(args).enumerate() {
                    if args.len() > 1 {
                        out.push(b' ');
                    }
                    out.extend_from_slice(format!("(= x{} ", k).as_bytes());
                    self.write_value(&mut out, m, v, *s)?;
                    out.push(b')');
                }
                if args.len() > 1 {
                    out.push(b')');
                }
                out.push(b' ');
                self.write_value(&mut out, m, &e.val, *ret)?;
                out.push(b' ');
                closing += 1;
            }
            self.write_value(&mut out, m, &interp.default, *ret)?;
            out.extend(std::iter::repeat_n(b')', closing));
            out.extend_from_slice(b")\n");
        }
        out.push(b')');
        Ok(out)
    }

    fn write_sort(&self, out: &mut Vec<u8>, s: Sort) {
        match s {
            Sort::Bool => out.extend_from_slice(b"Bool"),
            Sort::Bv(w) => out.extend_from_slice(format!("(_ BitVec {})", w).as_bytes()),
            Sort::U(i) => write_symbol(out, &self.sort_names[i]),
        }
    }

    fn write_value(&self, out: &mut Vec<u8>, m: &SmtModel, v: &SmtValue, s: Sort) -> Result<(), String> {
        match (v, s) {
            (SmtValue::Bool(b), Sort::Bool) => out.extend_from_slice(if *b { b"true" } else { b"false" }),
            (SmtValue::Bv(bits), Sort::Bv(w)) if bits.len() == w => {
                out.extend_from_slice(b"#b");
                out.extend(bits.iter().rev().map(|&b| if b { b'1' } else { b'0' }));
            }
            (SmtValue::Elem(k), Sort::U(i)) if *k < m.domains[i] => {
                // An abstract value (Section 3.1: symbols starting with @ are reserved for them),
                // with its sort made explicit by `as` (Section 4.2.6).
                out.extend_from_slice(b"(as ");
                out.extend_from_slice(&abstract_value(&self.sort_names[i], i, *k));
                out.push(b' ');
                write_symbol(out, &self.sort_names[i]);
                out.push(b')');
            }
            _ => return Err("the solver returned a value of the wrong sort".into()),
        }
        Ok(())
    }
}

impl Sort {
    fn width(self) -> usize {
        match self {
            Sort::Bv(w) => w,
            _ => 0,
        }
    }
}

/// The abstract value for element `k` of sort number `i` named `name`: `@name_k` when that is a
/// simple symbol, otherwise `@sort<i>_k`.
pub fn abstract_value(name: &[u8], i: usize, k: usize) -> Vec<u8> {
    let mut v = b"@".to_vec();
    v.extend_from_slice(name);
    v.extend_from_slice(format!("_{}", k).as_bytes());
    if is_simple_symbol(&v) { v } else { format!("@sort{}_{}", i, k).into_bytes() }
}
