//! A reference evaluator: checks that a model satisfies a problem, following the semantics of
//! SMT-LIB 2.6 (Core, FixedSizeBitVectors and the QF_BV extensions, uninterpreted functions).
//! It is used to test the solvers; it is not part of what is verified.

use crate::problem::*;

/// A value. Bit-vectors are least significant bit first.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Val {
    Bool(bool),
    Bv(Vec<bool>),
    Elem(usize),
}

fn value(v: &SmtValue) -> Val {
    match v {
        SmtValue::Bool(b) => Val::Bool(*b),
        SmtValue::Bv(b) => Val::Bv(b.clone()),
        SmtValue::Elem(k) => Val::Elem(*k),
    }
}

/// Whether `v` is a value of sort `s` in a model with these domain sizes.
fn has_sort(v: &SmtValue, s: &SmtSort, domains: &[usize]) -> bool {
    match (v, s) {
        (SmtValue::Bool(_), SmtSort::Bool) => true,
        (SmtValue::Bv(b), SmtSort::BitVec(w)) => b.len() == *w,
        (SmtValue::Elem(k), SmtSort::Uninterpreted(i)) => *i < domains.len() && *k < domains[*i],
        _ => false,
    }
}

/// Checks that `m` is a well-formed model of `p` (every value has the declared sort, every
/// domain is non-empty) and that every assertion is true in it. `Ok(false)`: well-formed, but
/// some assertion is false. `Err`: malformed model, or a term outside the semantics.
pub fn check_model(p: &SmtProblem, m: &SmtModel) -> Result<bool, String> {
    if m.domains.len() != p.num_sorts || m.domains.iter().any(|&d| d == 0) {
        return Err("bad domains".into());
    }
    if m.funs.len() != p.funs.len() {
        return Err("wrong number of interpretations".into());
    }
    for (f, i) in p.funs.iter().zip(&m.funs) {
        if !has_sort(&i.default, &f.ret, &m.domains) {
            return Err("default value of the wrong sort".into());
        }
        for e in &i.entries {
            if e.args.len() != f.args.len()
                || !has_sort(&e.val, &f.ret, &m.domains)
                || e.args.iter().zip(&f.args).any(|(v, s)| !has_sort(v, s, &m.domains))
            {
                return Err("table entry of the wrong sort".into());
            }
        }
    }
    let mut ev = Eval { p, m, cache: vec![None; p.defs.len()] };
    for t in &p.asserts {
        if ev.eval(t, &[])? != Val::Bool(true) {
            return Ok(false);
        }
    }
    Ok(true)
}

struct Eval<'a> {
    p: &'a SmtProblem,
    m: &'a SmtModel,
    /// The values of the definitions without parameters, once computed.
    cache: Vec<Option<Val>>,
}

fn bools(vs: &[Val]) -> Result<Vec<bool>, String> {
    vs.iter().map(|v| if let Val::Bool(b) = v { Ok(*b) } else { Err("expected a Boolean".to_string()) }).collect()
}

fn bvs(vs: &[Val]) -> Result<Vec<Vec<bool>>, String> {
    vs.iter().map(|v| if let Val::Bv(b) = v { Ok(b.clone()) } else { Err("expected a bit-vector".to_string()) }).collect()
}

impl Eval<'_> {
    fn eval(&mut self, t: &SmtTerm, params: &[Val]) -> Result<Val, String> {
        match t {
            SmtTerm::BoolConst(b) => Ok(Val::Bool(*b)),
            SmtTerm::BvConst(b) => Ok(Val::Bv(b.clone())),
            SmtTerm::Param(k) => params.get(*k).cloned().ok_or_else(|| "parameter out of range".into()),
            SmtTerm::Fun(f, args) => {
                let vs = args.iter().map(|a| self.eval(a, params)).collect::<Result<Vec<_>, _>>()?;
                let i = self.m.funs.get(*f).ok_or("function out of range")?;
                for e in &i.entries {
                    if e.args.iter().map(value).eq(vs.iter().cloned()) {
                        return Ok(value(&e.val));
                    }
                }
                Ok(value(&i.default))
            }
            SmtTerm::Def(d, args) => {
                let def = self.p.defs.get(*d).ok_or("definition out of range")?;
                if def.params.is_empty() {
                    if let Some(v) = &self.cache[*d] {
                        return Ok(v.clone());
                    }
                    let v = self.eval(&def.body, &[])?;
                    self.cache[*d] = Some(v.clone());
                    return Ok(v);
                }
                let vs = args.iter().map(|a| self.eval(a, params)).collect::<Result<Vec<_>, _>>()?;
                self.eval(&def.body, &vs)
            }
            SmtTerm::App(op, args) => {
                let vs = args.iter().map(|a| self.eval(a, params)).collect::<Result<Vec<_>, _>>()?;
                apply(op, &vs)
            }
        }
    }
}

fn apply(op: &SmtOp, vs: &[Val]) -> Result<Val, String> {
    use SmtOp::*;
    let b = Val::Bool;
    let v = Val::Bv;
    Ok(match op {
        Not => b(!bools(vs)?[0]),
        And => b(bools(vs)?.iter().all(|&x| x)),
        Or => b(bools(vs)?.iter().any(|&x| x)),
        Xor => b(bools(vs)?.iter().fold(false, |a, &x| a ^ x)),
        Implies => {
            // Right associative: (=> a b c) is (=> a (=> b c)).
            let xs = bools(vs)?;
            let (last, init) = xs.split_last().ok_or("=> without arguments")?;
            b(init.iter().any(|&x| !x) || *last)
        }
        Eq => b(vs.windows(2).all(|w| w[0] == w[1])),
        Distinct => b((0..vs.len()).all(|i| (i + 1..vs.len()).all(|j| vs[i] != vs[j]))),
        Ite => match &vs[0] {
            Val::Bool(c) => if *c { vs[1].clone() } else { vs[2].clone() },
            _ => return Err("ite condition".into()),
        },
        _ => {
            let x = bvs(vs)?;
            match op {
                Concat => {
                    let mut r = x[1].clone();
                    r.extend_from_slice(&x[0]);
                    v(r)
                }
                Extract(i, j) => v(x[0][*j..=*i].to_vec()),
                Bvnot => v(not(&x[0])),
                Bvand => v(x[1..].iter().fold(x[0].clone(), |a, y| zip(&a, y, |p, q| p & q))),
                Bvor => v(x[1..].iter().fold(x[0].clone(), |a, y| zip(&a, y, |p, q| p | q))),
                Bvneg => v(neg(&x[0])),
                Bvadd => v(x[1..].iter().fold(x[0].clone(), |a, y| add(&a, y))),
                Bvmul => v(x[1..].iter().fold(x[0].clone(), |a, y| mul(&a, y))),
                Bvudiv => v(udivrem(&x[0], &x[1]).0),
                Bvurem => v(udivrem(&x[0], &x[1]).1),
                Bvshl => v(shl(&x[0], amount(&x[1]))),
                Bvlshr => v(lshr(&x[0], amount(&x[1]), false)),
                Bvult => b(ult(&x[0], &x[1])),
                Bvnand => v(not(&zip(&x[0], &x[1], |p, q| p & q))),
                Bvnor => v(not(&zip(&x[0], &x[1], |p, q| p | q))),
                Bvxor => v(zip(&x[0], &x[1], |p, q| p ^ q)),
                Bvxnor => v(not(&zip(&x[0], &x[1], |p, q| p ^ q))),
                Bvcomp => v(vec![x[0] == x[1]]),
                Bvsub => v(add(&x[0], &neg(&x[1]))),
                Bvsdiv => v(sdiv(&x[0], &x[1])),
                Bvsrem => v(srem(&x[0], &x[1])),
                Bvsmod => v(smod(&x[0], &x[1])),
                Bvashr => v(lshr(&x[0], amount(&x[1]), *x[0].last().expect("width >= 1"))),
                Repeat(i) => v(x[0].iter().cycle().take(x[0].len() * i).copied().collect()),
                ZeroExtend(i) => {
                    let mut r = x[0].clone();
                    r.extend(std::iter::repeat_n(false, *i));
                    v(r)
                }
                SignExtend(i) => {
                    let mut r = x[0].clone();
                    let msb = *r.last().expect("width >= 1");
                    r.extend(std::iter::repeat_n(msb, *i));
                    v(r)
                }
                RotateLeft(i) => {
                    let w = x[0].len();
                    let r = i % w;
                    v((0..w).map(|k| x[0][(k + w - r) % w]).collect())
                }
                RotateRight(i) => {
                    let w = x[0].len();
                    let r = i % w;
                    v((0..w).map(|k| x[0][(k + r) % w]).collect())
                }
                Bvule => b(!ult(&x[1], &x[0])),
                Bvugt => b(ult(&x[1], &x[0])),
                Bvuge => b(!ult(&x[0], &x[1])),
                Bvslt => b(slt(&x[0], &x[1])),
                Bvsle => b(!slt(&x[1], &x[0])),
                Bvsgt => b(slt(&x[1], &x[0])),
                Bvsge => b(!slt(&x[0], &x[1])),
                Not | And | Or | Xor | Implies | Eq | Distinct | Ite => unreachable!(),
            }
        }
    })
}

fn zip(a: &[bool], b: &[bool], f: impl Fn(bool, bool) -> bool) -> Vec<bool> {
    a.iter().zip(b).map(|(&p, &q)| f(p, q)).collect()
}

fn not(a: &[bool]) -> Vec<bool> {
    a.iter().map(|&p| !p).collect()
}

fn add(a: &[bool], b: &[bool]) -> Vec<bool> {
    let mut c = false;
    a.iter()
        .zip(b)
        .map(|(&p, &q)| {
            let s = p ^ q ^ c;
            c = (p & q) | (c & (p ^ q));
            s
        })
        .collect()
}

fn neg(a: &[bool]) -> Vec<bool> {
    let mut one = vec![false; a.len()];
    one[0] = true;
    add(&not(a), &one)
}

fn mul(a: &[bool], b: &[bool]) -> Vec<bool> {
    let w = a.len();
    let mut r = vec![false; w];
    for i in 0..w {
        if b[i] {
            r = add(&r, &shl(a, i));
        }
    }
    r
}

/// The shift amount: the value of `b`, saturated at `usize::MAX`.
fn amount(b: &[bool]) -> usize {
    let mut n: usize = 0;
    for (i, &x) in b.iter().enumerate() {
        if x {
            if i >= usize::BITS as usize {
                return usize::MAX;
            }
            n |= 1 << i;
        }
    }
    n
}

fn shl(a: &[bool], n: usize) -> Vec<bool> {
    let w = a.len();
    (0..w).map(|k| k >= n && a[k - n]).collect()
}

fn lshr(a: &[bool], n: usize, fill: bool) -> Vec<bool> {
    let w = a.len();
    (0..w).map(|k| if n < w - k { a[k + n] } else { fill }).collect()
}

fn ult(a: &[bool], b: &[bool]) -> bool {
    for k in (0..a.len()).rev() {
        if a[k] != b[k] {
            return b[k];
        }
    }
    false
}

fn slt(a: &[bool], b: &[bool]) -> bool {
    let (sa, sb) = (*a.last().expect("width >= 1"), *b.last().expect("width >= 1"));
    (sa && !sb) || (sa == sb && ult(a, b))
}

/// Unsigned quotient and remainder; division by zero gives all ones and the dividend.
fn udivrem(a: &[bool], b: &[bool]) -> (Vec<bool>, Vec<bool>) {
    let w = a.len();
    if b.iter().all(|&x| !x) {
        return (vec![true; w], a.to_vec());
    }
    let mut q = vec![false; w];
    let mut r = vec![false; w + 1];
    let mut bb = b.to_vec();
    bb.push(false);
    for i in (0..w).rev() {
        r = shl(&r, 1);
        r[0] = a[i];
        if !ult(&r, &bb) {
            r = add(&r, &neg(&bb));
            q[i] = true;
        }
    }
    r.pop();
    (q, r)
}

fn msb(a: &[bool]) -> bool {
    *a.last().expect("width >= 1")
}

/// QF_BV definitions of bvsdiv, bvsrem, bvsmod by cases on the sign bits.
fn sdiv(s: &[bool], t: &[bool]) -> Vec<bool> {
    match (msb(s), msb(t)) {
        (false, false) => udivrem(s, t).0,
        (true, false) => neg(&udivrem(&neg(s), t).0),
        (false, true) => neg(&udivrem(s, &neg(t)).0),
        (true, true) => udivrem(&neg(s), &neg(t)).0,
    }
}

fn srem(s: &[bool], t: &[bool]) -> Vec<bool> {
    match (msb(s), msb(t)) {
        (false, false) => udivrem(s, t).1,
        (true, false) => neg(&udivrem(&neg(s), t).1),
        (false, true) => udivrem(s, &neg(t)).1,
        (true, true) => neg(&udivrem(&neg(s), &neg(t)).1),
    }
}

fn smod(s: &[bool], t: &[bool]) -> Vec<bool> {
    let abs_s = if msb(s) { neg(s) } else { s.to_vec() };
    let abs_t = if msb(t) { neg(t) } else { t.to_vec() };
    let u = udivrem(&abs_s, &abs_t).1;
    if u.iter().all(|&x| !x) {
        return u;
    }
    match (msb(s), msb(t)) {
        (false, false) => u,
        (true, false) => add(&neg(&u), t),
        (false, true) => add(&u, t),
        (true, true) => neg(&u),
    }
}
