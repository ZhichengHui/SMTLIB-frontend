use smtlib::semantics::check_model;
use smtlib::*;

/// Runs `src` with `solve` and returns the output.
fn run(src: &str, solve: &mut dyn FnMut(&SmtProblem) -> SmtAnswer) -> String {
    let mut out = Vec::new();
    script::run(src.as_bytes(), solve, &mut out).unwrap();
    String::from_utf8(out).unwrap()
}

fn unsat(_: &SmtProblem) -> SmtAnswer {
    SmtAnswer::Unsat
}

#[test]
fn lexer() {
    use smtlib::lexer::{Token, tokenize};
    let t = |s: &str| tokenize(s.as_bytes()).map(|v| v.into_iter().map(|x| x.1).collect::<Vec<_>>());
    assert_eq!(t("|a b| ab ; c\n#b01 #xA 12 1.5 :k \"x\"\"y\"").unwrap(), vec![
        Token::Symbol(b"a b".to_vec()),
        Token::Symbol(b"ab".to_vec()),
        Token::Binary("01".into()),
        Token::Hexadecimal("A".into()),
        Token::Numeral("12".into()),
        Token::Decimal("1.5".into()),
        Token::Keyword("k".into()),
        Token::String(b"x\"y".to_vec()),
    ]);
    assert_eq!(t("let").unwrap(), vec![Token::Reserved("let")]);
    assert_eq!(t("|let|").unwrap(), vec![Token::Symbol(b"let".to_vec())]);
    for bad in ["01", "#b", "#b2", "#x", "|a\\b|", "\"abc", "1a"] {
        assert!(t(bad).is_err(), "{}", bad);
    }
}

#[test]
fn problem_structure() {
    let src = "(set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (declare-fun p () Bool)
        (define-fun twice ((a (_ BitVec 4))) (_ BitVec 4) (let ((b (bvadd a a))) b))
        (assert (let ((y (twice x)) (z #x3)) (and p (= y z (bvadd x x x)))))
        (check-sat)";
    let mut seen = None;
    let out = run(src, &mut |p: &SmtProblem| {
        seen = Some((
            p.num_sorts,
            p.funs.len(),
            p.defs.iter().map(|d| d.params.len()).collect::<Vec<_>>(),
            p.asserts.len(),
        ));
        // The assertion is (and p (= y z (bvadd x x x))) with y, z let-bound.
        match &p.asserts[0] {
            SmtTerm::App(SmtOp::And, a) => match &a[1] {
                SmtTerm::App(SmtOp::Eq, e) => {
                    assert_eq!(e.len(), 3);
                    assert!(matches!(&e[2], SmtTerm::App(SmtOp::Bvadd, xs) if xs.len() == 3));
                }
                _ => panic!("expected ="),
            },
            _ => panic!("expected and"),
        }
        SmtAnswer::Unknown
    });
    assert_eq!(out, "unknown\n");
    // Definitions: b (the let inside twice, with twice's parameter), twice, y, z.
    assert_eq!(seen, Some((0, 2, vec![1, 1, 0, 0], 1)));
}

#[test]
fn responses() {
    let out = run("(set-option :print-success true)(set-logic QF_UF)(declare-sort U 0)(check-sat)(exit)(check-sat)", &mut unsat);
    // exit ends the script without a response; nothing after it runs.
    assert_eq!(out, "success\nsuccess\nsuccess\nunsat\n");
    // An unsupported command that changes the assertions makes check-sat answer unknown.
    let out = run("(set-logic QF_UF)(push 1)(check-sat)", &mut unsat);
    assert_eq!(out, "unsupported\nunknown\n");
    // A quantifier is not supported in these logics.
    let out = run("(set-logic QF_UF)(declare-sort U 0)(assert (forall ((x U)) (= x x)))(check-sat)", &mut unsat);
    assert_eq!(out, "unsupported\nunknown\n");
    // Errors stop the script.
    let out = run("(set-logic QF_UF)(assert (= 1 1))(check-sat)", &mut unsat);
    assert!(out.starts_with("(error") && !out.contains("unsat"), "{}", out);
    let out = run("(set-logic QF_BV)(declare-const x (_ BitVec 4))(assert (= x #b1))(check-sat)", &mut unsat);
    assert!(out.starts_with("(error"), "{}", out);
    let out = run("(set-logic QF_BV)(declare-const x (_ BitVec 4))(declare-const x (_ BitVec 4))", &mut unsat);
    assert!(out.starts_with("(error"), "{}", out);
    let out = run("(set-logic QF_BV)(declare-fun f ((_ BitVec 4)) (_ BitVec 4))", &mut unsat);
    assert!(out.starts_with("(error"), "{}", out);
    let out = run("(set-logic QF_LIA)(check-sat)", &mut unsat);
    assert_eq!(out, "unsupported\nunknown\n");
    let out = run("(get-model)", &mut unsat);
    assert!(out.starts_with("(error"), "{}", out);
}

#[test]
fn model_printing() {
    let src = "(set-logic QF_UFBV)
        (declare-sort U 0)
        (declare-fun f (U Bool) U)
        (declare-const c U)
        (declare-const v (_ BitVec 3))
        (declare-const |odd name| Bool)
        (check-sat)
        (get-model)";
    let out = run(src, &mut |_: &SmtProblem| {
        SmtAnswer::Sat(SmtModel {
            domains: vec![2],
            funs: vec![
                SmtInterp {
                    entries: vec![SmtEntry { args: vec![SmtValue::Elem(0), SmtValue::Bool(true)], val: SmtValue::Elem(1) }],
                    default: SmtValue::Elem(0),
                },
                SmtInterp { entries: vec![], default: SmtValue::Elem(1) },
                SmtInterp { entries: vec![], default: SmtValue::Bv(vec![true, false, false]) },
                SmtInterp { entries: vec![], default: SmtValue::Bool(false) },
            ],
        })
    });
    assert_eq!(
        out,
        "sat\n(\n  (define-fun f ((x0 U) (x1 Bool)) U (ite (and (= x0 (as @U_0 U)) (= x1 true)) (as @U_1 U) (as @U_0 U)))\n  (define-fun c () U (as @U_1 U))\n  (define-fun v () (_ BitVec 3) #b001)\n  (define-fun |odd name| () Bool false)\n)\n"
    );
}

/// Parses `src` and returns the problem at its first check-sat.
fn problem_of(src: &str, f: &mut dyn FnMut(&SmtProblem)) {
    run(src, &mut |p: &SmtProblem| {
        f(p);
        SmtAnswer::Unknown
    });
}

#[test]
fn reference_evaluator_core_and_uf() {
    let src = "(set-logic QF_UF)(declare-sort U 0)(declare-fun f (U) U)(declare-const a U)(declare-fun p (U) Bool)
        (define-fun g ((x U)) Bool (p (f x)))
        (assert (distinct a (f a)))(assert (g a))(assert (=> (p a) (p a) false))(check-sat)";
    problem_of(src, &mut |p| {
        let m = |pa: bool| SmtModel {
            domains: vec![2],
            funs: vec![
                SmtInterp { entries: vec![SmtEntry { args: vec![SmtValue::Elem(0)], val: SmtValue::Elem(1) }], default: SmtValue::Elem(0) },
                SmtInterp { entries: vec![], default: SmtValue::Elem(0) },
                SmtInterp { entries: vec![SmtEntry { args: vec![SmtValue::Elem(0)], val: SmtValue::Bool(pa) }], default: SmtValue::Bool(true) },
            ],
        };
        // f a = 1 /= a = 0; p (f a) = p 1 = true; p a must be false for the implication.
        assert_eq!(check_model(p, &m(false)), Ok(true));
        assert_eq!(check_model(p, &m(true)), Ok(false));
    });
}

/// A deterministic pseudo-random generator.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 >> 11
    }
}

fn bits(x: u64, w: u32) -> String {
    format!("#b{:0width$b}", x & ((1u64 << w) - 1), width = w as usize)
}

/// Checks the evaluator's bit-vector operations against u64 arithmetic on random operands.
#[test]
fn reference_evaluator_bitvectors() {
    let w: u32 = 8;
    let mask = (1u64 << w) - 1;
    let sx = |x: u64| ((x << (64 - w)) as i64) >> (64 - w);
    let mut r = Lcg(1);
    let ops: Vec<(&str, Box<dyn Fn(u64, u64) -> u64>)> = vec![
        ("bvadd", Box::new(move |x, y| (x + y) & mask)),
        ("bvsub", Box::new(move |x, y| x.wrapping_sub(y) & mask)),
        ("bvmul", Box::new(move |x, y| (x * y) & mask)),
        ("bvudiv", Box::new(move |x, y| if y == 0 { mask } else { x / y })),
        ("bvurem", Box::new(move |x, y| if y == 0 { x } else { x % y })),
        ("bvshl", Box::new(move |x, y| if y >= w as u64 { 0 } else { (x << y) & mask })),
        ("bvlshr", Box::new(move |x, y| if y >= w as u64 { 0 } else { x >> y })),
        ("bvashr", Box::new(move |x, y| ((sx(x) >> y.min(63)) as u64) & mask)),
        ("bvsdiv", Box::new(move |x, y| {
            if y == 0 { if sx(x) < 0 { 1 } else { mask } } else { (sx(x).wrapping_div(sx(y)) as u64) & mask }
        })),
        ("bvsrem", Box::new(move |x, y| if y == 0 { x } else { (sx(x).wrapping_rem(sx(y)) as u64) & mask })),
        ("bvsmod", Box::new(move |x, y| if y == 0 { x } else { (sx(x).rem_euclid(sx(y).abs()) as i64 + if sx(y) < 0 && sx(x).rem_euclid(sx(y).abs()) != 0 { sx(y) } else { 0 }) as u64 & mask })),
        ("bvxnor", Box::new(move |x, y| !(x ^ y) & mask)),
        ("bvnand", Box::new(move |x, y| !(x & y) & mask)),
    ];
    let preds: Vec<(&str, Box<dyn Fn(u64, u64) -> bool>)> = vec![
        ("bvult", Box::new(|x, y| x < y)),
        ("bvule", Box::new(|x, y| x <= y)),
        ("bvslt", Box::new(move |x, y| sx(x) < sx(y))),
        ("bvsge", Box::new(move |x, y| sx(x) >= sx(y))),
    ];
    for _ in 0..200 {
        let (x, y) = (r.next() & mask, if r.next() % 5 == 0 { 0 } else { r.next() & mask });
        for (name, f) in &ops {
            let src = format!("(set-logic QF_BV)(assert (= ({} {} {}) {}))(check-sat)", name, bits(x, w), bits(y, w), bits(f(x, y), w));
            problem_of(&src, &mut |p| {
                let m = SmtModel { domains: vec![], funs: vec![] };
                assert_eq!(check_model(p, &m), Ok(true), "{} {} {}", name, x, y);
            });
        }
        for (name, f) in &preds {
            let src = format!("(set-logic QF_BV)(assert (= ({} {} {}) {}))(check-sat)", name, bits(x, w), bits(y, w), f(x, y));
            problem_of(&src, &mut |p| {
                let m = SmtModel { domains: vec![], funs: vec![] };
                assert_eq!(check_model(p, &m), Ok(true), "{} {} {}", name, x, y);
            });
        }
    }
    // Indexed operations and concat on one example.
    let src = "(set-logic QF_BV)(assert (and
        (= ((_ extract 5 2) #b11010110) #b0101)
        (= (concat #b10 #b011) #b10011)
        (= ((_ repeat 3) #b10) #b101010)
        (= ((_ zero_extend 2) #b11) #b0011)
        (= ((_ sign_extend 2) #b10) #b1110)
        (= ((_ rotate_left 1) #b1001) #b0011)
        (= ((_ rotate_right 1) #b1001) #b1100)
        (= (bvcomp #b10 #b10) #b1)
        (= (_ bv13 4) #xd)
        (= (bvneg #b0001) #b1111)))(check-sat)";
    problem_of(src, &mut |p| {
        assert_eq!(check_model(p, &SmtModel { domains: vec![], funs: vec![] }), Ok(true));
    });
}
