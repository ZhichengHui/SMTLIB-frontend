//! `bridge!(core)` defines `problem_to_core` and `answer_from_core`, converting between this
//! crate's problem structure and the identical copy in the solver crate `core`. Every variant and
//! field is matched, so a difference between the two copies is a compile error.

#[macro_export]
macro_rules! bridge {
    ($core:ident) => {
        fn sort_to_core(s: &$crate::SmtSort) -> $core::SmtSort {
            match s {
                $crate::SmtSort::Bool => $core::SmtSort::Bool,
                $crate::SmtSort::BitVec(w) => $core::SmtSort::BitVec(*w),
                $crate::SmtSort::Uninterpreted(i) => $core::SmtSort::Uninterpreted(*i),
            }
        }

        fn op_to_core(o: &$crate::SmtOp) -> $core::SmtOp {
            use $crate::SmtOp as A;
            use $core::SmtOp as B;
            match o {
                A::Not => B::Not,
                A::And => B::And,
                A::Or => B::Or,
                A::Xor => B::Xor,
                A::Implies => B::Implies,
                A::Eq => B::Eq,
                A::Distinct => B::Distinct,
                A::Ite => B::Ite,
                A::Concat => B::Concat,
                A::Extract(i, j) => B::Extract(*i, *j),
                A::Bvnot => B::Bvnot,
                A::Bvand => B::Bvand,
                A::Bvor => B::Bvor,
                A::Bvneg => B::Bvneg,
                A::Bvadd => B::Bvadd,
                A::Bvmul => B::Bvmul,
                A::Bvudiv => B::Bvudiv,
                A::Bvurem => B::Bvurem,
                A::Bvshl => B::Bvshl,
                A::Bvlshr => B::Bvlshr,
                A::Bvult => B::Bvult,
                A::Bvnand => B::Bvnand,
                A::Bvnor => B::Bvnor,
                A::Bvxor => B::Bvxor,
                A::Bvxnor => B::Bvxnor,
                A::Bvcomp => B::Bvcomp,
                A::Bvsub => B::Bvsub,
                A::Bvsdiv => B::Bvsdiv,
                A::Bvsrem => B::Bvsrem,
                A::Bvsmod => B::Bvsmod,
                A::Bvashr => B::Bvashr,
                A::Repeat(i) => B::Repeat(*i),
                A::ZeroExtend(i) => B::ZeroExtend(*i),
                A::SignExtend(i) => B::SignExtend(*i),
                A::RotateLeft(i) => B::RotateLeft(*i),
                A::RotateRight(i) => B::RotateRight(*i),
                A::Bvule => B::Bvule,
                A::Bvugt => B::Bvugt,
                A::Bvuge => B::Bvuge,
                A::Bvslt => B::Bvslt,
                A::Bvsle => B::Bvsle,
                A::Bvsgt => B::Bvsgt,
                A::Bvsge => B::Bvsge,
            }
        }

        fn term_to_core(t: &$crate::SmtTerm) -> $core::SmtTerm {
            let args = |a: &Vec<$crate::SmtTerm>| a.iter().map(term_to_core).collect();
            match t {
                $crate::SmtTerm::BoolConst(b) => $core::SmtTerm::BoolConst(*b),
                $crate::SmtTerm::BvConst(b) => $core::SmtTerm::BvConst(b.clone()),
                $crate::SmtTerm::Param(k) => $core::SmtTerm::Param(*k),
                $crate::SmtTerm::Fun(f, a) => $core::SmtTerm::Fun(*f, args(a)),
                $crate::SmtTerm::Def(d, a) => $core::SmtTerm::Def(*d, args(a)),
                $crate::SmtTerm::App(o, a) => $core::SmtTerm::App(op_to_core(o), args(a)),
            }
        }

        pub fn problem_to_core(p: &$crate::SmtProblem) -> $core::SmtProblem {
            let $crate::SmtProblem { num_sorts, funs, defs, asserts } = p;
            $core::SmtProblem {
                num_sorts: *num_sorts,
                funs: funs
                    .iter()
                    .map(|$crate::SmtFun { args, ret }| $core::SmtFun {
                        args: args.iter().map(sort_to_core).collect(),
                        ret: sort_to_core(ret),
                    })
                    .collect(),
                defs: defs
                    .iter()
                    .map(|$crate::SmtDef { params, ret, body }| $core::SmtDef {
                        params: params.iter().map(sort_to_core).collect(),
                        ret: sort_to_core(ret),
                        body: term_to_core(body),
                    })
                    .collect(),
                asserts: asserts.iter().map(term_to_core).collect(),
            }
        }

        fn value_from_core(v: $core::SmtValue) -> $crate::SmtValue {
            match v {
                $core::SmtValue::Bool(b) => $crate::SmtValue::Bool(b),
                $core::SmtValue::Bv(b) => $crate::SmtValue::Bv(b),
                $core::SmtValue::Elem(k) => $crate::SmtValue::Elem(k),
            }
        }

        pub fn answer_from_core(a: $core::SmtAnswer) -> $crate::SmtAnswer {
            match a {
                $core::SmtAnswer::Sat($core::SmtModel { domains, funs }) => $crate::SmtAnswer::Sat($crate::SmtModel {
                    domains,
                    funs: funs
                        .into_iter()
                        .map(|$core::SmtInterp { entries, default }| $crate::SmtInterp {
                            entries: entries
                                .into_iter()
                                .map(|$core::SmtEntry { args, val }| $crate::SmtEntry {
                                    args: args.into_iter().map(value_from_core).collect(),
                                    val: value_from_core(val),
                                })
                                .collect(),
                            default: value_from_core(default),
                        })
                        .collect(),
                }),
                $core::SmtAnswer::Unsat => $crate::SmtAnswer::Unsat,
                $core::SmtAnswer::Unknown => $crate::SmtAnswer::Unknown,
            }
        }
    };
}
