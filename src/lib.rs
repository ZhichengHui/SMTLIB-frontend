//! SMT-LIB 2.6 front end shared by the QF_UF and QF_BV solvers.
//!
//! * [`problem`]: the general problem structure, the interface to the solvers.
//! * [`script`]: reads a script (logics QF_UF, QF_BV, QF_UFBV), builds the problem, calls the
//!   solver at `check-sat` and prints the responses, including `get-model`.
//! * [`semantics`]: a reference evaluator that checks models (for testing).
//! * [`bridge!`]: conversion to and from the copy of the problem structure in a solver crate.
//!
//! Section numbers refer to the SMT-LIB reference, Version 2.6, r2024-09-20.

pub mod bridge;
pub mod lexer;
pub mod problem;
pub mod script;
pub mod semantics;
pub mod sexp;

pub use problem::*;

use std::fmt;
use std::io::{Read, Write};

/// A lexical or syntax error at a byte offset of the source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub offset: usize,
    pub message: String,
}

impl Error {
    pub fn new(offset: usize, message: impl Into<String>) -> Self {
        Error { offset, message: message.into() }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} (byte {})", self.message, self.offset)
    }
}

/// The main function of a solver binary: runs the script named by the first argument (standard
/// input without one) with `solve` and prints the responses on standard output. It writes
/// nothing on standard error (SMT-COMP may read it as a result). The solvers recurse on terms,
/// so the script runs on a thread with a large stack.
pub fn cli_main(solve: fn(&SmtProblem) -> SmtAnswer) -> ! {
    let src = match std::env::args().nth(1) {
        Some(path) => match std::fs::read(&path) {
            Ok(s) => s,
            Err(e) => {
                println!("(error \"cannot read {}: {}\")", path, e);
                std::process::exit(1)
            }
        },
        None => {
            let mut s = Vec::new();
            if std::io::stdin().read_to_end(&mut s).is_err() {
                println!("(error \"cannot read standard input\")");
                std::process::exit(1)
            }
            s
        }
    };
    // A panic message would go to standard error; the exit code reports the failure instead.
    std::panic::set_hook(Box::new(|_| {}));
    let worker = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || {
            let mut solve = solve;
            let stdout = std::io::stdout();
            let mut out = stdout.lock();
            let _ = script::run(&src, &mut solve, &mut out);
            let _ = out.flush();
        })
        .expect("spawn the solver thread");
    let code = if worker.join().is_ok() { 0 } else { 1 };
    std::process::exit(code)
}
