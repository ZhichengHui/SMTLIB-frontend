//! S-expressions (Section 3.2): the tokens grouped by parentheses.

use crate::Error;
use crate::lexer::{Token, tokenize};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sexp {
    /// A token other than a parenthesis, at a byte offset.
    Atom(usize, Token),
    /// A parenthesized list, at the offset of its `(`.
    List(usize, Vec<Sexp>),
}

impl Sexp {
    pub fn offset(&self) -> usize {
        match self {
            Sexp::Atom(o, _) | Sexp::List(o, _) => *o,
        }
    }
}

/// The top-level s-expressions of `src`.
pub fn read(src: &[u8]) -> Result<Vec<Sexp>, Error> {
    let mut stack: Vec<(usize, Vec<Sexp>)> = vec![(0, Vec::new())];
    for (off, t) in tokenize(src)? {
        match t {
            Token::LParen => stack.push((off, Vec::new())),
            Token::RParen => {
                if stack.len() == 1 {
                    return Err(Error::new(off, "unmatched ')'"));
                }
                let (o, items) = stack.pop().expect("non-empty stack");
                stack.last_mut().expect("non-empty stack").1.push(Sexp::List(o, items));
            }
            t => stack.last_mut().expect("non-empty stack").1.push(Sexp::Atom(off, t)),
        }
    }
    if stack.len() > 1 {
        return Err(Error::new(stack.last().expect("non-empty stack").0, "unmatched '('"));
    }
    Ok(stack.pop().expect("non-empty stack").1)
}
