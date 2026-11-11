//! Lexical tokens of SMT-LIB 2.6 (reference r2024-09-20, Section 3.1).
//!
//! Source files consist of characters in any 8-bit encoding, so the lexer works on bytes.
//! Characters from 128 on are allowed only in string literals, quoted symbols and comments.

use crate::Error;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    LParen,
    RParen,
    /// The digits as written.
    Numeral(String),
    /// As written, e.g. `1.05`.
    Decimal(String),
    /// The digits after `#x`.
    Hexadecimal(String),
    /// The digits after `#b`.
    Binary(String),
    /// The contents between the quotes, with `""` read as `"`.
    String(Vec<u8>),
    /// A simple symbol, or the contents of a quoted symbol between the bars: `abc` and `|abc|` are
    /// the same symbol.
    Symbol(Vec<u8>),
    /// The characters after `:`.
    Keyword(String),
    Reserved(&'static str),
}

/// The reserved words: the basic set and every command name (Section 3.1).
pub const RESERVED: &[&str] = &[
    "BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING", "_", "!", "as", "exists", "forall", "let",
    "match", "par", "assert", "check-sat", "check-sat-assuming", "declare-const", "declare-datatype",
    "declare-datatypes", "declare-fun", "declare-sort", "define-fun", "define-fun-rec",
    "define-funs-rec", "define-sort", "echo", "exit", "get-assertions", "get-assignment", "get-info",
    "get-model", "get-option", "get-proof", "get-unsat-assumptions", "get-unsat-core", "get-value",
    "pop", "push", "reset", "reset-assertions", "set-info", "set-logic", "set-option",
];

pub fn is_whitespace(b: u8) -> bool {
    matches!(b, 9 | 10 | 13 | 32)
}

pub fn is_printable(b: u8) -> bool {
    (32..=126).contains(&b) || b >= 128
}

/// Letters, digits and `~ ! @ $ % ^ & * _ - + = < > . ? /`.
pub fn is_symbol_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b"~!@$%^&*_-+=<>.?/".contains(&b)
}

pub fn reserved(w: &[u8]) -> Option<&'static str> {
    RESERVED.iter().copied().find(|r| r.as_bytes() == w)
}

/// A simple symbol: symbol characters, not starting with a digit, not a reserved word.
pub fn is_simple_symbol(w: &[u8]) -> bool {
    !w.is_empty() && !w[0].is_ascii_digit() && w.iter().all(|&b| is_symbol_char(b)) && reserved(w).is_none()
}

/// `0`, or digits not starting with `0`.
pub fn is_numeral(w: &[u8]) -> bool {
    w == b"0" || (!w.is_empty() && w[0] != b'0' && w.iter().all(u8::is_ascii_digit))
}

fn ends_token(b: u8) -> bool {
    is_whitespace(b) || b"();\"|".contains(&b)
}

fn ascii(w: &[u8]) -> String {
    String::from_utf8(w.to_vec()).expect("checked to be ASCII")
}

fn classify(w: &[u8]) -> Result<Token, String> {
    let shown = String::from_utf8_lossy(w);
    if w.iter().any(|&c| !is_printable(c) || c >= 128) {
        return Err(format!("invalid character in token {}", shown));
    }
    if w[0] == b'#' {
        if let Some(d) = w.strip_prefix(b"#x") {
            if !d.is_empty() && d.iter().all(u8::is_ascii_hexdigit) {
                return Ok(Token::Hexadecimal(ascii(d)));
            }
        } else if let Some(d) = w.strip_prefix(b"#b") {
            if !d.is_empty() && d.iter().all(|&c| c == b'0' || c == b'1') {
                return Ok(Token::Binary(ascii(d)));
            }
        }
        return Err(format!("invalid literal {}", shown));
    }
    if w[0] == b':' {
        let r = &w[1..];
        if !r.is_empty() && r.iter().all(|&c| is_symbol_char(c)) {
            return Ok(Token::Keyword(ascii(r)));
        }
        return Err(format!("invalid keyword {}", shown));
    }
    if w[0].is_ascii_digit() {
        if is_numeral(w) {
            return Ok(Token::Numeral(ascii(w)));
        }
        if let Some(p) = w.iter().position(|&c| c == b'.') {
            let (n, f) = (&w[..p], &w[p + 1..]);
            if is_numeral(n) && !f.is_empty() && f.iter().all(u8::is_ascii_digit) {
                return Ok(Token::Decimal(ascii(w)));
            }
        }
        return Err(format!("invalid numeral {}", shown));
    }
    if w.iter().all(|&c| is_symbol_char(c)) {
        return Ok(match reserved(w) {
            Some(r) => Token::Reserved(r),
            None => Token::Symbol(w.to_vec()),
        });
    }
    Err(format!("invalid token {}", shown))
}

/// The tokens of `src` with their byte offsets; comments and whitespace are dropped.
pub fn tokenize(src: &[u8]) -> Result<Vec<(usize, Token)>, Error> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < src.len() {
        let b = src[i];
        if is_whitespace(b) {
            i += 1;
            continue;
        }
        if b == b';' {
            while i < src.len() && src[i] != 10 && src[i] != 13 {
                i += 1;
            }
            continue;
        }
        let start = i;
        match b {
            b'(' => {
                out.push((start, Token::LParen));
                i += 1;
            }
            b')' => {
                out.push((start, Token::RParen));
                i += 1;
            }
            b'"' => {
                let mut s = Vec::new();
                i += 1;
                loop {
                    if i >= src.len() {
                        return Err(Error::new(start, "unterminated string literal"));
                    }
                    let c = src[i];
                    if c == b'"' {
                        if i + 1 < src.len() && src[i + 1] == b'"' {
                            s.push(b'"');
                            i += 2;
                            continue;
                        }
                        i += 1;
                        break;
                    }
                    if !is_printable(c) && !is_whitespace(c) {
                        return Err(Error::new(i, "invalid character in a string literal"));
                    }
                    s.push(c);
                    i += 1;
                }
                out.push((start, Token::String(s)));
            }
            b'|' => {
                i += 1;
                let from = i;
                loop {
                    if i >= src.len() {
                        return Err(Error::new(start, "unterminated quoted symbol"));
                    }
                    let c = src[i];
                    if c == b'|' {
                        break;
                    }
                    if c == b'\\' || (!is_printable(c) && !is_whitespace(c)) {
                        return Err(Error::new(i, "invalid character in a quoted symbol"));
                    }
                    i += 1;
                }
                out.push((start, Token::Symbol(src[from..i].to_vec())));
                i += 1;
            }
            _ => {
                while i < src.len() && !ends_token(src[i]) {
                    i += 1;
                }
                out.push((start, classify(&src[start..i]).map_err(|m| Error::new(start, m))?));
            }
        }
    }
    Ok(out)
}
