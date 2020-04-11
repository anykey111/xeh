use num_bigint::{BigInt, ToBigInt};

use crate::error::Xerr;

#[derive(Debug, PartialEq)]
pub enum Tok {
    EndOfInput,
    Word(String),
    Num(BigInt),
    Str(String),
}

pub struct Lex {
    line: usize,
    col: usize,
    pos: usize,
    src: String,
}

impl Lex {
    pub fn from_str(s: &str) -> Self {
        Self {
            line: 1,
            col: 1,
            pos: 0,
            src: s.to_string(),
        }
    }

    pub fn push_str(&mut self, s: &str) {
        self.src.push_str(s);
    }

    pub fn linecol(&self) -> (usize, usize) {
        (self.line, self.col)
    }

    fn peek(&self) -> Option<(usize, char)> {
        let mut it = self.src[self.pos..].char_indices();
        let x = it.next()?;
        match (x, it.next()) {
            ((i, c), Some((i2, _c2))) => Some((i2 - i, c)),
            ((_, c), None) => Some((self.src.len() - self.pos, c)),
        }
    }

    fn take(&mut self) -> Option<char> {
        let x = self.peek()?;
        self.pos += x.0;
        if x.1 == '\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
        Some(x.1)
    }

    fn skip_whitespaces(&mut self) -> Option<char> {
        loop {
            let (_, c) = self.peek()?;
            if c.is_ascii_whitespace() {
                self.take();
            } else {
                break Some(c);
            }
        }
    }

    fn skip_comment(&mut self) {
        loop {
            match self.take() {
                None | Some('\n') => break,
                _ => continue,
            }
        }
    }

    fn is_schar(c: char) -> bool {
        match c {
            '(' | ')' | '[' | ']' | '{' | '}' => true,
            _ => false,
        }
    }

    fn is_special(c: char) -> bool {
        Self::is_schar(c) || c == '"' || c == '#'
    }

    fn parse_word(&mut self) -> Result<Tok, Xerr> {
        let start = self.pos;
        while let Some((_, c)) = self.peek() {
            if c.is_ascii_whitespace() || Self::is_special(c) {
                if self.pos == start && Self::is_schar(c) {
                    self.take();
                }
                break;
            }
            self.take();
        }
        let w = &self.src[start..self.pos];
        // maybe number
        let mut it = w.chars();
        let mut x = it.next();
        let mut sign_minus = false;
        if x == Some('+') {
            x = it.next();
        } else if x == Some('-') {
            sign_minus = true;
            x = it.next();
        }
        let mut digits: Vec<u8> = Vec::new();
        match x {
            Some(c) if c.is_digit(10) => {
                if sign_minus {
                    digits.push('-' as u8);
                }
                digits.push(c as u8);
            }
            _ => return Ok(Tok::Word(w.to_string())),
        }
        let mut radix = 10;
        if x == Some('0') {
            match it.next() {
                Some('x') | Some('X') => radix = 16,
                Some('b') | Some('B') => radix = 2,
                Some(c) if c.is_digit(10) => {
                    digits.push('0' as u8);
                    digits.push(c as u8);
                }
                None => digits.push('0' as u8),
                _ => {
                    self.pos = start;
                    return Err(Xerr::InputParseError);
                }
            }
        }
        while let Some(c) = it.next() {
            if c == '_' {
                continue;
            }
            if c.is_digit(radix) {
                digits.push(c as u8);
            } else {
                self.pos = start;
                return Err(Xerr::InputParseError);
            }
        }
        if let Some(i) = BigInt::parse_bytes(&digits, radix) {
            return Ok(Tok::Num(i));
        }
        self.pos = start;
        return Err(Xerr::InputParseError);
    }

    fn parse_string(&mut self) -> Result<Tok, Xerr> {
        let start = self.pos;
        self.take();
        let mut s = String::new();
        loop {
            match self.take() {
                None => {
                    self.pos = start;
                    return Err(Xerr::InputIncomplete);
                }
                Some('"') => break,
                Some(c) => {
                    if c != '\n' {
                        s.push(c);
                    }
                }
            }
        }
        Ok(Tok::Str(s))
    }

    pub fn next(&mut self) -> Result<Tok, Xerr> {
        let c = loop {
            match self.skip_whitespaces() {
                None => return Ok(Tok::EndOfInput),
                Some('#') => self.skip_comment(),
                Some(c) => break c,
            }
        };
        if c == '"' {
            self.parse_string()
        } else {
            self.parse_word()
        }
    }
}

#[test]
fn test_lex_ws() {
    let mut lex = Lex::from_str("\n\t");
    assert_eq!(Ok(Tok::EndOfInput), lex.next());
    assert_eq!((2, 2), lex.linecol());
    let mut lex = Lex::from_str("\n\t#567");
    assert_eq!(Ok(Tok::EndOfInput), lex.next());
    assert_eq!((2, 6), lex.linecol());
    let mut lex = Lex::from_str("a#b");
    assert_eq!(Ok(Tok::Word("a".to_string())), lex.next());
}

#[test]
fn test_lex_num() {
    let mut lex = Lex::from_str("x1 + - -1 -x1 -0x1 +0 0b11 0xff_00");
    assert_eq!(Tok::Word("x1".to_string()), lex.next().unwrap());
    assert_eq!((1, 3), lex.linecol());
    assert_eq!(Tok::Word("+".to_string()), lex.next().unwrap());
    assert_eq!(Tok::Word("-".to_string()), lex.next().unwrap());
    assert_eq!(Tok::Num((-1).to_bigint().unwrap()), lex.next().unwrap());
    assert_eq!(Tok::Word("-x1".to_string()), lex.next().unwrap());
    assert_eq!(Tok::Num((-1).to_bigint().unwrap()), lex.next().unwrap());
    assert_eq!(Tok::Num((0).to_bigint().unwrap()), lex.next().unwrap());
    assert_eq!(Tok::Num((3).to_bigint().unwrap()), lex.next().unwrap());
    assert_eq!(Tok::Num((0xff00).to_bigint().unwrap()), lex.next().unwrap());
}

#[test]
fn text_lex_schar() {
    let mut lex = Lex::from_str("({aa : +[bb]cc)");
    assert_eq!(Ok(Tok::Word("(".to_string())), lex.next());
    assert_eq!(Ok(Tok::Word("{".to_string())), lex.next());
    assert_eq!(Ok(Tok::Word("aa".to_string())), lex.next());
    assert_eq!(Ok(Tok::Word(":".to_string())), lex.next());
    assert_eq!(Ok(Tok::Word("+".to_string())), lex.next());
    assert_eq!(Ok(Tok::Word("[".to_string())), lex.next());
    assert_eq!(Ok(Tok::Word("bb".to_string())), lex.next());
    assert_eq!(Ok(Tok::Word("]".to_string())), lex.next());
    assert_eq!(Ok(Tok::Word("cc".to_string())), lex.next());
    assert_eq!(Ok(Tok::Word(")".to_string())), lex.next());
}

#[test]
fn test_lex_str() {
    let mut lex = Lex::from_str(" \"))\n[[\" ");
    assert_eq!(Ok(Tok::Str("))[[".to_string())), lex.next());

    let mut lex = Lex::from_str(" \" xx\n ");
    assert_eq!(Err(Xerr::InputIncomplete), lex.next());
    lex.push_str("\"");
    assert_eq!(Ok(Tok::Str(" xx ".to_string())), lex.next());
}
