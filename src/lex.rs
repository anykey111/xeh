use crate::{cell::{Xint, Xreal}, prelude::*};
use crate::error::*;

#[derive(Debug, PartialEq)]
pub enum Tok {
    EndOfInput,
    Word(String),
    Key(String),
    Num(Xint),
    Real(Xreal),
    Str(String),
    Bstr(Xbitstr),
}

#[derive(Clone, Debug, PartialEq)]
struct Location {
    line: usize,
    col: usize,
    pos: usize,
    len: usize,
}

#[derive(Clone, Debug)]
pub struct Lex {
    cursor: Location,
    buffer: String,
    last: Option<Location>,
    source_id: u32,
}

fn is_bracket(c: char) -> bool {
    match c {
        '(' | ')' | '[' | ']' | '{' | '}' => true,
        _ => false,
    }
}

fn is_special(c: char) -> bool {
    is_bracket(c) || c == '"' || c == '#'
}

impl Lex {

    pub fn new(buffer: String, source_id: u32) -> Lex {
        Self {
            cursor: Location {
                line: 1,
                col: 1,
                pos: 0,
                len: 0,
            },
            buffer,
            last: None,
            source_id,
        }
    }

    pub fn source_id(&self) -> u32 {
        self.source_id
    }

    pub fn last_token(&self) -> Option<(&str, usize, usize)> {
        self.last.as_ref().map(|loc| {
            let start = loc.pos;
            let end = start + loc.len;
            (&self.buffer[start..end], loc.line, loc.col)
        })
    }

    fn peek(&self) -> Option<(usize, char)> {
        let mut it = self.buffer[self.cursor.pos..].char_indices();
        let x = it.next()?;
        match (x, it.next()) {
            ((i, c), Some((i2, _c2))) => Some((i2 - i, c)),
            ((_, c), None) => Some((self.buffer.len() - self.cursor.pos, c)),
        }
    }

    fn take(&mut self) -> Option<char> {
        let x = self.peek()?;
        self.cursor.pos += x.0;
        if x.1 == '\n' {
            self.cursor.line += 1;
            self.cursor.col = 1;
        } else {
            self.cursor.col += 1;
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

    fn parse_word(&mut self) -> Xresult1<Tok> {
        let start = self.cursor.pos;
        let mut loc = self.cursor.clone();
        while let Some((_, c)) = self.peek() {
            if c.is_ascii_whitespace() || is_special(c) {
                if self.cursor.pos == start && is_bracket(c) {
                    self.take();
                }
                break;
            }
            self.take();
        }
        let w = &self.buffer[start..self.cursor.pos];
        loc.len = self.cursor.pos - start;
        self.last = Some(loc);
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
        let mut digits = String::with_capacity(w.len());
        match x {
            Some(c) if c.is_digit(10) => {
                if sign_minus {
                    digits.push('-');
                }
                digits.push(c);
            }
            _ => if w.ends_with(':') && w.len() > 1 {
                let mut k = w.to_string();
                k.pop();
                return Ok(Tok::Key(k));
            } else {
                return Ok(Tok::Word(w.to_string()))
            },
        }
        let mut radix = 10;
        if x == Some('0') {
            match it.next() {
                Some('x') => radix = 16,
                Some('b') => radix = 2,
                Some('s') => {
                    let mut tmp = Xbitstr::new();
                    let s0 = Xbitstr::from_u64(0, 1, LITTLE);
                    let s1 = Xbitstr::from_u64(1, 1, BIG);
                    while let Some(c) = it.next() {
                        match c {
                            '_' => continue,
                            '0' => tmp = tmp.append(&s0),
                            '1' => tmp = tmp.append(&s1),
                            _ => Err(Xerr::InputParseError)?,
                        }
                    };
                    return Ok(Tok::Bstr(tmp));
                }
                Some(c) => {
                    if c.is_digit(10) {
                        digits.push('0');
                        digits.push(c);
                    } else {
                        digits.push(c);
                    }
                }
                None => digits.push('0'),
            }
        }
        while let Some(c) = it.next() {
            if c == '_' {
                continue;
            }
            digits.push(c);
        }
        Xint::from_str_radix(&digits, radix)
            .map(|n| Tok::Num(n))
            .or(w.parse::<Xreal>().map(|r| Tok::Real(r)))
            .map_err(|_| Xerr::InputParseError)
    }

    fn parse_string(&mut self) -> Xresult1<Tok> {
        let start = self.cursor.pos;
        let mut loc = self.cursor.clone();
        self.take();
        let mut s = String::new();
        loop {
            match self.take() {
                None => {
                    loc.len = self.cursor.pos - start;
                    self.last = Some(loc);
                    self.cursor.pos = start;
                    return Err(Xerr::InputIncomplete);
                }
                Some('\\') => {
                    let c = self.take().ok_or(Xerr::InputParseError)?;
                    match c {
                        '\\' => s.push(c),
                        '\"' => s.push(c),
                        'n' => s.push('\n'),
                        'r' => s.push('\r'),
                        _ => return Err(Xerr::InputParseError),
                    }
                },
                Some('"') => break,
                Some(c) => {
                    if c != '\n' {
                        s.push(c);
                    }
                }
            }
        }
        loc.len = self.cursor.pos - start;
        self.last = Some(loc);
        Ok(Tok::Str(s))
    }

    pub fn next(&mut self) -> Xresult1<Tok> {
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

#[cfg(test)]
mod tests {
    use super::*;

    fn new_test_lex(s: &str) -> Lex {
        Lex::new(s.to_string(), 0)
    }

    #[test]
    fn test_lex_ws() {
        let mut lex = new_test_lex("\n\t");
        assert_eq!(Ok(Tok::EndOfInput), lex.next());
        assert_eq!(None, lex.last_token());
        let mut lex = new_test_lex("\n\t#567");
        assert_eq!(Ok(Tok::EndOfInput), lex.next());
        assert_eq!(None, lex.last_token());
        let mut lex = new_test_lex("a#b");
        assert_eq!(Ok(Tok::Word("a".to_string())), lex.next());
        let mut lex = new_test_lex(" abcde \n123");
        lex.next().unwrap();
        assert_eq!(("abcde", 1, 2), lex.last_token().unwrap());
        lex.next().unwrap();
        assert_eq!(("123", 2, 1), lex.last_token().unwrap());
    }

    #[test]
    fn test_lex_num() {
        let mut lex = new_test_lex("x1 + - -1 -x1 -0x1 +0 0b11 0xff_00");
        assert_eq!(Tok::Word("x1".to_string()), lex.next().unwrap());
        assert_eq!(Tok::Word("+".to_string()), lex.next().unwrap());
        assert_eq!(Tok::Word("-".to_string()), lex.next().unwrap());
        assert_eq!(Tok::Num(-1), lex.next().unwrap());
        assert_eq!(Tok::Word("-x1".to_string()), lex.next().unwrap());
        assert_eq!(Tok::Num(-1), lex.next().unwrap());
        assert_eq!(Tok::Num(0), lex.next().unwrap());
        assert_eq!(Tok::Num(3), lex.next().unwrap());
        assert_eq!(Tok::Num(0xff00), lex.next().unwrap());
        let mut lex = new_test_lex("--1 1- 0x1x 0x1G3");
        assert_eq!(Tok::Word("--1".to_string()), lex.next().unwrap());
        assert_eq!(Err(Xerr::InputParseError), lex.next());
        assert_eq!(Err(Xerr::InputParseError), lex.next());
        assert_eq!(Err(Xerr::InputParseError), lex.next());
    }

    #[test]
    fn test_lex_real() {
        let mut lex = new_test_lex("1e5 0.5 1.5");
        assert_eq!(Tok::Real(100000.0), lex.next().unwrap());
        assert_eq!(Tok::Real(0.5), lex.next().unwrap());
        assert_eq!(Tok::Real(1.5), lex.next().unwrap());
        assert_eq!(Err(Xerr::InputParseError), new_test_lex("0.0.1").next());
    }

    #[test]
    fn text_lex_schar() {
        let mut lex = new_test_lex("({aa : +[bb]cc)");
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
        let mut lex = new_test_lex(" \"))\n[[\" ");
        assert_eq!(Ok(Tok::Str("))[[".to_string())), lex.next());
        let mut lex = new_test_lex(" \" xx\n ");
        assert_eq!(Err(Xerr::InputIncomplete), lex.next());
        lex.buffer.push_str("\"");
        assert_eq!(Ok(Tok::Str(" xx ".to_string())), lex.next());
    }

    #[test]
    fn test_lex_escape() {
        let mut lex = new_test_lex(r#""\\ \" \r \n""#);
        assert_eq!(Ok(Tok::Str("\\ \" \r \n".to_string())), lex.next());
        let mut lex = new_test_lex(r#" " \x " "#);
        assert_eq!(Err(Xerr::InputParseError), lex.next());
    }

    #[test]
    fn test_lex_bstr() {
        let mut lex = new_test_lex(" 0s001 0s10_01 0s 0s2");
        assert_eq!(Ok(Tok::Bstr(Xbitstr::from_str_bin("001").unwrap())), lex.next());
        assert_eq!(Ok(Tok::Bstr(Xbitstr::from_str_bin("1001").unwrap())), lex.next());
        assert_eq!(Ok(Tok::Bstr(Xbitstr::from_str_bin("").unwrap())), lex.next());
        assert_eq!(Err(Xerr::InputParseError), lex.next());
    }
}
