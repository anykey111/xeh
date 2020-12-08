use crate::error::*;
use crate::cell::Xint;

#[derive(Debug, PartialEq)]
pub enum Tok {
    EndOfInput,
    Word(String),
    Num(Xint),
    Str(String),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Location {
    pub line: usize,
    pub col: usize,
    pub pos: usize,
    pub len: usize,
}

#[derive(Clone, Debug)]
pub struct Lex {
    cursor: Location,
    buffer: String,
    path: Option<String>,
    last: Option<Location>,
    source_id: Option<usize>,
}

impl Lex {
    pub fn from_str(s: &str) -> Self {
        Self::from_string(s.to_string())
    }

    pub fn from_string(s: String) -> Self {
        Self {
            cursor: Location {
                line: 1,
                col: 1,
                pos: 0,
                len: 0,
            },
            buffer: s,
            path: None,
            last: None,
            source_id: None,
        }
    }

    pub fn from_file(path: &str) -> Result<Self, std::io::Error> {
        let buf = std::fs::read_to_string(path)?;
        let mut lex = Self::from_string(buf);
        lex.path = Some(path.to_string());
        Ok(lex)
    }

    pub fn buffer(&mut self) -> &String {
        &self.buffer
    }

    pub fn set_source_id(&mut self, id: usize) {
        self.source_id = Some(id);
    }

    pub fn source_id(&self) -> Option<usize> {
        self.source_id
    }

    pub fn error_location(&self) -> String {
        let mut buf = String::new();
        if let Some((_tok, l)) = self.last_token() {
            let s = self.buffer.lines().nth(l.line - 1).unwrap();
            let name = self.path.as_ref().map(|p| p.as_str()).unwrap_or("<buffer>");
            buf = format!("{}:{}:{}:\n{}\n", name, l.line, l.col, s);
            for _ in 1..l.col {
                buf.push('-');
            }
            buf.push('^');
        }
        buf
    }

    pub fn last_token(&self) -> Option<(&str, &Location)> {
        self.last.as_ref().map(|loc| {
            let start = loc.pos;
            let end = start + loc.len;
            (&self.buffer[start..end], loc)
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

    fn is_schar(c: char) -> bool {
        match c {
            '(' | ')' | '[' | ']' | '{' | '}' | '!' => true,
            _ => false,
        }
    }

    fn is_special(c: char) -> bool {
        Self::is_schar(c) || c == '"' || c == '#'
    }

    fn parse_word(&mut self) -> Xresult1<Tok> {
        let start = self.cursor.pos;
        let mut loc = self.cursor.clone();
        while let Some((_, c)) = self.peek() {
            if c.is_ascii_whitespace() || Self::is_special(c) {
                if self.cursor.pos == start && Self::is_schar(c) {
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
                    return Ok(Tok::Word(w.to_string()));
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
                return Ok(Tok::Word(w.to_string()));
            }
        }
        let s = String::from_utf8_lossy(&digits);
        if let Some(i) = Xint::from_str_radix(&s, radix).ok() {
            return Ok(Tok::Num(i));
        }
        return Ok(Tok::Word(w.to_string()));
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

// tests ---------------------------------------------------------------------

#[test]
fn test_lex_ws() {
    let mut lex = Lex::from_str("\n\t");
    assert_eq!(Ok(Tok::EndOfInput), lex.next());
    assert_eq!(None, lex.last_token());
    let mut lex = Lex::from_str("\n\t#567");
    assert_eq!(Ok(Tok::EndOfInput), lex.next());
    assert_eq!(None, lex.last_token());
    let mut lex = Lex::from_str("a#b");
    assert_eq!(Ok(Tok::Word("a".to_string())), lex.next());
    let mut lex = Lex::from_str(" abcde \n123");
    lex.next().unwrap();
    let (s, loc) = lex.last_token().unwrap();
    assert_eq!(s, "abcde");
    assert_eq!(loc.len, 5);
    assert_eq!(loc.line, 1);
    assert_eq!(loc.col, 2);
    lex.next().unwrap();
    let (s, loc) = lex.last_token().unwrap();
    assert_eq!(s, "123");
    assert_eq!(loc.len, 3);
    assert_eq!(loc.line, 2);
    assert_eq!(loc.col, 1);
}

#[test]
fn test_lex_num() {
    let mut lex = Lex::from_str("x1 + - -1 -x1 -0x1 +0 0b11 0xff_00");
    assert_eq!(Tok::Word("x1".to_string()), lex.next().unwrap());
    assert_eq!(Tok::Word("+".to_string()), lex.next().unwrap());
    assert_eq!(Tok::Word("-".to_string()), lex.next().unwrap());
    assert_eq!(Tok::Num(-1), lex.next().unwrap());
    assert_eq!(Tok::Word("-x1".to_string()), lex.next().unwrap());
    assert_eq!(Tok::Num(-1), lex.next().unwrap());
    assert_eq!(Tok::Num(0), lex.next().unwrap());
    assert_eq!(Tok::Num(3), lex.next().unwrap());
    assert_eq!(Tok::Num(0xff00), lex.next().unwrap());
    let mut lex = Lex::from_str("--1 1- 0x1x");
    assert_eq!(Tok::Word("--1".to_string()), lex.next().unwrap());
    assert_eq!(Tok::Word("1-".to_string()), lex.next().unwrap());
    assert_eq!(Tok::Word("0x1x".to_string()), lex.next().unwrap());
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
    lex.buffer.push_str("\"");
    assert_eq!(Ok(Tok::Str(" xx ".to_string())), lex.next());
}
