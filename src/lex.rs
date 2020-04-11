use crate::error::Xerr;

#[derive(Debug, PartialEq)]
pub enum Tok {
    EndOfInput,
    Word(String),
    Num(i64),
    SChar(char),
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
        Self::is_schar(c) || c == '"'
    }

    fn parse_word(&mut self) -> Result<Tok, Xerr> {
        let start = self.pos;
        let mut maybe_sign = None;
        while let Some((_, c)) = self.peek() {
            if Self::is_special(c) || c.is_ascii_whitespace() {
                break;
            }
            if maybe_sign.is_none() {
                maybe_sign = self.take();
                let is_digit = self.peek().map(|x| x.1.is_digit(10)).unwrap_or(false);
                if (c == '+' || c == '-') && is_digit {
                    return self.parse_number(maybe_sign);
                }
            } else {
                self.take();
            }
        }
        let w = self.src[start..self.pos].to_string();
        Ok(Tok::Word(w))
    }

    fn parse_number(&mut self, sign: Option<char>) -> Result<Tok, Xerr> {
        let mut start = self.pos;
        let a = self.take().unwrap();
        let base = match self.peek().map(|x| x.1).unwrap_or('_') {
            'x' | 'X' if a == '0' => {
                self.take().unwrap();
                start = self.pos;
                16
            }
            'b' | 'B' if a == '0' => {
                self.take().unwrap();
                start = self.pos;
                2
            }
            _ => 10,
        };
        while let Some((_, c)) = self.peek() {
            if c == '_' || c.is_digit(base) {
                self.take();
            } else if c.is_ascii_whitespace() {
                break;
            } else {
                return Err(Xerr::InputParseError);
            }
        }
        let s: String = self.src[start..self.pos]
            .chars()
            .filter(|&c| c != '_')
            .collect();
        i64::from_str_radix(&s, base)
            .map(|n| {
                Tok::Num(match sign {
                    Some('-') => -n,
                    _ => n,
                })
            })
            .map_err(|_| Xerr::InputParseError)
    }

    fn parse_string(&mut self) -> Result<Tok, Xerr> {
        Err(Xerr::InputIncomplete)
    }

    pub fn next(&mut self) -> Result<Tok, Xerr> {
        let c = loop {
            match self.skip_whitespaces() {
                None => return Ok(Tok::EndOfInput),
                Some('#') => self.skip_comment(),
                Some(c) => break c,
            }
        };
        match c {
            c if Self::is_schar(c) => {
                self.take().unwrap();
                Ok(Tok::SChar(c))
            }
            '0'..='9' => self.parse_number(None),
            '"' => self.parse_string(),
            _ => self.parse_word(),
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
    let mut lex = Lex::from_str("x1 + -1 -x1 +1_2_3");
    let t = lex.next().unwrap();
    assert_eq!(Tok::Word("x1".to_string()), t);
    assert_eq!((1, 3), lex.linecol());
    let t = lex.next().unwrap();
    assert_eq!(Tok::Word("+".to_string()), t);
    let t = lex.next().unwrap();
    assert_eq!(Tok::Num(-1), t);
    let t = lex.next().unwrap();
    assert_eq!(Tok::Word("-x1".to_string()), t);
    let t = lex.next().unwrap();
    assert_eq!(Tok::Num(123), t);
    let mut lex = Lex::from_str("0xff 0b11");
    let t = lex.next().unwrap();
    assert_eq!(Tok::Num(255), t);
    let t = lex.next().unwrap();
    assert_eq!(Tok::Num(3), t);
}
