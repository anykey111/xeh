use crate::cell::*;
use crate::error::*;

#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    EndOfInput,
    Word(Xsubstr),
    Literal(Xcell),
}

#[derive(Clone)]
pub struct Lex {
    buf: Xstr,
    pos: usize,
    last_substr: Option<Xsubstr>,
    tmp: String,
}

impl Lex {
    pub fn new(buf: Xstr) -> Lex {
        Self { buf, pos: 0, last_substr: None, tmp: String::new() }
    }

    pub fn last_token(&self) -> Option<Xsubstr> {
        self.last_substr.clone()
    }

    fn peek_char(&self) -> Option<char> {
        self.buf[self.pos..].chars().next()
    }

    fn take_char(&mut self) -> Option<char> {
        let c = self.peek_char()?;
        self.pos += c.len_utf8();
        Some(c)
    }

    pub fn skip_line(&mut self) {
        while let Some(c) = self.take_char() {
            if c == '\n' {
                break;
            }
        }
    }

    fn skip_whitespaces(&mut self) {
        while let Some(c) = self.peek_char() {
            if c.is_ascii_whitespace() {
                self.take_char();
            } else {
                break;
            }
        }
    }

    pub fn next(&mut self) -> Xresult1<Tok> {
        self.skip_whitespaces();
        let start = self.pos;
        match self.take_char() {
            None => Ok(Tok::EndOfInput),
            Some('"') => {
                self.tmp.clear();
                loop {
                    let c = self.take_char().ok_or_else(|| Xerr::InputIncomplete)?;
                    if c == '\\' {
                        let c2 = self.take_char().ok_or_else(|| Xerr::InputIncomplete)?;
                        match c2 {
                            '\\' => self.tmp.push(c2),
                            '\"' => self.tmp.push(c2),
                            'n' => self.tmp.push('\n'),
                            'r' => self.tmp.push('\r'),
                            _ => break Err(Xerr::InputParseError),
                        }
                    } else if c == '"' {
                        let ss = self.buf.substr(start..self.pos);
                        self.last_substr = Some(ss);
                        let val = Xcell::Str(Xstr::from(&self.tmp));
                        break Ok(Tok::Literal(val))
                    } else {
                        self.tmp.push(c);
                    }
                }
            }
            Some(c) => {
                self.tmp.clear();
                let mut radix = 10;
                let mut has_dot = false;
                let mut num_prefix = false;
                if c.is_ascii_digit() {
                    self.tmp.push(c);
                    num_prefix = true;
                } else if c == '-' || c == '+' {
                    match self.peek_char() {
                        Some(c2) if c2.is_ascii_digit() => {
                            num_prefix = true;
                            self.tmp.push(c);
                            self.tmp.push(c2);
                            self.take_char();
                        }
                        _ => (),
                    }
                }
                if let Some('0') = self.tmp.chars().last() {
                    match self.peek_char() {
                        Some('b') => {
                            radix = 2;
                            self.take_char();
                            self.tmp.pop();
                        }
                        Some('x') | Some('_') => {
                            radix = 16;
                            self.take_char();
                            self.tmp.pop();
                        }
                        _ => (),
                    }
                }
                while let Some(c) = self.peek_char() {
                    if c.is_ascii_whitespace() || c == '"' {
                        break;
                    }
                    if num_prefix {
                        // prepare digits for parsing
                        if c == '.' {
                            has_dot = true;
                        }
                        if c != '_' {
                            self.tmp.push(c);
                        }
                    }
                    self.take_char();
                }
                let ss = self.buf.substr(start..self.pos);
                self.last_substr = Some(ss.clone());
                if !num_prefix {
                    return Ok(Tok::Word(ss));
                }
                let val = if has_dot {
                    if radix != 10 {
                        return Err(Xerr::InputParseError);
                    }
                    let r: Xreal = self.tmp.parse().map_err(|_x| {
                        //panic!("{:?}", (&self.tmp, x));
                        Xerr::InputParseError
                    })?;
                    Cell::Real(r)
                } else {
                    let i = Xint::from_str_radix(&self.tmp, radix).map_err(|_x| {
                        //panic!("{:?}", (&self.tmp, x));
                        Xerr::InputParseError
                    })?;
                    Cell::Int(i)
                };
                Ok(Tok::Literal(val))
            }
        }
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    fn word(s: &str) -> Tok {
        Tok::Word(Xstr::from(s).substr(..))
    }

    fn str(s: &str) -> Tok {
        Tok::Literal(Xcell::from(s))
    }

    fn int(i: Xint) -> Tok {
        Tok::Literal(Xcell::Int(i))
    }

    fn real(r: Xreal) -> Tok {
        Tok::Literal(Xcell::Real(r))
    }

    fn tokenize_input(s: &str) -> Xresult1<Vec<Tok>> {
        let mut it = Lex::new(Xstr::from(s));
        let mut res = Vec::new();
        loop {
            match it.next()? {
                Tok::EndOfInput => break Ok(res),
                t => res.push(t),
            }
        }
    }

    #[test]
    fn test_lex_tokenizer() {
        let res = tokenize_input("\n\t").unwrap();
        assert_eq!(res, vec![]);

        let res = tokenize_input("\n\t \r    \n ").unwrap();
        assert_eq!(res, vec![]);
          
        let res = tokenize_input("\n\t# 567").unwrap();
        assert_eq!(res, vec![word("#"), int(567)]);

        let res = tokenize_input("\n\t#123").unwrap();
        assert_eq!(res, vec![word("#123")]);
      
        let res = tokenize_input("a#b").unwrap();
        assert_eq!(res, vec![word("a#b")]);
        
        let res = tokenize_input(" abcde \n123").unwrap();
        assert_eq!(res, vec![word("abcde"), int(123)]);
    
        let res = tokenize_input("({aa : +[bb]cc)").unwrap();
        assert_eq!(res, vec![word("({aa"), word(":"), word("+[bb]cc)")]);

        let res = tokenize_input(" \"))\n[[\" ").unwrap();
        assert_eq!(res, vec![str("))\n[[")]);

        let res = tokenize_input( " \" xx\n ");
        assert_eq!(res, Err(Xerr::InputIncomplete));
    }

    #[test]
    fn test_lex_keys() {
        let res = tokenize_input(" a:1 x: 2").unwrap();
        assert_eq!(res, vec![word("a:1"),word("x:"),int(2)]);
    }

    #[test]
    fn test_lex_nums() {
        let res = tokenize_input(" + -f -1 -x1 -0x1 +0").unwrap();
        assert_eq!(res, vec![word("+"),word("-f"),int(-1),word("-x1"),int(-1), int(0)]);

        let res = tokenize_input(" --1 -- + - . .0  -_").unwrap();
        assert_eq!(res, vec![word("--1"),word("--"), word("+"), word("-"), word("."), word(".0"),word("-_")]);

        let res = tokenize_input("0x00_ff 123_0_00_ 0b_1_1").unwrap();
        assert_eq!(res, vec![int(255), int(123000), int(3)]);

        assert_eq!(Err(Xerr::InputParseError), tokenize_input("0f"));
        assert_eq!(Err(Xerr::InputParseError), tokenize_input("12-"));
        assert_eq!(Err(Xerr::InputParseError), tokenize_input("-0x"));
        assert_eq!(Err(Xerr::InputParseError), tokenize_input("-0b"));
        assert_eq!(Err(Xerr::InputParseError), tokenize_input("0_"));
        assert_eq!(Err(Xerr::InputParseError), tokenize_input("0x0.1"));
        assert_eq!(Err(Xerr::InputParseError), tokenize_input("0_.1"));

        let res = tokenize_input("1.2 0.1_1").unwrap();
        assert_eq!(res, vec![real(1.2), real(0.11)]);
    }

    #[test]
    fn test_lex_escape() {
        let res = tokenize_input(r#""\\ \" \r \n""#).unwrap();
        assert_eq!(res, vec![str("\\ \" \r \n")]);
        let res = tokenize_input(r#" " \x " "#);
        assert_eq!(res, Err(Xerr::InputParseError));
    }
}
