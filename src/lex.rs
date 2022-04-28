use crate::cell::*;
use crate::error::*;

use std::iter::Iterator;
use std::fmt;

#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    EndOfInput,
    Word(Xsubstr),
    Literal(Xcell),
}

#[derive(Clone)]
pub struct TokenLocation {
    pub line: usize,
    pub col: usize,
    pub filename: Xstr,
    pub whole_line: Xsubstr,
    pub token: Xsubstr,
}

impl fmt::Debug for TokenLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}:{}:{}", self.filename, self.line + 1, self.col + 1)?;
        writeln!(f, "{}", self.whole_line)?;
        write!(f, "{:->1$}", '^', self.col + 1)
    }
}

#[derive(Clone)]
pub struct Lex {
    buf: Xstr,
    pos: usize,
    last_substr: Option<Xsubstr>,
    tmp: String,
}

const PARSE_INT_ERRMSG: Xstr = arcstr::literal!("parse int error");
const PARSE_FLOAT_ERRMSG: Xstr = arcstr::literal!("parse float error");
const EOF_ERRMSG: Xstr = arcstr::literal!("unexpected end of file");
const ESCAPE_SEQ_ERRMSG: Xstr = arcstr::literal!("unknown string escape sequence");
const EXPECT_WS_ERRMSG: Xstr = arcstr::literal!("expect whitespace word separator");

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
                    let c = self.take_char().ok_or_else(|| Xerr::ParseError {
                        msg: EOF_ERRMSG,
                        substr: self.buf.substr(..),
                        pos: self.pos
                    })?;
                    if c == '\\' {
                        let c2 = self.take_char().ok_or_else(|| Xerr::ParseError {
                            msg: EOF_ERRMSG,
                            substr: self.buf.substr(..),
                            pos: self.pos
                        })?;
                        match c2 {
                            '\\' => self.tmp.push(c2),
                            '\"' => self.tmp.push(c2),
                            'n' => self.tmp.push('\n'),
                            'r' => self.tmp.push('\r'),
                            _ => break Err(Xerr::ParseError {
                                    msg: ESCAPE_SEQ_ERRMSG,
                                    substr: self.buf.substr(..),
                                    pos: self.pos - 2,
                                })
                        }
                    } else if c == '"' {
                        let ss = self.buf.substr(start..self.pos);
                        self.last_substr = Some(ss);
                        let val = Xcell::Str(Xstr::from(&self.tmp));
                        let ws = self
                            .peek_char()
                            .map(|c| c.is_ascii_whitespace())
                            .unwrap_or(true);
                        if ws {
                            break Ok(Tok::Literal(val))
                        } else {
                            break Err(Xerr::ParseError {
                                msg: EXPECT_WS_ERRMSG,
                                substr: self.buf.substr(..),
                                pos: self.pos
                            })
                        }
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
                    if c.is_ascii_whitespace() {
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
                let val = if has_dot && radix == 10 {
                    if radix != 10 {
                        return Err(Xerr::ParseError {
                            msg: PARSE_FLOAT_ERRMSG,
                            substr: self.buf.substr(..),
                            pos: start,
                        });
                    }
                    let r: Xreal = self.tmp.parse().map_err(|_| Xerr::ParseError {
                        msg: PARSE_FLOAT_ERRMSG,
                        substr: self.buf.substr(..),
                        pos: start,
                    })?;
                    Cell::Real(r)
                } else {
                    let i = Xint::from_str_radix(&self.tmp, radix).map_err(|_| Xerr::ParseError {
                        msg:PARSE_INT_ERRMSG,
                        substr: self.buf.substr(..),
                        pos: start,
                    })?;
                    Cell::Int(i)
                };
                Ok(Tok::Literal(val))
            }
        }
    }

}

pub fn token_filename(sources: &[(Xstr, Xstr)], token: &Xsubstr) -> Option<Xstr> {
    sources
        .iter()
        .find(|x| &x.1 == token.parent())
        .map(|x| x.0.clone())
}

pub fn token_location(sources: &[(Xstr, Xstr)], token: &Xsubstr) -> Option<TokenLocation> {
    let filename = token_filename(sources, &token)?;
    let tok_start = token.range().start;
    let par = token.parent();
    let mut it = par.char_indices();
    let mut start = 0;
    let mut end = 1;
    let mut line = 0;
    let mut col = 0;
    while let Some((i, c)) = it.next() {
        end = i + c.len_utf8();
        if c == '\n' || c == '\r' {
            if (start..end).contains(&tok_start) {
                end = i;
                break;
            }
            if c == '\n' {
                line += 1;
            }
            start = end;
            col = 0;
        } else if i < tok_start {
            col += 1;
        }
    }
    let whole_line = token.parent().substr(start..end);
    Some(TokenLocation {
        line,
        col,
        filename,
        whole_line,
        token: token.clone(),
    })
}

pub struct XstrLines {
    buf: Xstr,
    pos: usize,
}
 
impl Iterator for XstrLines {
    type Item = Xsubstr;
    fn next(&mut self) -> Option<Xsubstr> {
        let start = self.pos;
        if start >= self.buf.len() {
            return None;
        }
        let mut it = self.buf[start..].char_indices();
        while let Some((i, c)) = it.next() {
             if c == '\n' {
                let end = start + i;
                let ss = self.buf.substr(start..end);
                self.pos = end + c.len_utf8();
                return Some(ss);
             }
         }
        let ss = self.buf.substr(start..);
        self.pos = self.buf.len();
        return Some(ss);
    }
}

impl XstrLines {
    pub fn new(buf: Xstr) -> XstrLines {
        Self { buf, pos: 0}
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

        assert!(tokenize_input( " \" xx\n ").is_err());
    }

    #[test]
    fn test_lex_nums() {
        let res = tokenize_input(" + -f -1 -x1 -0x1 +0").unwrap();
        assert_eq!(res, vec![word("+"),word("-f"),int(-1),word("-x1"),int(-1), int(0)]);

        let res = tokenize_input(" --1 -- + - . .0  -_").unwrap();
        assert_eq!(res, vec![word("--1"),word("--"), word("+"), word("-"), word("."), word(".0"),word("-_")]);

        let res = tokenize_input("0x00_ff 123_0_00_ 0b_1_1").unwrap();
        assert_eq!(res, vec![int(255), int(123000), int(3)]);

        assert!(tokenize_input("0f").is_err());
        assert!(tokenize_input("12-").is_err());
        assert!(tokenize_input("-0x").is_err());
        assert!(tokenize_input("-0b").is_err());
        assert!(tokenize_input("0_").is_err());
        assert!(tokenize_input("0x0.1").is_err());
        assert!(tokenize_input("0_.1").is_err());

        let res = tokenize_input("1.2 0.1_1").unwrap();
        assert_eq!(res, vec![real(1.2), real(0.11)]);
    }

    #[test]
    fn test_lex_escape() {
        let res = tokenize_input(r#""\\ \" \r \n""#).unwrap();
        assert_eq!(res, vec![str("\\ \" \r \n")]);

        match tokenize_input(r#" " \x " "#) {
            Err(Xerr::ParseError { msg, pos: 3,..}) => assert_eq!(msg, ESCAPE_SEQ_ERRMSG),
            e => panic!("{:?}", e)
        }
        match tokenize_input(r#""aaa\"#) {
            Err(Xerr::ParseError { msg, pos: 5,..}) => assert_eq!(msg, EOF_ERRMSG),
            e => panic!("{:?}", e)
        }
        match tokenize_input(r#""aaa\""#) {
            Err(Xerr::ParseError { msg, pos: 6,..}) => assert_eq!(msg, EOF_ERRMSG),
            e => panic!("{:?}", e)
        }
    }

    #[test]
    fn test_str_tok() {
        match tokenize_input(r#" 1"a" "#) {
            Err(Xerr::ParseError { msg, pos: 1,..}) => assert_eq!(msg, PARSE_INT_ERRMSG),
            e => panic!("{:?}", e)
        }
        match tokenize_input(r#" "a"2 "#) {
            Err(Xerr::ParseError { msg, pos: 4,..}) => assert_eq!(msg, EXPECT_WS_ERRMSG),
            e => panic!("{:?}", e)
        }
    }

    #[test]
    fn test_xstr_lines() {
        let mut it = XstrLines::new("1\nff\nddd".into());
        assert_eq!(it.next(), Some("1".into()));
        assert_eq!(it.next(), Some("ff".into()));
        assert_eq!(it.next(), Some("ddd".into()));
        assert_eq!(it.next(), None);
    }
}
