use crate::cell::*;
use crate::error::*;

use std::fmt;
use std::iter::Iterator;

#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    EndOfInput,
    Word(Xsubstr),
    Literal(Xcell),
}

#[derive(Clone, PartialEq)]
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
    tmp: String,
    start_pos: usize,
}

const PARSE_INT_ERRMSG: Xstr = xstr_literal!("parse int error");
const PARSE_FLOAT_ERRMSG: Xstr = xstr_literal!("parse float error");
const PARSE_BITSTR_ERRMSG: Xstr = xstr_literal!("parse bitstr error");
const UNTERMINATED_STR_ERRMSG: Xstr = xstr_literal!("unterminated string");
const UNTERMINATED_BITSTR_ERRMSG: Xstr = xstr_literal!("unterminated bit-string");
const ESCAPE_SEQ_ERRMSG: Xstr = xstr_literal!("unknown string escape sequence");
const EXPECT_WS_ERRMSG: Xstr = xstr_literal!("expect whitespace word separator");

impl Lex {
    pub fn new(buf: Xstr) -> Lex {
        Self {
            buf,
            pos: 0,
            start_pos: 0,
            tmp: String::new(),
        }
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

    pub fn last_substr(&self) -> Xsubstr {
        self.buf.substr(self.start_pos..self.pos)
    }

    pub fn next(&mut self) -> Xresult1<Tok> {
        self.skip_whitespaces();
        self.start_pos = self.pos;
        let start = self.pos;
        match self.take_char() {
            None => Ok(Tok::EndOfInput),
            Some('"') | Some('“') => {
                self.tmp.clear();
                loop {
                    let c_pos = self.pos;
                    let c = self.take_char().ok_or_else(|| Xerr::ParseError {
                        msg: UNTERMINATED_STR_ERRMSG,
                        substr: self.buf.substr(c_pos..),
                    })?;
                    if c == '\\' {
                        let c2 = self.take_char().ok_or_else(|| Xerr::ParseError {
                            msg: UNTERMINATED_STR_ERRMSG,
                            substr: self.buf.substr(c_pos..),
                        })?;
                        match c2 {
                            '\\' => self.tmp.push(c2),
                            '"' => self.tmp.push(c2),
                            'n' => self.tmp.push('\n'),
                            'r' => self.tmp.push('\r'),
                            't' => self.tmp.push('\t'),
                            _ => {
                                break Err(Xerr::ParseError {
                                    msg: ESCAPE_SEQ_ERRMSG,
                                    substr: self.buf.substr(c_pos..self.pos),
                                })
                            }
                        }
                    } else if c == '"' || c == '”' {
                        let val = Xcell::Str(Xstr::from(&self.tmp));
                        let ws = self
                            .peek_char()
                            .map(|c| c.is_ascii_whitespace())
                            .unwrap_or(true);
                        if ws {
                            break Ok(Tok::Literal(val));
                        } else {
                            break Err(Xerr::ParseError {
                                msg: EXPECT_WS_ERRMSG,
                                substr: self.buf.substr(start..self.pos),
                            });
                        }
                    } else {
                        self.tmp.push(c);
                    }
                }
            }
            Some('|') => {
                let mut builder = crate::bitstr::BitvecBuilder::default();
                loop {
                    let c_pos = self.pos;
                    let c = self.take_char().ok_or_else(|| Xerr::ParseError {
                        msg: UNTERMINATED_BITSTR_ERRMSG,
                        substr: self.buf.substr(c_pos..),
                    })?;
                    if let Some(x) = c.to_digit(16) {
                        for i in (0..4).rev() {
                            builder.append_bit(((x >> i) as u8) & 1);
                        }
                    } else if c.is_ascii_whitespace() {
                        continue;
                    } else if c == '-' {
                        builder.append_bit(0);
                    } else if c == 'x' {
                        builder.append_bit(1);
                    } else if c == '|' {
                        let bs = builder.finish();
                        return Ok(Tok::Literal(Cell::from(bs)));
                    } else {
                        return Err(Xerr::ParseError {
                            msg: PARSE_BITSTR_ERRMSG,
                            substr: self.buf.substr(c_pos..),
                        });
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
                let substr = self.buf.substr(start..self.pos);
                if !num_prefix {
                    return Ok(Tok::Word(substr));
                }
                let val = if has_dot && radix == 10 {
                    if radix != 10 {
                        return Err(Xerr::ParseError {
                            msg: PARSE_FLOAT_ERRMSG,
                            substr,
                        });
                    }
                    let r: Xreal = self.tmp.parse().map_err(|_| Xerr::ParseError {
                        msg: PARSE_FLOAT_ERRMSG,
                        substr,
                    })?;
                    Cell::Real(r)
                } else {
                    let i =
                        Xint::from_str_radix(&self.tmp, radix).map_err(|_| Xerr::ParseError {
                            msg: PARSE_INT_ERRMSG,
                            substr,
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
        Self { buf, pos: 0 }
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

        assert!(tokenize_input(" \" xx\n ").is_err());
    }

    #[test]
    fn test_lex_nums() {
        let res = tokenize_input(" + -f -1 -x1 -0x1 +0").unwrap();
        assert_eq!(
            res,
            vec![word("+"), word("-f"), int(-1), word("-x1"), int(-1), int(0)]
        );

        let res = tokenize_input(" --1 -- + - . .0  -_").unwrap();
        assert_eq!(
            res,
            vec![
                word("--1"),
                word("--"),
                word("+"),
                word("-"),
                word("."),
                word(".0"),
                word("-_")
            ]
        );

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
        let res = tokenize_input(r#""\\ \" \r \t \n""#).unwrap();
        assert_eq!(res, vec![str("\\ \" \r \t \n")]);

        match tokenize_input(r#" " \x " "#) {
            Err(Xerr::ParseError { msg, substr }) => {
                assert_eq!(substr.range(), 3..5);
                assert_eq!(msg, ESCAPE_SEQ_ERRMSG);
            }
            e => panic!("{:?}", e),
        }
        match tokenize_input(r#""aaa\"#) {
            Err(Xerr::ParseError { msg, substr }) => {
                assert_eq!(substr, "\\");
                assert_eq!(substr.range(), 4..5);
                assert_eq!(msg, UNTERMINATED_STR_ERRMSG);
            }
            e => panic!("{:?}", e),
        }
        match tokenize_input(r#""aaa\""#) {
            Err(Xerr::ParseError { msg, substr }) => {
                assert_eq!(substr.range(), 6..6);
                assert_eq!(msg, UNTERMINATED_STR_ERRMSG);
            }
            e => panic!("{:?}", e),
        }
    }

    #[test]
    fn test_str_tok() {
        match tokenize_input(r#" 1"a" "#) {
            Err(Xerr::ParseError { msg, substr }) => {
                assert_eq!(substr, "1\"a\"");
                assert_eq!(substr.range(), 1..5);
                assert_eq!(msg, PARSE_INT_ERRMSG);
            }
            e => panic!("{:?}", e),
        }
        match tokenize_input(r#" "abc"2 "#) {
            Err(Xerr::ParseError { msg, substr }) => {
                assert_eq!(substr.range(), 1..6);
                assert_eq!(msg, EXPECT_WS_ERRMSG);
            }
            e => panic!("{:?}", e),
        }
    }

    #[test]
    fn test_bitstr_literal() {
        let res = tokenize_input("|FF|  |x--x| | 77 -- f |").unwrap();
        let mut it = res.iter();

        let s1 = Xbitstr::from_bin_str("1111 1111").unwrap();
        assert_eq!(&Tok::Literal(Cell::from(s1)), it.next().unwrap());
        
        let s2 = Xbitstr::from_bin_str("1001").unwrap();
        assert_eq!(&Tok::Literal(Cell::from(s2)), it.next().unwrap());

        let s3 = Xbitstr::from_bin_str("0111 0111 00 1111").unwrap();
        assert_eq!(&Tok::Literal(Cell::from(s3)), it.next().unwrap());
        
        match Lex::new(Xstr::from(" | f")).next() {
            Err(Xerr::ParseError { msg,..}) => assert_eq!(msg, UNTERMINATED_BITSTR_ERRMSG),
            other => panic!("{:?}", other),
        }

        match Lex::new(Xstr::from(" | ff g| ")).next() {
            Err(Xerr::ParseError { msg, substr}) => {
                assert_eq!(msg, PARSE_BITSTR_ERRMSG);
                assert_eq!(substr.range().start, 6);
            },
            other => panic!("{:?}", other),
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
