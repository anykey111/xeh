use crate::{lex::*};

struct SourceBuf {
    path: Option<String>,
    text: String,
}

#[derive(Default)]
pub struct DebugMap {
    code_map: Vec<(DebugInfo, Option<DebugLoc>)>,
    sources: Vec<SourceBuf>,
}

pub struct DebugLoc {
    pub source_id: u32,
    pub line: u32,
    pub col: u32,
}

#[derive(Debug, Clone, PartialEq)]
pub enum DebugInfo {
    Empty,
    Word(usize),
    Comment(&'static str),
    Local(String),
}

impl DebugMap {
    pub fn insert_with_source(&mut self, at: usize, dinfo: DebugInfo, lex: Option<&Lex>) {
        let pair = if dinfo == DebugInfo::Empty || lex.is_none() {
            (dinfo, None)
        } else {
            let mut dloc = None;
            let lex = lex.unwrap();
            if let Some((_, line, col)) = lex.last_token() {
                dloc = Some(DebugLoc {
                    source_id: lex.source_id(),
                    line: line as u32,
                    col: col as u32,
                });
            }
            (dinfo, dloc)
        };
        let len = self.code_map.len();
        if at < len {
            self.code_map[at] = pair;
        } else if at == len {
            self.code_map.push(pair)
        } else {
            panic!("non-linear allocation {}/{}", at, len);
        }
    }

    pub fn add_source(&mut self, text: &str, path: Option<String>) -> Lex {
        let id = self.sources.len();
        self.sources.push(SourceBuf {
            path,
            text: text.to_string(),
        });
        Lex::new(text.to_string(), id as u32)
    }

    pub fn find_debug_info(&self, at: usize) -> Option<&DebugInfo> {
        self.code_map.get(at).map(|x| &x.0)
    }

    pub fn find_debug_location(&self, at: usize) -> Option<&DebugLoc> {
        self.code_map.get(at).and_then(|x| x.1.as_ref())
    }

    pub fn format_lex_location(&self, lex: &Lex) -> String {
        use std::fmt::Write;
        let mut buf = String::new();
        if let Some((_tok, line, col)) = lex.last_token() {
            let id = lex.source_id();
            let srcbuf = &self.sources[id as usize];
            if let Some(path) = srcbuf.path.as_ref() {
                write!(buf, "{}:", path).unwrap();
            } else {
                write!(buf, "<buffer{}>:", id).unwrap();
            }
            writeln!(buf, "{}:{}:", line, col).unwrap();
            if let Some(s) = srcbuf.text.lines().nth(line - 1) {
                writeln!(buf, "{}", s).unwrap();
                for _ in 1..col {
                    buf.push('-');
                }
                buf.push('^');
            }
        }
        buf
    }

    pub fn format_location(&self, at: usize) -> Option<String> {
        self.find_debug_location(at).map(|dloc| {
            let src = &self.sources[dloc.source_id as usize].text;
            format!(
                "{}:{}:\n{}\n{}",
                dloc.line,
                dloc.col,
                src.lines().nth(dloc.line as usize - 1).unwrap(),
                format!("{:->1$}", '^', dloc.col as usize)
            )
        })
    }
}
