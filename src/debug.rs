use crate::{lex::*};
use std::fmt::Write;

struct SourceBuf {
    path: Option<String>,
    text: String,
}

#[derive(Default)]
pub struct DebugMap {
    code_map: Vec<Option<DebugLoc>>,
    sources: Vec<SourceBuf>,
}

pub struct DebugLoc {
    pub source_id: u32,
    pub line: u32,
    pub col: u32,
}

impl DebugMap {
    pub fn insert_with_source(&mut self, at: usize, lex: Option<&Lex>) {
        let mut dloc = None;
        if let Some(lex) = lex {
            let (line, col) = lex.location();
            dloc = Some(DebugLoc {
                source_id: lex.source_id(),
                line: line as u32,
                col: col as u32,
            });
        }
        let len = self.code_map.len();
        if at < len {
            self.code_map[at] = dloc;
        } else if at == len {
            self.code_map.push(dloc)
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

    pub fn format_lex_location(&self, lex: &Lex) -> String {
        let mut buf = String::new();
        let (line, col) = lex.location();
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
        buf
    }

    pub fn format_location(&self, at: usize) -> Option<String> {
        let item = self.code_map.get(at)?;
        let dloc = item.as_ref()?;
        let src = &self.sources[dloc.source_id as usize].text;
        let mut buf = String::new();
        writeln!(buf, "{}:{}:", dloc.line, dloc.col).unwrap();
        writeln!(buf, "{}", src.lines().nth(dloc.line as usize - 1).unwrap()).unwrap();
        writeln!(buf, "{:->1$}", '^', dloc.col as usize).unwrap();
        Some(buf)
    }
}
