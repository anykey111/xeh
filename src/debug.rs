use crate::lex::*;

#[derive(Default)]
pub struct DebugMap {
    code_map: Vec<(DebugInfo, Option<DebugLoc>)>,
    sources: Vec<String>,
}

pub struct DebugLoc {
    pub source_id: usize,
    pub location: Location,
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
            if let Some((_, loc)) = lex.last_token() {
                if let Some(source_id) = lex.source_id() {
                    dloc = Some(DebugLoc {
                        source_id: source_id,
                        location: loc.clone(),
                    });
                }
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

    pub fn add_buffer(&mut self, buf: &String) -> usize {
        let id = self.sources.len();
        self.sources.push(buf.clone());
        id
    }

    pub fn find_debug_info(&self, at: usize) -> Option<&DebugInfo> {
        self.code_map.get(at).map(|x| &x.0)
    }

    pub fn find_debug_location(&self, at: usize) -> Option<&DebugLoc> {
        self.code_map.get(at).and_then(|x| {
            x.1.as_ref()
        })
    }

    pub fn format_location(&self, at: usize) -> Option<String> {
        self.find_debug_location(at).map(|dloc| {
            let src = &self.sources[dloc.source_id];
            let loc = &dloc.location;
            format!(
                "{}:{}:{}:\n{}\n{}",
                "none", loc.line, loc.col, src.lines().nth(loc.line - 1).unwrap(),
                format!("{:->1$}", '^', loc.col))
        })
    }
}
