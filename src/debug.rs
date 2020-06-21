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
        let pair = if dinfo == DebugInfo::Empty {
            (dinfo, None)
        } else {
            let mut dloc = None;
            if let Some(lex) = lex {
                if let Some((_, loc)) = lex.last_token() {
                    if let Some(source_id) = lex.source_id() {
                        dloc = Some(DebugLoc {
                            source_id: source_id,
                            location: loc.clone(),
                        });
                    }
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
        self.code_map.get(at).map(|x| x.1.as_ref().unwrap())
    }
}
