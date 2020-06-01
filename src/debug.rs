use crate::cell::*;

#[derive(Default)]
pub struct DebugMap {
    map: Vec<(Xfn, DebugInfo)>,
}

#[derive(Clone)]
pub enum DebugInfo {
    Empty,
    Word(usize),
    Comment(&'static str),
    Local(String),
}

impl DebugMap {
    pub fn insert(&mut self, addr: Xfn, dinfo: DebugInfo) {
        self.map.push((addr, dinfo));
    }

    pub fn find(&self, at: usize) -> Option<&DebugInfo> {
        self.map
            .iter()
            .rfind(|x| match x.0 {
                Xfn::Interp(a) => a == at,
                _ => false,
            })
            .map(|x| &x.1)
    }
}
