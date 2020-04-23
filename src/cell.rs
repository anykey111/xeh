use crate::vm::VM;
use crate::error::Xresult;

pub type Xvec<T> = rpds::Vector<T>;
pub type Xlist<T> = rpds::List<T>;
pub type Xhashmap<K, V> = rpds::HashTrieMap<K, V>;
pub type XfnType = fn(&mut VM) -> Xresult;

#[derive(Clone)]
pub struct Xfn(pub XfnType);

#[derive(Clone, PartialEq)]
pub enum Cell {
    Int(i64),
    Real(f64),
    Str(String),
    InterpFn(usize),
    NativeFn(Xfn),
}

use std::fmt;

impl fmt::Debug for Cell {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<XEH Cell>")
    }
}

impl fmt::Debug for Xfn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {

        write!(f, "{:?}", self.0 as usize)
    }
}

impl PartialEq for Xfn {
    fn eq(&self, other: &Self) -> bool {
        self.0 as usize == other.0 as usize
    }
}

pub const ZERO: Cell = Cell::Int(0);
