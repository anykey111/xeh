use crate::vm::VM;
use crate::error::Xresult;

pub type Xvec<T> = rpds::Vector<T>;
pub type Xlist<T> = rpds::List<T>;
pub type Xhashmap<K, V> = rpds::HashTrieMap<K, V>;
pub type XfnType = fn(&mut VM) -> Xresult;

#[derive(Clone, Copy)]
pub struct Xfn(pub XfnType);

#[derive(Clone, PartialEq)]
pub enum Cell {
    Int(i64),
    Real(f64),
    Str(String),
    Vector(Xvec<Cell>),
    InterpFn(usize),
    NativeFn(Xfn),
}

use std::fmt;

impl fmt::Debug for Cell {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Cell::Int(n) => write!(f, "{}", n),
            Cell::Real(r) => write!(f, "{}", r),
            Cell::Str(s) => write!(f, "{}", s),
            Cell::Vector(v) => write!(f, "{:?}", v),
            Cell::InterpFn(a) => write!(f, "{:0x}", a),
            Cell::NativeFn(x) => write!(f, "{:?}", x),
        }
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
