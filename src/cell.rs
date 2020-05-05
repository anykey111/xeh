use crate::error::{Xerr, Xresult};
use crate::vm::VM;

pub type Xvec<T> = rpds::Vector<T>;
pub type Xlist<T> = rpds::List<T>;
pub type Xhashmap<K, V> = rpds::HashTrieMap<K, V>;
pub type XfnType = fn(&mut VM) -> Xresult;
pub type Xint = i64;
pub type Xreal = f64;

#[derive(Clone, Copy)]
pub struct Xfn(pub XfnType);

#[derive(Clone, PartialEq)]
pub enum Cell {
    Int(Xint),
    Real(Xreal),
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

impl Cell {
    pub fn to_usize(&self) -> Result<usize, Xerr> {
        match self {
            Cell::Int(i) => {
                if i.is_positive() {
                    Ok(*i as usize)
                } else {
                    Err(Xerr::IntegerOverflow)
                }
            }
            _other => Err(Xerr::TypeError),
        }
    }
}

pub const ZERO: Cell = Cell::Int(0);
