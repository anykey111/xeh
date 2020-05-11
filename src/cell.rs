use crate::error::{Xerr, Xresult};
use crate::vm::VM;

pub type Xvec<T> = rpds::Vector<T>;
pub type Xmap = rpds::Vector<(Cell, Cell)>;
pub type Xhashmap<K, V> = rpds::HashTrieMap<K, V>;
pub type XfnType = fn(&mut VM) -> Xresult;
pub type Xint = i64;
pub type Xreal = f64;
pub type Xanyrc = std::rc::Rc<std::cell::RefCell<dyn std::any::Any>>;

#[derive(Clone)]
pub enum Xfn {
    Interp(usize),
    Native(XfnType),
}

#[derive(Clone)]
pub enum Cell {
    Nil,
    Int(Xint),
    Real(Xreal),
    Str(String),
    Vector(Xvec<Cell>),
    Map(Xmap),
    Fun(Xfn),
    AnyRc(Xanyrc),
}

use std::fmt;

impl fmt::Debug for Cell {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Cell::Nil => write!(f, "nil"),
            Cell::Int(n) => write!(f, "{}", n),
            Cell::Real(r) => write!(f, "{}", r),
            Cell::Str(s) => write!(f, "{}", s),
            Cell::Vector(v) => write!(f, "{:?}", v),
            Cell::Map(v) => write!(f, "{:?}", v),
            Cell::Fun(x) => write!(f, "{:?}", x),
            Cell::AnyRc(x) => {
                match x.try_borrow() {
                    Ok(p) => write!(f, "<{:?}>", p.type_id()),
                    Err(_) => write!(f, "<any>"),
                }
            }
        }
    }
}

impl fmt::Debug for Xfn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Xfn::Interp(x) => write!(f, "{:?}", x),
            Xfn::Native(x) => write!(f, "{:?}", *x as usize),
        }
    }
}

impl PartialEq for Xfn {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Xfn::Interp(a), Xfn::Interp(b)) => a == b,
            (Xfn::Native(a), Xfn::Native(b)) => *a as usize == *b as usize,
            _ => false,
        }
    }
}

impl Cell {
    pub fn to_usize(&self) -> Result<usize, Xerr> {
        let i = self.to_int()?;
        if i.is_positive() {
            Ok(i as usize)
        } else {
            Err(Xerr::IntegerOverflow)
        }
    }

    pub fn to_int(&self) -> Result<Xint, Xerr> {
        match self {
            Cell::Int(i) => Ok(*i),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn is_true(&self) -> bool {
        match self {
            Cell::Nil | Cell::Int(0) => false,
            _ => true,
        }
    }

    pub fn to_any(&self) -> Result<Xanyrc, Xerr> {
        match self {
            Cell::AnyRc(p) => Ok(p.clone()),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn from_any<T>(val: T) -> Self where T: 'static{
        Cell::AnyRc(std::rc::Rc::new(std::cell::RefCell::new(val)))
    }
}

pub const ZERO: Cell = Cell::Int(0);
