use crate::error::{Xerr, Xresult, Xresult1};
use crate::state::State;

pub type Xvec<T> = rpds::Vector<T>;
pub type Xmap = rpds::Vector<(Cell, Cell)>;
pub type Xhashmap<K, V> = rpds::HashTrieMap<K, V>;
pub type XfnType = fn(&mut State) -> Xresult;
pub type Xint = i128;
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
            Cell::Vector(v) => f.debug_list().entries(v.iter()).finish(),
            Cell::Map(v) => f.debug_list().entries(v.iter()).finish(),
            Cell::Fun(x) => write!(f, "{:?}", x),
            Cell::AnyRc(x) => match x.try_borrow() {
                Ok(p) => write!(f, "any:{:?}", p.type_id()),
                Err(_) => write!(f, "any"),
            },
        }
    }
}

impl fmt::Debug for Xfn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Xfn::Interp(x) => write!(f, "f:{:x}", x),
            Xfn::Native(x) => write!(f, "xf:{:#x}", *x as usize),
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

impl PartialEq for Cell {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Cell::Nil, Cell::Nil) => true,
            (Cell::Int(a), Cell::Int(b)) => a == b,
            (Cell::Real(a), Cell::Real(b)) => a == b,
            (Cell::Str(a), Cell::Str(b)) => a == b,
            (Cell::Vector(a), Cell::Vector(b)) => a == b,
            (Cell::Map(a), Cell::Map(b)) => a == b,
            (Cell::Fun(a), Cell::Fun(b)) => a == b,
            _ => false,
        }
    }
}

impl Cell {
    pub fn to_address(self) -> Xresult1<usize> {
        let i: Xint = self.try_into()?;
        if i.is_positive() {
            Ok(i as usize)
        } else {
            Err(Xerr::IntegerOverflow)
        }
    }

    pub fn is_true(&self) -> bool {
        match self {
            Cell::Nil | Cell::Int(0) => false,
            _ => true,
        }
    }

    pub fn into_string(self) -> Xresult1<String> {
        match self {
            Cell::Str(s) => Ok(s),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn into_vector(self) -> Result<Xvec<Cell>, Xerr> {
        match self {
            Cell::Vector(x) => Ok(x),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn into_map(self) -> Xresult1<Xmap> {
        match self {
            Cell::Map(x) => Ok(x),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn into_real(self) -> Xresult1<Xreal> {
        match self {
            Cell::Real(x) => Ok(x),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn into_any(self) -> Xresult1<Xanyrc> {
        match self {
            Cell::AnyRc(rc) => Ok(rc),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn into_int(self) -> Xresult1<Xint> {
        match self {
            Cell::Int(i) => Ok(i),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn into_i64(self) -> Xresult1<i64> {
        self.into_int().map(|i| i as i64)
    }

    pub fn into_usize(self) -> Xresult1<usize> {
        self.into_int().map(|i| i as usize)
    }

    pub fn from_any<T>(val: T) -> Self
    where
        T: 'static,
    {
        Cell::AnyRc(std::rc::Rc::new(std::cell::RefCell::new(val)))
    }
}

impl From<usize> for Cell {
    fn from(x: usize) -> Self {
        Cell::Int(x as i128)
    }
}

impl From<isize> for Cell {
    fn from(x: isize) -> Self {
        Cell::Int(x as i128)
    }
}

impl From<u32> for Cell {
    fn from(x: u32) -> Self {
        Cell::Int(x as i128)
    }
}

impl From<f32> for Cell {
    fn from(x: f32) -> Self {
        Cell::Real(x as f64)
    }
}

impl From<f64> for Cell {
    fn from(x: f64) -> Self {
        Cell::Real(x)
    }
}

impl From<bool> for Cell {
    fn from(x: bool) -> Self {
        if x { ONE } else { ZERO }
    }
}

use std::convert::TryInto;

impl TryInto<f64> for Cell {
    type Error = Xerr;
    fn try_into(self) -> Result<f64, Self::Error> {
        match self {
            Cell::Real(r) => Ok(r),
            _ => Err(Xerr::TypeError),
        }
    }
}

impl TryInto<f32> for Cell {
    type Error = Xerr;
    fn try_into(self) -> Result<f32, Self::Error> {
        let r: f64 = self.try_into()?;
        Ok(r as f32)
    }
}

impl TryInto<Xint> for Cell {
    type Error = Xerr;
    fn try_into(self) -> Result<Xint, Self::Error> {
        match self {
            Cell::Int(i) => Ok(i),
            _ => Err(Xerr::TypeError),
        }
    }
}

impl TryInto<usize> for Cell {
    type Error = Xerr;
    fn try_into(self) -> Result<usize, Self::Error> {
        let i: Xint = self.try_into()?;
        Ok(i as usize)
    }
}

impl TryInto<isize> for Cell {
    type Error = Xerr;
    fn try_into(self) -> Result<isize, Self::Error> {
        let i: Xint = self.try_into()?;
        Ok(i as isize)
    }
}

impl TryInto<bool> for Cell {
    type Error = Xerr;
    fn try_into(self) -> Result<bool, Self::Error> {
        Ok(match self {
            Cell::Nil | Cell::Int(0) => false,
            _ => true,
        })
    }
}

pub const ZERO: Cell = Cell::Int(0);
pub const ONE: Cell = Cell::Int(1);
