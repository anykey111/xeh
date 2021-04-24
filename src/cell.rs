use crate::error::{Xerr, Xresult, Xresult1};
use crate::state::State;

pub type Xvec = rpds::Vector<Cell>;
pub type Xmap = rpds::Vector<(Cell, Cell)>;
pub type Xhashmap<K, V> = rpds::HashTrieMap<K, V>;
pub type XfnType = fn(&mut State) -> Xresult;
pub type Xint = i128;
pub type Xreal = f64;
pub type Xanyrc = std::rc::Rc<std::cell::RefCell<dyn std::any::Any>>;
pub type Xbitstr = crate::bitstring::Bitstring;
pub type Xcell = Cell;

pub const BIG: crate::bitstring::Byteorder = crate::bitstring::Byteorder::BE;
pub const LITTLE: crate::bitstring::Byteorder = crate::bitstring::Byteorder::LE;

#[derive(Clone, Copy)]
pub struct XfnPtr(pub XfnType);

impl PartialEq for XfnPtr {
    fn eq(&self, other: &Self) -> bool {
        self.0 as usize == other.0 as usize
    }
}

#[derive(Clone, PartialEq)]
pub enum Xfn {
    Interp(usize),
    Native(XfnPtr),
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Xref {
    None,
    Heap(usize),
    Word(usize),
}

impl Default for Xref {
    fn default() -> Self {
        Xref::None
    }
}

#[derive(Clone)]
pub enum Cell {
    Nil,
    Int(Xint),
    Real(Xreal),
    Str(String),
    Key(String),
    Vector(Xvec),
    Map(Xmap),
    Fun(Xfn),
    Ref(Xref),
    Bitstr(Xbitstr),
    AnyRc(Xanyrc),
}

use std::fmt;

impl fmt::Debug for XfnPtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:#x}", self.0 as usize)
    }
}

impl fmt::Debug for Cell {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Cell::Nil => write!(f, "nil"),
            Cell::Int(n) => match f.width().unwrap_or(10) {
                2 => write!(f, "{:#b}", n),
                8 => write!(f, "{:#o}", n),
                16 => write!(f, "{:#X}", n),
                _ => write!(f, "{:#}", n),
            },
            Cell::Real(r) => write!(f, "{}", r),
            Cell::Str(s) => write!(f, "{}", s),
            Cell::Key(k) => write!(f, "{}:", k),
            Cell::Vector(v) => f.debug_list().entries(v.iter()).finish(),
            Cell::Map(v) => f.debug_list().entries(v.iter()).finish(),
            Cell::Fun(x) => write!(f, "{:?}", x),
            Cell::Bitstr(s) => if s.is_bytestring() {
                    f
                    .debug_list()
                    .entries(s.iter8().map(|x| Cell::Int(x.0 as Xint)))
                    .finish()
                } else {
                    write!(f, "0s{}", s.to_bin_string())
                },
            Cell::Ref(x) => write!(f, "ref {:?}", x),
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
            Xfn::Interp(x) => write!(f, "f:{:#x}", x),
            Xfn::Native(x) => write!(f, "xf:{:#x}", x.0 as usize),
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
            (Cell::Bitstr(a), Cell::Bitstr(b)) => a == b,
            (Cell::Vector(a), Cell::Vector(b)) => a == b,
            (Cell::Map(a), Cell::Map(b)) => a == b,
            (Cell::Fun(a), Cell::Fun(b)) => a == b,
            (Cell::Ref(a), Cell::Ref(b)) => a == b,
            (Cell::Key(a), Cell::Key(b)) => a == b,
            _ => false,
        }
    }
}

impl Cell {

    pub fn into_ref(self) -> Xresult1<Xref> {
        match self {
            Cell::Ref(xref) => Ok(xref),
            _ => Err(Xerr::TypeError),
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

    pub fn into_vector(self) -> Result<Xvec, Xerr> {
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

    pub fn to_usize(&self) -> Xresult1<usize> {
        match self {
            Cell::Int(i) => Ok(*i as usize),
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

    pub fn into_bitstring(self) -> Xresult1<Xbitstr> {
        match self {
            Cell::Bitstr(s) => Ok(s),
            _ => Err(Xerr::TypeError),
        }
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
        Cell::Int(x as Xint)
    }
}

impl From<isize> for Cell {
    fn from(x: isize) -> Self {
        Cell::Int(x as Xint)
    }
}

impl From<u32> for Cell {
    fn from(x: u32) -> Self {
        Cell::Int(x as Xint)
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
        if x {
            ONE
        } else {
            ZERO
        }
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
pub const NIL: Cell = Cell::Nil;
