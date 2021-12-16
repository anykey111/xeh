use crate::error::{Xerr, Xresult, Xresult1};
use crate::state::State;

pub type Xvec = rpds::Vector<Cell>;
pub type Xstr = arcstr::ArcStr;
pub type XfnType = fn(&mut State) -> Xresult;
pub type Xint = i128;
pub type Xreal = f64;
pub type Xanyrc = std::rc::Rc<std::cell::RefCell<dyn std::any::Any>>;
pub type Xbitstr = crate::bitstring::Bitstring;
pub type Xcell = Cell;
pub type Xmeta = std::rc::Rc<XcellWithMeta>;

pub struct XcellWithMeta {
    meta: Cell,
    value: Cell,
}

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
    Str(Xstr),
    Key(Xstr),
    Vector(Xvec),
    Fun(Xfn),
    Bitstr(Xbitstr),
    AnyRc(Xanyrc),
    WithMeta(Xmeta),
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
                2 if f.alternate() => write!(f, "{:#b}", n),
                2 => write!(f, "{:b}", n),
                8 if f.alternate() => write!(f, "{:#o}", n),
                8 => write!(f, "{:o}", n),
                16 if f.alternate() => write!(f, "{:#X}", n),
                16 => write!(f, "{:X}", n),
                _ => write!(f, "{}", n),
            },
            Cell::Real(r) => write!(f, "{}", r),
            Cell::Str(s) => write!(f, "{}", s),
            Cell::Key(k) => write!(f, "{}:", k),
            Cell::Vector(v) => f.debug_list().entries(v.iter()).finish(),
            Cell::Fun(x) => write!(f, "{:?}", x),
            Cell::Bitstr(s) => if s.is_bytestring() {
                    f
                    .debug_list()
                    .entries(s.iter8().map(|x| Cell::Int(x.0 as Xint)))
                    .finish()
                } else {
                    write!(f, "0s{}", s.to_bin_string())
                },
            Cell::AnyRc(x) => match x.try_borrow() {
                Ok(p) => write!(f, "any:{:?}", p.type_id()),
                Err(_) => write!(f, "any"),
            },
            Cell::WithMeta(mc) => mc.value.fmt(f),
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
        match (self.value(), other.value()) {
            (Cell::Nil, Cell::Nil) => true,
            (Cell::Int(a), Cell::Int(b)) => a == b,
            (Cell::Real(a), Cell::Real(b)) => a == b,
            (Cell::Str(a), Cell::Str(b)) => a == b,
            (Cell::Bitstr(a), Cell::Bitstr(b)) => a == b,
            (Cell::Vector(a), Cell::Vector(b)) => a == b,
            (Cell::Fun(a), Cell::Fun(b)) => a == b,
            (Cell::Key(a), Cell::Key(b)) => a == b,
            _ => false,
        }
    }
}

use std::cmp::Ordering;

impl PartialOrd for Cell {
    fn partial_cmp(&self, other: &Cell) -> Option<Ordering> {
        match (self.value(), other.value()) {
            (Cell::Int(a), Cell::Int(b)) => a.partial_cmp(b),
            (Cell::Real(a), Cell::Real(b)) => a.partial_cmp(b),
            (Cell::Str(a), Cell::Str(b)) => a.partial_cmp(b),
            (Cell::Key(a), Cell::Key(b)) => a.partial_cmp(b),
            _ => None,
        }
    }
}

impl Ord for Cell {
    fn cmp(&self, other: &Cell) -> Ordering {
        self.partial_cmp(other).unwrap_or(Ordering::Equal)
    }
}
impl Eq for Cell {}

impl Cell {

    pub fn is_true(&self) -> bool {
        match self.value() {
            Cell::Nil | Cell::Int(0) => false,
            _ => true,
        }
    }

    pub fn is_key(&self) -> bool {
        match self.value() {
            Cell::Key(_) => true,
            _ => false,
        }
    }

    pub fn meta(&self) -> Option<&Cell> {
        match self {
            Cell::WithMeta(mc) => Some(&mc.meta),
            _ => None,
        }
    }

    pub fn with_meta(self, meta: Cell) -> Cell {
        Cell::WithMeta(Xmeta::new(XcellWithMeta{
            meta, value: self
        }))
    }

    pub fn value(&self) -> &Cell {
        match self {
            Cell::WithMeta(rc) => &rc.value,
            _ => self,
        }
    }

    pub fn vec(&self) -> Xresult1<&Xvec> {
        match self.value() {
           Cell::Vector(x) => Ok(x),
           _ => Err(Xerr::TypeError)
        }
    }

    pub fn to_string(&self) -> Xresult1<Xstr> {
        match self.value() {
            Cell::Str(s) => Ok(s.clone()),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn to_vector(&self) -> Result<Xvec, Xerr> {
        match self.value() {
            Cell::Vector(x) => Ok(x.clone()),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn to_real(&self) -> Xresult1<Xreal> {
        match self.value() {
            Cell::Real(x) => Ok(*x),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn into_any(self) -> Xresult1<Xanyrc> {
        match self {
            Cell::AnyRc(rc) => Ok(rc),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn to_isize(&self) -> Xresult1<isize> {
        match self.value() {
            Cell::Int(i) => Ok(*i as isize),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn to_usize(&self) -> Xresult1<usize> {
        match self.value() {
            Cell::Int(i) => Ok(*i as usize),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn to_int(&self) -> Xresult1<Xint> {
        match self.value() {
            Cell::Int(i) => Ok(*i),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn to_bitstring(&self) -> Xresult1<Xbitstr> {
        match self.value() {
            Cell::Bitstr(s) => Ok(s.clone()),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn new_key(k: &str) -> Cell {
        Cell::Key(Xstr::from(k))
    }

    pub fn new_str(k: &str) -> Cell {
        Cell::Str(Xstr::from(k))
    }

    pub fn empty_bitstr() -> Cell {
        Cell::Bitstr(Xbitstr::default())
    }

    pub fn empty_vec() -> Cell {
        Cell::Vector(Xvec::default())
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

impl From<u8> for Cell {
    fn from(x: u8) -> Self {
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

impl From<i64> for Cell {
    fn from(x: i64) -> Self {
        Cell::Int(x as Xint)
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

impl From<Xvec> for Cell {
    fn from(x: Xvec) -> Self {
        Cell::Vector(x)
    }
}

impl From<Xbitstr> for Cell {
    fn from(x: Xbitstr) -> Self {
        Cell::Bitstr(x)
    }
}

impl From<&str> for Cell {
    fn from(x: &str) -> Self {
        Cell::Str(Xstr::from(x))
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
pub const TRUE: Cell = ONE;
pub const FALSE: Cell = ZERO;


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cell_eq() {
        let a = Cell::from(33u8);
        let b = Cell::from(33u8);
        assert_eq!(&a, &b);
        let c = b.with_meta(ZERO.clone());
        assert_eq!(&a, &c);
        let a = Cell::from(32.0);
        let b = Cell::from(32.0);
        assert_eq!(&a, &b);
        let c = b.with_meta(ONE.clone());
        assert_eq!(&a, &c);
        let a = Cell::from("asd");
        let b = Cell::from("asd");
        assert_eq!(&a, &b);
        let c = b.with_meta(ONE.clone());
        assert_eq!(&a, &c);
    }

}