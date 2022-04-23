use crate::error::{Xerr, Xresult, Xresult1};
use crate::fmt_flags::FmtFlags;
use crate::state::State;

pub type Xvec = rpds::Vector<Cell>;
pub type Xstr = arcstr::ArcStr;
pub type Xsubstr = arcstr::Substr;
pub type XfnType = fn(&mut State) -> Xresult;
pub type Xint = i128;
pub type Xreal = f64;
pub type Xanyrc = std::rc::Rc<std::cell::RefCell<dyn std::any::Any>>;
pub type Xbitstr = crate::bitstring::Bitstring;
pub type Xcell = Cell;

pub struct WithTag {
    tag: Cell,
    value: Cell,
}

#[derive(Clone, Copy)]
pub struct XfnPtr(pub XfnType);

impl PartialEq for XfnPtr {
    fn eq(&self, other: &Self) -> bool {
        (self.0 as usize) == (other.0 as usize)
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
    Vector(Xvec),
    Fun(Xfn),
    Bitstr(Xbitstr),
    AnyRc(Xanyrc),
    WithTag(std::rc::Rc<WithTag>),
}

use std::fmt;

impl fmt::Debug for XfnPtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:#x}", self.0 as usize)
    }
}

impl fmt::Debug for Cell {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let flags = f.width().map(|n| FmtFlags::from_raw(n)).unwrap_or_default();
        match self {
            Cell::Nil => write!(f, "nil"),
            Cell::Int(n) => match flags.base() {
                2 if flags.show_prefix() => write!(f, "{:#b}", n),
                2 => write!(f, "{:b}", n),
                8 if flags.show_prefix() => write!(f, "{:#o}", n),
                8 => write!(f, "{:o}", n),
                16 if flags.show_prefix() => write!(f, "{:#x}", n),
                16 => write!(f, "{:x}", n),
                _ => write!(f, "{}", n),
            },
            Cell::Real(r) => write!(f, "{:0.1}", r),
            Cell::Str(s) => write!(f, "{}", s.as_str()),
            Cell::Vector(v) => {
                f.write_str("[ ")?;
                for x in v {
                    x.fmt(f)?;
                    f.write_str(" ")?;
                }
                f.write_str("]")
            }
            Cell::Fun(x) => write!(f, "{:?}", x),
            Cell::Bitstr(s) => if s.is_bytestring() {
                    f.write_str("[ ")?;
                    for x in s.iter8().map(|x| Cell::Int(x.0 as Xint)) {
                        x.fmt(f)?;
                        f.write_str(" ")?;
                    }
                    f.write_str( "]")
                } else {
                    write!(f, "0s{}", s.to_bin_string())
                },
            Cell::AnyRc(x) => match x.try_borrow() {
                Ok(p) => write!(f, "any:{:?}", p.type_id()),
                Err(_) => write!(f, "any"),
            },
            Cell::WithTag(rc) if flags.show_tags() => {
                rc.value.fmt(f)?;
                f.write_str(" @")?;
                rc.tag.fmt(f)
            },
            Cell::WithTag(rc) => rc.value.fmt(f),
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

const NIL_TYPE_NAME: &str = "nil";
const INT_TYPE_NAME: &str = "int";
const REAL_TYPE_NAME: &str = "real";
const STR_TYPE_NAME: &str = "str";
const VEC_TYPE_NAME: &str = "vec";
const FUN_TYPE_NAME: &str = "fun";
const BITSTR_TYPE_NAME: &str = "bitstr";
const ANY_TYPE_NAME: &str = "any";
const TAG_TYPE_NAME: &str = "tag";

impl Cell {

    pub fn type_name(&self) -> &str {
        match self {
            Cell::Nil{..} => NIL_TYPE_NAME,
            Cell::Int{..} => INT_TYPE_NAME,
            Cell::Real{..} => REAL_TYPE_NAME,
            Cell::Str{..} => STR_TYPE_NAME,
            Cell::Vector{..} => VEC_TYPE_NAME,
            Cell::Fun{..} => FUN_TYPE_NAME,
            Cell::Bitstr{..} => BITSTR_TYPE_NAME,
            Cell::AnyRc{..} => ANY_TYPE_NAME,
            Cell::WithTag{..} => TAG_TYPE_NAME,
        }
    }

    pub fn is_true(&self) -> bool {
        match self.value() {
            Cell::Nil | Cell::Int(0) => false,
            _ => true,
        }
    }

    pub fn tag(&self) -> Option<&Cell> {
        match self {
            Cell::WithTag(rc) => Some(&rc.tag),
            _ => None,
        }
    }

    pub fn with_tag(self, tag: Cell) -> Cell {
        Cell::WithTag(std::rc::Rc::new(WithTag{
            tag, value: self
        }))
    }

    pub fn multi_tag(self, new_tag: Cell) -> Cell {
        match self {
            Cell::WithTag(rc) => {
                let tags = match &rc.tag {
                    Cell::Vector(v) => v.push_back(new_tag),
                    c => {
                        let mut v = Xvec::new();
                        v.push_back_mut(c.clone());
                        v.push_back_mut(new_tag);
                        v
                    }
                };
                rc.value.clone().with_tag(Cell::from(tags))
            },
            _ => {
                let tags = Xvec::new().push_back(new_tag);
                self.with_tag(Cell::from(tags))
            }
        }
    }

    pub fn find_tagged(&self, tag: &Cell) -> Option<&Cell> {
        match self.tag()? {
            Cell::Vector(v) => v.iter().find_map(|c| c.find_tagged(tag)),
            t if t == tag => Some(self),
            _ => None,
        }
    }

    pub fn value(&self) -> &Cell {
        match self {
            Cell::WithTag(rc) => rc.value.value(),
            _ => self,
        }
    }

    pub fn vec(&self) -> Xresult1<&Xvec> {
        match self.value() {
           Cell::Vector(x) => Ok(x),
           _ => Err(Xerr::TypeError)
        }
    }

    pub fn str(&self) -> Xresult1<&str> {
        match self.value() {
            Cell::Str(s) => Ok(s.as_str()),
            _ => Err(Xerr::TypeError),
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

    pub fn bitstr(&self) -> Xresult1<&Xbitstr> {
        match self.value() {
            Cell::Bitstr(s) => Ok(s),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn to_bitstring(&self) -> Xresult1<Xbitstr> {
        match self.value() {
            Cell::Bitstr(s) => Ok(s.clone()),
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

impl From<i128> for Cell {
    fn from(x: i128) -> Self {
        Cell::Int(x)
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

impl From<String> for Cell {
    fn from(x: String) -> Self {
        Cell::Str(Xstr::from(x))
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
        let c = b.with_tag(ZERO.clone());
        assert_eq!(&a, &c);
        let a = Cell::from(32.0);
        let b = Cell::from(32.0);
        assert_eq!(&a, &b);
        let c = b.with_tag(ONE.clone());
        assert_eq!(&a, &c);
        let a = Cell::from("asd");
        let b = Cell::from("asd");
        assert_eq!(&a, &b);
        let c = b.with_tag(ONE.clone());
        assert_eq!(&a, &c);
    }

    #[test]
    fn test_with_tag() {
        let tag_a = Cell::from("a");
        let c = ONE.with_tag(tag_a.clone());
        assert_eq!(Some(&tag_a), c.tag());
        assert_eq!(ONE, c);
    }

    #[test]
    fn test_multi_tag() {
        let tag_a = Cell::from("a");
        let tag_b = Cell::from("b");
        let c = ONE.with_tag(tag_a.clone()).multi_tag(tag_b.clone());
        let tags = Xvec::new().push_back(tag_a).push_back(tag_b);
        assert_eq!(Some(&Cell::from(tags)), c.tag());
        assert_eq!(ONE, c);
    }

    #[test]
    fn test_multi_tag2() {
        let tag_a = Cell::from("a");
        let c = ZERO.multi_tag(tag_a.clone());
        let tags = Xvec::new().push_back(tag_a);
        assert_eq!(Some(&Cell::from(tags)), c.tag());
        assert_eq!(ZERO, c);
    }

    #[test]
    fn test_find_tagged() {
        let color_name = Cell::from("red");
        let color_tag = Cell::from("color");
        let comment_text = Cell::from("some text");
        let comment_tag = Cell::from("comment");
        let tag1 = comment_text.clone().with_tag(comment_tag.clone());
        let tag2 = color_name.clone().with_tag(color_tag.clone());
        let val = ONE.multi_tag(tag1).multi_tag(tag2);
        assert_eq!(Some(&comment_text), val.find_tagged(&comment_tag));
        assert_eq!(Some(&color_name), val.find_tagged(&color_tag));
        assert_eq!(None, val.find_tagged(&color_name));
        assert_eq!(None, val.find_tagged(&comment_text));
    }
}