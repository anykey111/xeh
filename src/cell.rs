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
pub type Xbitstr = crate::bitstr::Bitstr;
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
pub struct CellRef(usize);

impl Default for CellRef {
    fn default() -> Self {
        Self(usize::MAX)
    }
}

impl CellRef {
    pub fn from_index(idx: usize) -> Self {
        Self(idx)
    }
    pub fn index(&self) -> usize {
        self.0
    }
    pub fn is_initialized(&self) -> bool {
        self != &Self::default()
    }
}

#[derive(Clone)]
pub enum Cell {
    Nil,
    Flag(bool),
    Int(Xint),
    Real(Xreal),
    Str(Xstr),
    Vector(Xvec),
    Fun(Xfn),
    Bitstr(Xbitstr),
    AnyRc(Xanyrc),
    WithTag(std::rc::Rc<WithTag>),
}

use std::fmt::{self, Write};

impl fmt::Debug for XfnPtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:#x}", self.0 as usize)
    }
}

impl fmt::Debug for Cell {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let flags = f.width().map(|n| FmtFlags::from_raw(n)).unwrap_or_default();
        const BITSTR_ELIDE_LEN:usize = 30;
        const STR_ELIDE_LEN:usize = 75;
        const VEC_ELIDE_LEN:usize = 10;
        match self {
            Cell::Nil => write!(f, "nil"),
            Cell::Flag(x) => write!(f, "{}", if *x { "true" } else { "false" }),
            Cell::Int(n) => match flags.base() {
                2 if flags.show_prefix() => write!(f, "{:#b}", n),
                2 => write!(f, "{:b}", n),
                8 if flags.show_prefix() => write!(f, "{:#o}", n),
                8 => write!(f, "{:o}", n),
                16 if flags.show_prefix() => {
                    if flags.upcase() {
                        write!(f, "{:#X}", n)
                    } else {
                        write!(f, "{:#x}", n)
                    }
                }
                16 => {
                    if flags.upcase() {
                        write!(f, "{:X}", n)
                    } else {
                        write!(f, "{:x}", n)
                    }
                }
                _ => write!(f, "{}", n),
            },
            Cell::Real(r) => write!(f, "{}", r),
            Cell::Str(s) if flags.fitscreen() && s.len() > STR_ELIDE_LEN =>
                write!(f, "\"{} ...", s.split_at(STR_ELIDE_LEN).0),
            Cell::Str(s) => write!(f, "{:?}", s.as_str()),
            Cell::Vector(v) => {
                f.write_str("[ ")?;
                for (i, x) in v.iter().enumerate() {
                    x.fmt(f)?;
                    f.write_str(" ")?;
                    if flags.fitscreen() && i > VEC_ELIDE_LEN {
                        f.write_str("... ")?;
                        break;
                    }
                }
                f.write_str("]")
            }
            Cell::Fun(x) => write!(f, "{:?}", x),
            Cell::Bitstr(s) => {
                f.write_str("|")?;
                for (pos, (x, mut n)) in s.iter8().enumerate() {
                    if pos != 0 {
                        f.write_str(" ")?;
                    }
                    if flags.fitscreen() && pos > BITSTR_ELIDE_LEN {
                        f.write_str("...")?;
                        break;
                    }
                    if n > 4 {
                        n -= 4;
                        write!(f, "{:X}", x >> n)?;
                    }
                    if n == 4 {
                        n -= 4;
                        write!(f, "{:X}", x & 0xf)?;
                    }
                    for i in (0..n).rev() {
                        if (x & (1 << i)) > 0{
                            f.write_char('x')?;
                        } else {
                            f.write_char('-')?;
                        }
                    }
                }
                f.write_str("|")
            }
            Cell::AnyRc(x) => match x.try_borrow() {
                Ok(p) => write!(f, "any:{:?}", p.type_id()),
                Err(_) => write!(f, "any"),
            },
            Cell::WithTag(rc) if flags.show_tags() => {
                rc.value.fmt(f)?;
                f.write_str(" .")?;
                if !rc.tag.vec().is_ok() {
                    f.write_char(' ')?;
                }
                rc.tag.fmt(f)
            }
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
            (Cell::Flag(a), Cell::Flag(b)) => a == b,
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

const NIL_TYPE_NAME: Xstr = xstr_literal!("nil");
const FLAG_TYPE_NAME: Xstr = xstr_literal!("flag");
const INT_TYPE_NAME: Xstr = xstr_literal!("int");
const REAL_TYPE_NAME: Xstr = xstr_literal!("real");
const STR_TYPE_NAME: Xstr = xstr_literal!("str");
const VEC_TYPE_NAME: Xstr = xstr_literal!("vec");
const FUN_TYPE_NAME: Xstr = xstr_literal!("fun");
const BITSTR_TYPE_NAME: Xstr = xstr_literal!("bitstr");
const ANY_TYPE_NAME: Xstr = xstr_literal!("any");
const TAG_TYPE_NAME: Xstr = xstr_literal!("tag");

fn cell_type_error(msg: Xstr, val: Cell) -> Xerr {
    Xerr::TypeErrorMsg { msg, val }
}

impl Cell {
    pub fn type_name(&self) -> Xstr {
        match self {
            Cell::Nil { .. } => NIL_TYPE_NAME,
            Cell::Flag { .. } => FLAG_TYPE_NAME,
            Cell::Int { .. } => INT_TYPE_NAME,
            Cell::Real { .. } => REAL_TYPE_NAME,
            Cell::Str { .. } => STR_TYPE_NAME,
            Cell::Vector { .. } => VEC_TYPE_NAME,
            Cell::Fun { .. } => FUN_TYPE_NAME,
            Cell::Bitstr { .. } => BITSTR_TYPE_NAME,
            Cell::AnyRc { .. } => ANY_TYPE_NAME,
            Cell::WithTag { .. } => TAG_TYPE_NAME,
        }
    }

    pub fn flag(&self) -> Xresult1<bool> {
        match self.value() {
            Cell::Flag(x) => Ok(*x),
            _ => Err(cell_type_error(FLAG_TYPE_NAME, self.clone())),
        }
    }

    pub fn cond_true(&self) -> Xresult1<bool> {
        match self.value() {
            Cell::Nil => Ok(false),
            _ => self.flag(),
        }
    }

    pub fn tag(&self) -> Option<&Cell> {
        match self {
            Cell::WithTag(rc) => Some(&rc.tag),
            _ => None,
        }
    }

    pub fn with_tag(self, tag: Cell) -> Cell {
        let tagged = match self {
            Cell::WithTag(rc) => WithTag { tag, value: rc.value.clone() },
            value => WithTag { tag, value },
        };
        Cell::WithTag(std::rc::Rc::new(tagged))
    }
    
    pub fn get_tagged(&self, key: &Cell) -> Option<&Cell> {
        self.tag()?.vec().ok()?.iter().find(|x| x.tag() == Some(&key))
    }

    pub fn set_tagged(self, key: Cell, val: Cell) -> Xresult1<Cell> {
        match self.tag() {
            Some(Cell::Vector(v )) => {
                let tv = if let Some(i) = v.iter().position(|x| x.tag() == Some(&key)) {
                    v.set(i, val.with_tag(key)).unwrap()
                } else {
                    v.push_back(val.with_tag(key))
                };
                Ok(self.with_tag(Cell::from(tv)))
            }
            Some(val) => {
                Err(Xerr::TypeErrorMsg {
                    val: val.clone(),
                    msg: xstr_literal!("tagged vec")
                })
            }
            None => {
                let mut tv = Xvec::new();
                tv.push_back_mut(val.with_tag(key));
                Ok(self.with_tag(Cell::from(tv)))
            }
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
            val => Err(cell_type_error(VEC_TYPE_NAME, val.clone())),
        }
    }

    pub fn to_vec(&self) -> Xresult1<Xvec> {
        match self.value() {
            Cell::Vector(x) => Ok(x.clone()),
            val => Err(cell_type_error(VEC_TYPE_NAME, val.clone())),
        }
    }

    pub fn str(&self) -> Xresult1<&str> {
        match self.value() {
            Cell::Str(x) => Ok(x.as_str()),
            val => Err(cell_type_error(STR_TYPE_NAME, val.clone())),
        }
    }

    pub fn to_xstr(&self) -> Xresult1<Xstr> {
        match self.value() {
            Cell::Str(x) => Ok(x.clone()),
            val => Err(cell_type_error(STR_TYPE_NAME, val.clone())),
        }
    }

    pub fn to_real(&self) -> Xresult1<Xreal> {
        match self.value() {
            Cell::Real(x) => Ok(*x),
            val => Err(cell_type_error(REAL_TYPE_NAME, val.clone())),
        }
    }

    pub fn to_any(&self) -> Xresult1<Xanyrc> {
        match self.value() {
            Cell::AnyRc(rc) => Ok(rc.clone()),
            val => Err(cell_type_error(ANY_TYPE_NAME, val.clone())),
        }
    }

    pub fn to_xint(&self) -> Xresult1<Xint> {
        match self.value() {
            Cell::Int(x) => Ok(*x),
            val => Err(cell_type_error(INT_TYPE_NAME, val.clone())),
        }
    }
    pub fn to_isize(&self) -> Xresult1<isize> {
        match self.value() {
            Cell::Int(i) => Ok(*i as isize),
            val => Err(cell_type_error(INT_TYPE_NAME, val.clone())),
        }
    }

    pub fn to_usize(&self) -> Xresult1<usize> {
        match self.value() {
            Cell::Int(i) => Ok(*i as usize),
            val => Err(cell_type_error(INT_TYPE_NAME, val.clone())),
        }
    }

    pub fn bitstr(&self) -> Xresult1<&Xbitstr> {
        match self.value() {
            Cell::Bitstr(s) => Ok(s),
            val => Err(cell_type_error(BITSTR_TYPE_NAME, val.clone())),
        }
    }

    pub fn to_bitstr(&self) -> Xresult1<Xbitstr> {
        match self.value() {
            Cell::Bitstr(s) => Ok(s.clone()),
            val => Err(cell_type_error(BITSTR_TYPE_NAME, val.clone())),
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

impl From<i32> for Cell {
    fn from(x: i32) -> Self {
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
            TRUE
        } else {
            FALSE
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

impl From<Xstr> for Cell {
    fn from(x: Xstr) -> Self {
        Cell::Str(x)
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
pub const TRUE: Cell = Cell::Flag(true);
pub const FALSE: Cell = Cell::Flag(false);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cell_is_true() {
        assert_ne!(Ok(true), ZERO.flag());
        assert_ne!(Ok(true), NIL.flag());
        assert_eq!(Ok(true), TRUE.flag());
        assert_eq!(Ok(true), TRUE.cond_true());
        assert_eq!(Ok(false), FALSE.cond_true());
        assert_eq!(Ok(false), NIL.cond_true());
    }

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
    fn test_get_tagged() {
        let a = Cell::from("1").with_tag(Cell::from("a"));
        assert_eq!(a.get_tagged(&Cell::from("a")), None);
        let b = Cell::from("2").with_tag(Cell::from(rpds::vector![
                Cell::from("c"),
                a.clone()
            ]));
        assert_eq!(Some(&a), b.get_tagged(&Cell::from("a")));
        assert_eq!(None, b.get_tagged(&Cell::from("c")));
    }

    #[test]
    fn test_insert_tagged() {
        let x = Cell::from("x");
        let k1 = Cell::from("k1");
        let v1 = Cell::from("v1");
        let k2 = Cell::from("k2");
        let v2 = Cell::from("v2");
        let x = x.set_tagged(k1.clone(), v1.clone()).unwrap();
        let tv = x.tag().unwrap().to_vec().unwrap();
        assert_eq!(tv[0].tag(), Some(&k1));
        assert_eq!(tv[0].value(), &v1);
        let x = x.set_tagged(k2.clone(), v2.clone()).unwrap();
        let tv = x.tag().unwrap().to_vec().unwrap();
        assert_eq!(tv[1].tag(), Some(&k2));
        assert_eq!(tv[1].value(), &v2);
        let x = x.set_tagged(k1.clone(), v2.clone()).unwrap();
        let tv = x.tag().unwrap().to_vec().unwrap();
        assert_eq!(tv[0].tag(), Some(&k1));
        assert_eq!(tv[0].value(), &v2);
    }

}
