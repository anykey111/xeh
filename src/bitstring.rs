use std::convert::From;
use std::fmt;
use std::ops::Range;
use std::rc::Rc;

pub enum Byteorder {
    BigEndian,
    LittleEndian,
}

pub const BE: Byteorder = Byteorder::BigEndian;
pub const LE: Byteorder = Byteorder::LittleEndian;

#[derive(Debug, Clone)]
pub struct Bitrange(Range<usize>);

impl Bitrange {
    pub fn from_slice(data: &[u8]) -> Bitrange {
        Bitrange(0..data.len() * 8)
    }

    pub fn num_bits(&self) -> usize {
        self.0.len()
    }

    pub fn start(&self) -> usize {
        self.0.start
    }

    pub fn end(&self) -> usize {
        self.0.end
    }

    pub fn range(&self) -> Range<usize> {
        self.0.clone()
    }

    pub fn split_at(&self, bit_index: usize) -> Option<(Bitrange, Bitrange)> {
        let mid = self.0.start + bit_index;
        if mid > self.0.end {
            return None;
        }
        let left = Bitrange(self.0.start..mid);
        let right = Bitrange(mid..self.0.end);
        Some((left, right))
    }

    pub fn peek(&self, num_bits: usize) -> Option<Bitrange> {
        if num_bits > self.0.len() {
            None
        } else {
            let start = self.0.start;
            let end = start + num_bits;
            Some(Bitrange(start..end))
        }
    }

    pub fn read(&mut self, num_bits: usize) -> Option<Bitrange> {
        let bs = self.peek(num_bits)?;
        self.0.start += num_bits;
        Some(bs)
    }

    pub fn peek_rear(&self, num_bits: usize) -> Option<Bitrange> {
        if num_bits > self.0.len() {
            None
        } else {
            let end = self.0.end;
            let start = end - num_bits;
            Some(Bitrange(start..end))
        }
    }

    pub fn read_rear(&mut self, num_bits: usize) -> Option<Bitrange> {
        let bs = self.peek_rear(num_bits)?;
        self.0.end -= num_bits;
        Some(bs)
    }
}

macro_rules! to_unsigned {
    ($bounds:expr, $data:expr, $order:expr) => {{
        let mut acc = 0;
        match $order {
            Byteorder::BigEndian => fold_bits!($bounds, $data, |x, num_bits| {
                acc = (acc << num_bits) | (x as u64);
            }),
            Byteorder::LittleEndian => {
                let mut shift = 0;
                fold_bits!($bounds, $data, |x, num_bits| {
                    acc |= (x as u64) << shift;
                    shift += num_bits;
                })
            }
        }
        acc
    }};
}

macro_rules! to_signed {
    ($bounds:expr, $data:expr, $order:expr) => {{
        let val = to_unsigned!($bounds, $data, $order);
        let i = $bounds.len() - 1;
        let mask = 1 << i;
        if (val & mask) > 0 {
            ((val ^ mask) + 1).wrapping_neg() as i64
        } else {
            val as i64
        }
    }};
}

macro_rules! fold_bits {
    ($bounds:expr, $data:expr, $f:expr) => {{
        let mut start = $bounds.start;
        let end = $bounds.end;
        let mut drift = start % 8;
        let index = start / 8;
        let mut it = $data.iter().skip(index);
        while start < end {
            let n = (end - start).min(8 - drift);
            let v = it.next().unwrap();
            let v = v.wrapping_shl(drift as u32);
            let v = v.wrapping_shr((8 - n) as u32);
            start += n;
            drift = 0;
            $f(v, n as u32);
        }
    }};
}

macro_rules! num_to_big {
    ($val:expr, $num_bits:expr) => {{
        let val = $val;
        let num_bits: usize = $num_bits;
        let mut bs = Bitstring::new();
        let buf = Rc::make_mut(&mut bs.data);
        let mut n = num_bits;
        while n > 0 {
            let d = n.min(8);
            let x = if d < 8 {
                val.wrapping_shr((n - d) as u32)
                    .wrapping_shl((8 - d) as u32)
            } else {
                val.wrapping_shr((n - d) as u32)
            };
            buf.push(x as u8);
            n -= d;
        }
        bs.bounds = Bitrange(0..num_bits);
        assert!(bs.data.len() * 8 >= num_bits);
        bs
    }};
}

macro_rules! num_to_little {
    ($val:expr, $num_bits:expr) => {{
        let val = $val;
        let num_bits: usize = $num_bits;
        let mut bs = Bitstring::new();
        let buf = Rc::make_mut(&mut bs.data);
        let mut n = 0;
        while n < num_bits {
            let d = (num_bits - n).min(8);
            let x = if d < 8 {
                val.wrapping_shr(n as u32).wrapping_shl((8 - d) as u32)
            } else {
                val.wrapping_shr(n as u32)
            };
            buf.push(x as u8);
            n += d;
        }
        bs.bounds = Bitrange(0..num_bits);
        assert!(bs.data.len() * 8 >= num_bits);
        bs
    }};
}

#[derive(Clone)]
pub struct Bitstring {
    bounds: Bitrange,
    data: Rc<Vec<u8>>,
}

impl Bitstring {
    pub fn new() -> Self {
        Self {
            bounds: Bitrange(0..0),
            data: Rc::default(),
        }
    }

    pub fn len(&self) -> usize {
        self.bounds.num_bits()
    }

    pub fn bit_range(&self) -> Range<usize> {
        self.bounds.range()
    }

    pub fn read(&mut self, num_bits: usize) -> Option<Bitstring> {
        let tmp = self.bounds.read(num_bits)?;
        let mut bs = self.clone();
        bs.bounds = tmp;
        Some(bs)
    }

    pub fn split_at(&self, bit_index: usize) -> Option<(Bitstring, Bitstring)> {
        let (h, rest) = self.bounds.split_at(bit_index)?;
        let mut h_bs = self.clone();
        h_bs.bounds = h;
        let mut rest_bs = self.clone();
        rest_bs.bounds = rest;
        Some((h_bs, rest_bs))
    }

    pub fn to_i64(&self, order: Byteorder) -> i64 {
        let buf = &self.data;
        to_signed!(self.bit_range(), buf, order)
    }

    pub fn to_u64(&self, order: Byteorder) -> u64 {
        let buf = &self.data;
        to_unsigned!(self.bit_range(), buf, order)
    }

    pub fn from_i64(value: i64, num_bits: usize, order: Byteorder) -> Bitstring {
        match order {
            Byteorder::BigEndian => num_to_big!(value, num_bits),
            Byteorder::LittleEndian => num_to_little!(value, num_bits),
        }
    }

    pub fn from_u64(value: u64, num_bits: usize, order: Byteorder) -> Bitstring {
        match order {
            Byteorder::BigEndian => num_to_big!(value, num_bits),
            Byteorder::LittleEndian => num_to_little!(value, num_bits),
        }
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let buf = &self.data;
        let cap = upper_bound_byte_idx(self.bounds.num_bits());
        let mut bytes = Vec::<u8>::with_capacity(cap);
        let mut acc = 0u32;
        let mut n = 0;
        fold_bits!(self.bit_range(), buf, |x, num_bits| {
            acc = (acc << num_bits) | x as u32;
            n += num_bits;
            if n >= 8 {
                bytes.push((acc & 0xff) as u8);
                n -= 8;
                acc = acc >> 8;
            }
        });
        if n > 0 {
            bytes.push((acc << (8 - n)) as u8);
        }
        bytes
    }

    pub fn bits<'a>(&'a self) -> Bits<'a> {
        Bits {
            pos: self.bounds.start(),
            bs: self,
        }
    }

    fn start_index(&self) -> usize {
        self.bounds.start() / 8
    }

    fn end_index(&self) -> usize {
        upper_bound_byte_idx(self.bounds.end())
    }

    pub fn is_bytestring(&self) -> bool {
        (self.bounds.start() % 8 == 0) && (self.bounds.end() % 8 == 0)
    }

    pub fn detach(&self) -> Bitstring {
        if self.len() == 0 {
            Bitstring::new()
        } else {
            let a = self.start_index();
            let b = self.end_index();
            let num_bits = self.len();
            let mut tmp = Vec::from(&self.data[a..b]);
            let d = (num_bits % 8) as u32;
            if d > 0 {
                // clear unused bits
                let x = &mut tmp[num_bits / 8];
                *x = x.wrapping_shr(8 - d).wrapping_shl(8 - d);
            }
            Bitstring {
                bounds: Bitrange(0..num_bits),
                data: Rc::new(tmp),
            }
        }
    }

    pub fn append(&self, other: &Bitstring) -> Bitstring {
        if self.is_bytestring() && other.is_bytestring() {
            self.append_bytestring(other)
        } else {
            self.append_bitstring(other)
        }
    }

    fn append_bytestring(&self, other: &Bitstring) -> Bitstring {
        let mut tmp = self.detach();
        let buf = Rc::make_mut(&mut tmp.data);
        let from = other.bounds.start() / 8;
        let to = other.bounds.end() / 8;
        for x in &other.data[from..to] {
            buf.push(*x);
        }
        let start = tmp.bounds.start();
        let end = tmp.bounds.end() + other.len();
        tmp.bounds = Bitrange(start..end);
        tmp
    }

    fn append_bitstring(&self, other: &Bitstring) -> Bitstring {
        let mut ptr = self.bounds.end();
        let mut tmp = self.detach();
        let buf = Rc::make_mut(&mut tmp.data);
        let cap = upper_bound_byte_idx(self.len() + other.len());
        while buf.len() < cap {
            buf.push(0);
        }
        fold_bits!(other.bit_range(), &other.data, |x, num_bits| {
            let i = ptr / 8;
            let used = (ptr % 8) as u32;
            let rest = (8 - used) as u32;
            if num_bits <= rest {
                buf[i] |= (x << (rest - num_bits)) as u8;
            } else {
                buf[i] |= (x >> (num_bits - rest)) as u8;
                buf[i + 1] = (x << (8 - (num_bits - rest))) as u8;
            }
            ptr += num_bits as usize;
        });
        tmp.bounds = Bitrange(0..ptr);
        tmp
    }
}

fn upper_bound_byte_idx(bit_idx: usize) -> usize {
    ((bit_idx + 7) & !7) / 8
}

impl PartialEq for Bitstring {
    fn eq(&self, other: &Bitstring) -> bool {
        if self.len() != other.len() {
            false
        } else if self.is_bytestring() && other.is_bytestring() {
            let n = self.len();
            let ita = &self.data[self.bounds.range()];
            let itb = &other.data[other.bounds.range()];
            ita.iter().zip(itb).all(|x| x.0 == x.1)
        } else {
            self.bits().zip(other.bits()).all(|x| x.0 == x.1)
        }
    }
}

impl fmt::Debug for Bitstring {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let start = self.start_index();
        let end = self.end_index();
        let limit = (end - start).min(256);
        let mut buf = String::with_capacity(limit * 2 + 2);
        for x in self.data.iter().skip(start).take(limit) {
            let h: u8 = 0x30u8 + (x >> 4);
            let l: u8 = 0x30u8 + (x & 0xf);
            buf.push(h.into());
            buf.push(l.into());
        }
        if (end - start) > limit {
            buf.push_str("..");
        }
        write!(f, "Bitstring({:?}, [{}])", self.bounds.0, buf)
    }
}

impl<'a> From<&'a [u8]> for Bitstring {
    fn from(s: &'a [u8]) -> Self {
        let n = s.len() * 8;
        Bitstring {
            bounds: Bitrange(0..n),
            data: Rc::new(Vec::from(s)),
        }
    }
}

impl From<Vec<u8>> for Bitstring {
    fn from(v: Vec<u8>) -> Self {
        Bitstring {
            bounds: Bitrange::from_slice(&v),
            data: Rc::new(v),
        }
    }
}

impl<'a> From<&'a Vec<u8>> for Bitstring {
    fn from(v: &'a Vec<u8>) -> Self {
        Bitstring::from(&v[..])
    }
}

impl<'a> From<&'a str> for Bitstring {
    fn from(s: &'a str) -> Self {
        Bitstring::from(s.as_bytes())
    }
}

pub struct Bits<'a> {
    pos: usize,
    bs: &'a Bitstring,
}

impl<'a> Iterator for Bits<'a> {
    type Item = u8;
    fn next(&mut self) -> Option<u8> {
        if self.pos >= self.bs.bounds.end() {
            None
        } else {
            let idx = self.pos / 8;
            let shift = self.pos % 8;
            let bit = (self.bs.data[idx] >> shift) & 1 as u8;
            self.pos += 1;
            Some(bit)
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::bitstring::*;

    #[test]
    fn test_raw_read() {
        let vals = vec![0x81, 0xff, 0x81];
        let mut bs = Bitrange::from_slice(&vals);
        assert_eq!(0..4, bs.read(4).unwrap().range());
        assert_eq!(17..24, bs.read_rear(7).unwrap().range());
        let mut res = Vec::new();
        fold_bits!(bs.range(), vals, |x, num_bits| {
            res.push((x, num_bits));
        });
        assert_eq!(res, &[(0x1, 4), (0xff, 8), (1, 1)]);
    }

    #[test]
    fn test_split_at() {
        let bs = Bitstring::from(&vec![0x7f]);
        let (a, b) = bs.split_at(4).unwrap();
        assert_eq!(a.to_i64(LE), 0x7);
        assert_eq!(b.to_u64(LE), 0xf);
    }

    #[test]
    fn test_index_upper_bound() {
        assert_eq!(upper_bound_byte_idx(0), 0);
        assert_eq!(upper_bound_byte_idx(1), 1);
        assert_eq!(upper_bound_byte_idx(2), 1);
        assert_eq!(upper_bound_byte_idx(3), 1);
        assert_eq!(upper_bound_byte_idx(4), 1);
        assert_eq!(upper_bound_byte_idx(5), 1);
        assert_eq!(upper_bound_byte_idx(6), 1);
        assert_eq!(upper_bound_byte_idx(7), 1);
        assert_eq!(upper_bound_byte_idx(8), 1);
        assert_eq!(upper_bound_byte_idx(9), 2);
        assert_eq!(upper_bound_byte_idx(10), 2);
        assert_eq!(upper_bound_byte_idx(11), 2);
        assert_eq!(upper_bound_byte_idx(12), 2);
        assert_eq!(upper_bound_byte_idx(13), 2);
        assert_eq!(upper_bound_byte_idx(14), 2);
        assert_eq!(upper_bound_byte_idx(15), 2);
        assert_eq!(upper_bound_byte_idx(16), 2);
        assert_eq!(upper_bound_byte_idx(17), 3);
    }

    #[test]
    fn test_detach() {
        let mut a = Bitstring::from(&vec![0xff, 0x2f]);
        let b = a.read(8).unwrap().detach();
        assert_eq!(b.bit_range(), (0..8));
        assert_eq!(b.to_bytes(), vec![0xff]);
        let c = a.read(4).unwrap().detach();
        assert_eq!(c.bit_range(), (0..4));
        assert_eq!(c.to_bytes(), vec![0x20]);
        assert_eq!(a.bit_range(), (12..16));
        let mut x = Bitstring::from(&vec![0x12, 0x34]);
        x.read(4).unwrap();
        assert_eq!(x.read(8).unwrap().to_bytes(), vec![0x23]);
    }

    #[test]
    fn test_append() {
        // byte aligned
        let a = Bitstring::from(&vec![0x12, 0x34]);
        let b = Bitstring::from(&vec![0x56, 0x78]);
        assert_eq!(a.append(&b).to_bytes(), vec![0x12, 0x34, 0x56, 0x78]);
        // unaligned
        let mut g = Bitstring::from(&vec![0x12, 0x34]);
        let h = g.read(7).unwrap();
        let f = g.read(9).unwrap();
        assert_eq!(h.append(&f).to_bytes(), vec![0x12, 0x34]);
        let mut w = Bitstring::from(&vec![0xab, 0xcd, 0xef]);
        let x = w.read(9).unwrap();
        let y = w.read(13).unwrap();
        let z = w.read(1).unwrap();
        let r = w.read(1).unwrap();
        assert_eq!(
            x.append(&y).append(&z).append(&r).to_bytes(),
            vec![0xab, 0xcd, 0xef]
        );
    }

    #[test]
    fn test_value() {
        let bs = Bitstring::from(&vec![0x7f]);
        assert_eq!(bs.to_i64(LE), 127);
        assert_eq!(bs.to_u64(LE), 127);

        let bs = Bitstring::from(&vec![0xff]);
        assert_eq!(bs.to_u64(LE), 255);
        assert_eq!(bs.to_i64(LE), -128);

        let bs = Bitstring::from(&vec![0xff, 0xff]);
        assert_eq!(bs.to_i64(LE), i16::min_value() as i64);

        let bs = Bitstring::from(&vec![0xff, 0x7f]);
        assert_eq!(bs.to_i64(LE), i16::max_value() as i64);

        let bs = Bitstring::from(&vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]);
        assert_eq!(bs.to_i64(LE), i64::max_value());

        let bs = Bitstring::from(&vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]);
        assert_eq!(bs.to_i64(LE), i64::min_value());
        assert_eq!(bs.to_u64(LE), u64::max_value());
    }

    #[test]
    fn test_nums() {
        assert_eq!(Bitstring::from_u64(0, 0, BE).to_bytes(), vec![]);
        let bs = Bitstring::from_u64(1, 3, BE);
        assert_eq!(bs.to_i64(BE), 1);
        assert_eq!(bs.to_bytes(), vec![0x20]);
        assert_eq!(
            Bitstring::from_u64(0x12345678, 32, LE).to_bytes(),
            vec![0x78, 0x56, 0x34, 0x12]
        );
        assert_eq!(
            Bitstring::from_u64(0x12345678, 32, BE).to_bytes(),
            vec![0x12, 0x34, 0x56, 0x78]
        );
        assert_eq!(
            Bitstring::from_u64(0x7FFFFFFF, 32, LE).to_bytes(),
            vec![0xff, 0xff, 0xff, 0x7f]
        );
        assert_eq!(
            Bitstring::from_i64(0xFFFF_FFFF, 32, LE).to_i64(LE),
            i32::min_value() as i64
        );
        assert_eq!(
            Bitstring::from_i64(0x7FFF_FFFF, 32, LE).to_i64(LE),
            i32::max_value() as i64
        );
        assert_eq!(
            Bitstring::from_i64(0xFFFF_FFFF, 32, BE).to_i64(LE),
            i32::min_value() as i64
        );
        assert_eq!(
            Bitstring::from_i64(0x7FFF_FFFF, 32, BE).to_i64(BE),
            i32::max_value() as i64
        );
        assert_eq!(
            &Bitstring::from_i64(i64::max_value(), 64, LE).to_bytes(),
            &i64::max_value().to_le_bytes()
        );
        assert_eq!(
            &Bitstring::from_i64(i64::max_value(), 64, BE).to_bytes(),
            &i64::max_value().to_be_bytes()
        );
        assert_eq!(
            Bitstring::from_i64(i64::max_value(), 64, LE).to_i64(LE),
            i64::max_value()
        );
        assert_eq!(
            Bitstring::from_i64(i64::max_value(), 64, BE).to_i64(BE),
            i64::max_value()
        );
    }
}
