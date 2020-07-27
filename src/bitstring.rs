use std::convert::From;
use std::ops::Range;
use std::rc::Rc;

pub enum Byteorder {
    BE,
    LE,
}

#[derive(Debug, Clone)]
struct BitstringRange(Range<usize>);

impl Default for BitstringRange {
    fn default() -> Self {
        BitstringRange(0..0)
    }
}

impl BitstringRange {
    fn from_len(num_bytes: usize) -> BitstringRange {
        BitstringRange(0..(num_bytes * 8))
    }

    fn num_bits(&self) -> usize {
        self.0.len()
    }

    fn start(&self) -> usize {
        self.0.start
    }

    fn end(&self) -> usize {
        self.0.end
    }

    fn bits_range(&self) -> Range<usize> {
        self.0.clone()
    }

    fn bytes_range(&self) -> Range<usize> {
        let i = self.start() / 8;
        let e = Self::upper_bound_index(self.end());
        i..e
    }

    fn is_start_aligned(&self) -> bool {
        (self.start() % 8) == 0
    }

    fn is_bytestring(&self) -> bool {
        self.is_start_aligned() && (self.end() % 8 == 0)
    }

    fn upper_bound_index(bit_idx: usize) -> usize {
        ((bit_idx + 7) & !7) / 8
    }

    fn split_at(&self, bit_index: usize) -> Option<(BitstringRange, BitstringRange)> {
        let mid = self.start() + bit_index;
        if mid > self.end() {
            return None;
        }
        let left = BitstringRange(self.start()..mid);
        let right = BitstringRange(mid..self.end());
        Some((left, right))
    }

    fn peek(&self, num_bits: usize) -> Option<BitstringRange> {
        if num_bits > self.num_bits() {
            None
        } else {
            let start = self.start();
            let end = start + num_bits;
            Some(BitstringRange(start..end))
        }
    }

    fn read(&mut self, num_bits: usize) -> Option<BitstringRange> {
        let bs = self.peek(num_bits)?;
        self.0.start += num_bits;
        Some(bs)
    }

    fn peek_rear(&self, num_bits: usize) -> Option<BitstringRange> {
        if num_bits > self.num_bits() {
            None
        } else {
            let end = self.end();
            let start = end - num_bits;
            Some(BitstringRange(start..end))
        }
    }

    fn read_rear(&mut self, num_bits: usize) -> Option<BitstringRange> {
        let bs = self.peek_rear(num_bits)?;
        self.0.end -= num_bits;
        Some(bs)
    }
}

macro_rules! to_unsigned {
    ($range:expr, $data:expr, $order:expr, $t:ty) => {{
        let mut acc: $t = 0;
        match $order {
            Byteorder::BE => fold_bits!($range, $data, |x, num_bits| {
                acc = (acc << num_bits) | x as $t;
            }),
            Byteorder::LE => {
                let mut shift = 0;
                fold_bits!($range, $data, |x, num_bits| {
                    acc |= (x as $t) << shift;
                    shift += num_bits;
                })
            }
        }
        acc
    }};
}

macro_rules! to_signed {
    ($range:expr, $data:expr, $order:expr, $u_t:ty, $i_t:ty) => {{
        let val = to_unsigned!($range, $data, $order, $u_t);
        let mask = 1 << ($range.num_bits() - 1);
        if (val & mask) > 0 {
            (((val ^ mask) + 1) as $i_t).wrapping_neg()
        } else {
            val as $i_t
        }
    }};
}

macro_rules! fold_bits {
    ($range:expr, $data:expr, $f:expr) => {{
        let mut start = $range.start();
        let end = $range.end();
        for x in $data {
            let drift = start % 8;
            let n = (end - start).min(8 - drift);
            let val = (*x).wrapping_shl(drift as _).wrapping_shr((8 - n) as _);
            $f(val, n);
            start += n;
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
        bs.range = BitstringRange(0..num_bits);
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
        bs.range = BitstringRange(0..num_bits);
        bs
    }};
}

#[derive(Clone, Default)]
pub struct Bitstring {
    range: BitstringRange,
    data: Rc<Vec<u8>>,
}

impl Bitstring {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.range.num_bits()
    }

    pub fn read(&mut self, num_bits: usize) -> Option<Bitstring> {
        let tmp = self.range.read(num_bits)?;
        let mut bs = self.clone();
        bs.range = tmp;
        Some(bs)
    }

    pub fn split_at(&self, bit_index: usize) -> Option<(Bitstring, Bitstring)> {
        let (h, rest) = self.range.split_at(bit_index)?;
        let mut h_bs = self.clone();
        h_bs.range = h;
        let mut rest_bs = self.clone();
        rest_bs.range = rest;
        Some((h_bs, rest_bs))
    }

    pub fn to_i64(&self, order: Byteorder) -> i64 {
        let src = self.slice();
        to_signed!(self.range, src, order, u64, i64)
    }

    pub fn to_u64(&self, order: Byteorder) -> u64 {
        let src = self.slice();
        to_unsigned!(self.range, src, order, u64)
    }

    pub fn to_i128(&self, order: Byteorder) -> i128 {
        let src = self.slice();
        to_signed!(self.range, src, order, u128, i128)
    }

    pub fn to_u128(&self, order: Byteorder) -> u128 {
        let src = self.slice();
        to_unsigned!(self.range, src, order, u128)
    }

    pub fn from_i64(value: i64, num_bits: usize, order: Byteorder) -> Bitstring {
        match order {
            Byteorder::BE => num_to_big!(value, num_bits),
            Byteorder::LE => num_to_little!(value, num_bits),
        }
    }

    pub fn from_u64(value: u64, num_bits: usize, order: Byteorder) -> Bitstring {
        match order {
            Byteorder::BE => num_to_big!(value, num_bits),
            Byteorder::LE => num_to_little!(value, num_bits),
        }
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let src = self.slice();
        let cap = src.len();
        let mut bytes = Vec::<u8>::with_capacity(cap);
        let mut acc = 0u32;
        let mut n = 0;
        fold_bits!(self.range, src, |x, num_bits| {
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

    fn slice(&self) -> &[u8] {
        &self.data[self.range.bytes_range()]
    }

    pub fn bits<'a>(&'a self) -> Bits<'a> {
        Bits {
            pos: self.range.start(),
            bs: self,
        }
    }

    pub fn detach(&self) -> Bitstring {
        if self.len() == 0 {
            Bitstring::new()
        } else {
            let num_bits = self.len();
            let mut tmp = Vec::from(self.slice());
            let d = (num_bits % 8) as u32;
            if d > 0 {
                // clear unused bits
                let x = tmp.last_mut().unwrap();
                *x = x.wrapping_shr(8 - d).wrapping_shl(8 - d);
            }
            Bitstring {
                range: BitstringRange(0..num_bits),
                data: Rc::new(tmp),
            }
        }
    }

    pub fn append(&self, other: &Bitstring) -> Bitstring {
        if self.range.is_bytestring() && other.range.is_bytestring() {
            self.append_bytestring(other)
        } else {
            self.append_bitstring(other)
        }
    }

    fn append_bytestring(&self, other: &Bitstring) -> Bitstring {
        let mut tmp = self.detach();
        let dst = Rc::make_mut(&mut tmp.data);
        dst.extend_from_slice(other.slice());
        let start = tmp.range.start();
        let end = tmp.range.end() + other.len();
        tmp.range = BitstringRange(start..end);
        tmp
    }

    fn append_bitstring(&self, other: &Bitstring) -> Bitstring {
        let mut ptr = self.range.end();
        let mut tmp = self.detach();
        let dst = Rc::make_mut(&mut tmp.data);
        let new_len = BitstringRange::upper_bound_index(self.len() + other.len());
        dst.resize_with(new_len, || 0);
        let src = other.slice();
        fold_bits!(other.range, src, |x, num_bits| {
            let i = ptr / 8;
            let used = ptr % 8;
            let rest = 8 - used;
            if num_bits <= rest {
                dst[i] |= (x << (rest - num_bits)) as u8;
            } else {
                dst[i] |= (x >> (num_bits - rest)) as u8;
                dst[i + 1] = (x << (8 - (num_bits - rest))) as u8;
            }
            ptr += num_bits as usize;
        });
        tmp.range = BitstringRange(0..ptr);
        tmp
    }
}

impl PartialEq for Bitstring {
    fn eq(&self, other: &Bitstring) -> bool {
        if self.len() != other.len() {
            false
        } else if self.range.is_bytestring() && other.range.is_bytestring() {
            let a = self.slice();
            let b = other.slice();
            a.iter().zip(b).all(|x| x.0 == x.1)
        } else {
            self.bits().zip(other.bits()).all(|x| x.0 == x.1)
        }
    }
}

impl<'a> From<&'a [u8]> for Bitstring {
    fn from(s: &'a [u8]) -> Self {
        let n = s.len() * 8;
        Bitstring {
            range: BitstringRange(0..n),
            data: Rc::new(Vec::from(s)),
        }
    }
}

impl From<Vec<u8>> for Bitstring {
    fn from(v: Vec<u8>) -> Self {
        Bitstring {
            range: BitstringRange::from_len(v.len()),
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
        if self.pos >= self.bs.range.end() {
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
    const BE: Byteorder = Byteorder::BE;
    const LE: Byteorder = Byteorder::LE;

    #[test]
    fn test_split_at() {
        let bs = Bitstring::from(vec![0x7f]);
        let (a, b) = bs.split_at(4).unwrap();
        assert_eq!(a.to_i64(LE), 0x7);
        assert_eq!(b.to_u64(LE), 0xf);
    }

    #[test]
    fn test_index_upper_bound() {
        assert_eq!(BitstringRange::upper_bound_index(0), 0);
        assert_eq!(BitstringRange::upper_bound_index(1), 1);
        assert_eq!(BitstringRange::upper_bound_index(2), 1);
        assert_eq!(BitstringRange::upper_bound_index(3), 1);
        assert_eq!(BitstringRange::upper_bound_index(4), 1);
        assert_eq!(BitstringRange::upper_bound_index(5), 1);
        assert_eq!(BitstringRange::upper_bound_index(6), 1);
        assert_eq!(BitstringRange::upper_bound_index(7), 1);
        assert_eq!(BitstringRange::upper_bound_index(8), 1);
        assert_eq!(BitstringRange::upper_bound_index(9), 2);
        assert_eq!(BitstringRange::upper_bound_index(10), 2);
        assert_eq!(BitstringRange::upper_bound_index(11), 2);
        assert_eq!(BitstringRange::upper_bound_index(12), 2);
        assert_eq!(BitstringRange::upper_bound_index(13), 2);
        assert_eq!(BitstringRange::upper_bound_index(14), 2);
        assert_eq!(BitstringRange::upper_bound_index(15), 2);
        assert_eq!(BitstringRange::upper_bound_index(16), 2);
        assert_eq!(BitstringRange::upper_bound_index(17), 3);
    }

    #[test]
    fn test_detach() {
        let mut a = Bitstring::from(&vec![0xff, 0x2f]);
        let b = a.read(8).unwrap().detach();
        assert_eq!(b.range.bits_range(), (0..8));
        assert_eq!(b.to_bytes(), vec![0xff]);
        let c = a.read(4).unwrap().detach();
        assert_eq!(c.range.bits_range(), (0..4));
        assert_eq!(c.to_bytes(), vec![0x20]);
        assert_eq!(a.range.bits_range(), (12..16));
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
