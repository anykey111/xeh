use std::convert::From;
use std::ops::Range;
use std::rc::Rc;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Byteorder {
    BE,
    LE,
}

#[derive(Clone, PartialEq, Debug, Copy)]
pub enum BitstringFormat {
    Raw,
    Signed(Byteorder),
    Unsigned(Byteorder),
    Real(Byteorder),
}

impl Default for BitstringFormat {
    fn default() -> Self {
        BitstringFormat::Raw
    }
}

pub type BitstringRange = Range<usize>;

fn upper_bound_index(num_bits: usize) -> usize {
    let n = if (num_bits % 8) > 0 { 1 } else { 0 };
    (num_bits / 8) + n
}

fn bit_mask(len: usize) -> u8 {
    !0xffu32.wrapping_shl(len as u32) as u8
}

fn cut_bits(x: u8, start: usize, end: usize) -> (u8, usize) {
    let start_bit = start % 8;
    let len = (end - start).min(8 - start_bit);
    let result = x.wrapping_shr(start_bit as u32) & bit_mask(len);
    (result, len)
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
        let mask = 1 << (($range.end - $range.start) - 1);
        if (val & mask) > 0 {
            (((val ^ mask) + 1) as $i_t).wrapping_neg()
        } else {
            val as $i_t
        }
    }};
}

macro_rules! fold_bits {
    ($range:expr, $data:expr, $f:expr) => {{
        let mut start = $range.start;
        let end = $range.end;
        for x in $data {
            let (val, n) = cut_bits(*x, start, end);
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
        let mut i = num_bits;
        while i > 0 {
            let n = i.min(8);
            let x = val.wrapping_shr((i - n) as u32) as u8;
            buf.push(x);
            i -= n;
        }
        bs.range = 0..num_bits;
        bs
    }};
}

macro_rules! num_to_little {
    ($val:expr, $num_bits:expr) => {{
        let val = $val;
        let num_bits: usize = $num_bits;
        let mut bs = Bitstring::new();
        let buf = Rc::make_mut(&mut bs.data);
        let mut i = 0;
        while i < num_bits {
            let n = (num_bits - i).min(8);
            let x = val.wrapping_shr(i as u32) as u8;
            buf.push(x);
            i += n;
        }
        bs.range = 0..num_bits;
        bs
    }};
}

#[derive(Clone, Default)]
pub struct Bitstring {
    format: BitstringFormat,
    range: BitstringRange,
    data: Rc<Vec<u8>>,
}

impl Bitstring {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn from_str_bin(s: &str) -> Result<Bitstring, char> {
        let mut n = 0;
        let mut buf = Vec::new();
        buf.resize_with(s.len(), || 0u8);
        for c in s.chars() {
            let i = n % 8;
            match c {
                '_' | ' ' => continue,
                '0' => n += 1,
                '1' => {
                    buf[n / 8] |= 1u8 << i;
                    n += 1;
                },
                c => return Err(c),
            };
        }
        let mut result = Bitstring::from(buf);
        result.range.end = n;
        Ok(result)
    }

    pub fn to_bin_string(&self) -> String {
        let mut s = String::with_capacity(self.len());
        s.extend(self.bits().map(|x| if x > 0 { '1' } else { '0' }));
        return s;        
    }

    pub fn len(&self) -> usize {
        self.range.end - self.range.start
    }

    fn is_bytestring(&self) -> bool {
        (self.range.start % 8 == 0) && (self.range.end % 8 == 0)
    }

    pub fn format(&self) -> BitstringFormat {
        self.format
    }

    pub fn set_format(&mut self, format: BitstringFormat) {
        self.format = format;
    }

    pub fn read(&mut self, num_bits: usize) -> Option<Bitstring> {
        let pos = self.range.start + num_bits;
        if pos > self.range.end {
            return None;
        }
        let mut result = self.clone();
        result.range.end = pos;
        self.range.start = pos;
        Some(result)
    }

    pub fn split_at(&self, bit_index: usize) -> Option<(Bitstring, Bitstring)> {
        let mid = self.range.start + bit_index;
        if mid > self.range.end {
            return None;
        }
        let mut left = self.clone();
        left.range.end = mid;
        let mut right = self.clone();
        right.range.start = mid;
        Some((left, right))
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
        if self.is_bytestring() {
            return src.to_vec();
        }
        let cap = (self.len() + 8) / 8;
        let mut bytes = Vec::with_capacity(cap);
        let mut acc = 0u32;
        let mut n = 0;
        fold_bits!(self.range, src, |x, num_bits| {
            acc |= (x as u32) << n;
            n += num_bits;
            if n >= 8 {
                bytes.push(acc as u8);
                n -= 8;
                acc = acc >> 8;
            }
        });
        if n > 0 {
            bytes.push(acc as u8);
        }
        bytes
    }

    fn slice(&self) -> &[u8] {
        &self.data[self.bytes_range()]
    }

    fn bytes_range(&self) -> BitstringRange {
        let i = self.range.start / 8;
        let e = upper_bound_index(self.range.end);
        i..e
    }

    pub fn bits<'a>(&'a self) -> Bits<'a> {
        Bits {
            pos: self.range.start,
            bs: self,
        }
    }

    fn clear_padding_bits(&mut self) {
        let r = self.range.clone();
        let start_pad = r.start % 8;
        let data = Rc::make_mut(&mut self.data);
        data[r.start / 8] &= !bit_mask(start_pad);
        let end_pad = r.end % 8;
        if end_pad > 0 {
            data[r.end / 8] &= bit_mask(end_pad);
        }
    }

    pub fn detach(&self) -> Bitstring {
        if self.len() == 0 {
            Bitstring::new()
        } else {
            let start = self.range.start % 8;
            let end = start + self.len();
            let tmp = Vec::from(self.slice());
            let mut s = Bitstring {
                format: BitstringFormat::Raw,
                range: BitstringRange::from(start..end),
                data: Rc::new(tmp),
            };
            s.clear_padding_bits();
            s
        }
    }

    fn append_bytes_mut(mut self, tail: &Bitstring) -> Bitstring {
        let data = Rc::make_mut(&mut self.data);
        data.extend_from_slice(tail.slice());
        let start = self.range.start;
        let end = self.range.end + tail.len();
        self.range = BitstringRange::from(start..end);
        self
    }

    fn append_bits_mut(mut self, tail: &Bitstring) -> Bitstring {
        if self.is_bytestring() && tail.is_bytestring() {
            return self.append_bytes_mut(tail);
        }
        let mut pos = self.range.end;
        let new_len = upper_bound_index(pos + tail.len());
        let data = Rc::make_mut(&mut self.data);
        data.resize_with(new_len, || 0);
        for x in tail.bits() {
            let i = pos / 8;
            let offset = pos % 8;
            data[i] |= x << offset;
            pos += 1;
        }
        let start = self.range.start;
        self.range = BitstringRange::from(start..pos);
        self
    }

    pub fn append(self, tail: &Bitstring) -> Bitstring {
        if Rc::strong_count(&self.data) == 1 {
            self.append_bits_mut(tail)
        } else {
            let tmp = self.detach();
            tmp.append_bits_mut(tail)
        }
    }

    pub fn invert(self) -> Bitstring {
        let mut s = if Rc::strong_count(&self.data) == 1 {
            self
        } else {
            self.detach()
        };
        let r = s.bytes_range();
        let data = Rc::make_mut(&mut s.data);
        for x in data[r].iter_mut() {
            *x = !*x;
        }
        s.clear_padding_bits();
        s
    }
}

impl PartialEq for Bitstring {
    fn eq(&self, other: &Bitstring) -> bool {
        if self.len() != other.len() {
            false
        } else if self.is_bytestring() && other.is_bytestring() {
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
        Bitstring::from(Vec::from(s))
    }
}

impl From<Vec<u8>> for Bitstring {
    fn from(v: Vec<u8>) -> Self {
        Bitstring {
            format: BitstringFormat::Raw,
            range: BitstringRange::from(0..(v.len() * 8)),
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
        if self.pos >= self.bs.range.end {
            None
        } else {
            let i = self.pos / 8;
            let offset = self.pos % 8;
            let val = (self.bs.data[i] >> offset) & 1;
            self.pos += 1;
            Some(val)
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
        assert_eq!(a.to_i64(LE), -8);
        assert_eq!(b.to_u64(BE), 7);
    }

    #[test]
    fn test_index_upper_bound() {
        assert_eq!(upper_bound_index(0), 0);
        assert_eq!(upper_bound_index(1), 1);
        assert_eq!(upper_bound_index(2), 1);
        assert_eq!(upper_bound_index(3), 1);
        assert_eq!(upper_bound_index(4), 1);
        assert_eq!(upper_bound_index(5), 1);
        assert_eq!(upper_bound_index(6), 1);
        assert_eq!(upper_bound_index(7), 1);
        assert_eq!(upper_bound_index(8), 1);
        assert_eq!(upper_bound_index(9), 2);
        assert_eq!(upper_bound_index(10), 2);
        assert_eq!(upper_bound_index(11), 2);
        assert_eq!(upper_bound_index(12), 2);
        assert_eq!(upper_bound_index(13), 2);
        assert_eq!(upper_bound_index(14), 2);
        assert_eq!(upper_bound_index(15), 2);
        assert_eq!(upper_bound_index(16), 2);
        assert_eq!(upper_bound_index(17), 3);
    }

    #[test]
    fn test_detach() {
        let mut a = Bitstring::from(&vec![0xff, 0x2f]);
        let b = a.read(8).unwrap().detach();
        assert_eq!(b.range, (0..8));
        assert_eq!(b.to_bytes(), vec![0xff]);
        let c = a.read(4).unwrap().detach();
        assert_eq!(c.range, (0..4));
        assert_eq!(c.to_bytes(), vec![0x0f]);
        assert_eq!(a.range, (12..16));
        let mut x = Bitstring::from(&vec![0x12, 0x34]);
        x.read(4).unwrap();
        assert_eq!(x.read(8).unwrap().to_bytes(), vec![0x41]);
    }

    #[test]
    fn test_append() {
        // byte aligned
        let a = Bitstring::from(&vec![0x12, 0x34]);
        let b = Bitstring::from(&vec![0x56, 0x78]);
        assert_eq!(a.append(&b).to_bytes(), vec![0x12, 0x34, 0x56, 0x78]);
        // unaligned
        let mut g = Bitstring::from(&vec![0b11000001, 0b10011001]);
        let h = g.read(7).unwrap();
        let f = g.read(9).unwrap();
        assert_eq!(h.append(&f).to_bytes(), vec![0b11000001, 0b10011001]);
        let mut w = Bitstring::from(&vec![0xab, 0xcd, 0xef]);
        let x = w.read(9).unwrap();
        let y = w.read(13).unwrap();
        let z = w.read(1).unwrap();
        let r = w.read(1).unwrap();
        assert_eq!(
            x.append(&y).append(&z).append(&r).to_bytes(),
            vec![0xab, 0xcd, 0xef]
        );
        let mut s = Bitstring::from(&vec![0x13]);
        let a = s.read(4).unwrap();
        let b = s.read(4).unwrap();
        assert_eq!(b.append(&a).to_bytes(), vec![0x31]);

        let mut s = Bitstring::from_str_bin("0_1000000_0_0111011_0_1111000").unwrap();
        s.read(1).unwrap();
        let a = s.read(7).unwrap();
        let a_bits: Vec<_> = a.bits().collect();
        assert_eq!(a_bits, vec![1, 0, 0, 0, 0, 0, 0]);
        s.read(1).unwrap();
        let b = s.read(7).unwrap();
        let b_bits: Vec<_> = b.bits().collect();
        assert_eq!(b_bits, vec![0, 1, 1, 1, 0, 1, 1]);
        s.read(1).unwrap();
        let c = s.read(7).unwrap();
        let c_bits: Vec<_> = c.bits().collect();
        assert_eq!(c_bits, vec![1, 1, 1, 1, 0, 0, 0]);
        let sab = a.clone().append(&b);
        let sab_bits: Vec<_> = sab.bits().collect();
        assert_eq!(sab_bits, vec![1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1]);
        let sabc = a.clone().append(&b).append(&c);
        let sabc_bits: Vec<_> = sabc.bits().collect();
        assert_eq!(
            sabc_bits,
            vec![1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0]
        );
        let scba = c.append(&b).append(&a);
        let scba_bits: Vec<_> = scba.bits().collect();
        assert_eq!(
            scba_bits,
            vec![1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0]
        );
    }

    #[test]
    fn test_invert() {
        let mut a = Bitstring::from_str_bin("01111111_01111111").unwrap();
        let b = a.clone().invert();
        assert_eq!("1000000010000000", b.to_bin_string().as_str());
        assert_eq!("0111111101111111", b.invert().to_bin_string().as_str());
        let c = a.read(5).unwrap();
        assert_eq!(c.bits().collect::<Vec<_>>(), vec![0, 1, 1, 1, 1]);
        let c_inv = c.invert();
        assert_eq!(c_inv.bits().collect::<Vec<_>>(), vec![1, 0, 0, 0, 0]);
        assert_eq!(c_inv.data[0], 0x01);
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
        assert_eq!(bs.to_bytes(), vec![1]);
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

    #[test]
    fn test_from_str_bin() {
        let s = "10111001001";
        let bs1 = Bitstring::from_str_bin(s).unwrap();
        assert_eq!(s.len(), bs1.len());
        assert_eq!(s, bs1.to_bin_string().as_str());
    }

    #[test]
    fn test_cut() {
        assert_eq!((0b1111, 4), cut_bits(0b11110000, 4, 12));
        assert_eq!((0b111, 3), cut_bits(0b11110000, 5, 8));
        assert_eq!((0b1110000, 7), cut_bits(0b11110000, 0, 7));
        assert_eq!((0b11110000, 8), cut_bits(0b11110000, 0, 8));
        assert_eq!((0b11110000, 8), cut_bits(0b11110000, 0, 9));
        assert_eq!((0b1111000, 7), cut_bits(0b11110000, 1, 8));
    }

    #[test]
    fn test_bit_mask() {
        assert_eq!(0b00000000, bit_mask(0));
        assert_eq!(0b00000001, bit_mask(1));
        assert_eq!(0b00000011, bit_mask(2));
        assert_eq!(0b00000111, bit_mask(3));
        assert_eq!(0b00001111, bit_mask(4));
        assert_eq!(0b00011111, bit_mask(5));
        assert_eq!(0b00111111, bit_mask(6));
        assert_eq!(0b01111111, bit_mask(7));
        assert_eq!(0b11111111, bit_mask(8));
        assert_eq!(0b11111111, bit_mask(9));
    }

    #[test]
    fn test_bits() {
        let s = Bitstring::from(vec![0xc0]);
        let res: Vec<_> = s.bits().collect();
        assert_eq!(vec![0, 0, 0, 0, 0, 0, 1, 1], res);
    }
}
