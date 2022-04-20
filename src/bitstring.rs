use std::convert::From;
use std::ops::Range;
use std::rc::Rc;

#[derive(PartialEq, Clone, Copy)]
pub enum Xbyteorder {
    Little,
    Big,
}

pub const LITTLE: Xbyteorder = Xbyteorder::Little;
pub const BIG: Xbyteorder = Xbyteorder::Big;

#[cfg(target_endian = "little")]
pub const NATIVE: Xbyteorder = LITTLE;

#[cfg(target_endian = "big")]
pub const NATIVE: Xbyteorder = BIG;

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
    let shift = 8 - (start_bit + len);
    let result = x.wrapping_shr(shift as u32) & bit_mask(len);
    (result, len)
}

use std::borrow::Cow;

pub type CowBytes = Cow<'static, [u8]>;

use std::fmt;

impl fmt::Debug for Bitstring {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_bin_string())
    }
}

#[derive(Default)]
pub struct BitvecBuilder {
    len: usize,
    data: Vec<u8>,
}

impl BitvecBuilder {
    pub fn append_bit(&mut self, val: u8) {
        assert!(val <= 1);
        let idx = self.len / 8;
        if self.data.len() == idx {
            self.data.push(val << 7);
        } else {
            self.data[idx] |= val <<  (7 - (self.len % 8));
        }
        self.len += 1;
    }

    pub fn finish(self) -> Bitstring {
        let mut res = Bitstring::from(self.data);
        res.range.end = self.len;
        res
    }
}

#[derive(Clone, Default)]
pub struct Bitstring {
    pub (crate) range: BitstringRange,
    data: Rc<CowBytes>,
}

impl Bitstring {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn from_bin_str(s: &str) -> Result<Bitstring, usize> {
        let mut tmp = BitvecBuilder::default();
        for (pos, c) in s.chars().enumerate() {
            match c {
                '_' | ' ' => continue,
                '0' => tmp.append_bit(0),
                '1' => tmp.append_bit(1),
                _ => return Err(pos),
            }
        }
        Ok(tmp.finish())
    }

    pub fn to_bin_string(&self) -> String {
        let mut s = String::with_capacity(self.len());
        s.extend(self.bits().map(|x| if x > 0 { '1' } else { '0' }));
        return s;
    }

    pub fn from_hex_str(s: &str) -> Result<Bitstring, usize> {
        let mut n = 0;
        let mut buf = Vec::new();
        for (pos, c) in s.chars().enumerate() {
            if c == '_' || c == ' ' {
                continue;
            }
            let val = c.to_digit(16).ok_or_else(|| pos)? as u8;
            let idx = n / 8;
            if buf.len() == idx {
                buf.push(val << 4);
            } else {
                buf[idx] |= val;
            }
            n += 4;
        }
        let mut result = Bitstring::from(buf);
        result.range.end = n;
        Ok(result)
    }

    pub fn to_hex_string(&self) -> String {
        let mut s = String::with_capacity(self.len() / 4 + 1);
        for (val, len) in self.iter8() {
            if len > 4 {
                let c = char::from_digit(val as u32 >> 4, 16).unwrap();
                s.push(c);
            }
            let c = char::from_digit(val as u32 & 0xf, 16).unwrap();
            s.push(c);
        }
        return s;
    }

    pub fn start(&self) -> usize {
        self.range.start
    }

    pub fn end(&self) -> usize {
        self.range.end
    }

    pub fn len(&self) -> usize {
        self.range.end - self.range.start
    }

    pub fn is_bytestring(&self) -> bool {
        (self.range.start % 8 == 0) && (self.range.end % 8 == 0)
    }

    pub fn seek(&self, pos: usize) -> Option<Bitstring> {
        if self.range.start <= pos && pos <= self.range.end {
            let mut s = self.clone();
            s.range.start = pos;
            Some(s)
        } else {
            None
        }
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

    pub fn peek(&self, num_bits: usize) -> Option<Bitstring> {
        let end = self.start() + num_bits;
        if self.range.start <= end && end <= self.range.end {
            let mut s = self.clone();
            s.range.end = end;
            Some(s)
        } else {
            None
        }
    }

    pub fn substr(&self, start: usize, end: usize) -> Option<Bitstring> {
        if start <= end && self.range.start <= start && end <= self.range.end {
            let mut s = self.clone();
            s.range = start..end;
            Some(s)
        } else {
            None
        }
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

    pub fn to_int(&self, order: Xbyteorder) -> i128 {
        let val = self.to_uint(order);
        let len = self.len() as u32;
        let sign_bit = 1 << (len - 1);
        if len == i128::BITS {
            i128::from_le_bytes(val.to_ne_bytes())
        } else if (val & sign_bit) > 0 {
            let mask = !u128::MAX.overflowing_shl(len as u32).0;
            -(((!val & mask) + 1) as i128)
        } else {
            val as i128
        }
    }

    pub fn to_uint(&self, order: Xbyteorder) -> u128 {
        let mut acc: u128 = 0;
        let mut pos = self.start();
        let end = self.end();
        if order == BIG {
            for byte in self.slice() {
                let (val, n) = cut_bits(*byte, pos, end);
                acc = (acc << n) | (val as u128);
                pos += n;
            }
        } else {
            for byte in self.slice() {
                let (val, n) = cut_bits(*byte, pos, end);
                acc |= (val as u128) << (pos - self.start()) as u32;
                pos += n;
            }
        }
        acc
    }

    pub fn from_int(val: i128, num_bits: usize, order: Xbyteorder) -> Bitstring {
        let mut tmp = Vec::with_capacity(upper_bound_index(num_bits));
        if order == BIG {
            let mut i = num_bits;
            while i > 0 {
                let n = i.min(8);
                let x = val.wrapping_shr((i - n) as u32) as u8;
                tmp.push(x << (8 - n));
                i -= n;
            }
        } else {
            let mut i = 0;
            while i < num_bits {
                let n = (num_bits - i).min(8);
                let x = val.wrapping_shr(i as u32) as u8;
                tmp.push(x << (8 - n));
                i += n;
            }
        }
        Bitstring {
            range: BitstringRange::from(0..num_bits),
            data: Rc::new(Cow::from(tmp)),
        }
    }

    pub fn to_f32(&self, order: Xbyteorder) -> f32 {
        let mut it = self.iter8();
        let mut buf = [0u8; 4];
        for x in buf.iter_mut() {
            *x = it.next().map(|x| x.0).unwrap_or_default();
        }                
        if order == BIG {
            f32::from_be_bytes(buf)
        } else {
            f32::from_le_bytes(buf)
        }
    }

    pub fn to_f64(&self, order: Xbyteorder) -> f64 {
        let mut it = self.iter8();
        let mut buf = [0u8; 8];
        for x in buf.iter_mut() {
            *x = it.next().map(|x| x.0).unwrap_or_default();
        }                
        if order == BIG {
            f64::from_be_bytes(buf)
        } else {
            f64::from_le_bytes(buf)
        }
    }

    pub fn from_f32(val: f32, order: Xbyteorder) -> Bitstring {
        let bytes = if order == BIG {
            val.to_be_bytes()
        } else {
            val.to_le_bytes()
        };
        Bitstring::from(bytes.to_vec())
    }

    pub fn from_f64(val: f64, order: Xbyteorder) -> Bitstring {
        let bytes = if order == BIG {
            val.to_be_bytes()
        } else {
            val.to_le_bytes()
        };
        Bitstring::from(bytes.to_vec())
    }


    pub fn to_bytes(&self) -> Vec<u8> {
        if self.is_bytestring() {
            return self.slice().to_vec();
        }
        let cap = (self.len() + 8) / 8;
        let mut bytes = Vec::with_capacity(cap);
        bytes.extend(self.iter8().map(|(val, _)| val));
        bytes
    }

    pub fn slice(&self) -> &[u8] {
        &self.data[self.bytes_range()]
    }

    pub fn bytes_range(&self) -> BitstringRange {
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

    pub fn iter8<'a>(&'a self) -> Iter8<'a> {
        Iter8 {
            pos: self.range.start,
            bs: self,
        }
    }

    pub fn iter8_unleashed<'a>(&'a self, start: usize) -> Iter8<'a> {
        Iter8 {
            pos: start,
            bs: self,
        }
    }

    pub fn detach(self) -> Bitstring {
        if Rc::strong_count(&self.data) == 1 {
            self
        } else if self.len() == 0 {
            Bitstring::new()
        } else {
            let end = self.len();
            let mut tmp = Vec::with_capacity(upper_bound_index(end));
            tmp.extend(self.iter8().map(|(val, n)| val << (8 - n)));
            Bitstring {
                range: BitstringRange::from(0..end),
                data: Rc::new(Cow::from(tmp)),
            }
        }
    }

    fn data_mut(&mut self) -> &mut Vec<u8> {
        Rc::make_mut(&mut self.data).to_mut()
    }

    fn append_bytes_mut(mut self, tail: &Bitstring) -> Bitstring {
        self.data_mut().extend_from_slice(tail.slice());
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
        let data = self.data_mut();
        data.resize_with(new_len, || 0);
        for x in tail.bits() {
            let i = pos / 8;
            data[i] |= x << (7 - (pos % 8));
            pos += 1;
        }
        let start = self.range.start;
        self.range = BitstringRange::from(start..pos);
        self
    }

    pub fn append(self, tail: &Bitstring) -> Bitstring {
        self.detach().append_bits_mut(tail)
    }

    pub fn insert(self, bit_index: usize, s: &Bitstring) -> Option<Bitstring> {
        let (left, right) = self.split_at(bit_index)?;
        Some(left.detach().append_bits_mut(&s).append_bits_mut(&right))
    }

    pub fn invert(self) -> Bitstring {
        let r = self.range.clone();
        let mut s = self.detach();
        let data = s.data_mut();
        for pos in r {
            let i = pos / 8;
            data[i] ^= 1 << (7 - (pos % 8));
        }
        s
    }

    pub fn match_with(&self, other: &Bitstring) -> Result<(), usize> {
        if self.len() != other.len() {
            Err(self.len().min(other.len()))
        } else if self.is_bytestring() && other.is_bytestring() {
            let a = self.slice();
            let b = other.slice();
            if let Some(pos) = a.iter().zip(b.iter()).position(|(a, b)| a != b) {
                Err(pos * 8)
            } else {
                Ok(())
            }
        } else {
            if let Some(pos) = self.iter8().zip(other.iter8()).position(|(a, b)| a.0 != b.0) {
                Err(pos * 8)
            } else {
                Ok(())
            }
        }
    }
}

impl PartialEq for Bitstring {
    fn eq(&self, other: &Bitstring) -> bool {
        self.match_with(other).is_ok()
    }
}

impl<'a> From<&'static [u8]> for Bitstring {
    fn from(s: &'static [u8]) -> Self {
        Bitstring {
            range: BitstringRange::from(0..(s.len() * 8)),
            data: Rc::new(CowBytes::from(s)),
        }
    }
}

impl<'a> From<&'static str> for Bitstring {
    fn from(s: &'static str) -> Self {
        Bitstring::from(s.as_bytes())
    }
}

impl From<Vec<u8>> for Bitstring {
    fn from(v: Vec<u8>) -> Self {
        Bitstring {
            range: BitstringRange::from(0..(v.len() * 8)),
            data: Rc::new(CowBytes::from(v)),
        }
    }
}

#[derive(Clone)]
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
            let offset = 7 - (self.pos % 8);
            let val = (self.bs.data[i] >> offset) & 1;
            self.pos += 1;
            Some(val)
        }
    }
}

pub struct Iter8<'a> {
    pos: usize,
    bs: &'a Bitstring,
}

impl<'a> Iterator for Iter8<'a> {
    type Item = (u8, u32);
    fn next(&mut self) -> Option<Self::Item> {
        let start = self.pos;
        let end = self.bs.end();
        if start >= end {
            return None;
        }
        let len = (end - start).min(8);
        let idx = start / 8;
        let (mut val, n) = cut_bits(self.bs.data[idx], start, start + len);
        if n < len {
            let (val2, n2) = cut_bits(self.bs.data[idx + 1], start + n, start + len);
            val = (val << n2 ) | val2;
        }
        self.pos += len;
        Some((val, len as u32))
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_split_at() {
        let bs = Bitstring::from(vec![0x7f]);
        let (a, b) = bs.split_at(4).unwrap();
        assert_eq!(a.to_uint(BIG), 7);
        assert_eq!(b.to_int(LITTLE), -1);
        let (a, b) = bs.split_at(1).unwrap();
        assert_eq!(a.to_uint(LITTLE), 0);
        assert_eq!(b.to_uint(LITTLE), 0x7f);
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
        let mut a = Bitstring::from(vec![0xff, 0x2f]);
        let b = a.read(8).unwrap().detach();
        assert_eq!(b.range, (0..8));
        assert_eq!(b.to_bytes(), vec![0xff]);
        let c = a.read(4).unwrap().detach();
        assert_eq!(c.range, (0..4));
        assert_eq!(c.to_bytes(), vec![2]);
        assert_eq!(c.detach().data[0], 0x20);
        assert_eq!(a.range, (12..16));
        let mut x = Bitstring::from(vec![0x12, 0x34]);
        x.read(4).unwrap();
        assert_eq!(x.read(8).unwrap().to_bytes(), vec![0x23]);
    }

    #[test]
    fn test_cow() {
        static X: [u8; 1] = [255];
        let a = Bitstring::from(&X[..]);
        match &*a.data {
            Cow::Borrowed(x) => assert_eq!(x.as_ptr(), X.as_ptr()),
            other => panic!("fail {:?}", other),
        }
        let b = a.invert();
        match &*b.data {
            Cow::Owned(x) => assert_eq!(x, &vec![0]),
            other => panic!("fail {:?}", other),
        }
    }

    #[test]
    fn test_append() {
        // byte aligned
        let a = Bitstring::from(vec![0x12, 0x34]);
        let b = Bitstring::from(vec![0x56, 0x78]);
        assert_eq!(a.append(&b).to_bytes(), vec![0x12, 0x34, 0x56, 0x78]);
        // unaligned
        let mut g = Bitstring::from(vec![0b11000001, 0b10011001]);
        let h = g.read(7).unwrap();
        let f = g.read(9).unwrap();
        assert_eq!(h.append(&f).to_bytes(), vec![0b11000001, 0b10011001]);
        let mut w = Bitstring::from(vec![0xab, 0xcd, 0xef]);
        let x = w.read(9).unwrap();
        let y = w.read(13).unwrap();
        let z = w.read(1).unwrap();
        let r = w.read(1).unwrap();
        assert_eq!(
            x.append(&y).append(&z).append(&r).to_bytes(),
            vec![0xab, 0xcd, 0xef]
        );
        let mut s = Bitstring::from(vec![0x13]);
        let a = s.read(4).unwrap();
        let b = s.read(4).unwrap();
        assert_eq!(b.append(&a).to_bytes(), vec![0x31]);

        let mut s = Bitstring::from_bin_str("0_1000000_0_0111011_0_1111000").unwrap();
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
    fn test_seek() {
        let s = Bitstring::from(vec![0x12, 0x34]);
        assert_eq!(vec![0x34], s.seek(8).unwrap().to_bytes());
        assert_eq!(&s, &s.seek(0).unwrap());
        assert_eq!(Bitstring::new(), s.seek(16).unwrap());
        assert_eq!(None, s.seek(17));
    }

    #[test]
    fn test_peek() {
        let s = Bitstring::from(vec![0x12, 0x34, 0x56]);
        assert_eq!(vec![0x12], s.peek(8).unwrap().to_bytes());
        assert_eq!(None, s.peek(25));
        assert_eq!(Bitstring::new(), s.peek(0).unwrap());
        assert_eq!(&s, &s.peek(24).unwrap());
    }

    #[test]
    fn test_substr() {
        let s = Bitstring::from(vec![0x12, 0x34, 0x56]);
        assert_eq!(vec![0x34], s.substr(8, 16).unwrap().to_bytes());
        assert_eq!(&s, &s.substr(0, 24).unwrap());
        assert_eq!(None, s.substr(0, 25));
        assert_eq!(None, s.substr(24, 0));
        assert_eq!(Bitstring::new(), s.substr(0, 0).unwrap());
        
        
    }

    #[test]
    fn test_insert() {
        let f = Bitstring::from_bin_str("1111").unwrap();
        let res  = Bitstring::from(vec![0xaa, 0xbb])
                    .insert(4, &f).unwrap()
                    .insert(16, &f).unwrap();
        assert_eq!(vec![0xaf, 0xab, 0xfb], res.to_bytes());
        let z5 = Bitstring::from_bin_str("00000").unwrap();
        let res = Bitstring::from_bin_str("111111").unwrap()
            .insert(3, &z5).unwrap();
        assert_eq!(Bitstring::from_bin_str("11100000111").unwrap(), res);
    }

    #[test]
    fn test_invert() {
        let mut a = Bitstring::from_bin_str("01111111_01111111").unwrap();
        let b = a.clone().invert();
        assert_eq!("1000000010000000", b.to_bin_string().as_str());
        assert_eq!("0111111101111111", b.invert().to_bin_string().as_str());
        let c = a.read(5).unwrap();
        assert_eq!(c.bits().collect::<Vec<_>>(), vec![0, 1, 1, 1, 1]);
        let c_inv = c.invert();
        assert_eq!(c_inv.bits().collect::<Vec<_>>(), vec![1, 0, 0, 0, 0]);
        assert_eq!(c_inv.data[0], 0x80);
    }

    #[test]
    fn test_value() {
        let bs = Bitstring::from(vec![0x7f]);
        assert_eq!(bs.to_int(LITTLE), 127);
        assert_eq!(bs.to_uint(LITTLE), 127);

        let bs = Bitstring::from(vec![0xff]);
        assert_eq!(bs.to_uint(LITTLE), 255);
        assert_eq!(bs.to_int(LITTLE), -1);

        let bs = Bitstring::from(vec![0xfe]);
        assert_eq!(bs.to_uint(LITTLE), 254);
        assert_eq!(bs.to_int(LITTLE), -2);

        let bs = Bitstring::from(vec![0xff, 0xff]);
        assert_eq!(bs.to_int(LITTLE), -1);

        let bs = Bitstring::from(vec![0xff, 0x7f]);
        assert_eq!(bs.to_int(LITTLE), i16::max_value() as i128);

        let bs = Bitstring::from(vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]);
        assert_eq!(bs.to_int(LITTLE), i64::max_value() as i128);

        let bs = Bitstring::from(vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]);
        assert_eq!(bs.to_int(LITTLE), -1);
        assert_eq!(bs.to_uint(LITTLE), u64::max_value() as u128);

        let f = f32::MAX;
        let le = f.to_le_bytes().to_vec();
        assert_eq!(Bitstring::from(le).to_f32(LITTLE), f);
        let be = f.to_be_bytes().to_vec();
        assert_eq!(Bitstring::from(be).to_f32(BIG), f);

        let f: f32 = 1.234;
        assert_eq!(f.to_le_bytes().to_vec(), Bitstring::from_f32(f, LITTLE).to_bytes());
        assert_eq!(f.to_be_bytes().to_vec(), Bitstring::from_f32(f, BIG).to_bytes());

    }

    #[test]
    fn test_nums() {
        assert_eq!(Bitstring::from_int(0, 0, BIG).to_bytes(), vec![]);
        let bs = Bitstring::from_int(1, 3, BIG);
        assert_eq!(bs.to_int(BIG), 1);
        assert_eq!(bs.to_bytes(), vec![1]);
        let ls = Bitstring::from_int(1, 3, LITTLE);
        assert_eq!(ls.to_int(LITTLE), 1);
        assert_eq!(ls.to_bytes(), vec![1]);

        assert_eq!(
            &Bitstring::from_int(0x12345678, 32, LITTLE).to_bytes(),
            &0x12345678u32.to_le_bytes()
        );
        assert_eq!(
            &Bitstring::from_int(0x12345678, 32, BIG).to_bytes(),
            &0x12345678u32.to_be_bytes()
        );
        assert_eq!(
            &Bitstring::from_int(0x7FFFFFFF, 32, LITTLE).to_bytes(),
            &0x7FFFFFFFu32.to_le_bytes()
        );
        assert_eq!(
            Bitstring::from_int(0xFFFF_FFFF, 32, LITTLE).to_int(LITTLE),
            -1
        );
        assert_eq!(
            Bitstring::from_int(0x7FFF_FFFF, 32, LITTLE).to_int(LITTLE),
            i32::max_value() as i128
        );
        assert_eq!(
            Bitstring::from_int(0xFFFF_FFFF, 32, BIG).to_int(BIG),
            -1
        );
        assert_eq!(
            Bitstring::from_int(0x7FFF_FFFF, 32, BIG).to_int(BIG),
            i32::max_value() as i128
        );
        assert_eq!(
            &Bitstring::from_int(i64::MAX.into(), 64, LITTLE).to_bytes(),
            &i64::max_value().to_le_bytes()
        );
        assert_eq!(
            &Bitstring::from_int(i64::MAX.into(), 64, BIG).to_bytes(),
            &i64::max_value().to_be_bytes()
        );
        assert_eq!(
            Bitstring::from_int(i64::MAX.into(), 64, LITTLE).to_int(LITTLE),
            i64::max_value() as i128
        );
        assert_eq!(
            Bitstring::from_int(i64::MAX.into(), 64, BIG).to_int(BIG),
            i64::max_value() as i128
        );
        assert_eq!(
            Bitstring::from(i128::MAX.to_le_bytes().to_vec()).to_int(LITTLE),
            i128::MAX
        );
        assert_eq!(
            Bitstring::from(i128::MIN.to_le_bytes().to_vec()).to_int(LITTLE),
            i128::MIN
        );
    }

    #[test]
    fn test_from_bin_str() {
        let s = "10111001001";
        let bs = Bitstring::from_bin_str(s).unwrap();
        assert_eq!(bs.len(), s.len());
        assert_eq!(s, bs.to_bin_string().as_str());
        assert_eq!(Err(7), Bitstring::from_bin_str("11_11_02"));
        let bs = Bitstring::from_bin_str("1 1 1 1 1 1 1").unwrap();
        assert_eq!(*bs.data, vec![0xfe]);
    }

    #[test]
    fn test_from_hex_str() {
        let s = "fe1";
        let bs = Bitstring::from_hex_str(s).unwrap();
        assert_eq!(bs.len(), 12);
        assert_eq!(bs.to_bytes(), vec![0xfe, 0x1]);
        assert_eq!(bs.to_hex_string(), s);
        let bs = Bitstring::from_hex_str("f f 00 E _ E 11").unwrap();
        assert_eq!(bs.len(), 32);
        assert_eq!(bs.to_bytes(), vec![0xff, 0x00, 0xee,0x11]);
        assert_eq!(Err(1), Bitstring::from_hex_str("FX"));
    }

    #[test]
    fn test_cut() {
        assert_eq!((1, 1), cut_bits(0b1_0000_100, 0, 1));
        assert_eq!((0, 4), cut_bits(0b1_0000_100, 1, 5));
        assert_eq!((4, 3), cut_bits(0b1_0000_100, 5, 8));
        assert_eq!((1, 1), cut_bits(0b1_0000_100, 8, 9));
        assert_eq!((4, 3), cut_bits(0b1_0000_100, 5, 100));
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
        let s = Bitstring::from(vec![0b11000000]);
        let res: Vec<_> = s.bits().collect();
        assert_eq!(vec![1, 1, 0, 0, 0, 0, 0, 0], res);
    }

    #[test]
    fn test_iter8() {
        let a = Bitstring::from(vec![0xaf, 0xbc]);
        let mut it = a.iter8();
        assert_eq!(Some((0xaf, 8)), it.next());
        assert_eq!(Some((0xbc, 8)), it.next());
        assert_eq!(None, it.next());
        // unaligned
        let s = Bitstring::from(vec![0xab, 0xcd]);
        let b = s.seek(4).unwrap();
        let mut it = b.iter8();
        assert_eq!(Some((0xbc, 8)), it.next());
        assert_eq!(Some((0xd, 4)), it.next());
        assert_eq!(None, it.next());
    }
}
