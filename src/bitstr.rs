use std::convert::From;
use std::ops::Range;
use std::rc::Rc;

#[derive(PartialEq, Clone, Copy)]
pub enum Byteorder {
    Little,
    Big,
}

pub const LITTLE: Byteorder = Byteorder::Little;
pub const BIG: Byteorder = Byteorder::Big;

#[cfg(target_endian = "little")]
pub const NATIVE: Byteorder = LITTLE;

#[cfg(target_endian = "big")]
pub const NATIVE: Byteorder = BIG;

type BitstrRange = Range<usize>;

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

use std::fmt;

impl fmt::Debug for Bitstr {
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
            self.data[idx] |= val << (7 - (self.len % 8));
        }
        self.len += 1;
    }

    pub fn finish(self) -> Bitstr {
        let mut res = Bitstr::from(self.data);
        res.range.end = self.len;
        res
    }
}

#[derive(Clone, Default)]
pub struct Bitstr {
    range: BitstrRange,
    data: Rc<Cow<'static, [u8]>>,
}

impl Bitstr {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn from_bin_str(s: &str) -> Result<Bitstr, usize> {
        let mut tmp = BitvecBuilder::default();
        for (pos, c) in s.chars().enumerate() {
            if c.is_ascii_whitespace() {
                continue;
            }
            match c {
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

    pub fn from_hex_str(s: &str) -> Result<Bitstr, usize> {
        let mut n = 0;
        let mut buf = Vec::new();
        for (pos, c) in s.chars().enumerate() {
            if c.is_ascii_whitespace() {
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
        let mut result = Bitstr::from(buf);
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

    pub fn is_u8_slice(&self) -> bool {
        self.start() % 8 == 0 && self.is_bytestr()
    }

    pub fn is_bytestr(&self) -> bool {
        (self.range.end - self.range.start) % 8 == 0
    }

    pub fn seek(&self, pos: usize) -> Option<Bitstr> {
        if self.range.start <= pos && pos <= self.range.end {
            let mut s = self.clone();
            s.range.start = pos;
            Some(s)
        } else {
            None
        }
    }

    pub fn read(&mut self, num_bits: usize) -> Option<Bitstr> {
        let pos = self.range.start + num_bits;
        if pos > self.range.end {
            return None;
        }
        let mut result = self.clone();
        result.range.end = pos;
        self.range.start = pos;
        Some(result)
    }

    pub fn peek(&self, num_bits: usize) -> Option<Bitstr> {
        let end = self.start() + num_bits;
        if self.range.start <= end && end <= self.range.end {
            let mut s = self.clone();
            s.range.end = end;
            Some(s)
        } else {
            None
        }
    }

    pub fn substr(&self, start: usize, end: usize) -> Option<Bitstr> {
        if start <= end && self.range.start <= start && end <= self.range.end {
            let mut s = self.clone();
            s.range = start..end;
            Some(s)
        } else {
            None
        }
    }

    pub fn split_at(&self, bit_index: usize) -> Option<(Bitstr, Bitstr)> {
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

    pub fn to_int(&self, order: Byteorder) -> i128 {
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

    pub fn to_uint(&self, order: Byteorder) -> u128 {
        let mut acc: u128 = 0;
        let mut pos = self.start();
        let end = self.end();
        let data_bytes = &self.data[self.bytes_range()];
        if order == BIG {
            for byte in data_bytes {
                let (val, n) = cut_bits(*byte, pos, end);
                acc = (acc << n) | (val as u128);
                pos += n;
            }
        } else {
            for byte in data_bytes {
                let (val, n) = cut_bits(*byte, pos, end);
                acc |= (val as u128) << (pos - self.start()) as u32;
                pos += n;
            }
        }
        acc
    }

    pub fn from_int(val: i128, num_bits: usize, order: Byteorder) -> Bitstr {
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
        Bitstr {
            range: BitstrRange::from(0..num_bits),
            data: Rc::new(Cow::Owned(tmp)),
        }
    }

    pub fn to_f32(&self, order: Byteorder) -> f32 {
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

    pub fn to_f64(&self, order: Byteorder) -> f64 {
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

    pub fn from_f32(val: f32, order: Byteorder) -> Bitstr {
        let bytes = if order == BIG {
            val.to_be_bytes()
        } else {
            val.to_le_bytes()
        };
        Bitstr::from(bytes.to_vec())
    }

    pub fn from_f64(val: f64, order: Byteorder) -> Bitstr {
        let bytes = if order == BIG {
            val.to_be_bytes()
        } else {
            val.to_le_bytes()
        };
        Bitstr::from(bytes.to_vec())
    }

    pub fn to_bytes(&self) -> Option<Vec<u8>> {
        if self.is_bytestr() {
            if self.start() % 8 == 0 {
                self.slice().map(|s| s.to_vec())
            } else {
                Some(self.to_bytes_with_padding())
            }
        } else {
            None
        }
    }

    pub fn to_bytes_with_padding(&self) -> Vec<u8> {
        let cap = (self.len() + 8) / 8;
        let mut bytes = Vec::with_capacity(cap);
        bytes.extend(self.iter8().map(|(val, _)| val));
        bytes
    }

    pub fn bytestr<'a>(&'a self) -> Option<Cow<'a, [u8]>> {
        if let Some(data) = self.slice() {
            Some(Cow::Borrowed(data))
        } else if self.is_bytestr() {
            Some(Cow::Owned(self.to_bytes_with_padding()))
        } else {
            None
        }
    }

    pub fn slice(&self) -> Option<&[u8]> {
        if self.start() % 8 == 0 && self.is_bytestr() {
            Some(&self.data[self.bytes_range()])
        } else {
            None
        }
    }

    pub fn bytes_range(&self) -> BitstrRange {
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

    pub fn detach(self) -> Bitstr {
        if Rc::strong_count(&self.data) == 1 {
            self
        } else if self.len() == 0 {
            Bitstr::new()
        } else {
            let end = self.len();
            let mut tmp = Vec::with_capacity(upper_bound_index(end));
            tmp.extend(self.iter8().map(|(val, n)| val << (8 - n)));
            Bitstr {
                range: BitstrRange::from(0..end),
                data: Rc::new(Cow::from(tmp)),
            }
        }
    }

    fn data_mut(&mut self) -> &mut Vec<u8> {
        Rc::make_mut(&mut self.data).to_mut()
    }

    fn append_bits_mut(mut self, tail: &Bitstr) -> Bitstr {
        if self.is_u8_slice() && tail.is_u8_slice() {
            self.data_mut().extend_from_slice(tail.slice().unwrap());
            self.range.end = self.range.end + tail.len();
            return self;
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
        self.range = BitstrRange::from(start..pos);
        self
    }

    pub fn append(self, tail: &Bitstr) -> Bitstr {
        self.detach().append_bits_mut(tail)
    }

    pub fn insert(self, bit_index: usize, s: &Bitstr) -> Option<Bitstr> {
        let (left, right) = self.split_at(bit_index)?;
        Some(left.detach().append_bits_mut(&s).append_bits_mut(&right))
    }

    pub fn invert(self) -> Bitstr {
        let r = self.range.clone();
        let mut s = self.detach();
        let data = s.data_mut();
        for pos in r {
            let i = pos / 8;
            data[i] ^= 1 << (7 - (pos % 8));
        }
        s
    }

    pub fn eq_with(&self, other: &Bitstr) -> bool {
        if self.len() != other.len() {
            false
        } else if self.is_u8_slice() && other.is_u8_slice() {
            self.slice() == other.slice()
        } else {
            self.iter8().eq(other.iter8())
        }
    }
}

impl PartialEq for Bitstr {
    fn eq(&self, other: &Bitstr) -> bool {
        self.eq_with(other)
    }
}

impl<'a> From<&'static [u8]> for Bitstr {
    fn from(s: &'static [u8]) -> Self {
        Bitstr {
            range: BitstrRange::from(0..(s.len() * 8)),
            data: Rc::new(Cow::Borrowed(s)),
        }
    }
}

impl<'a> From<&'static str> for Bitstr {
    fn from(s: &'static str) -> Self {
        Bitstr::from(s.as_bytes())
    }
}

impl From<Vec<u8>> for Bitstr {
    fn from(v: Vec<u8>) -> Self {
        Bitstr {
            range: BitstrRange::from(0..(v.len() * 8)),
            data: Rc::new(Cow::Owned(v)),
        }
    }
}

#[derive(Clone)]
pub struct Bits<'a> {
    pos: usize,
    bs: &'a Bitstr,
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
    bs: &'a Bitstr,
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
            val = (val << n2) | val2;
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
        let bs = Bitstr::from(vec![0x7f]);
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
        let mut a = Bitstr::from(vec![0xff, 0x2f]);
        let b = a.read(8).unwrap().detach();
        assert_eq!(b.range, (0..8));
        assert_eq!(b.to_bytes().unwrap(), vec![0xff]);
        let c = a.read(4).unwrap().detach();
        assert_eq!(c.range, (0..4));
        assert_eq!(c.to_bytes_with_padding(), vec![2]);
        assert_eq!(c.detach().data[0], 0x20);
        assert_eq!(a.range, (12..16));
        let mut x = Bitstr::from(vec![0x12, 0x34]);
        x.read(4).unwrap();
        assert_eq!(x.read(8).unwrap().to_bytes().unwrap(), vec![0x23]);
    }

    #[test]
    fn test_cow() {
        static X: [u8; 1] = [255];
        let a = Bitstr::from(&X[..]);
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
        let a = Bitstr::from(vec![0x12, 0x34]);
        let b = Bitstr::from(vec![0x56, 0x78]);
        assert_eq!(
            a.append(&b).to_bytes().unwrap(),
            vec![0x12, 0x34, 0x56, 0x78]
        );
        // unaligned
        let mut g = Bitstr::from(vec![0b11000001, 0b10011001]);
        let h = g.read(7).unwrap();
        let f = g.read(9).unwrap();
        assert_eq!(
            h.append(&f).to_bytes().unwrap(),
            vec![0b11000001, 0b10011001]
        );
        let mut w = Bitstr::from(vec![0xab, 0xcd, 0xef]);
        let x = w.read(9).unwrap();
        let y = w.read(13).unwrap();
        let z = w.read(1).unwrap();
        let r = w.read(1).unwrap();
        assert_eq!(
            x.append(&y).append(&z).append(&r).to_bytes().unwrap(),
            vec![0xab, 0xcd, 0xef]
        );
        let mut s = Bitstr::from(vec![0x13]);
        let a = s.read(4).unwrap();
        let b = s.read(4).unwrap();
        assert_eq!(b.append(&a).to_bytes().unwrap(), vec![0x31]);

        let mut s = Bitstr::from_bin_str("0 1000000 0 0111011 0 1111000").unwrap();
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
        let s = Bitstr::from(vec![0x12, 0x34]);
        assert_eq!(vec![0x34], s.seek(8).unwrap().to_bytes().unwrap());
        assert_eq!(&s, &s.seek(0).unwrap());
        assert_eq!(Bitstr::new(), s.seek(16).unwrap());
        assert_eq!(None, s.seek(17));
    }

    #[test]
    fn test_peek() {
        let s = Bitstr::from(vec![0x12, 0x34, 0x56]);
        assert_eq!(vec![0x12], s.peek(8).unwrap().to_bytes().unwrap());
        assert_eq!(None, s.peek(25));
        assert_eq!(Bitstr::new(), s.peek(0).unwrap());
        assert_eq!(&s, &s.peek(24).unwrap());
    }

    #[test]
    fn test_substr() {
        let s = Bitstr::from(vec![0x12, 0x34, 0x56]);
        assert_eq!(vec![0x34], s.substr(8, 16).unwrap().to_bytes().unwrap());
        assert_eq!(&s, &s.substr(0, 24).unwrap());
        assert_eq!(None, s.substr(0, 25));
        assert_eq!(None, s.substr(24, 0));
        assert_eq!(Bitstr::new(), s.substr(0, 0).unwrap());
    }

    #[test]
    fn test_insert() {
        let f = Bitstr::from_bin_str("1111").unwrap();
        let res = Bitstr::from(vec![0xaa, 0xbb])
            .insert(4, &f)
            .unwrap()
            .insert(16, &f)
            .unwrap();
        assert_eq!(vec![0xaf, 0xab, 0xfb], res.to_bytes().unwrap());
        let z5 = Bitstr::from_bin_str("00000").unwrap();
        let res = Bitstr::from_bin_str("111111")
            .unwrap()
            .insert(3, &z5)
            .unwrap();
        assert_eq!(Bitstr::from_bin_str("11100000111").unwrap(), res);
    }

    #[test]
    fn test_invert() {
        let mut a = Bitstr::from_bin_str("01111111 01111111").unwrap();
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
        let bs = Bitstr::from(vec![0x7f]);
        assert_eq!(bs.to_int(LITTLE), 127);
        assert_eq!(bs.to_uint(LITTLE), 127);

        let bs = Bitstr::from(vec![0xff]);
        assert_eq!(bs.to_uint(LITTLE), 255);
        assert_eq!(bs.to_int(LITTLE), -1);

        let bs = Bitstr::from(vec![0xfe]);
        assert_eq!(bs.to_uint(LITTLE), 254);
        assert_eq!(bs.to_int(LITTLE), -2);

        let bs = Bitstr::from(vec![0xff, 0xff]);
        assert_eq!(bs.to_int(LITTLE), -1);

        let bs = Bitstr::from(vec![0xff, 0x7f]);
        assert_eq!(bs.to_int(LITTLE), i16::max_value() as i128);

        let bs = Bitstr::from(vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]);
        assert_eq!(bs.to_int(LITTLE), i64::max_value() as i128);

        let bs = Bitstr::from(vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]);
        assert_eq!(bs.to_int(LITTLE), -1);
        assert_eq!(bs.to_uint(LITTLE), u64::max_value() as u128);

        let f = f32::MAX;
        let le = f.to_le_bytes().to_vec();
        assert_eq!(Bitstr::from(le).to_f32(LITTLE), f);
        let be = f.to_be_bytes().to_vec();
        assert_eq!(Bitstr::from(be).to_f32(BIG), f);

        let f: f32 = 1.234;
        assert_eq!(
            f.to_le_bytes().to_vec(),
            Bitstr::from_f32(f, LITTLE).to_bytes().unwrap()
        );
        assert_eq!(
            f.to_be_bytes().to_vec(),
            Bitstr::from_f32(f, BIG).to_bytes().unwrap()
        );
    }

    #[test]
    fn test_nums() {
        assert_eq!(Bitstr::from_int(0, 0, BIG).to_bytes().unwrap(), vec![]);
        let bs = Bitstr::from_int(1, 3, BIG);
        assert_eq!(bs.to_int(BIG), 1);
        assert_eq!(bs.to_bytes_with_padding(), vec![1]);
        let ls = Bitstr::from_int(1, 3, LITTLE);
        assert_eq!(ls.to_int(LITTLE), 1);
        assert_eq!(ls.to_bytes_with_padding(), vec![1]);

        assert_eq!(
            &Bitstr::from_int(0x12345678, 32, LITTLE).to_bytes().unwrap(),
            &0x12345678u32.to_le_bytes()
        );
        assert_eq!(
            &Bitstr::from_int(0x12345678, 32, BIG).to_bytes().unwrap(),
            &0x12345678u32.to_be_bytes()
        );
        assert_eq!(
            &Bitstr::from_int(0x7FFFFFFF, 32, LITTLE).to_bytes().unwrap(),
            &0x7FFFFFFFu32.to_le_bytes()
        );
        assert_eq!(Bitstr::from_int(0xFFFF_FFFF, 32, LITTLE).to_int(LITTLE), -1);
        assert_eq!(
            Bitstr::from_int(0x7FFF_FFFF, 32, LITTLE).to_int(LITTLE),
            i32::max_value() as i128
        );
        assert_eq!(Bitstr::from_int(0xFFFF_FFFF, 32, BIG).to_int(BIG), -1);
        assert_eq!(
            Bitstr::from_int(0x7FFF_FFFF, 32, BIG).to_int(BIG),
            i32::max_value() as i128
        );
        assert_eq!(
            &Bitstr::from_int(i64::MAX.into(), 64, LITTLE)
                .to_bytes()
                .unwrap(),
            &i64::max_value().to_le_bytes()
        );
        assert_eq!(
            &Bitstr::from_int(i64::MAX.into(), 64, BIG)
                .to_bytes()
                .unwrap(),
            &i64::max_value().to_be_bytes()
        );
        assert_eq!(
            Bitstr::from_int(i64::MAX.into(), 64, LITTLE).to_int(LITTLE),
            i64::max_value() as i128
        );
        assert_eq!(
            Bitstr::from_int(i64::MAX.into(), 64, BIG).to_int(BIG),
            i64::max_value() as i128
        );
        assert_eq!(
            Bitstr::from(i128::MAX.to_le_bytes().to_vec()).to_int(LITTLE),
            i128::MAX
        );
        assert_eq!(
            Bitstr::from(i128::MIN.to_le_bytes().to_vec()).to_int(LITTLE),
            i128::MIN
        );
    }

    #[test]
    fn test_from_bin_str() {
        let s = "10111001001";
        let bs = Bitstr::from_bin_str(s).unwrap();
        assert_eq!(bs.len(), s.len());
        assert_eq!(s, bs.to_bin_string().as_str());
        assert_eq!(Err(7), Bitstr::from_bin_str("11 11 02"));
        let bs = Bitstr::from_bin_str("1 1 1 1 1 1 1").unwrap();
        assert_eq!(*bs.data, vec![0xfe]);
    }

    #[test]
    fn test_from_hex_str() {
        let s = "fe1";
        let bs = Bitstr::from_hex_str(s).unwrap();
        assert_eq!(bs.len(), 12);
        assert_eq!(bs.to_bytes_with_padding(), vec![0xfe, 0x1]);
        assert_eq!(bs.to_hex_string(), s);
        let bs = Bitstr::from_hex_str("f f 00 E  E 11").unwrap();
        assert_eq!(bs.len(), 32);
        assert_eq!(bs.to_bytes_with_padding(), vec![0xff, 0x00, 0xee, 0x11]);
        assert_eq!(Err(1), Bitstr::from_hex_str("FX"));
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
        let s = Bitstr::from(vec![0b11000000]);
        let res: Vec<_> = s.bits().collect();
        assert_eq!(vec![1, 1, 0, 0, 0, 0, 0, 0], res);
    }

    #[test]
    fn test_eq_with() {
        let a = Bitstr::from(vec![0x12, 0x34]);
        let b = Bitstr::from(vec![0x12, 0x34]);
        assert!(a.eq_with(&b));
        let c = a.seek(8).unwrap();
        let d = Bitstr::from(vec![0x34]);
        assert!(c.eq_with(&d));
        assert!(!c.eq_with(&a));
        let s1 = Bitstr::from_bin_str("1000 1000 111").unwrap();
        let s2 = s1.clone();
        assert!(s1.eq_with(&s2));
        let s3 = Bitstr::from_bin_str("1000 1000 1111").unwrap();
        assert!(!s1.eq_with(&s3));
        let s4 = Bitstr::from_bin_str("1000 1000 011").unwrap();
        assert!(!s1.eq_with(&s4));
    }

    #[test]
    fn test_iter8() {
        let a = Bitstr::from(vec![0xaf, 0xbc]);
        let mut it = a.iter8();
        assert_eq!(Some((0xaf, 8)), it.next());
        assert_eq!(Some((0xbc, 8)), it.next());
        assert_eq!(None, it.next());
        // unaligned
        let s = Bitstr::from(vec![0xab, 0xcd]);
        let b = s.seek(4).unwrap();
        let mut it = b.iter8();
        assert_eq!(Some((0xbc, 8)), it.next());
        assert_eq!(Some((0xd, 4)), it.next());
        assert_eq!(None, it.next());
    }
}
