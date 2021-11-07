use std::fmt::Write;
use crate::bitstring::*;
use crate::cell::*;
use crate::error::*;
use crate::prelude::*;

#[derive(Default)]
pub struct BitstrMod {
    big_endian: Xref,
    dump_start: Xref,
    input: Xref,
    last_read: Xref,
    input_deck: Xref,
}

pub fn load(xs: &mut Xstate) -> Xresult {
    let mut m = BitstrMod::default();
    m.big_endian = xs.defvar("big-endian?", ZERO)?;
    m.dump_start = xs.defvar("bitstr/dump-start", Cell::Int(0))?;
    m.input = xs.defvar("bitstr/input", Cell::Bitstr(Bitstring::new()))?;
    m.last_read = xs.defvar("bitstr/last-read", Cell::Bitstr(Bitstring::new()))?;
    m.input_deck = xs.defvar("bitstr/input-deck", Cell::Vector(Xvec::new()))?;
    xs.bitstr_mod = m;

    xs.defword("bits", bin_read_bitstring)?;
    xs.defword("bytes", bin_read_bytes)?;
    xs.defword("kbytes", bin_read_kbytes)?;
    xs.defword("mbytes", bin_read_mbytes)?;
    xs.defword("b>", to_num_bytes)?;
    xs.defword("kb>", to_num_kbytes)?;
    xs.defword("mb>", to_num_mbytes)?;
    xs.defword("int", bin_read_signed)?;
    xs.defword("uint", bin_read_unsigned)?;
    xs.defword("bitstr-append", bitstring_append)?;
    xs.defword("bitstr-invert", bitstring_invert)?;
    xs.defword(">bitstr", to_bitstring)?;
    xs.defword("bitstr>int", bitstring_to_signed)?;
    xs.defword("bitstr>uint", bitstring_to_unsigned)?;
    xs.defword("big-endian", |xs| set_byteorder(xs, BIG))?;
    xs.defword("little-endian", |xs| set_byteorder(xs, LITTLE))?;
    xs.defword("?", bin_match)?;
    xs.defword("u8", |xs| read_unsigned_n(xs, 8))?;
    xs.defword("u16", |xs| read_unsigned_n(xs, 16))?;
    xs.defword("u32", |xs| read_unsigned_n(xs, 32))?;
    xs.defword("u64", |xs| read_unsigned_n(xs, 64))?;
    xs.defword("u8be", |xs| read_unsigned_nb(xs, 8, BIG))?;
    xs.defword("u16be", |xs| read_unsigned_nb(xs, 16, BIG))?;
    xs.defword("u32be", |xs| read_unsigned_nb(xs, 32, BIG))?;
    xs.defword("u64be", |xs| read_unsigned_nb(xs, 64, BIG))?;
    xs.defword("u8le", |xs| read_unsigned_nb(xs, 8, LITTLE))?;
    xs.defword("u16le", |xs| read_unsigned_nb(xs, 16, LITTLE))?;
    xs.defword("u32le", |xs| read_unsigned_nb(xs, 32, LITTLE))?;
    xs.defword("u64le", |xs| read_unsigned_nb(xs, 64, LITTLE))?;
    xs.defword("i8", |xs| read_signed_n(xs, 8))?;
    xs.defword("i16", |xs| read_signed_n(xs, 16))?;
    xs.defword("i32", |xs| read_signed_n(xs, 32))?;
    xs.defword("i64", |xs| read_signed_n(xs, 64))?;
    xs.defword("i8be", |xs| read_signed_nb(xs, 8, BIG))?;
    xs.defword("i16be", |xs| read_signed_nb(xs, 16, BIG))?;
    xs.defword("i32be", |xs| read_signed_nb(xs, 32, BIG))?;
    xs.defword("i64be", |xs| read_signed_nb(xs, 64, BIG))?;
    xs.defword("i8le", |xs| read_signed_nb(xs, 8, LITTLE))?;
    xs.defword("i16le", |xs| read_signed_nb(xs, 16, LITTLE))?;
    xs.defword("i32le", |xs| read_signed_nb(xs, 32, LITTLE))?;
    xs.defword("i64le", |xs| read_signed_nb(xs, 64, LITTLE))?;
    xs.defword("f32", |xs| read_float_n(xs, 32))?;
    xs.defword("f32le", |xs| read_float_nb(xs, 32, LITTLE))?;
    xs.defword("f32be", |xs| read_float_nb(xs, 32, BIG))?;
    xs.defword("f64", |xs| read_float_n(xs, 64))?;
    xs.defword("f64le", |xs| read_float_nb(xs, 64, LITTLE))?;
    xs.defword("f64be", |xs| read_float_nb(xs, 64, BIG))?;
    xs.defword("i8>bitstr", |xs| num_to_bitstr(xs, 8, i8::MIN.into(), i8::MAX.into()))?;
    xs.defword("u8>bitstr", |xs| num_to_bitstr(xs, 8, u8::MIN.into(), u8::MAX.into()))?;
    xs.defword("i16>bitstr", |xs| num_to_bitstr(xs, 16, i16::MIN.into(), i16::MAX.into()))?;
    xs.defword("u16>bitstr", |xs| num_to_bitstr(xs, 16, u16::MIN.into(), u16::MAX.into()))?;
    xs.defword("i32>bitstr", |xs| num_to_bitstr(xs, 32, i32::MIN.into(), i32::MAX.into()))?;
    xs.defword("u32>bitstr", |xs| num_to_bitstr(xs, 32, u32::MIN.into(), u32::MAX.into()))?;
    xs.defword("i64>bitstr", |xs| num_to_bitstr(xs, 64, i64::MIN.into(), i64::MAX.into()))?;
    xs.defword("u64>bitstr", |xs| num_to_bitstr(xs, 64, u64::MIN as Xint, u64::MAX as Xint))?;
    xs.defword("seek", seek_bin)?;
    xs.defword("offset", offset_bin)?;
    xs.defword("remain", remain_bin)?;
    xs.defword("find", find_bin)?;
    xs.defword("dump", bitstr_dump)?;
    xs.defword("dump-at", bitstr_dump_at)?;
    xs.defword("bitstr-open", bitstring_open)?;
    xs.defword("bitstr-close", bitstring_close)?;
    OK
}

fn box_read_error(s: Bitstring, n: usize) -> Xerr {
    Xerr::BitReadError(Box::new((s, n)))
}

fn find_bin(xs: &mut Xstate) -> Xresult {
    let pat = bitstring_from(xs.pop_data()?)?;
    let s = bitstr_input(xs)?;
    if !(pat.is_bytestring() && s.is_bytestring()) {
        return Err(Xerr::UnalignedBitstr);
    }
    if let Some(pos) = twoway::find_bytes(s.slice(), pat.slice()) {
        let offs = s.start() + pos * 8;
        xs.push_data(Cell::from(offs))
    } else {
        xs.push_data(Cell::Nil)
    }
}

fn seek_bin(xs: &mut Xstate) -> Xresult {
    let pos = xs.pop_data()?.into_usize()?;
    let mut s = bitstr_input(xs)?.clone();
    if s.seek(pos).is_none() {
        Err(Xerr::BitSeekError(Box::new((s, pos))))
    } else {
        xs.set_var(xs.bitstr_mod.input, Cell::Bitstr(s)).map(|_| ())
    }
}

fn bitstr_input(xs: &mut Xstate) -> Xresult1<&Bitstring> {
    match xs.get_var(xs.bitstr_mod.input)? {
        Cell::Bitstr(bs) => Ok(bs),
        _ => Err(Xerr::TypeError),
    }
}

fn offset_bin(xs: &mut Xstate) -> Xresult {
    let offs = bitstr_input(xs)?.start() as Xint;
    xs.push_data(Cell::Int(offs))
}

fn remain_bin(xs: &mut Xstate) -> Xresult {
    let n = bitstr_input(xs)?.len() as Xint;
    xs.push_data(Cell::Int(n))
}

fn dump_start(xs: &mut Xstate) -> Xresult1<usize> {
    xs.get_var(xs.bitstr_mod.dump_start)?.to_usize()
}

fn dump_start_move(xs: &mut Xstate, pos: usize) -> Xresult {
    xs.set_var(xs.bitstr_mod.dump_start, Cell::from(pos))?;
    OK
}

fn bitstr_dump_at(xs: &mut Xstate) -> Xresult {
    let start = xs.pop_data()?.into_usize()?;
    let end = start + 16 * 8 * 8;
    bitstr_dump_range(xs, start..end, 8)?;
    dump_start_move(xs, end)
}

fn bitstr_dump(xs: &mut Xstate) -> Xresult {
    let start = dump_start(xs)?;
    let end = start + 16 * 8 * 8;
    bitstr_dump_range(xs, start..end, 8)?;
    dump_start_move(xs, end)
}

pub fn print_dump(xs: &mut Xstate, rows: usize, ncols: usize) -> Xresult {
    let start = bitstr_input(xs)?.start();
    let end = start + (rows * ncols * 8);
    bitstr_dump_range(xs, start..end, ncols)
}

fn bitstr_dump_range(xs: &mut Xstate, r: BitstringRange, ncols: usize) -> Xresult {
    let mut input = bitstr_input(xs)?.clone();
    let marker = input.start();
    if input.seek(r.start).is_none() {
        return Err(Xerr::BitSeekError(Box::new((input, r.start))));
    }
    let part = input.read(r.len().min(input.len())).unwrap();
    let mut buf = String::new();
    let mut pos = part.start();
    let mut hex  = String::new();
    let mut ascii  = String::new();
    let mut it = part.iter8();
    while pos < part.end() {
        write_dump_position(&mut buf, pos, part.end());
        buf.push(':');
        for _ in 0..ncols {
            if let Some((x, nbits)) = it.next() {
                buf.push(if pos <= marker && marker <= (pos + nbits as usize) { '*' } else { ' ' });
                write!(buf, "{:02x}", x).unwrap();
                pos += nbits as usize;
                let c = std::char::from_u32(x as u32).unwrap();
                if c.is_ascii_graphic() {
                    ascii.push(c);
                } else {
                    ascii.push('.');
                }
            } else {
                hex.push_str("  ");
            }
        }
        buf.push_str(&hex);
        buf.push_str(" | ");
        buf.push_str(&ascii);
        buf.push('\n');
        xs.print(&buf);
        buf.clear();
        hex.clear();
        ascii.clear();
    }
    OK
}
    
fn write_dump_position(buf: &mut String, start: usize, end: usize) {
    let pos = start / 8;
    let max = end / 8;
    if max <= 0xff {
        write!(buf, "{:02x}", pos).unwrap();
    } else if max <= 0xffff {
        write!(buf, "{:04x}", pos).unwrap();
    } else if max <= 0xffffff {
        write!(buf, "{:06x}", pos).unwrap();
    } else {
        write!(buf, "{:08x}", pos).unwrap();
    }
    if start % 8 > 0 {
        write!(buf, ".{}", start % 8).unwrap();
    }
}

fn bitstring_open(xs: &mut Xstate) -> Xresult {
    let new_bin = bitstring_from(xs.pop_data()?)?;
    let old_bin = bitstr_input(xs)?.clone();
    let deck = match xs.get_var(xs.bitstr_mod.input_deck)? {
        Cell::Vector(v) => v.push_back(Cell::Bitstr(old_bin)),
        _ => return Err(Xerr::TypeError),
    };
    xs.set_var(xs.bitstr_mod.input_deck, Cell::Vector(deck))?;
    xs.set_var(xs.bitstr_mod.input, Cell::Bitstr(new_bin))?;
    OK
}

fn bitstring_close(xs: &mut Xstate) -> Xresult {
    let mut deck = xs.get_var(xs.bitstr_mod.input_deck)?.clone().into_vector()?;
    if let Some(bin) = deck.last().cloned() {
        deck.drop_last_mut();
        xs.set_var(xs.bitstr_mod.input_deck, Cell::Vector(deck))?;
        xs.set_var(xs.bitstr_mod.input, bin)?;
    }
    OK
}

fn bitstring_append(xs: &mut Xstate) -> Xresult {
    let head = xs.pop_data()?.into_bitstring()?;
    let tail = xs.pop_data()?;
    let tail = bitstring_from(tail)?;
    let result = head.append(&tail);
    xs.push_data(Cell::Bitstr(result))
}

fn bitstring_invert(xs: &mut Xstate) -> Xresult {
    let s = xs.pop_data()?.into_bitstring()?;
    xs.push_data(Cell::Bitstr(s.invert()))
}

fn bitstring_to_signed(xs: &mut Xstate) -> Xresult {
    let s = xs.pop_data()?.into_bitstring()?;
    let bo = default_byteorder(xs)?;
    if s.len() > 128 {
        return Err(Xerr::IntegerOverflow);
    }
    let x = s.to_int(bo);
    //NOTE: result truncated!
    xs.push_data(Cell::Int(x as Xint))
}

fn bitstring_to_unsigned(xs: &mut Xstate) -> Xresult {
    let s = xs.pop_data()?.into_bitstring()?;
    let bo = default_byteorder(xs)?;
    if s.len() > 128 {
        return Err(Xerr::IntegerOverflow);
    }
    let x = s.to_uint(bo) as Xint;
    xs.push_data(Cell::Int(x))
}

fn num_to_bitstr(xs: &mut Xstate, num_bits: usize, min: Xint, max: Xint) -> Xresult {
    let val = xs.pop_data()?.into_int()?;
    let bo = default_byteorder(xs)?;
    if val < min || val > max {
        return Err(Xerr::IntegerOverflow);
    }
    let s = if val < 0 {
        Bitstring::from_i64(val as i64, num_bits, bo)
    } else {
        Bitstring::from_u64(val as u64, num_bits, bo)
    };
    xs.push_data(Cell::Bitstr(s))
}

fn to_bitstring(xs: &mut Xstate) -> Xresult {
    let val = xs.pop_data()?;
    let s = bitstring_from(val)?;
    xs.push_data(Cell::Bitstr(s))
}

pub fn bitstring_from(val: Cell) -> Xresult1<Bitstring> {
    match val {
        Cell::Str(s) => Ok(Bitstring::from(s.into_bytes())),
        Cell::Vector(v) => {
            let mut tmp = Xbitstr::new();
            for x in v.iter() {
                match x {
                    Cell::Int(i) => {
                        if 0 <= *i && *i <= 255 {
                            tmp = tmp.append(&Xbitstr::from(vec![*i as u8]));
                        } else {
                            return Err(Xerr::IntegerOverflow);
                        }
                    }
                    Cell::Str(s) => {
                        tmp = tmp.append(&Xbitstr::from(s.as_bytes().to_vec()));
                    }
                    Cell::Bitstr(s) => {
                        tmp = tmp.append(&s);
                    }
                    _ => return Err(Xerr::TypeError),
                }
            }
            Ok(Bitstring::from(tmp))
        }
        Cell::Bitstr(s) => Ok(s),
        _ => Err(Xerr::TypeError)
    }
}

fn take_length(xs: &mut Xstate) -> Xresult1<usize> {
    let n = xs.pop_data()?.into_int()?;
    Ok(n as usize)
}

fn set_rest(xs: &mut Xstate, rest: Bitstring) -> Xresult {
    xs.set_var(xs.bitstr_mod.input, Cell::Bitstr(rest)).map(|_| ())
}

fn set_last_chunk(xs: &mut Xstate, s: Bitstring) -> Xresult {
    xs.set_var(xs.bitstr_mod.last_read, Cell::Bitstr(s)).map(|_| ())
}

fn set_byteorder(xs: &mut Xstate, bo: Xbyteorder) -> Xresult {
    xs.set_var(xs.bitstr_mod.big_endian, if bo == LITTLE { ZERO } else { ONE })
        .map(|_| ())
}

fn default_byteorder(xs: &mut Xstate) -> Xresult1<Xbyteorder> {
    if xs.get_var(xs.bitstr_mod.big_endian)? == &ZERO {
        Ok(LITTLE)
    } else {
        Ok(BIG)
    }
}

fn bin_match(xs: &mut Xstate) -> Xresult {
    let val = xs.pop_data()?;
    let pat = bitstring_from(val)?;
    let (s, rest) = read_bitstring(xs, pat.len())?;
    if let Err(pos) = s.match_with(&pat) {
        let err = Box::new((s, pat, pos));
        return Err(Xerr::BitMatchError(err));
    }
    set_last_chunk(xs, s)?;
    set_rest(xs, rest)
}

fn read_bits(xs: &mut Xstate, n: usize) -> Xresult {
    let (s, rest) = read_bitstring(xs, n)?;
    set_last_chunk(xs, s.clone())?;
    xs.push_data(Cell::Bitstr(s))?;
    set_rest(xs, rest)
}

fn bin_read_bytes(xs: &mut Xstate) -> Xresult {
    let n = take_length(xs)?;
    read_bits(xs, n * 8)
}

fn bin_read_kbytes(xs: &mut Xstate) -> Xresult {
    let n = take_length(xs)?;
    read_bits(xs, n * 8 * 1024)
}

fn bin_read_mbytes(xs: &mut Xstate) -> Xresult {
    let n = take_length(xs)?;
    read_bits(xs, n * 8 * 1024 * 1024)
}

fn to_num_bytes(xs: &mut Xstate) -> Xresult {
    let n = take_length(xs)?;
    xs.push_data(Cell::from(n * 8))
}

fn to_num_kbytes(xs: &mut Xstate) -> Xresult {
    let n = take_length(xs)?;
    xs.push_data(Cell::from(n * 8 * 1024))
}

fn to_num_mbytes(xs: &mut Xstate) -> Xresult {
    let n = take_length(xs)?;
    xs.push_data(Cell::from(n * 8 * 1024 * 1024))
}

fn bin_read_bitstring(xs: &mut Xstate) -> Xresult {
    let n = take_length(xs)?;
    read_bits(xs, n)
}

fn bin_read_signed(xs: &mut Xstate) -> Xresult {
    let n = take_length(xs)?;
    let bo = default_byteorder(xs)?;
    let (x, rest) = read_signed(xs, n, bo)?;
    xs.push_data(Cell::Int(x))?;
    set_rest(xs, rest)
}

fn bin_read_unsigned(xs: &mut Xstate) -> Xresult {
    let n = take_length(xs)?;
    let bo = default_byteorder(xs)?;
    let (x, rest) = read_unsigned(xs, n, bo)?;
    xs.push_data(Cell::Int(x))?;
    set_rest(xs, rest)
}

fn read_bitstring(xs: &mut Xstate, n: usize) -> Xresult1<(Xbitstr, Xbitstr)> {
    let mut rest = bitstr_input(xs)?.clone();
    if let Some(s) = rest.read(n as usize) {
        Ok((s, rest))
    } else {
        Err(box_read_error(rest, n))
    }
}

fn read_unsigned(xs: &mut Xstate, n: usize, bo: Xbyteorder) -> Xresult1<(Xint, Xbitstr)> {
    let (mut s, rest) = read_bitstring(xs, n)?;
    if s.len() > 127 {
        return Err(Xerr::IntegerOverflow);
    }
    let x = s.to_uint(bo) as Xint;
    s.set_format(BitstringFormat::Unsigned(bo));
    set_last_chunk(xs, s)?;
    //NOTE: result truncated!
    Ok((x as Xint, rest))
}

fn read_signed(xs: &mut Xstate, n: usize, bo: Xbyteorder) -> Xresult1<(Xint, Xbitstr)> {
    let (mut s, rest) = read_bitstring(xs, n)?;
    if s.len() > 128 {
        return Err(Xerr::IntegerOverflow);
    }
    let x = s.to_int(bo);
    s.set_format(BitstringFormat::Signed(bo));
    set_last_chunk(xs, s)?;
    //NOTE: result truncated!
    Ok((x as Xint, rest))
}

fn read_signed_n(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = default_byteorder(xs)?;
    read_signed_nb(xs, n, bo)
}

fn read_signed_nb(xs: &mut Xstate, n: usize, bo: Xbyteorder) -> Xresult {
    let (x, rest) = read_signed(xs, n, bo)?;
    xs.push_data(Cell::Int(x))?;
    set_rest(xs, rest)
}

fn read_unsigned_n(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = default_byteorder(xs)?;
    read_unsigned_nb(xs, n, bo)
}

fn read_unsigned_nb(xs: &mut Xstate, n: usize, bo: Xbyteorder) -> Xresult {
    let (x, rest) = read_unsigned(xs, n, bo)?;
    xs.push_data(Cell::Int(x))?;
    set_rest(xs, rest)
}

fn read_float_n(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = default_byteorder(xs)?;
    read_float_nb(xs, n, bo)
}

fn read_float_nb(xs: &mut Xstate, n: usize, bo: Xbyteorder) -> Xresult {
    let (mut s, rest) = read_bitstring(xs, n)?;
    let val = match n {
        32 => s.to_f32(bo) as Xreal,
        64 => s.to_f64(bo) as Xreal,
        _ => return Err(Xerr::TypeError),
    };
    xs.push_data(Cell::Real(val))?;
    s.set_format(BitstringFormat::Real(bo));
    set_last_chunk(xs, s)?;
    set_rest(xs, rest)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitstring_mod() {
        let mut xs = Xstate::boot().unwrap();
        xs.interpret("[0 0xff] >bitstr").unwrap();
        let s = xs.pop_data().unwrap();
        assert_eq!(s, Cell::Bitstr(Xbitstr::from(vec![0, 255])));
        xs.set_binary_input(Xbitstr::from(vec![1, 255, 0])).unwrap();
        xs.interpret("u8").unwrap();
        assert_eq!(Cell::Int(1), xs.pop_data().unwrap());
        xs.interpret("i8").unwrap();
        assert_eq!(Cell::Int(-1), xs.pop_data().unwrap());
        xs.interpret("i8").unwrap();
        assert_eq!(Cell::Int(0), xs.pop_data().unwrap());
        assert_eq!(Err(Xerr::IntegerOverflow), xs.interpret("[256] >bitstr"));
        assert_eq!(Err(Xerr::IntegerOverflow), xs.interpret("[-1] >bitstr"));
        xs.interpret("[\"1\" 0x32 0s0011_0011] >bitstr").unwrap();
        assert_eq!(vec![0x31, 0x32, 0x33], xs.pop_data().unwrap().into_bitstring().unwrap().to_bytes());
    }

    #[test]
    fn test_int_uint() {
        let mut xs = Xstate::boot().unwrap();
        xs.interpret("[0xff 0xff] bitstr-open 8 uint 8 int").unwrap();
        assert_eq!(Cell::Int(-1), xs.pop_data().unwrap());
        assert_eq!(Cell::Int(255), xs.pop_data().unwrap());
    }

    #[test]
    fn test_bitstring_match() {
        let mut xs = Xstate::boot().unwrap();
        xs.set_binary_input(Xbitstr::from(vec![0x31, 0x32, 0x33])).unwrap();
        match xs.interpret("\"124\" ?") {
            Err(Xerr::BitMatchError(ctx)) => assert_eq!(16, ctx.2),
            other => panic!("{:?}", other),
        };
        xs.interpret("\"123\" ?").unwrap();
        match xs.interpret("[0] ?") {
            Err(Xerr::BitReadError(ctx)) => assert_eq!(8, ctx.1),
            other => panic!("{:?}", other),
        }
    }

    #[test]
    fn test_bitstring_chunk() {
        let mut xs = Xstate::boot().unwrap();
        xs.set_binary_input(Xbitstr::from(vec![1, 2, 3, 0])).unwrap();
        xs.interpret("u8").unwrap();
        assert_eq!(Cell::Int(1), xs.pop_data().unwrap());
        xs.interpret("bitstr/last-read").unwrap();
        let s = xs.pop_data().unwrap().into_bitstring().unwrap();
        assert_eq!(8, s.len());
        assert_eq!(BitstringFormat::Unsigned(LITTLE), s.format());
        xs.interpret("2 bytes").unwrap();
        let s = xs.pop_data().unwrap().into_bitstring().unwrap();
        assert_eq!(BitstringFormat::Raw, s.format());
        assert_eq!(16, s.len());
        assert_eq!(vec![2, 3], s.to_bytes());
        xs.interpret("2 bits").unwrap();
        let s = xs.pop_data().unwrap().into_bitstring().unwrap();
        assert_eq!(BitstringFormat::Raw, s.format());
        assert_eq!(2, s.len());
        xs.interpret("big-endian 2 int").unwrap();
        assert_eq!(Cell::Int(0), xs.pop_data().unwrap());
        xs.interpret("bitstr/last-read").unwrap();
        let s = xs.pop_data().unwrap().into_bitstring().unwrap();
        assert_eq!(2, s.len());
        assert_eq!(BitstringFormat::Signed(BIG), s.format());

        let f: f64 = 1.0;
        xs.set_binary_input(Xbitstr::from(f.to_be_bytes().to_vec())).unwrap();
        xs.interpret("f64be").unwrap();
        let f2 = xs.pop_data().unwrap().into_real().unwrap();
        assert_eq!(f,  f2);
        xs.interpret("bitstr/last-read").unwrap();
        let s = xs.pop_data().unwrap().into_bitstring().unwrap();
        assert_eq!(64, s.len());
        assert_eq!(BitstringFormat::Real(BIG), s.format());
    }

    #[test]
    fn test_xbytes() {
        let mut xs = Xstate::boot().unwrap();
        let s: Vec<u8> = (0..1024*1024+1024).map(|_| 1).collect();
        xs.set_binary_input(Xbitstr::from(s)).unwrap();
        xs.interpret("1 kbytes 1 mbytes remain").unwrap();
        assert_eq!(0, xs.pop_data().unwrap().into_int().unwrap());
    }

    #[test]
    fn test_to_num_bytes() {
        let mut xs = Xstate::boot().unwrap();
        xs.interpret("2 b>").unwrap();
        assert_eq!(16, xs.pop_data().unwrap().into_int().unwrap());
        xs.interpret("4 kb>").unwrap();
        assert_eq!(32768, xs.pop_data().unwrap().into_int().unwrap());
        xs.interpret("3 mb>").unwrap();
        assert_eq!(25165824, xs.pop_data().unwrap().into_int().unwrap());
    }

    #[test]
    fn test_bitstr_open() {
        let mut xs = Xstate::boot().unwrap();
        xs.interpret(
            "
        [1 5 7] bitstr-open u8
        [3] bitstr-open u8
        bitstr-close
        u8",
        )
        .unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(3)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        xs.interpret("bitstr/input").unwrap();
        let s = xs.pop_data().unwrap().into_bitstring().unwrap();
        assert_eq!(vec![7], s.to_bytes());
        xs.interpret("bitstr-close bitstr/input").unwrap();
        let s2 = xs.pop_data().unwrap().into_bitstring().unwrap();
        assert_eq!(0, s2.len());
        assert_eq!(OK, xs.interpret("bitstr-close"));
        assert_eq!(OK, xs.interpret("bitstr-close"));
        xs.interpret("bitstr/input").unwrap();
        let empty = xs.pop_data().unwrap().into_bitstring().unwrap(); 
        assert_eq!(0, empty.len());
    }

    #[test]
    fn test_bitstr_from_int() {
        let xs = &mut Xstate::boot().unwrap();
        let pop_bytes = |xs: &mut Xstate| xs.pop_data()?.into_bitstring().map(|s| s.to_bytes());
        xs.interpret("-128 i8>bitstr").unwrap();
        assert_eq!(Ok(vec![0x80]), pop_bytes(xs));
        xs.interpret("255 u8>bitstr").unwrap();
        assert_eq!(Ok(vec![0xff]), pop_bytes(xs));
        assert_eq!(Err(Xerr::IntegerOverflow), xs.interpret("-128 u8>bitstr"));
        assert_eq!(Err(Xerr::IntegerOverflow), xs.interpret("128 i8>bitstr"));
    }

    #[test]
    fn test_bitstring_input_seek() {
        let mut xs = Xstate::boot().unwrap();
        xs.set_binary_input(Xbitstr::from(vec![100, 200])).unwrap();
        match xs.interpret("100 seek") {
            Err(Xerr::BitSeekError(ctx)) => assert_eq!(100, ctx.1),
            other => panic!("{:?}", other),
        }
        assert_eq!(Err(Xerr::TypeError), xs.interpret("[] seek"));
        xs.interpret("8 seek u8").unwrap();
        assert_eq!(Cell::Int(200), xs.pop_data().unwrap());
        xs.interpret("0 seek u8").unwrap();
        assert_eq!(Cell::Int(100), xs.pop_data().unwrap());
    }

    #[test]
    fn test_bitstr_remain() {
        let mut xs = Xstate::boot().unwrap();
        xs.set_binary_input(Xbitstr::from(vec![1, 2])).unwrap();
        xs.interpret("remain").unwrap();
        assert_eq!(Cell::Int(16), xs.pop_data().unwrap());
        xs.interpret("5 bits drop remain").unwrap();
        assert_eq!(Cell::Int(11), xs.pop_data().unwrap());
        xs.interpret("11 bits drop remain").unwrap();
        assert_eq!(Cell::Int(0), xs.pop_data().unwrap());
    }

    #[test]
    fn test_bitstr_find() {
        let mut xs = Xstate::boot().unwrap();
        xs.interpret("[33 55 77] bitstr-open [77] find").unwrap();
        assert_eq!(Ok(Cell::Int(16)), xs.pop_data());
        xs.interpret("[55 77] find").unwrap();
        assert_eq!(Ok(Cell::Int(8)), xs.pop_data());
        xs.interpret("[] find").unwrap();
        assert_eq!(Ok(Cell::Int(0)), xs.pop_data());
        xs.interpret("[56] find").unwrap();
        assert_eq!(Ok(Cell::Nil), xs.pop_data());
        assert_eq!(Err(Xerr::UnalignedBitstr), xs.interpret("5 seek [56] find"));
        xs.interpret("[0x31 0x32 0x33] bitstr-open \"23\" find").unwrap();
        assert_eq!(Ok(Cell::Int(8)), xs.pop_data());
    }
}
