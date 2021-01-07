use crate::bitstring::*;
use crate::cell::*;
use crate::error::*;
use crate::prelude::*;

pub fn bitstring_load(xs: &mut Xstate) -> Xresult {
    xs.defword("bits", bin_read_bitstring)?;
    xs.defword("bytes", bin_read_bytes)?;
    xs.defword("signed", bin_read_signed)?;
    xs.defword("unsigned", bin_read_unsigned)?;
    xs.defword("bitstr", |xs| xs.push_data(Cell::Bitstr(Xbitstr::new())))?;
    xs.defword("bitstr-append", bitstring_append)?;
    xs.defword("bitstr-invert", bitstring_invert)?;
    xs.defword(">bitstr", to_bitstring)?;
    xs.defword("bitstr>signed", bitstring_to_signed)?;
    xs.defword("bitstr>unsigned", bitstring_to_unsigned)?;
    xs.defword("big-endian", |xs| set_byteorder(xs, Byteorder::BE))?;
    xs.defword("little-endian", |xs| set_byteorder(xs, Byteorder::LE))?;
    xs.defword("?", bin_match)?;
    xs.defword("u8", |xs| read_unsigned_n(xs, 8))?;
    xs.defword("u16", |xs| read_unsigned_n(xs, 16))?;
    xs.defword("u32", |xs| read_unsigned_n(xs, 32))?;
    xs.defword("u64", |xs| read_unsigned_n(xs, 64))?;
    xs.defword("u8be", |xs| read_unsigned_nb(xs, 8, Byteorder::BE))?;
    xs.defword("u16be", |xs| read_unsigned_nb(xs, 16, Byteorder::BE))?;
    xs.defword("u32be", |xs| read_unsigned_nb(xs, 32, Byteorder::BE))?;
    xs.defword("u64be", |xs| read_unsigned_nb(xs, 64, Byteorder::BE))?;
    xs.defword("u8le", |xs| read_unsigned_nb(xs, 8, Byteorder::LE))?;
    xs.defword("u16le", |xs| read_unsigned_nb(xs, 16, Byteorder::LE))?;
    xs.defword("u32le", |xs| read_unsigned_nb(xs, 32, Byteorder::LE))?;
    xs.defword("u64le", |xs| read_unsigned_nb(xs, 64, Byteorder::LE))?;
    xs.defword("i8", |xs| read_signed_n(xs, 8))?;
    xs.defword("i16", |xs| read_signed_n(xs, 16))?;
    xs.defword("i32", |xs| read_signed_n(xs, 32))?;
    xs.defword("i64", |xs| read_signed_n(xs, 64))?;
    xs.defword("i8be", |xs| read_signed_nb(xs, 8, Byteorder::BE))?;
    xs.defword("i16be", |xs| read_signed_nb(xs, 16, Byteorder::BE))?;
    xs.defword("i32be", |xs| read_signed_nb(xs, 32, Byteorder::BE))?;
    xs.defword("i64be", |xs| read_signed_nb(xs, 64, Byteorder::BE))?;
    xs.defword("i8le", |xs| read_signed_nb(xs, 8, Byteorder::LE))?;
    xs.defword("i16le", |xs| read_signed_nb(xs, 16, Byteorder::LE))?;
    xs.defword("i32le", |xs| read_signed_nb(xs, 32, Byteorder::LE))?;
    xs.defword("i64le", |xs| read_signed_nb(xs, 64, Byteorder::LE))?;
    xs.defword("seek", bitstring_seek)?;
    xs.defword("offset", bitstr_offset)?;
    xs.defword("remain", bitstr_remain)?;
    xs.defword("bitstr-open", bitstring_open)?;
    xs.defword("bitstr-close", bitstring_close)?;
    xs.bs_isbig = xs.defvar("big-endian?", ZERO)?;
    xs.bs_input = xs.defvar("*bitstr-input*", Cell::Bitstr(Bitstring::new()))?;
    xs.bs_chunk = xs.defvar("*bitstr-chunk*", Cell::Bitstr(Bitstring::new()))?;
    xs.bs_flow = xs.defvar("*bitstr-flow*", Cell::Vector(Xvec::default()))?;
    OK
}

fn bitstring_seek(xs: &mut Xstate) -> Xresult {
    let pos = xs.pop_data()?.into_usize()?;
    let mut bs = xs.get_var(xs.bs_input)?.clone().into_bitstring()?;
    bs.seek(pos).ok_or_else(|| Xerr::OutOfRange)?;
    xs.set_var(xs.bs_input, Cell::Bitstr(bs)).map(|_| ())
}

fn bitstr_offset(xs: &mut Xstate) -> Xresult {
    match xs.get_var(xs.bs_input)? {
        Cell::Bitstr(bs) => {
            let offs = bs.start() as Xint;
            xs.push_data(Cell::Int(offs))?;
            OK
        }
        _ => Err(Xerr::TypeError)
    }
}

fn bitstr_remain(xs: &mut Xstate) -> Xresult {
    match xs.get_var(xs.bs_input)? {
        Cell::Bitstr(bs) => {
            let n = bs.len() as Xint;
            xs.push_data(Cell::Int(n))?;
            OK
        }
        _ => Err(Xerr::TypeError)
    }
}

fn bitstring_open(xs: &mut Xstate) -> Xresult {
    let new_bin = xs.pop_data()?.into_bitstring()?;
    let old_bin = xs.get_var(xs.bs_input)?.clone();
    let flow = match xs.get_var(xs.bs_flow)? {
        Cell::Vector(v) => v.push_back(old_bin),
        _ => return Err(Xerr::TypeError),
    };
    xs.set_var(xs.bs_flow, Cell::Vector(flow))?;
    xs.set_var(xs.bs_input, Cell::Bitstr(new_bin))?;
    OK
}

fn bitstring_close(xs: &mut Xstate) -> Xresult {
    let flow = xs.get_var(xs.bs_flow)?.clone().into_vector()?;
    let old_bin = flow.last()
        .ok_or(Xerr::ControlFlowError)?
        .clone()
        .into_bitstring()?;
    xs.set_var(xs.bs_flow, Cell::Vector(flow.drop_last().unwrap()))?;
    xs.set_var(xs.bs_input, Cell::Bitstr(old_bin))?;
    OK
}

fn bitstring_append(xs: &mut Xstate) -> Xresult {
    let head = xs.pop_data()?.into_bitstring()?;
    let tail = xs.pop_data()?;
    let tail = into_bitstring(tail)?;
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
    let x = s.to_i128(bo);
    xs.push_data(Cell::Int(x))
}

fn bitstring_to_unsigned(xs: &mut Xstate) -> Xresult {
    let s = xs.pop_data()?.into_bitstring()?;
    let bo = default_byteorder(xs)?;
    if s.len() > 128 {
        return Err(Xerr::IntegerOverflow);
    }
    let x = s.to_u128(bo) as Xint;
    xs.push_data(Cell::Int(x))
}

fn to_bitstring(xs: &mut Xstate) -> Xresult {
    let val = xs.pop_data()?;
    let s = into_bitstring(val)?;
    xs.push_data(Cell::Bitstr(s))
}

fn into_bitstring(val: Cell) -> Xresult1<Bitstring> {
    match val {
        Cell::Str(s) => Ok(Bitstring::from(s.as_bytes())),
        Cell::Vector(v) => {
            let mut tmp = Vec::with_capacity(v.len());
            for x in v.iter() {
                match x {
                    Cell::Int(i) => {
                        if 0 <= *i && *i <= 255 {
                            tmp.push(*i as u8);
                        } else {
                            return Err(Xerr::IntegerOverflow);
                        }
                    }
                    _ => return Err(Xerr::TypeError),
                }
            }
            Ok(Bitstring::from(tmp))
        }
        Cell::Bitstr(s) => Ok(s),
        _ => Err(Xerr::TypeError),
    }
}

fn take_length(xs: &mut Xstate) -> Xresult1<usize> {
    let n = xs.pop_data()?.into_int()?;
    if n < 0 || n > (usize::MAX as i128) {
        Err(Xerr::OutOfRange)
    } else {
        Ok(n as usize)
    }
}

fn set_rest(xs: &mut Xstate, rest: Bitstring) -> Xresult {
    xs.set_var(xs.bs_input, Cell::Bitstr(rest)).map(|_| ())
}

fn set_last_chunk(xs: &mut Xstate, s: Bitstring) -> Xresult {
    xs.set_var(xs.bs_chunk, Cell::Bitstr(s)).map(|_| ())
}

fn set_byteorder(xs: &mut Xstate, bo: Byteorder) -> Xresult {
    xs.set_var(
        xs.bs_isbig,
        if bo == Byteorder::LE { ZERO } else { ONE },
    ).map(|_| ())
}

fn default_byteorder(xs: &mut Xstate) -> Xresult1<Byteorder> {
    if xs.get_var(xs.bs_isbig)? == &ZERO {
        Ok(Byteorder::LE)
    } else {
        Ok(Byteorder::BE)
    }
}

fn bin_match(xs: &mut Xstate) -> Xresult {
    let val = xs.pop_data()?;
    let pat = into_bitstring(val)?;
    let (s, rest) = read_bitstring(xs, pat.len())?;
    if s != pat {
        return Err(Xerr::BinaryMatchError);
    }
    set_last_chunk(xs, s)?;
    set_rest(xs, rest)
}

fn bin_read_bytes(xs: &mut Xstate) -> Xresult {
    let n = take_length(xs)?;
    let (s, rest) = read_bitstring(xs, n * 8)?;
    set_last_chunk(xs, s.clone())?;
    xs.push_data(Cell::Bitstr(s))?;
    set_rest(xs, rest)
}

fn bin_read_bitstring(xs: &mut Xstate) -> Xresult {
    let n = take_length(xs)?;
    let (s, rest) = read_bitstring(xs, n)?;
    set_last_chunk(xs, s.clone())?;
    xs.push_data(Cell::Bitstr(s))?;
    set_rest(xs, rest)
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
    let mut rest = xs.get_var(xs.bs_input)?.clone().into_bitstring()?;
    let s = rest.read(n as usize).ok_or(Xerr::OutOfRange)?;
    Ok((s, rest))
}

fn read_unsigned(xs: &mut Xstate, n: usize, bo: Byteorder) -> Xresult1<(Xint, Xbitstr)> {
    let (mut s, rest) = read_bitstring(xs, n)?;
    if s.len() > 127 {
        return Err(Xerr::IntegerOverflow);
    }
    let x = s.to_u128(bo) as Xint;
    s.set_format(BitstringFormat::Unsigned(bo));
    set_last_chunk(xs, s)?;
    Ok((x, rest))
}

fn read_signed(xs: &mut Xstate, n: usize, bo: Byteorder) -> Xresult1<(Xint, Xbitstr)> {
    let (mut s, rest) = read_bitstring(xs, n)?;
    if s.len() > 128 {
        return Err(Xerr::IntegerOverflow);
    }
    let x = s.to_i128(bo);
    s.set_format(BitstringFormat::Signed(bo));
    set_last_chunk(xs, s)?;
    Ok((x, rest))
}

fn read_signed_n(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = default_byteorder(xs)?;
    read_signed_nb(xs, n, bo)
}

fn read_signed_nb(xs: &mut Xstate, n: usize, bo: Byteorder) -> Xresult {
    let (x, rest) = read_signed(xs, n, bo)?;
    xs.push_data(Cell::Int(x))?;
    set_rest(xs, rest)
}

fn read_unsigned_n(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = default_byteorder(xs)?;
    read_unsigned_nb(xs, n, bo)
}

fn read_unsigned_nb(xs: &mut Xstate, n: usize, bo: Byteorder) -> Xresult {
    let (x, rest) = read_unsigned(xs, n, bo)?;
    xs.push_data(Cell::Int(x))?;
    set_rest(xs, rest)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitstring_mod() {
        let mut xs = Xstate::new().unwrap();
        xs.interpret("[0 0xff] >bitstr").unwrap();
        let s = xs.pop_data().unwrap();
        assert_eq!(s, Cell::Bitstr(Xbitstr::from(&vec![0, 255])));
        xs.set_binary_input_data(&vec![1, 255, 0]).unwrap();
        xs.interpret("u8").unwrap();
        assert_eq!(Cell::Int(1), xs.pop_data().unwrap());
        xs.interpret("i8").unwrap();
        assert_eq!(Cell::Int(-128), xs.pop_data().unwrap());
        xs.interpret("i8").unwrap();
        assert_eq!(Cell::Int(0), xs.pop_data().unwrap());
        assert_eq!(Err(Xerr::IntegerOverflow), xs.interpret("[256] >bitstr"));
        assert_eq!(Err(Xerr::IntegerOverflow), xs.interpret("[-1] >bitstr"));
        assert_eq!(Err(Xerr::TypeError), xs.interpret("[\"1\"] >bitstr"));
        assert_eq!(Err(Xerr::TypeError), xs.interpret("{} >bitstr"));
    }

    #[test]
    fn test_bitstring_match() {
        let mut xs = Xstate::new().unwrap();
        xs.set_binary_input_data(&vec![0x31, 0x32, 0x33]).unwrap();
        assert_eq!(Err(Xerr::BinaryMatchError), xs.interpret("\"124\" ?"));
        xs.interpret("\"123\" ?").unwrap();
        assert_eq!(Err(Xerr::TypeError), xs.interpret("{} ?"));
        assert_eq!(Err(Xerr::OutOfRange), xs.interpret("[0] ?"));
    }

    #[test]
    fn test_bitstring_chunk() {
        let mut xs = Xstate::new().unwrap();
        xs.set_binary_input_data(&vec![1, 2, 3, 0]).unwrap();
        xs.interpret("8 unsigned").unwrap();
        assert_eq!(Cell::Int(1), xs.pop_data().unwrap());
        xs.interpret("*bitstr-chunk*").unwrap();
        let s = xs.pop_data().unwrap().into_bitstring().unwrap();
        assert_eq!(8, s.len());
        assert_eq!(BitstringFormat::Unsigned(Byteorder::LE), s.format());
        xs.interpret("2 bytes").unwrap();
        let s = xs.pop_data().unwrap().into_bitstring().unwrap();
        assert_eq!(BitstringFormat::Raw, s.format());
        assert_eq!(16, s.len());
        assert_eq!(vec![2, 3], s.to_bytes());
        xs.interpret("2 bits").unwrap();
        let s = xs.pop_data().unwrap().into_bitstring().unwrap();
        assert_eq!(BitstringFormat::Raw, s.format());
        assert_eq!(2, s.len());
        xs.interpret("big-endian 2 signed").unwrap();
        assert_eq!(Cell::Int(0), xs.pop_data().unwrap());
        xs.interpret("*bitstr-chunk*").unwrap();
        let s = xs.pop_data().unwrap().into_bitstring().unwrap();
        assert_eq!(2, s.len());
        assert_eq!(BitstringFormat::Signed(Byteorder::BE), s.format());
    }

    #[test]
    fn test_bitstr_open() {
        let mut xs = Xstate::new().unwrap();
        xs.interpret("
        [1 5 7] >bitstr bitstr-open u8
        [3] >bitstr bitstr-open u8
        bitstr-close
        u8").unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(3)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        xs.interpret("*bitstr-input*").unwrap();
        let s = xs.pop_data().unwrap().into_bitstring().unwrap();
        assert_eq!(vec![7], s.to_bytes());
        xs.interpret("bitstr-close *bitstr-input*").unwrap();
        let s2 = xs.pop_data().unwrap().into_bitstring().unwrap();
        assert_eq!(0, s2.len());
        assert_eq!(Err(Xerr::ControlFlowError), xs.interpret("bitstr-close"));
    }

    #[test]
    fn test_bitstring_input_seek() {
        let mut xs = Xstate::new().unwrap();
        xs.set_binary_input_data(&vec![100, 200]).unwrap();
        assert_eq!(Err(Xerr::OutOfRange), xs.interpret("100 seek"));
        assert_eq!(Err(Xerr::TypeError), xs.interpret("[] seek"));
        xs.interpret("8 seek 8 unsigned").unwrap();
        assert_eq!(Cell::Int(200), xs.pop_data().unwrap());
        xs.interpret("0 seek 8 unsigned").unwrap();
        assert_eq!(Cell::Int(100), xs.pop_data().unwrap());
    }

    
    #[test]
    fn test_bitstr_remain() {
        let mut xs = Xstate::new().unwrap();
        xs.set_binary_input_data(&vec![1, 2]).unwrap();
        xs.interpret("remain").unwrap();
        assert_eq!(Cell::Int(16), xs.pop_data().unwrap());
        xs.interpret("5 bits drop remain").unwrap();
        assert_eq!(Cell::Int(11), xs.pop_data().unwrap());
        xs.interpret("11 bits drop remain").unwrap();
        assert_eq!(Cell::Int(0), xs.pop_data().unwrap());
    }
}
