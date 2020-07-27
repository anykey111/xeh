use crate::bitstring::*;
use crate::cell::*;
use crate::error::*;
use crate::prelude::*;

pub fn bitstring_load(xs: &mut Xstate) -> Xresult {
    xs.defword("bits", bin_read_bitstring)?;
    xs.defword("signed", bin_read_signed)?;
    xs.defword("unsigned", bin_read_unsigned)?;
    xs.defword(">bitstring", to_bitstring)?;
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
    xs.bin = xs.defonce("binary-input", Cell::Bitstr(Bitstring::new()))?;
    xs.bigendian = xs.defonce("binary-bigendian", ZERO)?;
    OK
}

fn bitstring_new(xs: &mut Xstate) -> Xresult {
    xs.push_data(Cell::Bitstr(Bitstring::new()))
}

fn to_bitstring(xs: &mut Xstate) -> Xresult {
    let s = match xs.pop_data()? {
        Cell::Str(s) => Bitstring::from(s.as_bytes()),
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
            Bitstring::from(tmp)
        }
        Cell::Bitstr(s) => s,
        _ => return Err(Xerr::TypeError),
    };
    xs.push_data(Cell::Bitstr(s))
}

fn take_length(xs: &mut Xstate) -> Xresult1<usize> {
    let n = xs.pop_data()?.into_int()?;
    if n < 0 || n > (usize::MAX as i128) {
        Err(Xerr::OutOfRange)
    } else {
        Ok(n as usize)
    }
}

fn save_rest(xs: &mut Xstate, rest: Bitstring) -> Xresult {
    xs.set_var(&xs.bin.clone(), Cell::Bitstr(rest))
}

fn default_byteorder(xs: &mut Xstate) -> Xresult1<Byteorder> {
    if xs.get_var(&xs.bigendian)? == &ZERO {
        Ok(Byteorder::LE)
    } else {
        Ok(Byteorder::BE)
    }
}

fn bin_read_bitstring(xs: &mut Xstate) -> Xresult {
    let n = take_length(xs)?;
    let (s, rest) = read_bitstring(xs, n)?;
    xs.push_data(Cell::Bitstr(s))?;
    save_rest(xs, rest)
}

fn bin_read_signed(xs: &mut Xstate) -> Xresult {
    let n = take_length(xs)?;
    let bo = default_byteorder(xs)?;
    let (x, rest) = read_signed(xs, n, bo)?;
    xs.push_data(Cell::Int(x))?;
    save_rest(xs, rest)
}

fn bin_read_unsigned(xs: &mut Xstate) -> Xresult {
    let n = take_length(xs)?;
    let bo = default_byteorder(xs)?;
    let (x, rest) = read_unsigned(xs, n, bo)?;
    xs.push_data(Cell::Int(x))?;
    save_rest(xs, rest)
}

fn read_bitstring(xs: &mut Xstate, n: usize) -> Xresult1<(Xbitstr, Xbitstr)> {
    let mut rest = xs.get_var(&xs.bin)?.clone().into_bitstring()?;
    let s = rest.read(n as usize).ok_or(Xerr::OutOfRange)?;
    Ok((s, rest))
}

fn read_unsigned(xs: &mut Xstate, n: usize, bo: Byteorder) -> Xresult1<(Xint, Xbitstr)> {
    let (s, rest) = read_bitstring(xs, n)?;
    if s.len() > 127 {
        return Err(Xerr::IntegerOverflow);
    }
    Ok((s.to_u128(bo) as Xint, rest))
}

fn read_signed(xs: &mut Xstate, n: usize, bo: Byteorder) -> Xresult1<(Xint, Xbitstr)> {
    let (s, rest) = read_bitstring(xs, n)?;
    if s.len() > 128 {
        return Err(Xerr::IntegerOverflow);
    }
    Ok((s.to_i128(bo), rest))
}

fn read_signed_n(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = default_byteorder(xs)?;
    read_signed_nb(xs, n, bo)
}

fn read_signed_nb(xs: &mut Xstate, n: usize, bo: Byteorder) -> Xresult {
    let (x, rest) = read_signed(xs, n, bo)?;
    xs.push_data(Cell::Int(x))?;
    save_rest(xs, rest)
}

fn read_unsigned_n(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = default_byteorder(xs)?;
    read_unsigned_nb(xs, n, bo)
}

fn read_unsigned_nb(xs: &mut Xstate, n: usize, bo: Byteorder) -> Xresult {
    let (x, rest) = read_unsigned(xs, n, bo)?;
    xs.push_data(Cell::Int(x))?;
    save_rest(xs, rest)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitstring_mod() {
        let mut xs = Xstate::new().unwrap();
        xs.interpret("[0x01 0xff 0] >bitstring -> binary-input")
            .unwrap();
        xs.interpret("u8").unwrap();
        assert_eq!(Cell::Int(1), xs.pop_data().unwrap());
        xs.interpret("i8").unwrap();
        assert_eq!(Cell::Int(-128), xs.pop_data().unwrap());
        xs.interpret("i8").unwrap();
        assert_eq!(Cell::Int(0), xs.pop_data().unwrap());
        assert_eq!(Err(Xerr::IntegerOverflow), xs.interpret("[256] >bitstring"));
        assert_eq!(Err(Xerr::IntegerOverflow), xs.interpret("[-1] >bitstring"));
        assert_eq!(Err(Xerr::TypeError), xs.interpret("[\"1\"] >bitstring"));
        assert_eq!(Err(Xerr::TypeError), xs.interpret("{} >bitstring"));
    }
}
