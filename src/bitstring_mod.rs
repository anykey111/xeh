use std::fmt::Write;
use crate::bitstring::*;
use crate::cell::*;
use crate::error::*;
use crate::prelude::*;

#[derive(Default, Clone)]
pub struct BitstrMod {
    big_endian: CellRef,
    offset: CellRef,
    input: CellRef,
    stash: CellRef,
}

macro_rules! def_data_word {
    ($xs:ident, $n:expr) => {
        $xs.defword(concat!("u", $n), |xs| read_unsigned_n(xs, $n))?;
        $xs.defword(concat!("u", $n, "le"), |xs| read_unsigned(xs, $n, LITTLE))?;
        $xs.defword(concat!("u", $n, "be"), |xs| read_unsigned(xs, $n, BIG))?;
        $xs.defword(concat!("i", $n), |xs| read_signed_n(xs, $n))?;
        $xs.defword(concat!("i", $n, "le"), |xs| read_signed(xs, $n, LITTLE))?;
        $xs.defword(concat!("i", $n, "be"), |xs| read_signed(xs, $n, BIG))?;
        $xs.defword(concat!("u", $n, "!"), |xs| pack_int(xs, $n))?;
        $xs.defword(concat!("u", $n, "le!"), |xs| pack_int_bo(xs, $n, LITTLE))?;
        $xs.defword(concat!("u", $n, "be!"), |xs| pack_int_bo(xs, $n, BIG))?;
        $xs.defword(concat!("i", $n, "!"), |xs| pack_int(xs, $n))?;
        $xs.defword(concat!("i", $n, "le!"), |xs| pack_int_bo(xs, $n, LITTLE))?;
        $xs.defword(concat!("i", $n, "be!"), |xs| pack_int_bo(xs, $n, BIG))?;
    };
}

macro_rules! def_data_word_real {
    ($xs:ident, $n:expr) => {
        $xs.defword(concat!("f", $n), |xs| read_float_n(xs, $n))?;
        $xs.defword(concat!("f", $n, "le"), |xs| read_float(xs, $n, LITTLE))?;
        $xs.defword(concat!("f", $n, "be"), |xs| read_float(xs, $n, BIG))?;
        $xs.defword(concat!("f", $n, "!"), |xs| pack_float(xs, $n))?;
        $xs.defword(concat!("f", $n, "le!"), |xs| pack_float_bo(xs, $n, LITTLE))?;
        $xs.defword(concat!("f", $n, "be!"), |xs| pack_float_bo(xs, $n, BIG))?;
    };
}

pub fn load(xs: &mut Xstate) -> Xresult {
    let mut m = BitstrMod::default();
    let empty = Cell::from(Xbitstr::new());
    m.big_endian = xs.defvar("big?", ZERO)?;
    m.input = xs.defvar("current-bitstr", empty)?;
    m.offset = xs.defvar("offset", ZERO)?;
    m.stash = xs.defvar_anonymous(Cell::from(Xvec::new()))?;
    xs.bitstr_mod = m;
    xs.defword("open-bitstr", word_open_bitstr)?;
    xs.defword("close-bitstr", word_close_bitstr)?;
    xs.defword("seek", word_seek)?;
    xs.defword("remain", word_remain)?;
    xs.defword("find", word_find)?;
    xs.defword("dump", word_dump)?;
    xs.defword("dump-at", word_dump_at)?;
    xs.defword("bits", word_bits)?;
    xs.defword("bytes", word_bytes)?;
    xs.defword("kbytes", word_kbytes)?;
    xs.defword("mbytes", word_mbytes)?;
    xs.defword("b>", to_num_bytes)?;
    xs.defword("kb>", to_num_kbytes)?;
    xs.defword("mb>", to_num_mbytes)?;
    xs.defword("bitstr-append", bitstring_append)?;
    xs.defword("bitstr-not", word_bitstr_not)?;
    xs.defword("bitstr-and", bitstring_and)?;
    xs.defword("bitstr-or", bitstring_or)?;
    xs.defword("bitstr-xor", bitstring_xor)?;
    xs.defword("hex>bitstr", hex_to_bitstr)?;
    xs.defword("bitstr>hex", bitstr_to_hex)?;
    xs.defword("bin>bitstr", bin_to_bitstr)?;
    xs.defword("bitstr>bin", bitstr_to_bin)?;
    xs.defword(">bitstr", to_bitstring)?;
    xs.defword("bitstr>utf8", bitstr_to_utf8)?;
    xs.defword("big", |xs| set_byteorder(xs, BIG))?;
    xs.defword("little", |xs| set_byteorder(xs, LITTLE))?;
    xs.defword("expect", word_expect)?;

    def_data_word!(xs, 8);
    def_data_word!(xs, 16);
    def_data_word!(xs, 32);
    def_data_word!(xs, 64);
    def_data_word_real!(xs, 32);
    def_data_word_real!(xs, 64);
    xs.defword("int", |xs| {
        let n = take_length(xs)?;
        let bo = current_byteorder(xs)?;
        read_signed(xs, n, bo)
    })?;
    xs.defword("uint", |xs| {
        let n = take_length(xs)?;
        let bo = current_byteorder(xs)?;
        read_unsigned(xs, n, bo)
    })?;
    xs.defword("int!", |xs| {
        let n = xs.pop_data()?.to_usize()?;
        pack_int(xs, n)
    })?;
    xs.defword("uint!", |xs| {
        let n = xs.pop_data()?.to_usize()?;
        pack_int(xs, n)
    })?;
    OK
}

fn pack_int_bo(xs: &mut Xstate, n: usize, bo: Byteorder) -> Xresult {
    let val = xs.pop_data()?.to_xint()?;
    let s = Bitstring::from_int(val, n, bo);
    xs.push_data(Cell::Bitstr(s))
}

fn pack_int(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = current_byteorder(xs)?;
    pack_int_bo(xs, n, bo)
}

fn pack_float_bo(xs: &mut Xstate, n: usize, bo: Byteorder) -> Xresult {
    let val = xs.pop_data()?.to_real()?;
    let s = match n {
        32 => Bitstring::from_f32(val as f32, bo),
        64 => Bitstring::from_f64(val, bo),
        n => return Err(Xerr::InvalidFloatLength(n)),
    };
    xs.push_data(Cell::Bitstr(s))
}

fn pack_float(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = current_byteorder(xs)?;
    pack_float_bo(xs, n, bo)
}

fn word_find(xs: &mut Xstate) -> Xresult {
    let pat = bitstring_from(xs.pop_data()?)?;
    let s = rest_bits(xs)?;
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

fn current_input(xs: &Xstate) -> Xresult1<&Xbitstr> {
    xs.get_var(xs.bitstr_mod.input)?.bitstr()
}

fn current_offset(xs: &Xstate) -> Xresult1<usize> {
    xs.get_var(xs.bitstr_mod.offset)?.to_usize()
}

fn move_offset_checked(xs: &mut Xstate, pos: usize) -> Xresult {
    let s = current_input(xs)?;
    if s.start() <= pos && pos <= s.end() {
        xs.set_var(xs.bitstr_mod.offset, Cell::from(pos))?;
        OK
    } else {
        Err(Xerr::SeekError { src: s.clone(), offset: pos })
    }
}

fn word_seek(xs: &mut Xstate) -> Xresult {
    let pos = xs.pop_data()?.to_usize()?;
    move_offset_checked(xs, pos)
}

fn word_remain(xs: &mut Xstate) -> Xresult {
    let s = current_input(xs)?;
    let offset = current_offset(xs)?;
    let res= Cell::from(s.end().max(offset) - offset);
    xs.push_data(res)
}

fn word_dump_at(xs: &mut Xstate) -> Xresult {
    let start = xs.pop_data()?.to_usize()?;
    dump_bitstr_at(xs, start, 8)
}

fn word_dump(xs: &mut Xstate) -> Xresult {
    let start = current_offset(xs)?;
    dump_bitstr_at(xs, start, 8)
}

fn dump_bitstr_at(xs: &mut Xstate, start: usize, ncols: usize) -> Xresult {
    let s = current_input(xs)?;
    let end = s.end().min(start + 16 * ncols * 8);
    let ss = s.substr(start, end).ok_or_else(|| Xerr::OutOfBounds(start))?;
    dump_bitstr(xs, &ss, ncols)
}

pub fn byte_to_dump_char(x: u8) -> char {
    let c = std::char::from_u32(x as u32).unwrap();
    if c.is_ascii_graphic() {
        c
    } else {
        '.'
    }
}

fn dump_bitstr(xs: &mut Xstate, s: &Bitstring, ncols: usize) -> Xresult {
    let mut buf = String::new();
    let mut pos = s.start();
    let mut hex  = String::new();
    let mut ascii  = String::new();
    let mut it = s.iter8();
    while pos < s.end() {
        write_dump_position(&mut buf, pos);
        buf.push(':');
        for _ in 0..ncols {
            if let Some((x, nbits)) = it.next() {
                write!(buf, " {:02x}", x).unwrap();
                pos += nbits as usize;
                ascii.push(byte_to_dump_char(x));
            } else {
                hex.push_str("  ");
                ascii.push(' ');
            }
        }
        buf.push_str(&hex);
        buf.push_str("  ");
        buf.push_str(&ascii);
        buf.push_str("\n");
        xs.print(&buf);
        buf.clear();
        hex.clear();
        ascii.clear();
    }
    OK
}
    
fn write_dump_position(buf: &mut String, start: usize) {
    let pos = start / 8;
    write!(buf, "{:05x}", pos).unwrap();
    if start % 8 > 0 {
        write!(buf, ",{}", start % 8).unwrap();
    }
}

pub(crate) fn open_bitstr(xs: &mut Xstate, s: Bitstring) -> Xresult {
    let old_offset = xs.get_var(xs.bitstr_mod.offset)?.clone();
    let old_input = xs.get_var(xs.bitstr_mod.input)?.clone();
    xs.set_var(xs.bitstr_mod.offset, Cell::from(s.start()))?;
    xs.set_var(xs.bitstr_mod.input, Cell::from(s))?;
    let stash = xs.get_var(xs.bitstr_mod.stash)?
        .vec()?
        .push_back(old_input.with_tag(old_offset));
    xs.set_var(xs.bitstr_mod.stash, Cell::from(stash))
}

fn word_open_bitstr(xs: &mut Xstate) -> Xresult {
    let s = bitstring_from(xs.pop_data()?)?;
    open_bitstr(xs, s)
}

fn word_close_bitstr(xs: &mut Xstate) -> Xresult {
    let stash = xs.get_var(xs.bitstr_mod.stash)?.vec()?;
    let last = stash.last().ok_or_else(|| Xerr::OutOfBounds(0))?;
    let offset = last.tag().unwrap_or(&ZERO).clone();
    let input = last.value().clone();
    let stash = stash.drop_last().unwrap();
    xs.set_var(xs.bitstr_mod.offset, offset)?;
    xs.set_var(xs.bitstr_mod.input, input)?;
    xs.set_var(xs.bitstr_mod.stash, Cell::from(stash))?;
    OK
}

fn bitstring_append(xs: &mut Xstate) -> Xresult {
    let head = xs.pop_data()?.to_bitstr()?;
    let tail = xs.pop_data()?;
    let tail = bitstring_from(tail)?;
    let result = head.append(&tail);
    xs.push_data(Cell::Bitstr(result))
}

fn word_bitstr_not(xs: &mut Xstate) -> Xresult {
    let s = xs.pop_data()?.to_bitstr()?;
    xs.push_data(Cell::Bitstr(s.invert()))
}

fn bitstring_zip_with(xs: &mut Xstate, op: fn(u8, u8) -> u8) -> Xresult {
    let sb = xs.pop_data()?.to_bitstr()?;
    let sa = xs.pop_data()?.to_bitstr()?;
    let mut tmp = BitvecBuilder::default();
    for (a, b) in sa.bits().zip(sb.bits().cycle()) {
        tmp.append_bit(op(a, b));
    }
    let res = Cell::Bitstr(tmp.finish());
    xs.push_data(res)
}

fn bitstring_and(xs: &mut Xstate) -> Xresult {
    bitstring_zip_with(xs, std::ops::BitAnd::bitand)
}

fn bitstring_or(xs: &mut Xstate) -> Xresult {
    bitstring_zip_with(xs, std::ops::BitOr::bitor)
}

fn bitstring_xor(xs: &mut Xstate) -> Xresult {
    bitstring_zip_with(xs, std::ops::BitXor::bitxor)
}

fn hex_to_bitstr(xs: &mut Xstate) -> Xresult {
    let s = xs.pop_data()?.to_xstr()?;
    match Bitstring::from_hex_str(&s) {
        Ok(bs) => xs.push_data(Cell::from(bs)),
        Err(pos) => {
            Err(Xerr::ParseError {
                msg: arcstr::literal!("hex string parse error"),
                substr: s.substr(..),
                pos,
            })
        }
    }
}

fn bitstr_to_hex(xs: &mut Xstate) -> Xresult {
    let bs = xs.pop_data()?;
    xs.push_data(Cell::from(bs.bitstr()?.to_hex_string()))
}

fn bin_to_bitstr(xs: &mut Xstate) -> Xresult {
    let s = xs.pop_data()?.to_xstr()?;
    match Bitstring::from_bin_str(&s) {
        Ok(bs) => xs.push_data(Cell::from(bs)),
        Err(pos) => {
            Err(Xerr::ParseError {
                msg: arcstr::literal!("bin string parse error"),
                substr: s.substr(..),
                pos,
            })
        }
    }
}

fn bitstr_to_bin(xs: &mut Xstate) -> Xresult {
    let bs = xs.pop_data()?.to_bitstr()?;
    xs.push_data(Cell::from(bs.to_bin_string()))
}


fn to_bitstring(xs: &mut Xstate) -> Xresult {
    let val = xs.pop_data()?;
    let s = bitstring_from(val)?;
    xs.push_data(Cell::Bitstr(s))
}

fn bitstr_to_utf8(xs: &mut Xstate) -> Xresult {
    let bs = xs.pop_data()?;
    match String::from_utf8(bs.bitstr()?.to_bytes()) {
        Ok(s) => xs.push_data(Cell::from(s)),
        Err(e) => {
            let pos = e.utf8_error().valid_up_to();
            let bytes = e.into_bytes();
            Err(Xerr::StrDecodeError {
                msg: arcstr::literal!("utf8 bytes parse error"),
                bytes,
                pos,
            })
        }
    }
}

pub fn bitstring_from(val: Cell) -> Xresult1<Bitstring> {
    match val {
        Cell::Str(s) => Ok(Bitstring::from(s.to_string().into_bytes())),
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
    xs.pop_data()?.to_usize()
}

fn set_byteorder(xs: &mut Xstate, bo: Byteorder) -> Xresult {
    xs.set_var(xs.bitstr_mod.big_endian, if bo == LITTLE { ZERO } else { ONE })?;
    OK
}

fn current_byteorder(xs: &mut Xstate) -> Xresult1<Byteorder> {
    if xs.get_var(xs.bitstr_mod.big_endian)? == &ZERO {
        Ok(LITTLE)
    } else {
        Ok(BIG)
    }
}

fn word_expect(xs: &mut Xstate) -> Xresult {
    let val = xs.pop_data()?;
    let pat = bitstring_from(val)?;
    let s = peek_bits(xs, pat.len())?;
    if !s.eq_with(&pat) {
        let pos = s.bits().zip(pat.bits()).position(|(a, b)| a != b).unwrap_or(0);
        return Err(Xerr::MatchError { src: s, expect: pat, fail_pos: pos });
    }
    move_offset_checked(xs, s.end())
}

fn read_bits(xs: &mut Xstate, n: usize) -> Xresult {
    let s = peek_bits(xs, n)?;
    move_offset_checked(xs, s.end())?;
    let val = Cell::from(s);
    xs.push_data(val)
}

fn word_bytes(xs: &mut Xstate) -> Xresult {
    let n = take_length(xs)?;
    read_bits(xs, n * 8)
}

fn word_kbytes(xs: &mut Xstate) -> Xresult {
    let n = take_length(xs)?;
    read_bits(xs, n * 8 * 1024)
}

fn word_mbytes(xs: &mut Xstate) -> Xresult {
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

fn word_bits(xs: &mut Xstate) -> Xresult {
    let n = take_length(xs)?;
    read_bits(xs, n)
}

fn rest_bits(xs: &mut Xstate) -> Xresult1<Xbitstr> {
    let rest = xs.get_var(xs.bitstr_mod.input)?.bitstr()?.clone();
    let start = xs.get_var(xs.bitstr_mod.offset)?.to_usize()?;
    rest.seek(start).ok_or_else(|| Xerr::OutOfBounds(start))
}

fn peek_bits(xs: &mut Xstate, n: usize) -> Xresult1<Xbitstr> {
    let s = xs.get_var(xs.bitstr_mod.input)?.bitstr()?;
    let start = xs.get_var(xs.bitstr_mod.offset)?.to_usize()?;
    let end = start + n;
    if let Some(ss) = s.substr(start, end) {
        Ok(ss)
    } else {
        Err(Xerr::ReadError { src: s.clone(), len: n })
    }
}

fn read_unsigned(xs: &mut Xstate, n: usize, bo: Byteorder) -> Xresult {
    let s = peek_bits(xs, n)?;
    if s.len() > (Xint::BITS - 1) as usize {
        return Err(Xerr::IntegerOverflow);
    }
    let x = s.to_uint(bo) as Xint;
    move_offset_checked(xs, s.end())?;
    let val = Cell::from(x).with_tag(bitstr_int_tag(n, bo));
    xs.push_data(val)    
}

fn read_signed(xs: &mut Xstate, n: usize, bo: Byteorder) -> Xresult {
    let s = peek_bits(xs, n)?;
    if s.len() > Xint::BITS as usize {
        return Err(Xerr::IntegerOverflow);
    }
    let x = s.to_int(bo);
    move_offset_checked(xs, s.end())?;
    let val = Cell::from(x).with_tag(bitstr_int_tag(n, bo));
    xs.push_data(val)
}

fn read_signed_n(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = current_byteorder(xs)?;
    read_signed(xs, n, bo)
}

fn read_unsigned_n(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = current_byteorder(xs)?;
    read_unsigned(xs, n, bo)
}

fn read_float_n(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = current_byteorder(xs)?;
    read_float(xs, n, bo)
}

fn read_float(xs: &mut Xstate, n: usize, bo: Byteorder) -> Xresult {
    let s = peek_bits(xs, n)?;
    let val = match n {
        32 => s.to_f32(bo) as Xreal,
        64 => s.to_f64(bo) as Xreal,
        n => return Err(Xerr::InvalidFloatLength(n)),
    };
    move_offset_checked(xs, s.end())?;
    xs.push_data(Cell::from(val).with_tag(bitstr_real_tag(n, bo)))
}

fn bitstr_int_tag(len: usize, bo: Byteorder) -> Cell {
    let mut v = Xvec::new();
    v.push_back_mut(Cell::from(len).with_tag(Cell::from("len")));
    if bo == BIG {
        v.push_back_mut(Cell::from("big"));
    } else {
        v.push_back_mut(Cell::from("little"));
    }
    Cell::from(v)
}

fn bitstr_real_tag(len: usize, bo: Byteorder) -> Cell {
    let mut v = Xvec::new();
    v.push_back_mut(Cell::from(len).with_tag(Cell::from("len")));
    if bo == Byteorder::Big {
        let s = Xstr::from("be");
        v.push_back_mut(Cell::Str(s));
    }
    Cell::from(v)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitstring_mod() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval("[ 0 0xff ] >bitstr").unwrap();
        let s = xs.pop_data().unwrap();
        assert_eq!(s, Cell::Bitstr(Xbitstr::from(vec![0, 255])));
        xs.set_binary_input(Xbitstr::from(vec![1, 255, 0])).unwrap();
        xs.eval("u8").unwrap();
        assert_eq!(Cell::Int(1), xs.pop_data().unwrap());
        xs.eval("i8").unwrap();
        assert_eq!(Cell::Int(-1), xs.pop_data().unwrap());
        xs.eval("i8").unwrap();
        assert_eq!(Cell::Int(0), xs.pop_data().unwrap());
        assert_eq!(Err(Xerr::IntegerOverflow), xs.eval("[ 256 ] >bitstr"));
        assert_eq!(Err(Xerr::IntegerOverflow), xs.eval("[ -1 ] >bitstr"));
        //xs.interpret("[ \"1\" 0x32 0s0011_0011 ] >bitstr").unwrap();
        //assert_eq!(vec![0x31, 0x32, 0x33], xs.pop_data().unwrap().to_bitstring().unwrap().to_bytes());
    }

    #[test]
    fn test_int_uint() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval("[ 0xff 0xff ] open-bitstr 8 uint 8 int").unwrap();
        assert_eq!(Cell::Int(-1), xs.pop_data().unwrap());
        assert_eq!(Cell::Int(255), xs.pop_data().unwrap());
    }

    #[test]
    fn test_exact_match() {
        let mut xs = Xstate::boot().unwrap();
        xs.set_binary_input(Xbitstr::from("123")).unwrap();
        match xs.eval("\"124\" expect") {
            Err(Xerr::MatchError{ fail_pos, ..}) => assert_eq!(21, fail_pos),
            other => panic!("{:?}", other),
        };
        xs.eval("\"123\" expect").unwrap();
        match xs.eval("[ 0 ] expect") {
            Err(Xerr::ReadError { len,.. }) => assert_eq!(8, len),
            other => panic!("{:?}", other),
        }
        let res = xs.eval(" \"111111\" bin>bitstr open-bitstr \"11101\" bin>bitstr expect");
        match &res {
            Err(Xerr::MatchError{ fail_pos, ..}) => assert_eq!(&3, fail_pos),
            other => panic!("{:?}", other),
        }
        assert_eq!(format!("{}", res.err().unwrap()),
        "source bits are differ from pattern at offset 3\n [ 03 ] source at 3\n [ 01 ] pattern at 3");
    }

    #[test]
    fn test_bitstr_tags() {
        let mut xs = Xstate::boot().unwrap();
        xs.set_binary_input(Xbitstr::from(vec![1, 2, 3, 0])).unwrap();
        {
            xs.eval("u8").unwrap();
            let val = xs.pop_data().unwrap();
            assert_eq!(&Cell::Int(1), val.value());
            assert_eq!(&bitstr_int_tag(8, NATIVE), val.tag().unwrap());
        }
        {
            xs.eval("2 bytes").unwrap();
            let val = xs.pop_data().unwrap();
            assert_eq!(None, val.tag());
            let s = val.value().to_bitstr().unwrap();
            assert_eq!(16, s.len());
            assert_eq!(vec![2, 3], s.to_bytes());
        }
        {        
            xs.eval("2 bits").unwrap();
            let val = xs.pop_data().unwrap();
            assert_eq!(None, val.tag());
            let s = val.value().to_bitstr().unwrap();
            assert_eq!(2, s.len());
        }
        {
            xs.eval("big 2 int").unwrap();
            let val = xs.pop_data().unwrap();
            assert_eq!(&bitstr_int_tag(2, BIG), val.tag().unwrap());
            assert_eq!(&Cell::Int(0), val.value());
        }
        {
            xs.eval("little 2 int").unwrap();
            let val = xs.pop_data().unwrap();
            assert_eq!(&bitstr_int_tag(2, LITTLE), val.tag().unwrap());
            assert_eq!(&Cell::Int(0), val.value());
        }
        {
            let f: f64 = 1.0;
            xs.set_binary_input(Xbitstr::from(f.to_be_bytes().to_vec())).unwrap();
            xs.eval("f64be").unwrap();
            let val = xs.pop_data().unwrap();
            assert_eq!(&Cell::from(f),  val.value());
            assert_eq!(&bitstr_real_tag(64, BIG), val.tag().unwrap());
        }
    }

    #[test]
    fn test_xbytes() {
        let mut xs = Xstate::boot().unwrap();
        let s: Vec<u8> = (0..1024*1024+1024).map(|_| 1).collect();
        xs.set_binary_input(Xbitstr::from(s)).unwrap();
        xs.eval("1 kbytes 1 mbytes remain").unwrap();
        assert_eq!(0, xs.pop_data().unwrap().to_usize().unwrap());
    }

    #[test]
    fn test_to_num_bytes() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval("2 b>").unwrap();
        assert_eq!(16, xs.pop_data().unwrap().to_usize().unwrap());
        xs.eval("4 kb>").unwrap();
        assert_eq!(32768, xs.pop_data().unwrap().to_usize().unwrap());
        xs.eval("3 mb>").unwrap();
        assert_eq!(25165824, xs.pop_data().unwrap().to_usize().unwrap());
    }

    #[test]
    fn test_bitstr_open() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval(include_str!("test-binary-input.xs")).unwrap();
        assert_eq!(Err(Xerr::OutOfBounds(0)), xs.eval("close-bitstr"));
    }

    #[test]
    fn test_bitstr_from_int() {
        let xs = &mut Xstate::boot().unwrap();
        let pop_bytes = |xs: &mut Xstate| xs.pop_data()?.to_bitstr().map(|s| s.to_bytes());
        xs.eval("-128 i8!").unwrap();
        assert_eq!(Ok(vec![0x80]), pop_bytes(xs));
        xs.eval("255 u8!").unwrap();
        assert_eq!(Ok(vec![0xff]), pop_bytes(xs));
        // assert_eq!(Err(Xerr::IntegerOverflow), xs.interpret("-128 u8!"));
        // assert_eq!(Err(Xerr::IntegerOverflow), xs.interpret("128 i8!"));
    }

    #[test]
    fn test_bitstr_read_int_overflow() {
        let xs = &mut Xstate::boot().unwrap();
        let mut bin = Vec::new();
        bin.resize_with(20, || 0xff);
        xs.set_binary_input(Xbitstr::from(bin.clone())).unwrap();
        assert_eq!(Err(Xerr::IntegerOverflow), xs.eval("128 uint"));
        assert_eq!(Err(Xerr::IntegerOverflow), xs.eval("129 int"));
        xs.eval("127 uint").unwrap();
        assert_eq!(Cell::Int(Xint::MAX), xs.pop_data().unwrap());
        xs.set_binary_input(Xbitstr::from(bin.clone())).unwrap();
        xs.eval("128 int").unwrap();
        assert_eq!(Cell::Int(-1), xs.pop_data().unwrap());
    }

    #[test]
    fn test_bitstring_input_seek() {
        let mut xs = Xstate::boot().unwrap();
        xs.set_binary_input(Xbitstr::from(vec![100, 200])).unwrap();
        match xs.eval("100 seek") {
            Err(Xerr::SeekError{offset,..}) => assert_eq!(100, offset),
            other => panic!("{:?}", other),
        }
        assert_ne!(OK, xs.eval("[ ] seek"));
        xs.eval("8 seek u8").unwrap();
        assert_eq!(Cell::Int(200), xs.pop_data().unwrap());
        xs.eval("0 seek u8").unwrap();
        assert_eq!(Cell::Int(100), xs.pop_data().unwrap());
    }

    #[test]
    fn test_bitstr_remain() {
        let mut xs = Xstate::boot().unwrap();
        xs.set_binary_input(Xbitstr::from(vec![1, 2])).unwrap();
        xs.eval("remain").unwrap();
        assert_eq!(Cell::Int(16), xs.pop_data().unwrap());
        xs.eval("5 bits drop remain").unwrap();
        assert_eq!(Cell::Int(11), xs.pop_data().unwrap());
        xs.eval("11 bits drop remain").unwrap();
        assert_eq!(Cell::Int(0), xs.pop_data().unwrap());
    }

    #[test]
    fn test_bitstr_find() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval("[ 33 55 77 ] open-bitstr [ 77 ] find").unwrap();
        assert_eq!(Ok(Cell::Int(16)), xs.pop_data());
        xs.eval("[ 55 77 ] find").unwrap();
        assert_eq!(Ok(Cell::Int(8)), xs.pop_data());
        xs.eval("[ ] find").unwrap();
        assert_eq!(Ok(Cell::Int(0)), xs.pop_data());
        xs.eval("[ 56 ] find").unwrap();
        assert_eq!(Ok(Cell::Nil), xs.pop_data());
        assert_eq!(Err(Xerr::UnalignedBitstr), xs.eval("5 seek [ 56 ] find"));
        xs.eval("[ 0x31 0x32 0x33 ] open-bitstr \"23\" find").unwrap();
        assert_eq!(Ok(Cell::Int(8)), xs.pop_data());
    }

    #[test]
    fn test_bitstr_to_utf8() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval(" \"just text\" >bitstr bitstr>utf8").unwrap();
        assert_eq!(Ok(Xstr::from("just text")), xs.pop_data().unwrap().to_xstr());
        let res = xs.eval(" [ \"just  text\" 0xff 0xff 0xff ] >bitstr bitstr>utf8");
        assert!(res.is_err());
    }

    #[test]
    fn test_bitstr_to_bin() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval(" \"faee\" hex>bitstr bitstr>hex").unwrap();
        assert_eq!(Ok(Xstr::from("faee")), xs.pop_data().unwrap().to_xstr());
    }

    #[test]
    fn test_bitstr_to_hex() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval(" \"1100\" bin>bitstr bitstr>bin").unwrap();
        assert_eq!(Ok(Xstr::from("1100")), xs.pop_data().unwrap().to_xstr());
    }

    #[test]
    fn test_bitstr_and() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval(" [ 0b1001 ] >bitstr [ 0b0011 ] >bitstr bitstr-and").unwrap();
        let res = xs.pop_data().unwrap().to_bitstr().unwrap();
        assert_eq!(res.to_bytes(), vec![0b1001 & 0b0011]);
    }

    #[test]
    fn test_bitstr_or() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval(" [ 0b101 ] >bitstr [ 0b011 ] >bitstr bitstr-or").unwrap();
        let res = xs.pop_data().unwrap().to_bitstr().unwrap();
        assert_eq!(res.to_bytes(), vec![0b101 | 0b011]);
    }

    #[test]
    fn test_bitstr_xor() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval(" [ 0b101 ] >bitstr [ 0b110 ] >bitstr bitstr-xor").unwrap();
        let res = xs.pop_data().unwrap().to_bitstr().unwrap();
        assert_eq!(res.to_bytes(), vec![0b101 ^ 0b110]);
        xs.eval(" [ 0xaa 0xbb 0xcc ] >bitstr [ 0x11 ] >bitstr bitstr-xor").unwrap();
        let res = xs.pop_data().unwrap().to_bitstr().unwrap();
        assert_eq!(res.to_bytes(), vec![0xaa ^ 0x11, 0xbb ^ 0x11, 0xcc ^ 0x11]);
    }

    #[test]
    fn  test_bitstr_pack() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval("255 u8!").unwrap();
        let bs = xs.pop_data().unwrap().to_bitstr().unwrap();
        assert_eq!(bs, Xbitstr::from(vec![255]));
        xs.eval("big 123 32 int!").unwrap();
        let bs = xs.pop_data().unwrap().to_bitstr().unwrap();
        assert_eq!(bs, Xbitstr::from(vec![0, 0, 0, 123]));
        
    }
}

