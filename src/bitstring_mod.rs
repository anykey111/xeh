use std::fmt::Write;
use crate::bitstring::*;
use crate::cell::*;
use crate::error::*;
use crate::prelude::*;

#[derive(Default, Clone)]
pub struct BitstrMod {
    big_endian: Xref,
    dump_start: Xref,
    input: Xref,
    input_deck: Xref,
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
    m.big_endian = xs.defvar("big-endian?", ZERO)?;
    m.dump_start = xs.defvar("bitstr/dump-start", Cell::Int(0))?;
    m.input = xs.defvar("bitstr/input", Cell::empty_bitstr())?;
    m.input_deck = xs.defvar("bitstr/input-deck", Cell::empty_vec())?;
    xs.bitstr_mod = m;

    xs.defword("bits", bin_read_bitstring)?;
    xs.defword("bytes", bin_read_bytes)?;
    xs.defword("kbytes", bin_read_kbytes)?;
    xs.defword("mbytes", bin_read_mbytes)?;
    xs.defword("b>", to_num_bytes)?;
    xs.defword("kb>", to_num_kbytes)?;
    xs.defword("mb>", to_num_mbytes)?;
    xs.defword("bitstr-append", bitstring_append)?;
    xs.defword("bitstr-invert", bitstring_invert)?;
    xs.defword(">bitstr", to_bitstring)?;
    xs.defword("big-endian", |xs| set_byteorder(xs, BIG))?;
    xs.defword("little-endian", |xs| set_byteorder(xs, LITTLE))?;
    xs.defword("native-endian", |xs| set_byteorder(xs, NATIVE))?;
    xs.defword("magic-bytes", bin_match)?;

    def_data_word!(xs, 8);
    def_data_word!(xs, 16);
    def_data_word!(xs, 32);
    def_data_word!(xs, 64);
    def_data_word_real!(xs, 32);
    def_data_word_real!(xs, 64);
    xs.defword("int", |xs| {
        let n = take_length(xs)?;
        let bo = default_byteorder(xs)?;
        read_signed(xs, n, bo)
    })?;
    xs.defword("uint", |xs| {
        let n = take_length(xs)?;
        let bo = default_byteorder(xs)?;
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
    xs.defword("seek", seek_bin)?;
    xs.defword("offset", offset_bin)?;
    xs.defword("remain", remain_bin)?;
    xs.defword("find", find_bin)?;
    xs.defword("dump", bitstr_dump)?;
    xs.defword("dump-at", bitstr_dump_at)?;
    xs.defword("bitstr-open", bitstr_open)?;
    xs.defword("bitstr-close", bitstr_close)?;
    OK
}

fn pack_int_bo(xs: &mut Xstate, n: usize, bo: Xbyteorder) -> Xresult {
    let val = xs.pop_data()?.to_int()?;
    let s = Bitstring::from_int(val, n, bo);
    xs.push_data(Cell::Bitstr(s))
}

fn pack_int(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = default_byteorder(xs)?;
    pack_int_bo(xs, n, bo)
}

fn pack_float_bo(xs: &mut Xstate, n: usize, bo: Xbyteorder) -> Xresult {
    let val = xs.pop_data()?.to_real()?;
    let s = match n {
        32 => Bitstring::from_f32(val as f32, bo),
        64 => Bitstring::from_f64(val, bo),
        n => return Err(Xerr::InvalidFloatLength(n)),
    };
    xs.push_data(Cell::Bitstr(s))
}

fn pack_float(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = default_byteorder(xs)?;
    pack_float_bo(xs, n, bo)
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
    let pos = xs.pop_data()?.to_usize()?;
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
    let start = xs.pop_data()?.to_usize()?;
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

pub fn byte_to_dump_char(x: u8) -> char {
    let c = std::char::from_u32(x as u32).unwrap();
    if c.is_ascii_graphic() {
        c
    } else {
        '.'
    }
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
        write_dump_position(&mut buf, pos);
        buf.push(':');
        for _ in 0..ncols {
            if let Some((x, nbits)) = it.next() {
                buf.push(if pos <= marker && marker <= (pos + nbits as usize) { '*' } else { ' ' });
                write!(buf, "{:02x}", x).unwrap();
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

pub(crate) fn bitstr_open(xs: &mut Xstate) -> Xresult {
    let new_bin = bitstring_from(xs.pop_data()?)?;
    let old = xs.set_var(xs.bitstr_mod.input, Cell::from(new_bin))?;
    let mut deck = xs.get_var(xs.bitstr_mod.input_deck)?.to_vector()?;
    deck.push_back_mut(old);
    xs.set_var(xs.bitstr_mod.input_deck, Cell::from(deck))?;
    OK
}

fn bitstr_close(xs: &mut Xstate) -> Xresult {
    let mut deck = xs.get_var(xs.bitstr_mod.input_deck)?.to_vector()?;
    let bin = deck.last().ok_or_else(|| Xerr::ControlFlowError)?.clone();
    deck.drop_last_mut();
    xs.set_var(xs.bitstr_mod.input_deck, Cell::from(deck))?;
    xs.set_var(xs.bitstr_mod.input, bin)?;
    OK
}

fn bitstring_append(xs: &mut Xstate) -> Xresult {
    let head = xs.pop_data()?.to_bitstring()?;
    let tail = xs.pop_data()?;
    let tail = bitstring_from(tail)?;
    let result = head.append(&tail);
    xs.push_data(Cell::Bitstr(result))
}

fn bitstring_invert(xs: &mut Xstate) -> Xresult {
    let s = xs.pop_data()?.to_bitstring()?;
    xs.push_data(Cell::Bitstr(s.invert()))
}

fn to_bitstring(xs: &mut Xstate) -> Xresult {
    let val = xs.pop_data()?;
    let s = bitstring_from(val)?;
    xs.push_data(Cell::Bitstr(s))
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
    let n = xs.pop_data()?.to_int()?;
    Ok(n as usize)
}

fn set_rest(xs: &mut Xstate, rest: Bitstring) -> Xresult {
    xs.set_var(xs.bitstr_mod.input, Cell::Bitstr(rest)).map(|_| ())
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
    set_rest(xs, rest)
}

fn read_bits(xs: &mut Xstate, n: usize) -> Xresult {
    let (s, rest) = read_bitstring(xs, n)?;
    let val = Cell::Bitstr(s).with_meta(bitstr_meta(n, None, false));
    xs.push_data(val)?;
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

fn read_bitstring(xs: &mut Xstate, n: usize) -> Xresult1<(Xbitstr, Xbitstr)> {
    let mut rest = bitstr_input(xs)?.clone();
    if let Some(s) = rest.read(n as usize) {
        Ok((s, rest))
    } else {
        Err(box_read_error(rest, n))
    }
}

fn read_unsigned(xs: &mut Xstate, n: usize, bo: Xbyteorder) -> Xresult {
    let (s, rest) = read_bitstring(xs, n)?;
    if s.len() > (Xint::BITS - 1) as usize {
        return Err(Xerr::IntegerOverflow);
    }
    let x = s.to_uint(bo) as Xint;
    let val = Cell::Int(x).with_meta(bitstr_meta(n, Some(bo), false));
    xs.push_data(val)?;
    set_rest(xs, rest)
}

fn read_signed(xs: &mut Xstate, n: usize, bo: Xbyteorder) -> Xresult {
    let (s, rest) = read_bitstring(xs, n)?;
    if s.len() > Xint::BITS as usize {
        return Err(Xerr::IntegerOverflow);
    }
    let x = s.to_int(bo);
    let val = Cell::Int(x).with_meta(bitstr_meta(n, Some(bo), true));
    xs.push_data(val)?;
    set_rest(xs, rest)
}

fn read_signed_n(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = default_byteorder(xs)?;
    read_signed(xs, n, bo)
}

fn read_unsigned_n(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = default_byteorder(xs)?;
    read_unsigned(xs, n, bo)
}

fn read_float_n(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = default_byteorder(xs)?;
    read_float(xs, n, bo)
}

fn read_float(xs: &mut Xstate, n: usize, bo: Xbyteorder) -> Xresult {
    let (s, rest) = read_bitstring(xs, n)?;
    let val = match n {
        32 => s.to_f32(bo) as Xreal,
        64 => s.to_f64(bo) as Xreal,
        n => return Err(Xerr::InvalidFloatLength(n)),
    };
    xs.push_data(Cell::from(val).with_meta(bitstr_meta(n, Some(bo), true)))?;
    set_rest(xs, rest)
}

fn bitstr_meta(len: usize, bo: Option<Xbyteorder>, signed: bool) -> Cell {
    let mut v = Xvec::new();
    v.push_back_mut(Cell::from(len));
    if bo == Some(Xbyteorder::Big) {
        let s = Xstr::from("big");
        v.push_back_mut(Cell::Str(s));
    }
    if signed {
        let s = Xstr::from("signed");
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
        xs.eval("[ 0xff 0xff ] bitstr-open 8 uint 8 int").unwrap();
        assert_eq!(Cell::Int(-1), xs.pop_data().unwrap());
        assert_eq!(Cell::Int(255), xs.pop_data().unwrap());
    }

    #[test]
    fn test_bitstring_match() {
        let mut xs = Xstate::boot().unwrap();
        xs.set_binary_input(Xbitstr::from(vec![0x31, 0x32, 0x33])).unwrap();
        match xs.eval("\"124\" magic-bytes") {
            Err(Xerr::BitMatchError(ctx)) => assert_eq!(16, ctx.2),
            other => panic!("{:?}", other),
        };
        xs.eval("\"123\" magic-bytes").unwrap();
        match xs.eval("[ 0 ] magic-bytes") {
            Err(Xerr::BitReadError(ctx)) => assert_eq!(8, ctx.1),
            other => panic!("{:?}", other),
        }
    }

    #[test]
    fn test_bitstring_meta() {
        let mut xs = Xstate::boot().unwrap();
        xs.set_binary_input(Xbitstr::from(vec![1, 2, 3, 0])).unwrap();
        {
            xs.eval("u8").unwrap();
            let val = xs.pop_data().unwrap();
            assert_eq!(&Cell::Int(1), val.value());
            assert_eq!(&bitstr_meta(8, None, false), val.meta().unwrap());
        }
        {
            xs.eval("2 bytes").unwrap();
            let val = xs.pop_data().unwrap();
            assert_eq!(&bitstr_meta(16, None, false), val.meta().unwrap());
            let s = val.value().to_bitstring().unwrap();
            assert_eq!(16, s.len());
            assert_eq!(vec![2, 3], s.to_bytes());
        }
        {        
            xs.eval("2 bits").unwrap();
            let val = xs.pop_data().unwrap();
            assert_eq!(&bitstr_meta(2, None, false), val.meta().unwrap());
            let s = val.value().to_bitstring().unwrap();
            assert_eq!(2, s.len());
        }
        {
            xs.eval("big-endian 2 int").unwrap();
            let val = xs.pop_data().unwrap();
            assert_eq!(&bitstr_meta(2, Some(BIG), true), val.meta().unwrap());
            assert_eq!(&Cell::Int(0), val.value());
        }
        {
            let f: f64 = 1.0;
            xs.set_binary_input(Xbitstr::from(f.to_be_bytes().to_vec())).unwrap();
            xs.eval("f64be").unwrap();
            let val = xs.pop_data().unwrap();
            assert_eq!(&Cell::from(f),  val.value());
            assert_eq!(&bitstr_meta(64, Some(BIG), true), val.meta().unwrap());
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
        xs.eval(
            "
        [ 1 5 7 ] bitstr-open u8
        [ 3 ] bitstr-open u8
        bitstr-close
        u8",
        )
        .unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(3)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        xs.eval("bitstr/input").unwrap();
        let s = xs.pop_data().unwrap().to_bitstring().unwrap();
        assert_eq!(vec![7], s.to_bytes());
        xs.eval("bitstr-close bitstr/input").unwrap();
        let s2 = xs.pop_data().unwrap().to_bitstring().unwrap();
        assert_eq!(0, s2.len());
        assert_eq!(Err(Xerr::ControlFlowError), xs.eval("bitstr-close"));
        xs.eval("bitstr/input").unwrap();
        let empty = xs.pop_data().unwrap().to_bitstring().unwrap(); 
        assert_eq!(0, empty.len());
    }

    #[test]
    fn test_bitstr_from_int() {
        let xs = &mut Xstate::boot().unwrap();
        let pop_bytes = |xs: &mut Xstate| xs.pop_data()?.to_bitstring().map(|s| s.to_bytes());
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
            Err(Xerr::BitSeekError(ctx)) => assert_eq!(100, ctx.1),
            other => panic!("{:?}", other),
        }
        assert_eq!(Err(Xerr::TypeError), xs.eval("[ ] seek"));
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
        xs.eval("[ 33 55 77 ] bitstr-open [ 77 ] find").unwrap();
        assert_eq!(Ok(Cell::Int(16)), xs.pop_data());
        xs.eval("[ 55 77 ] find").unwrap();
        assert_eq!(Ok(Cell::Int(8)), xs.pop_data());
        xs.eval("[ ] find").unwrap();
        assert_eq!(Ok(Cell::Int(0)), xs.pop_data());
        xs.eval("[ 56 ] find").unwrap();
        assert_eq!(Ok(Cell::Nil), xs.pop_data());
        assert_eq!(Err(Xerr::UnalignedBitstr), xs.eval("5 seek [ 56 ] find"));
        xs.eval("[ 0x31 0x32 0x33 ] bitstr-open \"23\" find").unwrap();
        assert_eq!(Ok(Cell::Int(8)), xs.pop_data());
    }

    #[test]
    fn  test_bitstr_pack() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval("255 u8!").unwrap();
        let bs = xs.pop_data().unwrap().to_bitstring().unwrap();
        assert_eq!(bs, Xbitstr::from(vec![255]));
        xs.eval("big-endian 123 32 int!").unwrap();
        let bs = xs.pop_data().unwrap().to_bitstring().unwrap();
        assert_eq!(bs, Xbitstr::from(vec![0, 0, 0, 123]));
        
    }
}
