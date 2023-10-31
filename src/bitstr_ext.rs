use crate::bitstr::*;
use crate::cell::*;
use crate::error::*;
use crate::prelude::*;
use memchr::memmem;
use std::fmt::Write;

const BIG_LIT: Cell = xeh_str_lit!("big");
const LEN_LIT: Cell = xeh_str_lit!("len");
const OFFSET_LIT: Cell = xeh_str_lit!("offset");

#[derive(Default, Clone)]
pub struct BitstrState {
    big_endian: CellRef,
    offset: CellRef,
    input: CellRef,
    stash: CellRef,
    output: CellRef,
    output_len: CellRef,
}

macro_rules! def_data_word {
    ($xs:ident, $n:expr) => {
        $xs.defword(concat!("u", $n), |xs| read_unsigned_n(xs, $n))?;
        $xs.defword(concat!("u", $n, "le"), |xs| read_unsigned(xs, $n, Byteorder::Little))?;
        $xs.defword(concat!("u", $n, "be"), |xs| read_unsigned(xs, $n, Byteorder::Big))?;
        $xs.defword(concat!("i", $n), |xs| read_signed_n(xs, $n))?;
        $xs.defword(concat!("i", $n, "le"), |xs| read_signed(xs, $n, Byteorder::Little))?;
        $xs.defword(concat!("i", $n, "be"), |xs| read_signed(xs, $n, Byteorder::Big))?;
        $xs.defword(concat!("u", $n, "!"), |xs| pack_int(xs, $n))?;
        $xs.defword(concat!("u", $n, "le!"), |xs| pack_int_bo(xs, $n, Byteorder::Little))?;
        $xs.defword(concat!("u", $n, "be!"), |xs| pack_int_bo(xs, $n, Byteorder::Big))?;
        $xs.defword(concat!("i", $n, "!"), |xs| pack_int(xs, $n))?;
        $xs.defword(concat!("i", $n, "le!"), |xs| pack_int_bo(xs, $n, Byteorder::Little))?;
        $xs.defword(concat!("i", $n, "be!"), |xs| pack_int_bo(xs, $n, Byteorder::Big))?;
    };
}

macro_rules! def_data_word_real {
    ($xs:ident, $n:expr) => {
        $xs.defword(concat!("f", $n), |xs| read_float_n(xs, $n))?;
        $xs.defword(concat!("f", $n, "le"), |xs| read_float(xs, $n, Byteorder::Little))?;
        $xs.defword(concat!("f", $n, "be"), |xs| read_float(xs, $n, Byteorder::Big))?;
        $xs.defword(concat!("f", $n, "!"), |xs| pack_float(xs, $n))?;
        $xs.defword(concat!("f", $n, "le!"), |xs| pack_float_bo(xs, $n, Byteorder::Little))?;
        $xs.defword(concat!("f", $n, "be!"), |xs| pack_float_bo(xs, $n, Byteorder::Big))?;
    };
}

pub fn load(xs: &mut Xstate) -> Xresult {
    let mut m = BitstrState::default();
    let empty = Cell::from(Xbitstr::new());
    m.big_endian = xs.defvar(xeh_xstr!("big?"), ZERO)?;
    m.input = xs.defvar(xeh_xstr!("input"), empty)?;
    m.offset = xs.defvar(xeh_xstr!("offset"), ZERO)?;
    m.stash = xs.defvar_anonymous(Cell::from(Xvec::new()))?;
    m.output = xs.defvar(xeh_xstr!("output"), NIL)?;
    m.output_len = xs.defvar(xeh_xstr!("output-length"), ZERO)?;
    xs.bitstr_mod = m;
    xs.defword("open-bitstr", word_open_bitstr)?;
    xs.defword("close-bitstr", word_close_bitstr)?;
    xs.defword(">b", b_units)?;
    xs.defword(">kb", kb_units)?;
    xs.defword(">mb", mb_units)?;
    xs.defword("seek", word_seek)?;
    xs.defword("remain", word_remain)?;
    xs.defword("find", word_find)?;
    xs.defword("dump", word_dump)?;
    xs.defword("dump-at", word_dump_at)?;
    xs.defword("bits", word_bitstr)?;
    xs.defword("bytes", word_bytes)?;
    xs.defword("bitstr-len", bitstr_len)?;
    xs.defword("bitstr-append", bitstring_append)?;
    xs.defword("bitstr-not", word_bitstr_not)?;
    xs.defword("bitstr-and", bitstring_and)?;
    xs.defword("bitstr-or", bitstring_or)?;
    xs.defword("bitstr-xor", bitstring_xor)?;
    xs.defword("hex>bitstr", hex_to_bitstr)?;
    xs.defword("bitstr>hex", bitstr_to_hex)?;
    xs.defword(">bitstr", into_bitstr)?;
    xs.defword("bitstr>utf8", bitstr_to_utf8)?;
    xs.defword("big", |xs| set_byteorder(xs, BIG))?;
    xs.defword("little", |xs| set_byteorder(xs, LITTLE))?;
    xs.defword("magic", word_magic)?;
    xs.defword("emit", word_emit)?;
    xs.defword("write-all", word_write)?;
    xs.defword("read-all", word_read_all)?;
    xs.defword("random-bits", random_bits)?;
    def_data_word!(xs, 8);
    def_data_word!(xs, 16);
    def_data_word!(xs, 32);
    def_data_word!(xs, 64);
    def_data_word_real!(xs, 32);
    def_data_word_real!(xs, 64);
    xs.defword("float", |xs| {
        let n = xs.pop_data()?.to_usize()?;
        let bo = current_byteorder(xs)?;
        read_float(xs, n, bo)
    })?;
    xs.defword("float!", |xs| {
        let n = xs.pop_data()?.to_usize()?;
        let bo = current_byteorder(xs)?;
        pack_float_bo(xs, n, bo)
    })?;
    xs.defword("int", |xs| {
        let n = xs.pop_data()?.to_usize()?;
        let bo = current_byteorder(xs)?;
        read_signed(xs, n, bo)
    })?;
    xs.defword("uint", |xs| {
        let n = xs.pop_data()?.to_usize()?;
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
    xs.defword("nulbytestr", nulbytestr_word)?;
    xs.defword("cstr", cstr_word)?;
    OK
}

pub fn intercept_output(xs: &mut Xstate, yes: bool) -> Xresult {
    if yes {
        let val = xs.get_var(xs.bitstr_mod.output)?;
        if val == &NIL {
            xs.set_var(xs.bitstr_mod.output, Cell::from(Xbitstr::new()))?;
        }
    } else {
        xs.set_var(xs.bitstr_mod.output, NIL)?;
    }
    OK
}

fn pack_int_bo(xs: &mut Xstate, n: usize, bo: Byteorder) -> Xresult {
    let val = xs.pop_data()?.to_xint()?;
    let s = Bitstr::from_int(val, n, bo);
    xs.push_data(Cell::Bitstr(s))
}

fn pack_int(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = current_byteorder(xs)?;
    pack_int_bo(xs, n, bo)
}

fn float_len_err(len: usize) -> Xerr {
    let errmsg = format!("unsupported float length {}", len);
    Xerr::ErrorMsg(errmsg.into())
}

fn pack_float_bo(xs: &mut Xstate, n: usize, bo: Byteorder) -> Xresult {
    let val = xs.pop_data()?.to_real()?;
    let s = match n {
        32 => Bitstr::from_f32(val as f32, bo),
        64 => Bitstr::from_f64(val, bo),
        n => return Err(float_len_err(n)),
    };
    xs.push_data(Cell::Bitstr(s))
}

fn pack_float(xs: &mut Xstate, n: usize) -> Xresult {
    let bo = current_byteorder(xs)?;
    pack_float_bo(xs, n, bo)
}

fn word_find(xs: &mut Xstate) -> Xresult {
    let pat = xs.pop_data()?.to_bitstr()?;
    let rest = rest_bits(xs)?;
    let pat_bytes = pat
        .bytestr()
        .ok_or_else(|| Xerr::ToBytestrError(pat.clone()))?;
    let rest_bytes = rest
        .slice()
        .ok_or_else(|| Xerr::BitstrSliceError(rest.clone()))?;
    if let Some(pos) = memmem::find(&rest_bytes, &pat_bytes) {
        let offs = rest.start() + pos * 8;
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
        Err(Xerr::SeekError {
            src: s.clone(),
            offset: pos,
        })
    }
}

fn bitstr_len(xs: &mut Xstate) -> Xresult {
    let n = xs.pop_data()?.bitstr()?.len();
    xs.push_data(Cell::from(n))
}

fn b_units(xs: &mut Xstate) -> Xresult {
    let n = xs.pop_data()?.to_usize()?;
    xs.push_data(Cell::Int(n as Xint * 8))
}

fn kb_units(xs: &mut Xstate) -> Xresult {
    let n = xs.pop_data()?.to_usize()?;
    xs.push_data(Cell::Int(n as Xint * 8 * 1024))
}

fn mb_units(xs: &mut Xstate) -> Xresult {
    let n = xs.pop_data()?.to_usize()?;
    xs.push_data(Cell::Int(n as Xint * 8 * 1024 * 1024))
}

fn word_seek(xs: &mut Xstate) -> Xresult {
    let pos = xs.pop_data()?.to_usize()?;
    move_offset_checked(xs, pos)
}

fn word_remain(xs: &mut Xstate) -> Xresult {
    let s = current_input(xs)?;
    let offset = current_offset(xs)?;
    let res = Cell::from(s.end().max(offset) - offset);
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
    let ss = s
        .substr(start, end)
        .ok_or_else(|| Xerr::out_of_range(start, s.bits_range()))?;
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

pub(crate) fn fmt_bitstr_dump(s: &Bitstr, ncols: usize) -> String {
    let mut buf = String::new();
    let mut pos = s.start();
    let mut hex = String::new();
    let mut ascii = String::new();
    let mut it = s.iter8();
    let mut result = String::new();
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
        result.push_str(&buf);
        buf.clear();
        hex.clear();
        ascii.clear();
    }
    result
}

fn dump_bitstr(xs: &mut Xstate, s: &Bitstr, ncols: usize) -> Xresult {
    let s = fmt_bitstr_dump(s, ncols);
    xs.print(&s)
}

fn write_dump_position(buf: &mut String, start: usize) {
    let pos = start / 8;
    write!(buf, "{:05x}", pos).unwrap();
    if start % 8 > 0 {
        write!(buf, ",{}", start % 8).unwrap();
    }
}

pub(crate) fn open_bitstr(xs: &mut Xstate, s: Bitstr) -> Xresult {
    let old_offset = xs.get_var(xs.bitstr_mod.offset)?.clone();
    let old_input = xs.get_var(xs.bitstr_mod.input)?.clone();
    xs.set_var(xs.bitstr_mod.offset, Cell::from(s.start()))?;
    xs.set_var(xs.bitstr_mod.input, Cell::from(s))?;
    let stash = xs
        .get_var(xs.bitstr_mod.stash)?
        .vec()?
        .push_back(old_input.insert_tag(OFFSET_LIT.clone(), old_offset));
    xs.set_var(xs.bitstr_mod.stash, Cell::from(stash))
}

fn word_open_bitstr(xs: &mut Xstate) -> Xresult {
    let s = xs.pop_data()?.to_bitstr()?;
    open_bitstr(xs, s)
}

fn word_close_bitstr(xs: &mut Xstate) -> Xresult {
    let stash = xs.get_var(xs.bitstr_mod.stash)?.vec()?;
    let last = stash.last().ok_or_else(|| Xerr::out_of_bounds(0, stash.len()))?;
    let offset = last.get_tag(&OFFSET_LIT).unwrap_or_else(|| &ZERO);
    let input = last.value().clone();
    let stash = stash.drop_last().unwrap();
    xs.set_var(xs.bitstr_mod.offset, offset.clone())?;
    xs.set_var(xs.bitstr_mod.input, input)?;
    xs.set_var(xs.bitstr_mod.stash, Cell::from(stash))?;
    OK
}

fn bitstring_append(xs: &mut Xstate) -> Xresult {
    let head = xs.pop_data()?.to_bitstr()?;
    let tail = xs.pop_data()?.to_bitstr()?;
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
    match Bitstr::from_hex_str(&s) {
        Ok(bs) => xs.push_data(Cell::from(bs)),
        Err(pos) => Err(Xerr::ParseError {
            msg: xeh_xstr!("hex string parse error"),
            substr: s.substr(pos..),
        }),
    }
}

fn bitstr_to_hex(xs: &mut Xstate) -> Xresult {
    let bs = xs.pop_data()?;
    xs.push_data(Cell::from(bs.bitstr()?.to_hex_string()))
}

fn into_bitstr(xs: &mut Xstate) -> Xresult {
    let val = xs.pop_data()?;
    let s = bitstr_concat(val)?;
    xs.push_data(Cell::Bitstr(s))
}

fn decode_utf8_str(bytes: Vec<u8>) -> Xresult1<String> {
    match String::from_utf8(bytes) {
        Ok(s) => Ok(s),
        Err(e) => {
            let pos = e.utf8_error().valid_up_to();
            let bytes = e.into_bytes();
            Err(Xerr::StrDecodeError {
                msg: xeh_xstr!("utf8 bytes parse error"),
                bytes,
                pos,
            })
        }
    }
}

fn bitstr_to_utf8(xs: &mut Xstate) -> Xresult {
    let val = xs.pop_data()?;
    let bs = val.bitstr()?;
    let bytes = bs
        .bytestr()
        .ok_or_else(|| Xerr::ToBytestrError(bs.clone()))?;
    let s = decode_utf8_str(bytes.into_owned())?;
    xs.push_data(Cell::from(s))
}

pub fn bitstr_concat(val: Cell) -> Xresult1<Bitstr> {
    match val.value() {
        Cell::Str(s) => Ok(Bitstr::from(s.to_string().into_bytes())),
        Cell::Vector(v) => {
            let mut tmp = Xbitstr::new();
            for x in v.iter() {
                match x.value() {
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
                    Cell::Vector(v) => {
                        let tmp2 = bitstr_concat(Cell::Vector(v.clone()))?;
                        tmp = tmp.append(&tmp2);
                    }
                    val => return Err(Xerr::type_not_supported(val.clone())),
                }
            }
            Ok(Bitstr::from(tmp))
        }
        Cell::Bitstr(s) => Ok(s.clone()),
        val => Err(Xerr::type_not_supported(val.clone())),
    }
}

fn set_byteorder(xs: &mut Xstate, bo: Byteorder) -> Xresult {
    xs.set_var(
        xs.bitstr_mod.big_endian,
        if bo == LITTLE { ZERO } else { ONE },
    )?;
    OK
}

fn current_byteorder(xs: &mut Xstate) -> Xresult1<Byteorder> {
    if xs.get_var(xs.bitstr_mod.big_endian)? == &ZERO {
        Ok(LITTLE)
    } else {
        Ok(BIG)
    }
}

fn word_emit(xs: &mut Xstate) -> Xresult {
    let bs = xs.pop_data()?.to_bitstr()?;
    let out_ref = xs.bitstr_mod.output;
    let len_ref = xs.bitstr_mod.output_len;
    xs.update_var(len_ref, |old| {
        let new_len = old.to_usize()? + bs.len();
        Ok(Cell::from(new_len))
    })?;
    let out = xs.get_var(out_ref)?;
    if out_ref.is_initialized() && out != &NIL {
        let tmp = out.to_bitstr()?.append(&bs); 
        xs.set_var(out_ref, Cell::from(tmp))
    } else {
        let buf = bs.bytestr().ok_or_else(|| Xerr::ToBytestrError(bs.clone()))?;
        crate::file::write_to_stdout(&buf)
    }
}

fn word_magic(xs: &mut Xstate) -> Xresult {
    let pat = xs.pop_data()?.to_bitstr()?;
    let s = peek_bits(xs, pat.len())?;
    if !s.eq_with(&pat) {
        let pos = s
            .bits()
            .zip(pat.bits())
            .position(|(a, b)| a != b)
            .unwrap_or(0);
        return Err(Xerr::MatchError {
            src: s,
            expect: pat,
            fail_pos: pos,
        });
    }
    move_offset_checked(xs, s.end())?;
    xs.push_data(Cell::from(s))
}

fn read_bits(xs: &mut Xstate, n: usize) -> Xresult {
    let s = peek_bits(xs, n)?;
    move_offset_checked(xs, s.end())?;
    let val = Cell::from(s);
    xs.push_data(val)
}

fn word_bitstr(xs: &mut Xstate) -> Xresult {
    let n = xs.pop_data()?.to_usize()?;
    read_bits(xs, n)
}

fn word_bytes(xs: &mut Xstate) -> Xresult {
    let n = xs.pop_data()?.to_usize()?;
    read_bits(xs, n * 8)
}

fn rest_bits(xs: &mut Xstate) -> Xresult1<Xbitstr> {
    let rest = xs.get_var(xs.bitstr_mod.input)?.bitstr()?.clone();
    let start = xs.get_var(xs.bitstr_mod.offset)?.to_usize()?;
    rest.seek(start).ok_or_else(|| Xerr::out_of_range(start, rest.bits_range()))
}

fn peek_bits(xs: &mut Xstate, n: usize) -> Xresult1<Xbitstr> {
    let s = xs.get_var(xs.bitstr_mod.input)?.bitstr()?;
    let start = xs.get_var(xs.bitstr_mod.offset)?.to_usize()?;
    let end = start + n;
    if let Some(ss) = s.substr(start, end) {
        Ok(ss)
    } else {
        let remain = s.end().max(start) - start; 
        Err(Xerr::ReadError {
            remain,
            len: n,
        })
    }
}

fn read_unsigned(xs: &mut Xstate, n: usize, bo: Byteorder) -> Xresult {
    let s = peek_bits(xs, n)?;
    if s.len() > (Xint::BITS - 1) as usize {
        return Err(Xerr::IntegerOverflow);
    }
    let x = s.to_uint(bo) as Xint;
    move_offset_checked(xs, s.end())?;
    xs.push_data(Cell::from(x).with_tags(bitstr_num_tags(s, bo)))
}

fn read_signed(xs: &mut Xstate, n: usize, bo: Byteorder) -> Xresult {
    let s = peek_bits(xs, n)?;
    if s.len() > Xint::BITS as usize {
        return Err(Xerr::IntegerOverflow);
    }
    let x = s.to_int(bo);
    move_offset_checked(xs, s.end())?;
    xs.push_data(Cell::from(x).with_tags(bitstr_num_tags(s, bo)))
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
        n => return Err(float_len_err(n)),
    };
    move_offset_checked(xs, s.end())?;
    xs.push_data(Cell::from(val).with_tags(bitstr_num_tags(s, bo)))
}

fn bitstr_num_tags(bs: Bitstr, bo: Byteorder) -> Xmap {
    let mut m = Xmap::new();
    m.insert_mut(LEN_LIT, Cell::from(bs.len()));
    if bo == BIG && bo != NATIVE {
        m.insert_mut(BIG_LIT, TRUE);
    }
    m
}

fn nulbytestr_read(xs: &mut Xstate) -> Xresult1<Bitstr> {
    let s = xs.get_var(xs.bitstr_mod.input)?.bitstr()?;
    let start = xs.get_var(xs.bitstr_mod.offset)?.to_usize()?;
    let ss = s.seek(start).ok_or_else(|| Xerr::out_of_range(start, s.bits_range()))?;
    if !ss.is_bytestr() {
        return Err(Xerr::ToBytestrError(ss));
    }
    let mut len = 0;
    for (x, n) in ss.iter8() {
        len += n as usize;
        if x == 0 {
            break;
        }
    }
    let end = start + len;
    s.substr(start, end).ok_or_else(|| Xerr::out_of_range(end, ss.bits_range()))
}

fn nulbytestr_word(xs: &mut Xstate) -> Xresult {
    let bs = nulbytestr_read(xs)?;
    xs.push_data(Cell::from(bs))
}

fn cstr_word(xs: &mut Xstate) -> Xresult {
    let bs = nulbytestr_read(xs)?;
    let mut s = String::with_capacity(bs.len() / 8 + 1);
    for (x, _) in bs.iter8() {
        if x == 0 {
            break;
        }
        let c = char::from_u32(x as u32).unwrap();
        s.push(c)
    }
    xs.push_data(Cell::from(s))
}

fn word_write(xs: &mut Xstate) -> Xresult {
    let data = xs.pop_data()?.to_bitstr()?;
    let path = xs.pop_data()?.to_xstr()?;
    crate::file::fs_overlay::write_all(&path, &data)
}

fn word_read_all(xs: &mut Xstate) -> Xresult {
    let path = xs.pop_data()?.to_xstr()?;
    let buf = crate::file::fs_overlay::read_all(&path)?;
    let bs = Xbitstr::from(buf);
    xs.push_data(Cell::from(bs))
}


fn random_bits(xs: &mut Xstate) -> Xresult {
    let n = xs.pop_data()?.to_usize()?;
    let i = crate::bitstr::upper_bound_index(n);
    let mut buf = Vec::with_capacity(i);
    buf.resize(i, 0);
    getrandom::getrandom(buf.as_mut_slice()).unwrap();
    let bs = if n % 8 > 0 {
        Xbitstr::from(buf).read(n).unwrap()
    } else {
        Xbitstr::from(buf)
    };
    xs.push_data(Cell::from(bs))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::borrow::Cow;

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
        xs.eval("[ \"X\" [ 0x1a [ 0x30 ] ] ] >bitstr").unwrap();
        assert_eq!(
            xs.pop_data().unwrap(),
            Cell::Bitstr(Xbitstr::from(vec!['X' as u8, 0x1a, 0x30]))
        );
        assert_eq!(Err(Xerr::IntegerOverflow), xs.eval("[ 256 ] >bitstr"));
        assert_eq!(Err(Xerr::IntegerOverflow), xs.eval("[ -1 ] >bitstr"));
    }

    #[test]
    fn test_int_uint() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval("|ff ff| open-bitstr 8 uint 8 int").unwrap();
        assert_eq!(Cell::Int(-1), xs.pop_data().unwrap());
        assert_eq!(Cell::Int(255), xs.pop_data().unwrap());
    }

    #[test]
    fn test_exact_match() {
        let mut xs = Xstate::boot().unwrap();
        xs.set_binary_input(Xbitstr::from("123")).unwrap();
        match xs.eval("\"124\" >bitstr magic") {
            Err(Xerr::MatchError { fail_pos, .. }) => assert_eq!(21, fail_pos),
            other => panic!("{:?}", other),
        };
        xs.eval("\"123\" >bitstr magic").unwrap();
        match xs.eval("|00| magic") {
            Err(Xerr::ReadError { len, remain }) => {
                assert_eq!(8, len);
                assert_eq!(0, remain);
            },
            other => panic!("{:?}", other),
        }
        let res = xs.eval(" |xxx xxx| open-bitstr |xxx.x| magic");
        match &res {
            Err(Xerr::MatchError { fail_pos, .. }) => assert_eq!(&3, fail_pos),
            other => panic!("{:?}", other),
        }
        assert_eq!(format!("{}", res.err().unwrap()),
        "source bits are differ from pattern at offset 3\n [ 0x03 ] source at 3\n [ 0x01 ] pattern at 3");
        let mut xs = Xstate::boot().unwrap();
        xs.set_binary_input(Xbitstr::from("abc")).unwrap();    
        xs.eval(" \"abc\" >bitstr magic \"abc\" >bitstr assert-eq").unwrap();
    }

    #[test]
    fn test_bitstr_tags() {
        let mut xs = Xstate::boot().unwrap();
        xs.set_binary_input(Xbitstr::from(vec![1, 2, 3, 0]))
            .unwrap();
        {
            xs.eval("u8").unwrap();
            let val = xs.pop_data().unwrap();
            assert_eq!(&Cell::Int(1), val.value());
            let bs = Bitstr::from_hex_str("01").unwrap();
            assert_eq!(&bitstr_num_tags(bs, NATIVE), val.tags().unwrap());
        }
        {
            xs.eval("16 bits").unwrap();
            let val = xs.pop_data().unwrap();
            assert_eq!(None, val.tags());
            let s = val.value().to_bitstr().unwrap();
            assert_eq!(16, s.len());
            assert_eq!(vec![2, 3], s.to_bytes_with_padding());
        }
        {
            xs.eval("2 bits").unwrap();
            let val = xs.pop_data().unwrap();
            assert_eq!(None, val.tags());
            let s = val.value().to_bitstr().unwrap();
            assert_eq!(2, s.len());
        }
        {
            xs.eval("big 2 int").unwrap();
            let val = xs.pop_data().unwrap();
            let bs = Bitstr::from_int(0, 2, BIG);
            assert_eq!(&bitstr_num_tags(bs, BIG), val.tags().unwrap());
            assert_eq!(&Cell::Int(0), val.value());
        }
        {
            xs.eval("little 2 int").unwrap();
            let val = xs.pop_data().unwrap();
            let bs = Bitstr::from_int(0, 2, LITTLE);
            assert_eq!(&bitstr_num_tags(bs, LITTLE), val.tags().unwrap());
            assert_eq!(&Cell::Int(0), val.value());
        }
        {
            let f: f64 = 1.0;
            let bs = Xbitstr::from(f.to_be_bytes().to_vec());
            xs.set_binary_input(bs.clone()).unwrap();
            xs.eval("64 big float").unwrap();
            let val = xs.pop_data().unwrap();
            assert_eq!(&Cell::from(f), val.value());
            assert_eq!(&bitstr_num_tags(bs, BIG), val.tags().unwrap());
        }
    }

    #[test]
    fn test_bytestr_slice() {
        let bs = Bitstr::from(vec![1, 2]);
        assert!(bs.slice().is_some());
        let (a4, b) = bs.split_at(4).unwrap();
        let b8 = b.peek(8).unwrap();
        assert_eq!(None, a4.slice());
        assert_eq!(None, b8.slice());
        assert!(!a4.is_bytestr());
        assert!(b8.is_bytestr());
        match b8.bytestr() {
            Some(Cow::Owned(_)) => (),
            other => panic!("{:?}", other),
        }
        match bs.bytestr() {
            Some(Cow::Borrowed(_)) => (),
            other => panic!("{:?}", other),
        }
    }

    #[test]
    fn test_bitstr_open() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval(include_str!("test-data/test-binary-input.xeh")).unwrap();
        assert_eq!(Err(Xerr::out_of_bounds(0, 0)), xs.eval("close-bitstr"));
    }
    
    #[test]
    fn test_read_all() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval("\"src/test-data/test-file.txt\" read-all \"1234\" >bitstr assert-eq").unwrap();
    }

    #[test]
    fn test_bitstr_from_int() {
        let xs = &mut Xstate::boot().unwrap();
        let pop_bytes = |xs: &mut Xstate| xs.pop_data()?.to_bitstr().map(|s| s.to_bytes().unwrap());
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
            Err(Xerr::SeekError { offset, .. }) => assert_eq!(100, offset),
            other => panic!("{:?}", other),
        }
        assert_ne!(OK, xs.eval("[ ] seek"));
        xs.eval("8 seek u8").unwrap();
        assert_eq!(Cell::Int(200), xs.pop_data().unwrap());
        xs.eval("0 seek u8").unwrap();
        assert_eq!(Cell::Int(100), xs.pop_data().unwrap());
    }

    #[test]
    fn test_units() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval("1 >b 8 assert-eq").unwrap();
        xs.eval("1 >kb 8192 assert-eq").unwrap();
        xs.eval("1 >mb 8388608 assert-eq").unwrap();
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
        xs.eval("|33 55 77| open-bitstr |77| find").unwrap();
        assert_eq!(Ok(Cell::Int(16)), xs.pop_data());
        xs.eval("|55 77| find").unwrap();
        assert_eq!(Ok(Cell::Int(8)), xs.pop_data());
        xs.eval("|| find").unwrap();
        assert_eq!(Ok(Cell::Int(0)), xs.pop_data());
        xs.eval("|56| find").unwrap();
        assert_eq!(Ok(Cell::Nil), xs.pop_data());
    }

    #[test]
    fn test_bitstr_to_utf8() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval(" \"just text\" >bitstr bitstr>utf8").unwrap();
        assert_eq!(
            Ok(Xstr::from("just text")),
            xs.pop_data().unwrap().to_xstr()
        );
        let res = xs.eval(" [ \"just  text\" 0xff 0xff 0xff ] >bitstr bitstr>utf8");
        assert!(res.is_err());
    }

    #[test]
    fn test_bytes() {
        let mut xs = Xstate::boot().unwrap();
        xs.set_binary_input(Bitstr::from(vec![0x33,0x34,0])).unwrap();
        xs.eval("2 bytes").unwrap();
        let bs = xs.pop_data().unwrap().to_bitstr().unwrap();
        assert_eq!(16, bs.len());
        assert_eq!(vec![0x33,0x34], bs.to_bytes().unwrap());
    }

    #[test]
    fn test_nulbytestr() {
        let mut xs = Xstate::boot().unwrap();
        xs.set_binary_input(Bitstr::from(vec![0x33,0x34,0])).unwrap();
        xs.eval(" nulbytestr |33 34 00| assert-eq").unwrap();
        xs.set_binary_input(Bitstr::from_hex_str("03500").unwrap()).unwrap();
        xs.eval(" 4 uint drop nulbytestr |35 00| assert-eq").unwrap();
        xs.set_binary_input(Bitstr::from_hex_str("360").unwrap()).unwrap();
        assert_ne!(OK, xs.eval("nulbytestr"));
    }

    #[test]
    fn test_cstr() {
        let mut xs = Xstate::boot().unwrap();
        let testvec: Vec<u8> = (1..=255).collect();
        xs.set_binary_input(Bitstr::from(testvec.clone())).unwrap();
        assert_eq!(OK, xs.eval("cstr"));
        let s = xs.pop_data().unwrap().to_xstr().unwrap();
        for (a,b) in s.chars().zip(testvec.iter()) {
            assert_eq!(a as u32, *b as u32);
        }
    }

    #[test]
    fn test_bitstr_to_xeh() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval(" \"f0E\" hex>bitstr bitstr>hex").unwrap();
        assert_eq!(Ok(Xstr::from("f0e")), xs.pop_data().unwrap().to_xstr());
    }

    #[test]
    fn test_bitstr_and() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval(" [ 0b1001 ] >bitstr [ 0b0011 ] >bitstr bitstr-and")
            .unwrap();
        let res = xs.pop_data().unwrap().to_bitstr().unwrap();
        assert_eq!(res.to_bytes_with_padding(), vec![0b1001 & 0b0011]);
    }

    #[test]
    fn test_bitstr_or() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval(" [ 0b101 ] >bitstr [ 0b011 ] >bitstr bitstr-or")
            .unwrap();
        let res = xs.pop_data().unwrap().to_bitstr().unwrap();
        assert_eq!(res.to_bytes_with_padding(), vec![0b101 | 0b011]);
    }

    #[test]
    fn test_bitstr_xor() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval(" [ 0b101 ] >bitstr [ 0b110 ] >bitstr bitstr-xor")
            .unwrap();
        let res = xs.pop_data().unwrap().to_bitstr().unwrap();
        assert_eq!(res.to_bytes().unwrap(), vec![0b101 ^ 0b110]);
        xs.eval(" [ 0xaa 0xbb 0xcc ] >bitstr [ 0x11 ] >bitstr bitstr-xor")
            .unwrap();
        let res = xs.pop_data().unwrap().to_bitstr().unwrap();
        assert_eq!(
            res.to_bytes().unwrap(),
            vec![0xaa ^ 0x11, 0xbb ^ 0x11, 0xcc ^ 0x11]
        );
    }

    #[test]
    fn test_bitstr_pack() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval("255 u8!").unwrap();
        let bs = xs.pop_data().unwrap().to_bitstr().unwrap();
        assert_eq!(bs, Xbitstr::from(vec![255]));
        xs.eval("big 123 32 int!").unwrap();
        let bs = xs.pop_data().unwrap().to_bitstr().unwrap();
        assert_eq!(bs, Xbitstr::from(vec![0, 0, 0, 123]));
    }

    #[test]
    fn test_bitstr_env() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval("big 255 u16! |00ff| assert-eq").unwrap();
        assert_eq!(Err(Xerr::const_context()), xs.eval("( big 255 u16! )"));
    }

    #[test]
    fn test_bitstr_output() {
        let mut xs = Xstate::boot().unwrap();
        xs.intercept_output(true).unwrap();
        xs.eval("0x33 u8! emit output |33| assert-eq
        output-length 8 assert-eq
        0xf 4 uint! emit output |33f| assert-eq
        output-length 12 assert-eq
        ").unwrap();
    }

    #[test]
    fn test_random_bits() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval("
            15 random-bits
            length 15 assert-eq
        ").unwrap();
        xs.eval("
            16 random-bits
            length 16 assert-eq
        ").unwrap();
    }

}
