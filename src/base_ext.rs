use crate::error::*;
use crate::prelude::*;

pub fn load(xs: &mut Xstate) -> Xresult {
    xs.defword("base32", base32_encode)?;
    xs.defword("base32hex", base32hex_encode)?;
    xs.defword("from-base32", base32_decode)?;
    xs.defword("from-base32hex", base32hex_decode)?;
    xs.defword("base64", base64_encode)?;
    xs.defword("zero85", zero85_encode)?;
    xs.defword("zero85>", zero85_decode)?;
    OK
}

pub fn base32_encode2(xs: &mut Xstate, alphabet: base32::Alphabet) -> Xresult {
    let val = xs.pop_data()?;
    let bs = crate::bitstr_ext::bitstr_concat(val)?;
    let bytes = bs.bytestr().ok_or_else(|| Xerr::ToBytestrError(bs.clone()))?;
    let res = base32::encode(alphabet, &bytes);
    let s = Cell::from(Xstr::from(res));
    xs.push_data(s)
}

pub fn base32_encode(xs: &mut Xstate) -> Xresult {
    base32_encode2(xs, base32::Alphabet::RFC4648 { padding: true })
}

pub fn base32hex_encode(xs: &mut Xstate) -> Xresult {
    base32_encode2(xs, base32::Alphabet::Crockford)
}

pub fn base32_decode2(xs: &mut Xstate, alphabet: base32::Alphabet) -> Xresult {
    let s = xs.pop_data()?.to_xstr()?;
    let res = base32::decode(alphabet, &s)
        .ok_or_else(|| Xerr::ErrorMsg(xstr_literal!("base32 decode error")))?;
    let bs = Cell::from(Xbitstr::from(res));
    xs.push_data(bs)
}

pub fn base32_decode(xs: &mut Xstate) -> Xresult {
    base32_decode2(xs, base32::Alphabet::RFC4648 { padding: true })
}

pub fn base32hex_decode(xs: &mut Xstate) -> Xresult {
    base32_decode2(xs, base32::Alphabet::Crockford)
}

pub fn base64_encode(xs: &mut Xstate) -> Xresult {
    use base64::{Engine as _, engine::general_purpose};
    let val = xs.pop_data()?;
    let bs = crate::bitstr_ext::bitstr_concat(val)?;
    let bytes = bs.bytestr().ok_or_else(|| Xerr::ToBytestrError(bs.clone()))?;
    let res = general_purpose::STANDARD.encode(&bytes);
    let s = Cell::from(Xstr::from(res));
    xs.push_data(s)
}

pub fn base64_decode(xs: &mut Xstate) -> Xresult {
    use base64::{Engine as _, engine::general_purpose};
    let s = xs.pop_data()?.to_xstr()?;
    let res = general_purpose::STANDARD.decode(&s)
        .map_err(|_| Xerr::ErrorMsg(xstr_literal!("base64 decode error")))?;
pub fn zero85_encode(xs: &mut Xstate) -> Xresult {
    let val = xs.pop_data()?;
    let bs = crate::bitstr_ext::bitstr_concat(val)?;
    let bytes = bs.bytestr().ok_or_else(|| Xerr::ToBytestrError(bs.clone()))?;
    let res = z85::encode(&bytes);
    let s = Xstr::from(res);
    xs.push_data(Cell::from(s))
}

pub fn zero85_decode_res(xs: &mut Xstate) -> Xresult1<Xbitstr> {
    let s = xs.pop_data()?.to_xstr()?;
    let res = z85::decode(&s)
        .map_err(|_| Xerr::ErrorMsg(xstr_literal!("zero85 decode error")))?;
    Ok(Xbitstr::from(res))
}

pub fn zero85_decode(xs: &mut Xstate) -> Xresult {
    if let Ok(bs) = zero85_decode_res(xs) {
        xs.push_data(Cell::from(bs))
    } else {
        xs.push_data(NIL)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_base32() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval("|4131| base32  \"IEYQ====\" assert-eq").unwrap();
        xs.eval("|4131| base32hex  \"84RG\" assert-eq").unwrap();
        xs.eval("|86 4F D2 6F B5 59 F7 5B| zero85 \"HelloWorld\" assert-eq").unwrap();
        xs.eval("\"HelloWorld\" zero85> |86 4F D2 6F B5 59 F7 5B| assert-eq").unwrap();

        xs.eval("\"JTKVSB%%)wK0E.X)V>+}o?pNmC{O&4W4b!Ni{Lh6\" zero85>
            |8E 0B DD 69 76 28 B9 1D 
            8F 24 55 87 EE 95 C5 B0 
            4D 48 96 3F 79 25 98 77 
            B4 9C D9 06 3A EA D3 B7|
            assert-eq").unwrap();

        xs.eval("\"JTK``\" zero85> nil assert-eq").unwrap();
    }
}
