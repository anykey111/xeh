use crate::error::*;
use crate::prelude::*;

pub fn load(xs: &mut Xstate) -> Xresult {
    xs.defword("base32", base32_encode)?;
    xs.defword("base32hex", base32hex_encode)?;
    xs.defword("from-base32", base32_decode)?;
    xs.defword("from-base32hex", base32hex_decode)?;
    xs.defword("base64", base64_encode)?;
    xs.defword("from-base64", base64_decode)?;
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
    let bs = Cell::from(Xbitstr::from(res));
    xs.push_data(bs)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_base32() {
        let mut xs = Xstate::boot().unwrap();
        xs.eval("|4131| base32  \"IEYQ====\" assert-eq").unwrap();
        xs.eval("|4131| base32hex  \"84RG\" assert-eq").unwrap();
        xs.eval(" \"84RG\" from-base32hex |4131| assert-eq").unwrap();
        xs.eval(" \"IEYQ====\" from-base32 |4131| assert-eq").unwrap();
        xs.eval(" \"QTE=\" from-base64 |4131| assert-eq").unwrap();
    }
}
