macro_rules! xeh_xstr {
    ($msg:literal) => {{
        const MSG: Xstr = arcstr::literal!($msg);
        MSG
    }};
}

#[macro_export]
macro_rules! xeh_str_lit {
    ($s:literal) => {{
        const S: Xstr = arcstr::literal!($s);
        $crate::cell::Cell::Str(S)
    }};
}

#[macro_export]
macro_rules! xeh_map {
    ($($k:expr => $v:expr),*) => {
        {
            #[allow(unused_mut)]
            let mut m = $crate::cell::Xmap::new();
            $(
                m.insert_mut($crate::cell::Cell::from($k), $crate::cell::Cell::from($v));
            )*
            m
        }
    };
}

#[macro_export]
macro_rules! xeh_vec {
    ($($e:expr),*) => {
        {
            #[allow(unused_mut)]
            let mut v = $crate::cell::Xvec::new();
            $(
                v.push_back_mut($crate::cell::Cell::from($e));
            )*
            v
        }
    };
}

#[macro_export]
macro_rules! xeh_lit {
    ($x:literal) => {{
        $crate::cell::Cell::from($x)
    }}
}

mod arith;
mod istype;
pub mod bitstr;
pub mod bitstr_ext;
pub mod base_ext;
pub mod cell;
pub mod d2_plugin;
pub mod error;
pub mod file;
mod fmt_flags;
pub mod lex;
mod opcodes;
#[cfg(feature = "stdio")]
pub mod repl;
pub mod state;

pub mod prelude {
    pub use std::convert::TryInto;
    pub type Xstate = crate::state::State;
    pub use crate::cell::*;
    pub use crate::error::*;
    pub type Xlex = crate::lex::Lex;
    pub type Xcell = crate::cell::Cell;
    pub use crate::cell::Xstr;
    pub use crate::lex::TokenLocation;
}

pub mod c_api {
    use std::ptr::{null, null_mut};

    use crate::prelude::{Xcell, Xstate};

    #[no_mangle]
    pub unsafe extern "C" fn xeh_open() -> *mut Xstate {
        match Xstate::boot() {
            Ok(xs) => Box::into_raw(Box::new(xs)),
            Err(err) => {
                eprintln!("error {:?}", err);
                null_mut()
            }
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn xeh_close(xs: *mut Xstate) {
        if xs != null_mut() {
            drop(Box::from_raw(xs));
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn xeh_snapshot(xs: *mut Xstate) -> *mut Xstate {
        let xs = Box::from_raw(xs);
        let xs2 = xs.clone();
        Box::into_raw(xs);
        Box::into_raw(xs2)
    }

    #[no_mangle]
    pub unsafe extern "C" fn xeh_top_len(xs: *mut Xstate) -> usize {
        let xs = Box::from_raw(xs);
        let n = xs.data_depth();
        Box::into_raw(xs);
        n
    }

    #[no_mangle]
    pub unsafe extern "C" fn xeh_is_nil(val: *const Xcell) -> bool {
        match *val {
            Xcell::Nil => true,
            _ => false,
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn xeh_is_int(val: *const Xcell) -> bool {
        match *val {
            Xcell::Int(_) => true,
            _ => false,
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn xeh_is_real(val: *const Xcell) -> bool {
        match *val {
            Xcell::Real(_) => true,
            _ => false,
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn xeh_is_string(val: *const Xcell) -> bool {
        match *val {
            Xcell::Str(_) => true,
            _ => false,
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn xeh_is_vector(val: *const Xcell) -> bool {
        match *val {
            Xcell::Vector(_) => true,
            _ => false,
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn xeh_is_bitstr(val: *const Xcell) -> bool {
        match *val {
            Xcell::Bitstr(_) => true,
            _ => false,
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn xeh_bitstr_bytes(val: *const Xcell) -> *const u8 {
        match &*val {
            Xcell::Bitstr(s) => 
                if let Some(bytes) = s.bytestr() {
                    bytes.as_ptr()
                } else {
                    null()
                },
            _ => null(),
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn xeh_bitstr_len(val: *const Xcell) -> usize {
        match &*val {
            Xcell::Bitstr(s) => s.len(),
            _ => 0,
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn xeh_vector_len(val: *const Xcell) -> usize {
        match &*val {
            Xcell::Vector(v) => v.len(),
            _ => 0,
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn xeh_vector_at(val: *const Xcell, idx: usize) -> *mut Xcell {
        match &*val {
            Xcell::Vector(v) => {
                if let Some(c) = v.get(idx) {
                    Box::into_raw(Box::new(c.clone()))
                } else {
                    null_mut()
                }
            }
            _ => null_mut(),
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn xeh_release(val: *mut Xcell) {
        if val != null_mut() {
            drop(Box::from_raw(val));
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn xeh_pop(xs: *mut Xstate) -> *mut Xcell {
        let mut xs = Box::from_raw(xs);
        let result = if let Ok(val) = xs.pop_data() {
            Box::into_raw(Box::new(val))
        } else {
            null_mut()
        };
        Box::into_raw(xs);
        result
    }

    #[no_mangle]
    pub unsafe extern "C" fn xeh_push(xs: *mut Xstate, val: *mut Xcell) {
        let mut xs = Box::from_raw(xs);
        let val = Box::from_raw(val);
        xs.push_data(*val).unwrap();
        Box::into_raw(xs);
    }
}
