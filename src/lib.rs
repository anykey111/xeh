extern crate num_bigint;
extern crate num_traits;
extern crate sha1;

pub mod hash;
pub mod error;
pub mod lex;
pub mod opcodes;
pub mod cell;
pub mod state;

pub mod prelude {
    pub use std::convert::TryInto;
    pub type Xstate = crate::state::State;
    pub type Xcell = crate::cell::Cell;
    pub use crate::error::{Xerr, Xresult};
}