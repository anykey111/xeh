extern crate num_bigint;
extern crate num_traits;
extern crate sha1;
extern crate rand;

pub mod lex;
mod opcodes;
mod arith;
pub mod hash;
pub mod error;
pub mod cell;
pub mod state;
pub mod repl;
pub mod debug;

pub mod prelude {
    pub use std::convert::TryInto;
    pub type Xstate = crate::state::State;
    pub type Xcell = crate::cell::Cell;
    pub use crate::error::{Xerr, Xresult};
}