extern crate rand;

mod arith;
pub mod bitstring;
mod bitstring_mod;
pub mod cell;
pub mod debug;
pub mod error;
pub mod lex;
mod opcodes;
pub mod repl;
pub mod state;

pub mod prelude {
    pub use std::convert::TryInto;
    pub type Xstate = crate::state::State;
    pub type Xcell = crate::cell::Cell;
    pub use crate::error::{Xerr, Xresult, OK};
}
