mod arith;
pub mod bitstring;
mod bitstring_mod;
pub mod cell;
pub mod debug;
pub mod error;
pub mod lex;
mod opcodes;
#[cfg(feature = "stdio")]
pub mod repl;
pub mod state;
mod file;

pub mod prelude {
    pub use std::convert::TryInto;
    pub type Xstate = crate::state::State;
    pub use crate::error::*;
    pub use crate::cell::*;
}
