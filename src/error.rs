use crate::prelude::Xbitstr;

#[derive(PartialEq)]
pub enum Xerr {
    UnknownWord,
    InputIncomplete,
    InputParseError,
    IntegerOverflow,
    ControlFlowError,
    StackUnderflow,
    ReturnStackUnderflow,
    LoopStackUnderflow,
    SpecialStackUnderflow,
    StackNotBalanced,
    TypeError,
    RecusriveDefinition,
    ExpectingName,
    ExpectingKey,
    NotFound,
    InvalidAddress,
    ReadonlyAddress,
    IOError,
    OutOfBounds,
    DebugAssertion,
    InternalError,
    // bitstring errors
    BitReadError(Box<(Xbitstr, usize)>),
    BitSeekError(Box<(Xbitstr, usize)>),
    BitMatchError(Box<(Xbitstr, Xbitstr, usize)>),
    UnalignedBitstr,
    InvalidFloatLength(usize),
    // Stop interpreter execution
    Exit(isize),
}

impl Xerr {
    pub fn name(&self) -> &str {
        match self {
        Xerr::UnknownWord => "UnknownWord",
        Xerr::InputIncomplete => "InputIncomplete",
        Xerr::InputParseError => "InputParseError",
        Xerr::IntegerOverflow => "IntegerOverflow",
        Xerr::ControlFlowError => "ControlFlowError",
        Xerr::StackUnderflow => "StackUnderflow",
        Xerr::ReturnStackUnderflow => "ReturnStackUnderflow",
        Xerr::LoopStackUnderflow => "LoopStackUnderflow",
        Xerr::SpecialStackUnderflow => "SpecialStackUnderflow",
        Xerr::StackNotBalanced => "StackNotBalanced",
        Xerr::TypeError => "TypeError",
        Xerr::RecusriveDefinition => "RecusriveDefinition",
        Xerr::ExpectingName => "ExpectingName",
        Xerr::ExpectingKey => "ExpectingKey",
        Xerr::NotFound => "NotFound",
        Xerr::InvalidAddress => "InvalidAddress",
        Xerr::ReadonlyAddress => "ReadonlyAddress",
        Xerr::IOError => "IOError",
        Xerr::OutOfBounds => "OutOfBounds",
        Xerr::DebugAssertion => "DebugAssertion",
        Xerr::InternalError => "InternalError",
        Xerr::BitReadError{..} => "BitReadError",
        Xerr::BitSeekError{..} => "BitSeekError",
        Xerr::BitMatchError{..} => "BitMatchError",
        Xerr::UnalignedBitstr => "UnalignedBitstr",
        Xerr::InvalidFloatLength{..} => "InvalidFloatLength",
        Xerr::Exit{..} => "Exit",
        }
    }
}

use std::fmt;

impl fmt::Debug for Xerr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{}", self.name()))
    }
}

pub type Xresult = Xresult1<()>;

pub type Xresult1<T> = Result<T, Xerr>;

pub const OK: Xresult = Ok(());
