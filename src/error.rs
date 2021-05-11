use crate::prelude::Xbitstr;

#[derive(PartialEq)]
pub enum Xerr {
    UnknownWord,
    InputIncomplete,
    InputParseError,
    IntegerOverflow,
    ControlFlowError,
    StackUnderflow,
    StackOverflow,
    ReturnStackUnderflow,
    LoopStackUnderflow,
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
    OutOfRange,
    BitMatchError(Box<(Xbitstr, Xbitstr)>),
    UnalignedBitstr,
    // return to interpreter loop
    DebugBreak,
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
        Xerr::StackOverflow => "StackOverflow",
        Xerr::ReturnStackUnderflow => "ReturnStackUnderflow",
        Xerr::LoopStackUnderflow => "LoopStackUnderflow",
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
        Xerr::OutOfRange => "OutOfRange",
        Xerr::BitMatchError{..} => "BitMatchError",
        Xerr::UnalignedBitstr => "UnalignedBitstr",
        Xerr::DebugBreak => "DebugBreak",
        }
    }

    pub fn message(&self) -> String {
        use std::fmt::Write;
        let mut msg = String::new();
        match self {
            Xerr::BitMatchError(ctx) => {
                let src = &ctx.0;
                let pat = &ctx.1;
                let pat_len = pat.len() / 8;
                let n = pat_len.min(16);
                writeln!(msg, "error: {} at offset {}", self.name(), src.start()).unwrap();
                write!(msg, " found  [").unwrap();
                for (x, _) in src.iter8().take(n) {
                    write!(msg, " {:02X}", x).unwrap();
                }
                writeln!(msg, " ]").unwrap();
                write!(msg, " expect [").unwrap();
                for (x, _) in  pat.iter8().take(n){
                    write!(msg, " {:02X}", x).unwrap();
                }
                writeln!(msg, " ]").unwrap();
            }
            e => {
                writeln!(msg, "error: {}", self.name()).unwrap();
            }
        }
        msg
    }
}

use std::fmt;

impl fmt::Debug for Xerr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{}", self.message()))
    }
}

pub type Xresult = Xresult1<()>;

pub type Xresult1<T> = Result<T, Xerr>;

pub const OK: Xresult = Ok(());
