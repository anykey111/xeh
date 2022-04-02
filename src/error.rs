use crate::prelude::{Xbitstr, Xstr};

use std::fmt;

#[derive(PartialEq, Clone)]
pub enum Xerr {
    UnknownWord(Xstr),
    InputIncomplete,
    InputParseError,
    IntegerOverflow,
    DivisionByZero,
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

impl fmt::Debug for Xerr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Xerr::UnknownWord(s) => write!(f, "unknown word {}", s),
            Xerr::InputIncomplete => f.write_str("InputIncomplete"),
            Xerr::InputParseError => f.write_str("InputParseError"),
            Xerr::IntegerOverflow => f.write_str("IntegerOverflow"),
            Xerr::DivisionByZero => f.write_str("division by zero"),
            Xerr::ControlFlowError => f.write_str("ControlFlowError"),
            Xerr::StackUnderflow => f.write_str("StackUnderflow"),
            Xerr::ReturnStackUnderflow => f.write_str("ReturnStackUnderflow"),
            Xerr::LoopStackUnderflow => f.write_str("LoopStackUnderflow"),
            Xerr::SpecialStackUnderflow => f.write_str("SpecialStackUnderflow"),
            Xerr::StackNotBalanced => f.write_str("StackNotBalanced"),
            Xerr::TypeError => f.write_str("TypeError"),
            Xerr::RecusriveDefinition => f.write_str("RecusriveDefinition"),
            Xerr::ExpectingName => f.write_str("ExpectingName"),
            Xerr::ExpectingKey => f.write_str("ExpectingKey"),
            Xerr::NotFound => f.write_str("NotFound"),
            Xerr::InvalidAddress => f.write_str("InvalidAddress"),
            Xerr::ReadonlyAddress => f.write_str("ReadonlyAddress"),
            Xerr::IOError => f.write_str("IOError"),
            Xerr::OutOfBounds => f.write_str("OutOfBounds"),
            Xerr::DebugAssertion => f.write_str("DebugAssertion"),
            Xerr::InternalError => f.write_str("InternalError"),
            Xerr::UnalignedBitstr => f.write_str("UnalignedBitstr"),
            Xerr::InvalidFloatLength{..} => f.write_str("InvalidFloatLength"),
            Xerr::Exit{..} => f.write_str("Exit"),
            Xerr::BitReadError(ctx) => {
                writeln!(f, " trying to read {} bits while only {} remain",
                    ctx.1, ctx.0.len())
            }
            Xerr::BitSeekError(ctx) => {
                writeln!(f, " position {} is beyond of available limit {}",
                    ctx.1, ctx.0.end())
            }
            Xerr::BitMatchError(ctx) => {
                let src = &ctx.0;
                let pat = &ctx.1;
                let at = ctx.2;
                writeln!(f, " source bits are differ from pattern at offset {}", at)?;
                write!(f, " [")?;
                let (_, src_diff) = src.split_at(at).unwrap();
                for (x, _) in src_diff.iter8().take(8) {
                    write!(f, " {:02X}", x)?;
                }
                writeln!(f, " ] source at {}", src.start() + at)?;
                write!(f, " [")?;
                let (_, pat_diff) = pat.split_at(at).unwrap();
                for (x, _) in pat_diff.iter8().take(8){
                    write!(f, " {:02X}", x)?
                }
                writeln!(f, " ] pattern at {}", pat.start() + at)
            }
        }
    }
}

pub type Xresult = Xresult1<()>;

pub type Xresult1<T> = Result<T, Xerr>;

pub const OK: Xresult = Ok(());
