use crate::prelude::{Xbitstr, Xstr,Cell};

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
    NotFound,
    InvalidAddress,
    ReadonlyAddress,
    IOError { filename: Xstr, reason: Xstr, },
    OutOfBounds,
    AssertFailed,
    AssertEqFailed(Cell, Cell),
    InternalError,
    // bitstring errors
    BitReadError(Box<(Xbitstr, usize)>),
    BitSeekError(Box<(Xbitstr, usize)>),
    BitMatchError(Box<(Xbitstr, Xbitstr, usize)>),
    BitstrParseError(Xstr, usize),
    UnalignedBitstr,
    InvalidFloatLength(usize),
    FromUtf8Error,
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
            Xerr::NotFound => f.write_str("NotFound"),
            Xerr::InvalidAddress => f.write_str("InvalidAddress"),
            Xerr::ReadonlyAddress => f.write_str("ReadonlyAddress"),
            Xerr::IOError { filename, reason } => writeln!(f, "{}: {}", filename, reason),
            Xerr::OutOfBounds => f.write_str("OutOfBounds"),
            Xerr::AssertFailed => f.write_str("assertion failed, the top stack value is zero"),
            Xerr::AssertEqFailed(a, b) => {
                writeln!(f, "assertion failed, two top stack values not equals")?;
                writeln!(f, "[0] {:?}", a)?;
                writeln!(f, "[1] {:?}", b)
            },
            Xerr::InternalError => f.write_str("InternalError"),
            Xerr::UnalignedBitstr => f.write_str("UnalignedBitstr"),
            Xerr::InvalidFloatLength{..} => f.write_str("InvalidFloatLength"),
            Xerr::Exit{..} => f.write_str("Exit"),
            Xerr::BitReadError(ctx) => {
                writeln!(f, "trying to read {} bits while only {} remain",
                    ctx.1, ctx.0.len())
            }
            Xerr::BitSeekError(ctx) => {
                writeln!(f, "position {} is beyond of available limit {}",
                    ctx.1, ctx.0.end())
            }
            Xerr::BitMatchError(ctx) => {
                let src = &ctx.0;
                let pat = &ctx.1;
                let at = ctx.2;
                writeln!(f, "source bits are differ from pattern at offset {}", at)?;
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
            Xerr::BitstrParseError(_, pos) => {
                writeln!(f, "char parse error at offset {}", pos)
            }
            Xerr::FromUtf8Error => {
                writeln!(f, "utf8 parse error")
            }
        }
    }
}

pub type Xresult = Xresult1<()>;

pub type Xresult1<T> = Result<T, Xerr>;

pub const OK: Xresult = Ok(());
