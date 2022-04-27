use crate::prelude::{Xbitstr, Xstr,Cell};

use std::fmt;

#[derive(PartialEq, Clone)]
pub enum Xerr {
    UnknownWord(Xstr),
    InputIncomplete,
    InputParseError,
    ControlFlowError,
    ExpectingName,
    IntegerOverflow,
    DivisionByZero,
    StackUnderflow,
    ReturnStackUnderflow,
    LoopStackUnderflow,
    SpecialStackUnderflow,
    StackNotBalanced,
    TypeError,
    TypeError2(Cell, Cell),
    InvalidAddress,
    IOError { filename: Xstr, reason: Xstr, },
    OutOfBounds(usize),
    AssertFailed,
    AssertEqFailed { a: Cell, b: Cell },
    InternalError,
    // bitstring errors
    ReadError { src: Xbitstr, len: usize },
    SeekError { src: Xbitstr, offset: usize },
    MatchError { src: Xbitstr, expect: Xbitstr, fail_pos: usize },
    RuntimeParseError(Xstr, usize),
    UnalignedBitstr,
    InvalidFloatLength(usize),
    FromUtf8Error,
    // just text error 
    ErrorStr(Xstr),
    // Stop interpreter execution
    Exit(isize),
}

impl fmt::Debug for Xerr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Xerr::ErrorStr(s) => f.write_str(s),
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
            Xerr::TypeError2(a, b) => write!(f, "unexpected types {:?} and {:?}",
                a.value().type_name(), b.value().type_name()),
            Xerr::ExpectingName => f.write_str("expecting a word name"),
            Xerr::InvalidAddress => f.write_str("InvalidAddress"),
            Xerr::IOError { filename, reason } => write!(f, "{}: {}", filename, reason),
            Xerr::OutOfBounds(index) => write!(f, "index {} out of bounds", index),
            Xerr::AssertFailed => f.write_str("assertion failed, the top stack value is zero"),
            Xerr::AssertEqFailed { a, b } => {
                f.write_str("assertion failed:")?;
                writeln!(f, "[0] {:?}", a)?;
                write!(f,   "[1] {:?}", b)
            },
            Xerr::InternalError => f.write_str("InternalError"),
            Xerr::UnalignedBitstr => f.write_str("UnalignedBitstr"),
            Xerr::InvalidFloatLength{..} => f.write_str("InvalidFloatLength"),
            Xerr::Exit{..} => f.write_str("Exit"),
            Xerr::ReadError { src, len } => {
                write!(f, "trying to read {} bits while only {} remain", len, src.len())
            }
            Xerr::SeekError { src, offset } => {
                write!(f, "bitstr offset {} out of range {}..{}", offset, src.start(), src.end())
            }
            Xerr::MatchError { src, expect, fail_pos} => {
                let fail_pos = *fail_pos;
                writeln!(f, "source bits are differ from pattern at offset {}", fail_pos)?;
                write!(f, " [")?;
                let (_, src_diff) = src.split_at(fail_pos).unwrap();
                for (x, _) in src_diff.iter8().take(8) {
                    write!(f, " {:02X}", x)?;
                }
                writeln!(f, " ] source at {}", src.start() + fail_pos)?;
                write!(f, " [")?;
                let (_, pat_diff) = expect.split_at(fail_pos).unwrap();
                for (x, _) in pat_diff.iter8().take(8){
                    write!(f, " {:02X}", x)?
                }
                write!(f, " ] pattern at {}", expect.start() + fail_pos)
            }
            Xerr::RuntimeParseError(_, pos) => {
                write!(f, "char parse error at offset {}", pos)
            }
            Xerr::FromUtf8Error => {
                write!(f, "utf8 parse error")
            }
        }
    }
}

pub type Xresult = Xresult1<()>;

pub type Xresult1<T> = Result<T, Xerr>;

pub const OK: Xresult = Ok(());
