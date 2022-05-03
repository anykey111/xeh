use crate::prelude::{Cell, Xbitstr, Xstr, Xsubstr};
use crate::state::Flow;

use std::fmt;

#[derive(PartialEq, Clone, Debug)]
pub enum Xerr {
    UnknownWord(Xstr),
    ParseError {
        msg: Xstr,
        substr: Xsubstr,
    },
    StrDecodeError {
        msg: Xstr,
        bytes: Vec<u8>,
        pos: usize,
    },
    ExpectingName,
    ControlFlowError,// { msg: Xstr },
    IntegerOverflow,
    DivisionByZero,
    StackUnderflow,
    ReturnStackUnderflow,
    LoopStackUnderflow,
    SpecialStackUnderflow,
    TypeError,
    TypeErrorMsg {
        val: Cell,
        msg: Xstr,
    },
    InvalidAddress,
    IOError {
        filename: Xstr,
        reason: Xstr,
    },
    OutOfBounds(usize),
    AssertFailed,
    AssertEqFailed {
        a: Cell,
        b: Cell,
    },
    InternalError,
    // bitstring errors
    ReadError {
        src: Xbitstr,
        len: usize,
    },
    SeekError {
        src: Xbitstr,
        offset: usize,
    },
    MatchError {
        src: Xbitstr,
        expect: Xbitstr,
        fail_pos: usize,
    },
    ToBytestrError(Xbitstr),
    BitstrSliceError(Xbitstr),
    // just text error
    ErrorMsg(Xstr),
    // Stop interpreter execution
    Exit(isize),
}

impl fmt::Display for Xerr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Xerr::ErrorMsg(s) => f.write_str(s),
            Xerr::UnknownWord(s) => write!(f, "unknown word {}", s),
            Xerr::ParseError { msg, .. } => write!(f, "{}", msg),
            Xerr::StrDecodeError { msg, .. } => write!(f, "{}", msg),
            Xerr::IntegerOverflow => f.write_str("integer overflow"),
            Xerr::DivisionByZero => f.write_str("division by zero"),
            Xerr::ControlFlowError{..} => f.write_str("control flow error"),
            Xerr::StackUnderflow => f.write_str("stack underflow"),
            Xerr::ReturnStackUnderflow => f.write_str("return stack underflow"),
            Xerr::LoopStackUnderflow => f.write_str("unbalanced loop"),
            Xerr::SpecialStackUnderflow => f.write_str("unbalanced vector"),
            Xerr::TypeError => f.write_str("unexpected type"),
            Xerr::TypeErrorMsg { val, msg } => write!(
                f,
                "expected {}, found {}\n# {:?}",
                msg,
                val.type_name(),
                val
            ),
            Xerr::ExpectingName => f.write_str("expecting a word name"),
            Xerr::InvalidAddress => f.write_str("InvalidAddress"),
            Xerr::IOError { filename, reason } => write!(f, "{}: {}", filename, reason),
            Xerr::OutOfBounds(index) => write!(f, "index {} out of bounds", index),
            Xerr::AssertFailed => f.write_str("assertion failed"),
            Xerr::AssertEqFailed { a, b } => {
                f.write_str("assertion failed, a <> b:")?;
                writeln!(f, "b: {:?}", b)?;
                write!(f, "a: {:?}", a)
            }
            Xerr::InternalError => f.write_str("InternalError"),
            Xerr::ToBytestrError { .. } => f.write_str("bytestr need to be divisible by 8"),
            Xerr::BitstrSliceError { .. } => f.write_str("bitstr not aligned to byte boundary"),
            Xerr::Exit { .. } => f.write_str("Exit"),
            Xerr::ReadError { src, len } => {
                write!(
                    f,
                    "trying to read {} bits while only {} remain",
                    len,
                    src.len()
                )
            }
            Xerr::SeekError { src, offset } => {
                write!(
                    f,
                    "bitstr offset {} out of range {}..{}",
                    offset,
                    src.start(),
                    src.end()
                )
            }
            Xerr::MatchError {
                src,
                expect,
                fail_pos,
            } => {
                let fail_pos = *fail_pos;
                writeln!(
                    f,
                    "source bits are differ from pattern at offset {}",
                    fail_pos
                )?;
                write!(f, " [")?;
                let (_, src_diff) = src.split_at(fail_pos).unwrap();
                for (x, _) in src_diff.iter8().take(8) {
                    write!(f, " {:02X}", x)?;
                }
                writeln!(f, " ] source at {}", src.start() + fail_pos)?;
                write!(f, " [")?;
                let (_, pat_diff) = expect.split_at(fail_pos).unwrap();
                for (x, _) in pat_diff.iter8().take(8) {
                    write!(f, " {:02X}", x)?
                }
                write!(f, " ] pattern at {}", expect.start() + fail_pos)
            }
        }
    }
}

macro_rules! errmsg {
    ($msg:expr) => {{
        const MSG: Xstr = arcstr::literal!($msg);
        MSG
    }};
}

impl Xerr {
    pub(crate) fn unbalanced_flow() -> Xerr {
        let msg = errmsg!("unbalanced control flow");
        Xerr::ControlFlowError
    }
    
    pub(crate) fn unbalanced_flow2(_flow: Option<&Flow>) -> Xerr {
        Xerr::ControlFlowError
    }

    pub(crate) fn unbalanced_vec_builder() -> Xerr {
        //let msg = errmsg!("unbalanced vector builder");
        Xerr::ControlFlowError
    }

    pub(crate) fn vec_stack_underflow() -> Xerr {
        // "vector builder stack underflow"
        Xerr::ControlFlowError
    }

    pub(crate) fn unbalanced_context() -> Xerr {
        Xerr::ErrorMsg(errmsg!("unbalanced context"))
    }
}
pub type Xresult = Xresult1<()>;

pub type Xresult1<T> = Result<T, Xerr>;

pub const OK: Xresult = Ok(());


// impl fmt::Display for Flow {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         match self {
//             Flow::If{..} => write!(f, "if"),
//             Flow::Else{..} => write!(f, "else"),
//             Flow::Begin{..} => write!(f, "begin"),
//             Flow::While{..} => write!(f, "while"),
//             Flow::Leave{..} => write!(f, "leave"),
//             Flow::Case{..} => write!(f, "case"),
//             Flow::CaseOf{..} => write!(f, "of"),
//             Flow::CaseEndOf{..} => write!(f, "endof"),
//             Flow::Vec{..} => write!(f, "vector"),
//             Flow::Fun{..} => write!(f, "function"),
//             Flow::Do{..} => write!(f, "do"),
//         }
//     }
// }