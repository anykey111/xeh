use crate::cell::*;
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
    ExpectingLiteral,
    ControlFlowError {
        msg: Xstr,
    },
    IntegerOverflow,
    DivisionByZero,
    StackUnderflow,
    ReturnStackUnderflow,
    LoopStackUnderflow,
    TypeError,
    TypeErrorMsg {
        val: Cell,
        msg: Xstr,
    },
    TypeNotSupported { val: Cell },
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
        remain: usize,
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
            Xerr::ControlFlowError { msg } => f.write_str(msg),
            Xerr::StackUnderflow => f.write_str("stack underflow"),
            Xerr::ReturnStackUnderflow => f.write_str("return stack underflow"),
            Xerr::LoopStackUnderflow => f.write_str("unbalanced loop"),
            Xerr::TypeError => f.write_str("unexpected type"),
            Xerr::TypeNotSupported { val } => write!(
                f, "value type of {} is not supported:\n{:?}",
                val.type_name(),
                val
            ),
            Xerr::TypeErrorMsg { val, msg } => write!(
                f,
                "expected {}, found {}\n# {:?}",
                msg,
                val.type_name(),
                val
            ),
            Xerr::ExpectingName => f.write_str("expecting a word name"),
            Xerr::ExpectingLiteral => f.write_str("expecting literal value"),
            Xerr::InvalidAddress => f.write_str("InvalidAddress"),
            Xerr::IOError { filename, reason } => write!(f, "{}: {}", filename, reason),
            Xerr::OutOfBounds(index) => write!(f, "index {} out of bounds", index),
            Xerr::AssertFailed => f.write_str("assertion failed"),
            Xerr::AssertEqFailed { a, b } => {
                writeln!(f, "assertion failed, a <> b")?;
                writeln!(f, "b: {:?}", b)?;
                write!(f, "a: {:?}", a)
            }
            Xerr::InternalError => f.write_str("InternalError"),
            Xerr::ToBytestrError { .. } => f.write_str("bytestr need to be divisible by 8"),
            Xerr::BitstrSliceError { .. } => f.write_str("bitstr not aligned to byte boundary"),
            Xerr::Exit { .. } => f.write_str("Exit"),
            Xerr::ReadError { remain, len } => {
                write!(
                    f,
                    "trying to read {} bits while only {} remain",
                    len,
                    remain
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
                    write!(f, " 0x{:02X}", x)?;
                }
                writeln!(f, " ] source at {}", src.start() + fail_pos)?;
                write!(f, " [")?;
                let (_, pat_diff) = expect.split_at(fail_pos).unwrap();
                for (x, _) in pat_diff.iter8().take(8) {
                    write!(f, " 0x{:02X}", x)?
                }
                write!(f, " ] pattern at {}", expect.start() + fail_pos)
            }
        }
    }
}

impl Xerr {
    pub(crate) fn control_flow_error(flow: Option<&Flow>) -> Xresult {
        let flow = flow.ok_or_else(|| {
            let msg = xstr_literal!("unbalanced control flow");
            Xerr::ControlFlowError { msg }
        })?;
        Err(Xerr::unbalanced_flow(&flow))
    }

    pub(crate) fn unbalanced_flow(flow: &Flow) -> Xerr {
        match flow {
            Flow::If { .. } => Self::unbalanced_endif(),
            Flow::Else { .. } => Self::unbalanced_endif(),
            Flow::Begin { .. } => Self::unbalanced_repeat(),
            Flow::While { .. } => Self::unbalanced_repeat(),
            Flow::Leave { .. } => Self::unbalanced_leave(),
            Flow::Case { .. } => Self::unbalanced_endcase(),
            Flow::CaseOf { .. } => Self::unbalanced_endof(),
            Flow::CaseEndOf { .. } => Self::unbalanced_endcase(),
            Flow::Vec { .. } => Self::unbalanced_vec_builder(),
            Flow::TagVec { .. } => Self::unbalanced_tag_vec_builder(),
            Flow::Fun { .. } => Self::unbalanced_fn_builder(),
            Flow::Do { .. } => Self::unbalanced_do(),
        }
    }

    pub(crate) fn conditional_var_definition() -> Xerr {
        let msg = xstr_literal!("variable definition must be unconditional");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn expect_fn_context() -> Xerr {
        let msg = xstr_literal!("has no effect outside of the function control flow");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_fn_builder() -> Xerr {
        let msg = xstr_literal!("balance ; with preceding :");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_vec_builder() -> Xerr {
        let msg = xstr_literal!("unbalanced vector builder");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_tag_vec_builder() -> Xerr {
        let msg = xstr_literal!("unbalanced tag vector builder");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn vec_stack_underflow() -> Xerr {
        let msg = xstr_literal!("vector stack underflow");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_leave() -> Xerr {
        let msg = xstr_literal!("leave used outside of the loop control flow");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_do() -> Xerr {
        let msg = xstr_literal!("balance do with closing loop");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_loop() -> Xerr {
        let msg = xstr_literal!("balance loop with preceding do");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_repeat() -> Xerr {
        let msg = xstr_literal!("balance repeat with preceding begin/while");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_while() -> Xerr {
        let msg = xstr_literal!("balance while with preceding begin");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_until() -> Xerr {
        let msg = xstr_literal!("balance util with preceding begin");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_else() -> Xerr {
        let msg = xstr_literal!("balance else with preceding if");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_endif() -> Xerr {
        let msg = xstr_literal!("balance endif with preceding if/else");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_endcase() -> Xerr {
        let msg = xstr_literal!("balance endcase with preceding case");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_endof() -> Xerr {
        let msg = xstr_literal!("balance endof with preceding of");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_context() -> Xerr {
        Xerr::ErrorMsg(xstr_literal!("unbalanced context"))
    }

    pub(crate) fn const_context() -> Xerr {
        Xerr::ErrorMsg(xstr_literal!(
            "the meta-eval context can operate only with const variables"
        ))
    }

    pub (crate) fn type_not_supported(val: Cell) -> Xerr {
        Xerr::TypeNotSupported { val }
    }
}
pub type Xresult = Xresult1<()>;

pub type Xresult1<T> = Result<T, Xerr>;

pub const OK: Xresult = Ok(());
