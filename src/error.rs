use crate::cell::*;
use crate::state::Flow;

use std::ops::Range;
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
    IOError {
        filename: Xstr,
        reason: Xstr,
    },
    OutOfBounds {
        index: Xint,
        range: Range<usize>,
    },
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
    UserError(Cell),
    // Stop interpreter execution
    Exit(isize),
}

pub(crate) const ASSERT_MSG: Cell = xeh_str_lit!("assert.msg");

fn assert_get_msg(a: &Cell) -> Option<&str> {
    a.get_tag(&ASSERT_MSG)?.str().ok()
}

impl fmt::Display for Xerr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Debug;
        match self {
            Xerr::ErrorMsg(s) => f.write_str(s),
            Xerr::UserError(err_value)  => err_value.fmt(f),
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
                "found {}, expected {}\n{:?}",
                val.type_name(),
                msg,
                val
            ),
            Xerr::ExpectingName => f.write_str("expecting a word name"),
            Xerr::ExpectingLiteral => f.write_str("expecting literal value"),
            Xerr::IOError { filename, reason } => write!(f, "{}: {}", filename, reason),
            Xerr::OutOfBounds { index, range } =>
                write!(f, "index {} out of bounds {:?}", index, range),
            Xerr::AssertFailed => f.write_str("assertion failed: false"),
            Xerr::AssertEqFailed { a, b } => {
                let msg = assert_get_msg(&a).or_else(|| assert_get_msg(&b));
                writeln!(f, "assertion failed: {}", msg.unwrap_or("not equals"))?;
                writeln!(f, "{:?}", a)?;
                write!(f, "{:?}", b)
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
            let msg = xeh_xstr!("unbalanced control flow");
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
            Flow::Break { .. } => Self::unbalanced_break(),
            Flow::Case { .. } => Self::unbalanced_endcase(),
            Flow::CaseOf { .. } => Self::unbalanced_endof(),
            Flow::CaseEndOf { .. } => Self::unbalanced_endcase(),
            Flow::Vec { .. } => Self::unbalanced_vec_builder(),
            Flow::Map { .. } => Self::unbalanced_map_builder(),
            Flow::Tags { .. } => Self::unbalanced_tag_map_builder(),
            Flow::Fun { .. } => Self::unbalanced_fn_builder(),
            Flow::Do { .. } => Self::unbalanced_do(),
        }
    }

    pub(crate) fn conditional_var_definition() -> Xerr {
        let msg = xeh_xstr!("variable definition must be unconditional");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn expect_fn_context() -> Xerr {
        let msg = xeh_xstr!("has no effect outside of the function control flow");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn let_expect_key_lit() -> Xerr {
        Xerr::ExpectingLiteral
    }

    pub(crate) fn let_name_or_lit() -> Xerr {
        Xerr::ErrorMsg(xeh_xstr!("expecting name or literal"))
    }

    pub(crate) fn unbalanced_fn_builder() -> Xerr {
        let msg = xeh_xstr!("balance ; with preceding :");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_vec_builder() -> Xerr {
        let msg = xeh_xstr!("unbalanced vector builder");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_map_builder() -> Xerr {
        let msg = xeh_xstr!("unbalanced map builder");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_tag_map_builder() -> Xerr {
        let msg = xeh_xstr!("unbalanced tag vector builder");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn vec_stack_underflow() -> Xerr {
        let msg = xeh_xstr!("vector stack underflow");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn map_stack_underflow() -> Xerr {
        let msg = xeh_xstr!("map stack underflow");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn map_missing_key() -> Xerr {
        let msg = xeh_xstr!("missing key element");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_break() -> Xerr {
        let msg = xeh_xstr!("`break` used outside of the loop control flow");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_do() -> Xerr {
        let msg = xeh_xstr!("balance do with closing loop");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_loop() -> Xerr {
        let msg = xeh_xstr!("balance loop with preceding do");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_repeat() -> Xerr {
        let msg = xeh_xstr!("balance repeat with preceding begin/while");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_while() -> Xerr {
        let msg = xeh_xstr!("balance while with preceding begin");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_until() -> Xerr {
        let msg = xeh_xstr!("balance util with preceding begin");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_else() -> Xerr {
        let msg = xeh_xstr!("balance else with preceding if");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_endif() -> Xerr {
        let msg = xeh_xstr!("balance endif with preceding if/else");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_endcase() -> Xerr {
        let msg = xeh_xstr!("balance endcase with preceding case");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_endof() -> Xerr {
        let msg = xeh_xstr!("balance endof with preceding of");
        Xerr::ControlFlowError { msg }
    }

    pub(crate) fn unbalanced_context() -> Xerr {
        Xerr::ErrorMsg(xeh_xstr!("unbalanced context"))
    }

    pub(crate) fn const_context() -> Xerr {
        Xerr::ErrorMsg(xeh_xstr!(
            "the meta-eval context can operate only with constants"
        ))
    }

    pub(crate) fn out_of_bounds(idx: usize, len: usize) -> Xerr {
        Xerr::OutOfBounds {
            index: idx as Xint,
            range: 0..len
        }
    }

    pub(crate) fn out_of_bounds_rel(ridx: isize, len: usize) -> Xerr {
        Xerr::OutOfBounds {
            index: ridx as Xint,
            range: 0..len
        }
    }

    pub(crate) fn out_of_range(idx: usize, range: Range<usize>) -> Xerr {
        Xerr::OutOfBounds { index: idx as Xint, range }
    }

    pub(crate) fn cell_out_of_bounds(cref: CellRef) -> Xerr {
        let idx = cref.index();
        Xerr::ErrorMsg(Xstr::from(format!("heap address {:#x} out of bounds", idx)))
    }

    pub(crate) fn local_out_of_bounds(idx: usize) -> Xerr {
        Xerr::ErrorMsg(Xstr::from(format!("local variable index {:#} out of bounds", idx)))
    }

    pub (crate) fn type_not_supported(val: Cell) -> Xerr {
        Xerr::TypeNotSupported { val }
    }
}
pub type Xresult = Xresult1<()>;

pub type Xresult1<T> = Result<T, Xerr>;

pub const OK: Xresult = Ok(());

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cell::Cell;
    
    #[test]
    fn test_assert_eq() {
        let msg = Xstr::from(xeh_xstr!("test1"));
        let a = ONE.insert_tag(ASSERT_MSG, Cell::Str(msg));
        let err = Xerr::AssertEqFailed { a , b: ZERO};
        assert_eq!("assertion failed: test1\n1\n0", format!("{}", err));
    }
    
}