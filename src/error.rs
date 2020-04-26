#[derive(Debug, PartialEq)]
pub enum Xerr {
    UnknownWord,
    InputIncomplete,
    InputParseError,
    IntegerOverflow,
    ControlFlowError,
    StackUnderflow,
    NoReturnAddress,
}

pub type Xresult = Result<(), Xerr>;

pub const OK: Xresult = Ok(());