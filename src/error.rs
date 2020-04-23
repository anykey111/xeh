#[derive(Debug, PartialEq)]
pub enum Xerr {
    UnknownWord,
    InputIncomplete,
    InputParseError,
    IntegerOverflow,
    ControlFlowError,
    StackUnderflow,
}

pub type Xresult = Result<(), Xerr>;

pub const OK: Xresult = Ok(());