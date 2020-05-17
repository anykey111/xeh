#[derive(Debug, PartialEq)]
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
    CollectionError,
    StackNotBalanced,
    TypeError,
    RecusriveDefinition,
    ExpectingName,
    NotAnExecutable,
    InvalidAddress,
    ReadonlyAddress,
    CustomError,
}

pub type Xresult = Result<(), Xerr>;

pub const OK: Xresult = Ok(());
