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
    BinaryMatchError,
    UnalignedBitstr,
    // return to interpreter loop
    DebugBreak,
}

pub type Xresult = Xresult1<()>;

pub type Xresult1<T> = Result<T, Xerr>;

pub const OK: Xresult = Ok(());
