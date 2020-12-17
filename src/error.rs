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
    InvalidAddress,
    ReadonlyAddress,
    IOError,
    OutOfBounds,
    DebugAssertion,
    InternalError,
    // bitstring errors
    OutOfRange,
    BinaryMatchError,
    // return to interpreter loop
    Next,
}

pub type Xresult = Xresult1<()>;

pub type Xresult1<T> = Result<T, Xerr>;

pub const OK: Xresult = Ok(());
