use crate::cell::*;

#[derive(Clone, PartialEq, Debug)]
pub enum Opcode {
    Nop,
    Next,
    Call(usize),
    Deferred(usize),
    NativeCall(XfnPtr),
    Ret,
    JumpIf(isize),
    JumpIfNot(isize),
    Jump(isize),
    Load(usize),
    LoadNil,
    LoadInt(Xint),
    LoadRef(Xref),
    Store(usize),
    InitLocal(usize),
    LoadLocal(usize),
}
