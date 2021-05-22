use crate::cell::*;

#[derive(Clone, PartialEq, Debug)]
pub enum Opcode {
    Call(usize),
    Deferred(usize),
    NativeCall(XfnPtr),
    Ret,
    JumpIf(isize),
    JumpIfNot(isize),
    Jump(isize),
    For(isize),
    Break(isize),
    Loop(isize),
    CaseOf(isize),
    Load(usize),
    LoadNil,
    LoadInt(Xint),
    Store(usize),
    InitLocal(usize),
    LoadLocal(usize),
}
