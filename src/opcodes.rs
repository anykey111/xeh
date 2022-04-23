use crate::cell::*;

pub type CellBox = std::rc::Rc<Cell>;

#[derive(Clone, PartialEq, Debug)]
pub enum Opcode {
    Call(usize),
    Resolve(Xstr),
    NativeCall(XfnPtr),
    Ret,
    JumpIf(isize),
    JumpIfNot(isize),
    Jump(isize),
    Do(isize),
    Break(isize),
    Loop(isize),
    CaseOf(isize),
    Load(usize),
    LoadNil,
    LoadInt(Xint),
    LoadCell(CellBox),
    Store(usize),
    InitLocal(usize),
    LoadLocal(usize),
}
