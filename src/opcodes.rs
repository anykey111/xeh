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
    LoadI64(i64),
    LoadCell(CellBox),
    Store(usize),
    InitLocal(usize),
    LoadLocal(usize),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    //#[ignore]
    fn test_size() {
        if isize::BITS == 64 {
            assert_eq!(8, std::mem::size_of::<Xstr>());
            assert_eq!(8, std::mem::size_of::<XfnPtr>());
            assert_eq!(16, std::mem::size_of::<Opcode>());
            assert_eq!(16, std::mem::size_of::<Xint>());
        }
    }

}