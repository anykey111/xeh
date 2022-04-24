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
    LoadF64(f64),
    LoadCell(CellBox),
    Store(usize),
    InitLocal(usize),
    LoadLocal(usize),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn test_size() {
        assert_eq!(8, std::mem::size_of::<Xstr>());
        assert_eq!(8, std::mem::size_of::<XfnPtr>());
        assert_eq!(16, std::mem::size_of::<Opcode>());
        assert_eq!(16, std::mem::size_of::<Xint>());
        assert_eq!(8, std::mem::size_of::<Xreal>());
        assert_eq!(32, std::mem::size_of::<Xcell>());
        assert_eq!(24, std::mem::size_of::<Xvec>());
        assert_eq!(24, std::mem::size_of::<Xbitstr>());
    }

}