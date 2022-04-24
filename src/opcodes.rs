use crate::cell::*;

pub type CellBox = std::rc::Rc<Cell>;


#[derive(Clone, Copy, PartialEq, Debug)]
pub struct RelativeJump(i32);

impl RelativeJump {
    pub fn from_to(origin: usize, dest: usize) -> Self {
        let i = if origin > dest {
            -((origin - dest) as isize)
        } else {
            (dest - origin) as isize
        };
        Self(i as i32)
    }

    pub fn uninit() -> Self {
        RelativeJump(0)
    }

    pub fn calculate(&self, ip: usize) -> usize {
        (ip as isize + self.0 as isize).max(0) as usize
    }

    #[cfg(test)]
    pub fn from_i32(i: i32) -> Self {
        RelativeJump(i)
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Opcode {
    Call(usize),
    Resolve(Xstr),
    NativeCall(XfnPtr),
    Ret,
    JumpIf(RelativeJump),
    JumpIfNot(RelativeJump),
    Jump(RelativeJump),
    Do(RelativeJump),
    Break(RelativeJump),
    Loop(RelativeJump),
    CaseOf(RelativeJump),
    Load(CellRef),
    LoadNil,
    LoadI64(i64),
    LoadF64(f64),
    LoadCell(CellBox),
    Store(CellRef),
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


    #[test]
    fn test_jump_offset() {
        assert_eq!(RelativeJump(2), RelativeJump::from_to(2, 4));
        assert_eq!(RelativeJump(-2), RelativeJump::from_to(4, 2));
    }

}