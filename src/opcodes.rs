use crate::cell::*;

#[derive(Clone)]
pub enum Opcode {
    Nop,
    Next,
    Call(usize),
    Deferred(usize),
    NativeCall(XfnType),
    Ret,
    JumpIf(isize),
    JumpIfNot(isize),
    Jump(isize),
    Load(usize),
    LoadInt(Xint),
    LoadRef(usize),
    Store(usize),
    InitLocal(usize),
    LoadLocal(usize),
}

use std::fmt;

impl fmt::Debug for Opcode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Nop => write!(f, "Nop"),
            Self::Next => write!(f, "Next"),
            Self::Call(a) => write!(f, "Call({})", a),
            Self::Deferred(a) => write!(f, "Deferred({})", a),
            Self::NativeCall(x) => write!(f, "NativeCall({})", *x as usize),
            Self::Ret => write!(f, "Ret"),
            Self::JumpIf(offs) => write!(f, "JumpIf({})", offs),
            Self::JumpIfNot(offs) => write!(f, "JumpIfNot({})", offs),
            Self::Jump(offs) => write!(f, "Jump({})", offs),
            Self::Load(a) => write!(f, "Load({})", a),
            Self::LoadRef(a) => write!(f, "LoadRef({})", a),
            Self::LoadInt(i) => write!(f, "LoadInt({})", i),
            Self::Store(a) => write!(f, "Store({})", a),
            Self::InitLocal(i) => write!(f, "InitLocal({})", i),
            Self::LoadLocal(i) => write!(f, "LoadLocal({})", i),
        }
    }
}

impl PartialEq for Opcode {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Nop, Self::Nop) => true,
            (Self::Call(a), Self::Call(b)) => a == b,
            (Self::Deferred(a), Self::Deferred(b)) => a == b,
            (Self::NativeCall(a), Self::NativeCall(b)) => *a as usize == *b as usize,
            (Self::Ret, Self::Ret) => true,
            (Self::JumpIf(a), Self::JumpIf(b)) => a == b,
            (Self::JumpIfNot(a), Self::JumpIfNot(b)) => a == b,
            (Self::Jump(a), Self::Jump(b)) => a == b,
            (Self::Load(a), Self::Load(b)) => a == b,
            (Self::LoadRef(a), Self::LoadRef(b)) => a == b,
            (Self::LoadInt(a), Self::LoadInt(b)) => a == b,
            (Self::Store(a), Self::Store(b)) => a == b,
            _ => false,
        }
    }
}
