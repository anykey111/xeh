use num_traits::ToPrimitive;

use crate::cell::*;
use crate::error::*;
use crate::hash::*;
use crate::lex::*;

#[derive(Debug)]
pub struct Entry {
    name: String,
    immediate: bool,
    hash: Xhash,
    data: Option<Cell>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Inst {
    Const(usize),
    Call(usize),
    Ret,
    JumpIf(isize),
    JumpIfNot(isize),
    Jump(isize),
    Load(usize),
    Store(usize),
}

#[derive(Clone)]
enum Flow {
    If(usize),
    Begin(usize),
    While(usize),
}

#[derive(Clone, Default)]
pub struct Ctx {
    code: Vec<Inst>,
    ip: usize,
    ds: Vec<Cell>,
    rs: Vec<usize>,
    fs: Vec<Flow>,
}

#[derive(Clone, Default)]
pub struct VM {
    dict: Xvec<Entry>,
    heap: Xvec<Cell>,
    ctx: Ctx,
    source: Lex,
}

impl VM {
    pub fn load(&mut self, source: &str) -> Xresult {
        self.source = Lex::from_str(source);
        self.build(true)
    }

    pub fn interpret(&mut self, source: &str) -> Xresult {
        self.source = Lex::from_str(source);
        self.build(false)
    }

    fn build(&mut self, is_loading: bool) -> Xresult {
        let mut start = self.ctx.code.len();
        loop {
            if !is_loading && !self.has_pending_flow() {
                self.emit(Inst::Ret)?;
                self.finish_building()?;
                self.call_addr(start)?;
                start = self.ctx.code.len();
            }
            match self.source.next()? {
                Tok::EndOfInput => {
                    self.finish_building()?;
                    if start < self.ctx.code.len() {
                        self.emit(Inst::Ret)?;
                        if is_loading {
                            break self.push_data(Cell::InterpFn(start));
                        } else {
                            break self.call_addr(start);
                        }
                    }
                    break OK;
                }
                Tok::Num(n) => {
                    let n = n.to_i64().ok_or(Xerr::IntegerOverflow)?;
                    let a = self.readonly_cell(Cell::Int(n));
                    self.emit(Inst::Const(a))?;
                }
                Tok::Str(s) => {
                    let a = self.readonly_cell(Cell::Str(s));
                    self.emit(Inst::Const(a))?;
                }
                Tok::Word(name) => {
                    let wa = self.insert_word(name);
                    if self.dict[wa].immediate {
                        self.run_immediate(wa)?;
                    } else {
                        self.emit(Inst::Call(wa))?;
                    }
                }
            }
        }
    }

    fn has_pending_flow(&self) -> bool {
        self.ctx.fs.len() > 0
    }

    fn finish_building(&mut self) -> Xresult {
        if self.has_pending_flow() {
            Err(Xerr::ControlFlowError)
        } else {
            OK
        }
    }

    pub fn boot() -> Result<VM, Xerr> {
        let mut vm = VM::default();
        vm.load_core()?;
        Ok(vm)
    }

    fn load_core(&mut self) -> Xresult {
        core_insert_imm_word(self, "if", core_word_if)?;
        core_insert_imm_word(self, "else", core_word_else)?;
        core_insert_imm_word(self, "then", core_word_then)?;
        core_insert_imm_word(self, "begin", core_word_begin)?;
        core_insert_imm_word(self, "while", core_word_while)?;
        core_insert_imm_word(self, "repeat", core_word_repeat)?;
        core_insert_imm_word(self, "until", core_word_until)?;
        OK
    }

    fn insert_word(&mut self, name: String) -> usize {
        if let Some(wa) = self.lookup(&name) {
            wa
        } else {
            let wa = self.dict.len();
            self.dict.push_back_mut(Entry {
                name: name,
                immediate: false,
                hash: Default::default(),
                data: None,
            });
            wa
        }
    }

    fn origin(&self) -> usize {
        self.ctx.code.len()
    }

    fn emit(&mut self, inst: Inst) -> Xresult {
        self.ctx.code.push(inst);
        OK
    }

    fn finish_context(&mut self) -> Xresult {
        if self.ctx.fs.is_empty() {
            OK
        } else {
            Err(Xerr::ControlFlowError)
        }
    }

    fn readonly_cell(&mut self, c: Cell) -> usize {
        if let Some(a) = self.heap.iter().position(|x| x == &c) {
            a
        } else {
            let a = self.heap.len();
            self.heap.push_back_mut(c);
            a
        }
    }

    fn run_immediate(&mut self, wa: usize) -> Xresult {
        let e = self.dict[wa].data.clone().ok_or(Xerr::UnknownWord)?;
        match e {
            Cell::NativeFn(f) => f.0(self),
            Cell::InterpFn(_) => todo!("immediate interpreted function"),
            other => panic!("invalid immediate function {:?}", other),
        }
    }

    fn run1(&mut self) -> Xresult {
        let ip = self.ctx.ip;
        match self.ctx.code[ip] {
            Inst::Jump(offs) => self.jump_to(offs),
            Inst::JumpIf(offs) => {
                let t = self.pop_data()? != ZERO;
                self.jump_if(t, offs)
            }
            Inst::JumpIfNot(offs) => {
                let t = self.pop_data()? == ZERO;
                self.jump_if(t, offs)
            }
            Inst::Const(data_index) => {
                let val = self.heap[data_index].clone();
                self.push_data(val)?;
                self.next_ip()
            }
            Inst::Call(a) => todo!("call inst"),
            Inst::Ret => {
                let ret_addr = self.ctx.rs.pop().ok_or(Xerr::NoReturnAddress)?;
                self.ctx.ip = ret_addr;
                OK
            }
            Inst::Load(a) => todo!("load inst"),
            Inst::Store(a) => todo!("store inst"),
        }
    }

    fn jump_to(&mut self, offs: isize) -> Xresult {
        let old_ip = self.ctx.ip;
        let new_ip = (old_ip as isize + offs) as usize;
        self.ctx.ip = new_ip;
        OK
    }

    fn jump_if(&mut self, t: bool, offs: isize) -> Xresult {
        if t {
            self.jump_to(offs)
        } else {
            self.next_ip()
        }
    }

    fn call_addr(&mut self, addr: usize) -> Xresult {
        let ip = self.ctx.ip + 1;
        self.ctx.rs.push(ip);
        self.ctx.ip = addr;
        self.run1()
    }

    fn next_ip(&mut self) -> Xresult {
        self.ctx.ip += 1;
        OK
    }

    fn patch_jump(&mut self, at: usize, offs: isize) -> Xresult {
        match &mut self.ctx.code[at] {
            Inst::Jump(ref mut a) => *a = offs,
            Inst::JumpIf(ref mut a) => *a = offs,
            Inst::JumpIfNot(ref mut a) => *a = offs,
            other => panic!("not a jump instruction {:?}", other),
        }
        OK
    }

    fn pop_flow(&mut self) -> Result<Flow, Xerr> {
        self.ctx.fs.pop().ok_or(Xerr::ControlFlowError)
    }

    fn push_flow(&mut self, flow: Flow) {
        self.ctx.fs.push(flow);
    }

    pub fn lookup(&mut self, name: &str) -> Option<usize> {
        self.dict.iter().position(|x| x.name == name)
    }

    pub fn push_data(&mut self, data: Cell) -> Xresult {
        self.ctx.ds.push(data);
        OK
    }

    pub fn pop_data(&mut self) -> Result<Cell, Xerr> {
        self.ctx.ds.pop().ok_or(Xerr::StackUnderflow)
    }

    pub fn top_data(&mut self) -> Result<&Cell, Xerr> {
        self.ctx.ds.last().ok_or(Xerr::StackUnderflow)
    }
}

fn core_insert_imm_word(vm: &mut VM, name: &str, f: XfnType) -> Xresult {
    if let Some(_) = vm.lookup(name) {
        panic!("core word duplication {:?}", name);
    }
    vm.dict.push_back_mut(Entry {
        name: name.to_string(),
        immediate: true,
        hash: Xhash::from(f),
        data: Some(Cell::NativeFn(Xfn(f))),
    });
    OK
}

fn core_word_if(vm: &mut VM) -> Xresult {
    let fwd = Flow::If(vm.origin());
    vm.emit(Inst::JumpIfNot(0))?;
    vm.push_flow(fwd);
    OK
}

fn core_word_else(vm: &mut VM) -> Xresult {
    match vm.pop_flow()? {
        Flow::If(if_org) => {
            let fwd = Flow::If(vm.origin());
            vm.emit(Inst::Jump(0))?;
            vm.push_flow(fwd);
            let offs = jump_offset(if_org, vm.origin());
            vm.patch_jump(if_org, offs)
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_then(vm: &mut VM) -> Xresult {
    match vm.pop_flow()? {
        Flow::If(if_org) => {
            let offs = jump_offset(if_org, vm.origin());
            vm.patch_jump(if_org, offs)
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_begin(vm: &mut VM) -> Xresult {
    vm.push_flow(Flow::Begin(vm.origin()));
    OK
}

fn core_word_until(vm: &mut VM) -> Xresult {
    match vm.pop_flow()? {
        Flow::Begin(begin_org) => {
            let offs = jump_offset(vm.origin(), begin_org);
            vm.emit(Inst::JumpIf(offs))
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_while(vm: &mut VM) -> Xresult {
    let cond = Flow::While(vm.origin());
    vm.emit(Inst::JumpIfNot(0))?;
    vm.push_flow(cond);
    OK
}

fn core_word_repeat(vm: &mut VM) -> Xresult {
    match vm.pop_flow()? {
        Flow::Begin(begin_org) => {
            let offs = jump_offset(vm.origin(), begin_org);
            vm.emit(Inst::Jump(offs))
        }
        Flow::While(cond_org) => match vm.pop_flow()? {
            Flow::Begin(begin_org) => {
                let offs = jump_offset(cond_org, vm.origin());
                vm.patch_jump(cond_org, offs)?;
                let offs = jump_offset(vm.origin(), begin_org);
                vm.emit(Inst::Jump(offs))
            }
            _ => Err(Xerr::ControlFlowError),
        },
        _ => Err(Xerr::ControlFlowError),
    }
}

fn jump_offset(origin: usize, dest: usize) -> isize {
    if origin > dest {
        -((origin - dest) as isize)
    } else {
        (dest - origin) as isize
    }
}

#[test]
fn test_jump_offset() {
    assert_eq!(2, jump_offset(2, 4));
    assert_eq!(-2, jump_offset(4, 2));
}

#[test]
fn test_if_flow() {
    let mut vm = VM::boot().unwrap();
    vm.load("1 if 222 then").unwrap();
    let mut it = vm.ctx.code.iter();
    it.next().unwrap();
    assert_eq!(&Inst::JumpIfNot(2), it.next().unwrap());
    let mut vm = VM::boot().unwrap();
    vm.load("1 if 222 else 333 then").unwrap();
    let mut it = vm.ctx.code.iter();
    it.next().unwrap();
    assert_eq!(&Inst::JumpIfNot(3), it.next().unwrap());
    it.next().unwrap();
    assert_eq!(&Inst::Jump(2), it.next().unwrap());
    // test errors
    let mut vm = VM::boot().unwrap();
    assert_eq!(Err(Xerr::ControlFlowError), vm.load("1 if 222 else 333"));
    let mut vm = VM::boot().unwrap();
    assert_eq!(Err(Xerr::ControlFlowError), vm.load("1 if 222 else"));
    let mut vm = VM::boot().unwrap();
    assert_eq!(Err(Xerr::ControlFlowError), vm.load("1 if 222"));
    let mut vm = VM::boot().unwrap();
    assert_eq!(Err(Xerr::ControlFlowError), vm.load("1 else 222 then"));
    assert_eq!(Err(Xerr::ControlFlowError), vm.load("else 222 if"));
}

#[test]
fn test_begin_repeat() {
    let mut vm = VM::boot().unwrap();
    vm.load("begin 5 while 1 - repeat").unwrap();
    let mut it = vm.ctx.code.iter();
    it.next().unwrap();
    assert_eq!(&Inst::JumpIfNot(3), it.next().unwrap());
    it.next().unwrap();
    it.next().unwrap();
    assert_eq!(&Inst::Jump(-4), it.next().unwrap());
    let mut vm = VM::boot().unwrap();
    vm.load("begin leave repeat").unwrap();
    let mut it = vm.ctx.code.iter();
    it.next().unwrap();
    assert_eq!(&Inst::Jump(-1), it.next().unwrap());
    let mut vm = VM::boot().unwrap();
    vm.load("0 begin 1 + until");
    let mut it = vm.ctx.code.iter();
    it.next().unwrap();
    it.next().unwrap();
    it.next().unwrap();
    assert_eq!(&Inst::JumpIf(-2), it.next().unwrap());
    assert_eq!(Err(Xerr::ControlFlowError), vm.load("if begin then repeat"));
    assert_eq!(Err(Xerr::ControlFlowError), vm.load("repeat begin"));
    assert_eq!(Err(Xerr::ControlFlowError), vm.load("begin then while"));
    assert_eq!(Err(Xerr::ControlFlowError), vm.load("until begin"));
    assert_eq!(Err(Xerr::ControlFlowError), vm.load("begin repeat until"));
    assert_eq!(Err(Xerr::ControlFlowError), vm.load("begin until repeat"));
}

