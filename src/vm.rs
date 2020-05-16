use num_traits::ToPrimitive;

use crate::cell::*;
use crate::error::*;
use crate::lex::*;

#[derive(Debug, Clone, PartialEq)]
enum Entry {
    Deferred,
    Variable(usize),
    Function { immediate: bool, xf: Xfn },
}

#[derive(Clone)]
pub enum Inst {
    Nop,
    Call(usize),
    Deferred(usize),
    NativeCall(XfnType),
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
    Leave(usize),
    Vec,
    Map,
    Fun { dict_idx: usize, start: usize },
}

#[derive(Clone)]
enum Loop {
    VecBuilder { stack_ptr: usize },
    MapBuilder { stack_ptr: usize },
}


#[derive(Clone, Default)]
struct CtxState {
    ds_len: usize,
    cs_len: usize,
    rs_len: usize,
    fs_len: usize,
    ls_len: usize,
    autoexec: bool,
}

#[derive(Clone, Default)]
struct Ctx {
    data_stack: Vec<Cell>,
    return_stack: Vec<usize>,
    flow_stack: Vec<Flow>,
    loops: Vec<Loop>,
    autoexec: bool,
}

#[derive(Clone, Default)]
pub struct VM {
    dict: Vec<(String, Entry)>,
    heap: Vec<Cell>,
    code: Vec<Inst>,
    ip: usize,
    ctx: Ctx,
    ctx_nested:  Vec<CtxState>,
    source: Lex,
}

impl VM {
    pub fn load(&mut self, source: &str) -> Xresult {
        self.source = Lex::from_str(source);
        self.build(false)
    }

    pub fn interpret(&mut self, source: &str) -> Xresult {
        self.source = Lex::from_str(source);
        self.build(true)
    }

    fn build(&mut self, autoexec: bool) -> Xresult {
        let mut start = self.code_offset();
        loop {
            if autoexec && !self.is_building() && start < self.code_offset() {
                self.code_emit(Inst::Ret)?;
                self.finish_building()?;
                self.run(Xfn::Interp(start))?;
                start = self.code_offset();
            }
            match self.source.next()? {
                Tok::EndOfInput => {
                    self.finish_building()?;
                    if start < self.code_offset() {
                        self.code_emit(Inst::Ret)?;
                        let xf = Xfn::Interp(start);
                        if autoexec {
                            break self.run(xf);
                        } else {
                            break self.push_data(Cell::Fun(xf));
                        }
                    }
                    break OK;
                }
                Tok::Num(n) => {
                    let n = n.to_i64().ok_or(Xerr::IntegerOverflow)?;
                    let a = self.readonly_cell(Cell::Int(n));
                    self.code_emit(Inst::Load(a))?;
                }
                Tok::Str(s) => {
                    let a = self.readonly_cell(Cell::Str(s));
                    self.code_emit(Inst::Load(a))?;
                }
                Tok::Word(name) => {
                    // get entry address or insert deferred
                    let idx = if let Some(idx) = self.dict_find(&name) {
                        idx
                    } else {
                        self.dict_insert(name, Entry::Deferred)?
                    };
                    match self.dict_at(idx).unwrap() {
                        Entry::Deferred => self.code_emit(Inst::Deferred(idx))?,
                        Entry::Variable(a) => {
                            let a = *a;
                            self.code_emit(Inst::Load(a))?;
                        }
                        Entry::Function {
                            immediate: true,
                            xf,
                        } => {
                            let xf = xf.clone();
                            self.run(xf)?;
                        }
                        Entry::Function {
                            immediate: false,
                            xf: Xfn::Interp(x),
                        } => {
                            let x = *x;
                            self.code_emit(Inst::Call(x))?;
                        }
                        Entry::Function {
                            immediate: false,
                            xf: Xfn::Native(x),
                        } => {
                            let x = *x;
                            self.code_emit(Inst::NativeCall(x))?;
                        }
                    }
                }
            }
        }
    }

    fn is_immediate(&self) -> bool {
        self.ctx_nested.last().map(|s| s.autoexec).unwrap_or(false) 
    }

    fn is_building(&self) -> bool {
        self.has_pending_flow() || self.ctx_nested.is_empty()
    }

    fn has_pending_flow(&self) -> bool {
        self.ctx.flow_stack.len() > 0
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

    pub fn defvar(&mut self, name: &str, value: Cell) -> Xresult {
        let a = self.alloc_cell()?;
        self.heap[a] = value;
        self.dict_insert(name.to_string(), Entry::Variable(a))?;
        OK
    }

    pub fn defword(&mut self, name: &str, x: XfnType) -> Xresult {
        let xf = Xfn::Native(x);
        self.dict_insert(
            name.to_string(),
            Entry::Function {
                immediate: false,
                xf,
            },
        )?;
        OK
    }

    fn load_core(&mut self) -> Xresult {
        core_insert_imm_word(self, "if", core_word_if)?;
        core_insert_imm_word(self, "else", core_word_else)?;
        core_insert_imm_word(self, "then", core_word_then)?;
        core_insert_imm_word(self, "begin", core_word_begin)?;
        core_insert_imm_word(self, "while", core_word_while)?;
        core_insert_imm_word(self, "repeat", core_word_repeat)?;
        core_insert_imm_word(self, "until", core_word_until)?;
        core_insert_imm_word(self, "leave", core_word_leave)?;
        core_insert_imm_word(self, "again", core_word_again)?;
        core_insert_imm_word(self, "[", core_word_vec_begin)?;
        core_insert_imm_word(self, "]", core_word_vec_end)?;
        core_insert_imm_word(self, "{", core_word_map_begin)?;
        core_insert_imm_word(self, "}", core_word_map_end)?;
        core_insert_imm_word(self, ":", core_word_def_begin)?;
        core_insert_imm_word(self, ";", core_word_def_end)?;
        core_insert_imm_word(self, "var", core_word_var)?;
        core_insert_imm_word(self, "->", core_word_setvar)?;
        core_insert_imm_word(self, "const", core_word_const)?;
        core_insert_imm_word(self, "(", core_word_nested_begin)?;
        core_insert_imm_word(self, ")", core_word_nested_end)?;
        OK
    }

    fn dict_insert(&mut self, name: String, e: Entry) -> Result<usize, Xerr> {
        let wa = self.dict.len();
        self.dict.push((name, e));
        Ok(wa)
    }

    pub fn dict_find(&self, name: &str) -> Option<usize> {
        self.dict.iter().rposition(|x| x.0 == name)
    }

    fn dict_at(&self, idx: usize) -> Option<&Entry> {
        self.dict.get(idx).map(|x| &x.1)
    }

    fn code_offset(&self) -> usize {
        self.code.len()
    }

    fn code_emit(&mut self, inst: Inst) -> Xresult {
        self.code.push(inst);
        OK
    }

    fn patch_insn(&mut self, at: usize, insn: Inst) -> Xresult {
        self.code[at] = insn;
        OK
    }

    fn patch_jump(&mut self, at: usize, offs: isize) -> Xresult {
        let insn = match &self.code[at] {
            Inst::Jump(_) => Inst::Jump(offs),
            Inst::JumpIf(_) => Inst::JumpIf(offs),
            Inst::JumpIfNot(_) => Inst::JumpIfNot(offs),
            _ => panic!("not a jump instruction at={}", at),
        };
        self.patch_insn(at, insn)
    }

    fn alloc_cell(&mut self) -> Result<usize, Xerr> {
        let a = self.heap.len();
        self.heap.push(Cell::Nil);
        Ok(a)
    }

    fn readonly_cell(&mut self, c: Cell) -> usize {
        let a = self.heap.len();
        self.heap.push(c);
        a
    }

    fn run(&mut self, x: Xfn) -> Xresult {
        match x {
            Xfn::Native(x) => x(self),
            Xfn::Interp(x) => {
                let old_ip = self.ip;
                let depth = self.ctx.return_stack.len();
                self.push_return(old_ip)?;
                self.set_ip(x)?;
                loop {
                    self.run_inst()?;
                    if depth == self.ctx.return_stack.len() {
                        assert_eq!(old_ip, self.ip);
                        break OK;
                    }
                }
            }
        }
    }

    fn run_inst(&mut self) -> Xresult {
        let ip = self.ip;
        match self.code[ip] {
            Inst::Nop => self.next_ip(),
            Inst::Jump(offs) => self.jump_to(offs),
            Inst::JumpIf(offs) => {
                let t = self.pop_data()?;
                self.jump_if(t.is_true(), offs)
            }
            Inst::JumpIfNot(offs) => {
                let t = self.pop_data()?;
                self.jump_if(!t.is_true(), offs)
            }
            Inst::Call(a) => {
                self.push_return(ip + 1)?;
                self.set_ip(a)
            }
            Inst::Deferred(idx) => match self.dict_at(idx).ok_or(Xerr::UnknownWord)? {
                Entry::Deferred => Err(Xerr::UnknownWord),
                Entry::Variable(a) => {
                    let a = *a;
                    self.patch_insn(ip, Inst::Load(a))
                }
                Entry::Function {
                    xf: Xfn::Interp(x), ..
                } => {
                    let x = *x;
                    self.patch_insn(ip, Inst::Call(x))
                }
                Entry::Function {
                    xf: Xfn::Native(x), ..
                } => {
                    let x = *x;
                    self.patch_insn(ip, Inst::NativeCall(x))
                }
            },
            Inst::NativeCall(x) => {
                x(self)?;
                self.next_ip()
            }
            Inst::Ret => {
                let new_ip = self.pop_return()?;
                self.set_ip(new_ip)
            }
            Inst::Load(a) => {
                let val = self.heap[a].clone();
                self.push_data(val)?;
                self.next_ip()
            }
            Inst::Store(a) => {
                let val = self.pop_data()?;
                self.heap[a] = val;
                self.next_ip()
            }
        }
    }

    fn jump_to(&mut self, offs: isize) -> Xresult {
        let new_ip = (self.ip as isize + offs) as usize;
        self.ip = new_ip;
        OK
    }

    fn jump_if(&mut self, t: bool, offs: isize) -> Xresult {
        if t {
            self.jump_to(offs)
        } else {
            self.next_ip()
        }
    }

    fn set_ip(&mut self, new_ip: usize) -> Xresult {
        self.ip = new_ip;
        OK
    }

    fn next_ip(&mut self) -> Xresult {
        self.ip += 1;
        OK
    }

    fn pop_flow(&mut self) -> Result<Flow, Xerr> {
        self.ctx.flow_stack.pop().ok_or(Xerr::ControlFlowError)
    }

    fn push_flow(&mut self, flow: Flow) -> Xresult {
        self.ctx.flow_stack.push(flow);
        OK
    }

    fn dropn(&mut self, len: usize) -> Xresult {
        let ds_len = self.ctx.data_stack.len();
        if ds_len < len {
            Err(Xerr::StackUnderflow)
        } else {
            self.ctx.data_stack.truncate(ds_len - len);
            OK
        }
    }

    pub fn push_data(&mut self, data: Cell) -> Xresult {
        self.ctx.data_stack.push(data);
        OK
    }

    pub fn pop_data_typed(&mut self) -> Result<Cell, Xerr> {
        todo!("wof!")
    }

    pub fn pop_data(&mut self) -> Result<Cell, Xerr> {
        let frozen_len = self.ctx_nested.last().map(|s| s.ds_len).unwrap_or(0);
        if self.ctx.data_stack.len() <= frozen_len {
            return Err(Xerr::StackUnderflow);
        }
        self.ctx.data_stack.pop().ok_or(Xerr::StackUnderflow)
    }

    pub fn top_data(&mut self) -> Option<&Cell> {
        self.ctx.data_stack.last()
    }

    fn push_return(&mut self, return_to: usize) -> Xresult {
        self.ctx.return_stack.push(return_to);
        OK
    }

    fn pop_return(&mut self) -> Result<usize, Xerr> {
        let frozen_len = self.ctx_nested.last().map(|s| s.rs_len).unwrap_or(0);
        if self.ctx.return_stack.len() <= frozen_len {
            return Err(Xerr::ReturnStackUnderflow);
        }
        self.ctx.return_stack.pop().ok_or(Xerr::ReturnStackUnderflow)
    }

    fn push_loop(&mut self, l: Loop) -> Xresult {
        self.ctx.loops.push(l);
        OK
    }

    fn pop_loop(&mut self) -> Result<Loop, Xerr> {
        let frozen_len = self.ctx_nested.last().map(|s| s.ls_len).unwrap_or(0);
        if self.ctx.loops.len() <= frozen_len {
            return Err(Xerr::ReturnStackUnderflow);
        }
        self.ctx.loops.pop().ok_or(Xerr::LoopStackUnderflow)
    }
}

fn core_insert_imm_word(vm: &mut VM, name: &str, x: XfnType) -> Xresult {
    vm.dict_insert(
        name.to_string(),
        Entry::Function {
            immediate: true,
            xf: Xfn::Native(x),
        },
    )?;
    OK
}

fn core_word_if(vm: &mut VM) -> Xresult {
    let fwd = Flow::If(vm.code_offset());
    vm.code_emit(Inst::JumpIfNot(0))?;
    vm.push_flow(fwd)
}

fn core_word_else(vm: &mut VM) -> Xresult {
    match vm.pop_flow()? {
        Flow::If(if_org) => {
            let fwd = Flow::If(vm.code_offset());
            vm.code_emit(Inst::Jump(0))?;
            vm.push_flow(fwd)?;
            let offs = jump_offset(if_org, vm.code_offset());
            vm.patch_jump(if_org, offs)
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_then(vm: &mut VM) -> Xresult {
    match vm.pop_flow()? {
        Flow::If(if_org) => {
            let offs = jump_offset(if_org, vm.code_offset());
            vm.patch_jump(if_org, offs)
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_begin(vm: &mut VM) -> Xresult {
    vm.push_flow(Flow::Begin(vm.code_offset()))
}

fn core_word_until(vm: &mut VM) -> Xresult {
    match vm.pop_flow()? {
        Flow::Begin(begin_org) => {
            let offs = jump_offset(vm.code_offset(), begin_org);
            vm.code_emit(Inst::JumpIf(offs))
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_while(vm: &mut VM) -> Xresult {
    let cond = Flow::While(vm.code_offset());
    vm.code_emit(Inst::JumpIfNot(0))?;
    vm.push_flow(cond)
}

fn core_word_again(vm: &mut VM) -> Xresult {
    loop {
        match vm.pop_flow()? {
            Flow::Leave(leave_org) => {
                let offs = jump_offset(leave_org, vm.code_offset() + 1);
                vm.patch_jump(leave_org, offs)?;
            }
            Flow::Begin(begin_org) => {
                let offs = jump_offset(vm.code_offset(), begin_org);
                break vm.code_emit(Inst::Jump(offs));
            }
            _ => break Err(Xerr::ControlFlowError),
        }
    }
}

fn core_word_repeat(vm: &mut VM) -> Xresult {
    loop {
        match vm.pop_flow()? {
            Flow::Leave(leave_org) => {
                let offs = jump_offset(leave_org, vm.code_offset() + 1);
                vm.patch_jump(leave_org, offs)?;
            }
            Flow::While(cond_org) => match vm.pop_flow()? {
                Flow::Begin(begin_org) => {
                    let offs = jump_offset(cond_org, vm.code_offset());
                    vm.patch_jump(cond_org, offs)?;
                    let offs = jump_offset(vm.code_offset(), begin_org);
                    break vm.code_emit(Inst::Jump(offs));
                }
                _ => break Err(Xerr::ControlFlowError),
            },
            _ => break Err(Xerr::ControlFlowError),
        }
    }
}

fn core_word_leave(vm: &mut VM) -> Xresult {
    let leave = Flow::Leave(vm.code_offset());
    vm.code_emit(Inst::Jump(0))?;
    vm.push_flow(leave)?;
    OK
}

fn jump_offset(origin: usize, dest: usize) -> isize {
    if origin > dest {
        -((origin - dest) as isize)
    } else {
        (dest - origin) as isize
    }
}

fn core_word_vec_begin(vm: &mut VM) -> Xresult {
    vm.push_flow(Flow::Vec)?;
    vm.code_emit(Inst::NativeCall(vec_builder_begin))
}

fn core_word_vec_end(vm: &mut VM) -> Xresult {
    match vm.pop_flow()? {
        Flow::Vec => vm.code_emit(Inst::NativeCall(vec_builder_end)),
        _ => Err(Xerr::ControlFlowError),
    }
}

fn vec_builder_begin(vm: &mut VM) -> Xresult {
    let stack_ptr = vm.ctx.data_stack.len();
    vm.push_loop(Loop::VecBuilder { stack_ptr })
}

fn vec_builder_end(vm: &mut VM) -> Xresult {
    match vm.pop_loop()? {
        Loop::VecBuilder { stack_ptr } => {
            let top_ptr = vm.ctx.data_stack.len();
            if top_ptr < stack_ptr {
                Err(Xerr::StackNotBalanced)
            } else {
                let mut v = Xvec::new();
                for x in &vm.ctx.data_stack[stack_ptr..] {
                    v.push_back_mut(x.clone());
                }
                vm.dropn(top_ptr - stack_ptr)?;
                vm.push_data(Cell::Vector(v))
            }
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_map_begin(vm: &mut VM) -> Xresult {
    vm.push_flow(Flow::Map)?;
    vm.code_emit(Inst::NativeCall(map_builder_begin))
}

fn core_word_map_end(vm: &mut VM) -> Xresult {
    match vm.pop_flow()? {
        Flow::Map => vm.code_emit(Inst::NativeCall(map_builder_end)),
        _ => Err(Xerr::ControlFlowError),
    }
}

fn map_builder_begin(vm: &mut VM) -> Xresult {
    let stack_ptr = vm.ctx.data_stack.len();
    vm.push_loop(Loop::MapBuilder { stack_ptr })
}

fn map_builder_end(vm: &mut VM) -> Xresult {
    match vm.pop_loop()? {
        Loop::MapBuilder { stack_ptr } => {
            let top_ptr = vm.ctx.data_stack.len();
            if top_ptr < stack_ptr || (top_ptr - stack_ptr) % 2 == 1 {
                Err(Xerr::StackNotBalanced)
            } else {
                let mut m = Xmap::new();
                for kv in vm.ctx.data_stack[stack_ptr..].chunks(2) {
                    m.push_back_mut((kv[0].clone(), kv[1].clone()));
                }
                vm.dropn(top_ptr - stack_ptr)?;
                vm.push_data(Cell::Map(m))
            }
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn is_building_word(vm: &mut VM) -> bool {
    vm.ctx.flow_stack.iter().any(|x| match x {
        Flow::Fun { .. } => true,
        _ => false,
    })
}

fn core_word_def_begin(vm: &mut VM) -> Xresult {
    if is_building_word(vm) {
        return Err(Xerr::RecusriveDefinition);
    }
    let name = match vm.source.next()? {
        Tok::Word(name) => name,
        _other => return Err(Xerr::ExpectingName),
    };
    let start = vm.code_offset();
    // jump over function body
    vm.code_emit(Inst::Jump(0))?;
    // function starts right after jump
    let xf = Xfn::Interp(vm.code_offset());
    let dict_idx = vm.dict_insert(
        name,
        Entry::Function {
            immediate: false,
            xf,
        },
    )?;
    vm.push_flow(Flow::Fun { dict_idx, start })
}

fn core_word_def_end(vm: &mut VM) -> Xresult {
    match vm.pop_flow()? {
        Flow::Fun { start, .. } => {
            vm.code_emit(Inst::Ret)?;
            let offs = jump_offset(start, vm.code_offset());
            vm.patch_jump(start, offs)
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_var(vm: &mut VM) -> Xresult {
    if is_building_word(vm) {
        return Err(Xerr::RecusriveDefinition);
    }
    let name = match vm.source.next()? {
        Tok::Word(name) => name,
        _other => return Err(Xerr::ExpectingName),
    };
    let a = vm.alloc_cell()?;
    vm.dict_insert(name, Entry::Variable(a))?;
    OK
}

fn core_word_setvar(vm: &mut VM) -> Xresult {
    let name = match vm.source.next()? {
        Tok::Word(name) => name,
        _other => return Err(Xerr::ExpectingName),
    };
    let e = vm
        .dict_find(&name)
        .and_then(|i| vm.dict_at(i))
        .ok_or(Xerr::UnknownWord)?;
    match e {
        Entry::Deferred => Err(Xerr::UnknownWord),
        Entry::Variable(a) => {
            let a = *a;
            vm.code_emit(Inst::Store(a))
        }
        _ => Err(Xerr::ReadonlyAddress),
    }
}

fn core_word_const(vm: &mut VM) -> Xresult {
    if is_building_word(vm) {
        return Err(Xerr::RecusriveDefinition);
    }
    let name = match vm.source.next()? {
        Tok::Word(name) => name,
        _other => return Err(Xerr::ExpectingName),
    };
    let a = vm.alloc_cell()?;
    let val = vm.pop_data()?;
    vm.heap[a] = val;
    vm.dict_insert(name, Entry::Variable(a))?;
    OK
}

fn core_word_nested_begin(vm: &mut VM) -> Xresult {
    vm.ctx_nested.push(CtxState {
        ds_len: vm.ctx.data_stack.len(),
        cs_len: vm.code.len(),
        rs_len: vm.ctx.return_stack.len(),
        fs_len: vm.ctx.flow_stack.len(),
        ls_len: vm.ctx.loops.len(),
        autoexec: true,        
    });
    OK
}

fn core_word_nested_end(vm: &mut VM) -> Xresult {
    let s = vm.ctx_nested.last().ok_or(Xerr::ControlFlowError)?.clone();
    if vm.ctx.flow_stack.len() > s.fs_len || vm.ctx.loops.len() > s.ls_len {
        return Err(Xerr::ControlFlowError);
    }
    vm.code_emit(Inst::Ret)?;
    vm.ctx_nested.pop();
    if s.autoexec {
        vm.run(Xfn::Interp(s.cs_len + 1))
        // drop code
    } else {
        OK
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
    vm.load("begin leave again").unwrap();
    let mut it = vm.ctx.code.iter();
    it.next().unwrap();
    assert_eq!(&Inst::Jump(-1), it.next().unwrap());
    let mut vm = VM::boot().unwrap();
    vm.load("0 begin 1 + until").unwrap();
    let mut it = vm.ctx.code.iter();
    it.next().unwrap();
    it.next().unwrap();
    it.next().unwrap();
    assert_eq!(&Inst::JumpIf(-2), it.next().unwrap());
    vm.interpret("var x 1 -> x begin x while 0 -> x repeat")
        .unwrap();
    assert_eq!(Err(Xerr::ControlFlowError), vm.load("if begin then repeat"));
    assert_eq!(Err(Xerr::ControlFlowError), vm.load("repeat begin"));
    assert_eq!(Err(Xerr::ControlFlowError), vm.load("begin then while"));
    assert_eq!(Err(Xerr::ControlFlowError), vm.load("until begin"));
    assert_eq!(Err(Xerr::ControlFlowError), vm.load("begin repeat until"));
    assert_eq!(Err(Xerr::ControlFlowError), vm.load("begin until repeat"));
}

#[test]
fn test_loop_leave() {
    let mut vm = VM::boot().unwrap();
    vm.interpret("begin 1 leave again").unwrap();
    let x = vm.pop_data().unwrap();
    assert_eq!(x.to_int(), Ok(1));
    assert_eq!(Some(Xerr::StackUnderflow), vm.pop_data().err());
    let mut vm = VM::boot().unwrap();
    let res = vm.load("begin 1 again leave");
    assert_eq!(Err(Xerr::ControlFlowError), res);
}
