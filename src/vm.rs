use num_traits::ToPrimitive;

use crate::cell::*;
use crate::error::*;
use crate::lex::*;

#[derive(Debug, Clone, PartialEq)]
enum Xflags {
    Empty,
    Immediate,
    Variable,
    Function,
}

#[derive(Debug, Clone)]
struct Entry {
    name: String,
    flags: Xflags,
    data: Cell,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Inst {
    Nop,
    Const(usize),
    Call(usize),
    Deferred(usize),
    NativeCall(Xfn),
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
    Fun { word_addr: usize, start: usize },
}

#[derive(Clone)]
enum Loop {
    VecBuilder { stack_ptr: usize },
    MapBuilder { stack_ptr: usize },
}

#[derive(Clone, Default)]
pub struct Ctx {
    code: Vec<Inst>,
    ip: usize,
    ds: Vec<Cell>,
    rs: Vec<usize>,
    fs: Vec<Flow>,
    ls: Vec<Loop>,
}

#[derive(Clone, Default)]
pub struct VM {
    dict: Vec<Entry>,
    heap: Vec<Cell>,
    ctx: Ctx,
    source: Lex,
    debug: bool,
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
            if !is_loading && !self.has_pending_flow() && start < self.ctx.code.len() {
                self.emit(Inst::Ret)?;
                self.finish_building()?;
                self.run(Cell::InterpFn(start))?;
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
                            break self.run(Cell::InterpFn(start));
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
                    let wa = self.lookup(&name).unwrap_or_else(|| self.insert_word(name));
                    match &self.dict[wa] {
                        Entry {
                            flags: Xflags::Empty,
                            ..
                        } => self.emit(Inst::Deferred(wa))?,
                        Entry {
                            flags: Xflags::Immediate,
                            data,
                            ..
                        } => {
                            let x = data.clone();
                            self.run(x)?;
                        }
                        Entry {
                            flags: Xflags::Variable,
                            ..
                        } => {
                            self.emit(Inst::Load(wa))?;
                        }
                        Entry {
                            flags: Xflags::Function,
                            data,
                            ..
                        } => {
                            let x = data.clone();
                            match x {
                                Cell::InterpFn(a) => self.emit(Inst::Call(a))?,
                                Cell::NativeFn(f) => self.emit(Inst::NativeCall(f))?,
                                _ => Err(Xerr::NotAnExecutable)?,
                            }
                        }
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
        vm.debug = true;
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
        core_insert_imm_word(self, "leave", core_word_leave)?;
        core_insert_imm_word(self, "again", core_word_again)?;
        core_insert_imm_word(self, "[", core_word_vec_begin)?;
        core_insert_imm_word(self, "]", core_word_vec_end)?;
        core_insert_imm_word(self, "{", core_word_map_begin)?;
        core_insert_imm_word(self, "}", core_word_map_end)?;
        core_insert_imm_word(self, ":", core_word_def_begin)?;
        core_insert_imm_word(self, ";", core_word_def_end)?;
        core_insert_imm_word(self, "var", core_word_var)?;
        core_insert_imm_word(self, "!", core_word_store)?;
        OK
    }

    fn insert_word(&mut self, name: String) -> usize {
        let wa = self.dict.len();
        self.dict.push(Entry {
            name: name,
            flags: Xflags::Empty,
            data: Cell::Nil,
        });
        wa
    }

    fn origin(&self) -> usize {
        self.ctx.code.len()
    }

    fn emit(&mut self, inst: Inst) -> Xresult {
        self.ctx.code.push(inst);
        OK
    }

    fn patch_insn(&mut self, at: usize, insn: Inst) -> Xresult {
        self.ctx.code[at] = insn;
        OK
    }

    fn patch_jump(&mut self, at: usize, offs: isize) -> Xresult {
        let insn = match &self.ctx.code[at] {
            Inst::Jump(_) => Inst::Jump(offs),
            Inst::JumpIf(_) => Inst::JumpIf(offs),
            Inst::JumpIfNot(_) => Inst::JumpIfNot(offs),
            other => panic!("not a jump instruction {:?}", other),
        };
        self.patch_insn(at, insn)
    }

    fn word_get(&self, wa: usize) -> Result<&Entry, Xerr> {
        self.dict.get(wa).ok_or(Xerr::InvalidAddress)
    }

    fn word_modify(&mut self, a: usize, c: Cell) -> Xresult {
        let p = self.dict.get_mut(a).ok_or(Xerr::InvalidAddress)?;
        p.data = c;
        OK
    }

    fn readonly_cell(&mut self, c: Cell) -> usize {
        if let Some(a) = self.heap.iter().position(|x| x == &c) {
            a
        } else {
            let a = self.heap.len();
            self.heap.push(c);
            a
        }
    }

    fn run(&mut self, c: Cell) -> Xresult {
        match c {
            Cell::NativeFn(f) => f.0(self),
            Cell::InterpFn(a) => {
                let old_ip = self.ctx.ip;
                let depth = self.ctx.rs.len();
                self.push_return(old_ip)?;
                self.set_ip(a)?;
                loop {
                    self.run_inst()?;
                    if depth == self.ctx.rs.len() {
                        assert_eq!(old_ip, self.ctx.ip);
                        break OK;
                    }
                }
            }
            _ => Err(Xerr::NotAnExecutable),
        }
    }

    fn run_inst(&mut self) -> Xresult {
        let ip = self.ctx.ip;
        match self.ctx.code[ip] {
            Inst::Nop => self.next_ip(),
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
            Inst::Call(a) => {
                self.push_return(ip + 1)?;
                self.set_ip(a)
            }
            Inst::Deferred(wa) => match self.word_get(wa)? {
                Entry {
                    flags: Xflags::Empty,
                    ..
                } => Err(Xerr::UnknownWord),
                Entry {
                    flags: Xflags::Variable,
                    ..
                } => self.patch_insn(ip, Inst::Load(wa)),
                Entry { data, .. } => match data.clone() {
                    Cell::InterpFn(a) => self.patch_insn(ip, Inst::Call(a)),
                    Cell::NativeFn(f) => self.patch_insn(ip, Inst::NativeCall(f)),
                    _ => Err(Xerr::NotAnExecutable),
                },
            },
            Inst::NativeCall(f) => {
                f.0(self)?;
                self.next_ip()
            }
            Inst::Ret => {
                let new_ip = self.pop_return()?;
                self.set_ip(new_ip)
            }
            Inst::Load(wa) => {
                let c = self.word_get(wa)?.data.clone();
                self.push_data(c)?;
                self.next_ip()
            }
            Inst::Store(wa) => {
                let c = self.pop_data()?;
                self.word_modify(wa, c)?;
                self.next_ip()
            }
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

    fn set_ip(&mut self, new_ip: usize) -> Xresult {
        self.ctx.ip = new_ip;
        OK
    }

    fn next_ip(&mut self) -> Xresult {
        self.ctx.ip += 1;
        OK
    }

    fn pop_flow(&mut self) -> Result<Flow, Xerr> {
        self.ctx.fs.pop().ok_or(Xerr::ControlFlowError)
    }

    fn push_flow(&mut self, flow: Flow) -> Xresult {
        self.ctx.fs.push(flow);
        OK
    }

    pub fn lookup(&mut self, name: &str) -> Option<usize> {
        self.dict.iter().rposition(|x| x.name == name)
    }

    fn dropn(&mut self, len: usize) -> Xresult {
        let ds_len = self.ctx.ds.len();
        if ds_len < len {
            Err(Xerr::StackUnderflow)
        } else {
            self.ctx.ds.truncate(ds_len - len);
            OK
        }
    }

    pub fn push_data(&mut self, data: Cell) -> Xresult {
        self.ctx.ds.push(data);
        OK
    }

    pub fn pop_data_typed(&mut self) -> Result<Cell, Xerr> {
        todo!("wof!")
    }

    pub fn pop_data(&mut self) -> Result<Cell, Xerr> {
        self.ctx.ds.pop().ok_or(Xerr::StackUnderflow)
    }

    pub fn top_data(&mut self) -> Option<&Cell> {
        self.ctx.ds.last()
    }

    fn push_return(&mut self, return_to: usize) -> Xresult {
        self.ctx.rs.push(return_to);
        OK
    }

    fn pop_return(&mut self) -> Result<usize, Xerr> {
        self.ctx.rs.pop().ok_or(Xerr::ReturnStackUnderflow)
    }

    fn push_loop(&mut self, l: Loop) -> Xresult {
        self.ctx.ls.push(l);
        OK
    }

    fn pop_loop(&mut self) -> Result<Loop, Xerr> {
        self.ctx.ls.pop().ok_or(Xerr::LoopStackUnderflow)
    }
}

fn core_insert_imm_word(vm: &mut VM, name: &str, f: XfnType) -> Xresult {
    if let Some(_) = vm.lookup(name) {
        panic!("core word duplication {:?}", name);
    }
    vm.dict.push(Entry {
        name: name.to_string(),
        flags: Xflags::Immediate,
        data: Cell::NativeFn(Xfn(f)),
    });
    OK
}

fn core_word_if(vm: &mut VM) -> Xresult {
    let fwd = Flow::If(vm.origin());
    vm.emit(Inst::JumpIfNot(0))?;
    vm.push_flow(fwd)
}

fn core_word_else(vm: &mut VM) -> Xresult {
    match vm.pop_flow()? {
        Flow::If(if_org) => {
            let fwd = Flow::If(vm.origin());
            vm.emit(Inst::Jump(0))?;
            vm.push_flow(fwd)?;
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
    vm.push_flow(Flow::Begin(vm.origin()))
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
    vm.push_flow(cond)
}

fn core_word_again(vm: &mut VM) -> Xresult {
    loop {
        match vm.pop_flow()? {
            Flow::Leave(leave_org) => {
                let offs = jump_offset(leave_org, vm.origin() + 1);
                vm.patch_jump(leave_org, offs)?;
            }
            Flow::Begin(begin_org) => {
                let offs = jump_offset(vm.origin(), begin_org);
                break vm.emit(Inst::Jump(offs));
            }
            _ => break Err(Xerr::ControlFlowError),
        }
    }
}

fn core_word_repeat(vm: &mut VM) -> Xresult {
    loop {
        match vm.pop_flow()? {
            Flow::Leave(leave_org) => {
                let offs = jump_offset(leave_org, vm.origin() + 1);
                vm.patch_jump(leave_org, offs)?;
            }
            Flow::While(cond_org) => match vm.pop_flow()? {
                Flow::Begin(begin_org) => {
                    let offs = jump_offset(cond_org, vm.origin());
                    vm.patch_jump(cond_org, offs)?;
                    let offs = jump_offset(vm.origin(), begin_org);
                    break vm.emit(Inst::Jump(offs));
                }
                _ => break Err(Xerr::ControlFlowError),
            },
            _ => break Err(Xerr::ControlFlowError),
        }
    }
}

fn core_word_leave(vm: &mut VM) -> Xresult {
    let leave = Flow::Leave(vm.origin());
    vm.emit(Inst::Jump(0))?;
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
    vm.emit(Inst::NativeCall(Xfn(vec_builder_begin)))
}

fn core_word_vec_end(vm: &mut VM) -> Xresult {
    match vm.pop_flow()? {
        Flow::Vec => vm.emit(Inst::NativeCall(Xfn(vec_builder_end))),
        _ => Err(Xerr::ControlFlowError),
    }
}

fn vec_builder_begin(vm: &mut VM) -> Xresult {
    let stack_ptr = vm.ctx.ds.len();
    vm.push_loop(Loop::VecBuilder { stack_ptr })
}

fn vec_builder_end(vm: &mut VM) -> Xresult {
    match vm.pop_loop()? {
        Loop::VecBuilder { stack_ptr } => {
            let top_ptr = vm.ctx.ds.len();
            if top_ptr < stack_ptr {
                Err(Xerr::StackNotBalanced)
            } else {
                let mut v = Xvec::new();
                for x in &vm.ctx.ds[stack_ptr..] {
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
    vm.emit(Inst::NativeCall(Xfn(map_builder_begin)))
}

fn core_word_map_end(vm: &mut VM) -> Xresult {
    match vm.pop_flow()? {
        Flow::Map => vm.emit(Inst::NativeCall(Xfn(map_builder_end))),
        _ => Err(Xerr::ControlFlowError),
    }
}

fn map_builder_begin(vm: &mut VM) -> Xresult {
    let stack_ptr = vm.ctx.ds.len();
    vm.push_loop(Loop::MapBuilder { stack_ptr })
}

fn map_builder_end(vm: &mut VM) -> Xresult {
    match vm.pop_loop()? {
        Loop::MapBuilder { stack_ptr } => {
            let top_ptr = vm.ctx.ds.len();
            if top_ptr < stack_ptr || (top_ptr - stack_ptr) % 2 == 1 {
                Err(Xerr::StackNotBalanced)
            } else {
                let mut m = Xmap::new();
                for kv in vm.ctx.ds[stack_ptr..].chunks(2) {
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
    vm.ctx.fs.iter().any(|x| match x {
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
    let word_addr = vm.lookup(&name).unwrap_or_else(|| vm.insert_word(name));
    vm.dict[word_addr].flags = Xflags::Function;
    let start = vm.origin();
    vm.emit(Inst::Jump(0))?; // jump over function body
    vm.push_flow(Flow::Fun { word_addr, start })
}

fn core_word_def_end(vm: &mut VM) -> Xresult {
    match vm.pop_flow()? {
        Flow::Fun { word_addr, start } => {
            vm.emit(Inst::Ret)?;
            let offs = jump_offset(start, vm.origin());
            vm.patch_jump(start, offs)?;
            let start = start + 1; // skip jump
            vm.dict[word_addr].data = Cell::InterpFn(start);
            OK
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
    let wa = vm.lookup(&name).unwrap_or_else(|| vm.insert_word(name));
    vm.dict[wa].flags = Xflags::Variable;
    OK
}

fn core_word_store(vm: &mut VM) -> Xresult {
    let name = match vm.source.next()? {
        Tok::Word(name) => name,
        _other => return Err(Xerr::ExpectingName),
    };
    let wa = vm.lookup(&name).ok_or(Xerr::UnknownWord)?;
    vm.emit(Inst::Store(wa))
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
    assert_eq!(x, Cell::Int(1));
    assert_eq!(Err(Xerr::StackUnderflow), vm.pop_data());
    let mut vm = VM::boot().unwrap();
    let res = vm.load("begin 1 again leave");
    assert_eq!(Err(Xerr::ControlFlowError), res);
}
