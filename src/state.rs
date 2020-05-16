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

#[derive(Clone, PartialEq)]
enum ContextMode {
    // assemble function and return address
    Load,
    // normal evaluation
    Eval,
    // meta evaluation
    Nested,
}

impl Default for ContextMode {
    fn default() -> Self {
        ContextMode::Eval
    }
}

#[derive(Clone, Default)]
struct Context {
    ds_len: usize,
    cs_len: usize,
    rs_len: usize,
    fs_len: usize,
    ls_len: usize,
    code_start: usize,
    ip: usize,
    mode: ContextMode,
    source: Option<Lex>,
}

#[derive(Clone, Default)]
pub struct State {
    dict: Vec<(String, Entry)>,
    heap: Vec<Cell>,
    code: Vec<Inst>,
    data_stack: Vec<Cell>,
    return_stack: Vec<usize>,
    flow_stack: Vec<Flow>,
    loops: Vec<Loop>,
    ctx: Context,
    nested: Vec<Context>,
}

impl State {
    pub fn load(&mut self, source: &str) -> Xresult {
        self.context_open(ContextMode::Load, Some(Lex::from_str(source)))?;
        self.build()
    }

    pub fn interpret(&mut self, source: &str) -> Xresult {
        self.context_open(ContextMode::Eval, Some(Lex::from_str(source)))?;
        self.build()
    }

    fn build(&mut self) -> Xresult {
        loop {
            let start = self.ctx.code_start;
            if self.ctx.mode != ContextMode::Load
                && !self.has_pending_flow()
                && start < self.code_offset()
            {
                self.code_emit(Inst::Ret)?;
                self.ctx.code_start = self.code_offset();
                self.run(Xfn::Interp(start))?;
            }
            match self.next_token()? {
                Tok::EndOfInput => {
                    if self.has_pending_flow() {
                        break Err(Xerr::ControlFlowError);
                    }
                    if start < self.code_offset() {
                        self.code_emit(Inst::Ret)?;
                        self.ctx.code_start = self.code_offset();
                        let xf = Xfn::Interp(start);
                        if self.ctx.mode == ContextMode::Load {
                            break self.push_data(Cell::Fun(xf));
                        } else {
                            break self.run(xf);
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

    fn next_token(&mut self) -> Result<Tok, Xerr> {
        if let Some(lex) = &mut self.ctx.source {
            lex.next()
        } else {
            Ok(Tok::EndOfInput)
        }
    }

    fn context_open(&mut self, mode: ContextMode, source: Option<Lex>) -> Xresult {
        let mut tmp = Context {
            ds_len: self.data_stack.len(),
            cs_len: self.code.len(),
            rs_len: self.return_stack.len(),
            fs_len: self.flow_stack.len(),
            ls_len: self.loops.len(),
            code_start: self.code_offset(),
            ip: self.ip(),
            mode,
            source,
        };
        if tmp.source.is_none() {
            // take source form previous context
            tmp.source = self.ctx.source.take();
        }
        std::mem::swap(&mut self.ctx, &mut tmp);
        self.nested.push(tmp);
        OK
    }

    fn context_close(&mut self) -> Xresult {
        let mut tmp = self.nested.pop().ok_or(Xerr::ControlFlowError)?;
        if tmp.source.is_none() {
            // take source from current context
            tmp.source = self.ctx.source.take();
        }
        if self.ctx.mode == ContextMode::Nested {
            // clear context code after evaluation
            self.code.truncate(tmp.cs_len);
        }
        std::mem::swap(&mut self.ctx, &mut tmp);
        OK
    }

    fn has_pending_flow(&self) -> bool {
        self.flow_stack.len() > 0
    }

    pub fn new() -> Result<State, Xerr> {
        let mut xs = State::default();
        xs.load_core()?;
        Ok(xs)
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
                let old_ip = self.ip();
                let depth = self.return_stack.len();
                self.push_return(old_ip)?;
                self.set_ip(x)?;
                loop {
                    self.run_inst()?;
                    if depth == self.return_stack.len() {
                        assert_eq!(old_ip, self.ip());
                        break OK;
                    }
                }
            }
        }
    }

    fn run_inst(&mut self) -> Xresult {
        let ip = self.ip();
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
        let new_ip = (self.ip() as isize + offs) as usize;
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

    fn ip(&self) -> usize {
        self.ctx.ip
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
        self.flow_stack.pop().ok_or(Xerr::ControlFlowError)
    }

    fn push_flow(&mut self, flow: Flow) -> Xresult {
        self.flow_stack.push(flow);
        OK
    }

    fn dropn(&mut self, len: usize) -> Xresult {
        let ds_len = self.data_stack.len();
        if ds_len < len {
            Err(Xerr::StackUnderflow)
        } else {
            self.data_stack.truncate(ds_len - len);
            OK
        }
    }
    pub fn push_data(&mut self, data: Cell) -> Xresult {
        self.data_stack.push(data);
        OK
    }

    pub fn pop_data(&mut self) -> Result<Cell, Xerr> {
        if self.data_stack.len() > self.ctx.ds_len {
            self.data_stack.pop().ok_or(Xerr::StackUnderflow)
        } else {
            Err(Xerr::StackUnderflow)
        }
    }

    pub fn top_data(&mut self) -> Option<&Cell> {
        self.data_stack.last()
    }

    fn push_return(&mut self, return_to: usize) -> Xresult {
        self.return_stack.push(return_to);
        OK
    }

    fn pop_return(&mut self) -> Result<usize, Xerr> {
        if self.return_stack.len() > self.ctx.rs_len {
            self.return_stack.pop().ok_or(Xerr::ReturnStackUnderflow)
        } else {
            Err(Xerr::ReturnStackUnderflow)
        }
    }

    fn push_loop(&mut self, l: Loop) -> Xresult {
        self.loops.push(l);
        OK
    }

    fn pop_loop(&mut self) -> Result<Loop, Xerr> {
        if self.loops.len() > self.ctx.ls_len {
            self.loops.pop().ok_or(Xerr::LoopStackUnderflow)
        } else {
            Err(Xerr::LoopStackUnderflow)
        }
    }
}

fn core_insert_imm_word(xs: &mut State, name: &str, x: XfnType) -> Xresult {
    xs.dict_insert(
        name.to_string(),
        Entry::Function {
            immediate: true,
            xf: Xfn::Native(x),
        },
    )?;
    OK
}

fn core_word_if(xs: &mut State) -> Xresult {
    let fwd = Flow::If(xs.code_offset());
    xs.code_emit(Inst::JumpIfNot(0))?;
    xs.push_flow(fwd)
}

fn core_word_else(xs: &mut State) -> Xresult {
    match xs.pop_flow()? {
        Flow::If(if_org) => {
            let fwd = Flow::If(xs.code_offset());
            xs.code_emit(Inst::Jump(0))?;
            xs.push_flow(fwd)?;
            let offs = jump_offset(if_org, xs.code_offset());
            xs.patch_jump(if_org, offs)
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_then(xs: &mut State) -> Xresult {
    match xs.pop_flow()? {
        Flow::If(if_org) => {
            let offs = jump_offset(if_org, xs.code_offset());
            xs.patch_jump(if_org, offs)
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_begin(xs: &mut State) -> Xresult {
    xs.push_flow(Flow::Begin(xs.code_offset()))
}

fn core_word_until(xs: &mut State) -> Xresult {
    match xs.pop_flow()? {
        Flow::Begin(begin_org) => {
            let offs = jump_offset(xs.code_offset(), begin_org);
            xs.code_emit(Inst::JumpIf(offs))
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_while(xs: &mut State) -> Xresult {
    let cond = Flow::While(xs.code_offset());
    xs.code_emit(Inst::JumpIfNot(0))?;
    xs.push_flow(cond)
}

fn core_word_again(xs: &mut State) -> Xresult {
    loop {
        match xs.pop_flow()? {
            Flow::Leave(leave_org) => {
                let offs = jump_offset(leave_org, xs.code_offset() + 1);
                xs.patch_jump(leave_org, offs)?;
            }
            Flow::Begin(begin_org) => {
                let offs = jump_offset(xs.code_offset(), begin_org);
                break xs.code_emit(Inst::Jump(offs));
            }
            _ => break Err(Xerr::ControlFlowError),
        }
    }
}

fn core_word_repeat(xs: &mut State) -> Xresult {
    loop {
        match xs.pop_flow()? {
            Flow::Leave(leave_org) => {
                let offs = jump_offset(leave_org, xs.code_offset() + 1);
                xs.patch_jump(leave_org, offs)?;
            }
            Flow::While(cond_org) => match xs.pop_flow()? {
                Flow::Begin(begin_org) => {
                    let offs = jump_offset(cond_org, xs.code_offset());
                    xs.patch_jump(cond_org, offs)?;
                    let offs = jump_offset(xs.code_offset(), begin_org);
                    break xs.code_emit(Inst::Jump(offs));
                }
                _ => break Err(Xerr::ControlFlowError),
            },
            _ => break Err(Xerr::ControlFlowError),
        }
    }
}

fn core_word_leave(xs: &mut State) -> Xresult {
    let leave = Flow::Leave(xs.code_offset());
    xs.code_emit(Inst::Jump(0))?;
    xs.push_flow(leave)?;
    OK
}

fn jump_offset(origin: usize, dest: usize) -> isize {
    if origin > dest {
        -((origin - dest) as isize)
    } else {
        (dest - origin) as isize
    }
}

fn core_word_vec_begin(xs: &mut State) -> Xresult {
    xs.push_flow(Flow::Vec)?;
    xs.code_emit(Inst::NativeCall(vec_builder_begin))
}

fn core_word_vec_end(xs: &mut State) -> Xresult {
    match xs.pop_flow()? {
        Flow::Vec => xs.code_emit(Inst::NativeCall(vec_builder_end)),
        _ => Err(Xerr::ControlFlowError),
    }
}

fn vec_builder_begin(xs: &mut State) -> Xresult {
    let stack_ptr = xs.data_stack.len();
    xs.push_loop(Loop::VecBuilder { stack_ptr })
}

fn vec_builder_end(xs: &mut State) -> Xresult {
    match xs.pop_loop()? {
        Loop::VecBuilder { stack_ptr } => {
            let top_ptr = xs.data_stack.len();
            if top_ptr < stack_ptr {
                Err(Xerr::StackNotBalanced)
            } else {
                let mut v = Xvec::new();
                for x in &xs.data_stack[stack_ptr..] {
                    v.push_back_mut(x.clone());
                }
                xs.dropn(top_ptr - stack_ptr)?;
                xs.push_data(Cell::Vector(v))
            }
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_map_begin(xs: &mut State) -> Xresult {
    xs.push_flow(Flow::Map)?;
    xs.code_emit(Inst::NativeCall(map_builder_begin))
}

fn core_word_map_end(xs: &mut State) -> Xresult {
    match xs.pop_flow()? {
        Flow::Map => xs.code_emit(Inst::NativeCall(map_builder_end)),
        _ => Err(Xerr::ControlFlowError),
    }
}

fn map_builder_begin(xs: &mut State) -> Xresult {
    let stack_ptr = xs.data_stack.len();
    xs.push_loop(Loop::MapBuilder { stack_ptr })
}

fn map_builder_end(xs: &mut State) -> Xresult {
    match xs.pop_loop()? {
        Loop::MapBuilder { stack_ptr } => {
            let top_ptr = xs.data_stack.len();
            if top_ptr < stack_ptr || (top_ptr - stack_ptr) % 2 == 1 {
                Err(Xerr::StackNotBalanced)
            } else {
                let mut m = Xmap::new();
                for kv in xs.data_stack[stack_ptr..].chunks(2) {
                    m.push_back_mut((kv[0].clone(), kv[1].clone()));
                }
                xs.dropn(top_ptr - stack_ptr)?;
                xs.push_data(Cell::Map(m))
            }
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn is_building_word(xs: &mut State) -> bool {
    xs.flow_stack.iter().any(|x| match x {
        Flow::Fun { .. } => true,
        _ => false,
    })
}

fn core_word_def_begin(xs: &mut State) -> Xresult {
    if is_building_word(xs) {
        return Err(Xerr::RecusriveDefinition);
    }
    let name = match xs.next_token()? {
        Tok::Word(name) => name,
        _other => return Err(Xerr::ExpectingName),
    };
    let start = xs.code_offset();
    // jump over function body
    xs.code_emit(Inst::Jump(0))?;
    // function starts right after jump
    let xf = Xfn::Interp(xs.code_offset());
    let dict_idx = xs.dict_insert(
        name,
        Entry::Function {
            immediate: false,
            xf,
        },
    )?;
    xs.push_flow(Flow::Fun { dict_idx, start })
}

fn core_word_def_end(xs: &mut State) -> Xresult {
    match xs.pop_flow()? {
        Flow::Fun { start, .. } => {
            xs.code_emit(Inst::Ret)?;
            let offs = jump_offset(start, xs.code_offset());
            xs.patch_jump(start, offs)
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_var(xs: &mut State) -> Xresult {
    if is_building_word(xs) {
        return Err(Xerr::RecusriveDefinition);
    }
    let name = match xs.next_token()? {
        Tok::Word(name) => name,
        _other => return Err(Xerr::ExpectingName),
    };
    let a = xs.alloc_cell()?;
    xs.dict_insert(name, Entry::Variable(a))?;
    OK
}

fn core_word_setvar(xs: &mut State) -> Xresult {
    let name = match xs.next_token()? {
        Tok::Word(name) => name,
        _other => return Err(Xerr::ExpectingName),
    };
    let e = xs
        .dict_find(&name)
        .and_then(|i| xs.dict_at(i))
        .ok_or(Xerr::UnknownWord)?;
    match e {
        Entry::Deferred => Err(Xerr::UnknownWord),
        Entry::Variable(a) => {
            let a = *a;
            xs.code_emit(Inst::Store(a))
        }
        _ => Err(Xerr::ReadonlyAddress),
    }
}

fn core_word_const(xs: &mut State) -> Xresult {
    if is_building_word(xs) {
        return Err(Xerr::RecusriveDefinition);
    }
    let name = match xs.next_token()? {
        Tok::Word(name) => name,
        _other => return Err(Xerr::ExpectingName),
    };
    let a = xs.alloc_cell()?;
    let val = xs.pop_data()?;
    xs.heap[a] = val;
    xs.dict_insert(name, Entry::Variable(a))?;
    OK
}

fn core_word_nested_begin(xs: &mut State) -> Xresult {
    xs.context_open(ContextMode::Nested, None)
}

fn core_word_nested_end(xs: &mut State) -> Xresult {
    if xs.ctx.mode != ContextMode::Nested
        || xs.flow_stack.len() > xs.ctx.fs_len
        || xs.loops.len() > xs.ctx.ls_len
    {
        return Err(Xerr::ControlFlowError);
    }
    xs.context_close()
}

#[test]
fn test_jump_offset() {
    assert_eq!(2, jump_offset(2, 4));
    assert_eq!(-2, jump_offset(4, 2));
}

#[test]
fn test_if_flow() {
    let mut xs = State::new().unwrap();
    xs.load("1 if 222 then").unwrap();
    let mut it = xs.code.iter();
    it.next().unwrap();
    assert_eq!(&Inst::JumpIfNot(2), it.next().unwrap());
    let mut xs = State::new().unwrap();
    xs.load("1 if 222 else 333 then").unwrap();
    let mut it = xs.code.iter();
    it.next().unwrap();
    assert_eq!(&Inst::JumpIfNot(3), it.next().unwrap());
    it.next().unwrap();
    assert_eq!(&Inst::Jump(2), it.next().unwrap());
    // test errors
    let mut xs = State::new().unwrap();
    assert_eq!(Err(Xerr::ControlFlowError), xs.load("1 if 222 else 333"));
    let mut xs = State::new().unwrap();
    assert_eq!(Err(Xerr::ControlFlowError), xs.load("1 if 222 else"));
    let mut xs = State::new().unwrap();
    assert_eq!(Err(Xerr::ControlFlowError), xs.load("1 if 222"));
    let mut xs = State::new().unwrap();
    assert_eq!(Err(Xerr::ControlFlowError), xs.load("1 else 222 then"));
    assert_eq!(Err(Xerr::ControlFlowError), xs.load("else 222 if"));
}

#[test]
fn test_begin_repeat() {
    let mut xs = State::new().unwrap();
    xs.load("begin 5 while 1 - repeat").unwrap();
    let mut it = xs.code.iter();
    it.next().unwrap();
    assert_eq!(&Inst::JumpIfNot(3), it.next().unwrap());
    it.next().unwrap();
    it.next().unwrap();
    assert_eq!(&Inst::Jump(-4), it.next().unwrap());
    let mut xs = State::new().unwrap();
    xs.load("begin leave again").unwrap();
    let mut it = xs.code.iter();
    it.next().unwrap();
    assert_eq!(&Inst::Jump(-1), it.next().unwrap());
    let mut xs = State::new().unwrap();
    xs.load("0 begin 1 + until").unwrap();
    let mut it = xs.code.iter();
    it.next().unwrap();
    it.next().unwrap();
    it.next().unwrap();
    assert_eq!(&Inst::JumpIf(-2), it.next().unwrap());
    xs.interpret("var x 1 -> x begin x while 0 -> x repeat")
        .unwrap();
    assert_eq!(Err(Xerr::ControlFlowError), xs.load("if begin then repeat"));
    assert_eq!(Err(Xerr::ControlFlowError), xs.load("repeat begin"));
    assert_eq!(Err(Xerr::ControlFlowError), xs.load("begin then while"));
    assert_eq!(Err(Xerr::ControlFlowError), xs.load("until begin"));
    assert_eq!(Err(Xerr::ControlFlowError), xs.load("begin repeat until"));
    assert_eq!(Err(Xerr::ControlFlowError), xs.load("begin until repeat"));
}

#[test]
fn test_loop_leave() {
    let mut xs = State::new().unwrap();
    xs.interpret("begin 1 leave again").unwrap();
    let x = xs.pop_data().unwrap();
    assert_eq!(x.to_int(), Ok(1));
    assert_eq!(Some(Xerr::StackUnderflow), xs.pop_data().err());
    let mut xs = State::new().unwrap();
    let res = xs.load("begin 1 again leave");
    assert_eq!(Err(Xerr::ControlFlowError), res);
}
