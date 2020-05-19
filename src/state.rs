use num_traits::ToPrimitive;

use crate::cell::*;
use crate::error::*;
use crate::lex::*;
use crate::opcodes::*;

#[derive(Debug, Clone, PartialEq)]
enum Entry {
    Deferred,
    Variable(usize),
    Function {
        immediate: bool,
        xf: Xfn,
        len: Option<usize>,
    },
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
    code: Vec<Opcode>,
    data_stack: Vec<Cell>,
    return_stack: Vec<usize>,
    flow_stack: Vec<Flow>,
    loops: Vec<Loop>,
    ctx: Context,
    nested: Vec<Context>,
}

pub struct Xvar(usize);

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
            let mut start = self.ctx.code_start;
            if self.ctx.mode != ContextMode::Load
                && !self.has_pending_flow()
                && start < self.code_offset()
            {
                self.code_emit(Opcode::Ret)?;
                self.ctx.code_start = self.code_offset();
                self.run(Xfn::Interp(start))?;
                start = self.ctx.code_start;
            }
            match self.next_token()? {
                Tok::EndOfInput => {
                    if self.has_pending_flow() {
                        break Err(Xerr::ControlFlowError);
                    }
                    if start < self.code_offset() {
                        self.code_emit(Opcode::Ret)?;
                        self.ctx.code_start = self.code_offset();
                        let xf = Xfn::Interp(start);
                        if self.ctx.mode == ContextMode::Load {
                            break self.push_data(Cell::Fun(xf));
                        } else {
                            break self.run(xf);
                        }
                    }
                    break self.context_close();
                }
                Tok::Num(n) => {
                    let n = n.to_i128().ok_or(Xerr::IntegerOverflow)?;
                    self.code_emit(Opcode::LoadInt(n))?;
                }
                Tok::Str(s) => {
                    let a = self.readonly_cell(Cell::Str(s));
                    self.code_emit(Opcode::Load(a))?;
                }
                Tok::Word(name) => {
                    // get entry address or insert deferred
                    let idx = if let Some(idx) = self.dict_find(&name) {
                        idx
                    } else {
                        self.dict_insert(name, Entry::Deferred)?
                    };
                    match self.dict_at(idx).unwrap() {
                        Entry::Deferred => self.code_emit(Opcode::Deferred(idx))?,
                        Entry::Variable(a) => {
                            let a = *a;
                            self.code_emit(Opcode::Load(a))?;
                        }
                        Entry::Function {
                            immediate: true,
                            xf,
                            ..
                        } => {
                            let xf = xf.clone();
                            self.run(xf)?;
                        }
                        Entry::Function {
                            immediate: false,
                            xf: Xfn::Interp(x),
                            ..
                        } => {
                            let x = *x;
                            self.code_emit(Opcode::Call(x))?;
                        }
                        Entry::Function {
                            immediate: false,
                            xf: Xfn::Native(x),
                            ..
                        } => {
                            let x = *x;
                            self.code_emit(Opcode::NativeCall(x))?;
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

    pub fn defonce(&mut self, name: &str, value: Cell) -> Result<Xvar, Xerr> {
        if let Some(a) = self.dict_find(name) {
            Ok(Xvar(a))
        } else {
            let a = self.alloc_cell()?;
            self.heap[a] = value;
            self.dict_insert(name.to_string(), Entry::Variable(a))?;
            Ok(Xvar(a))
        }
    }

    pub fn get_var(&self, var: &Xvar) -> Result<&Cell, Xerr> {
        self.heap.get(var.0).ok_or(Xerr::InvalidAddress)
    }

    pub fn defword(&mut self, name: &str, x: XfnType) -> Xresult {
        let xf = Xfn::Native(x);
        self.dict_insert(
            name.to_string(),
            Entry::Function {
                immediate: false,
                xf,
                len: Some(0),
            },
        )?;
        OK
    }

    pub fn code_section(&self) -> &[Opcode] {
        &self.code[..]
    }
    pub fn code_fmt(&self, at: usize) -> Option<String> {
        self.code.get(at).map(|op| format_opcode(op, at))
    }

    fn load_core(&mut self) -> Xresult {
        struct Def(&'static str, XfnType);
        for i in [
            Def("if", core_word_if),
            Def("else", core_word_else),
            Def("then", core_word_then),
            Def("begin", core_word_begin),
            Def("while", core_word_while),
            Def("repeat", core_word_repeat),
            Def("until", core_word_until),
            Def("leave", core_word_leave),
            Def("again", core_word_again),
            Def("[", core_word_vec_begin),
            Def("]", core_word_vec_end),
            Def("{", core_word_map_begin),
            Def("}", core_word_map_end),
            Def(":", core_word_def_begin),
            Def(";", core_word_def_end),
            Def("var", core_word_var),
            Def("->", core_word_setvar),
            Def("const", core_word_const),
            Def("(", core_word_nested_begin),
            Def(")", core_word_nested_end),
            Def("see-code", core_word_see_code),
        ]
        .iter()
        {
            core_insert_word(self, i.0, i.1, true)?;
        }
        for i in [Def("dump", core_word_stack_dump)].iter() {
            core_insert_word(self, i.0, i.1, false)?;
        }
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

    fn code_emit(&mut self, inst: Opcode) -> Xresult {
        self.code.push(inst);
        OK
    }

    fn patch_insn(&mut self, at: usize, insn: Opcode) -> Xresult {
        self.code[at] = insn;
        OK
    }

    fn patch_jump(&mut self, at: usize, offs: isize) -> Xresult {
        let insn = match &self.code[at] {
            Opcode::Jump(_) => Opcode::Jump(offs),
            Opcode::JumpIf(_) => Opcode::JumpIf(offs),
            Opcode::JumpIfNot(_) => Opcode::JumpIfNot(offs),
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
            Opcode::Nop => self.next_ip(),
            Opcode::Jump(offs) => self.jump_to(offs),
            Opcode::JumpIf(offs) => {
                let t = self.pop_data()?;
                self.jump_if(t.is_true(), offs)
            }
            Opcode::JumpIfNot(offs) => {
                let t = self.pop_data()?;
                self.jump_if(!t.is_true(), offs)
            }
            Opcode::Call(a) => {
                self.push_return(ip + 1)?;
                self.set_ip(a)
            }
            Opcode::Deferred(idx) => match self.dict_at(idx).ok_or(Xerr::UnknownWord)? {
                Entry::Deferred => Err(Xerr::UnknownWord),
                Entry::Variable(a) => {
                    let a = *a;
                    self.patch_insn(ip, Opcode::Load(a))
                }
                Entry::Function {
                    xf: Xfn::Interp(x), ..
                } => {
                    let x = *x;
                    self.patch_insn(ip, Opcode::Call(x))
                }
                Entry::Function {
                    xf: Xfn::Native(x), ..
                } => {
                    let x = *x;
                    self.patch_insn(ip, Opcode::NativeCall(x))
                }
            },
            Opcode::NativeCall(x) => {
                x(self)?;
                self.next_ip()
            }
            Opcode::Ret => {
                let new_ip = self.pop_return()?;
                self.set_ip(new_ip)
            }
            Opcode::LoadInt(n) => {
                self.push_data(Cell::Int(n))?;
                self.next_ip()
            }
            Opcode::Load(a) => {
                let val = self.heap[a].clone();
                self.push_data(val)?;
                self.next_ip()
            }
            Opcode::Store(a) => {
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

fn core_insert_word(xs: &mut State, name: &str, x: XfnType, immediate: bool) -> Xresult {
    xs.dict_insert(
        name.to_string(),
        Entry::Function {
            immediate,
            xf: Xfn::Native(x),
            len: None,
        },
    )?;
    OK
}

fn core_word_if(xs: &mut State) -> Xresult {
    let fwd = Flow::If(xs.code_offset());
    xs.code_emit(Opcode::JumpIfNot(0))?;
    xs.push_flow(fwd)
}

fn core_word_else(xs: &mut State) -> Xresult {
    match xs.pop_flow()? {
        Flow::If(if_org) => {
            let fwd = Flow::If(xs.code_offset());
            xs.code_emit(Opcode::Jump(0))?;
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
            xs.code_emit(Opcode::JumpIf(offs))
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_while(xs: &mut State) -> Xresult {
    let cond = Flow::While(xs.code_offset());
    xs.code_emit(Opcode::JumpIfNot(0))?;
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
                break xs.code_emit(Opcode::Jump(offs));
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
                    let offs = jump_offset(cond_org, xs.code_offset() + 1);
                    xs.patch_jump(cond_org, offs)?;
                    let offs = jump_offset(xs.code_offset(), begin_org);
                    break xs.code_emit(Opcode::Jump(offs));
                }
                _ => break Err(Xerr::ControlFlowError),
            },
            _ => break Err(Xerr::ControlFlowError),
        }
    }
}

fn core_word_leave(xs: &mut State) -> Xresult {
    let leave = Flow::Leave(xs.code_offset());
    xs.code_emit(Opcode::Jump(0))?;
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
    xs.code_emit(Opcode::NativeCall(vec_builder_begin))
}

fn core_word_vec_end(xs: &mut State) -> Xresult {
    match xs.pop_flow()? {
        Flow::Vec => xs.code_emit(Opcode::NativeCall(vec_builder_end)),
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
    xs.code_emit(Opcode::NativeCall(map_builder_begin))
}

fn core_word_map_end(xs: &mut State) -> Xresult {
    match xs.pop_flow()? {
        Flow::Map => xs.code_emit(Opcode::NativeCall(map_builder_end)),
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

fn core_word_def_begin(xs: &mut State) -> Xresult {
    let name = match xs.next_token()? {
        Tok::Word(name) => name,
        _other => return Err(Xerr::ExpectingName),
    };
    let start = xs.code_offset();
    // jump over function body
    xs.code_emit(Opcode::Jump(0))?;
    // function starts right after jump
    let xf = Xfn::Interp(xs.code_offset());
    let dict_idx = xs.dict_insert(
        name,
        Entry::Function {
            immediate: false,
            xf,
            len: None,
        },
    )?;
    xs.push_flow(Flow::Fun { dict_idx, start })
}

fn core_word_def_end(xs: &mut State) -> Xresult {
    match xs.pop_flow()? {
        Flow::Fun { start, dict_idx } => {
            xs.code_emit(Opcode::Ret)?;
            let offs = jump_offset(start, xs.code_offset());
            let fun_len = xs.code_offset() - start;
            match xs.dict.get_mut(dict_idx).ok_or(Xerr::InvalidAddress)? {
                (_, Entry::Function { ref mut len, .. }) => *len = Some(fun_len),
                _ => panic!("entry type"),
            }
            xs.patch_jump(start, offs)
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_var(xs: &mut State) -> Xresult {
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
            xs.code_emit(Opcode::Store(a))
        }
        _ => Err(Xerr::ReadonlyAddress),
    }
}

fn core_word_const(xs: &mut State) -> Xresult {
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

fn format_opcode(op: &Opcode, ip: usize) -> String {
    let jumpaddr = |ip, offs| (ip as isize + offs) as usize;
    format!(
        "{:05x} {}",
        ip,
        match op {
            Opcode::Nop => format!("nop"),
            Opcode::Call(a) => format!("call ${:05x}", a),
            Opcode::Deferred(a) => format!("deferred {}", a),
            Opcode::NativeCall(x) => format!("callx ${:05x}", *x as usize),
            Opcode::Ret => format!("ret"),
            Opcode::JumpIf(offs) => format!("jumpif ${:05x}", jumpaddr(ip, offs)),
            Opcode::JumpIfNot(offs) => format!("jumpifnot ${:05x}", jumpaddr(ip, offs)),
            Opcode::Jump(offs) => format!("jump ${:05x}", jumpaddr(ip, offs)),
            Opcode::Load(a) => format!("load {}", a),
            Opcode::LoadInt(i) => format!("loadint {}", i),
            Opcode::Store(a) => format!("store {}", a),
        }
    )
}

fn try_print_code(xs: &mut State, start: usize) -> Xresult {
    for ip in start..xs.code.len() {
        let op = &xs.code[ip];
        println!("{}", format_opcode(op, ip));
        if *op == Opcode::Ret {
            break;
        }
    }
    OK
}

fn core_word_see_code(xs: &mut State) -> Xresult {
    let name = match xs.next_token()? {
        Tok::Word(name) => name,
        Tok::Num(n) => return try_print_code(xs, n.to_usize().ok_or(Xerr::InvalidAddress)?),
        _other => return Err(Xerr::ExpectingName),
    };
    let e = xs
        .dict_find(&name)
        .and_then(|i| xs.dict_at(i))
        .ok_or(Xerr::UnknownWord)?;
    match e {
        Entry::Deferred => {
            println!("unknown word");
        }
        Entry::Variable(a) => {
            println!("heap address: {}", a);
            println!("value: {:?}", xs.heap[*a]);
        }
        Entry::Function {
            immediate,
            xf: Xfn::Native(x),
            ..
        } => {
            println!(
                "native-function: 0x{:x}{}",
                *x as usize,
                if *immediate { " <immediate>" } else { "" }
            );
        }
        Entry::Function {
            immediate,
            xf: Xfn::Interp(a),
            len,
        } => {
            let start = *a;
            let end = start + len.unwrap_or(0);
            println!(
                "function: {}{}",
                start,
                if *immediate { " <immediate>" } else { "" }
            );
            for (i, op) in xs.code[start..end].iter().enumerate() {
                let ip = start + i;
                println!("{}", format_opcode(op, ip));
            }
        }
    }
    OK
}

fn core_word_stack_dump(xs: &mut State) -> Xresult {
    for val in xs.data_stack.iter().rev() {
        println!("\t{:?}", val);
    }
    OK
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
    assert_eq!(&Opcode::JumpIfNot(2), it.next().unwrap());
    let mut xs = State::new().unwrap();
    xs.load("1 if 222 else 333 then").unwrap();
    let mut it = xs.code.iter();
    it.next().unwrap();
    assert_eq!(&Opcode::JumpIfNot(3), it.next().unwrap());
    it.next().unwrap();
    assert_eq!(&Opcode::Jump(2), it.next().unwrap());
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
    assert_eq!(&Opcode::JumpIfNot(4), it.next().unwrap());
    it.next().unwrap();
    it.next().unwrap();
    assert_eq!(&Opcode::Jump(-4), it.next().unwrap());
    let mut xs = State::new().unwrap();
    xs.load("begin leave again").unwrap();
    let mut it = xs.code.iter();
    it.next().unwrap();
    assert_eq!(&Opcode::Jump(-1), it.next().unwrap());
    let mut xs = State::new().unwrap();
    xs.load("0 begin 1 + until").unwrap();
    let mut it = xs.code.iter();
    it.next().unwrap();
    it.next().unwrap();
    it.next().unwrap();
    assert_eq!(&Opcode::JumpIf(-2), it.next().unwrap());
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
    assert_eq!(Err(Xerr::StackUnderflow), xs.pop_data());
    let mut xs = State::new().unwrap();
    let res = xs.load("begin 1 again leave");
    assert_eq!(Err(Xerr::ControlFlowError), res);
}
