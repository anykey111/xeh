use crate::arith::*;
use crate::cell::*;
use crate::debug::*;
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
struct FunctionFlow {
    dict_idx: usize,
    start: usize,
    locals: Vec<String>,
}

#[derive(Clone)]
enum Flow {
    If(usize),
    Begin(usize),
    While(usize),
    Leave(usize),
    Vec,
    Map,
    Fun(FunctionFlow),
    Do { test_org: usize, jump_org: usize },
}

#[derive(Debug, Clone)]
pub enum Loop {
    VecBuilder { stack_ptr: usize },
    MapBuilder { stack_ptr: usize },
    Do { start: Xint, end: Xint },
}

#[derive(Clone, PartialEq)]
enum ContextMode {
    // assemble function
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
    ip: usize,
    mode: ContextMode,
    source: Option<Lex>,
}

#[derive(Debug, Clone, Default)]
pub struct Frame {
    return_to: usize,
    locals: Vec<Cell>,
}

impl Frame {
    fn from_addr(return_to: usize) -> Self {
        Self {
            return_to,
            locals: Default::default(),
        }
    }
}

#[derive(Debug)]
pub enum StateChange {
    SetIp(usize),
    DecrementIp,
    PushData(Cell),
    PopData,
    SwapData,
    RotData,
    OverData,
    PopReturn,
    PushReturn(Frame),
    PopLoop,
    PushLoop(Loop),
}

fn journal_state_change(rec: &mut Vec<StateChange>, x: StateChange) {
    if rec.len() > 10_000 {
        let mut rest = rec.split_off(5_000);
        std::mem::swap(rec, &mut rest);
    }
    rec.push(x);
}

#[derive(Default)]
pub struct State {
    dict: Vec<(String, Entry)>,
    heap: Vec<Cell>,
    code: Vec<Opcode>,
    debug_map: DebugMap,
    data_stack: Vec<Cell>,
    return_stack: Vec<Frame>,
    flow_stack: Vec<Flow>,
    loops: Vec<Loop>,
    ctx: Context,
    nested: Vec<Context>,
    state_rec: Option<Vec<StateChange>>,
    pub(crate) about_to_stop: bool,
    // current input binary
    pub(crate) bs_input: Xref,
    pub(crate) bs_isbig: Xref,
    pub(crate) bs_chunk: Xref,
    pub(crate) bs_flow: Xref,
    // default base
    pub(crate) base: Xref,
    // dump state
    pub(crate) dump_start: Xref,
}

impl State {

    pub fn error_context(&mut self, err: &Xerr) -> String {
        let mut error_text = format!("error: {:?}\n", err);
        if err == &Xerr::UnknownWord || err == &Xerr::InputParseError {
            if let Some(lex) = self.ctx.source.as_ref() {
                error_text.push_str(&format!("{:?}", lex.error_context()));
            }
        } else if let Some(loc) = self.debug_map.format_location(self.ip()) {
            error_text.push_str(&loc);
        }
        error_text
    }

    pub fn current_line(&self) -> String {
        let mut buf = String::new();
        if let Some(loc) = self.debug_map.format_location(self.ip()) {
            buf.push_str(&loc);
        }
        buf
    }

    pub fn set_binary_input(&mut self, path: &str) -> Xresult {
        let buf = std::fs::read(path).map_err(|e| {
            eprintln!("{}: {}", path, e.to_string());
            Xerr::IOError
        })?;
        let s = Xbitstr::from(buf);
        self.set_var(self.bs_input, Cell::Bitstr(s)).map(|_| ())
    }

    pub fn set_binary_input_data(&mut self, data: &[u8]) -> Xresult {
        let s = Xbitstr::from(data);
        self.set_var(self.bs_input, Cell::Bitstr(s)).map(|_| ())
    }

    pub fn load(&mut self, source: &str) -> Xresult {
        self.load_source(Lex::from_str(source))
    }

    pub fn load_source(&mut self, source: Lex) -> Xresult {
        self.context_open(ContextMode::Load, Some(source));
        let depth = self.nested.len();
        let result = self.build();
        if result.is_err() {
            if let Some(lex) = self.ctx.source.as_ref() {
                eprintln!("{:?}", lex.error_context());
            }
            while self.nested.len() > depth {
                self.context_close()?;
            }
        }
        result
    }

    pub fn interpret(&mut self, source: &str) -> Xresult {
        self.context_open(ContextMode::Eval, Some(Lex::from_str(source)));
        let depth = self.nested.len();
        let result = self.build();
        if let Err(e) = result.as_ref() {
            eprintln!("{}", self.error_context(e));
            while self.nested.len() > depth {
                self.context_close()?;
            }
        }
        result
    }

    fn build(&mut self) -> Xresult {
        loop {
            if self.ctx.mode != ContextMode::Load
                && !self.has_pending_flow()
                && self.ip() < self.code_origin()
            {
                self.run()?;
            }
            match self.next_token()? {
                Tok::EndOfInput => {
                    if self.has_pending_flow() {
                        break Err(Xerr::ControlFlowError);
                    }
                    if self.ip() < self.code_origin() {
                        if self.ctx.mode != ContextMode::Load {
                            self.run()?;
                        }
                    }
                    break self.context_close();
                }
                Tok::Num(n) => {
                    self.code_emit_value(Cell::Int(n))?;
                }
                Tok::Real(r) => {
                    self.code_emit_value(Cell::Real(r))?;
                }
                Tok::Str(s) => {
                    self.code_emit_value(Cell::Str(s))?;
                }
                Tok::Word(name) => {
                    let idx = match self.dict_find(&name) {
                        Some(idx) => idx,
                        None => {
                            let idx = self
                                .top_function_flow()
                                .and_then(|ff| ff.locals.iter().rposition(|x| x == &name))
                                .ok_or(Xerr::UnknownWord)?;
                            self.code_emit(Opcode::LoadLocal(idx), DebugInfo::Local(name))?;
                            continue;
                        }
                    };
                    match self.dict_at(idx).unwrap() {
                        Entry::Deferred => {
                            self.code_emit(Opcode::Deferred(idx), DebugInfo::Word(idx))?
                        }
                        Entry::Variable(a) => {
                            let a = *a;
                            self.code_emit(Opcode::Load(a), DebugInfo::Word(idx))?;
                        }
                        Entry::Function {
                            immediate: true,
                            xf,
                            ..
                        } => {
                            let xf = xf.clone();
                            self.call_fn(xf)?;
                        }
                        Entry::Function {
                            immediate: false,
                            xf: Xfn::Interp(x),
                            ..
                        } => {
                            let x = *x;
                            self.code_emit(Opcode::Call(x), DebugInfo::Word(idx))?;
                        }
                        Entry::Function {
                            immediate: false,
                            xf: Xfn::Native(x),
                            ..
                        } => {
                            let x = *x;
                            self.code_emit(Opcode::NativeCall(x), DebugInfo::Word(idx))?;
                        }
                    }
                }
            }
        }
    }

    fn next_token(&mut self) -> Xresult1<Tok> {
        if let Some(lex) = &mut self.ctx.source {
            lex.next()
        } else {
            Ok(Tok::EndOfInput)
        }
    }

    fn context_open(&mut self, mode: ContextMode, mut source: Option<Lex>) {
        if let Some(source) = source.as_mut() {
            let id = self.debug_map.add_buffer(source.buffer());
            source.set_source_id(id);
        }
        let mut tmp = Context {
            ds_len: 0,
            cs_len: self.code.len(),
            rs_len: self.return_stack.len(),
            fs_len: self.flow_stack.len(),
            ls_len: self.loops.len(),
            ip: self.code_origin(),
            mode,
            source,
        };
        if tmp.source.is_none() {
            // take source form previous context
            tmp.source = self.ctx.source.take();
        }
        if tmp.mode == ContextMode::Nested {
            // set bottom stack limit for nested interpreter
            tmp.ds_len = self.data_stack.len();
        }
        std::mem::swap(&mut self.ctx, &mut tmp);
        self.nested.push(tmp);
    }

    fn context_close(&mut self) -> Xresult {
        let mut prev_ctx = self.nested.pop().ok_or(Xerr::ControlFlowError)?;
        if prev_ctx.source.is_none() {
            // take source from current context
            prev_ctx.source = self.ctx.source.take();
        }
        if self.ctx.mode == ContextMode::Nested {
            // purge nested context code after evaluation
            self.code.truncate(self.ctx.cs_len);
            if prev_ctx.mode == ContextMode::Load {
                // compile evaluation result
                while self.data_stack.len() > self.ctx.ds_len {
                    let val = self.pop_data()?;
                    self.code_emit_value(val)?;
                }
            }
        }
        self.ctx = prev_ctx;
        OK
    }

    fn has_pending_flow(&self) -> bool {
        (self.flow_stack.len() - self.ctx.fs_len) > 0
    }

    pub fn new() -> Xresult1<State> {
        let mut xs = State::default();
        xs.base = xs.defvar("BASE", Cell::Int(10))?;
        xs.load_core()?;
        crate::bitstring_mod::bitstring_load(&mut xs)?;
        Ok(xs)
    }

    pub fn set_state_recording(&mut self, t: bool) {
        self.state_rec = if t { Some(Vec::default()) } else { None };
    }

    pub fn defvar(&mut self, name: &str, val: Cell) -> Xresult1<Xref> {
        // shadow previous definition
        let a = self.alloc_cell(val)?;
        self.dict_insert(name.to_string(), Entry::Variable(a))?;
        Ok(Xref::Heap(a))
    }

    pub fn get_var_by_name(&self, name: &str) -> Xresult1<&Cell> {
        let e = self.dict_find(name)
                    .and_then(|idx| self.dict_at(idx))
                    .ok_or(Xerr::UnknownWord)?;
        match e {
            Entry::Variable(a) => self.get_var(Xref::Heap(*a)),
            Entry::Function{..} => Err(Xerr::ReadonlyAddress),
            Entry::Deferred => Err(Xerr::UnknownWord),
        }        
    }

    pub fn get_var(&self, xref: Xref) -> Xresult1<&Cell> {
        match xref {
            Xref::Heap(a) => self.heap.get(a).ok_or(Xerr::InvalidAddress),
            _ => Err(Xerr::InvalidAddress),
        }
    }

    pub fn set_var(&mut self, xref: Xref, mut val: Cell) -> Xresult1<Cell> {
        match xref {
            Xref::Heap(a) => {
                let x = self.heap.get_mut(a).ok_or(Xerr::InvalidAddress)?;
                std::mem::swap(&mut val, x);
                Ok(val)
            },
            _ => Err(Xerr::InvalidAddress),
        }
    }

    pub fn defword(&mut self, name: &str, x: XfnType) -> Xresult1<Xref> {
        let xf = Xfn::Native(XfnPtr(x));
        let idx = self.dict_insert(
            name.to_string(),
            Entry::Function {
                immediate: false,
                xf,
                len: Some(0),
            },
        )?;
        Ok(Xref::Word(idx))
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
            Def("immediate", core_word_immediate),
            Def("local", core_word_def_local),
            Def("var", core_word_variable),
            Def("->", core_word_setvar),
            Def("nil", core_word_nil),
            Def("(", core_word_nested_begin),
            Def(")", core_word_nested_end),
            Def("execute", core_word_execute),
            Def("defer", core_word_defer),
            Def("do", core_word_do),
            Def("loop", core_word_loop),
            Def("breakpoint", core_word_breakpoint),
        ]
        .iter()
        {
            core_insert_word(self, i.0, i.1, true)?;
        }
        for i in [
            Def("I", core_word_counter_i),
            Def("J", core_word_counter_j),
            Def("K", core_word_counter_k),
            Def("length", core_word_length),
            Def("get", core_word_get),
            Def("assoc", core_word_assoc),
            Def("dup", |xs| xs.dup_data()),
            Def("drop", |xs| xs.drop_data()),
            Def("swap", |xs| xs.swap_data()),
            Def("rot", |xs| xs.rot_data()),
            Def("over", |xs| xs.over_data()),
            Def("+", core_word_add),
            Def("-", core_word_sub),
            Def("*", core_word_mul),
            Def("/", core_word_div),
            Def("neg", core_word_negate),
            Def("abs", core_word_abs),
            Def("inc", core_word_inc),
            Def("dec", core_word_dec),
            Def("<", core_word_less_then),
            Def("=", core_word_eq),
            Def("rem", core_word_rem),
            Def("band", core_word_bitand),
            Def("bor", core_word_bitor),
            Def("bxor", core_word_bitxor),
            Def("bshl", core_word_bitshl),
            Def("bshr", core_word_bitshr),
            Def("bnot", core_word_bitnot),
            Def("random", core_word_random),
            Def("round", core_word_round),
            Def("assert", core_word_assert),
            Def("assert-eq", core_word_assert_eq),
            Def("bye", core_word_bye),
            Def(".", core_word_println),
            Def("println", core_word_println),
            Def("print", core_word_print),
            Def("newline", core_word_newline),
            Def("HEX", core_word_hex),
            Def("DEC", core_word_decimal),
            Def("OCT", core_word_octal),
            Def("BIN", core_word_binary),
        ]
        .iter()
        {
            core_insert_word(self, i.0, i.1, false)?;
        }
        OK
    }

    fn dict_insert(&mut self, name: String, e: Entry) -> Xresult1<usize> {
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

    fn code_origin(&self) -> usize {
        self.code.len()
    }

    fn code_emit_value(&mut self, val: Cell) -> Xresult {
        match val {
            Cell::Int(i) => self.code_emit(Opcode::LoadInt(i), DebugInfo::Empty),
            Cell::Ref(p) => self.code_emit(Opcode::LoadRef(p), DebugInfo::Empty),
            Cell::Nil => self.code_emit(Opcode::LoadNil, DebugInfo::Empty),
            val => {
                let a = self.alloc_cell(val)?;
                self.code_emit(Opcode::Load(a), DebugInfo::Empty)
            }
        }
    }

    fn code_emit(&mut self, op: Opcode, dinfo: DebugInfo) -> Xresult {
        let at = self.code.len();
        let lex = self.ctx.source.as_ref();
        self.debug_map.insert_with_source(at, dinfo, lex);
        self.code.push(op);
        OK
    }

    fn patch_insn(&mut self, at: usize, insn: Opcode) -> Xresult {
        self.code[at] = insn;
        OK
    }

    fn patch_jump(&mut self, at: usize, offs: isize) -> Xresult {
        let insn = match self.code.get(at).ok_or(Xerr::InternalError)? {
            Opcode::Jump(_) => Opcode::Jump(offs),
            Opcode::JumpIf(_) => Opcode::JumpIf(offs),
            Opcode::JumpIfNot(_) => Opcode::JumpIfNot(offs),
            _ => panic!("not a jump instruction at={}", at),
        };
        self.patch_insn(at, insn)
    }

    fn alloc_cell(&mut self, val: Cell) -> Xresult1<usize> {
        let a = self.heap.len();
        self.heap.push(val);
        Ok(a)
    }

    fn call_fn(&mut self, x: Xfn) -> Xresult {
        match x {
            Xfn::Native(x) => x.0(self),
            Xfn::Interp(x) => {
                let old_ip = self.ip();
                self.push_return(old_ip)?;
                self.set_ip(x)?;
                self.run()
            }
        }
    }

    pub fn run(&mut self) -> Xresult {
        while self.ip() < self.code.len() {
            self.next()?;
        }
        OK
    }

    pub fn next(&mut self) -> Xresult {
        let ip = self.ip();
        match self.code.get(ip).cloned().ok_or(Xerr::InternalError)? {
            Opcode::Break => {
                self.next_ip()?;
                Err(Xerr::DebugBreak)
            }
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
            Opcode::NativeCall(x) => {
                x.0(self)?;
                self.next_ip()
            }
            Opcode::Ret => {
                let frame = self.pop_return()?;
                self.set_ip(frame.return_to)
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
            Opcode::LoadInt(n) => {
                self.push_data(Cell::Int(n))?;
                self.next_ip()
            }
            Opcode::LoadRef(xr) => {
                self.push_data(Cell::Ref(xr))?;
                self.next_ip()
            }
            Opcode::LoadNil => {
                self.push_data(Cell::Nil)?;
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
            Opcode::InitLocal(i) => {
                let val = self.pop_data()?;
                let frame = self.top_frame().ok_or(Xerr::ReturnStackUnderflow)?;
                assert_eq!(i, frame.locals.len());
                frame.locals.push(val);
                self.next_ip()
            }
            Opcode::LoadLocal(i) => {
                let frame = self.top_frame().ok_or(Xerr::ReturnStackUnderflow)?;
                let val = frame.locals.get(i).cloned().ok_or(Xerr::InvalidAddress)?;
                self.push_data(val)?;
                self.next_ip()
            }
        }
    }

    pub fn rnext(&mut self) -> Xresult {
        if let Some(rec) = self.state_rec.as_mut() {
            match rec.pop() {
                None => (),
                Some(StateChange::DecrementIp) => {
                    if self.ctx.ip > 0 {
                        self.ctx.ip -= 1;
                    }
                }
                Some(StateChange::SetIp(ip)) => {
                    self.ctx.ip = ip;
                }
                Some(StateChange::PopData) => {
                    if self.data_stack.len() > self.ctx.ds_len {
                        self.data_stack.pop();
                    } else {
                        return Err(Xerr::StackUnderflow);
                    }
                }
                Some(StateChange::PushData(val)) => {
                    self.data_stack.push(val);
                }
                Some(StateChange::SwapData) => {
                    let len = self.data_stack.len();
                    if (len - self.ctx.ds_len) >= 2 {
                        self.data_stack.swap(len - 1, len - 2);
                    } else {
                        return Err(Xerr::StackUnderflow);
                    }
                }
                Some(StateChange::RotData) => {
                    let len = self.data_stack.len();
                    if (len - self.ctx.ds_len) >= 3 {
                        self.data_stack.swap(len - 1, len - 3);
                    } else {
                        return Err(Xerr::StackUnderflow);
                    }
                }
                Some(StateChange::OverData) => {
                    self.drop_data()?;
                }
                Some(StateChange::PopReturn) => {
                    if self.return_stack.len() > self.ctx.rs_len {
                        self.return_stack.pop();
                    } else {
                        return Err(Xerr::ReturnStackUnderflow);
                    }
                }
                Some(StateChange::PushReturn(frame)) => {
                    self.return_stack.push(frame);
                }
                Some(StateChange::PushLoop(l)) => {
                    self.loops.push(l);
                }
                Some(StateChange::PopLoop) => {
                    if self.loops.len() > self.ctx.ls_len {
                        self.loops.pop();
                    } else {
                        return Err(Xerr::LoopStackUnderflow);
                    }
                }
            }
        }
        OK
    }

    fn jump_to(&mut self, offs: isize) -> Xresult {
        let new_ip = (self.ip() as isize + offs) as usize;
        self.set_ip(new_ip)
    }

    fn jump_if(&mut self, t: bool, offs: isize) -> Xresult {
        if t {
            self.jump_to(offs)
        } else {
            self.next_ip()
        }
    }

    pub fn ip(&self) -> usize {
        self.ctx.ip
    }

    fn set_ip(&mut self, new_ip: usize) -> Xresult {
        if let Some(rec) = self.state_rec.as_mut() {
            journal_state_change(rec, StateChange::SetIp(self.ctx.ip));
        }
        self.ctx.ip = new_ip;
        OK
    }

    fn next_ip(&mut self) -> Xresult {
        if let Some(rec) = self.state_rec.as_mut() {
            journal_state_change(rec, StateChange::DecrementIp);
        }
        self.ctx.ip += 1;
        OK
    }

    fn pop_flow(&mut self) -> Xresult1<Flow> {
        if self.flow_stack.len() > self.ctx.fs_len {
            self.flow_stack.pop().ok_or(Xerr::ControlFlowError)
        } else {
            Err(Xerr::ControlFlowError)
        }
    }

    fn push_flow(&mut self, flow: Flow) -> Xresult {
        self.flow_stack.push(flow);
        OK
    }

    fn top_function_flow(&mut self) -> Option<&mut FunctionFlow> {
        self.flow_stack[self.ctx.fs_len..]
            .iter_mut()
            .rev()
            .find_map(|i| match i {
                Flow::Fun(ref mut ff) => Some(ff),
                _ => None,
            })
    }

    fn dropn(&mut self, n: usize) -> Xresult {
        let ds_len = self.data_stack.len() - self.ctx.ds_len;
        if ds_len < n {
            Err(Xerr::StackUnderflow)
        } else {
            self.data_stack.truncate(ds_len - n);
            OK
        }
    }

    pub fn push_data(&mut self, data: Cell) -> Xresult {
        if let Some(rec) = self.state_rec.as_mut() {
            journal_state_change(rec, StateChange::PopData);
        }
        self.data_stack.push(data);
        OK
    }

    pub fn pop_data(&mut self) -> Xresult1<Cell> {
        if self.data_stack.len() > self.ctx.ds_len {
            let val = self.data_stack.pop().ok_or(Xerr::StackUnderflow)?;
            if let Some(rec) = self.state_rec.as_mut() {
                journal_state_change(rec, StateChange::PushData(val.clone()));
            }
            Ok(val)
        } else {
            Err(Xerr::StackUnderflow)
        }
    }

    pub fn get_data(&self, idx: usize) -> Option<&Cell> {
        self.data_stack.iter().rev().nth(idx)
    }

    pub fn top_data(&self) -> Option<&Cell> {
        if self.data_stack.len() > self.ctx.ds_len {
            self.data_stack.last()
        } else {
            None
        }
    }

    fn drop_data(&mut self) -> Xresult {
        self.pop_data()?;
        OK
    }

    fn dup_data(&mut self) -> Xresult {
        let val = self.top_data().ok_or(Xerr::StackUnderflow)?.clone();
        self.push_data(val)
    }

    fn swap_data(&mut self) -> Xresult {
        let len = self.data_stack.len();
        if (len - self.ctx.ds_len) >= 2 {
            if let Some(rec) = self.state_rec.as_mut() {
                journal_state_change(rec, StateChange::SwapData);
            }
            self.data_stack.swap(len - 1, len - 2);
            OK
        } else {
            Err(Xerr::StackUnderflow)
        }
    }

    fn rot_data(&mut self) -> Xresult {
        let len = self.data_stack.len();
        if (len - self.ctx.ds_len) >= 3 {
            if let Some(rec) = self.state_rec.as_mut() {
                journal_state_change(rec, StateChange::RotData);
            }
            self.data_stack.swap(len - 1, len - 3);
            OK
        } else {
            Err(Xerr::StackUnderflow)
        }
    }

    fn over_data(&mut self) -> Xresult {
        let len = self.data_stack.len();
        if (len - self.ctx.ds_len) >= 2 {
            if let Some(rec) = self.state_rec.as_mut() {
                journal_state_change(rec, StateChange::OverData);
            }
            let val = self.data_stack[len - 2].clone();
            self.push_data(val)
        } else {
            Err(Xerr::StackUnderflow)
        }
    }

    fn push_return(&mut self, return_to: usize) -> Xresult {
        if let Some(rec) = self.state_rec.as_mut() {
            journal_state_change(rec, StateChange::PopReturn);
        }
        self.return_stack.push(Frame::from_addr(return_to));
        OK
    }

    fn pop_return(&mut self) -> Xresult1<Frame> {
        if self.return_stack.len() > self.ctx.rs_len {
            let ret = self.return_stack.pop().ok_or(Xerr::ReturnStackUnderflow)?;
            if let Some(rec) = self.state_rec.as_mut() {
                journal_state_change(rec, StateChange::PushReturn(ret.clone()));
            }
            Ok(ret)
        } else {
            Err(Xerr::ReturnStackUnderflow)
        }
    }

    fn top_frame(&mut self) -> Option<&mut Frame> {
        if self.return_stack.len() > self.ctx.rs_len {
            self.return_stack.last_mut()
        } else {
            None
        }
    }

    fn push_loop(&mut self, l: Loop) -> Xresult {
        if let Some(rec) = self.state_rec.as_mut() {
            journal_state_change(rec, StateChange::PopLoop);
        }
        self.loops.push(l);
        OK
    }

    fn top_loop(&self) -> Result<&Loop, Xerr> {
        if self.loops.len() > self.ctx.ls_len {
            self.loops.last().ok_or(Xerr::LoopStackUnderflow)
        } else {
            Err(Xerr::LoopStackUnderflow)
        }
    }

    fn pop_loop(&mut self) -> Xresult1<Loop> {
        if self.loops.len() > self.ctx.ls_len {
            let l = self.loops.pop().ok_or(Xerr::LoopStackUnderflow)?;
            if let Some(rec) = self.state_rec.as_mut() {
                journal_state_change(rec, StateChange::PushLoop(l.clone()));
            }
            Ok(l)
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
            xf: Xfn::Native(XfnPtr(x)),
            len: None,
        },
    )?;
    OK
}

fn take_if_flow(xs: &mut State) -> Xresult1<usize> {
    for (i, f) in xs.flow_stack[xs.ctx.fs_len..].iter().rev().enumerate() {
        match f {
            Flow::If(if_org) => {
                let org = *if_org;
                let pos = xs.flow_stack.len() - (i + 1);
                xs.flow_stack.remove(pos);
                return Ok(org);
            }
            Flow::Leave(_) => continue,
            _ => break,
        }
    }
    return Err(Xerr::ControlFlowError);
}

fn core_word_if(xs: &mut State) -> Xresult {
    let fwd = Flow::If(xs.code_origin());
    xs.code_emit(Opcode::JumpIfNot(0), DebugInfo::Comment("if"))?;
    xs.push_flow(fwd)
}

fn core_word_else(xs: &mut State) -> Xresult {
    let if_org = take_if_flow(xs)?;
    let fwd = Flow::If(xs.code_origin());
    xs.code_emit(Opcode::Jump(0), DebugInfo::Comment("else"))?;
    xs.push_flow(fwd)?;
    let offs = jump_offset(if_org, xs.code_origin());
    xs.patch_jump(if_org, offs)
}

fn core_word_then(xs: &mut State) -> Xresult {
    let if_org = take_if_flow(xs)?;
    let offs = jump_offset(if_org, xs.code_origin());
    xs.patch_jump(if_org, offs)
}

fn core_word_begin(xs: &mut State) -> Xresult {
    xs.push_flow(Flow::Begin(xs.code_origin()))
}

fn core_word_until(xs: &mut State) -> Xresult {
    match xs.pop_flow()? {
        Flow::Begin(begin_org) => {
            let offs = jump_offset(xs.code_origin(), begin_org);
            xs.code_emit(Opcode::JumpIf(offs), DebugInfo::Comment("until"))
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_while(xs: &mut State) -> Xresult {
    let cond = Flow::While(xs.code_origin());
    xs.code_emit(Opcode::JumpIfNot(0), DebugInfo::Comment("while"))?;
    xs.push_flow(cond)
}

fn core_word_again(xs: &mut State) -> Xresult {
    loop {
        match xs.pop_flow()? {
            Flow::Leave(leave_org) => {
                let offs = jump_offset(leave_org, xs.code_origin() + 1);
                xs.patch_jump(leave_org, offs)?;
            }
            Flow::Begin(begin_org) => {
                let offs = jump_offset(xs.code_origin(), begin_org);
                break xs.code_emit(Opcode::Jump(offs), DebugInfo::Comment("again"));
            }
            _ => break Err(Xerr::ControlFlowError),
        }
    }
}

fn core_word_repeat(xs: &mut State) -> Xresult {
    loop {
        match xs.pop_flow()? {
            Flow::Leave(leave_org) => {
                let offs = jump_offset(leave_org, xs.code_origin() + 1);
                xs.patch_jump(leave_org, offs)?;
            }
            Flow::While(cond_org) => match xs.pop_flow()? {
                Flow::Begin(begin_org) => {
                    let offs = jump_offset(cond_org, xs.code_origin() + 1);
                    xs.patch_jump(cond_org, offs)?;
                    let offs = jump_offset(xs.code_origin(), begin_org);
                    break xs.code_emit(Opcode::Jump(offs), DebugInfo::Comment("repeat"));
                }
                _ => break Err(Xerr::ControlFlowError),
            },
            _ => break Err(Xerr::ControlFlowError),
        }
    }
}

fn core_word_leave(xs: &mut State) -> Xresult {
    let leave = Flow::Leave(xs.code_origin());
    xs.code_emit(Opcode::Jump(0), DebugInfo::Comment("leave"))?;
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
    xs.code_emit(
        Opcode::NativeCall(XfnPtr(vec_builder_begin)),
        DebugInfo::Comment("["),
    )
}

fn core_word_vec_end(xs: &mut State) -> Xresult {
    match xs.pop_flow()? {
        Flow::Vec => xs.code_emit(Opcode::NativeCall(XfnPtr(vec_builder_end)),
                                  DebugInfo::Comment("]")),
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
    xs.code_emit(
        Opcode::NativeCall(XfnPtr(map_builder_begin)),
        DebugInfo::Comment("{"),
    )
}

fn core_word_map_end(xs: &mut State) -> Xresult {
    match xs.pop_flow()? {
        Flow::Map => xs.code_emit(Opcode::NativeCall(XfnPtr(map_builder_end)),
                                  DebugInfo::Comment("}")),
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
    let start = xs.code_origin();
    // jump over function body
    xs.code_emit(Opcode::Jump(0), DebugInfo::Comment(":"))?;
    // function starts right after jump
    let xf = Xfn::Interp(xs.code_origin());
    let dict_idx = xs.dict_insert(
        name,
        Entry::Function {
            immediate: false,
            xf,
            len: None,
        },
    )?;
    xs.push_flow(Flow::Fun(FunctionFlow {
        dict_idx,
        start,
        locals: Default::default(),
    }))
}

fn core_word_def_end(xs: &mut State) -> Xresult {
    match xs.pop_flow()? {
        Flow::Fun(FunctionFlow {
            start, dict_idx, ..
        }) => {
            xs.code_emit(Opcode::Ret, DebugInfo::Comment(";"))?;
            let offs = jump_offset(start, xs.code_origin());
            let fun_len = xs.code_origin() - start;
            match xs.dict.get_mut(dict_idx).ok_or(Xerr::InvalidAddress)? {
                (_, Entry::Function { ref mut len, .. }) => *len = Some(fun_len),
                _ => panic!("entry type"),
            }
            xs.patch_jump(start, offs)
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_immediate(xs: &mut State) -> Xresult {
    let dict_idx = xs
        .top_function_flow()
        .map(|f| f.dict_idx)
        .ok_or(Xerr::ControlFlowError)?;
    match xs.dict.get_mut(dict_idx).ok_or(Xerr::InvalidAddress)?.1 {
        Entry::Function {
            ref mut immediate, ..
        } => {
            *immediate = true;
            OK
        }
        _ => panic!("entry type"),
    }
}

fn core_word_def_local(xs: &mut State) -> Xresult {
    let name = match xs.next_token()? {
        Tok::Word(name) => name,
        _ => return Err(Xerr::ExpectingName),
    };
    let ff = xs.top_function_flow().ok_or(Xerr::ControlFlowError)?;
    let dinfo = DebugInfo::Local(name.clone());
    let idx = ff.locals.len();
    ff.locals.push(name);
    xs.code_emit(Opcode::InitLocal(idx), dinfo)
}

fn core_word_variable(xs: &mut State) -> Xresult {
    let name = match xs.next_token()? {
        Tok::Word(name) => name,
        _other => return Err(Xerr::ExpectingName),
    };
    let a = if xs.ctx.mode == ContextMode::Load {
        let a = xs.alloc_cell(Cell::Nil)?;
        xs.code_emit(Opcode::Store(a), DebugInfo::Empty)?;
        a
    } else {
        let val = xs.pop_data()?;
        xs.alloc_cell(val)?
    };
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
            xs.code_emit(Opcode::Store(a), DebugInfo::Word(a))
        }
        _ => Err(Xerr::ReadonlyAddress),
    }
}

fn core_word_nil(xs: &mut State) -> Xresult {
    if xs.ctx.mode == ContextMode::Load {
        xs.code_emit(Opcode::LoadNil, DebugInfo::Empty)
    } else {
        xs.push_data(Cell::Nil)
    }
}

fn core_word_nested_begin(xs: &mut State) -> Xresult {
    xs.context_open(ContextMode::Nested, None);
    OK
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

pub fn format_opcode(xs: &State, at: usize) -> String {
    let jumpaddr = |ip, offs| (ip as isize + offs) as usize;
    let debug_comment = xs
        .debug_map
        .find_debug_info(at)
        .map(|di| match di {
            DebugInfo::Empty => "",
            DebugInfo::Comment(text) => text,
            DebugInfo::Local(name) => name.as_str(),
            DebugInfo::Word(a) => xs
                .dict
                .get(*a)
                .map(|e| e.0.as_str())
                .unwrap_or("<entry not found>"),
        })
        .unwrap_or("");
    format!(
        "{:08x}{}{:<30} # {}",
        at,
        if xs.ip() == at { " * " } else { "   " },
        match &xs.code[at] {
            Opcode::Break => format!("break"),
            Opcode::Call(a) => format!("call       {:#x}", a),
            Opcode::Deferred(a) => format!("defer      {:#x}", a),
            Opcode::NativeCall(x) => format!("callx      {:#x}", x.0 as usize),
            Opcode::Ret => format!("ret"),
            Opcode::JumpIf(offs) => format!("jumpif     ${:05x}", jumpaddr(at, offs)),
            Opcode::JumpIfNot(offs) => format!("jumpifnot  ${:05x}", jumpaddr(at, offs)),
            Opcode::Jump(offs) => format!("jump       ${:05x}", jumpaddr(at, offs)),
            Opcode::Load(a) => format!("load       {}", a),
            Opcode::LoadInt(i) => format!("loadint    {}", i),
            Opcode::LoadRef(a) => format!("loadref    {:?}", a),
            Opcode::LoadNil => format!("loadnil"),
            Opcode::Store(a) => format!("store      {}", a),
            Opcode::InitLocal(i) => format!("initlocal  {}", i),
            Opcode::LoadLocal(i) => format!("loadlocal  {}", i),
        },
        debug_comment,
    )
}

fn core_word_execute(xs: &mut State) -> Xresult {
    match xs.pop_data()? {
        Cell::Fun(x) => xs.call_fn(x),
        _ => Err(Xerr::TypeError),
    }
}

fn core_word_defer(xs: &mut State) -> Xresult {
    let name = match xs.next_token()? {
        Tok::Word(name) => name,
        _ => return Err(Xerr::ExpectingName),
    };
    if xs.dict_find(&name).is_none() {
        xs.dict_insert(name, Entry::Deferred)?;
    }
    OK
}

fn core_word_do_init(xs: &mut State) -> Xresult {
    let start = xs.pop_data()?.into_int()?;
    let end = xs.pop_data()?.into_int()?;
    xs.push_loop(Loop::Do { start, end })
}

fn core_word_do_test(xs: &mut State) -> Xresult {
    match xs.top_loop()? {
        Loop::Do { start, end } if start < end => xs.push_data(ONE),
        _ => xs.push_data(ZERO),
    }
}

fn core_word_do(xs: &mut State) -> Xresult {
    xs.code_emit(
        Opcode::NativeCall(XfnPtr(core_word_do_init)),
        DebugInfo::Comment("do init"),
    )?;
    let test_org = xs.code_origin();
    xs.code_emit(
        Opcode::NativeCall(XfnPtr(core_word_do_test)),
        DebugInfo::Comment("do test"),
    )?;
    let jump_org = xs.code_origin();
    xs.code_emit(Opcode::JumpIfNot(0), DebugInfo::Comment("do"))?;
    xs.push_flow(Flow::Do { test_org, jump_org })
}

fn core_word_loop_inc(xs: &mut State) -> Xresult {
    match xs.pop_loop()? {
        Loop::Do { start, end } => xs.push_loop(Loop::Do {
            start: start + 1,
            end,
        }),
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_loop_leave(xs: &mut State) -> Xresult {
    match xs.pop_loop()? {
        Loop::Do { .. } => OK,
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_loop(xs: &mut State) -> Xresult {
    xs.code_emit(
        Opcode::NativeCall(XfnPtr(core_word_loop_inc)),
        DebugInfo::Comment("loop increment counter"),
    )?;
    let next_org = xs.code_origin();
    xs.code_emit(Opcode::Jump(0), DebugInfo::Comment("loop"))?;
    let break_org = xs.code_origin();
    xs.code_emit(
        Opcode::NativeCall(XfnPtr(core_word_loop_leave)),
        DebugInfo::Comment("loop leave"),
    )?;
    loop {
        match xs.pop_flow()? {
            Flow::Leave(leave_org) => {
                let offs = jump_offset(leave_org, break_org);
                xs.patch_jump(leave_org, offs)?;
            }
            Flow::Do { test_org, jump_org } => {
                let offs = jump_offset(test_org, next_org);
                xs.patch_jump(jump_org, offs)?;
                let offs = jump_offset(next_org, test_org);
                break xs.patch_jump(next_org, offs);
            }
            _ => break Err(Xerr::ControlFlowError),
        }
    }
}

fn counter_value(xs: &mut State, n: usize) -> Xresult {
    match &xs.loops[xs.ctx.ls_len..].iter().nth_back(n) {
        Some(Loop::Do { start, .. }) => {
            let val = *start;
            xs.push_data(Cell::Int(val))
        }
        _ => Err(Xerr::LoopStackUnderflow),
    }
}

fn core_word_counter_i(xs: &mut State) -> Xresult {
    counter_value(xs, 0)
}

fn core_word_counter_j(xs: &mut State) -> Xresult {
    counter_value(xs, 1)
}

fn core_word_counter_k(xs: &mut State) -> Xresult {
    counter_value(xs, 2)
}

fn core_word_length(xs: &mut State) -> Xresult {
    match xs.pop_data()? {
        Cell::Vector(x) => xs.push_data(Cell::from(x.len())),
        Cell::Map(x) => xs.push_data(Cell::from(x.len())),
        Cell::Str(x) => xs.push_data(Cell::from(x.len())),
        _ => Err(Xerr::TypeError),
    }
}

fn core_word_get(xs: &mut State) -> Xresult {
    match xs.pop_data()? {
        Cell::Vector(x) => {
            let idx = xs.pop_data()?.into_usize()?;
            let val = x.get(idx).ok_or(Xerr::OutOfBounds)?;
            xs.push_data(val.clone())
        }
        Cell::Map(x) => {
            let k = xs.pop_data()?;
            let val = x
                .iter()
                .find(|kv| kv.0 == k)
                .map(|kv| kv.1.clone())
                .unwrap_or(Cell::Nil);
            xs.push_data(val.clone())
        }
        Cell::Str(_x) => {
            todo!("index string")
            // let idx = k.into_usize()?;
            // let val = x.chars().nth(idx).ok_or(Xerr::OutOfBounds)?;
            // xs.push_data(val.clone())
        }
        _ => Err(Xerr::TypeError),
    }
}

fn core_word_assoc(xs: &mut State) -> Xresult {
    match xs.pop_data()? {
        Cell::Vector(mut x) => {
            let idx = xs.pop_data()?.into_usize()?;
            let v = xs.pop_data()?;
            if x.set_mut(idx, v) {
                xs.push_data(Cell::Vector(x))
            } else {
                Err(Xerr::OutOfBounds)
            }
        }
        Cell::Map(mut x) => {
            let k = xs.pop_data()?;
            let v = xs.pop_data()?;
            if let Some(idx) = x.iter().position(|kv| kv.0 == k) {
                if !x.set_mut(idx, (k, v)) {
                    panic!("assoc failed");
                }
                xs.push_data(Cell::Map(x))
            } else {
                x.push_back_mut((k, v));
                xs.push_data(Cell::Map(x))
            }
        }
        _ => Err(Xerr::TypeError),
    }
}

fn core_word_assert(xs: &mut State) -> Xresult {
    if xs.pop_data()?.is_true() {
        OK
    } else {
        Err(Xerr::DebugAssertion)
    }
}

fn core_word_assert_eq(xs: &mut State) -> Xresult {
    let a = xs.get_data(0).ok_or(Xerr::StackUnderflow)?;
    let b = xs.get_data(1).ok_or(Xerr::StackUnderflow)?;
    if a == b {
        xs.pop_data()?;
        xs.pop_data()?;
        OK
    } else {
        eprintln!("[0]: {:?}", a);
        eprintln!("[1]: {:?}", b);
        Err(Xerr::DebugAssertion)
    }
}

fn core_word_bye(xs: &mut State) -> Xresult {
    xs.about_to_stop = true;
    core_word_breakpoint(xs)
}

fn core_word_println(xs: &mut State) -> Xresult {
    core_word_print(xs)?;
    core_word_newline(xs)
}

fn core_word_print(xs: &mut State) -> Xresult {
    let val = xs.pop_data()?;
    match xs.get_var(xs.base)? {
        Cell::Int(2) => print!("{:2?}", val),
        Cell::Int(16) => print!("{:16?}", val),
        _ => print!("{:10?}", val),
    };
    OK
}

fn core_word_newline(_xs: &mut State) -> Xresult {
    println!("");
    OK
}

fn core_word_hex(xs: &mut State) -> Xresult {
    xs.set_var(xs.base, Cell::Int(16)).map(|_| ())
}

fn core_word_decimal(xs: &mut State) -> Xresult {
    xs.set_var(xs.base, Cell::Int(10)).map(|_| ())
}

fn core_word_octal(xs: &mut State) -> Xresult {
    xs.set_var(xs.base, Cell::Int(8)).map(|_| ())
}

fn core_word_binary(xs: &mut State) -> Xresult {
    xs.set_var(xs.base, Cell::Int(2)).map(|_| ())
}

fn core_word_breakpoint(xs: &mut State) -> Xresult {
    if xs.ctx.mode == ContextMode::Load {
        xs.code_emit(Opcode::Break, DebugInfo::Empty)
    } else {
        Err(Xerr::DebugBreak)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_jump_offset() {
        assert_eq!(2, jump_offset(2, 4));
        assert_eq!(-2, jump_offset(4, 2));
    }

    #[test]
    fn test_data_stack() {
        let mut xs = State::new().unwrap();
        xs.interpret("1 \"s\" 2").unwrap();
        xs.interpret("dup").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        xs.interpret("drop").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        let res = xs.interpret("drop");
        assert_eq!(Err(Xerr::StackUnderflow), res);
        let res = xs.interpret("dup");
        assert_eq!(Err(Xerr::StackUnderflow), res);
        xs.interpret("5 6 swap").unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(6)), xs.pop_data());
        assert_eq!(Err(Xerr::StackUnderflow), xs.interpret("1 (2 swap)"));
        let mut xs = State::new().unwrap();
        assert_eq!(Err(Xerr::StackUnderflow), xs.interpret("1 swap"));
        let mut xs = State::new().unwrap();
        xs.interpret("1 2 3 rot").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(3)), xs.pop_data());
        let mut xs = State::new().unwrap();
        assert_eq!(Err(Xerr::StackUnderflow), xs.interpret("1 (2 3 rot)"));
        let mut xs = State::new().unwrap();
        xs.interpret("1 2 over").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        assert_eq!(Err(Xerr::StackUnderflow), xs.interpret("1 over"));
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
        xs.load("begin 5 while 1 2 repeat").unwrap();
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
        xs.load("0 begin 1 2 until").unwrap();
        let mut it = xs.code.iter();
        it.next().unwrap();
        it.next().unwrap();
        it.next().unwrap();
        assert_eq!(&Opcode::JumpIf(-2), it.next().unwrap());
        xs.interpret("1 var x begin x while 0 -> x repeat").unwrap();
        assert_eq!(Err(Xerr::ControlFlowError), xs.load("if begin then repeat"));
        assert_eq!(Err(Xerr::ControlFlowError), xs.load("repeat begin"));
        assert_eq!(Err(Xerr::ControlFlowError), xs.load("begin then while"));
        assert_eq!(Err(Xerr::ControlFlowError), xs.load("until begin"));
        assert_eq!(Err(Xerr::ControlFlowError), xs.load("begin repeat until"));
        assert_eq!(Err(Xerr::ControlFlowError), xs.load("begin until repeat"));
    }

    #[test]
    fn test_length() {
        let mut xs = State::new().unwrap();
        xs.interpret("[1 2 3] length").unwrap();
        assert_eq!(Ok(Cell::Int(3)), xs.pop_data());
        xs.interpret("{\"a\" 1 \"b\" 1 } length").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        xs.interpret("\"12345\" length").unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
        let mut xs = State::new().unwrap();
        let res = xs.interpret("length");
        assert_eq!(Err(Xerr::StackUnderflow), res);
        let res = xs.interpret("1 length");
        assert_eq!(Err(Xerr::TypeError), res);
    }

    #[test]
    fn test_loop_leave() {
        let mut xs = State::new().unwrap();
        xs.interpret("begin 1 leave again").unwrap();
        let x = xs.pop_data().unwrap();
        assert_eq!(x.into_int(), Ok(1));
        assert_eq!(Err(Xerr::StackUnderflow), xs.pop_data());
        let mut xs = State::new().unwrap();
        let res = xs.load("begin 1 again leave");
        assert_eq!(Err(Xerr::ControlFlowError), res);
        let mut xs = State::new().unwrap();
        xs.load("begin 1 if leave else leave then again").unwrap();
    }

    #[test]
    fn test_do_loop() {
        let mut xs = State::new().unwrap();
        xs.interpret("10 0 do I loop").unwrap();
        for i in (0..10).rev() {
            assert_eq!(Ok(Cell::Int(i)), xs.pop_data());
        }
        let mut xs = State::new().unwrap();
        xs.interpret("102 100 do 12 10 do 2 0 do I J K loop loop loop")
            .unwrap();
        for i in (100..102).rev() {
            for j in (10..12).rev() {
                for k in (0..2).rev() {
                    assert_eq!(Cell::Int(i), xs.pop_data().unwrap());
                    assert_eq!(Cell::Int(j), xs.pop_data().unwrap());
                    assert_eq!(Cell::Int(k), xs.pop_data().unwrap());
                }
            }
        }
    }

    #[test]
    fn test_get_assoc() {
        let mut xs = State::new().unwrap();
        xs.interpret("55 0 [11 22] assoc").unwrap();
        let v = xs.pop_data().unwrap().into_vector().unwrap();
        assert_eq!(Some(&Cell::Int(55)), v.get(0));
        assert_eq!(Some(&Cell::Int(22)), v.get(1));
        assert_eq!(Err(Xerr::OutOfBounds), xs.interpret("55 2 [11 22] assoc"));
        assert_eq!(Err(Xerr::OutOfBounds), xs.interpret("2 [11 22] get"));
        xs.interpret("1 [33 44] get").unwrap();
        assert_eq!(Ok(Cell::Int(44)), xs.pop_data());
        xs.interpret("3 \"a\" {\"a\" 1} assoc ").unwrap();
        let m = xs.pop_data().unwrap().into_map().unwrap();
        assert_eq!(
            &(Cell::Str("a".to_string()), Cell::Int(3)),
            m.first().unwrap()
        );
        xs.interpret("\"a\" {\"a\" 22} get").unwrap();
        assert_eq!(Cell::Int(22), xs.pop_data().unwrap());
        xs.interpret("1 {} get").unwrap();
        assert_eq!(Cell::Nil, xs.pop_data().unwrap());
    }

    #[test]
    fn test_locals() {
        let mut xs = State::new().unwrap();
        xs.interpret(": f local x local y x y y x ; 1 2 f").unwrap();
        assert_eq!(Cell::Int(2), xs.pop_data().unwrap());
        assert_eq!(Cell::Int(1), xs.pop_data().unwrap());
        assert_eq!(Cell::Int(1), xs.pop_data().unwrap());
        assert_eq!(Cell::Int(2), xs.pop_data().unwrap());
        assert_eq!(Err(Xerr::UnknownWord), xs.interpret("x y"));
    }

    #[test]
    fn test_base() {
        let mut xs = State::new().unwrap();
        xs.interpret("HEX 16 BASE assert-eq").unwrap();
        xs.interpret("DEC 10 BASE assert-eq").unwrap();
        xs.interpret("OCT 8 BASE assert-eq").unwrap();
        xs.interpret("BIN 2 BASE assert-eq").unwrap();
    }

    #[test]
    fn test_immediate() {
        let mut xs = State::new().unwrap();
        let res = xs.load(": f 0 [] get immediate ; f");
        assert_eq!(Err(Xerr::OutOfBounds), res);
    }

    #[test]
    fn test_nested_interpreter() {
        let mut xs = State::new().unwrap();
        xs.load("(3 5 *)").unwrap();
        xs.run().unwrap();
        assert_eq!(Ok(Cell::Int(15)), xs.pop_data());
        xs.interpret("(2 2 +)").unwrap();
        assert_eq!(Ok(Cell::Int(4)), xs.pop_data());
        xs.interpret("(10 var x 2 var y (x y *))").unwrap();
        assert_eq!(Ok(Cell::Int(20)), xs.pop_data());
        xs.interpret("(3 var n [n 0 do I loop])").unwrap();
        let v = xs.pop_data().unwrap().into_vector().unwrap();
        assert_eq!(3, v.len());
    }

    #[test]
    fn test_defvar() {
        let mut xs = State::new().unwrap();
        let x = xs.defvar("X", Cell::Int(1)).unwrap();
        assert_eq!(Ok(&Cell::Int(1)), xs.get_var(x));
        let x2 = xs.defvar("X", Cell::Int(2)).unwrap();
        assert_eq!(Ok(&Cell::Int(2)), xs.get_var(x2));
        xs.interpret(": Y 3 ;").unwrap();
        xs.defvar("Y", Cell::Nil).unwrap();
        xs.interpret("4 var Z").unwrap();
        xs.defvar("Z", Cell::Nil).unwrap();
    }
}
