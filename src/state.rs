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

struct DictEntry {
    name: String,
    entry: Entry,
    help: Option<String>,
}

impl DictEntry {
    fn new(name: String, entry: Entry) -> Self {
        Self {
            name,
            entry,
            help: None,
        }
    }
}

#[derive(Clone, Debug)]
struct FunctionFlow {
    dict_idx: usize,
    start: usize,
    locals: Vec<String>,
}

#[derive(Clone, Debug)]
enum Flow {
    If(usize),
    Else(usize),
    Begin(usize),
    While(usize),
    Leave(usize),
    Case,
    CaseOf(usize),
    CaseEndOf(usize),
    Vec,
    Fun(FunctionFlow),
    Do { test_org: usize, jump_org: usize },
}

#[derive(Debug, Clone)]
pub enum Loop {
    VecBuilder { stack_ptr: usize },
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
    dict: Vec<DictEntry>,
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
    console: Option<String>,
    pub(crate) about_to_stop: bool,
    // current input binary
    pub(crate) bs_input: Xref,
    pub(crate) bs_isbig: Xref,
    pub(crate) bs_chunk: Xref,
    pub(crate) bs_flow: Xref,
    // default base
    pub(crate) fmt_base: Xref,
    pub(crate) fmt_prefix: Xref,
    // dump state
    pub(crate) dump_start: Xref,
}

impl State {
    pub fn error_context(&mut self, err: &Xerr) -> String {
        let mut error_text = err.message();
        if self.ctx.mode == ContextMode::Load {
            let lex = self.ctx.source.as_ref().unwrap();
            error_text.push_str(&self.debug_map.format_lex_location(lex));
        } else if let Some(loc) = self.debug_map.format_location(self.ip()) {
            error_text.push_str(&loc);
        } else {
            let lex = self.ctx.source.as_ref().unwrap();
            error_text.push_str(&self.debug_map.format_lex_location(lex));
        }
        error_text
    }

    pub fn log_error(&mut self, mut msg: String) {
        msg.push_str("\n");
        self.print(&msg);
    }

    pub fn print(&mut self, msg: &str) {
        #[cfg(not(feature = "stdio"))]
        if let Some(out) = self.console.as_mut() {
            out.push_str(msg);
        }
        #[cfg(feature = "stdio")]
        if let Some(out) = self.console.as_mut() {
            out.push_str(msg)
        } else {
            eprint!("{}", msg);
        }
    }

    pub fn console(&mut self) -> Option<&mut String> {
        self.console.as_mut()
    }

    pub fn print_dump(&mut self, rows: usize, cols: usize) -> Xresult {
        let bs = self.get_var(self.bs_input)?.clone().into_bitstring()?;
        let start = bs.start() - (bs.start() % (cols * 8));
        let end = start + rows * cols * 8;
        crate::bitstring_mod::bitstr_dump_range(self, start..end, cols)
    }

    pub fn current_line(&self) -> String {
        self.debug_map.format_location(self.ip()).unwrap_or_else(|| {
            format!("{:x}:", self.ip())
        })
    }

    pub fn set_binary_input(&mut self, bin: Xbitstr) -> Xresult {
        self.set_var(self.bs_input, Cell::Bitstr(bin)).map(|_| ())
    }

    pub fn load_source(&mut self, path: &str) -> Xresult {
        let buf =     std::fs::read_to_string(path).map_err(|e| {
            self.log_error(format!("{}: {}", path, e));
            Xerr::IOError
        })?;
        let src = self.debug_map.add_source(&buf, Some(path.to_string()));
        self.load1(src)
    }

    pub fn load(&mut self, source: &str) -> Xresult {
        let src = self.debug_map.add_source(source, None);
        self.load1(src)
    }

    fn load1(&mut self, src: Lex) -> Xresult {
        self.context_open(ContextMode::Load, Some(src));
        let depth = self.nested.len();
        let result = self.build();
        if let Err(e) = result.as_ref() {
            let errstr = self.error_context(e);
            self.log_error(errstr);
            while self.nested.len() > depth {
                self.context_close()?;
            }
        }
        result
    }

    pub fn interpret(&mut self, buffer: &str) -> Xresult {
        let src = self.debug_map.add_source(buffer, None);
        self.interpret1(src)
    }

    fn interpret1(&mut self, src: Lex) -> Xresult {
        self.context_open(ContextMode::Eval, Some(src));
        let depth = self.nested.len();
        let result = self.build();
        if let Err(e) = result.as_ref() {
            let msg = self.error_context(e);
            self.log_error(msg);
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
                Tok::Bstr(s) => {
                    self.code_emit_value(Cell::Bitstr(s))?;
                }
                Tok::Key(key) => {
                    self.code_emit_value(Cell::Key(key))?;
                }
                Tok::Word(name) => {
                    let idx = match self.dict_find(&name) {
                        Some(idx) => idx,
                        None => {
                            let idx = self
                                .top_function_flow()
                                .and_then(|ff| ff.locals.iter().rposition(|x| x == &name))
                                .ok_or(Xerr::UnknownWord)?;
                            self.code_emit(Opcode::LoadLocal(idx))?;
                            continue;
                        }
                    };
                    match self.dict_at(idx).unwrap() {
                        Entry::Deferred => {
                            self.code_emit(Opcode::Deferred(idx))?
                        }
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
                            self.call_fn(xf)?;
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

    fn next_token(&mut self) -> Xresult1<Tok> {
        if let Some(lex) = &mut self.ctx.source {
            lex.next()
        } else {
            Ok(Tok::EndOfInput)
        }
    }

    fn context_open(&mut self, mode: ContextMode, source: Option<Lex>) {
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
        #[cfg(not(feature = "stdio"))]
        {
            xs.console = Some(String::new());
        }
        xs.fmt_base = xs.defvar("BASE", Cell::Int(10))?;
        xs.fmt_prefix = xs.defvar("*PREFIX*", ONE)?;
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
        self.dict_insert(DictEntry::new(name.to_string(), Entry::Variable(a)))?;
        Ok(Xref::Heap(a))
    }

    pub fn get_var_by_name(&self, name: &str) -> Xresult1<&Cell> {
        let e = self
            .dict_find(name)
            .and_then(|idx| self.dict_at(idx))
            .ok_or(Xerr::UnknownWord)?;
        match e {
            Entry::Variable(a) => self.get_var(Xref::Heap(*a)),
            Entry::Function { .. } => Err(Xerr::ReadonlyAddress),
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
            }
            _ => Err(Xerr::InvalidAddress),
        }
    }

    pub fn defword(&mut self, name: &str, x: XfnType) -> Xresult1<Xref> {
        let xf = Xfn::Native(XfnPtr(x));
        let idx = self.dict_insert(DictEntry::new(
            name.to_string(),
            Entry::Function {
                immediate: false,
                xf,
                len: Some(0),
            })
        )?;
        Ok(Xref::Word(idx))
    }

    pub fn defwordself(&mut self, name: &str, x: XfnType, slf: Cell) -> Xresult1<Xref> {
        let start = self.code_origin();
        self.code_emit(Opcode::Jump(0))?;
        let fn_addr = self.code_origin();
        self.code_emit_value(slf)?;
        self.code_emit(Opcode::NativeCall(XfnPtr(x)))?;
        self.code_emit(Opcode::Ret)?;
        let len = self.code_origin() - start;
        let word_addr = self.dict_insert(DictEntry::new(
            name.to_string(),
            Entry::Function {
                immediate: false,
                xf: Xfn::Interp(fn_addr),
                len: Some(len),
            }))?;
        let offs = jump_offset(start, self.code_origin());
        self.patch_jump(start, offs)?;
        Ok(Xref::Word(word_addr))
    }

    pub fn help(&self, name: &str) -> Option<&String> {
        let a = self.dict_find(name)?;
        self.dict.get(a).and_then(|x| x.help.as_ref())
    }

    fn load_core(&mut self) -> Xresult {
        struct Def(&'static str, XfnType);
        for i in [
            Def("if", core_word_if),
            Def("else", core_word_else),
            Def("then", core_word_then),
            Def("case", case_word),
            Def("of", of_word),
            Def("endof", endof_word),
            Def("endcase", endcase_word),
            Def("begin", core_word_begin),
            Def("while", core_word_while),
            Def("repeat", core_word_repeat),
            Def("until", core_word_until),
            Def("leave", core_word_leave),
            Def("again", core_word_again),
            Def("[", core_word_vec_begin),
            Def("]", core_word_vec_end),
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
            self.dict_insert(DictEntry::new(
            i.0.to_string(),
                Entry::Function {
                    immediate: true,
                    xf: Xfn::Native(XfnPtr(i.1)),
                    len: None,
                })
            )?;
        }
        for i in [
            Def("I", core_word_counter_i),
            Def("J", core_word_counter_j),
            Def("K", core_word_counter_k),
            Def("length", core_word_length),
            Def("set", core_word_set),
            Def("get", core_word_get),
            Def("lookup", core_word_lookup),
            Def("assoc", core_word_assoc),
            Def("sort", core_word_sort),
            Def("sort-by-key", core_word_sort_by_key),
            Def("rev", core_word_rev),
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
            Def("println", core_word_println),
            Def("print", core_word_print),
            Def("newline", core_word_newline),
            Def("file-write", crate::file::core_word_file_write),
            Def("load", core_word_load),
            Def("HEX", core_word_hex),
            Def("DEC", core_word_decimal),
            Def("OCT", core_word_octal),
            Def("BIN", core_word_binary),
            Def("PREFIX", core_word_prefix),
            Def("NO-PREFIX", core_word_no_prefix),
        ]
        .iter()
        {
            self.dict_insert(DictEntry::new(
                i.0.to_string(),
                    Entry::Function {
                        immediate: false,
                        xf: Xfn::Native(XfnPtr(i.1)),
                        len: None,
                    }
                ))?;
        }
        OK
    }

    fn dict_insert(&mut self, e: DictEntry) -> Xresult1<usize> {
        let wa = self.dict.len();
        self.dict.push(e);
        Ok(wa)
    }

    pub fn dict_find(&self, name: &str) -> Option<usize> {
        self.dict.iter().rposition(|x| x.name == name)
    }

    fn dict_at(&self, idx: usize) -> Option<&Entry> {
        self.dict.get(idx).map(|x| &x.entry)
    }

    fn code_origin(&self) -> usize {
        self.code.len()
    }

    fn code_emit_value(&mut self, val: Cell) -> Xresult {
        match val {
            Cell::Int(i) => self.code_emit(Opcode::LoadInt(i)),
            Cell::Nil => self.code_emit(Opcode::LoadNil),
            val => {
                let a = self.alloc_cell(val)?;
                self.code_emit(Opcode::Load(a))
            }
        }
    }

    fn code_emit(&mut self, op: Opcode) -> Xresult {
        let at = self.code.len();
        let lex = self.ctx.source.as_ref();
        self.debug_map.insert_with_source(at, lex);
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
            Opcode::CaseOf(_) => Opcode::CaseOf(offs),
            _ => panic!("not a jump instruction at={}", at),
        };
        self.patch_insn(at, insn)
    }

    pub fn alloc_cell(&mut self, val: Cell) -> Xresult1<usize> {
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
            Opcode::CaseOf(rel) => {
                let a = self.pop_data()?;
                let b = self.top_data().ok_or(Xerr::StackUnderflow)?;
                if &a == b {
                    self.pop_data()?;
                    self.next_ip()
                } else {
                    self.jump_to(rel)
                }
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

fn take_first_cond_flow(xs: &mut State) -> Xresult1<Flow> {
    for i in (xs.ctx.fs_len..xs.flow_stack.len()).rev() {
        let t = match xs.flow_stack[i] {
            Flow::If(_) => true,
            Flow::Else(_) => true,
            Flow::Case => true,
            Flow::CaseOf(_) => true,
            Flow::CaseEndOf(_) => true,
            Flow::Leave(_) => continue,
            _ => break,
        };
        if t {
            return Ok(xs.flow_stack.remove(i))
        }
    }
    Err(Xerr::ControlFlowError)
}

fn core_word_if(xs: &mut State) -> Xresult {
    let org = xs.code_origin();
    xs.push_flow(Flow::If(org))?;
    xs.code_emit(Opcode::JumpIfNot(0))    
}

fn core_word_else(xs: &mut State) -> Xresult {
    let if_org = match take_first_cond_flow(xs)? {
        Flow::If(org) => org,
        _ => return Err(Xerr::ControlFlowError),
    };
    let else_org = xs.code_origin();
    xs.push_flow(Flow::Else(else_org))?;
    xs.code_emit(Opcode::Jump(0))?;
    let rel = jump_offset(if_org, xs.code_origin());
    xs.patch_jump(if_org, rel)
}

fn core_word_then(xs: &mut State) -> Xresult {
    let if_org = match take_first_cond_flow(xs)? {
        Flow::If(org) => org,
        Flow::Else(org) => org,
        _ => return Err(Xerr::ControlFlowError),
    };  
    let offs = jump_offset(if_org, xs.code_origin());
    xs.patch_jump(if_org, offs)
}

fn case_word(xs: &mut State) -> Xresult {
    xs.push_flow(Flow::Case)
}

fn endcase_word(xs: &mut State) -> Xresult {
    let endcase_org = xs.code_origin();
    loop {
        match take_first_cond_flow(xs)? {
            Flow::CaseEndOf(endof_org) => {
                let rel = jump_offset(endof_org, endcase_org);
                xs.patch_jump(endof_org, rel)?;
            }
            Flow::Case => break OK,
            _ => break Err(Xerr::ControlFlowError),
        }
    }
}

fn of_word(xs: &mut State) -> Xresult {
    let of_org = xs.code_origin();
    xs.push_flow(Flow::CaseOf(of_org))?;
    xs.code_emit(Opcode::CaseOf(0))
}

fn endof_word(xs: &mut State) -> Xresult {
    match take_first_cond_flow(xs)? {
        Flow::CaseOf(of_org) => {
            let endof_org = xs.code_origin();
            xs.code_emit(Opcode::Jump(0))?;
            let next_case_rel = jump_offset(of_org, xs.code_origin());
            xs.patch_jump(of_org, next_case_rel)?;
            xs.push_flow(Flow::CaseEndOf(endof_org))
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_begin(xs: &mut State) -> Xresult {
    xs.push_flow(Flow::Begin(xs.code_origin()))
}

fn core_word_until(xs: &mut State) -> Xresult {
    match xs.pop_flow()? {
        Flow::Begin(begin_org) => {
            let offs = jump_offset(xs.code_origin(), begin_org);
            xs.code_emit(Opcode::JumpIf(offs))
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_while(xs: &mut State) -> Xresult {
    let cond = Flow::While(xs.code_origin());
    xs.code_emit(Opcode::JumpIfNot(0))?;
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
                let offs = jump_offset(leave_org, xs.code_origin() + 1);
                xs.patch_jump(leave_org, offs)?;
            }
            Flow::While(cond_org) => match xs.pop_flow()? {
                Flow::Begin(begin_org) => {
                    let offs = jump_offset(cond_org, xs.code_origin() + 1);
                    xs.patch_jump(cond_org, offs)?;
                    let offs = jump_offset(xs.code_origin(), begin_org);
                    break xs.code_emit(Opcode::Jump(offs));
                }
                _ => break Err(Xerr::ControlFlowError),
            },
            _ => break Err(Xerr::ControlFlowError),
        }
    }
}

fn core_word_leave(xs: &mut State) -> Xresult {
    let leave = Flow::Leave(xs.code_origin());
    xs.code_emit(Opcode::Jump(0))?;
    xs.push_flow(leave)
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
    xs.code_emit(Opcode::NativeCall(XfnPtr(vec_builder_begin)))
}

fn core_word_vec_end(xs: &mut State) -> Xresult {
    match xs.pop_flow()? {
        Flow::Vec => xs.code_emit(Opcode::NativeCall(XfnPtr(vec_builder_end))),
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

fn core_word_def_begin(xs: &mut State) -> Xresult {
    let name = match xs.next_token()? {
        Tok::Word(name) => name,
        _other => return Err(Xerr::ExpectingName),
    };
    let start = xs.code_origin();
    // jump over function body
    xs.code_emit(Opcode::Jump(0))?;
    // function starts right after jump
    let xf = Xfn::Interp(xs.code_origin());
    let dict_idx = xs.dict_insert(DictEntry::new(
        name,
        Entry::Function {
            immediate: false,
            xf,
            len: None,
        }))?;
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
            xs.code_emit(Opcode::Ret)?;
            let offs = jump_offset(start, xs.code_origin());
            let fun_len = xs.code_origin() - start;
            match xs.dict.get_mut(dict_idx).ok_or(Xerr::InvalidAddress)? {
                DictEntry { entry: Entry::Function { ref mut len, .. }, ..} => *len = Some(fun_len),
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
    match xs.dict.get_mut(dict_idx).ok_or(Xerr::InvalidAddress)?.entry {
        Entry::Function {
            ref mut immediate, ..
        } => {
            *immediate = true;
            OK
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_def_local(xs: &mut State) -> Xresult {
    let name = match xs.next_token()? {
        Tok::Word(name) => name,
        _ => return Err(Xerr::ExpectingName),
    };
    let ff = xs.top_function_flow().ok_or(Xerr::ControlFlowError)?;
    let idx = ff.locals.len();
    ff.locals.push(name);
    xs.code_emit(Opcode::InitLocal(idx))
}

fn core_word_variable(xs: &mut State) -> Xresult {
    let name = match xs.next_token()? {
        Tok::Word(name) => name,
        _other => return Err(Xerr::ExpectingName),
    };
    let a = if xs.ctx.mode == ContextMode::Load {
        let a = xs.alloc_cell(Cell::Nil)?;
        xs.code_emit(Opcode::Store(a))?;
        a
    } else {
        let val = xs.pop_data()?;
        xs.alloc_cell(val)?
    };
    xs.dict_insert(DictEntry::new(name, Entry::Variable(a)))?;
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

fn core_word_nil(xs: &mut State) -> Xresult {
    if xs.ctx.mode == ContextMode::Load {
        xs.code_emit(Opcode::LoadNil)
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
    let debug_comment = "not implemented!";
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
            Opcode::CaseOf(rel) => format!("caseof     ${:05x}", jumpaddr(at, rel)),
            Opcode::Load(a) => format!("load       {}", a),
            Opcode::LoadInt(i) => format!("loadint    {}", i),
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
        xs.dict_insert(DictEntry::new(name, Entry::Deferred))?;
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
    xs.code_emit(Opcode::NativeCall(XfnPtr(core_word_do_init)))?;
    let test_org = xs.code_origin();
    xs.code_emit(Opcode::NativeCall(XfnPtr(core_word_do_test)))?;
    let jump_org = xs.code_origin();
    xs.code_emit(Opcode::JumpIfNot(0))?;
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
    xs.code_emit(Opcode::NativeCall(XfnPtr(core_word_loop_inc)))?;
    let next_org = xs.code_origin();
    xs.code_emit(Opcode::Jump(0))?;
    let break_org = xs.code_origin();
    xs.code_emit(Opcode::NativeCall(XfnPtr(core_word_loop_leave)))?;
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

fn counter_value(xs: &mut State, mut n: usize) -> Xresult {
    for x in xs.loops[xs.ctx.ls_len..].iter().rev() {
        if let Loop::Do { start, .. } = x {
            if n == 0 {
                let val = *start;
                return xs.push_data(Cell::Int(val));
            }
            n -= 1;
        }
    }
    Err(Xerr::LoopStackUnderflow)
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
        Cell::Str(x) => xs.push_data(Cell::from(x.len())),
        _ => Err(Xerr::TypeError),
    }
}

fn vector_relative_index(v: &Xvec, index: isize) -> Xresult1<usize> {
    if index >= 0 {
        Ok(index as usize)
    } else {
        v.len().checked_sub(index.abs() as usize).ok_or(Xerr::OutOfBounds)
    }
}

fn vector_get<'a>(v: &'a Xvec, index: isize) -> Xresult1<&'a Cell> {
    let new_index = vector_relative_index(v, index)?;
    v.get(new_index).ok_or(Xerr::OutOfBounds)
}

fn vector_get_by_key<'a>(v: &'a Xvec, key: &Cell) -> Xresult1<&'a Cell> {
    let mut it = v.iter();
    let mut val = None;
    while let Some(x) = it.next() {
        if x == key {
            val = it.next();
            break;
        }
    }
    val.ok_or(Xerr::NotFound)
}

fn core_word_get(xs: &mut State) -> Xresult {
    let index = xs.pop_data()?.into_isize()?;
    let v = xs.pop_data()?.into_vector()?;
    xs.push_data(vector_get(&v, index)?.clone())
}

fn core_word_set(xs: &mut State) -> Xresult {
    let val = xs.pop_data()?;
    let index = xs.pop_data()?.into_isize()?;
    let mut v = xs.pop_data()?.into_vector()?;
    let new_index = vector_relative_index(&v, index)?;
    if v.set_mut(new_index, val) {
        xs.push_data(Cell::Vector(v))
    } else {
        Err(Xerr::OutOfBounds)
    }
}

fn core_word_lookup(xs: &mut State) -> Xresult {
    let key = xs.pop_data()?;
    if !key.is_key() {
        return Err(Xerr::ExpectingKey);
    }
    if xs.top_data().ok_or(Xerr::StackUnderflow)?.is_key() {
        core_word_lookup(xs)?;
    }
    let v = xs.pop_data()?.into_vector()?;
    xs.push_data(vector_get_by_key(&v, &key)?.clone())
}

fn core_word_assoc(xs: &mut State) -> Xresult {
    let val = xs.pop_data()?;
    let key = xs.pop_data()?;
    match xs.pop_data()? {
        Cell::Vector(mut v) => {
            let mut it = v.iter().enumerate();
            let mut reuse = None;
            while let Some((index, x)) = it.next() {
                if x == &key {
                    reuse = Some(index + 1);
                    break;
                }
                it.next();
            }
            if let Some(index) = reuse {
                if !v.set_mut(index, val) {
                    return Err(Xerr::OutOfBounds);
                }
            } else {
                v.push_back_mut(key);
                v.push_back_mut(val);
            }
            xs.push_data(Cell::Vector(v))
        }
        _ => Err(Xerr::TypeError),
    }
}

fn core_word_sort(xs: &mut State) -> Xresult {
    use std::iter::FromIterator;
    let v = xs.pop_data()?.into_vector()?;
    let m: std::collections::BTreeSet<Cell> = v.iter().cloned().collect();
    let sorted = Xvec::from_iter(m.into_iter());
    xs.push_data(Cell::Vector(sorted))
}

fn core_word_sort_by_key(xs: &mut State) -> Xresult {
    use std::iter::FromIterator;
    let key = xs.pop_data()?;
    let v = xs.pop_data()?.into_vector()?;
    let mut m = std::collections::BTreeMap::new();
    for i in v.iter() {
        let pv = if let Cell::Vector(pv) = i {
            pv
        } else {
            return Err(Xerr::TypeError)
        };
        m.insert(vector_get_by_key(pv, &key)?, i);
    }
    let sorted = Xvec::from_iter(m.values().map(|x| (*x).clone()));
    xs.push_data(Cell::Vector(sorted))
}

fn core_word_rev(xs: &mut State) -> Xresult {
    use std::iter::FromIterator;
    let v = xs.pop_data()?.into_vector()?;
    let rv = Xvec::from_iter(v.iter().rev().cloned());
    xs.push_data(Cell::Vector(rv))
}

fn core_word_assert(xs: &mut State) -> Xresult {
    if xs.pop_data()?.is_true() {
        OK
    } else {
        Err(Xerr::DebugAssertion)
    }
}

fn core_word_assert_eq(xs: &mut State) -> Xresult {
    let a = xs.pop_data()?;
    let b = xs.pop_data()?;
    if a == b {
        OK
    } else {
        let msg = format!("[0]: {:?}\n[1]: {:?}", a, b);
        xs.log_error(msg);
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
    let prefix = xs
        .get_var(xs.fmt_prefix)
        .map(|val| val.is_true())
        .unwrap_or(false);
    let s= match xs.get_var(xs.fmt_base)? {
        Cell::Int(2) if prefix => format!("{:#2?}", val),
        Cell::Int(2)  => format!("{:2?}", val),
        Cell::Int(8) if prefix => format!("{:#8?}", val),
        Cell::Int(8)  => format!("{:8?}", val),
        Cell::Int(16) if prefix => format!("{:#16?}", val),
        Cell::Int(16) => format!("{:16?}", val),
        _ => format!("{:10?}", val),
    };
    xs.print(&s);
    OK
}

fn core_word_newline(xs: &mut State) -> Xresult {
    xs.print("\n");
    OK
}

fn core_word_hex(xs: &mut State) -> Xresult {
    xs.set_var(xs.fmt_base, Cell::Int(16)).map(|_| ())
}

fn core_word_decimal(xs: &mut State) -> Xresult {
    xs.set_var(xs.fmt_base, Cell::Int(10)).map(|_| ())
}

fn core_word_octal(xs: &mut State) -> Xresult {
    xs.set_var(xs.fmt_base, Cell::Int(8)).map(|_| ())
}

fn core_word_binary(xs: &mut State) -> Xresult {
    xs.set_var(xs.fmt_base, Cell::Int(2)).map(|_| ())
}

fn core_word_prefix(xs: &mut State) -> Xresult {
    xs.set_var(xs.fmt_prefix, ONE).map(|_| ())
}
fn core_word_no_prefix(xs: &mut State) -> Xresult {
    xs.set_var(xs.fmt_prefix, ZERO).map(|_| ())
}

fn core_word_breakpoint(xs: &mut State) -> Xresult {
    if xs.ctx.mode == ContextMode::Load {
        xs.code_emit(Opcode::Break)
    } else {
        Err(Xerr::DebugBreak)
    }
}

fn core_word_load(xs: &mut State) -> Xresult {
    let path = xs.pop_data()?.into_string()?;
    xs.load_source(&path)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{xvec, xkey};

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
        xs.interpret("2 1 do [I] loop").unwrap();
        let v1 = xs.pop_data().unwrap().into_vector().unwrap();
        assert_eq!(ONE, v1[0]);
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
    fn test_get_set() {
        let mut xs = State::new().unwrap();
        xs.interpret("[11 22 33] 2 get").unwrap();
        assert_eq!(Cell::from(33isize), xs.pop_data().unwrap());
        xs.interpret("[11 22 33] -2 get").unwrap();
        assert_eq!(Cell::from(22isize), xs.pop_data().unwrap());
        xs.interpret("[1 2 3] 0 5 set 0 get").unwrap();
        assert_eq!(Cell::from(5isize), xs.pop_data().unwrap());
        assert_eq!(Err(Xerr::OutOfBounds), xs.interpret("[1 2 3] 100 get"));
        assert_eq!(Err(Xerr::OutOfBounds), xs.interpret("[1 2 3] -100 get"));
        assert_eq!(Err(Xerr::TypeError), xs.interpret("[] key: get"));
    }

    #[test]
    fn test_lookup() {
        let mut xs = State::new().unwrap();
        xs.interpret("[x: 1] x: lookup").unwrap();
        assert_eq!(Cell::from(1isize), xs.pop_data().unwrap());
        xs.interpret("[x: [y: [z: 10]]] x: y: z: lookup").unwrap();
        assert_eq!(Cell::from(10isize), xs.pop_data().unwrap());
        assert_eq!(Err(Xerr::NotFound), xs.interpret("[x: [y: [1 2 3]]] f: y: x: lookup"));
    }

    #[test]
    fn test_assoc() {
        let mut xs = State::new().unwrap();
        xs.interpret("[] x: 1 assoc y: 2 assoc").unwrap();
        assert_eq!(xvec![xkey![x], 1u32, xkey![y], 2u32], xs.pop_data().unwrap());
        xs.interpret("[x: 1] x: 2 assoc x: lookup").unwrap();
        assert_eq!(Xcell::from(2usize), xs.pop_data().unwrap());
        xs.interpret("[x: 1 y: 3] x: 5 assoc x: lookup").unwrap();
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
        let res = xs.load(": f [] 0 get immediate ; f");
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

    #[test]
    fn test_defwordself() {
        let mut xs = State::new().unwrap();
        xs.defwordself( "self1", |xs| {
            assert_eq!(Ok(ONE), xs.pop_data());
            xs.push_data(ZERO)
        }, ONE).unwrap();
        xs.interpret("self1").unwrap();
        assert_eq!(Ok(ZERO), xs.pop_data());
    }

    #[test]
    fn test_caseof() {
        let mut xs = State::new().unwrap();
        xs.interpret("2 case 1 of 100 endof 2 of 200 endof endcase").unwrap();
        assert_eq!(Ok(Cell::Int(200)), xs.pop_data());
        xs.interpret("5 case 1 of 100 endof 2 of 200 endof 0 endcase").unwrap();
        assert_eq!(Ok(ZERO), xs.pop_data());
        xs.interpret("10 0 do I I case 5 of leave endof drop endcase loop").unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
    }

    #[test]
    fn test_fmt_prefix() {
        let mut xs = State::new().unwrap();
        xs.console = Some(String::new());
        xs.interpret("255 HEX print").unwrap();
        assert_eq!(Some("0xFF".to_string()), xs.console);
        xs.console = Some(String::new());
        xs.interpret("255 NO-PREFIX HEX print").unwrap();
        assert_eq!(Some("FF".to_string()), xs.console);
        xs.console = Some(String::new());
        xs.interpret("[255] NO-PREFIX HEX print").unwrap();
        assert_eq!(Some("[FF]".to_string()), xs.console);
    }

    #[test]
    fn test_rev() {
        let mut xs = State::new().unwrap();
        xs.interpret("[1 2 3] rev").unwrap();
        assert_eq!(xvec![3isize, 2isize, 1isize], xs.pop_data().unwrap());
    }

    #[test]
    fn test_sort() {
        let mut xs = State::new().unwrap();
        xs.interpret("[2 3 1] sort").unwrap();
        assert_eq!(xvec![1isize, 2isize, 3isize], xs.pop_data().unwrap());
    }

    #[test]
    fn test_sort_by_key() {
        let mut xs = State::new().unwrap();
        xs.interpret("[[k: 2] [k: 3] [k: 1]] k: sort-by-key var x").unwrap();
        xs.interpret("[ 3 0 do x I get k: lookup loop ]").unwrap();
        assert_eq!(xvec![1isize, 2isize, 3isize], xs.pop_data().unwrap());
    }
}
