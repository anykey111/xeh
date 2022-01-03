use crate::arith::*;
use crate::cell::*;
use crate::error::*;
use crate::lex::*;
use crate::opcodes::*;
use crate::bitstring_mod::BitstrMod;

use std::fmt::*;
use std::ops::Range;

#[derive(Debug, Clone, PartialEq)]
enum Entry {
    Variable(usize),
    Function {
        immediate: bool,
        xf: Xfn,
        len: Option<usize>,
    },
}

#[derive(Clone)]
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

#[derive(Clone, Debug, PartialEq)]
struct FunctionFlow {
    dict_idx: usize,
    start: usize,
    locals: Vec<String>,
}

#[derive(Clone, Debug, PartialEq)]
enum Flow {
    If(usize),
    Else(usize),
    Begin(usize),
    While(usize),
    Break(usize),
    Case,
    CaseOf(usize),
    CaseEndOf(usize),
    Vec,
    Fun(FunctionFlow),
    For { for_org: usize, body_org: usize },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Loop {
    range: Range<isize>,
}

// hold runtime things that flow stack don't know
#[derive(Debug, Clone, PartialEq)]
pub enum Special {
    VecStackStart(usize),
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
    ss_ptr: usize,
    ip: usize,
    mode: ContextMode,
    source: Option<Lex>,
}

#[derive(Debug, Clone, Default, PartialEq)]
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

#[derive(Debug, Clone)]
pub enum ReverseStep {
    SetIp(usize),
    PushData(Cell),
    PopData,
    SwapData,
    RotData,
    OverData,
    PopReturn,
    PushReturn(Frame),
    PopLoop,
    PushLoop(Loop),
    LoopNextBack(Loop),
    PopSpecial,
    PushSpecial(Special),
    DropLocal(usize),
}

#[derive(Default, Clone, Debug)]
struct SourceBuf {
    name: String,
    buf: Xstr,
}

#[derive(Default, Clone)]
pub struct State {
    dict: Vec<DictEntry>,
    heap: Vec<Cell>,
    code: Vec<Opcode>,
    debug_map: Vec<Option<Xsubstr>>,
    sources: Vec<SourceBuf>,
    data_stack: Vec<Cell>,
    return_stack: Vec<Frame>,
    flow_stack: Vec<Flow>,
    loops: Vec<Loop>,
    special: Vec<Special>,
    ctx: Context,
    nested: Vec<Context>,
    reverse_log: Option<Vec<ReverseStep>>,
    console: Option<String>,
    pub(crate) about_to_stop: bool,
    pub(crate) bitstr_mod: BitstrMod,
    // default base
    pub(crate) fmt_base: Xref,
    pub(crate) fmt_prefix: Xref,
}

impl State {
    fn format_error(&mut self, err: &Xerr) -> String {
        let mut msg = String::with_capacity(1000);
        writeln!(msg, "error: {}", err.name()).unwrap();
        match err {
            Xerr::BitReadError(ctx) => {
                writeln!(msg, " trying to read {} bits while only {} remain",
                    ctx.1, ctx.0.len()).unwrap();
            }
            Xerr::BitSeekError(ctx) => {
                writeln!(msg, " position {} is beyond of available limit {}",
                    ctx.1, ctx.0.end()).unwrap();
            }
            Xerr::BitMatchError(ctx) => {
                let src = &ctx.0;
                let pat = &ctx.1;
                let at = ctx.2;
                writeln!(msg, " source bits are differ from pattern at offset {}", at).unwrap();
                write!(msg, " [").unwrap();
                let (_, src_diff) = src.split_at(at).unwrap();
                for (x, _) in src_diff.iter8().take(8) {
                    write!(msg, " {:02X}", x).unwrap();
                }
                writeln!(msg, " ] source at {}", src.start() + at).unwrap();
                write!(msg, " [").unwrap();
                let (_, pat_diff) = pat.split_at(at).unwrap();
                for (x, _) in pat_diff.iter8().take(8){
                    write!(msg, " {:02X}", x).unwrap();
                }
                writeln!(msg, " ] pattern at {}", pat.start() + at).unwrap();
            }
            _ => (),
        }
        msg
    }

    pub fn format_cell(&self, val: &Cell) -> Xresult1<String> {
        let prefix = self
            .get_var(self.fmt_prefix)
            .map(|val| val.is_true())
            .unwrap_or(false);
        let s= match self.get_var(self.fmt_base)? {
            Cell::Int(2) if prefix => format!("{:#2?}", val),
            Cell::Int(2)  => format!("{:2?}", val),
            Cell::Int(8) if prefix => format!("{:#8?}", val),
            Cell::Int(8)  => format!("{:8?}", val),
            Cell::Int(16) if prefix => format!("{:#16?}", val),
            Cell::Int(16) => format!("{:16?}", val),
            _ => format!("{:10?}", val),
        };
        Ok(s)
    }

    fn write_location(&self, buf: &mut String, tok: &Xsubstr) {
        let mut line_start = 0;
        let tok_start = tok.range().start;
        for (i, s) in tok.parent().lines().enumerate() {
            let line_end = line_start + s.len();
            if line_start <= tok_start || tok_start <= line_end {
                let len = tok_start - line_start;
                let col = s[..len].chars().count();
                let name = self.sources
                    .iter()
                    .find(|x| &x.buf == tok.parent())
                    .map(|x| x.name.as_str())
                    .unwrap_or_default();
                writeln!(buf, "{}:{}:{}", name, i + 1, col + 1).unwrap();
                writeln!(buf, "{}", s).unwrap();
                writeln!(buf, "{:->1$}", '^', col).unwrap();
                break;
            }
            line_start = line_end;
        }
    }

    pub fn current_line(&mut self) -> String {
        let mut buf = String::with_capacity(1000);
        if self.ctx.mode == ContextMode::Load {
            if let Some(tok) = self.ctx.source.as_ref().and_then(|x| x.last_token()) {
                self.write_location(&mut buf, &tok);
            }
        } else{
            if let Some(Some(tok)) = self.debug_map.get(self.ip()) {
                self.write_location(&mut buf, tok);
            }
        }
        buf
    }

    pub fn pretty_error(&mut self, err: &Xerr) -> String {
        let mut buf = self.format_error(err);
        buf.push_str(&self.current_line());
        buf
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

    pub fn print_dump(&mut self, nrows: usize, ncols: usize) -> Xresult {
        crate::bitstring_mod::print_dump(self, nrows, ncols)
    }

    pub fn set_binary_input(&mut self, bin: Xbitstr) -> Xresult {
        self.push_data(Cell::Bitstr(bin))?;
        self.eval_word("bitstr-open")
    }

    pub fn load_source(&mut self, path: &str) -> Xresult {
        let buf =     std::fs::read_to_string(path).map_err(|e| {
            self.log_error(format!("{}: {}", path, e));
            Xerr::IOError
        })?;
        let src = self.add_source(&buf, Some(path));
        self.build_source(src, ContextMode::Load)
    }

    pub fn load(&mut self, source: &str) -> Xresult {
        let src = self.add_source(source, None);
        self.build_source(src, ContextMode::Load)
    }

    pub fn interpret(&mut self, buffer: &str) -> Xresult {
        let src = self.add_source(buffer, None);
        self.build_source(src, ContextMode::Eval)
    }

    fn add_source(&mut self, buf: &str, path: Option<&str>) -> Lex {
        let id = self.sources.len();
        let buf = Xstr::from(buf);
        let lex = Lex::new(buf.clone());
        let name = if let Some(s) = path {
            s.to_string()
        } else {
            format!("<buffer#{}>", id)
        };
        self.sources.push(SourceBuf {
            name,
            buf,
        });
        lex
    }

    fn build_source(&mut self, src: Lex, mode: ContextMode) -> Xresult {
        self.context_open(mode, Some(src));
        let depth = self.nested.len();
        let result = self.build();
        if let Err(e) = result.as_ref() {
            if depth == self.nested.len() {
                let msg = self.pretty_error(e);
                self.log_error(msg);
            }
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
                Tok::Literal(val) => {
                    self.code_emit_value(val)?;
                }
                Tok::Word(name) => {
                    // search for local variables first
                    if let Some(i) = self.top_function_flow()
                        .and_then(|ff| ff.locals.iter().rposition(|x| x == name.as_str())) {
                            self.code_emit(Opcode::LoadLocal(i))?;
                    } else {
                        self.build_resolve_word(name)?;
                    }
                }
            }
        }
    }

    fn build_resolve_word(&mut self, name: Xsubstr) -> Xresult {
        match self.dict_entry(name.as_str()) {
            None =>
                self.code_emit(Opcode::Unresolved(Xstr::from(name.as_str()))),

            Some(Entry::Variable(a)) => {
                let a = *a;
                self.code_emit(Opcode::Load(a))
            }
            Some(Entry::Function {
                immediate: true,
                xf,
                ..
            }) => {
                let xf = xf.clone();
                self.call_fn(xf)
            }
            Some(Entry::Function {
                immediate: false,
                xf: Xfn::Interp(x),
                ..
            }) => {
                let x = *x;
                self.code_emit(Opcode::Call(x))
            }
            Some(Entry::Function {
                immediate: false,
                xf: Xfn::Native(x),
                ..
            }) => {
                let x = *x;
                self.code_emit(Opcode::NativeCall(x))
            }
        }
    }

    fn next_name(&mut self) -> Xresult1<String> {
        if let Some(lex) = &mut self.ctx.source {
            if let Tok::Word(name) = lex.next()? {
                return Ok(name.to_string());
            }
        }
        Err(Xerr::ExpectingName)
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
            ss_ptr: self.special.len(),
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
        assert_eq!(prev_ctx.ls_len, self.loops.len());
        assert_eq!(prev_ctx.ss_ptr, self.special.len());
        assert_eq!(prev_ctx.rs_len, self.return_stack.len());
        self.ctx = prev_ctx;
        OK
    }

    fn has_pending_flow(&self) -> bool {
        (self.flow_stack.len() - self.ctx.fs_len) > 0
    }

    pub fn boot() -> Xresult1<State> {
        let mut xs = State::default();
        #[cfg(not(feature = "stdio"))]
        {
            xs.console = Some(String::new());
        }
        xs.fmt_base = xs.defvar("BASE", Cell::Int(10))?;
        xs.fmt_prefix = xs.defvar("*PREFIX*", ONE)?;
        xs.load_core()?;
        crate::bitstring_mod::load(&mut xs)?;
        Ok(xs)
    }

    pub fn start_reverse_debugging(&mut self) {
        self.reverse_log = Some(Vec::default());
    }

    pub fn stop_reverse_debugging(&mut self) {
        self.reverse_log = None;
    }

    pub fn defvar(&mut self, name: &str, val: Cell) -> Xresult1<Xref> {
        // shadow previous definition
        let a = self.alloc_cell(val)?;
        self.dict_insert(DictEntry::new(name.to_string(), Entry::Variable(a)))?;
        Ok(Xref::Heap(a))
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
        self.backpatch_jump(start, offs)?;
        Ok(Xref::Word(word_addr))
    }

    pub fn set_doc(&mut self, name: &str, help: String) -> Xresult {
        let a = self.dict_find(name).ok_or(Xerr::UnknownWord)?;
        self.dict[a].help = Some(help);
        OK
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
            Def("until", core_word_until),
            Def("break", core_word_break),
            Def("again", core_word_again),
            Def("[", core_word_vec_begin),
            Def("]", core_word_vec_end),
            Def(":", core_word_def_begin),
            Def(";", core_word_def_end),
            Def("#", core_word_comment),
            Def("immediate", core_word_immediate),
            Def("local", core_word_def_local),
            Def("var", core_word_variable),
            Def("->", core_word_setvar),
            Def("nil", core_word_nil),
            Def("(", core_word_nested_begin),
            Def(")", core_word_nested_end),
            Def("for", core_word_for),
            Def("loop", core_word_loop),
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
            Def("len", core_word_len),
            Def("set", core_word_set),
            Def("nth", core_word_nth),
            Def("get", core_word_get),
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
            Def("exit", core_word_exit),
            Def("println", core_word_println),
            Def("print", core_word_print),
            Def("newline", core_word_newline),
            Def("file-write", crate::file::core_word_file_write),
            Def("load", core_word_load),
            Def("meta", core_word_meta),
            Def("with-meta", core_word_with_meta),
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

    fn dict_entry(&self, name: &str) -> Option<&Entry> {
        self.dict.iter().rfind(|x| x.name == name).map(|x| &x.entry)
    }

    pub fn dict_find(&self, name: &str) -> Option<usize> {
        self.dict.iter().rposition(|x| x.name == name)
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
        let len = self.debug_map.len();
        let loc = self.ctx.source.as_ref().and_then(|x| x.last_token());
        if at < len {
            self.debug_map[at] = loc.clone();
        } else if at == len {
            self.debug_map.push(loc.clone());
        } else {
            panic!("non-linear allocation {}/{}", at, len);
        }
        self.code.push(op);
        OK
    }

    fn backpatch(&mut self, at: usize, op: Opcode) -> Xresult {
        self.code[at] = op;
        OK
    }

    fn backpatch_jump(&mut self, at: usize, offs: isize) -> Xresult {
        let insn = match self.code.get(at).ok_or(Xerr::InternalError)? {
            Opcode::Jump(_) => Opcode::Jump(offs),
            Opcode::JumpIf(_) => Opcode::JumpIf(offs),
            Opcode::JumpIfNot(_) => Opcode::JumpIfNot(offs),
            Opcode::CaseOf(_) => Opcode::CaseOf(offs),
            _ => panic!("not a jump instruction at={}", at),
        };
        self.backpatch(at, insn)
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
            self.fetch_and_run()?;
        }
        OK
    }

    pub fn eval_word(&mut self, name: &str) -> Xresult {
        match self.dict_entry(name) {
            None => Err(Xerr::UnknownWord),
            Some(Entry::Variable(a)) => {
                let val = self.heap[*a].clone();
                self.push_data(val)
            }
            Some(Entry::Function { xf, .. }) => {
                let xf = xf.clone();
                self.call_fn(xf)
            }
        }

    }

    fn fetch_and_run(&mut self) -> Xresult {
        let ip = self.ip();
        match self.code[ip] {
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
            Opcode::Unresolved(ref name) => match self.dict_entry(&name) {
                None => Err(Xerr::UnknownWord),
                Some(Entry::Variable(a)) => {
                    let a = *a;
                    self.backpatch(ip, Opcode::Load(a))
                }
                Some(Entry::Function {
                    xf: Xfn::Interp(x), ..
                }) => {
                    let x = *x;
                    self.backpatch(ip, Opcode::Call(x))
                }
                Some(Entry::Function {
                    xf: Xfn::Native(x), ..
                }) => {
                    let x = *x;
                    self.backpatch(ip, Opcode::NativeCall(x))
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
                if self.reverse_debugging() {
                    self.add_reverse_step(ReverseStep::DropLocal(i));
                }
                self.next_ip()
            }
            Opcode::LoadLocal(i) => {
                let frame = self.top_frame().ok_or(Xerr::ReturnStackUnderflow)?;
                let val = frame.locals.get(i).cloned().ok_or(Xerr::InvalidAddress)?;
                self.push_data(val)?;
                self.next_ip()
            }
            Opcode::For(rel) => {
                let l = for_init(self)?;
                if l.range.is_empty() {
                    self.jump_to(rel)
                } else {
                    self.push_loop(l)?;
                    self.next_ip()
                }                
            }
            Opcode::Break(rel) => {
                self.pop_loop()?;
                self.jump_to(rel)
            }
            Opcode::Loop(rel) => {
                if self.loop_next()? {
                    self.jump_to(rel)
                } else {
                    self.pop_loop()?;
                    self.next_ip()
                }
            }
        }
    }

    pub fn next(&mut self) -> Xresult {
        if self.ip() < self.code.len() {
            self.fetch_and_run()?;
        }
        OK
    }

    pub fn rnext(&mut self) -> Xresult {
        // Every instruction may have arbitrary numer of state changes,
        // so rollback aleast one. Then stop on first SetIp.
        let pop = |xs: &mut State| xs.reverse_log.as_mut().and_then(|log| log.pop());
        if let Some(r) = pop(self) {
            self.reverse_changes(r)?;
        }
        while let Some(step) = pop(self) {
            match &step {
                ReverseStep::SetIp{..} => {
                    // this is anohter instruction, queue back to log
                    self.add_reverse_step(step);
                    break;
                },
                _ => self.reverse_changes(step)?
            }
        }
        OK
    }
    
    fn reverse_debugging(&self) -> bool {
        self.reverse_log.is_some()
    }

    fn add_reverse_step(&mut self, step: ReverseStep) {
        if let Some(log) = self.reverse_log.as_mut() {
            log.push(step);
        }
    }

    fn reverse_changes(&mut self, r: ReverseStep) -> Xresult {
        match r {
            ReverseStep::SetIp(ip) => {
                self.ctx.ip = ip;
            }
            ReverseStep::PopData => {
                if self.data_stack.len() > self.ctx.ds_len {
                    self.data_stack.pop();
                } else {
                    return Err(Xerr::StackUnderflow)
                }
            }
            ReverseStep::PushData(val) => {
                self.data_stack.push(val);
            }
            ReverseStep::SwapData => {
                let len = self.data_stack.len();
                if (len - self.ctx.ds_len) >= 2 {
                    self.data_stack.swap(len - 1, len - 2);
                } else {
                    return Err(Xerr::StackUnderflow);
                }
            }
            ReverseStep::RotData => {
                let len = self.data_stack.len();
                if (len - self.ctx.ds_len) >= 3 {
                    self.data_stack.swap(len - 1, len - 3);
                } else {
                    return Err(Xerr::StackUnderflow);
                }
            }
            ReverseStep::OverData => {
                self.drop_data()?;
            }
            ReverseStep::PopReturn => {
                if self.return_stack.len() > self.ctx.rs_len {
                    self.return_stack.pop();
                } else {
                    return Err(Xerr::ReturnStackUnderflow);
                }
            }
            ReverseStep::PushReturn(frame) => {
                self.return_stack.push(frame);
            }
            ReverseStep::PushLoop(l) => {
                self.loops.push(l);
            }
            ReverseStep::PopLoop => {
                if self.loops.len() > self.ctx.ls_len {
                    self.loops.pop();
                } else {
                    return Err(Xerr::LoopStackUnderflow);
                }
            }
            ReverseStep::LoopNextBack(val) => {
                if self.loops.len() > self.ctx.ls_len {
                    let l = self.loops.last_mut().ok_or_else(|| Xerr::InternalError)?;
                    *l = val;
                } else {
                    return Err(Xerr::LoopStackUnderflow);
                }
            }
            ReverseStep::PushSpecial(x) => {
                self.special.push(x);
            }
            ReverseStep::PopSpecial => {
                if self.special.len() > self.ctx.ss_ptr {
                    self.special.pop();
                } else {
                    return Err(Xerr::SpecialStackUnderflow);
                }
            }
            ReverseStep::DropLocal(_) => {
                let f = self.top_frame().ok_or_else(|| Xerr::ReturnStackUnderflow)?;
                f.locals.pop();
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
        if self.reverse_debugging() {
            self.add_reverse_step(ReverseStep::SetIp(self.ctx.ip));
        }
        self.ctx.ip = new_ip;
        OK
    }

    fn next_ip(&mut self) -> Xresult {
        if self.reverse_debugging() {
            self.add_reverse_step(ReverseStep::SetIp(self.ctx.ip));
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

    pub fn push_data(&mut self, data: Cell) -> Xresult {
        if self.reverse_debugging() {
            self.add_reverse_step(ReverseStep::PopData);
        }
        self.data_stack.push(data);
        OK
    }

    pub fn pop_data(&mut self) -> Xresult1<Cell> {
        if self.data_stack.len() > self.ctx.ds_len {
            let val = self.data_stack.pop().unwrap();
            if self.reverse_debugging() {
                self.add_reverse_step(ReverseStep::PushData(val.clone()));
            }
            Ok(val)
        } else {
            Err(Xerr::StackUnderflow)
        }
    }

    pub fn get_data(&self, idx: usize) -> Option<&Cell> {
        self.data_stack.iter().rev().nth(idx)
    }

    pub fn data_depth(&self) -> usize {
        self.data_stack.len() - self.ctx.ds_len
    }

    fn top_data(&self) -> Option<&Cell> {
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
        if self.data_stack.len() > self.ctx.ds_len {
            let val = self.data_stack.last().unwrap().clone();
            self.push_data(val)
        } else {
            Err(Xerr::StackUnderflow)
        }
    }

    fn swap_data(&mut self) -> Xresult {
        let len = self.data_stack.len();
        if (len - self.ctx.ds_len) >= 2 {
            if self.reverse_debugging() {
                self.add_reverse_step(ReverseStep::SwapData);
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
            if self.reverse_debugging() {
                self.add_reverse_step(ReverseStep::RotData);
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
            if self.reverse_debugging() {
                self.add_reverse_step(ReverseStep::OverData);
            }
            let val = self.data_stack[len - 2].clone();
            self.push_data(val)
        } else {
            Err(Xerr::StackUnderflow)
        }
    }

    fn push_return(&mut self, return_to: usize) -> Xresult {
        if self.reverse_debugging() {
            self.add_reverse_step(ReverseStep::PopReturn);
        }
        self.return_stack.push(Frame::from_addr(return_to));
        OK
    }

    fn pop_return(&mut self) -> Xresult1<Frame> {
        if self.return_stack.len() > self.ctx.rs_len {
            let ret = self.return_stack.pop().ok_or(Xerr::ReturnStackUnderflow)?;
            if self.reverse_debugging() {
                self.add_reverse_step(ReverseStep::PushReturn(ret.clone()));
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
        if self.reverse_debugging() {
            self.add_reverse_step(ReverseStep::PopLoop);
        }
        self.loops.push(l);
        OK
    }

    fn pop_loop(&mut self) -> Xresult1<Loop> {
        if self.loops.len() > self.ctx.ls_len {
            let l = self.loops.pop().ok_or(Xerr::InternalError)?;
            if self.reverse_debugging() {
                self.add_reverse_step(ReverseStep::PushLoop(l.clone()));
            }
            Ok(l)
        } else {
            Err(Xerr::LoopStackUnderflow)
        }
    }

    fn loop_next(&mut self) -> Xresult1<bool> {
        if self.ctx.ls_len < self.loops.len() {
            let l = self.loops.last_mut().ok_or_else(|| Xerr::InternalError)?;
            let old = l.clone();
            l.range.next();
            let has_more = !l.range.is_empty();
            if self.reverse_debugging() {
                self.add_reverse_step(ReverseStep::LoopNextBack(old));
            }
            Ok(has_more)
        } else {
            Err(Xerr::LoopStackUnderflow)
        }
    }

    fn push_special(&mut self, s: Special) -> Xresult {
        if self.reverse_debugging() {
            self.add_reverse_step(ReverseStep::PopSpecial);
        }
        self.special.push(s);
        OK
    }

    fn pop_special(&mut self) -> Xresult1<Special> {
        if self.special.len() > self.ctx.ss_ptr {
            let s = self.special.pop().ok_or(Xerr::InternalError)?;
            if self.reverse_debugging() {
                self.add_reverse_step(ReverseStep::PushSpecial(s.clone()));
            }
            Ok(s)
        } else {
            Err(Xerr::SpecialStackUnderflow)
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
            Flow::Break(_) => continue,
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
    xs.backpatch_jump(if_org, rel)
}

fn core_word_then(xs: &mut State) -> Xresult {
    let if_org = match take_first_cond_flow(xs)? {
        Flow::If(org) => org,
        Flow::Else(org) => org,
        _ => return Err(Xerr::ControlFlowError),
    };  
    let offs = jump_offset(if_org, xs.code_origin());
    xs.backpatch_jump(if_org, offs)
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
                xs.backpatch_jump(endof_org, rel)?;
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
            xs.backpatch_jump(of_org, next_case_rel)?;
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
            Flow::Break(org) => {
                let offs = jump_offset(org, xs.code_origin() + 1);
                xs.backpatch_jump(org, offs)?;
            }
            Flow::Begin(begin_org) => {
                let offs = jump_offset(xs.code_origin(), begin_org);
                break xs.code_emit(Opcode::Jump(offs));
            }
            Flow::While(cond_org) => match xs.pop_flow()? {
                Flow::Begin(begin_org) => {
                    let offs = jump_offset(cond_org, xs.code_origin() + 1);
                    xs.backpatch_jump(cond_org, offs)?;
                    let offs = jump_offset(xs.code_origin(), begin_org);
                    break xs.code_emit(Opcode::Jump(offs));
                }
                _ => break Err(Xerr::ControlFlowError),
            },
            _ => break Err(Xerr::ControlFlowError),
        }
    }
}

fn core_word_break(xs: &mut State) -> Xresult {
    let org = xs.code_origin();
    xs.code_emit(Opcode::Jump(0))?;
    xs.push_flow(Flow::Break(org))
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
    let ptr = xs.data_stack.len();
    xs.push_special(Special::VecStackStart(ptr))
}

fn vec_builder_end(xs: &mut State) -> Xresult {
    match xs.pop_special()? {
        Special::VecStackStart(stack_ptr) => {
            let top_ptr = xs.data_stack.len();
            if top_ptr < stack_ptr {
                Err(Xerr::StackNotBalanced)
            } else {
                let mut v = Xvec::new();
                for x in &xs.data_stack[stack_ptr..] {
                    v.push_back_mut(x.clone());
                }
                for _ in 0..top_ptr - stack_ptr {
                    xs.pop_data()?;
                }
                xs.push_data(Cell::from(v))
            }
        }
    }
}

fn core_word_def_begin(xs: &mut State) -> Xresult {
    let name = xs.next_name()?;
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
            xs.backpatch_jump(start, offs)
        }
        _ => Err(Xerr::ControlFlowError),
    }
}

fn core_word_comment(xs: &mut State) -> Xresult {
    if let Some(src) = xs.ctx.source.as_mut(){
        src.skip_line();
    }
    OK
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
    let name = xs.next_name()?;
    let ff = xs.top_function_flow().ok_or(Xerr::ControlFlowError)?;
    let idx = ff.locals.len();
    ff.locals.push(name);
    xs.code_emit(Opcode::InitLocal(idx))
}

fn core_word_variable(xs: &mut State) -> Xresult {
    let name = xs.next_name()?;
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
    let name = xs.next_name()?;
    match xs.dict_entry(&name) {
        None => Err(Xerr::UnknownWord),
        Some(Entry::Variable(a)) => {
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
            Opcode::Call(a) => format!("call       {:#x}", a),
            Opcode::Unresolved(name) => format!("unresolved {:?}", &name),
            Opcode::NativeCall(x) => format!("callx      {:#x}", x.0 as usize),
            Opcode::Ret => format!("ret"),
            Opcode::JumpIf(offs) => format!("jumpif     ${:05x}", jumpaddr(at, offs)),
            Opcode::JumpIfNot(offs) => format!("jumpifnot  ${:05x}", jumpaddr(at, offs)),
            Opcode::Jump(offs) => format!("jump       ${:05x}", jumpaddr(at, offs)),
            Opcode::CaseOf(rel) => format!("caseof     ${:05x}", jumpaddr(at, rel)),
            Opcode::For(rel) => format!("for        ${:05x}", jumpaddr(at, rel)),
            Opcode::Loop(rel) => format!("loop       ${:05x}", jumpaddr(at, rel)),
            Opcode::Break(rel) => format!("break      ${:05x}", jumpaddr(at, rel)),
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

fn for_init(xs: &mut State) -> Xresult1<Loop> {
    match xs.pop_data()? {
        Cell::Int(n) =>
            Ok(Loop { range: 0..n as isize }),
        Cell::Vector(v) => {
            if v.len() == 2 {
                let start = vector_get(&v, 0)?.to_isize()?;
                let end = vector_get(&v, 1)?.to_isize()?;
                Ok(Loop { range: start..end })
            } else {
                Err(Xerr::TypeError)
            }
        }
        _ => Err(Xerr::TypeError),
    }
}

fn core_word_for(xs: &mut State) -> Xresult {
    let for_org = xs.code_origin();
    xs.code_emit(Opcode::For(0))?; // init and jump over if range is empty
    let body_org = xs.code_origin();
    xs.push_flow(Flow::For { for_org, body_org })
}

fn core_word_loop(xs: &mut State) -> Xresult {
    let loop_org = xs.code_origin();
    xs.code_emit(Opcode::Loop(0))?;
    let stop_org = xs.code_origin();
    loop {
        match xs.pop_flow()? {
            Flow::Break(org) => {
                let stop_rel = jump_offset(org, stop_org);
                xs.backpatch(org, Opcode::Break(stop_rel))?;
            }
            Flow::For { for_org, body_org } => {
                let stop_rel = jump_offset(for_org, stop_org);
                xs.backpatch(for_org, Opcode::For(stop_rel))?;
                let body_rel = jump_offset(loop_org, body_org);
                break xs.backpatch(loop_org, Opcode::Loop(body_rel));
            }
            _ => break Err(Xerr::ControlFlowError),
        }
    }
}

fn counter_value(xs: &mut State, n: usize) -> Xresult {
    let l = xs.loops[xs.ctx.ls_len..]
        .iter()
        .nth_back(n)
        .ok_or_else(|| Xerr::LoopStackUnderflow)?;
    let val = l.range.start;
    return xs.push_data(Cell::from(val))
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

fn core_word_len(xs: &mut State) -> Xresult {
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

pub(crate) fn vector_get_by_key<'a>(v: &'a Xvec, key: &Cell) -> Xresult1<&'a Cell> {
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

fn core_word_nth(xs: &mut State) -> Xresult {
    let index = xs.pop_data()?.to_isize()?;
    let v = xs.pop_data()?.to_vector()?;
    xs.push_data(vector_get(&v, index)?.clone())
}

fn core_word_set(xs: &mut State) -> Xresult {
    let val = xs.pop_data()?;
    let index = xs.pop_data()?.to_isize()?;
    let mut v = xs.pop_data()?.to_vector()?;
    let new_index = vector_relative_index(&v, index)?;
    if v.set_mut(new_index, val) {
        xs.push_data(Cell::from(v))
    } else {
        Err(Xerr::OutOfBounds)
    }
}

fn core_word_get(xs: &mut State) -> Xresult {
    let key = xs.pop_data()?;
    if !key.is_key() {
        return Err(Xerr::ExpectingKey);
    }
    if xs.top_data().ok_or(Xerr::StackUnderflow)?.is_key() {
        core_word_get(xs)?;
    }
    let v = xs.pop_data()?.to_vector()?;
    xs.push_data(vector_get_by_key(&v, &key)?.clone())
}

fn core_word_assoc(xs: &mut State) -> Xresult {
    let val = xs.pop_data()?;
    let key = xs.pop_data()?;
    let mut v = xs.pop_data()?.to_vector()?;
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
    xs.push_data(Cell::from(v))
}

fn core_word_sort(xs: &mut State) -> Xresult {
    use std::iter::FromIterator;
    let v = xs.pop_data()?.to_vector()?;
    let m: std::collections::BTreeSet<Cell> = v.iter().cloned().collect();
    let sorted = Xvec::from_iter(m.into_iter());
    xs.push_data(Cell::from(sorted))
}

fn core_word_sort_by_key(xs: &mut State) -> Xresult {
    use std::iter::FromIterator;
    let key = xs.pop_data()?;
    let v = xs.pop_data()?.to_vector()?;
    let mut m = std::collections::BTreeMap::new();
    for i in v.iter() {
        let pv = i.vec()?;
        m.insert(vector_get_by_key(pv, &key)?, i);
    }
    let sorted = Xvec::from_iter(m.values().map(|x| (*x).clone()));
    xs.push_data(Cell::from(sorted))
}

fn core_word_rev(xs: &mut State) -> Xresult {
    use std::iter::FromIterator;
    let v = xs.pop_data()?.to_vector()?;
    let rv = Xvec::from_iter(v.iter().rev().cloned());
    xs.push_data(Cell::from(rv))
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

fn core_word_exit(xs: &mut State) -> Xresult {
    xs.about_to_stop = true;
    let code = xs.pop_data()?.to_isize()?;
    Err(Xerr::Exit(code))
}

fn core_word_println(xs: &mut State) -> Xresult {
    core_word_print(xs)?;
    core_word_newline(xs)
}

fn core_word_print(xs: &mut State) -> Xresult {
    let val = xs.pop_data()?;
    let s = xs.format_cell(&val)?;
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

fn core_word_load(xs: &mut State) -> Xresult {
    let path = xs.pop_data()?.to_string()?;
    xs.load_source(&path)
}

fn core_word_meta(xs: &mut State) -> Xresult {
    let val = xs.top_data().and_then(|x| x.meta()).unwrap_or(&NIL).clone();
    xs.push_data(val)
}

fn core_word_with_meta(xs: &mut State) -> Xresult {
    let meta = xs.pop_data()?;
    let val = xs.pop_data()?.with_meta(meta);
    xs.push_data(val)
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
        let mut xs = State::boot().unwrap();
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
        assert_eq!(Err(Xerr::StackUnderflow), xs.interpret("1 ( 2 swap )"));
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::StackUnderflow), xs.interpret("1 swap"));
        let mut xs = State::boot().unwrap();
        xs.interpret("1 2 3 rot").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(3)), xs.pop_data());
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::StackUnderflow), xs.interpret("1 ( 2 3 rot )"));
        let mut xs = State::boot().unwrap();
        xs.interpret("1 2 over").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        assert_eq!(Err(Xerr::StackUnderflow), xs.interpret("1 over"));
    }

    #[test]
    fn test_if_flow() {
        let mut xs = State::boot().unwrap();
        xs.load("1 if 222 then").unwrap();
        let mut it = xs.code.iter();
        it.next().unwrap();
        assert_eq!(&Opcode::JumpIfNot(2), it.next().unwrap());
        let mut xs = State::boot().unwrap();
        xs.load("1 if 222 else 333 then").unwrap();
        let mut it = xs.code.iter();
        it.next().unwrap();
        assert_eq!(&Opcode::JumpIfNot(3), it.next().unwrap());
        it.next().unwrap();
        assert_eq!(&Opcode::Jump(2), it.next().unwrap());
        // test errors
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::ControlFlowError), xs.load("1 if 222 else 333"));
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::ControlFlowError), xs.load("1 if 222 else"));
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::ControlFlowError), xs.load("1 if 222"));
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::ControlFlowError), xs.load("1 else 222 then"));
        assert_eq!(Err(Xerr::ControlFlowError), xs.load("else 222 if"));
    }

    #[test]
    fn test_begin_again() {
        let mut xs = State::boot().unwrap();
        xs.interpret("0 begin dup 5 < while inc again").unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
        let mut xs = State::boot().unwrap();
        xs.load("begin break again").unwrap();
        let mut it = xs.code.iter();
        assert_eq!(&Opcode::Jump(2), it.next().unwrap());
        assert_eq!(&Opcode::Jump(-1), it.next().unwrap());
        let mut xs = State::boot().unwrap();
        xs.interpret("begin 1 0 until").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        xs.interpret("1 var x begin x while 0 -> x again").unwrap();
        assert_eq!(Err(Xerr::ControlFlowError), xs.load("if begin then repeat"));
        assert_eq!(Err(Xerr::ControlFlowError), xs.load("again begin"));
        assert_eq!(Err(Xerr::ControlFlowError), xs.load("begin then while"));
        assert_eq!(Err(Xerr::ControlFlowError), xs.load("until begin"));
        assert_eq!(Err(Xerr::ControlFlowError), xs.load("begin again until"));
        assert_eq!(Err(Xerr::ControlFlowError), xs.load("begin until again"));
    }

    #[test]
    fn test_length() {
        let mut xs = State::boot().unwrap();
        xs.interpret("[ 1 2 3 ] len").unwrap();
        assert_eq!(Ok(Cell::Int(3)), xs.pop_data());
        xs.interpret("\"12345\" len").unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
        let mut xs = State::boot().unwrap();
        let res = xs.interpret("len");
        assert_eq!(Err(Xerr::StackUnderflow), res);
        let res = xs.interpret("1 len");
        assert_eq!(Err(Xerr::TypeError), res);
    }

    #[test]
    fn test_loop_break() {
        let mut xs = State::boot().unwrap();
        xs.interpret("begin 1 break again").unwrap();
        let x = xs.pop_data().unwrap();
        assert_eq!(x.to_int(), Ok(1));
        assert_eq!(Err(Xerr::StackUnderflow), xs.pop_data());
        let mut xs = State::boot().unwrap();
        let res = xs.load("begin 1 again break");
        assert_eq!(Err(Xerr::ControlFlowError), res);
        let mut xs = State::boot().unwrap();
        xs.load("begin 1 if break else break then again").unwrap();
    }

    
    #[test]
    fn test_for_loop() {
        let mut xs = State::boot().unwrap();
        // short form for [0 3]
        xs.interpret("3 for I loop").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(0)), xs.pop_data());
        // start with negative
        let mut xs = State::boot().unwrap();
        xs.interpret("[ -1 1 ] for I loop").unwrap();
        assert_eq!(Ok(Cell::Int(0)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(-1)), xs.pop_data());
        // start from zero
        let mut xs = State::boot().unwrap();
        xs.interpret("[ 0 3 ] for I loop").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(0)), xs.pop_data());
        // counters
        let mut xs = State::boot().unwrap();
        xs.interpret("[ 5 6 ] for [ 2 3 ] for 1 for I J K loop loop loop")
            .unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(0)), xs.pop_data());
        // empty range
        let mut xs = State::boot().unwrap();
        xs.interpret("[ 3 0 ] for I loop").unwrap();
        assert_eq!(Err(Xerr::StackUnderflow), xs.pop_data());
        xs.interpret("[ 0 0 ] for I loop").unwrap();
        assert_eq!(Err(Xerr::StackUnderflow), xs.pop_data());
        // invalid range        
        assert_eq!(Err(Xerr::TypeError), xs.interpret("[ ] for I loop"));
        assert_eq!(Err(Xerr::TypeError), xs.interpret("[ 1 ] for I loop"));
        assert_eq!(Err(Xerr::TypeError), xs.interpret("[ 1 2 3 ] for I loop"));

    }

    #[test]
    fn test_get_set() {
        let mut xs = State::boot().unwrap();
        xs.interpret("[ 11 22 33 ] 2 nth").unwrap();
        assert_eq!(Cell::from(33isize), xs.pop_data().unwrap());
        xs.interpret("[ 11 22 33 ] -2 nth").unwrap();
        assert_eq!(Cell::from(22isize), xs.pop_data().unwrap());
        xs.interpret("[ 1 2 3 ] 0 5 set 0 nth").unwrap();
        assert_eq!(Cell::from(5isize), xs.pop_data().unwrap());
        assert_eq!(Err(Xerr::OutOfBounds), xs.interpret("[ 1 2 3 ] 100 nth"));
        assert_eq!(Err(Xerr::OutOfBounds), xs.interpret("[ 1 2 3 ] -100 nth"));
        assert_eq!(Err(Xerr::TypeError), xs.interpret("[ ] key: nth"));
    }

    #[test]
    fn test_lookup() {
        let mut xs = State::boot().unwrap();
        xs.interpret("[ x: 1 ] x: get").unwrap();
        assert_eq!(Cell::from(1isize), xs.pop_data().unwrap());
        xs.interpret("[ x: [ y: [ z: 10 ] ] ] x: y: z: get").unwrap();
        assert_eq!(Cell::from(10isize), xs.pop_data().unwrap());
        assert_eq!(Err(Xerr::NotFound), xs.interpret("[ x: [ y: [1 2 3 ] ] ] f: y: x: get"));
    }

    #[test]
    fn test_assoc() {
        let mut xs = State::boot().unwrap();
        xs.interpret("[ ] x: 1 assoc y: 2 assoc").unwrap();
        let mut m = Xvec::new();
        m.push_back_mut(Cell::Key("x".into()));
        m.push_back_mut(Cell::from(1u32));
        m.push_back_mut(Cell::Key("y".into()));
        m.push_back_mut(Cell::from(2u32));
        assert_eq!(Ok(m), xs.pop_data().unwrap().to_vector());
        xs.interpret("[ x: 1 ] x: 2 assoc x: get").unwrap();
        assert_eq!(Xcell::from(2usize), xs.pop_data().unwrap());
        xs.interpret("[ x: 1 y: 3 ] x: 5 assoc x: get").unwrap();
    }

    #[test]
    fn test_locals() {
        let mut xs = State::boot().unwrap();
        xs.interpret(": f local x local y x y y x ; 1 2 f").unwrap();
        assert_eq!(Cell::Int(2), xs.pop_data().unwrap());
        assert_eq!(Cell::Int(1), xs.pop_data().unwrap());
        assert_eq!(Cell::Int(1), xs.pop_data().unwrap());
        assert_eq!(Cell::Int(2), xs.pop_data().unwrap());
        assert_eq!(Err(Xerr::UnknownWord), xs.interpret("x y"));
    }

    #[test]
    fn test_base() {
        let mut xs = State::boot().unwrap();
        xs.interpret("HEX 16 BASE assert-eq").unwrap();
        xs.interpret("DEC 10 BASE assert-eq").unwrap();
        xs.interpret("OCT 8 BASE assert-eq").unwrap();
        xs.interpret("BIN 2 BASE assert-eq").unwrap();
    }

    #[test]
    fn test_immediate() {
        let mut xs = State::boot().unwrap();
        let res = xs.load(": f [ ] 0 nth immediate ; f");
        assert_eq!(Err(Xerr::OutOfBounds), res);
    }

    #[test]
    fn test_nested_interpreter() {
        let mut xs = State::boot().unwrap();
        xs.load("( 3 5 * )").unwrap();
        xs.run().unwrap();
        assert_eq!(Ok(Cell::Int(15)), xs.pop_data());
        xs.interpret("( 2 2 + )").unwrap();
        assert_eq!(Ok(Cell::Int(4)), xs.pop_data());
        xs.interpret("( 10 var x 2 var y ( x y * ) )").unwrap();
        assert_eq!(Ok(Cell::Int(20)), xs.pop_data());
        xs.interpret("( 3 var n [ n for I loop ] )").unwrap();
        let v = xs.pop_data().unwrap().to_vector().unwrap();
        assert_eq!(3, v.len());
    }

    #[test]
    fn test_defvar() {
        let mut xs = State::boot().unwrap();
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
        let mut xs = State::boot().unwrap();
        xs.defwordself( "self1", |xs| {
            assert_eq!(Ok(ONE), xs.pop_data());
            xs.push_data(ZERO)
        }, ONE).unwrap();
        xs.interpret("self1").unwrap();
        assert_eq!(Ok(ZERO), xs.pop_data());
    }

    #[test]
    fn test_caseof() {
        let mut xs = State::boot().unwrap();
        xs.interpret("2 case 1 of 100 endof 2 of 200 endof endcase").unwrap();
        assert_eq!(Ok(Cell::Int(200)), xs.pop_data());
        xs.interpret("5 case 1 of 100 endof 2 of 200 endof 0 endcase").unwrap();
        assert_eq!(Ok(ZERO), xs.pop_data());
        xs.interpret("10 for I I case 5 of break endof drop endcase loop").unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
    }

    #[test]
    fn test_fmt_prefix() {
        let mut xs = State::boot().unwrap();
        xs.console = Some(String::new());
        xs.interpret("255 HEX print").unwrap();
        assert_eq!(Some("0xFF".to_string()), xs.console);
        xs.console = Some(String::new());
        xs.interpret("255 NO-PREFIX HEX print").unwrap();
        assert_eq!(Some("FF".to_string()), xs.console);
        xs.console = Some(String::new());
        xs.interpret("[ 255 ] NO-PREFIX HEX print").unwrap();
        assert_eq!(Some("[ FF ]".to_string()), xs.console);
    }

    #[test]
    fn test_rev() {
        let mut xs = State::boot().unwrap();
        xs.interpret("[ 1 2 3 ] rev").unwrap();
        let mut v = Xvec::new();
        v.push_back_mut(Cell::Int(3));
        v.push_back_mut(Cell::Int(2));
        v.push_back_mut(Cell::Int(1));
        assert_eq!(Ok(&v), xs.pop_data().unwrap().vec());
    }

    #[test]
    fn test_sort() {
        let mut xs = State::boot().unwrap();
        xs.interpret("[ 2 3 1 ] sort").unwrap();
        let mut v = Xvec::new();
        v.push_back_mut(Cell::Int(1));
        v.push_back_mut(Cell::Int(2));
        v.push_back_mut(Cell::Int(3));
        assert_eq!(Ok(&v), xs.pop_data().unwrap().vec());
    }

    #[test]
    fn test_sort_by_key() {
        let mut xs = State::boot().unwrap();
        xs.interpret("[ [ \"k\" 2 ] [ \"k\" 3 ] [ \"k\" 1 ] ] \"k\" sort-by-key var x").unwrap();
        xs.interpret("[ 3 for x I nth \"k\" get loop ]").unwrap();
        let mut v = Xvec::new();
        v.push_back_mut(Cell::Int(1));
        v.push_back_mut(Cell::Int(2));
        v.push_back_mut(Cell::Int(3));
        assert_eq!(Ok(&v), xs.pop_data().unwrap().vec());
    }


    fn collect_ints(xs: &State) -> Vec<isize> {
        xs.data_stack.iter().cloned().map(|x| x.to_isize().unwrap()).collect()
    }

    #[test]
    fn test_reverse_next() {
        let mut xs = State::boot().unwrap();
        assert_eq!(OK, xs.rnext());
        xs.start_reverse_debugging();
        xs.load(r#"
        100 4 /
        3 *
        5 +
        "#).unwrap();
        xs.run().unwrap();
        assert_eq!(vec![80], collect_ints(&xs));
        xs.rnext().unwrap();
        assert_eq!(vec![75, 5], collect_ints(&xs));
        xs.rnext().unwrap();
        assert_eq!(vec![75], collect_ints(&xs));
        xs.rnext().unwrap();
        assert_eq!(vec![25, 3], collect_ints(&xs));
        xs.rnext().unwrap();
        assert_eq!(vec![25], collect_ints(&xs));
        xs.rnext().unwrap();
        assert_eq!(vec![100, 4], collect_ints(&xs));
        xs.rnext().unwrap();
        assert_eq!(vec![100], collect_ints(&xs));
        xs.rnext().unwrap();
        assert_eq!(0, collect_ints(&xs).len());
        assert_eq!(0, xs.ip());
        xs.rnext().unwrap();
        // replay again
        assert_eq!(0, xs.ip());
        assert_eq!(OK, xs.next());
        assert_eq!(OK, xs.next());
        assert_eq!(vec![100, 4], collect_ints(&xs));
        assert_eq!(OK, xs.next());
        // rerun div few times
        assert_eq!(vec![25], collect_ints(&xs));
        assert_eq!(OK, xs.rnext());
        assert_eq!(vec![100, 4], collect_ints(&xs));
        assert_eq!(OK, xs.next());
        assert_eq!(vec![25], collect_ints(&xs));
    }

    #[test]
    fn test_reverse_vec() {
        let snapshot = |xs: &State| (xs.data_stack.clone(), xs.loops.clone());
        let mut xs = State::boot().unwrap();
        xs.start_reverse_debugging();
        xs.load("[ 3 for I loop ] len").unwrap();
        let mut log = Vec::new();
        for _ in 0..3 {
            while xs.ip() != xs.code.len() {
                log.push(snapshot(&xs));
                xs.next().unwrap();
            }
            while xs.ip() != 0 {
                xs.rnext().unwrap();
                let expected_state = log.pop().unwrap();
                assert_eq!(expected_state, snapshot(&xs));
            }
        }
    }

    #[test]
    fn test_reverse_recur() {
        let snapshot = |xs: &State| (
             xs.data_stack.clone(),
             xs.return_stack.clone());
        let mut xs = State::boot().unwrap();
        xs.start_reverse_debugging();
        xs.load(r#"
       : tower-of-hanoi
            local aux
            local to
            local from
            local n
            n 1 = if
                [ n from to]
            else
                n dec from aux to tower-of-hanoi
                [ n from to ]
                n dec aux to from tower-of-hanoi
            then
        ;        
        4 "a" "c" "b" tower-of-hanoi
        "#).unwrap();
        
        let mut log = Vec::new();
        for _ in 0..3 {
            while xs.ip() != xs.code.len() {
                log.push(snapshot(&xs));
                xs.next().unwrap();
            }
            while xs.ip() != 0 {
                xs.rnext().unwrap();
                let expected_state = log.pop().unwrap();
                assert_eq!(expected_state, snapshot(&xs));
            }
        }
    }

    #[test]
    fn test_meta() {
        let mut xs = State::boot().unwrap();
        xs.interpret(" 123 \"test\" with-meta").unwrap();
        assert_eq!(xs.top_data(), Some(&Cell::Int(123)));
        xs.interpret("meta").unwrap();
        assert_eq!(xs.top_data(), Some(&Cell::Str(Xstr::from("test"))));
    }

    #[test]
    fn test_exit_err() {
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::Exit(-1)), xs.interpret("-1 exit drop"));
        let mut xs = State::boot().unwrap();
        xs.load("0 exit +").unwrap();
        assert_eq!(Err(Xerr::Exit(0)), xs.run());
    }
}
