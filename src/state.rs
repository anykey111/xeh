use crate::bitstr_ext;
use crate::bitstr_ext::BitstrState;
use crate::cell::*;
use crate::error::*;
use crate::fmt_flags::FmtFlags;
use crate::lex::*;
use crate::opcodes::*;

use std::iter::FromIterator;
use std::ops::Range;

#[derive(Debug, Clone, PartialEq)]
enum Entry {
    Constant(Cell),
    Variable(CellRef),
    Function {
        immediate: bool,
        xf: Xfn,
        len: Option<usize>,
    },
}

#[derive(Clone)]
struct DictEntry {
    name: Xstr,
    entry: Entry,
    help: CellRef,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct FunctionFlow {
    dict_idx: usize,
    start: usize,
    locals: Vec<Xsubstr>,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Flow {
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
    Do { for_org: usize, body_org: usize },
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

#[derive(Clone, PartialEq, Debug)]
enum ContextMode {
    // assemble bytecode
    Compile,
    // normal evaluation
    Eval,
    // meta evaluation
    MetaEval,
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
    SwapRef(CellRef, Cell),
}

#[derive(Clone)]
pub struct ErrorContext {
    err: Xerr,
    location: Option<TokenLocation>,
}

#[derive(Default, Clone)]
pub struct State {
    dict: Vec<DictEntry>,
    heap: Vec<Cell>,
    code: Vec<Opcode>,
    debug_map: Vec<Xsubstr>,
    sources: Vec<(Xstr, Xstr)>,
    input: Vec<Lex>,
    data_stack: Vec<Cell>,
    return_stack: Vec<Frame>,
    flow_stack: Vec<Flow>,
    loops: Vec<Loop>,
    special: Vec<Special>,
    ctx: Context,
    nested: Vec<Context>,
    // expose for rrlog debug
    pub reverse_log: Option<Vec<ReverseStep>>,
    stdout: Option<String>,
    last_error: Option<ErrorContext>,
    last_token: Option<Xsubstr>,
    pub(crate) about_to_stop: bool,
    pub(crate) bitstr_mod: BitstrState,
    // formatter flags
    fmt_flags: CellRef,
    // d2 canvas
    pub(crate) d2: CellRef,
}

impl State {
    pub fn format_cell(&self, val: &Cell) -> Xresult1<String> {
        let flags = self
            .get_var(self.fmt_flags)
            .map(|val| FmtFlags::from(val))?;
        Ok(format!("{:1$?}", val, flags.into_raw()))
    }

    pub fn fmt_opcode(&self, ip: usize, op: &Opcode) -> String {
        match op {
            Opcode::Call(x) => {
                let name = self
                    .dict
                    .iter()
                    .rev()
                    .find(|e| match e.entry {
                        Entry::Function {
                            xf: Xfn::Interp(f), ..
                        } => f == *x,
                        _ => false,
                    })
                    .map(|e| e.name.as_str())
                    .unwrap_or_default();
                format!("call {:#x} # {}", x, name)
            }
            Opcode::NativeCall(x) => {
                let name = self
                    .dict
                    .iter()
                    .rev()
                    .find(|e| match e.entry {
                        Entry::Function {
                            xf: Xfn::Native(f), ..
                        } => f == *x,
                        _ => false,
                    })
                    .map(|e| e.name.as_str())
                    .unwrap_or_default();
                format!("nativecall {:#x} # {}", x.0 as usize, name)
            }
            Opcode::Resolve(name) => format!("resolve    {:?}", &name),
            Opcode::Ret => format!("ret"),
            Opcode::JumpIf(rel) => format!("jumpif     #{:#05x}", rel.calculate(ip)),
            Opcode::JumpIfNot(rel) => format!("jumpifnot  {:#05x}", rel.calculate(ip)),
            Opcode::Jump(rel) => format!("jump       {:#05x}", rel.calculate(ip)),
            Opcode::CaseOf(rel) => format!("caseof     {:#05x}", rel.calculate(ip)),
            Opcode::Do(rel) => format!("do         {:#05x}", rel.calculate(ip)),
            Opcode::Loop(rel) => format!("loop       {:#05x}", rel.calculate(ip)),
            Opcode::Break(rel) => format!("break      {:#05x}", rel.calculate(ip)),
            Opcode::Load(a) => format!("load       {}", a.index()),
            Opcode::LoadI64(i) => format!("loadi64    {}", i),
            Opcode::LoadF64(i) => format!("loadf64    {}", i),
            Opcode::LoadNil => format!("loadnil"),
            Opcode::LoadCell(c) => format!("loadcell  {:?}", c),
            Opcode::Store(a) => format!("store      {}", a.index()),
            Opcode::InitLocal(i) => format!("initlocal  {}", i),
            Opcode::LoadLocal(i) => format!("loadlocal  {}", i),
        }
    }

    pub fn word_list(&self) -> Vec<Xstr> {
        Vec::from_iter(self.dict.iter().map(|e| e.name.clone()))
    }

    fn clear_last_error(&mut self) {
        self.last_error = None;
    }

    pub fn last_error(&self) -> Option<&Xerr> {
        self.last_error.as_ref().map(|x| &x.err)
    }
    pub fn last_err_location(&self) -> Option<&TokenLocation> {
        self.last_error.as_ref().and_then(|x| x.location.as_ref())
    }

    pub fn location_from_current_ip(&self) -> Option<TokenLocation> {
        self.debug_map
            .get(self.ip())
            .and_then(|tok| token_location(&self.sources, tok))
    }

    pub fn pretty_error(&self) -> Option<String> {
        let ec = self.last_error.as_ref()?;
        let errmsg = if let Some(loc) = &ec.location {
            format!("{}\n{:?}", ec.err, loc)
        } else {
            format!("{}", ec.err)
        };
        Some(errmsg)
    }

    pub fn print(&mut self, msg: &str) {
        if let Some(out) = self.stdout.as_mut() {
            out.push_str(msg);
        } else {
            #[cfg(feature = "stdio")]
            print!("{}", msg);
        }
    }

    pub fn intercept_stdout(&mut self, yes: bool) {
        if yes {
            if self.stdout.is_none() {
                self.stdout = Some(String::new());
            }
        } else {
            self.stdout = None;
        }
    }

    pub fn read_stdout(&mut self) -> Option<String> {
        self.stdout.as_mut().map(|s| {
            let result = s.clone();
            s.clear();
            result
        })
    }

    pub fn stdout(&mut self) -> Option<&mut String> {
        self.stdout.as_mut()
    }

    pub fn set_binary_input(&mut self, s: Xbitstr) -> Xresult {
        bitstr_ext::open_bitstr(self, s)
    }

    pub fn compile(&mut self, s: &str) -> Xresult {
        self.compile_xstr(s.into())
    }

    pub fn compile_xstr(&mut self, s: Xstr) -> Xresult {
        self.context_open(ContextMode::Compile)?;
        self.intern_source(s.into(), None)?;
        self.build0()?;
        self.context_close()
    }

    pub fn eval_from_file(&mut self, path: &str) -> Xresult {
        let s = crate::file::read_source_file(path)?;
        self.intern_source(s.into(), Some(path))?;
        self.context_open(ContextMode::Eval)?;
        self.build0()?;
        self.context_close()
    }

    pub fn eval(&mut self, s: &str) -> Xresult {
        self.evalxstr(s.into())
    }

    pub fn evalxstr(&mut self, s: Xstr) -> Xresult {
        self.intern_source(s, None)?;
        self.context_open(ContextMode::Eval)?;
        self.build0()?;
        self.context_close()
    }

    fn intern_source(&mut self, buf: Xstr, path: Option<&str>) -> Xresult {
        let id = self.sources.len();
        let lex = Lex::new(buf.clone());
        let name = if let Some(name) = path {
            name.into()
        } else {
            format!("<buffer#{}>", id).into()
        };
        self.sources.push((name, buf));
        self.input.push(lex);
        OK
    }

    fn build0(&mut self) -> Xresult {
        self.clear_last_error();
        self.build1().map_err(|e| {
            // build-time error
            if self.last_error.is_none() {
                let tok = self.last_token.take();
                let location = tok.and_then(|tok| token_location(&self.sources, &tok));
                self.last_error = Some(ErrorContext {
                    err: e.clone(),
                    location,
                });
            }
            e
        })
    }

    fn build1(&mut self) -> Xresult {
        let ctx_depth = self.nested.len();
        loop {
            if self.ctx.mode == ContextMode::MetaEval && !self.has_pending_flow() {
                self.run()?;
            }
            match self.next_token()? {
                Tok::EndOfInput => {
                    if self.nested.len() != ctx_depth {
                        break Err(Xerr::unbalanced_context());
                    }
                    if self.has_pending_flow() {
                        break Xerr::control_flow_error(self.flow_stack.last());
                    }
                    break OK;
                }
                Tok::Literal(val) => {
                    self.code_emit_value(val)?;
                }
                Tok::Word(name) => {
                    // search for local variables first
                    if let Some(i) = self
                        .top_function_flow()
                        .and_then(|ff| ff.locals.iter().rposition(|x| x == name.as_str()))
                    {
                        self.code_emit(Opcode::LoadLocal(i))?;
                    } else {
                        self.build_word(name)?;
                    }
                }
            }
        }
    }

    fn build_word(&mut self, name: Xsubstr) -> Xresult {
        match self.dict_entry(name.as_str()) {
            None => self.code_emit(Opcode::Resolve(Xstr::from(name.as_str()))),
            Some(Entry::Constant(c)) => {
                let op = self.load_value_opcode(c.clone());
                self.code_emit(op)
            }
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
                self.run_immediate(xf)
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

    fn next_name(&mut self) -> Xresult1<Xsubstr> {
        let prev_token = self.last_token.clone();
        match self.next_token()? {
            Tok::Word(name) => Ok(name),
            _ => {
                if prev_token.is_some() {
                    // move error marker to prev token
                    self.last_token = prev_token;
                }
                Err(Xerr::ExpectingName)
            },
        }
    }

    fn next_token(&mut self) -> Xresult1<Tok> {
        let lex = self.input.last_mut().expect("input source");
        let res = lex.next();
        self.last_token = Some(lex.last_substr());
        if let Ok(Tok::EndOfInput) = &res {
            self.input.pop();
        }
        res
    }

    fn context_open(&mut self, mode: ContextMode) -> Xresult {
        let mut tmp = Context {
            ds_len: 0,
            cs_len: self.code.len(),
            rs_len: self.return_stack.len(),
            fs_len: self.flow_stack.len(),
            ls_len: self.loops.len(),
            ss_ptr: self.special.len(),
            ip: self.code_origin(),
            mode,
        };
        if tmp.mode == ContextMode::MetaEval {
            // set bottom stack limit for meta interpreter
            tmp.ds_len = self.data_stack.len();
        }
        std::mem::swap(&mut self.ctx, &mut tmp);
        self.nested.push(tmp);
        OK
    }

    fn context_close(&mut self) -> Xresult {
        let mut prev = self.nested.pop().ok_or_else(|| Xerr::unbalanced_context())?;
        if self.ctx.mode != ContextMode::Compile {
            self.run()?;
            if self.ctx.mode == ContextMode::MetaEval {
                // purge meta context code after evaluation
                self.code.truncate(self.ctx.cs_len);
                self.debug_map.truncate(self.ctx.cs_len);
            }
        }
        if prev.mode == self.ctx.mode {
            if self.ctx.mode == ContextMode::Eval {
                // preserve current ip value
                prev.ip = self.ctx.ip;
            }
        } else if self.ctx.mode == ContextMode::MetaEval {
            // emit meta-evaluation result
            while self.data_stack.len() > self.ctx.ds_len {
                let val = self.pop_data()?;
                self.code_emit_value(val)?;
            }
        }
        self.ctx = prev;
        OK
    }

    fn has_pending_flow(&self) -> bool {
        (self.flow_stack.len() - self.ctx.fs_len) > 0
    }

    pub fn boot() -> Xresult1<State> {
        let mut xs = State::default();
        #[cfg(not(feature = "stdio"))]
        xs.intercept_stdout(true);
        xs.fmt_flags = xs.defvar_anonymous(FmtFlags::default().build())?;
        xs.load_core()?;
        crate::arith::load(&mut xs)?;
        crate::bitstr_ext::load(&mut xs)?;
        Ok(xs)
    }

    pub fn defvar(&mut self, name: &str, val: Cell) -> Xresult1<CellRef> {
        // shadow previous definition
        let cref = self.alloc_cell(val)?;
        self.dict_insert(name, Entry::Variable(cref))?;
        Ok(cref)
    }

    pub fn defvar_anonymous(&mut self, val: Cell) -> Xresult1<CellRef> {
        self.alloc_cell(val)
    }

    //#[cfg(test)]
    pub fn get_var_value(&self, name: &str) -> Xresult1<&Cell> {
        match self.dict_entry(name) {
            None => Err(Xerr::UnknownWord(Xstr::from(name))),
            Some(Entry::Variable(a)) => self.cell_ref(*a),
            _ => Err(Xerr::TypeError),
        }
    }

    pub fn get_var(&self, cref: CellRef) -> Xresult1<&Cell> {
        self.cell_ref(cref)
    }

    pub fn set_var(&mut self, cref: CellRef, val: Cell) -> Xresult {
        self.swap_cell_ref(cref, val)
    }

    fn dict_add_word(&mut self, name: &str, f: XfnType, immediate: bool) -> Xresult {
        let xf = Xfn::Native(XfnPtr(f));
        self.dict_insert(
            name.into(),
            Entry::Function {
                immediate,
                xf,
                len: None,
            },
        )?;
        OK
    }

    pub fn defword(&mut self, name: &str, f: XfnType) -> Xresult {
        self.dict_add_word(name, f, false)?;
        OK
    }

    pub fn def_immediate(&mut self, name: &str, f: XfnType) -> Xresult {
        self.dict_add_word(name, f, true)
    }

    pub fn defwordself(&mut self, name: &str, x: XfnType, slf: Cell) -> Xresult {
        let start = self.code_origin();
        self.code_emit(Opcode::Jump(RelativeJump::uninit()))?;
        let fn_addr = self.code_origin();
        self.code_emit_value(slf)?;

        self.code_emit(Opcode::NativeCall(XfnPtr(x)))?;
        self.code_emit(Opcode::Ret)?;
        let len = self.code_origin() - start;
        self.dict_insert(
            name.into(),
            Entry::Function {
                immediate: false,
                xf: Xfn::Interp(fn_addr),
                len: Some(len),
            },
        )?;
        let offs = jump_offset(start, self.code_origin());
        self.backpatch_jump(start, offs)?;
        OK
    }

    pub fn help_str(&self, name: &str) -> Option<&Cell> {
        let cref = self.dict_key(name)?.help;
        self.get_var(cref).ok()
    }

    fn load_core(&mut self) -> Xresult {
        self.dict_insert(
            arcstr::literal!("true").as_str(),
            Entry::Constant(TRUE),
        )?;
        self.dict_insert(
            arcstr::literal!("false").as_str(),
            Entry::Constant(FALSE),
        )?;
        self.def_immediate("if", core_word_if)?;
        self.def_immediate("else", core_word_else)?;
        self.def_immediate("endif", core_word_endif)?;
        self.def_immediate("case", case_word)?;
        self.def_immediate("of", of_word)?;
        self.def_immediate("endof", endof_word)?;
        self.def_immediate("endcase", endcase_word)?;
        self.def_immediate("begin", core_word_begin)?;
        self.def_immediate("while", core_word_while)?;
        self.def_immediate("until", core_word_until)?;
        self.def_immediate("leave", core_word_leave)?;
        self.def_immediate("repeat", core_word_repeat)?;
        self.def_immediate("again", core_word_again)?;
        self.def_immediate("[", core_word_vec_begin)?;
        self.def_immediate("]", core_word_vec_end)?;
        self.def_immediate(":", core_word_def_begin)?;
        self.def_immediate(";", core_word_def_end)?;
        self.def_immediate("#", core_word_comment)?;
        self.def_immediate("immediate", core_word_immediate)?;
        self.def_immediate("local", core_word_def_local)?;
        self.def_immediate("var", core_word_variable)?;
        self.def_immediate("->", core_word_setvar)?;
        self.def_immediate("nil", core_word_nil)?;
        self.def_immediate("(", core_word_nested_begin)?;
        self.def_immediate(")", core_word_nested_end)?;
        self.def_immediate("const", core_word_const)?;
        self.def_immediate("do", core_word_do)?;
        self.def_immediate("loop", core_word_loop)?;
        self.defword("doc", core_word_doc)?;
        self.defword("help", core_word_help)?;
        self.defword("help-str", core_word_help_str)?;
        self.defword("I", core_word_counter_i)?;
        self.defword("J", core_word_counter_j)?;
        self.defword("K", core_word_counter_k)?;
        self.defword("length", core_word_length)?;
        self.defword("get", core_word_get)?;
        self.defword("sort", core_word_sort)?;
        self.defword("reverse", core_word_reverse)?;
        self.defword("dup", |xs| xs.dup_data())?;
        self.defword("drop", |xs| xs.drop_data())?;
        self.defword("swap", |xs| xs.swap_data())?;
        self.defword("rot", |xs| xs.rot_data())?;
        self.defword("over", |xs| xs.over_data())?;
        self.defword("depth", core_word_depth)?;
        self.defword("assert", core_word_assert)?;
        self.defword("assert-eq", core_word_assert_eq)?;
        self.defword("exit", core_word_exit)?;
        self.defword(".s", core_word_display_stack)?;
        self.defword("println", core_word_println)?;
        self.defword("print", core_word_print)?;
        self.defword("newline", core_word_newline)?;
        self.defword("file-write", crate::file::core_word_file_write)?;
        self.defword("load", core_word_load)?;
        self.defword("tag-of", core_word_tag_of)?;
        self.defword("with-tag", core_word_with_tag)?;
        self.defword("insert-tagged", core_word_insert_tagged)?;
        self.defword("get-tagged", core_word_get_tagged)?;
        self.defword("HEX", |xs| set_fmt_base(xs, 16))?;
        self.defword("DEC", |xs| set_fmt_base(xs, 10))?;
        self.defword("OCT", |xs| set_fmt_base(xs, 8))?;
        self.defword("BIN", |xs| set_fmt_base(xs, 2))?;
        self.defword("PREFIX", |xs| set_fmt_prefix(xs, true))?;
        self.defword("NO-PREFIX", |xs| set_fmt_prefix(xs, false))?;
        self.defword("TAGS", |xs| set_fmt_tags(xs, true))?;
        self.defword("NO-TAGS", |xs| set_fmt_tags(xs, false))?;
        OK
    }

    fn dict_insert(&mut self, name: &str, entry: Entry) -> Xresult1<usize> {
        let wa = self.dict.len();
        let help = if self.ctx.mode == ContextMode::MetaEval {
            CellRef::default()
        } else {
            self.defvar_anonymous(NIL)?
        };
        self.dict.push(DictEntry {
            name: Xstr::from(name),
            entry,
            help,
        });
        Ok(wa)
    }

    fn dict_entry(&self, name: &str) -> Option<&Entry> {
        self.dict_key(name).map(|x| &x.entry)
    }

    fn dict_key(&self, name: &str) -> Option<&DictEntry> {
        self.dict.iter().rfind(|x| x.name == name)
    }

    fn code_origin(&self) -> usize {
        self.code.len()
    }

    fn load_value_opcode(&self, val: Cell) -> Opcode {
        match val {
            Cell::Int(i) if i64::MIN as Xint <= i && i <= i64::MAX as Xint => {
                Opcode::LoadI64(i as i64)
            }
            Cell::Nil => Opcode::LoadNil,
            val => Opcode::LoadCell(CellBox::from(val)),
        }
    }

    fn code_emit_value(&mut self, val: Cell) -> Xresult {
        let op = self.load_value_opcode(val);
        self.code_emit(op)
    }

    fn code_emit(&mut self, op: Opcode) -> Xresult {
        let at = self.code.len();
        let len = self.debug_map.len();
        let loc = self.last_token.clone().unwrap_or_default();
        if at < len {
            self.debug_map[at] = loc;
        } else if at == len {
            self.debug_map.push(loc);
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

    fn backpatch_jump(&mut self, at: usize, offs: RelativeJump) -> Xresult {
        let insn = match self.code.get(at).ok_or_else(|| Xerr::InternalError)? {
            Opcode::Jump(_) => Opcode::Jump(offs),
            Opcode::JumpIf(_) => Opcode::JumpIf(offs),
            Opcode::JumpIfNot(_) => Opcode::JumpIfNot(offs),
            Opcode::CaseOf(_) => Opcode::CaseOf(offs),
            _ => panic!("not a jump instruction at={}", at),
        };
        self.backpatch(at, insn)
    }

    fn cell_ref(&self, cref: CellRef) -> Xresult1<&Cell> {
        self.heap
            .get(cref.index())
            .ok_or_else(|| Xerr::InvalidAddress)
    }

    fn swap_cell_ref(&mut self, cref: CellRef, val: Cell) -> Xresult {
        if self.ctx.mode == ContextMode::MetaEval {
            return Err(Xerr::const_context());
        }
        let mut old = val;
        std::mem::swap(
            self.heap
                .get_mut(cref.index())
                .ok_or_else(|| Xerr::InvalidAddress)?,
            &mut old,
        );
        if self.is_recording() {
            self.add_reverse_step(ReverseStep::SwapRef(cref, old));
        }
        OK
    }

    fn alloc_cell(&mut self, val: Cell) -> Xresult1<CellRef> {
        if self.ctx.mode == ContextMode::MetaEval {
            return Err(Xerr::const_context());
        }
        let idx = self.heap.len();
        self.heap.push(val);
        Ok(CellRef::from_index(idx))
    }

    fn run_immediate(&mut self, x: Xfn) -> Xresult {
        match x {
            Xfn::Native(x) => x.0(self),
            Xfn::Interp(x) => {
                let old_ip = self.ip();
                self.push_return(old_ip)?;
                self.set_ip(x);
                self.run()
            }
        }
    }

    pub fn run(&mut self) -> Xresult {
        self.clear_last_error();
        while self.is_running() {
            self.fetch_and_run().map_err(|e| {
                self.set_runtime_err_location(&e);
                e
            })?;
        }
        OK
    }

    fn set_runtime_err_location(&mut self, e: &Xerr) {
        if self.last_error.is_none() {
            let location = self.location_from_current_ip();
            self.last_error = Some(ErrorContext {
                err: e.clone(),
                location,
            });
        }
    }

    fn fetch_and_run(&mut self) -> Xresult {
        let ip = self.ip();
        match &self.code[ip] {
            Opcode::Jump(rel) => {
                let new_ip = rel.calculate(ip);
                self.set_ip(new_ip);
            }
            Opcode::JumpIf(rel) => {
                let new_ip = rel.calculate(ip);
                if self.pop_data()?.cond_true()? {
                    self.set_ip(new_ip);
                } else {
                    self.next_ip();
                }
            }
            Opcode::JumpIfNot(rel) => {
                let new_ip = rel.calculate(ip);
                if !self.pop_data()?.cond_true()? {
                    self.set_ip(new_ip);
                } else {
                    self.next_ip();
                }
            }
            Opcode::CaseOf(rel) => {
                let new_ip = rel.calculate(ip);
                let a = self.pop_data()?;
                let b = self.top_data()?;
                if &a == b {
                    self.pop_data()?;
                    self.next_ip();
                } else {
                    self.set_ip(new_ip);
                }
            }
            Opcode::Call(a) => {
                let fn_addr = *a;
                self.push_return(ip + 1)?;
                self.set_ip(fn_addr);
            }
            Opcode::NativeCall(x) => {
                x.0(self)?;
                self.next_ip();
            }
            Opcode::Ret => {
                let frame = self.pop_return()?;
                self.set_ip(frame.return_to);
            }
            Opcode::Resolve(ref name) => {
                let e = self
                    .dict_entry(&name)
                    .ok_or_else(|| Xerr::UnknownWord(name.clone()))?;
                match e {
                    Entry::Constant(c) => {
                        let op = self.load_value_opcode(c.clone());
                        self.backpatch(ip, op)?;
                        self.fetch_and_run()?;
                    }
                    Entry::Variable(a) => {
                        let op = Opcode::Load(*a);
                        self.backpatch(ip, op)?;
                        self.fetch_and_run()?;
                    }
                    Entry::Function {
                        xf: Xfn::Interp(x), ..
                    } => {
                        let op = Opcode::Call(*x);
                        self.backpatch(ip, op)?;
                        self.fetch_and_run()?;
                    }
                    Entry::Function {
                        xf: Xfn::Native(x), ..
                    } => {
                        let op = Opcode::NativeCall(*x);
                        self.backpatch(ip, op)?;
                        self.fetch_and_run()?;
                    }
                }
            }
            Opcode::LoadF64(x) => {
                let val = Cell::from(*x);
                self.push_data(val)?;
                self.next_ip();
            }
            Opcode::LoadI64(x) => {
                let val = Cell::from(*x);
                self.push_data(val)?;
                self.next_ip();
            }
            Opcode::LoadNil => {
                self.push_data(Cell::Nil)?;
                self.next_ip();
            }
            Opcode::LoadCell(c) => {
                let val = c.as_ref().clone();
                self.push_data(val)?;
                self.next_ip();
            }
            Opcode::Load(cref) => {
                let cref = *cref;
                let val = self.cell_ref(cref)?.clone();
                self.push_data(val)?;
                self.next_ip();
            }
            Opcode::Store(cref) => {
                let cref = *cref;
                let val = self.pop_data()?;
                self.swap_cell_ref(cref, val)?;
                self.next_ip();
            }
            Opcode::InitLocal(i) => {
                let idx = *i;
                let val = self.pop_data()?;
                let frame = self.top_frame()?;
                debug_assert_eq!(idx, frame.locals.len());
                frame.locals.push(val);
                if self.is_recording() {
                    self.add_reverse_step(ReverseStep::DropLocal(idx));
                }
                self.next_ip();
            }
            Opcode::LoadLocal(i) => {
                let i = *i;
                let frame = self.top_frame()?;
                let val = frame
                    .locals
                    .get(i)
                    .cloned()
                    .ok_or_else(|| Xerr::InvalidAddress)?;
                self.push_data(val)?;
                self.next_ip();
            }
            Opcode::Do(rel) => {
                let done_ip = rel.calculate(ip);
                let l = do_init(self)?;
                if l.range.is_empty() {
                    self.set_ip(done_ip);
                } else {
                    self.push_loop(l)?;
                    self.next_ip();
                }
            }
            Opcode::Break(rel) => {
                let break_ip = rel.calculate(ip);
                self.pop_loop()?;
                self.set_ip(break_ip);
            }
            Opcode::Loop(ref rel) => {
                let done_ip = rel.calculate(ip);
                if self.loop_next()? {
                    self.set_ip(done_ip);
                } else {
                    self.pop_loop()?;
                    self.next_ip();
                }
            }
        }
        OK
    }

    pub fn next(&mut self) -> Xresult {
        if self.is_running() {
            self.clear_last_error();
            self.fetch_and_run().map_err(|e| {
                self.set_runtime_err_location(&e);
                e
            })?;
        }
        OK
    }

    pub fn rnext(&mut self) -> Xresult {
        // Every instruction may have arbitrary numer of state changes,
        // so rollback aleast one. Then stop on first SetIp.
        let pop = |xs: &mut State| xs.reverse_log.as_mut().and_then(|log| log.pop());
        if let Some(r) = pop(self) {
            self.clear_last_error();
            self.reverse_changes(r)?;
        }
        while let Some(step) = pop(self) {
            match &step {
                ReverseStep::SetIp { .. } => {
                    // this is anohter instruction, queue back to log
                    self.add_reverse_step(step);
                    break;
                }
                _ => self.reverse_changes(step)?,
            }
        }
        OK
    }

    pub fn set_recording_enabled(&mut self, yes: bool) {
        if yes {
            if self.reverse_log.is_none() {
                self.reverse_log = Some(Vec::new());
            }
        } else {
            self.reverse_log = None;
        }
    }

    pub fn is_recording(&self) -> bool {
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
                    return Err(Xerr::StackUnderflow);
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
                    return Err(Xerr::unbalanced_vec_builder());
                }
            }
            ReverseStep::DropLocal(_) => {
                let f = self.top_frame()?;
                f.locals.pop();
            }
            ReverseStep::SwapRef(cref, val) => {
                let a = self
                    .heap
                    .get_mut(cref.index())
                    .ok_or_else(|| Xerr::InvalidAddress)?;
                let mut b = val;
                std::mem::swap(a, &mut b);
            }
        }
        OK
    }

    pub fn ip(&self) -> usize {
        self.ctx.ip
    }

    pub fn is_running(&self) -> bool {
        self.ip() < self.code.len()
    }

    pub fn bytecode(&self) -> &[Opcode] {
        &self.code
    }

    fn set_ip(&mut self, new_ip: usize) {
        if self.is_recording() {
            self.add_reverse_step(ReverseStep::SetIp(self.ctx.ip));
        }
        self.ctx.ip = new_ip;
    }

    fn next_ip(&mut self) {
        if self.is_recording() {
            self.add_reverse_step(ReverseStep::SetIp(self.ctx.ip));
        }
        self.ctx.ip += 1;
    }

    fn pop_flow(&mut self) -> Option<Flow> {
        if self.flow_stack.len() > self.ctx.fs_len {
            self.flow_stack.pop()
        } else {
            None
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
        if self.is_recording() {
            self.add_reverse_step(ReverseStep::PopData);
        }
        self.data_stack.push(data);
        OK
    }

    pub fn pop_data(&mut self) -> Xresult1<Cell> {
        if self.data_stack.len() > self.ctx.ds_len {
            let val = self.data_stack.pop().unwrap();
            if self.is_recording() {
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

    pub fn top_data(&self) -> Xresult1<&Cell> {
        let len = self.data_stack.len();
        if len > self.ctx.ds_len {
            Ok(&self.data_stack[len - 1])
        } else {
            Err(Xerr::StackUnderflow)
        }
    }

    fn drop_data(&mut self) -> Xresult {
        self.pop_data()?;
        OK
    }

    fn dup_data(&mut self) -> Xresult {
        let len = self.data_stack.len();
        if len > self.ctx.ds_len {
            let val = self.data_stack[len - 1].clone();
            self.push_data(val)
        } else {
            Err(Xerr::StackUnderflow)
        }
    }

    fn swap_data(&mut self) -> Xresult {
        let len = self.data_stack.len();
        if (len - self.ctx.ds_len) >= 2 {
            if self.is_recording() {
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
            if self.is_recording() {
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
            if self.is_recording() {
                self.add_reverse_step(ReverseStep::OverData);
            }
            let val = self.data_stack[len - 2].clone();
            self.push_data(val)
        } else {
            Err(Xerr::StackUnderflow)
        }
    }

    fn push_return(&mut self, return_to: usize) -> Xresult {
        if self.is_recording() {
            self.add_reverse_step(ReverseStep::PopReturn);
        }
        self.return_stack.push(Frame::from_addr(return_to));
        OK
    }

    fn pop_return(&mut self) -> Xresult1<Frame> {
        if self.return_stack.len() > self.ctx.rs_len {
            let ret = self
                .return_stack
                .pop()
                .ok_or_else(|| Xerr::ReturnStackUnderflow)?;
            if self.is_recording() {
                self.add_reverse_step(ReverseStep::PushReturn(ret.clone()));
            }
            Ok(ret)
        } else {
            Err(Xerr::ReturnStackUnderflow)
        }
    }

    fn top_frame(&mut self) -> Xresult1<&mut Frame> {
        let len = self.return_stack.len();
        if len > self.ctx.rs_len {
            Ok(&mut self.return_stack[len - 1])
        } else {
            Err(Xerr::ReturnStackUnderflow)
        }
    }

    fn push_loop(&mut self, l: Loop) -> Xresult {
        if self.is_recording() {
            self.add_reverse_step(ReverseStep::PopLoop);
        }
        self.loops.push(l);
        OK
    }

    fn pop_loop(&mut self) -> Xresult1<Loop> {
        if self.loops.len() > self.ctx.ls_len {
            let l = self.loops.pop().ok_or_else(|| Xerr::InternalError)?;
            if self.is_recording() {
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
            if self.is_recording() {
                self.add_reverse_step(ReverseStep::LoopNextBack(old));
            }
            Ok(has_more)
        } else {
            Err(Xerr::LoopStackUnderflow)
        }
    }

    fn push_special(&mut self, s: Special) -> Xresult {
        if self.is_recording() {
            self.add_reverse_step(ReverseStep::PopSpecial);
        }
        self.special.push(s);
        OK
    }

    fn pop_special(&mut self) -> Option<Special> {
        if self.special.len() > self.ctx.ss_ptr {
            let s = self.special.pop().unwrap();
            if self.is_recording() {
                self.add_reverse_step(ReverseStep::PushSpecial(s.clone()));
            }
            Some(s)
        } else {
            None
        }
    }
}

fn take_first_cond_flow(xs: &mut State) -> Option<Flow> {
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
            return Some(xs.flow_stack.remove(i));
        }
    }
    None
}

fn core_word_if(xs: &mut State) -> Xresult {
    let org = xs.code_origin();
    xs.push_flow(Flow::If(org))?;
    xs.code_emit(Opcode::JumpIfNot(RelativeJump::uninit()))
}

fn core_word_else(xs: &mut State) -> Xresult {
    let if_org = match take_first_cond_flow(xs) {
        Some(Flow::If(org)) => org,
        _ => return Err(Xerr::unbalanced_else()),
    };
    let else_org = xs.code_origin();
    xs.push_flow(Flow::Else(else_org))?;
    xs.code_emit(Opcode::Jump(RelativeJump::uninit()))?;
    let rel = jump_offset(if_org, xs.code_origin());
    xs.backpatch_jump(if_org, rel)
}

fn core_word_endif(xs: &mut State) -> Xresult {
    let if_org = match take_first_cond_flow(xs) {
        Some(Flow::If(org)) => org,
        Some(Flow::Else(org)) => org,
        _ => return Err(Xerr::unbalanced_endif())
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
        match take_first_cond_flow(xs) {
            Some(Flow::CaseEndOf(endof_org)) => {
                let rel = jump_offset(endof_org, endcase_org);
                xs.backpatch_jump(endof_org, rel)?;
            }
            Some(Flow::Case) => break OK,
            _ => break Err(Xerr::unbalanced_endcase()),
        }
    }
}

fn of_word(xs: &mut State) -> Xresult {
    let of_org = xs.code_origin();
    xs.push_flow(Flow::CaseOf(of_org))?;
    xs.code_emit(Opcode::CaseOf(RelativeJump::uninit()))
}

fn endof_word(xs: &mut State) -> Xresult {
    match take_first_cond_flow(xs) {
        Some(Flow::CaseOf(of_org)) => {
            let endof_org = xs.code_origin();
            xs.code_emit(Opcode::Jump(RelativeJump::uninit()))?;
            let next_case_rel = jump_offset(of_org, xs.code_origin());
            xs.backpatch_jump(of_org, next_case_rel)?;
            xs.push_flow(Flow::CaseEndOf(endof_org))
        }
        _ => Err(Xerr::unbalanced_endof()),
    }
}

fn core_word_begin(xs: &mut State) -> Xresult {
    xs.push_flow(Flow::Begin(xs.code_origin()))
}

fn core_word_until(xs: &mut State) -> Xresult {
    match xs.pop_flow() {
        Some(Flow::Begin(begin_org)) => {
            let offs = jump_offset(xs.code_origin(), begin_org);
            xs.code_emit(Opcode::JumpIf(offs))
        }
        _ => Err(Xerr::unbalanced_until())
    }
}

fn core_word_while(xs: &mut State) -> Xresult {
    let cond = Flow::While(xs.code_origin());
    xs.code_emit(Opcode::JumpIfNot(RelativeJump::uninit()))?;
    xs.push_flow(cond)
}

fn core_word_again(xs: &mut State) -> Xresult {
    loop {
        match xs.pop_flow() {
            Some(Flow::Leave(org)) => {
                let offs = jump_offset(org, xs.code_origin() + 1);
                xs.backpatch_jump(org, offs)?;
            }
            Some(Flow::Begin(begin_org)) => {
                let offs = jump_offset(xs.code_origin(), begin_org);
                break xs.code_emit(Opcode::Jump(offs));
            }
            _ => break Err(Xerr::unbalanced_again())
        }
    }
}

fn core_word_repeat(xs: &mut State) -> Xresult {
    loop {
        match xs.pop_flow() {
            Some(Flow::Leave(org)) => {
                let offs = jump_offset(org, xs.code_origin() + 1);
                xs.backpatch_jump(org, offs)?;
            }
            // todo: forbig begin ... repeat endless loop ?
            Some(Flow::Begin(begin_org)) => {
                let offs = jump_offset(xs.code_origin(), begin_org);
                break xs.code_emit(Opcode::Jump(offs));
            }
            Some(Flow::While(cond_org)) => match xs.pop_flow() {
                Some(Flow::Begin(begin_org)) => {
                    let offs = jump_offset(cond_org, xs.code_origin() + 1);
                    xs.backpatch_jump(cond_org, offs)?;
                    let offs = jump_offset(xs.code_origin(), begin_org);
                    break xs.code_emit(Opcode::Jump(offs));
                }
                _ => break Err(Xerr::unbalanced_while()),
            },
            _ => break Err(Xerr::unbalanced_repeat()),
        }
    }
}

fn core_word_leave(xs: &mut State) -> Xresult {
    let org = xs.code_origin();
    xs.code_emit(Opcode::Jump(RelativeJump::uninit()))?;
    xs.push_flow(Flow::Leave(org))
}

fn jump_offset(origin: usize, dest: usize) -> RelativeJump {
    RelativeJump::from_to(origin, dest)
}

fn core_word_vec_begin(xs: &mut State) -> Xresult {
    xs.push_flow(Flow::Vec)?;
    xs.code_emit(Opcode::NativeCall(XfnPtr(vec_builder_begin)))
}

fn core_word_vec_end(xs: &mut State) -> Xresult {
    match xs.pop_flow() {
        Some(Flow::Vec) => xs.code_emit(Opcode::NativeCall(XfnPtr(vec_builder_end))),
        _ => Err(Xerr::unbalanced_vec_builder())
    }
}

fn vec_builder_begin(xs: &mut State) -> Xresult {
    let ptr = xs.data_stack.len();
    xs.push_special(Special::VecStackStart(ptr))
}

fn vec_builder_end(xs: &mut State) -> Xresult {
    match xs.pop_special() {
        Some(Special::VecStackStart(stack_ptr)) => {
            let top_ptr = xs.data_stack.len();
            if top_ptr < stack_ptr {
                Err(Xerr::vec_stack_underflow())
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
        _ => Err(Xerr::unbalanced_vec_builder()),
    }
}

fn core_word_def_begin(xs: &mut State) -> Xresult {
    if xs.ctx.mode == ContextMode::MetaEval {
        return Err(Xerr::const_context());
    }
    // jump over function body
    let start = xs.code_origin();
    xs.code_emit(Opcode::Jump(RelativeJump::uninit()))?;
    let name = xs.next_name()?;
    // function starts right after jump
    let xf = Xfn::Interp(xs.code_origin());
    let dict_idx = xs.dict_insert(
        &name,
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
    match xs.pop_flow() {
        Some(Flow::Fun(FunctionFlow {
            start, dict_idx, ..
        })) => {
            xs.code_emit(Opcode::Ret)?;
            let offs = jump_offset(start, xs.code_origin());
            let fun_len = xs.code_origin() - start;
            match xs
                .dict
                .get_mut(dict_idx)
                .ok_or_else(|| Xerr::InvalidAddress)?
            {
                DictEntry {
                    entry: Entry::Function { ref mut len, .. },
                    ..
                } => *len = Some(fun_len),
                _ => panic!("entry type"),
            }
            xs.backpatch_jump(start, offs)
        }
        _ => Err(Xerr::unbalanced_fn_builder()),
    }
}

fn core_word_comment(xs: &mut State) -> Xresult {
    if let Some(src) = xs.input.last_mut() {
        src.skip_line();
    }
    OK
}

fn core_word_immediate(xs: &mut State) -> Xresult {
    let dict_idx = xs
        .top_function_flow()
        .map(|f| f.dict_idx)
        .ok_or_else(|| Xerr::expect_fn_context())?;
    match xs
        .dict
        .get_mut(dict_idx)
    {
        Some(DictEntry {
            entry: Entry::Function { ref mut immediate, .. },
            ..
        }) => {
            *immediate = true;
            OK
        }
        _ => Err(Xerr::expect_fn_context()),
    }
}

fn core_word_def_local(xs: &mut State) -> Xresult {
    let name = xs.next_name()?;
    let ff = xs
        .top_function_flow()
        .ok_or_else(|| Xerr::expect_fn_context())?;
    let idx = ff.locals.len();
    ff.locals.push(name);
    xs.code_emit(Opcode::InitLocal(idx))
}

fn core_word_variable(xs: &mut State) -> Xresult {
    let name = xs.next_name()?;
    if !xs.flow_stack.is_empty() {
        return Err(Xerr::conditional_var_definition());
    }
    let a = xs.alloc_cell(Cell::Nil)?;
    xs.dict_insert(&name, Entry::Variable(a))?;
    xs.code_emit(Opcode::Store(a))
}

fn core_word_setvar(xs: &mut State) -> Xresult {
    let name = xs.next_name()?;
    match xs.dict_entry(&name) {
        None => Err(Xerr::UnknownWord(Xstr::from(name.as_str()))),
        Some(Entry::Variable(a)) => {
            let a = *a;
            xs.code_emit(Opcode::Store(a))
        }
        _ => {
            const ERRMSG: Xstr = arcstr::literal!("word is readonly");
            Err(Xerr::ErrorMsg(ERRMSG))
        }
    }
}

fn core_word_nil(xs: &mut State) -> Xresult {
    xs.code_emit(Opcode::LoadNil)
}

fn core_word_nested_begin(xs: &mut State) -> Xresult {
    xs.context_open(ContextMode::MetaEval)
}

fn core_word_nested_end(xs: &mut State) -> Xresult {
    if xs.ctx.mode != ContextMode::MetaEval {
        Err(Xerr::unbalanced_context())
    } else if xs.has_pending_flow() {
        Xerr::control_flow_error(xs.flow_stack.last())
    } else {
        debug_assert!(xs.loops.len() == xs.ctx.ls_len);
        xs.context_close()
    }
}

fn core_word_const(xs: &mut State) -> Xresult {
    let name = xs.next_name()?;
    if xs.ctx.mode != ContextMode::MetaEval {
        let s = arcstr::literal!("const word used out of meta-eval context");
        Err(Xerr::ErrorMsg(s))
    } else {
        let val = xs.pop_data()?;
        xs.dict_insert(&name, Entry::Constant(val))?;
        OK
    }
}

fn do_init(xs: &mut State) -> Xresult1<Loop> {
    let start = xs.pop_data()?;
    let limit = xs.pop_data()?;
    let start = start.to_isize()?;
    let limit = limit.to_isize()?;
    Ok(Loop {
        range: start..limit,
    })
}

fn core_word_do(xs: &mut State) -> Xresult {
    let for_org = xs.code_origin();
    xs.code_emit(Opcode::Do(RelativeJump::uninit()))?; // init and jump over if range is empty
    let body_org = xs.code_origin();
    xs.push_flow(Flow::Do { for_org, body_org })
}

fn core_word_loop(xs: &mut State) -> Xresult {
    let loop_org = xs.code_origin();
    xs.code_emit(Opcode::Loop(RelativeJump::uninit()))?;
    let stop_org = xs.code_origin();
    loop {
        match xs.pop_flow() {
            Some(Flow::Leave(org)) => {
                let stop_rel = jump_offset(org, stop_org);
                xs.backpatch(org, Opcode::Break(stop_rel))?;
            }
            Some(Flow::Do { for_org, body_org }) => {
                let stop_rel = jump_offset(for_org, stop_org);
                xs.backpatch(for_org, Opcode::Do(stop_rel))?;
                let body_rel = jump_offset(loop_org, body_org);
                break xs.backpatch(loop_org, Opcode::Loop(body_rel));
            }
            _ => break Err(Xerr::unbalanced_loop()),
        }
    }
}

fn core_word_help_str(xs: &mut State) -> Xresult {
    let name = xs.pop_data()?.to_xstr()?;
    let help = xs.help_str(&name).ok_or_else(|| Xerr::UnknownWord(name))?.clone();
    xs.push_data(help)
}

fn core_word_help(xs: &mut State) -> Xresult {
    let name = xs.pop_data()?.to_xstr()?;
    let help = xs.help_str(&name).ok_or_else(|| Xerr::UnknownWord(name))?;
    if let Ok(s) = help.to_xstr() {
        xs.print(&s);
    }
    OK
}

fn core_word_doc(xs: &mut State) -> Xresult {
    let name = xs.pop_data()?;
    let help = xs.pop_data()?;
    let _testtype = help.str()?;
    let name = name.to_xstr()?;
    let cref = xs.dict_key(&name).ok_or_else(|| Xerr::UnknownWord(name))?.help;
    xs.set_var(cref, help)
}

fn counter_value(xs: &mut State, n: usize) -> Xresult {
    let l = xs.loops[xs.ctx.ls_len..]
        .iter()
        .nth_back(n)
        .ok_or_else(|| Xerr::LoopStackUnderflow)?;
    let val = l.range.start;
    return xs.push_data(Cell::from(val));
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
        let rel_index = index.abs() as usize;
        if rel_index > v.len() {
            Ok(v.len() - (rel_index % v.len()))
        } else {
            Ok(v.len() - rel_index)
        }
    }
}

fn vector_get<'a>(v: &'a Xvec, index: isize) -> Xresult1<&'a Cell> {
    let new_index = vector_relative_index(v, index)?;
    v.get(new_index).ok_or_else(|| Xerr::OutOfBounds(new_index))
}

fn core_word_get(xs: &mut State) -> Xresult {
    let index = xs.pop_data()?.to_isize()?;
    let v = xs.pop_data()?.to_vec()?;
    xs.push_data(vector_get(&v, index)?.clone())
}

fn core_word_sort(xs: &mut State) -> Xresult {
    let v = xs.pop_data()?.to_vec()?;
    let m: std::collections::BTreeSet<Cell> = v.iter().cloned().collect();
    let sorted = Xvec::from_iter(m.into_iter());
    xs.push_data(Cell::from(sorted))
}

fn core_word_reverse(xs: &mut State) -> Xresult {
    let v = xs.pop_data()?.to_vec()?;
    let rv = Xvec::from_iter(v.iter().rev().cloned());
    xs.push_data(Cell::from(rv))
}

fn core_word_depth(xs: &mut State) -> Xresult {
    let n = xs.data_depth();
    xs.push_data(Cell::from(n))
}

fn core_word_assert(xs: &mut State) -> Xresult {
    if xs.pop_data()?.cond_true()? {
        OK
    } else {
        Err(Xerr::AssertFailed)
    }
}

fn core_word_assert_eq(xs: &mut State) -> Xresult {
    let a = xs.pop_data()?;
    let b = xs.pop_data()?;
    if a == b {
        OK
    } else {
        Err(Xerr::AssertEqFailed { a, b })
    }
}

fn core_word_exit(xs: &mut State) -> Xresult {
    xs.about_to_stop = true;
    let code = xs.pop_data()?.to_isize()?;
    Err(Xerr::Exit(code))
}

fn core_word_display_stack(xs: &mut State) -> Xresult {
    let mut buf = String::new();
    for x in xs.data_stack.iter().rev() {
        let s = xs.format_cell(x)?;
        buf.push_str(&s);
        buf.push_str("\n");
    }
    xs.print(&buf);
    OK
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

fn set_fmt_base(xs: &mut State, n: usize) -> Xresult {
    let old_flags = xs.get_var(xs.fmt_flags)?;
    let flags = FmtFlags::from(old_flags).set_base(n).build();
    xs.set_var(xs.fmt_flags, flags)?;
    OK
}

fn set_fmt_prefix(xs: &mut State, show: bool) -> Xresult {
    let old_flags = xs.get_var(xs.fmt_flags)?;
    let flags = FmtFlags::from(old_flags).set_show_prefix(show).build();
    xs.set_var(xs.fmt_flags, flags)?;
    OK
}

fn set_fmt_tags(xs: &mut State, show: bool) -> Xresult {
    let old_flags = xs.get_var(xs.fmt_flags)?;
    let flags = FmtFlags::from(old_flags).set_show_tags(show).build();
    xs.set_var(xs.fmt_flags, flags)?;
    OK
}

fn core_word_load(xs: &mut State) -> Xresult {
    let path = xs.pop_data()?.to_xstr()?;
    xs.eval_from_file(&path)
}

fn core_word_tag_of(xs: &mut State) -> Xresult {
    let val = xs.top_data()?;
    let tag = val.tag().unwrap_or(&NIL).clone();
    xs.push_data(tag)
}

fn core_word_with_tag(xs: &mut State) -> Xresult {
    let tag = xs.pop_data()?;
    let val = xs.pop_data()?.with_tag(tag);
    xs.push_data(val)
}

fn core_word_insert_tagged(xs: &mut State) -> Xresult {
    let val = xs.pop_data()?;
    let mut vec = xs.pop_data()?.to_vec()?;
    let pos = vec.iter().position(|x| x.tag() == val.tag());
    if let Some(index) = pos {
        vec.set_mut(index, val);
    } else {
        vec.push_back_mut(val);
    };
    xs.push_data(Cell::from(vec))
}

fn core_word_get_tagged(xs: &mut State) -> Xresult {
    let tag = xs.pop_data()?;
    let vec = xs.pop_data()?;
    let item = vec.vec()?.iter().find(|x| x.tag() == Some(&tag)).cloned();
    xs.push_data(item.unwrap_or_else(|| NIL))
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! eval_boot {
        ($e:expr) => {{
            let mut xs = State::boot().unwrap();
            xs.eval($e)
        }}
    }

    macro_rules! eval_ok {
        ($xs:expr,$e:expr) => {
            $xs.eval($e)
                .map_err(|err| {
                    println!("*** error: {}", $xs.pretty_error().unwrap_or_default());
                    err
                })
                .unwrap()
        };
    }

    #[test]
    fn test_data_stack() {
        let mut xs = State::boot().unwrap();
        xs.eval("1 \"s\" 2").unwrap();
        xs.eval("dup").unwrap();
        assert_eq!(OK, xs.eval("depth 4 assert-eq"));
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        xs.eval("drop").unwrap();
        assert_eq!(OK, xs.eval("depth 1 assert-eq"));
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        assert_eq!(OK, xs.eval("depth 0 assert-eq"));
        let res = xs.eval("drop");
        assert_eq!(Err(Xerr::StackUnderflow), res);
        let res = xs.eval("dup");
        assert_eq!(Err(Xerr::StackUnderflow), res);
        xs.eval("5 6 swap").unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(6)), xs.pop_data());
        assert_eq!(Err(Xerr::StackUnderflow), xs.eval("1 ( 2 swap )"));
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::StackUnderflow), xs.eval("1 swap"));
        let mut xs = State::boot().unwrap();
        xs.eval("1 2 3 rot").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(3)), xs.pop_data());
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::StackUnderflow), xs.eval("1 ( 2 3 rot )"));
        let mut xs = State::boot().unwrap();
        xs.eval("1 2 over").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        assert_eq!(Err(Xerr::StackUnderflow), xs.eval("1 over"));
    }

    #[test]
    fn test_data_stack_iter() {
        let mut xs = State::boot().unwrap();
        xs.eval("1 2 3").unwrap();
        assert_eq!(Some(&Cell::Int(3)), xs.get_data(0));
        assert_eq!(Some(&Cell::Int(2)), xs.get_data(1));
        assert_eq!(Some(&Cell::Int(1)), xs.get_data(2));
        assert_eq!(3, xs.data_depth());
    }

    #[test]
    fn test_vec_balanced() {
        let mut xs = State::boot().unwrap();
        assert_ne!(OK, xs.eval(" 1 [ 2 drop drop ] "));
    }

    #[test]
    fn test_if_flow() {
        let mut xs = State::boot().unwrap();
        xs.compile("1 if 222 endif").unwrap();
        let mut it = xs.code.iter();
        it.next().unwrap();
        assert_eq!(
            &Opcode::JumpIfNot(RelativeJump::from_i32(2)),
            it.next().unwrap()
        );
        let mut xs = State::boot().unwrap();
        xs.compile("1 if 222 else 333 endif").unwrap();
        let mut it = xs.code.iter();
        it.next().unwrap();
        assert_eq!(
            &Opcode::JumpIfNot(RelativeJump::from_i32(3)),
            it.next().unwrap()
        );
        it.next().unwrap();
        assert_eq!(&Opcode::Jump(RelativeJump::from_i32(2)), it.next().unwrap());
        // test errors
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::unbalanced_endif()), xs.compile("1 if 222 else 333"));
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::unbalanced_endif()), xs.compile("1 if 222 else"));
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::unbalanced_endif()), xs.compile("1 if 222"));
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::unbalanced_else()), xs.compile("1 else 222 endif"));
        assert_eq!(Err(Xerr::unbalanced_else()), xs.compile("else 222 if"));
    }

    #[test]
    fn test_last_err_loc() {
        // control flow
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::unbalanced_endif()), xs.eval(" if "));
        assert_ne!(None, xs.last_err_location());
        // end of file
        let mut xs = State::boot().unwrap();
        assert_ne!(OK, xs.eval(" ( "));
        assert_ne!(None, xs.last_err_location());
        // parse error test
        let mut xs = State::boot().unwrap();
        assert_ne!(OK, xs.eval(" 2d "));
        assert_ne!(None, xs.last_err_location());
    }

    #[test]
    fn test_if_var() {
        let mut xs = State::boot().unwrap();
        let res = xs.eval("nil if 100 var X endif 10 -> X");
        assert_eq!(Err(Xerr::conditional_var_definition()), res);
    }

    #[test]
    fn test_begin_again() {
        let mut xs = State::boot().unwrap();
        xs.eval("0 begin dup 5 < while 1 + repeat").unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
        let mut xs = State::boot().unwrap();
        xs.compile("begin leave again").unwrap();
        let mut it = xs.code.iter();
        assert_eq!(&Opcode::Jump(RelativeJump::from_i32(2)), it.next().unwrap());
        assert_eq!(
            &Opcode::Jump(RelativeJump::from_i32(-1)),
            it.next().unwrap()
        );
        let mut xs = State::boot().unwrap();
        xs.eval("begin 1 false until").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        xs.eval("1 var x begin x 0 <> while 0 -> x repeat").unwrap();
        assert_eq!(
            Err(Xerr::unbalanced_endif()),
            xs.compile("if begin endif repeat")
        );
        assert_eq!(Err(Xerr::unbalanced_again()), xs.compile("again begin"));
        assert_eq!(Err(Xerr::unbalanced_endif()), xs.compile("begin endif while"));
        assert_eq!(Err(Xerr::unbalanced_until()), xs.compile("until begin"));
        assert_eq!(Err(Xerr::unbalanced_until()), xs.compile("begin again until"));
        assert_eq!(Err(Xerr::unbalanced_again()), xs.compile("begin until again"));
    }

    #[test]
    fn test_length() {
        let mut xs = State::boot().unwrap();
        xs.eval("[ 1 2 3 ] length").unwrap();
        assert_eq!(Ok(Cell::Int(3)), xs.pop_data());
        xs.eval("\"12345\" length").unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
        let mut xs = State::boot().unwrap();
        let res = xs.eval("length");
        assert_eq!(Err(Xerr::StackUnderflow), res);
        let res = xs.eval("1 length");
        assert_eq!(Err(Xerr::TypeError), res);
    }

    #[test]
    fn test_loop_break() {
        let mut xs = State::boot().unwrap();
        xs.eval("begin 1 leave again").unwrap();
        let x = xs.pop_data().unwrap();
        assert_eq!(x.to_xint(), Ok(1));
        assert_eq!(Err(Xerr::StackUnderflow), xs.pop_data());
        let mut xs = State::boot().unwrap();
        let res = xs.compile("begin 1 again leave");
        assert_eq!(Err(Xerr::unbalanced_leave()), res);
        let mut xs = State::boot().unwrap();
        xs.compile("begin 1 if leave else leave endif again")
            .unwrap();
    }

    #[test]
    fn test_for_loop() {
        let mut xs = State::boot().unwrap();
        // short form for [0 3]
        xs.eval("3 0 do I loop").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(0)), xs.pop_data());
        assert_eq!(Err(Xerr::StackUnderflow), xs.pop_data());
        // start with negative
        let mut xs = State::boot().unwrap();
        xs.eval(" 1 -1 do I loop").unwrap();
        assert_eq!(Ok(Cell::Int(0)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(-1)), xs.pop_data());
        assert_eq!(Err(Xerr::StackUnderflow), xs.pop_data());
        // start from zero
        let mut xs = State::boot().unwrap();
        xs.eval(" 3 0 do I loop").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(0)), xs.pop_data());
        // counters
        let mut xs = State::boot().unwrap();
        xs.eval(" 6 5 do 3 2 do 1 0 do I J K loop loop loop")
            .unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(0)), xs.pop_data());
        // empty range
        let mut xs = State::boot().unwrap();
        xs.eval("0 3 do i loop").unwrap();
        assert_eq!(Err(Xerr::StackUnderflow), xs.pop_data());
        xs.eval("0 0 do i loop").unwrap();
        assert_eq!(Err(Xerr::StackUnderflow), xs.pop_data());
        // invalid range
        assert_ne!(OK, xs.eval("0 0.5 do i loop"));
    }

    #[test]
    fn test_get() {
        let mut xs = State::boot().unwrap();
        xs.eval("[ 11 22 33 ] 2 get").unwrap();
        assert_eq!(Cell::from(33isize), xs.pop_data().unwrap());
        xs.eval("[ 11 22 33 ] -2 get").unwrap();
        assert_eq!(Cell::from(22isize), xs.pop_data().unwrap());
        assert_eq!(Err(Xerr::OutOfBounds(100)), xs.eval("[ 1 2 3 ] 100 get"));
    }

    #[test]
    fn test_get_relative() {
        let mut xs = State::boot().unwrap();
        eval_ok!(xs, "[ 1 2 3 ] -2 get");
        assert_eq!(Cell::from(2isize), xs.pop_data().unwrap());
        eval_ok!(xs, "[ 1 2 3 ] -1 get");
        assert_eq!(Cell::from(3isize), xs.pop_data().unwrap());
        eval_ok!(xs, "[ 1 2 3 ] -4 get");
        assert_eq!(Cell::from(3isize), xs.pop_data().unwrap());
        assert_ne!(OK, xs.eval("[ 1 ] \"0\" get"));
    }

    #[test]
    fn test_locals() {
        let mut xs = State::boot().unwrap();
        xs.eval(": f local x local y x y y x ; 1 2 f").unwrap();
        assert_eq!(Cell::Int(2), xs.pop_data().unwrap());
        assert_eq!(Cell::Int(1), xs.pop_data().unwrap());
        assert_eq!(Cell::Int(1), xs.pop_data().unwrap());
        assert_eq!(Cell::Int(2), xs.pop_data().unwrap());
        assert_eq!(Err(Xerr::UnknownWord(Xstr::from("x"))), xs.eval("x y"));
    }

    #[test]
    fn test_fmt_base() {
        let mut xs = State::boot().unwrap();
        xs.intercept_stdout(true);
        xs.eval("HEX 255 print").unwrap();
        assert_eq!(Some("0xff".to_string()), xs.read_stdout());
        xs.eval("DEC 13 print").unwrap();
        assert_eq!(Some("13".to_string()), xs.read_stdout());
        xs.eval("OCT 10 print").unwrap();
        assert_eq!(Some("0o12".to_string()), xs.read_stdout());
        xs.eval("BIN 3 print").unwrap();
        assert_eq!(Some("0b11".to_string()), xs.read_stdout());
    }

    #[test]
    fn test_fmt_prefix() {
        let mut xs = State::boot().unwrap();
        xs.intercept_stdout(true);
        xs.eval("255 HEX print").unwrap();
        assert_eq!(Some("0xff".to_string()), xs.read_stdout());
        xs.eval("255 NO-PREFIX HEX print").unwrap();
        assert_eq!(Some("ff".to_string()), xs.read_stdout());
        xs.eval("[ ] print").unwrap();
        assert_eq!(Some("[ ]".to_string()), xs.read_stdout());
        xs.eval(" [ 0xff 0xee ] >bitstr NO-PREFIX BIN print")
            .unwrap();
        assert_eq!(Some("[ 11111111 11101110 ]".to_string()), xs.read_stdout());
        xs.eval(" [ ] >bitstr HEX NO-PREFIX print").unwrap();
        assert_eq!(Some("[ ]".to_string()), xs.read_stdout());
    }

    #[test]
    fn test_immediate() {
        let mut xs = State::boot().unwrap();
        let res = xs.compile(": f [ ] 0 get immediate ; f");
        assert_eq!(Err(Xerr::OutOfBounds(0)), res);
    }

    #[test]
    fn test_nested_interpreter() {
        let mut xs = State::boot().unwrap();
        xs.compile("( 3 5 * )").unwrap();
        assert_eq!(Err(Xerr::StackUnderflow), xs.pop_data());
        xs.run().unwrap();
        assert_eq!(Ok(Cell::Int(15)), xs.pop_data());
        eval_ok!(xs, "( 2 2 + )");
        assert_eq!(Ok(Cell::Int(4)), xs.pop_data());
        eval_ok!(xs, "10 var x  ( ( x nil assert-eq  ) )");
        eval_ok!(xs, "(  [ x 0 do I loop ] )");
        let v = xs.pop_data().unwrap().to_vec().unwrap();
        assert_eq!(10, v.len());
        eval_ok!(xs, ": f [ ( 3 3 * ) ] ; f 0 get");
        assert_eq!(Ok(Cell::Int(9)), xs.pop_data());
    }

    #[test]
    fn test_nested_fn_purge() {
        let mut xs = State::boot().unwrap();
        let res = xs.eval(" ( : f 2 ; ) f println");
        assert_eq!(Err(Xerr::const_context()), res);
    }
    
    #[test]
    fn test_nested_var_purge() {
        let mut xs = State::boot().unwrap();
        let res = xs.eval(" ( 2 var x ) x println");
        assert_eq!(Err(Xerr::const_context()), res);
    }

    #[test]
    fn test_recursive_def() {
        let mut xs = State::boot().unwrap();
        eval_ok!(xs, ": a  : b  23 ; b ; a 23 assert-eq");
        assert_eq!(0, xs.data_depth());
    }

    #[test]
    fn test_readonly_word() {
        let mut xs = State::boot().unwrap();
        eval_ok!(xs, "( 1 const x ) : y x ; 2 var g : f g ; ");
        assert!(xs.eval("0 -> x").is_err());
        assert!(xs.eval("0 -> y").is_err());
        eval_ok!(xs, "0 -> g  f 0 assert-eq");
    }

    #[test]
    fn test_const() {
        let mut xs = State::boot().unwrap();
        match xs.eval(" 33 const ss") {
            Err(Xerr::ErrorMsg(_)) => (),
            other => panic!("{:?}", other),
        }
        let mut xs = State::boot().unwrap();
        eval_ok!(
            xs,
            " ( 33 const ss ss 33 assert-eq ) ( ( 11 ss + ) const ss ) ss 44 assert-eq "
        );
    }

    #[test]
    fn test_defvar() {
        let mut xs = State::boot().unwrap();
        let x = xs.defvar("X", Cell::Int(1)).unwrap();
        assert_eq!(Ok(&Cell::Int(1)), xs.get_var(x));
        let x2 = xs.defvar("X", Cell::Int(2)).unwrap();
        assert_eq!(Ok(&Cell::Int(2)), xs.get_var(x2));
        xs.eval(": Y 3 ;").unwrap();
        xs.defvar("Y", Cell::Nil).unwrap();
        xs.eval("4 var Z").unwrap();
        let z = xs.defvar("Z", Cell::Nil).unwrap();
        xs.eval("10 -> Z").unwrap();
        assert_eq!(Ok(&Cell::Int(10)), xs.get_var(z));
    }

    #[test]
    fn test_defwordself() {
        let mut xs = State::boot().unwrap();
        xs.defwordself(
            "self1",
            |xs| {
                assert_eq!(Ok(ONE), xs.pop_data());
                xs.push_data(ZERO)
            },
            ONE,
        )
        .unwrap();
        xs.eval("self1").unwrap();
        assert_eq!(Ok(ZERO), xs.pop_data());
    }

    #[test]
    fn test_caseof() {
        let mut xs = State::boot().unwrap();
        xs.eval("2 case 1 of 100 endof 2 of 200 endof endcase")
            .unwrap();
        assert_eq!(Ok(Cell::Int(200)), xs.pop_data());
        xs.eval("5 case 1 of 100 endof 2 of 200 endof 0 endcase")
            .unwrap();
        assert_eq!(Ok(ZERO), xs.pop_data());
        xs.eval("10 0 do I I case 5 of leave endof drop endcase loop")
            .unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
    }

    #[test]
    fn test_rev() {
        let mut xs = State::boot().unwrap();
        xs.eval("[ 1 2 3 ] reverse").unwrap();
        let mut v = Xvec::new();
        v.push_back_mut(Cell::Int(3));
        v.push_back_mut(Cell::Int(2));
        v.push_back_mut(Cell::Int(1));
        assert_eq!(Ok(&v), xs.pop_data().unwrap().vec());
    }

    #[test]
    fn test_sort() {
        let mut xs = State::boot().unwrap();
        xs.eval("[ 2 3 1 ] sort").unwrap();
        let mut v = Xvec::new();
        v.push_back_mut(Cell::Int(1));
        v.push_back_mut(Cell::Int(2));
        v.push_back_mut(Cell::Int(3));
        assert_eq!(Ok(&v), xs.pop_data().unwrap().vec());
    }

    fn collect_ints(xs: &State) -> Vec<isize> {
        xs.data_stack
            .iter()
            .cloned()
            .map(|x| x.to_isize().unwrap())
            .collect()
    }

    #[test]
    fn text_next() {
        let mut xs = State::boot().unwrap();
        xs.compile("1 2 +").unwrap();
        assert_eq!(OK, xs.next());
        assert_eq!(xs.top_data(), Ok(&Cell::Int(1)));
        assert_eq!(OK, xs.next());
        assert_eq!(xs.top_data(), Ok(&Cell::Int(2)));
        assert_eq!(OK, xs.next());
        assert_eq!(xs.top_data(), Ok(&Cell::Int(3)));
    }

    #[test]
    fn test_reverse_next() {
        let mut xs = State::boot().unwrap();
        assert_eq!(OK, xs.rnext());
        xs.set_recording_enabled(true);
        xs.compile(
            r#"
        100 4 /
        3 *
        5 +
        "#,
        )
        .unwrap();
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
        xs.set_recording_enabled(true);
        xs.compile("[ 3 0 do I loop ] length").unwrap();
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
    fn test_rnext_var() {
        let mut xs = State::boot().unwrap();
        xs.set_recording_enabled(true);
        eval_ok!(xs, "3 var GG");
        assert_eq!(Ok(&Cell::Int(3)), xs.get_var_value("GG"));
        xs.rnext().unwrap();
        assert_eq!(Ok(&NIL), xs.get_var_value("GG"));
        xs.next().unwrap();
        assert_eq!(Ok(&Cell::Int(3)), xs.get_var_value("GG"));
        eval_ok!(xs, "5 -> GG");
        assert_eq!(Ok(&Cell::Int(5)), xs.get_var_value("GG"));
        xs.rnext().unwrap();
        assert_eq!(Ok(&Cell::Int(3)), xs.get_var_value("GG"));
        xs.next().unwrap();
        assert_eq!(Ok(&Cell::Int(5)), xs.get_var_value("GG"));
    }

    #[test]
    fn test_reverse_recur() {
        let snapshot = |xs: &State| (xs.data_stack.clone(), xs.return_stack.clone());
        let mut xs = State::boot().unwrap();
        xs.set_recording_enabled(true);
        xs.compile(
            r#"
       : tower-of-hanoi
            local aux
            local to
            local from
            local n
            n 1 = if
                [ n from to ]
            else
                n 1 - from aux to tower-of-hanoi
                [ n from to ]
                n 1 - aux to from tower-of-hanoi
            endif
        ;        
        4 "a" "c" "b" tower-of-hanoi
        "#,
        )
        .unwrap();

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
    fn test_tag() {
        let mut xs = State::boot().unwrap();
        eval_ok!(xs, include_str!("test-tag.xs"));
    }

    #[test]
    fn test_tagged() {
        let mut xs = State::boot().unwrap();
        eval_ok!(xs, include_str!("test-tagged.xeh"));
    }

    #[test]
    fn test_unbalanced_flow() {
        assert_eq!(Err(Xerr::unbalanced_vec_builder()), eval_boot!("[1 2 ]"));
        assert_eq!(Err(Xerr::unbalanced_endif()), eval_boot!("[ endif ]"));
        assert_eq!(Err(Xerr::unbalanced_context()), eval_boot!(" ( "));
        assert_eq!(Err(Xerr::unbalanced_context()), eval_boot!(" ) "));
        assert_eq!(Err(Xerr::unbalanced_do()), eval_boot!(" ( do ) loop "));
    }

    #[test]
    fn test_nested_debug_token() {
        let mut xs = State::boot().unwrap();
        assert_eq!(OK, xs.eval("( 1 2 +  )"));
        assert_eq!(xs.debug_map[0], ")");
        assert_eq!(xs.code.len(), 1);
    }

    #[test]
    fn test_error_location() {
        let mut xs = State::boot().unwrap();
        assert_eq!(
            Err(Xerr::UnknownWord(Xstr::from("x"))),
            xs.eval(" \r\n \r\n\n   x")
        );
        assert_eq!(
            format!("{:?}", xs.last_err_location().unwrap()),
            concat!("<buffer#0>:4:4\n", "   x\n", "---^")
        );

        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::UnknownWord("z".into())), xs.eval("z"));
        assert_eq!(
            format!("{:?}", xs.last_err_location().unwrap()),
            concat!("<buffer#0>:1:1\n", "z\n", "^")
        );

        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::UnknownWord("q".into())), xs.eval("\n q\n"));
        assert_eq!(
            format!("{:?}", xs.last_err_location().unwrap()),
            concat!("<buffer#0>:2:2\n", " q\n", "-^")
        );

        let mut xs = State::boot().unwrap();
        let res = xs.eval("[\n10 loop\n]");
        assert_eq!(Err(Xerr::unbalanced_loop()), res);
        assert_eq!(
            format!("{:?}", xs.last_err_location().unwrap()),
            concat!(
                "<buffer#0>:2:4\n",
                "10 loop\n",
                "---^"
            )
        );

        let mut xs = State::boot().unwrap();
        let res = xs.compile("( [\n( loop )\n] )");
        assert_eq!(Err(Xerr::unbalanced_loop()), res);
        assert_eq!(
            format!("{:?}", xs.last_err_location().unwrap()),
            concat!(
                "<buffer#0>:2:3\n",
                "( loop )\n",
                "--^"
            )
        );

        let mut xs = State::boot().unwrap();
        let res = xs.eval("\"src/test-location1.xs\" load");
        assert_eq!(Err(Xerr::unbalanced_again()), res);
        assert_eq!(
            format!("{:?}", xs.last_err_location().unwrap()),
            concat!(
                "src/test-location2.xs:2:3\n",
                "[ again ]\n",
                "--^"
            )
        );

        let mut xs = State::boot().unwrap();
        xs.eval(": test3 0 get ;").unwrap();
        let res = xs.eval("[ ] test3");
        assert_eq!(Err(Xerr::OutOfBounds(0)), res);
        assert_eq!(
            format!("{:?}", xs.last_err_location().unwrap()),
            concat!(
                "<buffer#0>:1:11\n",
                ": test3 0 get ;\n",
                "----------^"
            )
        );
    }

    #[test]
    fn test_fmt_opcode() {
        let mut xs = State::boot().unwrap();
        xs.compile(": myword  1 ;").unwrap();
        let a = match xs.dict_entry("myword").unwrap() {
            Entry::Function {
                xf: Xfn::Interp(a), ..
            } => Some(*a),
            _ => None,
        };
        let s = format!("call {:#x} # myword", a.unwrap());
        assert_eq!(s, xs.fmt_opcode(0, &Opcode::Call(a.unwrap())));

        let f = match xs.dict_entry("drop").unwrap() {
            Entry::Function {
                xf: Xfn::Native(f), ..
            } => Some(*f),
            _ => None,
        };
        let s = format!("nativecall {:#x} # drop", f.unwrap().0 as usize);
        assert_eq!(s, xs.fmt_opcode(0, &Opcode::NativeCall(f.unwrap())));
    }

    #[test]
    fn test_doc_help() {
        let mut xs = State::boot().unwrap();
        xs.intercept_stdout(true);
        xs.eval(": ff ;  \"test-help\" \"ff\" doc ").unwrap();
        xs.eval("\"ff\" help").unwrap();
        assert_eq!(xs.read_stdout(), Some("test-help".to_string()));
    }

    #[test]
    fn test_help_str() {
        let mut xs = State::boot().unwrap();
        assert_eq!(OK, xs.eval(": ee ;  \"123\" 3 with-tag \"ee\" doc \"ee\" help-str"));
        let help = xs.help_str("ee").unwrap();
        assert_eq!(Some(&Cell::Int(3)), help.tag());
        assert_eq!(&Cell::from("123"), help.value());
        assert_eq!(Ok(Cell::from("123")), xs.pop_data());
    }

    #[test]
    fn test_builtin_help() {
        let mut xs = State::boot().unwrap();
        let res = xs.eval_from_file("docs/help.xs");
        assert_eq!(None, xs.last_err_location());
        assert_eq!(OK, res);
    }

    #[test]
    fn test_exit_err() {
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::Exit(-1)), xs.eval("-1 exit drop"));
        let mut xs = State::boot().unwrap();
        xs.compile("0 exit +").unwrap();
        assert_eq!(Err(Xerr::Exit(0)), xs.run());
    }
}
