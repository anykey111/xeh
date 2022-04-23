use crate::arith::*;
use crate::bitstring_mod;
use crate::cell::*;
use crate::error::*;
use crate::fmt_flags::FmtFlags;
use crate::lex::*;
use crate::opcodes::*;
use crate::bitstring_mod::BitstrMod;

use std::fmt;
use std::fmt::Debug;
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
    name: Xsubstr,
    entry: Entry,
    help: Option<Xstr>,
}

impl DictEntry {
    fn new(name: Xsubstr, entry: Entry) -> Self {
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
    locals: Vec<Xsubstr>,
}

#[derive(Clone, Debug, PartialEq)]
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
}

#[derive(Default, Clone, Debug)]
struct SourceBuf {
    name: String,
    buf: Xstr,
}

#[derive(Clone)]
pub struct TokenLocation {
    line: usize,
    col: usize,
    filename: String,
    whole_line: Xsubstr,
}

impl fmt::Debug for TokenLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}:{}:{}", self.filename, self.line + 1, self.col + 1)?;
        writeln!(f, "{}", self.whole_line)?;
        write!(f, "{:->1$}", '^', self.col + 1)
    }
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
    debug_map: Vec<Option<Xsubstr>>,
    sources: Vec<SourceBuf>,
    input: Vec<Lex>,
    data_stack: Vec<Cell>,
    return_stack: Vec<Frame>,
    flow_stack: Vec<Flow>,
    loops: Vec<Loop>,
    special: Vec<Special>,
    ctx: Context,
    nested: Vec<Context>,
    pub reverse_log: Option<Vec<ReverseStep>>,
    stdout: Option<String>,
    last_error: Option<ErrorContext>,
    pub(crate) about_to_stop: bool,
    pub(crate) bitstr_mod: BitstrMod,
    // formatter flags
    fmt_flags: Xref,
    // d2 canvas
    pub(crate) d2: Xref,
}

impl State {
    
    pub fn format_cell(&self, val: &Cell) -> Xresult1<String> {
        let flags = self
            .get_var(self.fmt_flags)
            .map(|val| FmtFlags::from(val))?;
        Ok(format!("{:1$?}", val, flags.into_raw()))
    }

    pub fn fmt_opcode(&self, ip: usize, op: &Opcode) -> String {
        let jumpaddr = |ip, offs| (ip as isize + offs) as usize;
        match op {
            Opcode::Call(x) => {
                let name = self.dict.iter().rev().find(|e| {
                    match e.entry {
                        Entry::Function { xf: Xfn::Interp(f), ..} => f == *x,
                        _ => false,
                    }
                }).map(|e| e.name.as_str()).unwrap_or_default();
                format!("call {:#x} # {}" , x, name)
            },
            Opcode::NativeCall(x)=> {
                let name = self.dict.iter().rev().find(|e| {
                    match e.entry {
                        Entry::Function { xf: Xfn::Native(f), ..} => f == *x,
                        _ => false,
                    }
                }).map(|e| e.name.as_str()).unwrap_or_default();
                format!("nativecall {:#x} # {}" , x.0 as usize, name)
            },
            Opcode::Resolve(name) => format!("resolve    {:?}", &name),
            Opcode::Ret => format!("ret"),
            Opcode::JumpIf(offs) => format!("jumpif     #{:#05x}", jumpaddr(ip, offs)),
            Opcode::JumpIfNot(offs) => format!("jumpifnot  {:#05x}", jumpaddr(ip, offs)),
            Opcode::Jump(offs) => format!("jump       {:#05x}", jumpaddr(ip, offs)),
            Opcode::CaseOf(rel) => format!("caseof     {:#05x}", jumpaddr(ip, rel)),
            Opcode::Do(rel) => format!("do         {:#05x}", jumpaddr(ip, rel)),
            Opcode::Loop(rel) => format!("loop       {:#05x}", jumpaddr(ip, rel)),
            Opcode::Break(rel) => format!("break      {:#05x}", jumpaddr(ip, rel)),
            Opcode::Load(a) => format!("load       {}", a),
            Opcode::LoadI64(i) => format!("loadint    {}", i),
            Opcode::LoadNil => format!("loadnil"),
            Opcode::LoadCell(c) => format!("loadcell  {:?}", c),
            Opcode::Store(a) => format!("store      {}", a),
            Opcode::InitLocal(i) => format!("initlocal  {}", i),
            Opcode::LoadLocal(i) => format!("loadlocal  {}", i),
        }
    }

    pub fn pretty_error(&self) -> Option<String> {
        let ec = self.last_error()?;
        let errmsg = if let Some(loc) = &ec.location {
            format!("{:?}\n{:?}", ec.err, loc)
        } else {
            format!("{:?}", ec.err)
        };
        Some(errmsg)
    }

    pub fn last_error(&self) -> Option<&ErrorContext> {
        self.last_error.as_ref()
    }

    fn token_location(&self, token: Xsubstr) -> Option<TokenLocation> {
        let tok_start = token.range().start;
        let par = token.parent();
        let mut it = par.char_indices();
        let mut start = 0;
        let mut end = 1;
        let mut line = 0;
        let mut col = 0;
        while let Some((i, c)) = it.next() {
            end = i + c.len_utf8();
            if c == '\n' || c == '\r' {
                if (start..end).contains(&tok_start) {
                    end = i;
                    break;
                }
                if c == '\n' {
                    line += 1;
                }
                start = end;
                col = 0;
            } else if i < tok_start {
                col += 1;
            }
        }
        let name = self.sources
                    .iter()
                    .find(|x| &x.buf == token.parent())
                    .map(|x| x.name.as_str())?;
        let whole_line = token.parent().substr(start..end);
        Some(TokenLocation {
            line,
            col,
            filename: name.to_owned(),
            whole_line,
        })
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
        bitstring_mod::open_bitstr(self, s)
    }

    pub fn compile(&mut self, s: &str) -> Xresult {
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

    fn evalxstr(&mut self, s: Xstr) -> Xresult {
        self.intern_source(s, None)?;
        self.context_open(ContextMode::Eval)?;
        self.build0()?;
        self.context_close()
    }

    fn intern_source(&mut self, buf: Xstr, path: Option<&str>) -> Xresult {
        let id = self.sources.len();
        let lex = Lex::new(buf.clone());
        let name = if let Some(name) = path {
            name.to_string()
        } else {
            format!("<buffer#{}>", id)
        };
        self.sources.push(SourceBuf {
            name,
            buf,
        });
        self.input.push(lex);
            OK
        }

    fn build0(&mut self) -> Xresult {
        self.last_error.take();
        self.build1().map_err(|e| {
            // build-time error
            if self.last_error.is_none() {
                let location = self.input.last()
                    .and_then(|lex| lex.last_token())
                    .and_then(|tok| self.token_location(tok));
                self.last_error = Some(ErrorContext { err: e.clone(), location });
            }
            e
        })
    }

    fn build1(&mut self) -> Xresult {
        loop {
            match self.next_token()? {
                Tok::EndOfInput => {
                    if self.has_pending_flow() {
                        break Err(Xerr::ControlFlowError);
                    }
                    break OK;
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
                        self.build_word(name)?;
                    }
                }
            }
        }
    }

    fn build_word(&mut self, name: Xsubstr) -> Xresult {
        match self.dict_entry(name.as_str()) {
            None =>
                self.code_emit(Opcode::Resolve(Xstr::from(name.as_str()))),

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
        if let Some(lex) = &mut self.input.last_mut() {
            if let Tok::Word(name) = lex.next()? {
                return Ok(name);
            }
        }
        Err(Xerr::ExpectingName)
    }

    fn next_token(&mut self) -> Xresult1<Tok> {
        if let Some(lex) = self.input.last_mut() {
            let tok = lex.next()?;
            if tok == Tok::EndOfInput {
                self.input.pop();
            }
            Ok(tok)
        } else {
            Ok(Tok::EndOfInput)
        }
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
        if self.ctx.mode != ContextMode::Compile {
            self.run()?;
        if self.ctx.mode == ContextMode::MetaEval {
            // purge meta context code after evaluation
            self.code.truncate(self.ctx.cs_len);
            }
        }
        let mut prev = self.nested.pop().ok_or(Xerr::ControlFlowError)?;
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
        crate::bitstring_mod::load(&mut xs)?;
        Ok(xs)
    }

    pub fn load_help(&mut self) -> Xresult {
        let src = include_str!("../docs/help.xs").into();
        self.intern_source(src, Some("docs/help.xs"))?;
        self.build0()
    }

    pub fn start_recording(&mut self) {
        if self.reverse_log.is_none() {
            self.reverse_log = Some(Vec::default());
        }
    }

    pub fn stop_recording(&mut self) {
        self.reverse_log = None;
    }

    pub fn defvar(&mut self, name: &str, val: Cell) -> Xresult1<Xref> {
        // shadow previous definition
        let a = self.alloc_cell(val)?;
        self.dict_insert(DictEntry::new(name.into(), Entry::Variable(a)))?;
        Ok(Xref::Heap(a))
    }

    pub fn defvar_anonymous(&mut self, val: Cell) -> Xresult1<Xref> {
        let a = self.alloc_cell(val)?;
        Ok(Xref::Heap(a))
    }

    pub fn get_var_value(&self, name: &str) -> Xresult1<&Cell> {
        match self.dict_entry(name) {
            None => Err(Xerr::UnknownWord(Xstr::from(name))),
            Some(Entry::Variable(a)) => Ok(&self.heap[*a]),
            _ => Err(Xerr::InvalidAddress),
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

    fn dict_add_word(&mut self, name: &str, f: XfnType, immediate: bool) -> Xresult1<Xref> {
        let xf = Xfn::Native(XfnPtr(f));
        let i = self.dict_insert(DictEntry::new(name.into(),
            Entry::Function { immediate, xf, len: None }))?;
        Ok(Xref::Word(i))
    }

    pub fn defword(&mut self, name: &str, f: XfnType) -> Xresult1<Xref> {
        self.dict_add_word(name, f, false)
    }

    pub fn def_immediate(&mut self, name: &str, f: XfnType) -> Xresult1<Xref> {
        self.dict_add_word(name, f, true)
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
            name.into(),
            Entry::Function {
                immediate: false,
                xf: Xfn::Interp(fn_addr),
                len: Some(len),
            }))?;
        let offs = jump_offset(start, self.code_origin());
        self.backpatch_jump(start, offs)?;
        Ok(Xref::Word(word_addr))
    }

    pub fn set_doc(&mut self, name: Xstr, help: Xstr) -> Xresult {
        let a = self.dict_find(name.as_str())
            .ok_or(Xerr::UnknownWord(name))?;
        self.dict[a].help = Some(help);
        OK
    }

    pub fn help(&self, name: &str) -> Option<&Xstr> {
        let a = self.dict_find(name)?;
        self.dict.get(a).and_then(|x| x.help.as_ref())
    }

    fn load_core(&mut self) -> Xresult {
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
        self.def_immediate("do", core_word_do)?;
        self.def_immediate("loop", core_word_loop)?;
        self.defword("doc", core_word_doc)?;
        self.defword("help", core_word_help)?;
        self.defword("i", core_word_counter_i)?;
        self.defword("j", core_word_counter_j)?;
        self.defword("k", core_word_counter_k)?;
        self.defword("length", core_word_length)?;
        self.defword("get", core_word_get)?;
        self.defword("sort", core_word_sort)?;
        self.defword("reverse", core_word_reverse)?;
        self.defword("dup", |xs| xs.dup_data())?;
        self.defword("drop", |xs| xs.drop_data())?;
        self.defword("swap", |xs| xs.swap_data())?;
        self.defword("rot", |xs| xs.rot_data())?;
        self.defword("over", |xs| xs.over_data())?;
        self.defword("+", core_word_add)?;
        self.defword("-", core_word_sub)?;
        self.defword("*", core_word_mul)?;
        self.defword("/", core_word_div)?;
        self.defword("negate", core_word_negate)?;
        self.defword("abs", core_word_abs)?;
        self.defword("<", core_word_less_then)?;
        self.defword("=", core_word_eq)?;
        self.defword("rem", core_word_rem)?;
        self.defword("and", core_word_bitand)?;
        self.defword("or", core_word_bitor)?;
        self.defword("xor", core_word_bitxor)?;
        self.defword("shl", core_word_bitshl)?;
        self.defword("shr", core_word_bitshr)?;
        self.defword("not", core_word_bitnot)?;
        self.defword("random", core_word_random)?;
        self.defword("round", core_word_round)?;
        self.defword("assert", core_word_assert)?;
        self.defword("assert-eq", core_word_assert_eq)?;
        self.defword("exit", core_word_exit)?;
        self.defword(".s", core_word_display_stack)?;
        self.defword("println", core_word_println)?;
        self.defword("print", core_word_print)?;
        self.defword("newline", core_word_newline)?;
        self.defword("file-write", crate::file::core_word_file_write)?;
        self.defword("load", core_word_load)?;
        self.defword("tag", core_word_get_tag)?;
        self.defword("with-tag", core_word_with_tag)?;
        self.defword("multi-tag", core_word_multi_tag)?;
        self.defword("find-tagged", core_word_find_tagged)?;
        self.defword(".", core_word_find_tagged)?;
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

    fn dict_insert(&mut self, e: DictEntry) -> Xresult1<usize> {
        let wa = self.dict.len();
        self.dict.push(e);
        Ok(wa)
    }

    fn dict_entry(&self, name: &str) -> Option<&Entry> {
        self.dict.iter().rfind(|x| x.name == name).map(|x| &x.entry)
    }

    fn dict_find(&self, name: &str) -> Option<usize> {
        self.dict.iter().rposition(|e| e.name == name)
    }

    pub fn dict_get_help(&self, index: usize) -> Option<(&str, &str)> {
        self.dict.get(index).map(|e| {
            let h = e.help.as_ref().map(|s| s.as_str());
            (e.name.as_str(), h.unwrap_or_default())
        })
    }

    fn code_origin(&self) -> usize {
        self.code.len()
    }

    fn code_emit_value(&mut self, val: Cell) -> Xresult {
        match val {
            Cell::Int(i) if i64::MIN as Xint <= i && i <= i64::MAX as Xint =>
                self.code_emit(Opcode::LoadI64(i as i64)),
            Cell::Nil => self.code_emit(Opcode::LoadNil),
            val => {
                let c = CellBox::from(val);
                self.code_emit(Opcode::LoadCell(c))
            }
        }
    }

    fn code_emit(&mut self, op: Opcode) -> Xresult {
        let at = self.code.len();
        let len = self.debug_map.len();
        let loc = self.input.last().and_then(|x| x.last_token());
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
        if self.ctx.mode == ContextMode::MetaEval {
            return Err(Xerr::ReadonlyAddress);
        }
        let a = self.heap.len();
        self.heap.push(val);
        Ok(a)
    }

    fn run_immediate(&mut self, x: Xfn) -> Xresult {
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
        self.last_error.take();
        while self.is_running() {
            self.fetch_and_run().map_err(|e| {
                if self.last_error.is_none() {
                    let location = self.debug_map.get(self.ip())
                        .and_then(|dbg| dbg.clone())
                        .and_then(|tok| self.token_location(tok));
                    self.last_error = Some(ErrorContext { err: e.clone(), location });
                }
                e
            })?;
        }
        OK
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
            Opcode::Resolve(ref name) => match self.dict_entry(&name) {
                None => Err(Xerr::UnknownWord(name.clone())),
                Some(Entry::Variable(a)) => {
                    let a = *a;
                    self.backpatch(ip, Opcode::Load(a))?;
                    self.fetch_and_run()
                }
                Some(Entry::Function {
                    xf: Xfn::Interp(x), ..
                }) => {
                    let x = *x;
                    self.backpatch(ip, Opcode::Call(x))?;
                    self.fetch_and_run()
                }
                Some(Entry::Function {
                    xf: Xfn::Native(x), ..
                }) => {
                    let x = *x;
                    self.backpatch(ip, Opcode::NativeCall(x))?;
                    self.fetch_and_run()
                }
            },
            Opcode::LoadI64(n) => {
                self.push_data(Cell::from(n))?;
                self.next_ip()
            }
            Opcode::LoadNil => {
                self.push_data(Cell::Nil)?;
                self.next_ip()
            }
            Opcode::LoadCell(ref c) => {
                let val = c.as_ref().clone();
                self.push_data(val)?;
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
            Opcode::Do(rel) => {
                let l = do_init(self)?;
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
        if self.is_running() {
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
        debug_assert!(offs != 0);
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

    pub fn is_running(&self) -> bool {
        self.ip() < self.code.len()
    }

    pub fn bytecode(&self) -> &[Opcode] {
        &self.code
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
    xs.backpatch_jump(if_org, rel)
}

fn core_word_endif(xs: &mut State) -> Xresult {
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
            Flow::Leave(org) => {
                let offs = jump_offset(org, xs.code_origin() + 1);
                xs.backpatch_jump(org, offs)?;
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
            Flow::Leave(org) => {
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

fn core_word_leave(xs: &mut State) -> Xresult {
    let org = xs.code_origin();
    xs.code_emit(Opcode::Jump(0))?;
    xs.push_flow(Flow::Leave(org))
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
    // jump over function body
    let start = xs.code_origin();
    xs.code_emit(Opcode::Jump(0))?;
    let name = xs.next_name()?;
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
    if let Some(src) = xs.input.last_mut() {
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
    if !xs.flow_stack.is_empty() {
        //FIXME: do something with variables
        return Err(Xerr::ControlFlowError);
    }
    let a = xs.alloc_cell(Cell::Nil)?;
    xs.dict_insert(DictEntry::new(name, Entry::Variable(a)))?;
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
        _ => Err(Xerr::ReadonlyAddress),
    }
}

fn core_word_nil(xs: &mut State) -> Xresult {
    xs.code_emit(Opcode::LoadNil)
}

fn core_word_nested_begin(xs: &mut State) -> Xresult {
    xs.context_open(ContextMode::MetaEval)
}

fn core_word_nested_end(xs: &mut State) -> Xresult {
    if xs.ctx.mode != ContextMode::MetaEval
        || xs.flow_stack.len() > xs.ctx.fs_len
        || xs.loops.len() > xs.ctx.ls_len
    {
        return Err(Xerr::ControlFlowError);
    }
    xs.context_close()
}

fn do_init(xs: &mut State) -> Xresult1<Loop> {
    let start = xs.pop_data()?;
    let limit = xs.pop_data()?;
    let start = start.to_isize()?;
    let limit = limit.to_isize()?;
    Ok(Loop { range: start..limit })
}

fn core_word_do(xs: &mut State) -> Xresult {
    let for_org = xs.code_origin();
    xs.code_emit(Opcode::Do(0))?; // init and jump over if range is empty
    let body_org = xs.code_origin();
    xs.push_flow(Flow::Do { for_org, body_org })
}

fn core_word_loop(xs: &mut State) -> Xresult {
    let loop_org = xs.code_origin();
    xs.code_emit(Opcode::Loop(0))?;
    let stop_org = xs.code_origin();
    loop {
        match xs.pop_flow()? {
            Flow::Leave(org) => {
                let stop_rel = jump_offset(org, stop_org);
                xs.backpatch(org, Opcode::Break(stop_rel))?;
            }
            Flow::Do { for_org, body_org } => {
                let stop_rel = jump_offset(for_org, stop_org);
                xs.backpatch(for_org, Opcode::Do(stop_rel))?;
                let body_rel = jump_offset(loop_org, body_org);
                break xs.backpatch(loop_org, Opcode::Loop(body_rel));
            }
            _ => break Err(Xerr::ControlFlowError),
        }
    }
}

fn core_word_help(xs: &mut State) -> Xresult {
    let name = xs.pop_data()?.to_string()?;
    let res = xs.dict_find(name.as_str())
        .and_then(|a| xs.dict.get(a))
        .and_then(|e| e.help.clone());
    if let Some(help) = res {
        xs.print(help.as_str());
    }
    OK
}

fn core_word_doc(xs: &mut State) -> Xresult {
    let name = xs.pop_data()?;
    let help = xs.pop_data()?.to_string()?;
    match name.value() {
        Cell::Vector(v) => {
            for x in v.iter() {
                let name = x.to_string()?;
                xs.set_doc(name, help.clone())?;
            }
            OK
        },
        Cell::Str(name) => xs.set_doc(name.clone(), help),
        _ => Err(Xerr::ExpectingName),
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
    let v = xs.pop_data()?.to_vector()?;
    xs.push_data(vector_get(&v, index)?.clone())
}

fn core_word_sort(xs: &mut State) -> Xresult {
    use std::iter::FromIterator;
    let v = xs.pop_data()?.to_vector()?;
    let m: std::collections::BTreeSet<Cell> = v.iter().cloned().collect();
    let sorted = Xvec::from_iter(m.into_iter());
    xs.push_data(Cell::from(sorted))
}

fn core_word_reverse(xs: &mut State) -> Xresult {
    use std::iter::FromIterator;
    let v = xs.pop_data()?.to_vector()?;
    let rv = Xvec::from_iter(v.iter().rev().cloned());
    xs.push_data(Cell::from(rv))
}

fn core_word_assert(xs: &mut State) -> Xresult {
    if xs.pop_data()?.is_true() {
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
        Err(Xerr::AssertEqFailed(a, b))
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
    let path = xs.pop_data()?.to_string()?;
    xs.eval_from_file(&path)
}

fn core_word_get_tag(xs: &mut State) -> Xresult {
    let val = xs.top_data().and_then(|x| x.tag()).unwrap_or(&NIL).clone();
    xs.push_data(val)
}

fn core_word_with_tag(xs: &mut State) -> Xresult {
    let tag = xs.pop_data()?;
    let val = xs.pop_data()?.with_tag(tag);
    xs.push_data(val)
}

fn core_word_multi_tag(xs: &mut State) -> Xresult {
    let tag = xs.pop_data()?;
    let val = xs.pop_data()?.multi_tag(tag);
    xs.push_data(val)
}

fn core_word_find_tagged(xs: &mut State) -> Xresult {
    let tag = xs.pop_data()?;
    let result = xs.pop_data()?.find_tagged(&tag).unwrap_or(&NIL).clone();
    xs.push_data(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! eval_ok {
        ($xs:expr,$e:expr) => {
            $xs.eval($e).map_err(|err| {
                println!("*** error: {}", $xs.pretty_error().unwrap_or_default());
                err
            }).unwrap()
        };
    }


    #[test]
    fn test_jump_offset() {
        assert_eq!(2, jump_offset(2, 4));
        assert_eq!(-2, jump_offset(4, 2));
    }

    #[test]
    fn test_data_stack() {
        let mut xs = State::boot().unwrap();
        xs.eval("1 \"s\" 2").unwrap();
        xs.eval("dup").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        xs.eval("drop").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
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
    fn test_if_flow() {
        let mut xs = State::boot().unwrap();
        xs.compile("1 if 222 endif").unwrap();
        let mut it = xs.code.iter();
        it.next().unwrap();
        assert_eq!(&Opcode::JumpIfNot(2), it.next().unwrap());
        let mut xs = State::boot().unwrap();
        xs.compile("1 if 222 else 333 endif").unwrap();
        let mut it = xs.code.iter();
        it.next().unwrap();
        assert_eq!(&Opcode::JumpIfNot(3), it.next().unwrap());
        it.next().unwrap();
        assert_eq!(&Opcode::Jump(2), it.next().unwrap());
        // test errors
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::ControlFlowError), xs.compile("1 if 222 else 333"));
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::ControlFlowError), xs.compile("1 if 222 else"));
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::ControlFlowError), xs.compile("1 if 222"));
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::ControlFlowError), xs.compile("1 else 222 then"));
        assert_eq!(Err(Xerr::ControlFlowError), xs.compile("else 222 if"));
    }

    #[test]
    fn test_if_var() {
        let mut xs = State::boot().unwrap();
        let res = xs.eval("0 if 100 var X endif");
        assert_eq!(Err(Xerr::ControlFlowError), res);
    }

    #[test]
    fn test_begin_again() {
        let mut xs = State::boot().unwrap();
        xs.eval("0 begin dup 5 < while 1 + repeat").unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
        let mut xs = State::boot().unwrap();
        xs.compile("begin leave again").unwrap();
        let mut it = xs.code.iter();
        assert_eq!(&Opcode::Jump(2), it.next().unwrap());
        assert_eq!(&Opcode::Jump(-1), it.next().unwrap());
        let mut xs = State::boot().unwrap();
        xs.eval("begin 1 0 until").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        xs.eval("1 var x begin x while 0 -> x repeat").unwrap();
        assert_eq!(Err(Xerr::ControlFlowError), xs.compile("if begin endif repeat"));
        assert_eq!(Err(Xerr::ControlFlowError), xs.compile("again begin"));
        assert_eq!(Err(Xerr::ControlFlowError), xs.compile("begin endif while"));
        assert_eq!(Err(Xerr::ControlFlowError), xs.compile("until begin"));
        assert_eq!(Err(Xerr::ControlFlowError), xs.compile("begin again until"));
        assert_eq!(Err(Xerr::ControlFlowError), xs.compile("begin until again"));
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
        assert_eq!(x.to_int(), Ok(1));
        assert_eq!(Err(Xerr::StackUnderflow), xs.pop_data());
        let mut xs = State::boot().unwrap();
        let res = xs.compile("begin 1 again leave");
        assert_eq!(Err(Xerr::ControlFlowError), res);
        let mut xs = State::boot().unwrap();
        xs.compile("begin 1 if leave else leave endif again").unwrap();
    }

    
    #[test]
    fn test_for_loop() {
        let mut xs = State::boot().unwrap();
        // short form for [0 3]
        xs.eval("3 0 do i loop").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(0)), xs.pop_data());
        assert_eq!(Err(Xerr::StackUnderflow), xs.pop_data());
        // start with negative
        let mut xs = State::boot().unwrap();
        xs.eval(" 1 -1 do i loop").unwrap();
        assert_eq!(Ok(Cell::Int(0)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(-1)), xs.pop_data());
        assert_eq!(Err(Xerr::StackUnderflow), xs.pop_data());
        // start from zero
        let mut xs = State::boot().unwrap();
        xs.eval(" 3 0 do i loop").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        assert_eq!(Ok(Cell::Int(0)), xs.pop_data());
        // counters
        let mut xs = State::boot().unwrap();
        xs.eval(" 6 5 do 3 2 do 1 0 do i j k loop loop loop")
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
        assert_eq!(Err(Xerr::TypeError), xs.eval("0 0.5 do i loop"));
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
        assert_eq!(Err(Xerr::TypeError), xs.eval("[ 1 ] \"0\" get"));
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
        xs.eval(" [ 0xff 0xee ] >bitstr NO-PREFIX BIN print").unwrap();
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
        eval_ok!(xs, "(  [ x 0 do i loop ] )");
        let v = xs.pop_data().unwrap().to_vector().unwrap();
        assert_eq!(10, v.len());
        eval_ok!(xs, ": f [ ( 3 3 * ) ] ; f 0 get");
        assert_eq!(Ok(Cell::Int(9)), xs.pop_data());
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
        xs.defwordself( "self1", |xs| {
            assert_eq!(Ok(ONE), xs.pop_data());
            xs.push_data(ZERO)
        }, ONE).unwrap();
        xs.eval("self1").unwrap();
        assert_eq!(Ok(ZERO), xs.pop_data());
    }

    #[test]
    fn test_caseof() {
        let mut xs = State::boot().unwrap();
        xs.eval("2 case 1 of 100 endof 2 of 200 endof endcase").unwrap();
        assert_eq!(Ok(Cell::Int(200)), xs.pop_data());
        xs.eval("5 case 1 of 100 endof 2 of 200 endof 0 endcase").unwrap();
        assert_eq!(Ok(ZERO), xs.pop_data());
        xs.eval("10 0 do i i case 5 of leave endof drop endcase loop").unwrap();
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
        xs.data_stack.iter().cloned().map(|x| x.to_isize().unwrap()).collect()
    }

    #[test]
    fn text_next() {
        let mut xs = State::boot().unwrap();
        xs.compile("1 2 +").unwrap();
        assert_eq!(OK, xs.next());
        assert_eq!(xs.top_data(), Some(&Cell::Int(1)));
        assert_eq!(OK, xs.next());
        assert_eq!(xs.top_data(), Some(&Cell::Int(2)));
        assert_eq!(OK, xs.next());
        assert_eq!(xs.top_data(), Some(&Cell::Int(3)));
    }

    #[test]
    fn test_reverse_next() {
        let mut xs = State::boot().unwrap();
        assert_eq!(OK, xs.rnext());
        xs.start_recording();
        xs.compile(r#"
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
        xs.start_recording();
        xs.compile("[ 3 0 do i loop ] length").unwrap();
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
        xs.start_recording();
        xs.compile(r#"
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
    fn test_tag() {
        let mut xs = State::boot().unwrap();
        xs.eval(include_str!("test-tag.xs")).unwrap();
    }

    #[test]
    fn test_error_location() {
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::UnknownWord(Xstr::from("x"))), xs.eval(" \r\n \r\n\n   x"));
        assert_eq!(xs.pretty_error().unwrap(), concat!(
            "unknown word x\n",
            "<buffer#0>:4:4\n",
            "   x\n",
            "---^"));

        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::UnknownWord("z".into())), xs.eval("z"));
        assert_eq!(xs.pretty_error().unwrap(), concat!(
            "unknown word z\n",
            "<buffer#0>:1:1\n",
            "z\n",
            "^"));

        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::UnknownWord("q".into())), xs.eval("\n q\n"));
        assert_eq!(xs.pretty_error().unwrap(), concat!(
            "unknown word q\n",
            "<buffer#0>:2:2\n",
            " q\n",
            "-^"));

        let mut xs = State::boot().unwrap();
        let res = xs.eval("[\n10 loop\n]");
        assert_eq!(Err(Xerr::ControlFlowError), res);
        assert_eq!(xs.pretty_error().unwrap(), concat!(
            "ControlFlowError\n",
            "<buffer#0>:2:4\n",
            "10 loop\n",
            "---^"));

        let mut xs = State::boot().unwrap();
        let res = xs.compile("( [\n( loop )\n] )");
        assert_eq!(Err(Xerr::ControlFlowError), res);
        assert_eq!(xs.pretty_error().unwrap(), concat!(
            "ControlFlowError\n",
            "<buffer#0>:2:3\n",
            "( loop )\n",
            "--^"));

        let mut xs = State::boot().unwrap();
        let res = xs.eval("\"src/test-location1.xs\" load");
        assert_eq!(Err(Xerr::ControlFlowError), res);
        assert_eq!(xs.pretty_error().unwrap(), concat!(
            "ControlFlowError\n",
            "src/test-location2.xs:2:3\n",
            "[ again ]\n",
            "--^"));

        let mut xs = State::boot().unwrap();
        xs.eval(": test3 0 get ;").unwrap();
        let res = xs.eval("[ ] test3");
        assert_eq!(Err(Xerr::OutOfBounds(0)), res);
        assert_eq!(xs.pretty_error().unwrap(), concat!(
            "index 0 out of bounds\n",
            "<buffer#0>:1:11\n",
            ": test3 0 get ;\n",
            "----------^"));
    }

    #[test]
    fn test_fmt_opcode() {
        let mut xs = State::boot().unwrap();
        xs.compile(": myword  1 ;").unwrap();
        let a = match xs.dict_entry("myword").unwrap() {
            Entry::Function { xf: Xfn::Interp(a), .. } => Some(*a),
            _ => None,
        };
        let s = format!("call {:#x} # myword", a.unwrap());
        assert_eq!(s, xs.fmt_opcode(0, &Opcode::Call(a.unwrap())));

        let f = match xs.dict_entry("drop").unwrap() {
            Entry::Function { xf: Xfn::Native(f), .. } => Some(*f),
            _ => None,
        };
        let s = format!("nativecall {:#x} # drop", f.unwrap().0 as usize);
        assert_eq!(s, xs.fmt_opcode(0, &Opcode::NativeCall(f.unwrap())));
    }

    #[test]
    fn test_doc_help() {
        let mut xs = State::boot().unwrap();
        xs.intercept_stdout(true);
        xs.compile(": ff ; ( \"test-help\" \"ff\" doc )").unwrap();
        assert_eq!(xs.help("ff"), Some(&Xstr::from("test-help")));
        xs.eval("\"ff\" help").unwrap();
        assert_eq!(xs.read_stdout(), Some("test-help".to_string()));
    }

    #[test]
    fn test_builtin_help() {
        let mut xs = State::boot().unwrap();
        xs.load_help().unwrap();
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
