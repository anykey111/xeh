use crate::prelude::*;
use getopts::Options;
use rustyline as rl;
use rustyline_derive::{Helper, Highlighter, Validator};

struct ReplState {
    trial: Option<String>,
    snapshots: Vec<Xstate>,
    xs: Xstate,
}

impl ReplState {
    fn reset_xstate(&mut self) {
        if let Some(old_xs) = self.snapshots.last() {
            self.xs = old_xs.clone();
        }
    }

    fn update_xstate(&mut self) {
        let tmp = self.xs.clone();
        self.trial = Some(String::new());
        self.snapshots.pop();
        self.snapshots.push(tmp);
    }

    fn rollback(&mut self) {
        if let Some(mut old_xs) = self.snapshots.pop() {
            std::mem::swap(&mut self.xs, &mut old_xs);
            println!("OK");
        }
    }
    fn snapshot(&mut self) {
        let tmp = self.xs.clone();
        self.snapshots.push(tmp);
    }
}

type ReplStateRef = std::cell::RefCell<ReplState>;
type ReplStateRc = std::rc::Rc<ReplStateRef>;

#[derive(Helper, Highlighter, Validator)]
struct XsHelper(Vec<Xstr>, ReplStateRc);

struct ComplStr(Xstr);
impl rl::completion::Candidate for ComplStr {
    fn display(&self) -> &str {
        self.0.as_str()
    }
    fn replacement(&self) -> &str {
        self.0.as_str()
    }
}

fn find_token_start(s: &str, pos: usize) -> Option<usize> {
    s[..pos]
        .char_indices()
        .rev()
        .find(|c| c.1.is_whitespace())
        .map(|x| x.0 + 1)
}

impl rl::completion::Completer for XsHelper {
    type Candidate = ComplStr;
    fn complete(
        &self,
        line: &str,
        pos: usize,
        _ctx: &rl::Context<'_>,
    ) -> rl::Result<(usize, Vec<Self::Candidate>)> {
        let pos0 = find_token_start(line, pos).unwrap_or(0);
        let pat = &line[pos0..pos];
        let words = self
            .0
            .iter()
            .filter(|s| s.starts_with(pat))
            .map(|s| ComplStr(s.clone()))
            .collect();
        Ok((pos0, words))
    }
}
struct Xhint(String);

impl rl::hint::Hint for Xhint {
    fn display(&self) -> &str {
        self.0.as_str()
    }
    /// Text to insert in line when right arrow is pressed
    fn completion(&self) -> Option<&str> {
        None
    }
}

impl rl::hint::Hinter for XsHelper {
    type Hint = Xhint;
    fn hint(&self, line: &str, pos: usize, ctx: &rl::Context<'_>) -> Option<Self::Hint> {
        let _ = (line, pos, ctx);
        let mut st = (*self.1).borrow_mut();
        let repl_cmd = line.trim();
        if repl_cmd.is_empty()
            || !st.trial.as_ref().map(|s| s != line).unwrap_or(false)
            || REPL_CMD_HINTS.iter().any(|s| s == repl_cmd)
        {
            return None;
        }
        st.trial = Some(line.to_string());
        st.xs.intercept_stdout(true);
        let res = st.xs.eval(line);
        let sout = st.xs.read_stdout();
        st.xs.intercept_stdout(false);
        let mut text = String::new();
        if let Err(_) = res {
            text.push_str("\nERROR: ");
            if let Some(errmsg) = st.xs.pretty_error() {
                text.push_str(&errmsg);
            }
        } else {
            text.push_str("\nOK");
            if st.xs.data_depth() > 0 {
                const DEPTH_LIMIT: usize = 15;
                for i in 0..st.xs.data_depth() {
                    if i > DEPTH_LIMIT {
                        let n = st.xs.data_depth() - DEPTH_LIMIT;
                        text.push_str(&format!("\n... {} more items on the stack", n));
                        break;
                    }
                    let c = st.xs.get_data(i).unwrap_or(&NIL);
                    let valstr = st.xs.fmt_cell_safe(c).unwrap_or_default();
                    text.push('\n');
                    text.push_str(&valstr);
                }
            }
        }
        if let Some(s) = sout {
            if s.len() > 0 {
                text.push_str("\n");
                text.push_str(&s);
            }
        }
        st.reset_xstate();
        if text.len() > 0 {
            Some(Xhint(text))
        } else {
            None
        }
    }
}

fn print_pretty_error(xs: &Xstate, e: &Xerr) {
    let s = xs.pretty_error().unwrap_or_else(|| format!("{}", e));
    eprintln!("{}", s);
}

const CMD_NEXT: Xstr = xstr_literal!("/next");
const CMD_RNEXT: Xstr = xstr_literal!("/rnext");
const CMD_TRIAL: Xstr = xstr_literal!("/trial");
const CMD_REPL: Xstr = xstr_literal!("/repl");
const CMD_SNAPSHOT: Xstr = xstr_literal!("/snapshot");
const CMD_ROLLBACK: Xstr = xstr_literal!("/rollback");
const REPL_CMD_HINTS: &[Xstr] = &[
    CMD_NEXT,
    CMD_RNEXT,
    CMD_TRIAL,
    CMD_REPL,
    CMD_SNAPSHOT,
    CMD_ROLLBACK,
];

fn switch_to_trial(st: &mut ReplState) {
    if st.trial.is_none() {
        println!("# Trial and error mode!");
        println!("# Everyting is evaluating on-fly, hit Enter to freeze the changes.");
        println!("# Switch between modes using /repl and /trial commands.");
        st.trial = Some(Default::default());
        st.snapshot();
    }
}

fn switch_to_repl(st: &mut ReplState) {
    if st.trial.take().is_some() {
        println!("# Read-Eval-Print-Loop mode!");
        println!("# Switch between modes using /repl and /trial commands.");
    }
}

fn run_line(st: &mut ReplState, line: &str) {
    let cmd = line.trim();
    let res = if cmd == CMD_NEXT {
        st.xs.next()
    } else if cmd == CMD_RNEXT {
        st.xs.rnext()
    } else if cmd == CMD_TRIAL {
        switch_to_trial(st);
        OK
    } else if cmd == CMD_REPL {
        switch_to_repl(st);
        OK
    } else if cmd == CMD_SNAPSHOT {
        println!("Taking snapshot...");
        st.snapshot();
        println!("OK");
        OK
    } else if cmd == CMD_ROLLBACK {
        st.rollback();
        OK
    } else {
        let res = st.xs.eval(line);
        if st.trial.is_some() {
            st.update_xstate();
        }
        res
    };
    if let Err(e) = &res {
        print_pretty_error(&st.xs, &e);
    }
}

fn run_tty_repl(xs: Xstate, args: XcmdArgs) -> Xresult {
    let mut st_tmp = ReplState {
        xs,
        trial: None,
        snapshots: Vec::new(),
    };
    switch_to_trial(&mut st_tmp);
    let st_rc = ReplStateRc::new(ReplStateRef::new(st_tmp));
    let mut rl_state =
        rl::Editor::<XsHelper>::with_config(rl::Config::builder().auto_add_history(true).build());
    if let Some(filename) = &args.history_file {
        let _ = rl_state.load_history(filename);
    }
    loop {
        let (lst, trial) = {
            let st = (*st_rc).borrow_mut();
            if st.xs.about_to_stop {
                eprintln!("BYE!");
                break;
            }
            let mut lst = st.xs.word_list();
            lst.extend(REPL_CMD_HINTS.iter().cloned());
            lst.sort();
            (lst, st.trial.is_some())
        };
        rl_state.set_helper(Some(XsHelper(lst, st_rc.clone())));
        let prompt = if trial { "trial> " } else { "repl> " };
        let res = rl_state.readline(prompt);
        match res {
            Ok(line) => {
                let mut st = (*st_rc).borrow_mut();
                run_line(&mut st, &line);
            }
            Err(rl::error::ReadlineError::Interrupted) => {
                eprintln!("CTRL-C");
                break;
            }
            Err(rl::error::ReadlineError::Eof) => {
                eprintln!("CTRL-D");
                break;
            }
            Err(err) => {
                eprintln!("readline error: {:?}", err);
                break;
            }
        }
    }
    if let Some(filename) = &args.history_file {
        if let Err(e) = rl_state.save_history(filename) {
            eprintln!("history save faield: {:}", e);
        }
    }
    OK
}

pub struct XcmdArgs {
    pub reverse_debug: bool,
    pub binary_path: Option<String>,
    pub sources: Vec<String>,
    pub eval: Vec<String>,
    pub history_file: Option<String>,
}

pub fn parse_args() -> Xresult1<XcmdArgs> {
    let mut opts = Options::new();
    opts.optopt("i", "", "input binary file ", "path");
    opts.optmulti("e", "", "evaluate expression", "expression");
    opts.optflag("r", "", "enable reverse debugging");
    opts.optflag("h", "help", "print help");
    let it = std::env::args().skip(1);
    let matches = opts.parse(it).map_err(|e| {
        let errmsg = format!("getopts: {}", e);
        eprintln!("{}", errmsg);
        Xerr::ErrorMsg(errmsg.into())
    })?;
    if matches.opt_present("h") {
        println!("{}", opts.usage("xeh options [script]\nexample: xeh -i file.bin script.xeh"));
        std::process::exit(0);
    }
    Ok(XcmdArgs {
        reverse_debug: matches.opt_present("r"),
        binary_path: matches.opt_str("i"),
        eval: matches.opt_strs("e"),
        history_file: Some("xeh_history.txt".to_string()),
        sources: matches.free,
    })
}

fn spawn_state(args: &XcmdArgs) -> Xresult1<Xstate> {
    let mut xs = Xstate::boot()?;
    crate::d2_plugin::load(&mut xs)?;
    if let Some(ref path) = args.binary_path {
        crate::file::fs_overlay::load_binary(&mut xs, path)?;
    }
    Ok(xs)
}

pub fn run_with_args() -> Xresult {
    let args = parse_args()?;
    let mut xs = spawn_state(&args).map_err(|e| {
        eprintln!("startup error: {}", e);
        e
    })?;
    if let Err(e) = xs.eval(include_str!("help.xeh")) {
        print_pretty_error(&xs, &e);
        return Err(e);
    }
    if args.reverse_debug {
        xs.set_recording_enabled(true);
    }
    for path in args.sources.iter() {
        if let Err(e) = xs.eval_file(path.into()) {
            print_pretty_error(&xs, &e);
            return Err(e);
        }
    }
    if !args.eval.is_empty() {
        for s in args.eval.iter() {
            if let Err(e) = xs.eval(&s) {
                print_pretty_error(&xs, &e);
                return Err(e);
            }
        }
    } else if args.sources.is_empty() {
        run_tty_repl(xs, args)?;
    }
    OK
}
