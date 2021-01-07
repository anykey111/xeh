use crate::state::*;
use crate::error::*;
use crate::lex::*;
use rustyline::error::ReadlineError;
use rustyline::Editor;
use getopts::Options;

pub fn run(xs: &mut State) -> Xresult {
    crate::repl::run_tty_repl(xs, true);
    OK
}

fn eval_line(xs: &mut State, line: &str) {
    let cmd = line.trim();
    if cmd == ".next" {
        if let Err(e) = xs.next() {
            println!("{}", xs.error_context(&e));
            println!("{}", format_opcode(xs, xs.ip()));
        } else {
            println!("{}", xs.current_line());
        }
    } else if cmd == ".rnext" {
        if let Err(e) = xs.rnext() {
            println!("{}", xs.error_context(&e));
            println!("{}", format_opcode(xs, xs.ip()));
        } else {
            println!("{}", xs.current_line());
        }
    } else if cmd == ".s" {
        let mut i = 0;
        while let Some(val) = xs.get_data(i) {
            println!("\t{:1?}", val);
            i += 1;
        }
    } else if cmd == ".top" {
        if let Some(val) = xs.get_data(0) {
            println!("\t{:?}", val);
        }        
    } else {
        let _ = xs.interpret(line);
    }
}

fn run_tty_repl(xs: &mut State, load_history: bool) {
    let mut rl = Editor::<()>::new();
    if load_history {
        let _ = rl.load_history("history.txt");
    }
    loop {
        let readline = rl.readline(">");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                eval_line(xs, &line);
            }
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            }
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }
    if load_history {
        if let Err(e) = rl.save_history("history.txt") {
            println!("history save faield: {:}", e);
        }
    }
}

pub struct XcmdArgs {
    pub debug: bool,
    pub binary_path: Option<String>,
    pub script_path: Option<String>,
}

pub fn parse_args() -> Xresult1<XcmdArgs> {
    let mut opts = Options::new();
    opts.optopt("s", "", "set script file name", "path");
    opts.optopt("i", "", "input binary file ", "path");
    opts.optflag("d", "", "enable debugging");
    let it = std::env::args().skip(1);
    let matches = opts.parse(it).map_err(|_| Xerr::InputParseError)?;
    let binary_path = matches.opt_str("i");
    let script_path = matches.opt_str("s");
    let debug = matches.opt_present("d");
    Ok(XcmdArgs {
        debug,
        binary_path,
        script_path,
    })
}

pub fn run_with_args(xs: &mut State, args: XcmdArgs) -> Xresult {
    if args.debug {
        xs.set_state_recording(true);
    }
    if let Some(path) = args.binary_path {
        xs.set_binary_input(&path)?;
    }
    if let Some(path) = args.script_path {
        let src = Lex::from_file(&path).unwrap();
        if let Err(e) = xs.load_source(src) {
            eprintln!("{}", xs.error_context(&e));
            xs.run_repl()?;
        } else if let Err(e) = xs.run() {
            eprintln!("{}", xs.error_context(&e));
            xs.run_repl()?;
        } else if args.debug {
            xs.run_repl()?;
        }
    } else {
        xs.run_repl()?;
    }
    OK
}
