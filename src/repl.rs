use crate::prelude::*;
use crate::state::format_opcode;
use getopts::Options;
use rustyline::error::ReadlineError;
use rustyline::Editor;

pub fn run(xs: &mut Xstate) -> Xresult {
    crate::repl::run_tty_repl(xs, true);
    OK
}

fn eval_line(xs: &mut Xstate, line: &str) -> Xresult {
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
        xs.interpret(line)?;
    }
    OK
}

fn run_tty_repl(xs: &mut Xstate, load_history: bool) {
    let mut rl = Editor::<()>::new();
    if load_history {
        let _ = rl.load_history("history.txt");
    }
    loop {
        if xs.about_to_stop {
            eprintln!("BYE!");
            break;
        }
        let readline = rl.readline(">");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                let _ = eval_line(xs, &line);
            }
            Err(ReadlineError::Interrupted) => {
                eprintln!("CTRL-C");
                xs.about_to_stop = true;
            }
            Err(ReadlineError::Eof) => {
                eprintln!("CTRL-D");
                xs.about_to_stop = true;
            }
            Err(err) => {
                eprintln!("readline error: {:?}", err);
                xs.about_to_stop = true;
            }
        }
    }
    if load_history {
        if let Err(e) = rl.save_history("history.txt") {
            eprintln!("history save faield: {:}", e);
        }
    }
}

pub struct XcmdArgs {
    pub debug: bool,
    pub binary_path: Option<String>,
    pub sources: Vec<String>,
    pub eval: Option<String>,
}

pub fn parse_args() -> Xresult1<XcmdArgs> {
    let mut opts = Options::new();
    opts.optopt("i", "", "input binary file ", "path");
    opts.optopt("e", "", "evaluate expression", "expression");
    opts.optflag("d", "", "enable debugging");
    let it = std::env::args().skip(1);
    let matches = opts.parse(it).map_err(|e| {
        eprintln!("getopts: {}", e);
        Xerr::InputParseError
    })?;
    let debug = matches.opt_present("d");
    let binary_path = matches.opt_str("i");
    let eval = matches.opt_str("e");
    Ok(XcmdArgs {
        debug,
        binary_path,
        sources: matches.free,
        eval,
    })
}

pub fn run_with_args(xs: &mut Xstate, args: XcmdArgs) -> Xresult {
    if args.debug {
        xs.set_state_recording(true);
    }
    if let Some(ref path) = args.binary_path {
        crate::file::load_binary(xs, path)?;
    }
    for filename in args.sources.iter() {
        xs.load_source(filename)?;
    }
    let mut result = OK;
    if !args.sources.is_empty() {
        result = xs.run();
        if let Err(ref e) = result {
            eprintln!("{:?}", e);
        }
    }
    if let Some(s) = args.eval {
        if result.is_ok() {
            if let Err(e) = xs.interpret(&s) {
                eprintln!("{:?}", e);
            }
        }
    }
    crate::repl::run(xs)
}
