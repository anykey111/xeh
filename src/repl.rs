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
            eprintln!("{}", xs.pretty_error(&e));
            eprintln!("{}", format_opcode(xs, xs.ip()));
        } else {
            eprintln!("{}", xs.current_line());
        }
    } else if cmd == ".rnext" {
        if let Err(e) = xs.rnext() {
            eprintln!("{}", xs.pretty_error(&e));
            eprintln!("{}", format_opcode(xs, xs.ip()));
        } else {
            eprintln!("{}", xs.current_line());
        }
    } else if cmd == ".s" {
        let mut i = 0;
        while let Some(val) = xs.get_data(i) {
            eprintln!("\t{:1?}", val);
            i += 1;
        }
    } else if cmd == ".top" {
        if let Some(val) = xs.get_data(0) {
            eprintln!("\t{:?}", val);
        }
    } else {
        xs.eval(line)?;
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
        let readline = rl.readline(">>");
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
    if let Some(ref path) = args.binary_path {
        crate::file::load_binary(xs, path)?;
    }
    if args.debug {
        xs.start_reverse_debugging();
    }
    for filename in args.sources.iter() {
        xs.load_file(filename)?;
    }
    if !args.sources.is_empty() {
        let result = xs.run();
        if let Err(e) = &result {
            eprintln!("{}", xs.pretty_error(e));
            return result;
        }
    }
    if let Some(s) = args.eval {
        xs.eval(&s)
    } else if args.sources.is_empty() {
        crate::repl::run(xs)
    } else {
        OK
    }
}
