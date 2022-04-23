use crate::prelude::*;
use getopts::Options;
use rustyline::error::ReadlineError;
use rustyline::Editor;

fn print_pretty_error(xs: &mut Xstate, e: &Xerr) {
    let s = xs.pretty_error().unwrap_or_else(|| format!("{:?}", e));
    eprintln!("{}", s);
}

fn eval_line(xs: &mut Xstate, line: &str) -> Xresult {
    let cmd = line.trim();
    if cmd == ".next" {
        xs.next()
    } else if cmd == ".rnext" {
        xs.rnext()
    } else {
        xs.eval(line)
    }
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
                if let Err(e) = eval_line(xs, &line) {
                    print_pretty_error(xs, &e);
                }
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
    pub reverse_debug: bool,
    pub binary_path: Option<String>,
    pub sources: Vec<String>,
    pub eval: Option<String>,
}

pub fn parse_args() -> Xresult1<XcmdArgs> {
    let mut opts = Options::new();
    opts.optopt("i", "", "input binary file ", "path");
    opts.optopt("e", "", "evaluate expression", "expression");
    opts.optflag("r", "", "reverse debugging");
    let it = std::env::args().skip(1);
    let matches = opts.parse(it).map_err(|e| {
        eprintln!("getopts: {}", e);
        Xerr::InputParseError
    })?;
    Ok(XcmdArgs {
        reverse_debug: matches.opt_present("r"),
        binary_path: matches.opt_str("i"),
        eval: matches.opt_str("e"),
        sources: matches.free,
    })
}

pub fn run_with_args(xs: &mut Xstate, args: XcmdArgs) -> Xresult {
    let res = run_with_args1(xs, args);
    if let Err(e) = res.as_ref() {
        print_pretty_error(xs, e);
    }
    res
}

pub fn run_with_args1(xs: &mut Xstate, args: XcmdArgs) -> Xresult {
    if let Some(ref path) = args.binary_path {
        crate::file::load_binary(xs, path)?;
    }
    xs.load_help()?;
    if args.reverse_debug {
        xs.start_recording();
    }
    for path in args.sources.iter() {
        xs.eval_from_file(&path)?;
    }
    if let Some(s) = args.eval {
        xs.eval(&s)
    } else if args.sources.is_empty() {
        run_tty_repl(xs, true);
        OK
    } else {
        OK
    }
}
