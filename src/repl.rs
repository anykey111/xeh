use crate::state::*;
use crate::error::*;
use rustyline::error::ReadlineError;
use rustyline::Editor;

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
