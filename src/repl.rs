use crate::state::*;
use rustyline::error::ReadlineError;
use rustyline::Editor;

pub fn console_repl(xs: &mut State, load_history: bool) {
    let mut rl = Editor::<()>::new();
    if load_history {
        let _ = rl.load_history("history.txt");
    }
    loop {
        let readline = rl.readline(">");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                if line.trim() == ".next" {
                    if let Err(e) = xs.next() {
                        xs.print_error(&e);
                    }
                } else if line.trim() == ".rnext" {
                    if let Err(e) = xs.rnext() {
                        xs.print_error(&e);
                    } else {
                        println!("{}", format_opcode(xs, xs.ip()));
                    }
                } else {
                    if let Err(e) = xs.interpret_continue(line.as_str()) {
                        xs.print_error(&e);
                    }
                }
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
