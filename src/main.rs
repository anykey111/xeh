use xeh::cell::*;
use xeh::state::*;

use rustyline::error::ReadlineError;
use rustyline::Editor;

fn main() {
    let mut rl = Editor::<()>::new();
    let _ = rl.load_history("history.txt");
    let mut xs = State::new().unwrap();
    loop {
        let readline = rl.readline(">");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                let res = xs.interpret(line.as_str());
                if res.is_err() {
                    println!("Error: {:?}", res);
                }
            },
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break
            },
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break
            },
            Err(err) => {
                println!("Error: {:?}", err);
                break
            }
        }
    }
    rl.save_history("history.txt").unwrap();
}

