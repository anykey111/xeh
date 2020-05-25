use xeh::state::*;

use rustyline::error::ReadlineError;
use rustyline::Editor;

use getopts::Options;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut opts = Options::new();
    opts.optopt("s", "", "set script file name", "NAME");
    let matches = opts.parse(&args[1..]).unwrap();

    let mut xs = State::new().unwrap();
    if matches.opt_present("s") {
        let filename = matches.opt_str("s").expect("script file name");
        if xs.load_file(&filename).is_ok() {
            if let Err(e) = xs.run() {
                xs.print_error(&e);
            }
        }
    }

    let mut rl = Editor::<()>::new();
    let _ = rl.load_history("history.txt");
    loop {
        let readline = rl.readline(">");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                if let Err(e) = xs.interpret_continue(line.as_str()) {
                    xs.print_error(&e);
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
    rl.save_history("history.txt").unwrap();
}
