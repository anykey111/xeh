use xeh::state::*;
use xeh::lex::*;

use getopts::Options;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut opts = Options::new();
    opts.optopt("s", "", "set script file name", "path");
    opts.optopt("i", "", "set input binary", "path");
    opts.optflag("d", "", "enable debugging");
    let matches = opts.parse(&args[1..]).unwrap();

    let mut xs = State::new().unwrap();
    if matches.opt_present("i") {
        let path = matches.opt_str("i").expect("binary file");
        xs.set_binary_input(&path).unwrap();
    }
    if matches.opt_present("d") {
        xs.set_state_recording(true);
    }
    if matches.opt_present("s") {
        let filename = matches.opt_str("s").expect("script file name");
        let src = Lex::from_file(&filename).unwrap();
        if let Err(e) = xs.load_source(src) {
            eprintln!("{}", xs.error_context(&e));
            xs.run_repl().unwrap();
        } else if let Err(e) = xs.run() {
            eprintln!("{}", xs.error_context(&e));
            xs.run_repl().unwrap();
        }
    } else {
        xs.run_repl().unwrap();
    }
}
