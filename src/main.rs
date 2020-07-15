use xeh::state::*;

use getopts::Options;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut opts = Options::new();
    opts.optopt("s", "", "set script file name", "NAME");
    opts.optopt("d", "", "enable debugging", "NAME");
    let matches = opts.parse(&args[1..]).unwrap();

    let mut xs = State::new().unwrap();
    if matches.opt_present("s") {
        let filename = matches.opt_str("s").expect("script file name");
        if xs.load_file(&filename).is_ok() {
            if let Err(e) = xs.run() {
                eprintln!("{}", xs.format_error(&e));
            }
        }
    }

    xs.run_repl();
}
