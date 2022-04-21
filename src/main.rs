use std::process::exit;

use xeh::prelude::*;

#[cfg(feature = "stdio")]
fn run() -> Xresult {
    let mut xs = Xstate::boot()?;
    xeh::d2_plugin::load(&mut xs)?;
    let args = xeh::repl::parse_args()?;
    let res = xeh::repl::run_with_args(&mut xs, args);
    if let Err(e) = &res {
        let errstr = xs.pretty_error(e);
        eprintln!("{:?}", errstr);
    }
    res
}

#[cfg(not(feature = "stdio"))]
fn run() -> Xresult {
    panic!("stdio feature disabled");
}

fn main() {
    if run().is_err() {
        exit(1)
    }
    exit(0)
}
