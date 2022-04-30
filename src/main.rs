use std::process::exit;

use xeh::prelude::*;

#[cfg(feature = "stdio")]
fn run() -> Xresult {
    xeh::repl::run_with_args()
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
