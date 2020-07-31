use xeh::prelude::*;
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut xs = Xstate::new().unwrap();
    xeh::repl::run_with_args(&mut xs, args).unwrap();
}
