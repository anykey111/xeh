use xeh::prelude::*;

fn main() -> Xresult {
    let mut xs = Xstate::new()?;
    let args = xeh::repl::parse_args()?;
    xeh::repl::run_with_args(&mut xs, args)
}
