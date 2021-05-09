use xeh::prelude::*;

fn main() -> Xresult {
    #[cfg(not(feature = "stdio"))]
    panic!("stdio feature disabled");

    #[cfg(feature = "stdio")]
    {
        let mut xs = Xstate::new()?;
        xeh::d2_plugin::load(&mut xs)?;
        let args = xeh::repl::parse_args()?;
        xeh::repl::run_with_args(&mut xs, args)
    }
}
