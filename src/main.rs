
use xeh::vm::*;

fn main() {
    //use xeh::lex::Lex;
    //let mut lex = Lex::from_str("(+[");
    let mut vm = VM::boot().unwrap();
    vm.interpret("begin 1 leave again").unwrap();
    println!("{:?}", vm.top_data());
}
