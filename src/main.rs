
use xeh::vm::*;

fn main() {
    //use xeh::lex::Lex;
    //let mut lex = Lex::from_str("(+[");
    let mut vm = VM::boot().unwrap();
    vm.interpret("[1, 2]").unwrap();
    println!("{:?}", vm.top_data());
}
