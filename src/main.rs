
use xeh::vm::*;
use xeh::cell::*;

fn main() {
    //use xeh::lex::Lex;
    //let mut lex = Lex::from_str("(+[");
    let mut vm = VM::boot().unwrap();
    vm.interpret("[1 {2 2} ]").unwrap();
    println!("{:?}", vm.top_data());
    
}
