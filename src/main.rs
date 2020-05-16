
use xeh::vm::*;
use xeh::cell::*;

fn main() {
    //use xeh::lex::Lex;
    //let mut lex = Lex::from_str("(+[");
    println!("{:?}", std::mem::size_of::<Cell>());
    let mut vm = VM::boot().unwrap();
    
    vm.interpret("([1 2]) const x").unwrap();
    println!("{:?}", vm.top_data());

}

