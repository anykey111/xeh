
use xeh::vm::VM;

fn main() {
    //use xeh::lex::Lex;
    //let mut lex = Lex::from_str("(+[");
    let mut vm = VM::boot().unwrap();
    vm.load("1 else 222 then").unwrap();
}
