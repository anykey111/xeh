use crate::cell::*;
use crate::error::*;
use crate::state::*;

fn arithmetic_ops_int(xs: &mut State, ops_int: fn(Xint, Xint) -> Xint) -> Xresult {
    let a = xs.pop_data()?.into_int()?;
    let b = xs.pop_data()?.into_int()?;
    let c = ops_int(a, b);
    xs.push_data(Cell::Int(c))
}

fn arithmetic_ops_real(
    xs: &mut State,
    ops_int: fn(Xint, Xint) -> Xint,
    ops_real: fn(f64, f64) -> f64,
) -> Xresult {
    let a = xs.pop_data()?;
    let b = xs.pop_data()?;
    match (a, b) {
        (Cell::Int(a), Cell::Int(b)) => xs.push_data(Cell::Int(ops_int(a, b))),
        (Cell::Int(a), Cell::Real(b)) => xs.push_data(Cell::Real(ops_real(a as f64, b))),
        (Cell::Real(a), Cell::Int(b)) => xs.push_data(Cell::Real(ops_real(a, b as f64))),
        (Cell::Real(a), Cell::Real(b)) => xs.push_data(Cell::Real(ops_real(a, b as f64))),
        _ => Err(Xerr::TypeError),
    }
}

pub fn core_word_add(xs: &mut State) -> Xresult {
    arithmetic_ops_real(xs, Xint::wrapping_add, std::ops::Add::<f64>::add)
}

pub fn core_word_sub(xs: &mut State) -> Xresult {
    arithmetic_ops_real(xs, Xint::wrapping_sub, std::ops::Sub::<f64>::sub)
}

pub fn core_word_mul(xs: &mut State) -> Xresult {
    arithmetic_ops_real(xs, Xint::wrapping_mul, std::ops::Mul::<f64>::mul)
}

pub fn core_word_div(xs: &mut State) -> Xresult {
    arithmetic_ops_real(xs, Xint::wrapping_div, std::ops::Div::<f64>::div)
}

pub fn core_word_rem(xs: &mut State) -> Xresult {
    arithmetic_ops_real(xs, Xint::wrapping_rem, std::ops::Rem::<f64>::rem)
}

pub fn core_word_bitand(xs: &mut State) -> Xresult {
    arithmetic_ops_int(xs, std::ops::BitAnd::<Xint>::bitand)
}

pub fn core_word_bitor(xs: &mut State) -> Xresult {
    arithmetic_ops_int(xs, std::ops::BitOr::<Xint>::bitor)
}

pub fn core_word_bitxor(xs: &mut State) -> Xresult {
    arithmetic_ops_int(xs, std::ops::BitXor::<Xint>::bitxor)
}

pub fn core_word_bitshl(xs: &mut State) -> Xresult {
    arithmetic_ops_int(xs, |a, b| Xint::wrapping_shl(a, b as u32))
}

pub fn core_word_bitshr(xs: &mut State) -> Xresult {
    arithmetic_ops_int(xs, |a, b| Xint::wrapping_shr(a, b as u32))
}

pub fn core_word_bitnot(xs: &mut State) -> Xresult {
    match xs.pop_data()? {
        Cell::Int(x) => xs.push_data(Cell::Int(!x)),

        _ => Err(Xerr::TypeError),
    }
}

#[test]
fn test_arith() {
    let mut xs = State::new().unwrap();
    xs.interpret("5 4 -").unwrap();
    assert_eq!(Ok(Cell::Int(-1)), xs.pop_data());
    xs.interpret("4 5 -").unwrap();
    assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
    xs.interpret("4 5 *").unwrap();
    assert_eq!(Ok(Cell::Int(20)), xs.pop_data());
    xs.interpret("4 20 /").unwrap();
    assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
    xs.interpret("1 1 +").unwrap();
    assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
    xs.interpret("3 7 rem").unwrap();
    assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
    assert_eq!(Err(Xerr::StackUnderflow), xs.interpret("1 +"));
    assert_eq!(Err(Xerr::StackUnderflow), xs.interpret("+"));
    assert_eq!(Err(Xerr::TypeError), xs.interpret("\"s\" 1 +"));
    xs.interpret("1 1 bitand").unwrap();
    assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
    xs.interpret("1 2 bitor").unwrap();
    assert_eq!(Ok(Cell::Int(3)), xs.pop_data());
    xs.interpret("1 3 bitxor").unwrap();
    assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
    xs.interpret("0 bitnot").unwrap();
    assert_eq!(Ok(Cell::Int(-1)), xs.pop_data());
    xs.interpret("3 1 bitshl").unwrap();
    assert_eq!(Ok(Cell::Int(8)), xs.pop_data());
    xs.interpret("3 16 bitshr").unwrap();
    assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
}
