use crate::cell::*;
use crate::error::*;
use crate::state::*;

// (a b -- c)
fn arithmetic_ops_int(xs: &mut State, ops_int: fn(Xint, Xint) -> Xint) -> Xresult {
    let b = xs.pop_data()?.into_int()?;
    let a = xs.pop_data()?.into_int()?;
    let c = ops_int(a, b);
    xs.push_data(Cell::Int(c))
}

fn arithmetic_ops_real(
    xs: &mut State,
    ops_int: fn(Xint, Xint) -> Xint,
    ops_real: fn(f64, f64) -> f64,
) -> Xresult {
    let b = xs.pop_data()?;
    let a = xs.pop_data()?;
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

pub fn core_word_inc(xs: &mut State) -> Xresult {
    match xs.pop_data()? {
        Cell::Int(a) => xs.push_data(Cell::Int(a + 1)),
        Cell::Real(a) => xs.push_data(Cell::Real(a + 1.0)),
        _ => Err(Xerr::TypeError),
    }
}

pub fn core_word_dec(xs: &mut State) -> Xresult {
    match xs.pop_data()? {
        Cell::Int(a) => xs.push_data(Cell::Int(a - 1)),
        Cell::Real(a) => xs.push_data(Cell::Real(a - 1.0)),
        _ => Err(Xerr::TypeError),
    }
}

pub fn core_word_negate(xs: &mut State) -> Xresult {
    match xs.pop_data()? {
        Cell::Int(a) => xs.push_data(Cell::Int(a.checked_neg().ok_or(Xerr::IntegerOverflow)?)),
        Cell::Real(a) => xs.push_data(Cell::Real(-a)),
        _ => Err(Xerr::TypeError),
    }
}

pub fn core_word_abs(xs: &mut State) -> Xresult {
    match xs.pop_data()? {
        Cell::Int(a) => xs.push_data(Cell::Int(a.abs())),
        Cell::Real(a) => xs.push_data(Cell::Real(a.abs())),
        _ => Err(Xerr::TypeError),
    }
}

use std::cmp::Ordering;

fn compare_reals(a: Xreal, b: Xreal) -> Ordering {
    if a < b {
        Ordering::Less
    } else if a > b {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

fn compare_cells(xs: &mut State) -> Xresult1<Ordering> {
    let b = xs.pop_data()?;
    let a = xs.pop_data()?;
    match (a, b) {
        (Cell::Int(a), Cell::Int(b)) => Ok(a.cmp(&b)),
        (Cell::Int(a), Cell::Real(b)) => Ok(compare_reals(a as Xreal, b)),
        (Cell::Real(a), Cell::Int(b)) => Ok(compare_reals(a, b as Xreal)),
        (Cell::Real(a), Cell::Real(b)) => Ok(compare_reals(a, b)),
        _ => Err(Xerr::TypeError),
    }
}

pub fn core_word_less_then(xs: &mut State) -> Xresult {
    let c = compare_cells(xs)?;
    xs.push_data(Cell::from(c == Ordering::Less))
}

pub fn core_word_eq(xs: &mut State) -> Xresult {
    let c = compare_cells(xs)?;
    xs.push_data(Cell::from(c == Ordering::Equal))
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

use rand::prelude::*;

pub fn core_word_random(xs: &mut State) -> Xresult {
    let mut rng = rand::thread_rng();
    let r: f64 = rng.gen();
    xs.push_data(Cell::Real(r))
}

pub fn core_word_round(xs: &mut State) -> Xresult {
    match xs.pop_data()? {
        n @ Cell::Int(_) => xs.push_data(n),
        Cell::Real(x) => xs.push_data(Cell::Int(x as Xint)),
        _ => Err(Xerr::TypeError),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arith() {
        let mut xs = State::new().unwrap();
        xs.interpret("5 4 -").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        xs.interpret("4 5 -").unwrap();
        assert_eq!(Ok(Cell::Int(-1)), xs.pop_data());
        xs.interpret("4 5 *").unwrap();
        assert_eq!(Ok(Cell::Int(20)), xs.pop_data());
        xs.interpret("20 4 /").unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
        xs.interpret("1 1 +").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        xs.interpret("7 3 rem").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        xs.interpret("1 inc").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        xs.interpret("1 dec").unwrap();
        assert_eq!(Ok(Cell::Int(0)), xs.pop_data());
        assert_eq!(Err(Xerr::StackUnderflow), xs.interpret("1 +"));
        assert_eq!(Err(Xerr::StackUnderflow), xs.interpret("+"));
        assert_eq!(Err(Xerr::TypeError), xs.interpret("\"s\" 1 +"));
        xs.interpret("1 1 bit-and").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        xs.interpret("1 2 bit-or").unwrap();
        assert_eq!(Ok(Cell::Int(3)), xs.pop_data());
        xs.interpret("1 3 bit-xor").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        xs.interpret("0 bit-not").unwrap();
        assert_eq!(Ok(Cell::Int(-1)), xs.pop_data());
        xs.interpret("1 3 bit-shift-left").unwrap();
        assert_eq!(Ok(Cell::Int(8)), xs.pop_data());
        xs.interpret("16 3 bit-shift-right").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        xs.interpret("1 neg").unwrap();
        assert_eq!(Ok(Cell::Int(-1)), xs.pop_data());
        xs.interpret("-1 neg").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
    }

    #[test]
    fn test_random_round() {
        let mut xs = State::new().unwrap();
        xs.interpret("random").unwrap();
        let r = xs.pop_data().unwrap().into_real().unwrap();
        assert!(0.0 <= r && r <= 1.0);
        xs.interpret("random round").unwrap();
        let i = xs.pop_data().unwrap().into_int().unwrap();
        assert!(0 <= i && i <= 1);
        xs.interpret("1 round").unwrap();
        assert_eq!(Ok(1), xs.pop_data().unwrap().into_int());
        assert_eq!(Err(Xerr::TypeError), xs.interpret("[] round"));
    }

    #[test]
    fn test_cmp() {
        let mut xs = State::new().unwrap();
        xs.interpret("-1 0 <").unwrap();
        assert_eq!(Ok(ONE), xs.pop_data());
        xs.interpret("10 5 <").unwrap();
        assert_eq!(Ok(ZERO), xs.pop_data());
        xs.interpret("2 3 =").unwrap();
        assert_eq!(Ok(ZERO), xs.pop_data());
        xs.interpret("4 4 =").unwrap();
        assert_eq!(Ok(ONE), xs.pop_data());
    }
}
