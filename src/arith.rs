use crate::cell::*;
use crate::error::*;
use crate::state::*;

// (a b -- c)
fn arithmetic_ops_int(xs: &mut State, ops_int: fn(Xint, Xint) -> Xint) -> Xresult {
    let b = xs.pop_data()?.to_int()?;
    let a = xs.pop_data()?.to_int()?;
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
    match (a.value(), b.value()) {
        (Cell::Int(a), Cell::Int(b)) => xs.push_data(Cell::Int(ops_int(*a, *b))),
        (Cell::Int(a), Cell::Real(b)) => xs.push_data(Cell::Real(ops_real(*a as f64, *b))),
        (Cell::Real(a), Cell::Int(b)) => xs.push_data(Cell::Real(ops_real(*a, *b as f64))),
        (Cell::Real(a), Cell::Real(b)) => xs.push_data(Cell::Real(ops_real(*a, *b as f64))),
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
    let b = xs.pop_data()?;
    let a = xs.pop_data()?;
    match (a.value(), b.value()) {
        (Cell::Int(a), Cell::Int(b)) => if *b == 0 {
                Err(Xerr::DivisionByZero)
            } else {
                xs.push_data(Cell::Int(*a / *b))
            },
        (Cell::Int(a), Cell::Real(b)) => if *b == 0.0 {
                Err(Xerr::DivisionByZero)
            } else {
                xs.push_data(Cell::Real(*a as f64 / *b))
            },
        (Cell::Real(a), Cell::Int(b)) => if *b == 0 {
                Err(Xerr::DivisionByZero)
            } else {
                xs.push_data(Cell::Real(*a / *b as f64))
            },
        (Cell::Real(a), Cell::Real(b)) => if *b == 0.0 {
                Err(Xerr::DivisionByZero)
            } else {
                xs.push_data(Cell::Real(*a / *b as f64))
            },
        _ => Err(Xerr::TypeError),
    }
}

pub fn core_word_negate(xs: &mut State) -> Xresult {
    match xs.pop_data()?.value() {
        Cell::Int(a) => xs.push_data(Cell::Int(a.checked_neg().ok_or(Xerr::IntegerOverflow)?)),
        Cell::Real(a) => xs.push_data(Cell::Real(-a)),
        _ => Err(Xerr::TypeError),
    }
}

pub fn core_word_abs(xs: &mut State) -> Xresult {
    match xs.pop_data()?.value() {
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
    match (a.value(), b.value()) {
        (Cell::Int(a), Cell::Int(b)) => Ok(a.cmp(&b)),
        (Cell::Int(a), Cell::Real(b)) => Ok(compare_reals(*a as Xreal, *b)),
        (Cell::Real(a), Cell::Int(b)) => Ok(compare_reals(*a, *b as Xreal)),
        (Cell::Real(a), Cell::Real(b)) => Ok(compare_reals(*a, *b)),
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
    match xs.pop_data()?.value() {
        Cell::Int(x) => xs.push_data(Cell::Int(!x)),
        _ => Err(Xerr::TypeError),
    }
}

pub fn core_word_random(xs: &mut State) -> Xresult {
    let mut buf = [0u8; 4];
    getrandom::getrandom(&mut buf).unwrap();
    let r = u32::from_le_bytes(buf) as Xreal / u32::MAX as Xreal;
    xs.push_data(Cell::Real(r))
}

pub fn core_word_round(xs: &mut State) -> Xresult {
    match xs.pop_data()?.value() {
        n @ Cell::Int(_) => xs.push_data(n.clone()),
        Cell::Real(x) => xs.push_data(Cell::Int(*x as Xint)),
        _ => Err(Xerr::TypeError),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arith() {
        let mut xs = State::boot().unwrap();
        xs.eval("5 4 -").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        xs.eval("4 5 -").unwrap();
        assert_eq!(Ok(Cell::Int(-1)), xs.pop_data());
        xs.eval("4 5 *").unwrap();
        assert_eq!(Ok(Cell::Int(20)), xs.pop_data());
        xs.eval("20 4 /").unwrap();
        assert_eq!(Ok(Cell::Int(5)), xs.pop_data());
        xs.eval("1 1 +").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        xs.eval("7 3 rem").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        assert_eq!(Err(Xerr::StackUnderflow), xs.eval("1 +"));
        assert_eq!(Err(Xerr::StackUnderflow), xs.eval("+"));
        assert_eq!(Err(Xerr::TypeError), xs.eval("\"s\" 1 +"));
        xs.eval("1 1 band").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        xs.eval("1 2 bor").unwrap();
        assert_eq!(Ok(Cell::Int(3)), xs.pop_data());
        xs.eval("1 3 bxor").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        xs.eval("0 bnot").unwrap();
        assert_eq!(Ok(Cell::Int(-1)), xs.pop_data());
        xs.eval("1 3 bshl").unwrap();
        assert_eq!(Ok(Cell::Int(8)), xs.pop_data());
        xs.eval("16 3 bshr").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        xs.eval("1 negate").unwrap();
        assert_eq!(Ok(Cell::Int(-1)), xs.pop_data());
        xs.eval("-1 negate").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
    }

    #[test]
    fn test_meta_arith() {
        let mut xs = State::boot().unwrap();
        xs.eval("1 \"ok\" with-meta 1.0 +").unwrap();
        assert_eq!(Ok(Cell::Real(2.0)), xs.pop_data());
        xs.eval("2 [ ] with-meta 1 +").unwrap();
        assert_eq!(Ok(Cell::Int(3)), xs.pop_data());
    }

    #[test]
    fn test_random_round() {
        let mut xs = State::boot().unwrap();
        xs.eval("random").unwrap();
        let r = xs.pop_data().unwrap().to_real().unwrap();
        assert!(0.0 <= r && r <= 1.0);
        xs.eval("random round").unwrap();
        let i = xs.pop_data().unwrap().to_int().unwrap();
        assert!(0 <= i && i <= 1);
        xs.eval("1 round").unwrap();
        assert_eq!(Ok(1), xs.pop_data().unwrap().to_int());
        assert_eq!(Err(Xerr::TypeError), xs.eval("[ ] round"));
    }

    #[test]
    fn test_div_by_zero() {
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::DivisionByZero), xs.eval("1 0 /"));
        assert_eq!(Err(Xerr::DivisionByZero), xs.eval("1 0.0 /"));
        assert_eq!(OK, xs.eval("1 0.00000001 /"));
    }

    #[test]
    fn test_cmp() {
        let mut xs = State::boot().unwrap();
        xs.eval("-1 0 <").unwrap();
        assert_eq!(Ok(ONE), xs.pop_data());
        xs.eval("10 5 <").unwrap();
        assert_eq!(Ok(ZERO), xs.pop_data());
        xs.eval("2 3 =").unwrap();
        assert_eq!(Ok(ZERO), xs.pop_data());
        xs.eval("4 4 =").unwrap();
        assert_eq!(Ok(ONE), xs.pop_data());
    }
}
