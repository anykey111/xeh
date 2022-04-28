use crate::cell::*;
use crate::error::*;
use crate::prelude::Xstate;
use crate::state::*;

pub fn load(xs: &mut Xstate) -> Xresult {
    xs.defword("+", core_word_add)?;
    xs.defword("-", core_word_sub)?;
    xs.defword("*", core_word_mul)?;
    xs.defword("/", core_word_div)?;
    xs.defword("negate", core_word_negate)?;
    xs.defword("abs", core_word_abs)?;
    xs.defword("<", |xs| {
        let t = compare_cells(xs)?.is_lt();
        xs.push_data(Cell::from(t))
    })?;
    xs.defword("<=", |xs| {
        let t = compare_cells(xs)?.is_le();
        xs.push_data(Cell::from(t))
    })?;
    xs.defword(">", |xs| {
        let t = compare_cells(xs)?.is_gt();
        xs.push_data(Cell::from(t))
    })?;
    xs.defword(">=", |xs| {
        let t = compare_cells(xs)?.is_ge();
        xs.push_data(Cell::from(t))
    })?;
    xs.defword("=", |xs| {
        let t = compare_cells(xs)?.is_eq();
        xs.push_data(Cell::from(t))
    })?;
    xs.defword("<>", |xs| {
        let t = compare_cells(xs)?.is_ne();
        xs.push_data(Cell::from(t))
    })?;
    xs.defword("rem", core_word_rem)?;
    xs.defword("and", core_word_bitand)?;
    xs.defword("or", core_word_bitor)?;
    xs.defword("xor", core_word_bitxor)?;
    xs.defword("shl", core_word_bitshl)?;
    xs.defword("shr", core_word_bitshr)?;
    xs.defword("not", core_word_bitnot)?;
    xs.defword("round", core_word_round)?;
    xs.defword("random", core_word_random)?;
    xs.defword("min", core_word_min)?;
    xs.defword("max", core_word_max)?;
    OK
}

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
    ops_real: fn(Xreal, Xreal) -> Xreal,
) -> Xresult {
    let b = xs.pop_data()?;
    let a = xs.pop_data()?;
    match b.value() {
        Cell::Int(b) => {
            match a.value() {
                Cell::Int(a) => {
                    let c = Cell::from(ops_int(*a, *b));
                    xs.push_data(c)
                }
                _ => Err(Xerr::TypeError)
            }
        },
        Cell::Real(b) => {
            match a.value() {
                Cell::Real(a) => {
                    let c = Cell::from(ops_real(*a, *b));
                    xs.push_data(c)
                }
                _ => Err(Xerr::TypeError)
            }
        }
        _ => Err(Xerr::TypeError)
    }
}

fn core_word_add(xs: &mut State) -> Xresult {
    arithmetic_ops_real(xs, Xint::wrapping_add, std::ops::Add::<Xreal>::add)
}

fn core_word_sub(xs: &mut State) -> Xresult {
    arithmetic_ops_real(xs, Xint::wrapping_sub, std::ops::Sub::<Xreal>::sub)
}

fn core_word_mul(xs: &mut State) -> Xresult {
    arithmetic_ops_real(xs, Xint::wrapping_mul, std::ops::Mul::<Xreal>::mul)
}

fn core_word_div(xs: &mut State) -> Xresult {
    let b = xs.pop_data()?;
    let a = xs.pop_data()?;
    match b.value() {
        Cell::Int(b) => {
            match a.value() {
                Cell::Int(a) => {
                    if *b == 0 {
                        Err(Xerr::DivisionByZero)
                    } else {
                        let c = Cell::from(*a / *b);
                        xs.push_data(c)
                    }
                }
                _ => Err(Xerr::TypeError)
            }
        },
        Cell::Real(b) => {
            match a.value() {
                Cell::Real(a) => {
                    if *b == 0.0 {
                        Err(Xerr::DivisionByZero)
                    } else {
                        let c = Cell::from(*a / *b);
                        xs.push_data(c)
                    }
                }
                _ => Err(Xerr::TypeError)
            }
        }
        _ => Err(Xerr::TypeError)
    }
}

fn core_word_negate(xs: &mut State) -> Xresult {
    match xs.pop_data()?.value() {
        Cell::Int(a) => xs.push_data(Cell::Int(a.checked_neg().ok_or(Xerr::IntegerOverflow)?)),
        Cell::Real(a) => xs.push_data(Cell::Real(-a)),
        _ => Err(Xerr::TypeError),
    }
}

fn core_word_abs(xs: &mut State) -> Xresult {
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

fn core_word_min(xs: &mut State) -> Xresult {
    arithmetic_ops_real(xs, |a, b| a.min(b), |a,b| a.min(b))
}

fn core_word_max(xs: &mut State) -> Xresult {
    arithmetic_ops_real(xs, |a, b| a.max(b), |a,b| a.max(b))
}

fn core_word_rem(xs: &mut State) -> Xresult {
    arithmetic_ops_real(xs, Xint::wrapping_rem, std::ops::Rem::<f64>::rem)
}

fn core_word_bitand(xs: &mut State) -> Xresult {
    arithmetic_ops_int(xs, std::ops::BitAnd::<Xint>::bitand)
}

fn core_word_bitor(xs: &mut State) -> Xresult {
    arithmetic_ops_int(xs, std::ops::BitOr::<Xint>::bitor)
}

fn core_word_bitxor(xs: &mut State) -> Xresult {
    arithmetic_ops_int(xs, std::ops::BitXor::<Xint>::bitxor)
}

fn core_word_bitshl(xs: &mut State) -> Xresult {
    arithmetic_ops_int(xs, |a, b| Xint::wrapping_shl(a, b as u32))
}

fn core_word_bitshr(xs: &mut State) -> Xresult {
    arithmetic_ops_int(xs, |a, b| Xint::wrapping_shr(a, b as u32))
}

fn core_word_bitnot(xs: &mut State) -> Xresult {
    match xs.pop_data()?.value() {
        Cell::Int(x) => xs.push_data(Cell::Int(!x)),
        _ => Err(Xerr::TypeError),
    }
}

fn core_word_random(xs: &mut State) -> Xresult {
    let mut buf = [0u8; 4];
    getrandom::getrandom(&mut buf).unwrap();
    let r = u32::from_le_bytes(buf) as Xreal / u32::MAX as Xreal;
    xs.push_data(Cell::Real(r))
}

fn core_word_round(xs: &mut State) -> Xresult {
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
        match xs.eval("\"s\" 1 +") {
            Err(Xerr::TypeError) => (),
            other => panic!("result {:?}", other),
        }
        xs.eval("1 1 and").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        xs.eval("1 2 or").unwrap();
        assert_eq!(Ok(Cell::Int(3)), xs.pop_data());
        xs.eval("1 3 xor").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        xs.eval("0 not").unwrap();
        assert_eq!(Ok(Cell::Int(-1)), xs.pop_data());
        xs.eval("1 3 shl").unwrap();
        assert_eq!(Ok(Cell::Int(8)), xs.pop_data());
        xs.eval("16 3 shr").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        xs.eval("1 negate").unwrap();
        assert_eq!(Ok(Cell::Int(-1)), xs.pop_data());
        xs.eval("-1 negate").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
    }

    #[test]
    fn test_tag_arith() {
        let mut xs = State::boot().unwrap();
        xs.eval("1.0 \"ok\" with-tag 1.0 +").unwrap();
        assert_eq!(Ok(Cell::Real(2.0)), xs.pop_data());
        xs.eval("2 [ ] with-tag 1 +").unwrap();
        assert_eq!(Ok(Cell::Int(3)), xs.pop_data());
    }

    #[test]
    fn test_min_max() {
        let mut xs = State::boot().unwrap();
        xs.eval("-1.0 0 min").unwrap();
        assert_eq!(Ok(Cell::from(-1.0)), xs.pop_data());
        xs.eval("-1 0 max").unwrap();
        assert_eq!(Ok(Cell::from(0u32)), xs.pop_data());        
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
        assert_eq!(Err(Xerr::DivisionByZero), xs.eval("1.0 0.0 /"));
        assert_eq!(OK, xs.eval("1.0 0.00000001 /"));
    }

    #[test]
    fn test_cmp() {
        let mut xs = State::boot().unwrap();
        assert_eq!(Ok(TRUE), xs.eval("-1 0 <").and_then(|_| xs.pop_data()));
        assert_eq!(Ok(FALSE), xs.eval("10 5 <").and_then(|_| xs.pop_data()));
        assert_eq!(Ok(FALSE), xs.eval("2 3 =").and_then(|_| xs.pop_data()));
        assert_eq!(Ok(TRUE), xs.eval("4 4 =").and_then(|_| xs.pop_data()));
        assert_eq!(Ok(TRUE), xs.eval("2 1 >").and_then(|_| xs.pop_data()));
        assert_eq!(Ok(TRUE), xs.eval("2 2 >=").and_then(|_| xs.pop_data()));
        assert_eq!(Ok(FALSE), xs.eval("1 2 >").and_then(|_| xs.pop_data()));
        assert_eq!(Ok(TRUE), xs.eval("1 1 >=").and_then(|_| xs.pop_data()));
        assert_eq!(Ok(FALSE), xs.eval("7 7 <>").and_then(|_| xs.pop_data()));
        assert_eq!(Ok(TRUE), xs.eval("7 8 <>").and_then(|_| xs.pop_data()));
    }
}
