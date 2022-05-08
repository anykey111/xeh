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
    xs.defword("and", logical_and)?;
    xs.defword("or", logical_or)?;
    xs.defword("xor", logical_xor)?;
    xs.defword("not", logical_not)?;
    xs.defword("bit-and", core_word_bitand)?;
    xs.defword("bit-or", core_word_bitor)?;
    xs.defword("bit-xor",core_word_bitxor)?;
    xs.defword("bit-not", core_word_bitnot)?;
    xs.defword("bit-shl", core_word_bitshl)?;
    xs.defword("bit-shr", core_word_bitshr)?;
    xs.defword("round", core_word_round)?;
    xs.defword("random", core_word_random)?;
    xs.defword("min", core_word_min)?;
    xs.defword("max", core_word_max)?;
    xs.defword(">real", core_word_into_real)?;
    xs.defword(">int", core_word_into_int)?;
    xs.defword("zero?", core_word_is_zero)?;
    xs.defword("positive?", core_word_is_positive)?;
    xs.defword("negative?", core_word_is_negative)?;
    OK
}

const NUM_TYPE_NAME: Xstr = arcstr::literal!("num");

// (a b -- c)
fn arithmetic_ops_int(xs: &mut State, ops_int: fn(Xint, Xint) -> Xint) -> Xresult {
    let b = xs.pop_data()?.to_xint()?;
    let a = xs.pop_data()?.to_xint()?;
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
            let a = a.to_xint()?;
            let c = Cell::from(ops_int(a, *b));
            xs.push_data(c)
        }
        Cell::Real(b) => {
            let a = a.to_real()?;
            let c = Cell::from(ops_real(a, *b));
            xs.push_data(c)
        }
        _ => Err(Xerr::TypeErrorMsg {
            msg: NUM_TYPE_NAME,
            val: b,
        }),
    }
}

fn num_type_error(val: Cell) -> Xerr {
    Xerr::TypeErrorMsg {
        msg: NUM_TYPE_NAME,
        val,
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
            let a = a.to_xint()?;
            if *b == 0 {
                Err(Xerr::DivisionByZero)
            } else {
                let c = Cell::from(a / *b);
                xs.push_data(c)
            }
        }
        Cell::Real(b) => {
            let a = a.to_real()?;
            if *b == 0.0 {
                Err(Xerr::DivisionByZero)
            } else {
                let c = Cell::from(a / *b);
                xs.push_data(c)
            }
        }
        _ => Err(num_type_error(b)),
    }
}

fn core_word_negate(xs: &mut State) -> Xresult {
    let a = xs.pop_data()?;
    match a.value() {
        Cell::Int(a) => {
            let neg = a.checked_neg().ok_or_else(|| Xerr::IntegerOverflow)?;
            xs.push_data(Cell::Int(neg))
        }
        Cell::Real(a) => xs.push_data(Cell::Real(-a)),
        _ => Err(num_type_error(a)),
    }
}

fn core_word_abs(xs: &mut State) -> Xresult {
    let a = xs.pop_data()?;
    match a.value() {
        Cell::Int(a) => xs.push_data(Cell::Int(a.abs())),
        Cell::Real(a) => xs.push_data(Cell::Real(a.abs())),
        _ => Err(num_type_error(a)),
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
    match b.value() {
        Cell::Int(b) => {
            let a = a.to_xint()?;
            Ok(a.cmp(b))
        }
        Cell::Real(b) => {
            let a = a.to_real()?;
            Ok(compare_reals(a, *b))
        }
        _ => Err(num_type_error(b)),
    }
}

fn core_word_into_real(xs: &mut State) -> Xresult {
    match xs.top_data()?.value() {
        Cell::Real(_) => OK,
        _ => {
            let a = xs.pop_data()?.to_xint()?;
            xs.push_data(Cell::from(a as Xreal))
        }
    }
}

fn core_word_into_int(xs: &mut State) -> Xresult {
    match xs.top_data()?.value() {
        Cell::Int(_) => OK,
        _ => {
            let a = xs.pop_data()?.to_real()?;
            xs.push_data(Cell::from(a as Xint))
        }
    }
}

fn core_word_is_zero(xs: &mut State) -> Xresult {
    match xs.top_data()?.value() {
        Cell::Int(a) => {
            let flag = Cell::from(*a == 0);
            xs.push_data(flag)
        }
        Cell::Real(a) => {
            let flag = Cell::from(*a == 0.0);
            xs.push_data(flag)
        }
        _ => {
            let val = xs.top_data()?.clone();
            Err(num_type_error(val))
        }
    }
}

fn core_word_is_positive(xs: &mut State) -> Xresult {
    match xs.top_data()?.value() {
        Cell::Int(a) => {
            let flag = Cell::from(*a > 0);
            xs.push_data(flag)
        }
        Cell::Real(a) => {
            let flag = Cell::from(*a > 0.0);
            xs.push_data(flag)
        }
        _ => {
            let val = xs.top_data()?.clone();
            Err(num_type_error(val))
        }
    }
}

fn core_word_is_negative(xs: &mut State) -> Xresult {
    match xs.top_data()?.value() {
        Cell::Int(a) => {
            let flag = Cell::from(*a < 0);
            xs.push_data(flag)
        }
        Cell::Real(a) => {
            let flag = Cell::from(*a < 0.0);
            xs.push_data(flag)
        }
        _ => {
            let val = xs.top_data()?.clone();
            Err(num_type_error(val))
        }
    }
}

fn logical_not(xs: &mut State) -> Xresult {
    let f = xs.pop_data()?.flag()?;
    xs.push_data(Cell::from(!f))
}

fn logical_and(xs: &mut State) -> Xresult {
    let b = xs.pop_data()?;
    let a = xs.pop_data()?;
    let c = a.flag()? & b.flag()?;
    xs.push_data(Cell::from(c))
}

fn logical_or(xs: &mut State) -> Xresult {
    let b = xs.pop_data()?;
    let a = xs.pop_data()?;
    let c = a.flag()? | b.flag()?;
    xs.push_data(Cell::from(c))
}

fn logical_xor(xs: &mut State) -> Xresult {
    let b = xs.pop_data()?;
    let a = xs.pop_data()?;
    let c = a.flag()? ^ b.flag()?;
    xs.push_data(Cell::from(c))
}

fn core_word_min(xs: &mut State) -> Xresult {
    arithmetic_ops_real(xs, |a, b| a.min(b), |a, b| a.min(b))
}

fn core_word_max(xs: &mut State) -> Xresult {
    arithmetic_ops_real(xs, |a, b| a.max(b), |a, b| a.max(b))
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
    let a = xs.pop_data()?.to_xint()?;
    xs.push_data(Cell::from(!a))
}

fn core_word_random(xs: &mut State) -> Xresult {
    let mut buf = [0u8; 4];
    getrandom::getrandom(&mut buf).unwrap();
    let r = u32::from_le_bytes(buf) as Xreal / u32::MAX as Xreal;
    xs.push_data(Cell::Real(r))
}

fn core_word_round(xs: &mut State) -> Xresult {
    let x = xs.pop_data()?.to_real()?;
    xs.push_data(Cell::from(x.round()))
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
            Err(Xerr::TypeErrorMsg { .. }) => (),
            other => panic!("result {:?}", other),
        }
        xs.eval("1 1 bit-and").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
        xs.eval("1 2 bit-or").unwrap();
        assert_eq!(Ok(Cell::Int(3)), xs.pop_data());
        xs.eval("1 3 bit-xor").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        xs.eval("0 bit-not").unwrap();
        assert_eq!(Ok(Cell::Int(-1)), xs.pop_data());
        xs.eval("1 3 bit-shl").unwrap();
        assert_eq!(Ok(Cell::Int(8)), xs.pop_data());
        xs.eval("16 3 bit-shr").unwrap();
        assert_eq!(Ok(Cell::Int(2)), xs.pop_data());
        xs.eval("1 negate").unwrap();
        assert_eq!(Ok(Cell::Int(-1)), xs.pop_data());
        xs.eval("-1 negate").unwrap();
        assert_eq!(Ok(Cell::Int(1)), xs.pop_data());
    }

    #[test]
    fn test_logical_ops() {
        let mut xs = State::boot().unwrap();
        assert_eq!(OK, xs.eval("true false and"));
        assert_eq!(Ok(FALSE), xs.pop_data());
        assert_eq!(OK, xs.eval("true true and"));
        assert_eq!(Ok(TRUE), xs.pop_data());
        assert_eq!(OK, xs.eval("true false or"));
        assert_eq!(Ok(TRUE), xs.pop_data());
        assert_eq!(OK, xs.eval("false false or"));
        assert_eq!(Ok(FALSE), xs.pop_data());
        assert_eq!(OK, xs.eval("true true xor"));
        assert_eq!(Ok(FALSE), xs.pop_data());
        assert_eq!(OK, xs.eval("true false xor"));
        assert_eq!(Ok(TRUE), xs.pop_data());
        assert_eq!(OK, xs.eval("true not"));
        assert_eq!(Ok(FALSE), xs.pop_data());
        assert_eq!(OK, xs.eval("false not"));
        assert_eq!(Ok(TRUE), xs.pop_data());
        assert_ne!(OK, xs.eval("1 not"));
        assert_ne!(OK, xs.eval("1 1 and"));
    }

    #[test]
    fn test_into_real() {
        let mut xs = State::boot().unwrap();
        assert_eq!(OK, xs.eval("1 >real 1.0 assert-eq"));
        assert_eq!(OK, xs.eval("1.0 >real 1.0 assert-eq"));
        assert_ne!(OK, xs.eval("\"1\" >real 1.0 assert-eq"));
    }

    #[test]
    fn test_into_int() {
        let mut xs = State::boot().unwrap();
        assert_eq!(OK, xs.eval("1.4 >int 1 assert-eq"));
        assert_eq!(OK, xs.eval("1.6 >int 1 assert-eq"));
        assert_eq!(OK, xs.eval("1 >int 1 assert-eq"));
        assert_ne!(OK, xs.eval("\"1\" >int 1 assert-eq"));
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
        xs.eval("-1.0 0.0 min").unwrap();
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
        let i = xs.pop_data().unwrap().to_real().unwrap();
        assert!(0.0 <= i && i <= 1.0);
        assert_ne!(OK, xs.eval("1 round"));
        assert_ne!(OK, xs.eval("[ ] round"));
    }

    #[test]
    fn test_div_by_zero() {
        let mut xs = State::boot().unwrap();
        assert_eq!(Err(Xerr::DivisionByZero), xs.eval("1 0 /"));
        assert_eq!(Err(Xerr::DivisionByZero), xs.eval("1.0 0.0 /"));
        assert_eq!(OK, xs.eval("1.0 0.00000001 /"));
    }
    #[test]
    fn test_neg() {
        let mut xs = State::boot().unwrap();
        assert_eq!(OK, xs.eval(&format!("{} negate", Xint::MAX)));
        assert_ne!(OK, xs.eval(&format!("{} negate", Xint::MIN)));
        assert_eq!(
            OK,
            xs.eval(&format!("{}. negate", Xreal::to_string(&Xreal::MAX)))
        );
        assert_eq!(
            OK,
            xs.eval(&format!("{}. negate", Xreal::to_string(&Xreal::MIN)))
        );
    }

    #[test]
    fn test_zero() {
        let mut xs = State::boot().unwrap();
        assert_eq!(OK, xs.eval("0 zero?"));
        assert_eq!(Ok(TRUE), xs.pop_data());
        assert_eq!(OK, xs.eval("0.0 zero?"));
        assert_eq!(Ok(TRUE), xs.pop_data());
        assert_eq!(OK, xs.eval("-0.0 zero?"));
        assert_eq!(Ok(TRUE), xs.pop_data());
        assert_eq!(OK, xs.eval("1.0 zero?"));
        assert_eq!(Ok(FALSE), xs.pop_data());
        assert_eq!(OK, xs.eval("-1.0 zero?"));
        assert_eq!(Ok(FALSE), xs.pop_data());
        assert_ne!(OK, xs.eval("false zero?"));
    }

    #[test]
    fn test_positive() {
        let mut xs = State::boot().unwrap();
        assert_eq!(OK, xs.eval("0 positive?"));
        assert_eq!(Ok(FALSE), xs.pop_data());
        assert_eq!(OK, xs.eval("0.0 positive?"));
        assert_eq!(Ok(FALSE), xs.pop_data());
        assert_eq!(OK, xs.eval("-0.0 positive?"));
        assert_eq!(Ok(FALSE), xs.pop_data());
        assert_eq!(OK, xs.eval("1.0 positive?"));
        assert_eq!(Ok(TRUE), xs.pop_data());
        assert_eq!(OK, xs.eval("1 positive?"));
        assert_eq!(Ok(TRUE), xs.pop_data());
        assert_eq!(OK, xs.eval("-0.001 positive?"));
        assert_eq!(Ok(FALSE), xs.pop_data());
        assert_eq!(OK, xs.eval("0.001 positive?"));
        assert_eq!(Ok(TRUE), xs.pop_data());
        assert_ne!(OK, xs.eval("true positive?"));
        assert_ne!(OK, xs.eval("false positive?"));
    }

    #[test]
    fn test_negative() {
        let mut xs = State::boot().unwrap();
        assert_eq!(OK, xs.eval("0 negative?"));
        assert_eq!(Ok(FALSE), xs.pop_data());
        assert_eq!(OK, xs.eval("0.0 negative?"));
        assert_eq!(Ok(FALSE), xs.pop_data());
        assert_eq!(OK, xs.eval("-0.0 negative?"));
        assert_eq!(Ok(FALSE), xs.pop_data());
        assert_eq!(OK, xs.eval("1.0 negative?"));
        assert_eq!(Ok(FALSE), xs.pop_data());
        assert_eq!(OK, xs.eval("1 negative?"));
        assert_eq!(Ok(FALSE), xs.pop_data());
        assert_eq!(OK, xs.eval("-0.001 negative?"));
        assert_eq!(Ok(TRUE), xs.pop_data());
        assert_eq!(OK, xs.eval("0.001 negative?"));
        assert_eq!(Ok(FALSE), xs.pop_data());
        assert_ne!(OK, xs.eval("true negative?"));
        assert_ne!(OK, xs.eval("false negative?"));
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
