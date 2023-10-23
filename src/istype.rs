use crate::prelude::*;
use crate::state::*;
use crate::cell::*;

pub fn load(xs: &mut State) -> Xresult {
    xs.defword("nil?", is_nil_xf)?;
    xs.defword("bool?", is_bool_xf)?;
    xs.defword("int?", is_int_xf)?;
    xs.defword("real?", is_real_xf)?;
    xs.defword("str?", is_str_xf)?;
    xs.defword("bitstr?", is_bitstr_xf)?;
    xs.defword("vec?", is_vec_xf)?;
    OK
}

fn is_nil_xf(xs: &mut State) -> Xresult {
    let yes = xs.pop_data()?.value() == &NIL;
    xs.push_data(Cell::from(yes))
}

fn is_bool_xf(xs: &mut State) -> Xresult {
    let yes = xs.pop_data()?.to_bool().is_ok();
    xs.push_data(Cell::from(yes))
}

fn is_int_xf(xs: &mut State) -> Xresult {
    let yes = xs.pop_data()?.to_xint().is_ok();
    xs.push_data(Cell::from(yes))
}

fn is_real_xf(xs: &mut State) -> Xresult {
    let yes = xs.pop_data()?.to_real().is_ok();
    xs.push_data(Cell::from(yes))
}

fn is_str_xf(xs: &mut State) -> Xresult {
    let yes = xs.pop_data()?.str().is_ok();
    xs.push_data(Cell::from(yes))
}

fn is_bitstr_xf(xs: &mut State) -> Xresult {
    let yes = xs.pop_data()?.bitstr().is_ok();
    xs.push_data(Cell::from(yes))
}

fn is_vec_xf(xs: &mut State) -> Xresult {
    let yes = xs.pop_data()?.vec().is_ok();
    xs.push_data(Cell::from(yes))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_typecheck() {
        let mut xs = State::boot().unwrap();
        xs.eval("
        nil nil? assert
        1 nil? not assert
        1 int? assert
        1.0 int? not assert
        2.0 real? assert
        2 real? not assert
        \"ee\" str? assert
        |ff| str? not assert
        |ff| bitstr? assert
        \"ee\" bitstr? not assert
        [ ] vec? assert
        | | vec? not assert
        true bool? assert
        false bool? assert
        nil bool? not assert
        ").unwrap()
    }
}
