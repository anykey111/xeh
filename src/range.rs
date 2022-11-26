use crate::prelude::*;
use crate::state::*;
use std::ops::Range;

pub struct DoToRange {
    pub limit: isize,
    pub start: Option<isize>,
}

impl DoToRange {
    pub fn range(&self) -> Range<isize> {
        if let Some(start) = self.start {
            start..self.limit
        } else {
            0..self.limit
        }
    }
}

pub(crate) fn load(xs: &mut State) -> Xresult {
    xs.defword("range", range_xf)?;
    xs.defword("range-from", range_from_xf)?;
    OK
}

fn range_xf(xs: &mut State) -> Xresult {
    let start = xs.pop_data()?.to_isize()?;
    let limit = xs.pop_data()?.to_isize()?;
    let doto = Cell::from(limit).with_tag(Cell::from(start));
    xs.push_data(doto)
}

fn range_from_xf(xs: &mut State) -> Xresult {
    let start = xs.pop_data()?.to_isize()?;
    let doto = Cell::from(isize::MAX).with_tag(Cell::from(start));
    xs.push_data(doto)
}

pub(crate) fn parse_do_to(val: &Cell) -> Xresult1<DoToRange> {
    let limit = val.to_isize()?;
    let start = val.tag().and_then(|x| x.to_isize().ok());
    Ok(DoToRange {
        limit,
        start
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::iter::FromIterator;

    fn make_range(limit: isize, start: isize) -> Cell {
        Cell::from(limit).with_tag(Cell::from(start))
    }

    #[test]
    fn test_range_doto() {
        let res = Vec::from_iter(parse_do_to(&make_range(3, 0)).unwrap().range());
        assert_eq!(res, vec![0, 1, 2]);
        let res = Vec::from_iter(parse_do_to(&Cell::from(3isize)).unwrap().range());
        assert_eq!(res, vec![0, 1, 2]);
        let res = Vec::from_iter(parse_do_to(&make_range(3, -1)).unwrap().range());
        assert_eq!(res, vec![-1, 0, 1, 2]);
        // empty range
        let res = Vec::from_iter(parse_do_to(&Cell::from(-2isize)).unwrap().range());
        assert_eq!(res, vec![]);
        let res = Vec::from_iter(parse_do_to(&Cell::from(0isize)).unwrap().range());
        assert_eq!(res, vec![]);
        let res = Vec::from_iter(parse_do_to(&make_range(-3, 0)).unwrap().range());
        assert_eq!(res, vec![]);
    }

    #[test]
    fn test_range() {
        let mut xs = State::boot().unwrap();
        xs.eval("3 0 range").unwrap();
        assert_eq!(xs.pop_data(), Ok(make_range(3, 0)));
        xs.eval("3 range-from").unwrap();
        assert_eq!(xs.pop_data(), Ok(make_range(isize::MAX, 3)));
    }

}
