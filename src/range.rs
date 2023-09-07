use crate::prelude::*;
use crate::state::*;
use std::ops::Range;

const START_LIT: Cell = xeh_str_lit!("start");

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
    xs.defword("^start", set_start)?;
    OK
}

fn set_start(xs: &mut State) -> Xresult {
    let start = xs.pop_data()?.to_isize()?;
    let limit = xs.pop_data()?;
    let _ = limit.to_isize()?;
    let range = limit.insert_tag(START_LIT, Cell::from(start));
    xs.push_data(range)
}

pub(crate) fn parse_do_to(range: Cell) -> Xresult1<DoToRange> {
    let limit = range.to_isize()?;
    let mut start = None;
    if let Some(n) = range.lookup_tag(&START_LIT) {
        start = Some(n.to_isize()?);
    }
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
        Cell::from(limit).insert_tag(START_LIT, Cell::from(start))
    }

    #[test]
    fn test_range_doto() {
        let res = Vec::from_iter(parse_do_to(make_range(3, 0)).unwrap().range());
        assert_eq!(res, vec![0, 1, 2]);
        let res = Vec::from_iter(parse_do_to(Cell::from(3isize)).unwrap().range());
        assert_eq!(res, vec![0, 1, 2]);
        let res = Vec::from_iter(parse_do_to(make_range(3, -1)).unwrap().range());
        assert_eq!(res, vec![-1, 0, 1, 2]);
        // empty range
        let res = Vec::from_iter(parse_do_to(Cell::from(-2isize)).unwrap().range());
        assert_eq!(res, vec![]);
        let res = Vec::from_iter(parse_do_to(Cell::from(0isize)).unwrap().range());
        assert_eq!(res, vec![]);
        let res = Vec::from_iter(parse_do_to(make_range(-3, 0)).unwrap().range());
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
