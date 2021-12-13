use crate::prelude::*;

#[derive(Default)]
struct D2Context {
    data: Vec<u32>,
    pal: Option<Vec<u32>>,
    color: u32,
    width: usize,
    height: usize,
}

fn resize(xs: &mut Xstate) -> Xresult {
    let any = xs.pop_data()?.into_any()?;
    let mut p = any.try_borrow_mut().map_err(|_| Xerr::TypeError)?;
    let d2 = p.downcast_mut::<D2Context>().ok_or(Xerr::TypeError)?;
    let h = xs.pop_data()?.to_usize()?;
    let w = xs.pop_data()?.to_usize()?;
    let n = w * h;
    d2.width = w;
    d2.height = h;
    d2.data.resize(n, 0);
    OK
}

fn color_set(xs: &mut Xstate) -> Xresult {
    let any = xs.pop_data()?.into_any()?;
    let mut p = any.try_borrow_mut().map_err(|_| Xerr::TypeError)?;
    let d2 = p.downcast_mut::<D2Context>().ok_or(Xerr::TypeError)?;
    let color = xs.pop_data()?.to_usize()?;
    d2.color = color as u32;
    OK
}

fn width_get(xs: &mut Xstate) -> Xresult {
    let any = xs.pop_data()?.into_any()?;
    let mut p = any.try_borrow_mut().map_err(|_| Xerr::TypeError)?;
    let d2 = p.downcast_mut::<D2Context>().ok_or(Xerr::TypeError)?;
    xs.push_data(Xcell::from(d2.width))
}

fn height_get(xs: &mut Xstate) -> Xresult {
    let any = xs.pop_data()?.into_any()?;
    let mut p = any.try_borrow_mut().map_err(|_| Xerr::TypeError)?;
    let d2 = p.downcast_mut::<D2Context>().ok_or(Xerr::TypeError)?;
    xs.push_data(Xcell::from(d2.height))
}

fn palette_set(xs: &mut Xstate) -> Xresult {
    let any = xs.pop_data()?.into_any()?;
    let mut p = any.try_borrow_mut().map_err(|_| Xerr::TypeError)?;
    let d2 = p.downcast_mut::<D2Context>().ok_or(Xerr::TypeError)?;
    let newpal = xs.pop_data()?.to_vector()?;
    let mut pal = d2.pal.take().unwrap_or_else(|| Vec::with_capacity(newpal.len()));
    pal.reserve(newpal.len());
    pal.extend(newpal.iter().map(|c|
        match c {
            Cell::Int(x) => *x as u32,
            _ => 0,
        }
    ));
    d2.pal = Some(pal);
    OK
}

fn data_set(xs: &mut Xstate) -> Xresult {
    let any = xs.pop_data()?.into_any()?;
    let mut p = any.try_borrow_mut().map_err(|_| Xerr::TypeError)?;
    let d2 = p.downcast_mut::<D2Context>().ok_or(Xerr::TypeError)?;
    let y = xs.pop_data()?.to_usize()?;
    let x = xs.pop_data()?.to_usize()?;
    let index = y * d2.width + x;
    let color = if let Some(pal) = &d2.pal {
        *pal.get(d2.color as usize).ok_or(Xerr::OutOfBounds)?
    } else {
        d2.color
    };
    let p = d2.data.get_mut(index).ok_or(Xerr::OutOfBounds)?;
    *p = color;
    OK
}

fn data_get(xs: &mut Xstate) -> Xresult {
    let any = xs.pop_data()?.into_any()?;
    let mut p = any.try_borrow_mut().map_err(|_| Xerr::TypeError)?;
    let d2 = p.downcast_mut::<D2Context>().ok_or(Xerr::TypeError)?;
    let y = xs.pop_data()?.to_usize()?;
    let x = xs.pop_data()?.to_usize()?;
    let index = y * d2.width + x;
    if let Some(p) = d2.data.get(index) {
        xs.push_data(Xcell::from(*p))
    } else {
        xs.push_data(NIL)
    }
}

pub fn load(xs: &mut Xstate) -> Xresult1<Xcell> {
    let d2 = Xcell::from_any(D2Context::default());
    xs.defwordself("d2-resize", resize, d2.clone())?;
    xs.defwordself("d2-width", width_get, d2.clone())?;
    xs.defwordself("d2-height", height_get, d2.clone())?;
    xs.defwordself("d2-palette!", palette_set, d2.clone())?;
    xs.defwordself("d2-color!", color_set, d2.clone())?;
    xs.defwordself("d2-data!", data_set, d2.clone())?;
    xs.defwordself("d2-data", data_get, d2.clone())?;
    xs.defwordself("d2-capture-rgba", buffer_u8_get, d2.clone())?;
    Ok(d2)
}

fn buffer_u8_get(xs: &mut Xstate) -> Xresult {
    let ctx = xs.pop_data()?;
    let mut buf = Vec::new();
    copy_rgba_data(ctx, &mut buf)?;
    let mut v = Xvec::new();
    v.extend(buf.iter().map(|x| Xcell::from(*x)));
    xs.push_data(Xcell::Bitstr(Xbitstr::from(buf)))
}

pub fn copy_rgba_data(d2ctx: Xcell, buf: &mut Vec<u8>) -> Xresult1<(usize, usize)> {
    let any = d2ctx.into_any()?;
    let mut p = any.try_borrow_mut().map_err(|_| Xerr::TypeError)?;
    let d2 = p.downcast_mut::<D2Context>().ok_or(Xerr::TypeError)?;
    buf.clear();
    buf.reserve(d2.data.len() * 4);
    for c in d2.data.iter() {
        let c = *c;
        buf.push((c >> 24) as u8);
        buf.push((c >> 16) as u8);
        buf.push((c >> 8) as u8);
        buf.push(c as u8);
    }
    Ok((d2.width, d2.height))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_d2_rgba() {
        let mut xs = Xstate::boot().unwrap();
        self::load(&mut xs).unwrap();
        xs.interpret("
        3 var W
        2 var H
        W H d2-resize
        H for
            W for 
                J W * I + d2-color!
                I J d2-data!
            loop
        loop
        d2-capture-rgba
        ").unwrap();
        let mut bs = xs.pop_data().unwrap().to_bitstring().unwrap();
        assert_eq!(3 * 2 * 32, bs.len());
        for y in 0..2 {
            for x in 0..3 {
                let c = bs.read(32).unwrap().to_bytes();
                assert_eq!(c[3], y * 3 + x);
            }
        }
    }
}