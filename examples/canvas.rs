extern crate minifb;
extern crate xeh;
use minifb::{Key, Window, WindowOptions, Scale};

use xeh::cell::Cell;
use xeh::error::*;
use xeh::state::*;

struct MiniFb {
    width: usize,
    height: usize,
    buffer: Vec<u32>,
    window: Window,
    last_frame_time: std::time::Instant,
}

impl MiniFb {
    fn new(width: usize, height: usize, scale: Scale) -> Self {
        let buffer = vec![0; width * height];
        let mut opts = WindowOptions::default();
        opts.scale = scale;
        let mut window = Window::new(
            "Test - ESC to exit",
            width,
            height,
            opts,
        )
        .unwrap_or_else(|e| {
            panic!("{}", e);
        });
        window.limit_update_rate(Some(std::time::Duration::from_millis(16)));
        MiniFb {
            width,
            height,
            window,
            buffer,
            last_frame_time: std::time::Instant::now(),
        }
    }
}

fn minifb_new(xs: &mut State) -> Xresult {
    let height = xs.pop_data()?.into_usize()?;
    let width = xs.pop_data()?.into_usize()?;
    let scale = match xs.get_var_by_name("minifb-default-scale") {
        Ok(Cell::Int(2)) => Scale::X2,
        Ok(Cell::Int(4)) => Scale::X4,
        Ok(Cell::Int(8)) => Scale::X8,
        Ok(Cell::Int(16)) => Scale::X16,
        Ok(Cell::Int(32)) => Scale::X32,
        _ => Scale::X1,
    };
    let fb = MiniFb::new(width, height, scale);
    xs.push_data(Cell::from_any(fb))
}

fn minifb_update(xs: &mut State) -> Xresult {
    let p = xs.pop_data()?.into_any()?;
    let mut p = p.try_borrow_mut().map_err(|_| Xerr::TypeError)?;
    let fb = p.downcast_mut::<MiniFb>().ok_or(Xerr::TypeError)?;
    let buf = &fb.buffer[..];
    let w = fb.width;
    let h = fb.height;
    fb.window.update_with_buffer(&buf, w, h).unwrap();
    let t = std::time::Instant::now();
    println!("{:?}", t - fb.last_frame_time);
    fb.last_frame_time = t;
    OK
}

fn minifb_put_pixel(xs: &mut State) -> Xresult {
    let p = xs.pop_data()?.into_any()?;
    let mut p = p.try_borrow_mut().map_err(|_| Xerr::TypeError)?;
    let fb = p.downcast_mut::<MiniFb>().ok_or(Xerr::TypeError)?;
    let color = xs.pop_data()?.into_int()?;
    let y = xs.pop_data()?.into_usize()?;
    let x = xs.pop_data()?.into_usize()?;
    if let Some(p) = fb.buffer.get_mut(y * fb.width + x) {
        *p = color as u32;
        OK
    } else {
        Err(Xerr::OutOfBounds)
    }
}

fn minifb_is_open(xs: &mut State) -> Xresult {
    let p = xs.pop_data()?.into_any()?;
    let mut p = p.try_borrow_mut().map_err(|_| Xerr::TypeError)?;
    let fb = p.downcast_mut::<MiniFb>().ok_or(Xerr::TypeError)?;
    let t = fb.window.is_open() && !fb.window.is_key_down(Key::Escape);
    let c = Cell::from(t);
    xs.push_data(c)
}

struct ByteArray(Vec<u8>);

fn bytearray_new(xs: &mut State) -> Xresult {
    let len = xs.pop_data()?.into_usize()?;
    let mut v = Vec::with_capacity(len);
    v.resize_with(len,|| 0);
    xs.push_data(Cell::from_any(ByteArray(v)))
}

fn bytearray_get(xs: &mut State) -> Xresult {
    let p = xs.pop_data()?.into_any()?;
    let mut p = p.try_borrow_mut().map_err(|_| Xerr::TypeError)?;
    let ba = p.downcast_mut::<ByteArray>().ok_or(Xerr::TypeError)?;
    let idx = xs.pop_data()?.into_usize()?;
    let val = ba.0.get(idx).ok_or(Xerr::OutOfBounds)?;
    xs.push_data(Cell::from(*val as usize))
}

fn bytearray_set(xs: &mut State) -> Xresult {
    let p = xs.pop_data()?.into_any()?;
    let mut p = p.try_borrow_mut().map_err(|_| Xerr::TypeError)?;
    let ba = p.downcast_mut::<ByteArray>().ok_or(Xerr::TypeError)?;
    let idx = xs.pop_data()?.into_usize()?;
    let val = xs.pop_data()?.into_usize()? as u8;
    let x = ba.0.get_mut(idx).ok_or(Xerr::OutOfBounds)?;
    *x = val;
    OK
}

fn bytearray_from(xs: &mut State) -> Xresult {
    match xs.pop_data()? {
        Cell::Vector(v) => {
            let mut tmp = Vec::with_capacity(v.len());
            for x in v.iter() {
                match x {
                    &Cell::Int(val) if 0 <= val && val <= 255 =>
                        tmp.push(val as u8),
                    _ => return Err(Xerr::OutOfRange),
                }
            }
            xs.push_data(Cell::from_any(ByteArray(tmp)))
        }
        _ => Err(Xerr::TypeError),
    }
}

fn main() -> Xresult {
    let mut xs = State::new().unwrap();

    xs.defword(">bytearray", bytearray_from).unwrap();
    xs.defword("bytearray_new", bytearray_new).unwrap();
    xs.defword("bytearray_get", bytearray_get).unwrap();
    xs.defword("bytearray_set", bytearray_set).unwrap();

    xs.defword("minifb_new", minifb_new).unwrap();
    xs.defword("minifb_is_open", minifb_is_open).unwrap();
    xs.defword("minifb_update", minifb_update).unwrap();
    xs.defword("minifb_put_pixel", minifb_put_pixel).unwrap();
    xs.defvar("minifb-default-scale", Cell::Int(1)).unwrap();

    let args = xeh::repl::parse_args()?;
    xeh::repl::run_with_args(&mut xs, args)
}
