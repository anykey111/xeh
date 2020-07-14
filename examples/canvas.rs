extern crate minifb;
extern crate xeh;
use minifb::{Key, Window, WindowOptions};

use xeh::cell::Cell;
use xeh::error::*;
use xeh::state::*;

struct MiniFb {
    width: usize,
    height: usize,
    buffer: Vec<u32>,
    window: Window,
}

impl MiniFb {
    fn new(width: usize, height: usize) -> Self {
        let buffer = vec![0; width * height];
        let mut window = Window::new(
            "Test - ESC to exit",
            width,
            height,
            WindowOptions::default(),
        )
        .unwrap_or_else(|e| {
            panic!("{}", e);
        });
        window.limit_update_rate(Some(std::time::Duration::from_secs(1)));
        MiniFb {
            width,
            height,
            window,
            buffer,
        }
    }
}

fn minifb_new(xs: &mut State) -> Xresult {
    let height = xs.pop_data()?.into_usize()?;
    let width = xs.pop_data()?.into_usize()?;
    let fb = MiniFb::new(width, height);
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
    OK
}

fn minifb_put_pixel(xs: &mut State) -> Xresult {
    let p = xs.pop_data()?.into_any()?;
    let mut p = p.try_borrow_mut().map_err(|_| Xerr::TypeError)?;
    let fb = p.downcast_mut::<MiniFb>().ok_or(Xerr::TypeError)?;
    let color = xs.pop_data()?.into_int()?;
    let y = xs.pop_data()?.into_usize()?;
    let x = xs.pop_data()?.into_usize()?;
    fb.buffer[y * fb.width + x] = color as u32;
    OK
}

fn minifb_is_open(xs: &mut State) -> Xresult {
    let p = xs.pop_data()?.into_any()?;
    let mut p = p.try_borrow_mut().map_err(|_| Xerr::TypeError)?;
    let fb = p.downcast_mut::<MiniFb>().ok_or(Xerr::TypeError)?;
    let t = fb.window.is_open() && !fb.window.is_key_down(Key::Escape);
    let c = Cell::from(t);
    xs.push_data(c)
}

fn main() {
    let mut xs = State::new().unwrap();
    xs.set_state_recording(true);

    xs.defword("minifb_new", minifb_new).unwrap();
    xs.defword("minifb_is_open", minifb_is_open).unwrap();
    xs.defword("minifb_update", minifb_update).unwrap();
    xs.defword("minifb_put_pixel", minifb_put_pixel).unwrap();

    let file = std::env::args().nth(1).expect("filename");
    xs.load_file(&file).unwrap();
    if let Err(e) = xs.run() {
        xs.println(&format!("error: {:?}", e));
        xs.println(&format!("{}", format_source_location(&xs, xs.ip())));
        xs.println(&format!("{}", format_xstate(&xs).join("\n")));
        xs.builtin_repl();
    }
}
