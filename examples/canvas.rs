extern crate minifb;
extern crate xeh;
use minifb::{Key, Window, WindowOptions};
use std::any::Any;
use xeh::vm::State;
use xeh::cell::{Cell};
use xeh::error::*;

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
            width, height,window,buffer,
        }
    }
}

fn minifb_new(vm: &mut State) -> Xresult {
    let height = vm.pop_data()?.to_usize()?;
    let width = vm.pop_data()?.to_usize()?;
    let fb = MiniFb::new(width, height);
    vm.push_data(Cell::from_any(fb))
}

fn minifb_update(vm: &mut State) -> Xresult {
    let p = vm.pop_data()?.to_any()?;
    let mut p = p.try_borrow_mut().map_err(|_| Xerr::TypeError)?;
    let fb = p.downcast_mut::<MiniFb>().ok_or(Xerr::TypeError)?;
    let buf = &fb.buffer[..];
    let w = fb.width;
    let h = fb.height;
    fb.window.update_with_buffer(&buf, w, h).unwrap();
    OK
}

fn minifb_is_open(vm: &mut State) -> Xresult {
    let p = vm.pop_data()?.to_any()?;
    let mut p = p.try_borrow_mut().map_err(|_| Xerr::TypeError)?;
    let fb = p.downcast_mut::<MiniFb>().ok_or(Xerr::TypeError)?;
    let t = fb.window.is_open() && !fb.window.is_key_down(Key::Escape);
    let c = Cell::Int(if t {1} else {0});
    vm.push_data(c)
}

fn main() {
    let mut vm = State::boot().unwrap();
    
    vm.defword("minifb-new", minifb_new).unwrap();
    vm.defword("minifb-is-open", minifb_is_open).unwrap();
    vm.defword("minifb-update", minifb_update).unwrap();
    
    vm.interpret("
    var fb
    320 200 minifb-new -> fb

    begin fb minifb-is-open while
       fb minifb-update
    repeat
    ").unwrap();
}
