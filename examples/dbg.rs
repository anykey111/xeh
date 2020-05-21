use font_kit::family_name::FamilyName;
use font_kit::properties::Properties;
use font_kit::source::SystemSource;
use minifb::{MouseMode, Scale, ScaleMode, Window, WindowOptions};
use raqote::{
    DrawOptions, DrawTarget, PathBuilder, Point, SolidSource, Source, StrokeStyle, Transform,
};

use xeh::prelude::*;

fn main() -> Xresult {
    let mut xs = Xstate::new().unwrap();
    let xd_width = xs.defonce("xd-width", Xcell::from(640))?;
    let xd_height = xs.defonce("xd-height", Xcell::from(480))?;
    let xd_text_size = xs.defonce("xd-text-size", Xcell::from(16.0))?;
    let xd_bg_color = xs.defonce("xd-background-color", Xcell::from(0x272822))?;
    let xd_text_color = xs.defonce("xd-text-color", Xcell::from(0xf8f8f2))?;

    //let _ = xs.interpret("203344 -> xd-text-color");

    let mut window = Window::new(
        "XEH Debugger",
        xs.fetch_var(&xd_width)?.try_into()?,
        xs.fetch_var(&xd_height)?.try_into()?,
        WindowOptions {
            ..WindowOptions::default()
        },
    )
    .unwrap();
    let font = SystemSource::new()
        .select_best_match(&[FamilyName::Monospace], &Properties::new())
        .unwrap()
        .load()
        .unwrap();
    window.limit_update_rate(Some(std::time::Duration::from_millis(33)));
    let size = window.get_size();
    let mut dt = DrawTarget::new(size.0 as i32, size.1 as i32);
    let text_stroke = StrokeStyle::default();

    while window.is_open() {
        let width = size.0 as f32;
        let height = size.1 as f32;
        let background_color = solid_color(xs.fetch_var(&xd_bg_color)?.try_into()?);
        let text_color = solid_color(xs.fetch_var(&xd_text_color)?.try_into()?);
        let text_size: f32 = xs.fetch_var(&xd_text_size)?.try_into()?;

        dt.clear(background_color);
        let mut pb = PathBuilder::new();
        pb.move_to(0., height - text_size);
        pb.line_to(width, height - text_size);
        let path = pb.finish();
        dt.stroke(
            &path,
            &Source::Solid(text_color),
            &text_stroke,
            &DrawOptions::new(),
        );

        for (i, _) in xs.code_section().iter().enumerate().take(10) {
            let mut s = xs.code_fmt(i).unwrap();
            dt.draw_text(
                &font,
                text_size,
                s.as_str(),
                Point::new(0., (i + 1) as f32 * text_size),
                &Source::Solid(text_color),
                &DrawOptions::new(),
            );
        }


        //if let Some(pos) = window.get_mouse_pos(MouseMode::Clamp) {}

        window
            .update_with_buffer(dt.get_data(), size.0, size.1)
            .unwrap();
    }
    Ok(())
}

fn solid_color(c: usize) -> SolidSource {
    SolidSource::from_unpremultiplied_argb(0xff, (c >> 16) as u8, (c >> 8) as u8, c as u8)
}
