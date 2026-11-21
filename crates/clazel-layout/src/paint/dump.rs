//! A display list as text: the format of the golden paint dumps
//! (`tests/golden_paint.rs`) and of the unit tests.
//!
//! One line per item, in paint order, in device pixels: `fill x,y wxh
//! #aarrggbb`, `text x,y wxh #aarrggbb face=f size=s glyphs=n first=x,y`
//! (the bounds, then the first glyph's position in 1/64 device px),
//! `image x,y wxh id=i src=x,y wxh linear|nearest`, `push-clip x,y wxh`,
//! `pop-clip`; then one line per hit region: `hit
//! x,y wxh node=n url`.

use std::fmt::Write as _;

use super::state::{DeviceRect, DisplayList, Item};

fn rect(r: &DeviceRect) -> String {
    format!("{},{} {}x{}", r.x, r.y, r.width, r.height)
}

/// `list` printed.
pub fn dump(list: &DisplayList) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "scale {}", list.scale);
    for item in &list.items {
        let _ = match item {
            Item::Fill { rect: r, colour } => writeln!(out, "fill {} #{colour:08x}", rect(r)),
            Item::Text { bounds, run } => {
                let first = run
                    .glyphs
                    .first()
                    .map_or(String::new(), |g| format!(" first={},{}", g.x, g.y));
                writeln!(
                    out,
                    "text {} #{:08x} face={} size={} glyphs={}{first}",
                    rect(bounds),
                    run.colour,
                    run.face,
                    run.size,
                    run.glyphs.len()
                )
            }
            Item::Image {
                rect: r,
                image,
                src,
                linear,
            } => writeln!(
                out,
                "image {} id={image} src={},{} {}x{} {}",
                rect(r),
                src[0],
                src[1],
                src[2],
                src[3],
                if *linear { "linear" } else { "nearest" }
            ),
            Item::PushClip { rect: r } => writeln!(out, "push-clip {}", rect(r)),
            Item::PopClip => writeln!(out, "pop-clip"),
        };
    }
    for h in &list.hits {
        let _ = writeln!(
            out,
            "hit {} node={} {}",
            rect(&h.rect),
            h.node,
            h.url.as_deref().unwrap_or("(failure)")
        );
    }
    out
}
