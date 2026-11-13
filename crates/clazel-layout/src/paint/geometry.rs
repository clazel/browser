//! Device pixels, colours, border strips and clips (phase-5.md item 5.16).
//!
//! Sources: CSS 2.1 §8.5 "Border properties" (the border area's four
//! sides), §11.1 (clipping "to its padding edge"); item 5.17a's display list
//! (`clazel-displaylist`): premultiplied `0xAARRGGBB` colours and clips.
//!
//! Modelling choices: `mod.rs`'s "Device pixels", "Borders are solid" and
//! the clip choice; each step's contract is in `state.rs`.

use super::state::{ClipChange, Clips, DeviceRect};
use crate::flow::fragment::{Rect, Sides};

/// The most device pixels per CSS pixel (`mod.rs`).
pub const MAX_SCALE: u32 = 16;

/// `scale` within `1..=MAX_SCALE`.
pub fn clamp_scale(scale: u32) -> u32 {
    scale.clamp(1, MAX_SCALE)
}

/// `v` (1/64 CSS px) to the nearest device pixel at `scale` device pixels
/// per CSS pixel, half up, saturating at `i32` (`state.rs`'s contract).
pub fn snap(v: i32, scale: u32) -> i32 {
    let s = i64::from(clamp_scale(scale));
    let rounded = i64::from(v)
        .saturating_mul(s)
        .saturating_add(32)
        .div_euclid(64);
    i32::try_from(rounded).unwrap_or(if rounded < 0 { i32::MIN } else { i32::MAX })
}

/// `v` (1/64 CSS px) in 1/64 device px at `scale` (exact, saturating).
pub fn fine(v: i32, scale: u32) -> i32 {
    let p = i64::from(v).saturating_mul(i64::from(clamp_scale(scale)));
    i32::try_from(p).unwrap_or(if p < 0 { i32::MIN } else { i32::MAX })
}

/// `r` in device pixels, each edge snapped on its own (`state.rs`'s
/// contract).
pub fn snap_rect(r: Rect, scale: u32) -> DeviceRect {
    let x0 = snap(r.x, scale);
    let y0 = snap(r.y, scale);
    let x1 = snap(r.right(), scale);
    let y1 = snap(r.bottom(), scale);
    let w = i64::from(x1).saturating_sub(i64::from(x0)).max(0);
    let h = i64::from(y1).saturating_sub(i64::from(y0)).max(0);
    DeviceRect {
        x: x0,
        y: y0,
        width: u32::try_from(w).unwrap_or(u32::MAX),
        height: u32::try_from(h).unwrap_or(u32::MAX),
    }
}

/// `rgba` as item 5.17a's premultiplied `0xAARRGGBB`: each channel times
/// the alpha over 255, rounded half up (`state.rs`'s contract).
pub fn premultiply(rgba: [u8; 4]) -> u32 {
    let [r, g, b, a] = rgba;
    let a32 = u32::from(a);
    let mul = |c: u8| {
        u32::from(c)
            .saturating_mul(a32)
            .saturating_add(127)
            .checked_div(255)
            .unwrap_or(0)
            .min(a32)
    };
    (a32 << 24) | (mul(r) << 16) | (mul(g) << 8) | mul(b)
}

/// Whether `rgba` paints nothing (its alpha is 0).
pub fn transparent(rgba: [u8; 4]) -> bool {
    rgba[3] == 0
}

/// The four border strips of border box `b` with widths `w` (CSS 2.1
/// §8.5), in 1/64 CSS px: top, right, bottom, left. Top and bottom span
/// the whole width; left and right lie between them. Widths are clamped to
/// the box (`state.rs`'s contract).
pub fn border_rects(b: Rect, w: Sides) -> [Rect; 4] {
    let width = b.width.max(0);
    let height = b.height.max(0);
    let top = w.top.clamp(0, height);
    let bottom = w.bottom.clamp(0, height.saturating_sub(top));
    let left = w.left.clamp(0, width);
    let right = w.right.clamp(0, width.saturating_sub(left));
    let middle = height.saturating_sub(top).saturating_sub(bottom);
    let mid_y = b.y.saturating_add(top);
    [
        Rect {
            x: b.x,
            y: b.y,
            width,
            height: top,
        },
        Rect {
            x: b.x.saturating_add(width).saturating_sub(right),
            y: mid_y,
            width: right,
            height: middle,
        },
        Rect {
            x: b.x,
            y: b.y.saturating_add(height).saturating_sub(bottom),
            width,
            height: bottom,
        },
        Rect {
            x: b.x,
            y: mid_y,
            width: left,
            height: middle,
        },
    ]
}

/// The intersection of two device rectangles (empty, at `a`'s corner
/// clamped into `b`, when they do not meet).
pub fn intersect(a: DeviceRect, b: DeviceRect) -> DeviceRect {
    let x0 = i64::from(a.x).max(i64::from(b.x));
    let y0 = i64::from(a.y).max(i64::from(b.y));
    let x1 = a.right().min(b.right()).max(x0);
    let y1 = a.bottom().min(b.bottom()).max(y0);
    DeviceRect {
        x: i32::try_from(x0).unwrap_or(a.x),
        y: i32::try_from(y0).unwrap_or(a.y),
        width: u32::try_from(x1.saturating_sub(x0)).unwrap_or(0),
        height: u32::try_from(y1.saturating_sub(y0)).unwrap_or(0),
    }
}

impl Clips {
    /// A box's clip `rect` starts (`state.rs`'s contract).
    pub fn enter(self, rect: DeviceRect) -> (Clips, ClipChange) {
        let current = match self.current {
            Some(c) => intersect(c, rect),
            None => rect,
        };
        (
            Clips {
                depth: self.depth.saturating_add(1),
                current: Some(current),
            },
            ClipChange {
                pop: self.current.is_some(),
                push: Some(current),
            },
        )
    }

    /// The latest clip ends; `outer` is the clip that was in force before
    /// it (`state.rs`'s contract).
    pub fn leave(self, outer: Option<DeviceRect>) -> (Clips, ClipChange) {
        let depth = self.depth.saturating_sub(1);
        let current = if depth == 0 {
            None
        } else {
            outer.or(self.current)
        };
        (
            Clips { depth, current },
            ClipChange {
                pop: self.current.is_some(),
                push: current,
            },
        )
    }
}
