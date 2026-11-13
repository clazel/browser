//! The address bar strip (phase-5.md item 5.23): drawn by the host, outside the
//! sandbox, from the kernel's URL or the user's typing, never from a byte the page
//! chose. Text goes through `clazel-font` (the face), `clazel-layout`'s shaping
//! and `clazel-glyph-mask`'s masks, blended here; the host has no GPU.
//!
//! # Modelling choices
//!
//! - **The font is a system TrueType face** (5.0(c): TrueType only): the first of
//!   [`FONT_PATHS`] that parses. None found: the strip is drawn without text and
//!   the host says so once on stderr. Nothing is bundled yet.
//! - **Geometry, in points times the backing scale**: the strip is
//!   [`STRIP_POINTS`] tall. At its left is the back button ([`back_button`]): a
//!   square 8 points from the left edge and inset by 6 points above and below.
//!   The field starts 6 points after it and is inset by 6 points, text at 13
//!   points, 8 points from the field's left, its baseline 4.5 points below the
//!   field's middle. Colours are fixed greys; the field's border is blue while
//!   editing.
//! - **The back button is drawn by the host, without the font**: a chevron of
//!   filled rows, dark when the host's list of committed URLs has somewhere to go
//!   back to and pale when it has not. Nothing of the page is in it.
//! - **Blending** is coverage over the background, per channel,
//!   `(fg·c + bg·(255 − c)) / 255` rounded down, the text black (the URL before
//!   the first `Paint` is grey: it is what was asked for, not yet committed).
//! - **Long text is cut at the field**: from its start when shown, and from its end
//!   while editing so the caret stays in view.
//! - **Glyph positions** are whole pixels plus a quarter-pixel offset in x (the
//!   masks' `Offset`), y on the baseline.

use clazel_font::Face;
use clazel_glyph_mask::{Offset, Quarter, glyph_mask};
use clazel_layout::shape::{Script, Shaper};

/// The strip's height in points.
pub const STRIP_POINTS: f64 = 36.0;

/// Where a TrueType face is looked for, in order.
pub const FONT_PATHS: &[&str] = &[
    "/System/Library/Fonts/Supplemental/Arial.ttf",
    "/System/Library/Fonts/Geneva.ttf",
    "/Library/Fonts/Arial Unicode.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    "C:\\Windows\\Fonts\\arial.ttf",
];

/// The first face of [`FONT_PATHS`] that reads and parses.
pub fn system_font() -> Option<Vec<u8>> {
    FONT_PATHS.iter().find_map(|p| {
        let bytes = std::fs::read(p).ok()?;
        Face::parse(&bytes, 0).ok()?;
        Some(bytes)
    })
}

pub(crate) const BACKGROUND: u32 = 0x00EC_ECEC;
const RULE: u32 = 0x00C8_C8C8;
pub(crate) const FIELD: u32 = 0x00FF_FFFF;
const BORDER: u32 = 0x00B0_B0B0;
const EDITING: u32 = 0x003B_82F6;
const TEXT: u32 = 0x0000_0000;
const PENDING: u32 = 0x0080_8080;
pub(crate) const BACK_ENABLED: u32 = 0x0040_4040;
pub(crate) const BACK_DISABLED: u32 = 0x00B8_B8B8;

/// What the strip shows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Contents<'a> {
    /// The text in the field.
    pub text: &'a str,
    /// The user is typing in the field: blue border, caret after the text.
    pub editing: bool,
    /// The text is the kernel's committed URL (black), not only what was asked
    /// for (grey).
    pub committed: bool,
    /// There is a URL to go back to: the back button is drawn dark.
    pub can_go_back: bool,
}

/// `points` at backing `scale`, in pixels. `as` saturates a float at the
/// integer's ends.
fn pixels(points: f64, scale: f64) -> i64 {
    (points * scale).round() as i64
}

/// The back button's rectangle `(x0, y0, x1, y1)` in a strip `height` pixels
/// tall at backing `scale`: what [`render`] draws and what a click is tested
/// against.
pub fn back_button(height: u32, scale: f64) -> (i64, i64, i64, i64) {
    let (x0, y0) = (pixels(8.0, scale), pixels(6.0, scale));
    let y1 = sub(i64::from(height), y0);
    (x0, y0, add(x0, sub(y1, y0).max(0)), y1)
}

/// Whether the point `(x, y)` of the strip is on the back button.
pub fn on_back_button(x: i64, y: i64, height: u32, scale: f64) -> bool {
    let (x0, y0, x1, y1) = back_button(height, scale);
    x >= x0 && x < x1 && y >= y0 && y < y1
}

/// A `width` by `height` image (pixels, rows from the top, `0x00RRGGBB`).
struct Canvas {
    width: u32,
    height: u32,
    pixels: Vec<u32>,
}

impl Canvas {
    fn at(&mut self, x: i64, y: i64) -> Option<&mut u32> {
        let (x, y) = (u32::try_from(x).ok()?, u32::try_from(y).ok()?);
        if x >= self.width || y >= self.height {
            return None;
        }
        let i = u64::from(y)
            .checked_mul(u64::from(self.width))?
            .checked_add(u64::from(x))?;
        self.pixels.get_mut(usize::try_from(i).ok()?)
    }

    fn fill(&mut self, (x0, y0, x1, y1): (i64, i64, i64, i64), colour: u32) {
        for y in y0..y1 {
            for x in x0..x1 {
                if let Some(p) = self.at(x, y) {
                    *p = colour;
                }
            }
        }
    }
}

/// One channel of `fg` over `bg` at coverage `c`: at most 255 · 255 before the
/// division, so nothing saturates.
fn mix(fg: u32, bg: u32, c: u8, shift: u32) -> u32 {
    let (f, b, c) = ((fg >> shift) & 0xFF, (bg >> shift) & 0xFF, u32::from(c));
    let sum = f
        .saturating_mul(c)
        .saturating_add(b.saturating_mul(u32::from(!u8::try_from(c).unwrap_or(255))));
    (sum / 255) << shift
}

/// `fg` over `bg` at coverage `c`.
pub fn blend(fg: u32, bg: u32, c: u8) -> u32 {
    mix(fg, bg, c, 16) | mix(fg, bg, c, 8) | mix(fg, bg, c, 0)
}

/// `a + b` and `a − b`, saturating: positions here are far from `i64`'s ends.
fn add(a: i64, b: i64) -> i64 {
    a.saturating_add(b)
}

fn sub(a: i64, b: i64) -> i64 {
    a.saturating_sub(b)
}

/// The strip, `width` by `height` pixels at backing `scale`, in `font` if there
/// is one.
pub fn render(
    font: Option<&[u8]>,
    width: u32,
    height: u32,
    scale: f64,
    what: &Contents<'_>,
) -> Vec<u32> {
    let len = u64::from(width).saturating_mul(u64::from(height));
    let mut canvas = Canvas {
        width,
        height,
        pixels: vec![BACKGROUND; usize::try_from(len).unwrap_or(0)],
    };
    let px = |points: f64| pixels(points, scale);
    let one = px(1.0).max(1);
    let (w, h) = (i64::from(width), i64::from(height));
    canvas.fill((0, sub(h, one), w, h), RULE);
    let button = back_button(height, scale);
    chevron(&mut canvas, button, scale, what.can_go_back);
    let field = (
        add(button.2, px(6.0)),
        px(6.0),
        sub(w, px(8.0)),
        sub(h, px(6.0)),
    );
    let border = if what.editing { EDITING } else { BORDER };
    canvas.fill(field, border);
    let inner = (
        add(field.0, one),
        add(field.1, one),
        sub(field.2, one),
        sub(field.3, one),
    );
    canvas.fill(inner, FIELD);
    let colour = if what.committed { TEXT } else { PENDING };
    let left = add(field.0, px(8.0));
    let right = sub(field.2, px(8.0));
    let baseline = add(add(field.1, field.3) / 2, px(4.5));
    let pen = font.and_then(|f| {
        text(
            &mut canvas,
            f,
            what,
            (left, right, baseline),
            scale,
            colour,
            inner,
        )
    });
    if what.editing {
        let x = pen.unwrap_or(left);
        let caret = (x, add(field.1, px(6.0)), add(x, one), sub(field.3, px(6.0)));
        canvas.fill(caret, TEXT);
    }
    canvas.pixels
}

/// The back button's chevron, pointing left, in the middle of `button`: one
/// filled run per row, 5 points above and below the middle, its point 3 points
/// left of the middle and its ends 3 points right of it.
fn chevron(canvas: &mut Canvas, button: (i64, i64, i64, i64), scale: f64, enabled: bool) {
    let colour = if enabled { BACK_ENABLED } else { BACK_DISABLED };
    let (cx, cy) = (add(button.0, button.2) / 2, add(button.1, button.3) / 2);
    let reach = pixels(5.0, scale).max(1);
    let (half, thick) = (pixels(3.0, scale), pixels(2.0, scale).max(1));
    for dy in sub(0, reach)..=reach {
        // `reach` is at least 1, so the division is defined.
        let across = dy
            .saturating_abs()
            .saturating_mul(half.saturating_mul(2))
            .checked_div(reach)
            .unwrap_or(0);
        let x = add(sub(cx, half), across);
        let y = add(cy, dy);
        canvas.fill((x, y, add(x, thick), add(y, 1)), colour);
    }
}

/// Draw `what.text` from `left` on `baseline`, cut at `right` and inside `clip`;
/// where the pen ends.
fn text(
    canvas: &mut Canvas,
    font: &[u8],
    what: &Contents<'_>,
    (left, right, baseline): (i64, i64, i64),
    scale: f64,
    colour: u32,
    clip: (i64, i64, i64, i64),
) -> Option<i64> {
    let face = Face::parse(font, 0).ok()?;
    let size = (13.0 * scale * 64.0).round() as i32;
    let shaper = Shaper::new(face, Script::Latin);
    let run = shaper.shape_at(what.text, size);
    let width = i64::from(run.advance) / 64;
    // Editing shows the end of a long text, so the caret is in view.
    let shift = if what.editing {
        sub(width, sub(right, left)).max(0)
    } else {
        0
    };
    let origin = sub(left, shift);
    for g in &run.glyphs {
        let x26 = i64::from(g.x);
        let gx = add(origin, x26.div_euclid(64));
        let quarter = match x26.rem_euclid(64) / 16 {
            0 => Quarter::Zero,
            1 => Quarter::One,
            2 => Quarter::Two,
            _ => Quarter::Three,
        };
        if gx > right {
            break;
        }
        let path = shaper.face().path(g.glyph, size);
        let offset = Offset {
            x: quarter,
            y: Quarter::Zero,
        };
        let Ok(mask) = glyph_mask(&path, offset) else {
            continue;
        };
        let top = add(sub(baseline, i64::from(g.y) / 64), i64::from(mask.top));
        let mask_left = add(gx, i64::from(mask.left));
        for my in 0..mask.height {
            for mx in 0..mask.width {
                let (x, y) = (add(mask_left, i64::from(mx)), add(top, i64::from(my)));
                if x < clip.0 || x >= clip.2.min(right) || y < clip.1 || y >= clip.3 {
                    continue;
                }
                let c = mask.get(mx, my).unwrap_or(0);
                if let Some(p) = canvas.at(x, y) {
                    *p = blend(colour, *p, c);
                }
            }
        }
    }
    Some(add(origin, width).min(right))
}
