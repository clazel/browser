//! Glyph masks (phase-5.md item 5.17): a glyph outline to an 8-bit coverage
//! mask, on the CPU, in the renderer.
//!
//! The GPU draws rectangles and textured quads; glyph shapes become coverage
//! masks here, so font bytes never reach the GPU process, only masks
//! (decision 5.0(d) as the plan now stands: the GPU rasterizes, glyph masks
//! are still made on the CPU in the renderer). No surface and no blending:
//! the output is coverage only.
//!
//! # Sources
//!
//! There is no standard for rasterizing; the plan's Crates table lists this
//! crate's standard as "none (ours)". What fixes the input's meaning:
//!
//! - OpenType 1.9, chapter `glyf`
//!   (<https://learn.microsoft.com/en-us/typography/opentype/otspec190/glyf>),
//!   "Simple Glyph Description": closed contours of on-curve and off-curve
//!   points, each off-curve point a quadratic Bézier control point, filled
//!   by the non-zero winding rule (the chapter's overlap discussion; Apple's
//!   TrueType Reference Manual, chapter 1, names the rule).
//! - The method is the signed-area accumulation of `font-rs` (Raph Levien,
//!   "Inside the fastest font renderer in the world", 2016) and of
//!   stb_truetype's second rasterizer (`stbtt__rasterize_sorted_edges`,
//!   version 2). No code is taken from either; [`accumulate`] derives it.
//!
//! # Modelling choices
//!
//! Each is listed in the plan as "a listed choice" or decided from it:
//!
//! - **Input**: [`clazel_font::outline::Path`], item 5.10's type: points in
//!   26.6 fixed point (`i32`, 1/64 px), y up, with on-curve flags and
//!   contour ends. Any value of the type is accepted, well formed or not
//!   ([`segments`] says how a malformed contour reads).
//! - **Quarter-pixel offset**: the glyph is drawn at an offset of 0, ¼, ½
//!   or ¾ px in x and in y ([`Offset`]), so a shaper's subpixel pen
//!   positions need four masks per axis, not one per position.
//! - **Béziers flattened within a quarter pixel** ([`flatten`]): uniform
//!   subdivision with the least piece count whose error bound is at most
//!   15/64 px, the points rounded to 2⁻¹⁴ px.
//! - **Exact-area coverage per scanline, clamped to [0, 1]**
//!   ([`accumulate`]): the magnitude of the signed area, so either contour
//!   orientation paints. This equals non-zero winding except where contours
//!   overlap with opposite orientation (the plan says so too).
//! - **Fixed point throughout**: no floating point, so the Kani harnesses
//!   cover the arithmetic exactly. Mask units are 2⁻¹⁴ px.
//! - **Mask size**: at most [`MAX_SIDE`] × [`MAX_SIDE`] pixels (1024 × 1024,
//!   enough for a glyph at about 700 px); a larger glyph is
//!   [`Error::TooLarge`] and draws nothing (listed for the hostile pages of
//!   5.26). The mask is the path's control box rounded out to whole pixels.
//! - **Complexity**: at most [`MAX_LINES`] lines after flattening (65,536;
//!   a glyph of the vendored fonts at 72 px has at most a few hundred), else
//!   [`Error::TooComplex`]. This bounds the time per glyph and keeps every
//!   sum far inside `i64`.
//! - **Rounding**: coverage is `round(min(|area|, 1) × 255)`, half up.

pub mod accumulate;
pub mod flatten;
pub mod place;
pub mod segments;

#[cfg(kani)]
mod proofs;

use clazel_font::outline::Path;

pub use accumulate::Point;

/// The largest mask side, in pixels.
pub const MAX_SIDE: u32 = 1024;

/// The most lines a path may flatten to.
pub const MAX_LINES: usize = 65_536;

/// Why a path has no mask.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The mask would be wider or taller than [`MAX_SIDE`].
    TooLarge,
    /// The path flattens to more than [`MAX_LINES`] lines.
    TooComplex,
    /// An arithmetic step or index left its range. Not reachable within the
    /// bounds above (the Kani harnesses and the crate's README); kept so
    /// that every step is checked rather than assumed.
    Overflow,
}

/// A quarter of a pixel.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Quarter {
    /// No offset.
    #[default]
    Zero,
    /// ¼ px.
    One,
    /// ½ px.
    Two,
    /// ¾ px.
    Three,
}

impl Quarter {
    /// The quarter in 26.6 units (0, 16, 32 or 48).
    pub fn units(self) -> i64 {
        match self {
            Quarter::Zero => 0,
            Quarter::One => 16,
            Quarter::Two => 32,
            Quarter::Three => 48,
        }
    }
}

/// Where the glyph is drawn relative to its origin: right by `x` and down by
/// `y` quarters of a pixel (screen directions).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Offset {
    /// Rightwards.
    pub x: Quarter,
    /// Downwards.
    pub y: Quarter,
}

/// An 8-bit coverage mask and where it goes.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Mask {
    /// The mask's left edge, in screen pixels from the glyph origin.
    pub left: i32,
    /// The mask's top edge, in screen pixels from the glyph origin, y down.
    pub top: i32,
    /// Width in pixels, at most [`MAX_SIDE`].
    pub width: u32,
    /// Height in pixels, at most [`MAX_SIDE`].
    pub height: u32,
    /// Coverage, 0 (none) to 255 (full), row after row from the top,
    /// `width` bytes per row.
    pub coverage: Vec<u8>,
}

impl Mask {
    /// The coverage of pixel (`x`, `y`) of the mask, if it is inside.
    pub fn get(&self, x: u32, y: u32) -> Option<u8> {
        if x >= self.width {
            return None;
        }
        let w = usize::try_from(self.width).ok()?;
        let at = usize::try_from(y)
            .ok()?
            .checked_mul(w)?
            .checked_add(usize::try_from(x).ok()?)?;
        self.coverage.get(at).copied()
    }
}

/// A path flattened to lines in its mask.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Lines {
    /// As [`Mask::left`].
    pub left: i32,
    /// As [`Mask::top`].
    pub top: i32,
    /// As [`Mask::width`].
    pub width: u32,
    /// As [`Mask::height`].
    pub height: u32,
    /// The lines, in mask units (2⁻¹⁴ px from the mask's top left corner, y
    /// down), every point inside the mask.
    pub lines: Vec<(Point, Point)>,
}

/// The mask of `path` drawn at `offset`.
pub fn glyph_mask(path: &Path, offset: Offset) -> Result<Mask, Error> {
    accumulate_lines(&flatten_path(path, offset, MAX_SIDE)?)
}

/// `path` at `offset` flattened to lines, in a mask of at most `max_side`
/// pixels a side ([`glyph_mask`] uses [`MAX_SIDE`]; the Kani harnesses use
/// smaller masks).
pub fn flatten_path(path: &Path, offset: Offset, max_side: u32) -> Result<Lines, Error> {
    let placed = place::place(path, offset, max_side)?;
    let mut lines = Vec::new();
    let mut push = |a: Point, b: Point| -> Result<(), Error> {
        if lines.len() >= MAX_LINES {
            return Err(Error::TooComplex);
        }
        lines.push((a, b));
        Ok(())
    };
    let mut start = 0usize;
    for &end in &placed.contour_ends {
        let contour = placed.points.get(start..end).ok_or(Error::Overflow)?;
        segments::for_each_segment(contour, |s| match s {
            segments::Segment::Line(a, b) => push(a, b),
            segments::Segment::Quad(a, c, b) => {
                let n = flatten::pieces(a, c, b)?;
                let mut prev = a;
                for i in 1..=n {
                    let q = flatten::point(a, c, b, n, i)?;
                    push(prev, q)?;
                    prev = q;
                }
                Ok(())
            }
        })?;
        start = end;
    }
    Ok(Lines {
        left: placed.left,
        top: placed.top,
        width: placed.width,
        height: placed.height,
        lines,
    })
}

/// The mask of a flattened path.
pub fn accumulate_lines(lines: &Lines) -> Result<Mask, Error> {
    let mut acc = accumulate::Accumulator::new(lines.width, lines.height)?;
    for &(a, b) in &lines.lines {
        acc.line(a, b)?;
    }
    Ok(Mask {
        left: lines.left,
        top: lines.top,
        width: lines.width,
        height: lines.height,
        coverage: acc.finish()?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use clazel_font::outline::PathPoint;

    fn pt(x: i32, y: i32, on_curve: bool) -> PathPoint {
        PathPoint { x, y, on_curve }
    }

    #[test]
    fn a_box_fills_its_pixels() -> Result<(), Error> {
        // 2 × 2 px, clockwise with y up as TrueType's outer contours are.
        let path = Path {
            points: vec![
                pt(0, 0, true),
                pt(0, 128, true),
                pt(128, 128, true),
                pt(128, 0, true),
            ],
            contour_ends: vec![4],
        };
        let m = glyph_mask(&path, Offset::default())?;
        assert_eq!((m.left, m.top, m.width, m.height), (0, -2, 2, 2));
        assert_eq!(m.coverage, [255; 4]);
        assert_eq!(m.get(1, 1), Some(255));
        assert_eq!(m.get(2, 0), None);
        assert_eq!(m.get(0, 2), None);
        // At ½ px right and ¼ px down: half, full-ish, quarter.
        let off = Offset {
            x: Quarter::Two,
            y: Quarter::One,
        };
        let m = glyph_mask(&path, off)?;
        assert_eq!((m.left, m.top, m.width, m.height), (0, -2, 3, 3));
        assert_eq!(m.coverage, [96, 191, 96, 128, 255, 128, 32, 64, 32]);
        Ok(())
    }

    #[test]
    fn four_arcs_have_their_area() -> Result<(), Error> {
        // On-curve points on the axes at radius 8 px, each quarter a
        // quadratic whose control is the corner (±r, ±r). Each arc adds ⅔ of
        // its control triangle (r²/2) to the square of diagonal 2r (2r²):
        // 2r² + 4 × ⅔ × r²/2 = 10r²/3 = 213⅓ px².
        let r = 8 * 64;
        let path = Path {
            points: vec![
                pt(r, 0, true),
                pt(r, r, false),
                pt(0, r, true),
                pt(-r, r, false),
                pt(-r, 0, true),
                pt(-r, -r, false),
                pt(0, -r, true),
                pt(r, -r, false),
            ],
            contour_ends: vec![8],
        };
        let m = glyph_mask(&path, Offset::default())?;
        assert_eq!((m.left, m.top, m.width, m.height), (-8, -8, 16, 16));
        let total: u64 = m.coverage.iter().map(|&v| u64::from(v)).sum();
        let got = total as f64 / 255.0;
        let area = 10.0 * 64.0 / 3.0;
        // Flattening within ¼ px moves the boundary inwards by at most
        // that much (chords lie inside a convex arc): at most ¼ px times
        // the perimeter (< 4 × 2 × 8 px), and rounding adds ½ level a pixel.
        assert!(got <= area + 256.0 * 0.5 / 255.0, "{got} vs {area}");
        assert!(
            got >= area - 0.25 * 64.0 - 256.0 * 0.5 / 255.0,
            "{got} vs {area}"
        );
        // The mask is symmetric in both axes, within one level (cuts round
        // down, which is not symmetric).
        let near = |a: Option<u8>, b: Option<u8>| match (a, b) {
            (Some(a), Some(b)) => a.abs_diff(b) <= 1,
            _ => false,
        };
        for y in 0..16u32 {
            for x in 0..16u32 {
                assert!(near(m.get(x, y), m.get(15 - x, y)), "({x}, {y})");
                assert!(near(m.get(x, y), m.get(x, 15 - y)), "({x}, {y})");
            }
        }
        Ok(())
    }

    #[test]
    fn errors() {
        let big = Path {
            points: vec![pt(0, 0, true), pt(1025 * 64, 0, true), pt(0, 64, true)],
            contour_ends: vec![3],
        };
        assert_eq!(glyph_mask(&big, Offset::default()), Err(Error::TooLarge));
        // 65,537 lines: a contour of that many on-curve points.
        let many = Path {
            points: (0..65_537).map(|i| pt(i % 64, i / 1024, true)).collect(),
            contour_ends: vec![65_537],
        };
        assert_eq!(glyph_mask(&many, Offset::default()), Err(Error::TooComplex));
        assert_eq!(
            glyph_mask(&Path::default(), Offset::default()),
            Ok(Mask::default())
        );
    }
}
