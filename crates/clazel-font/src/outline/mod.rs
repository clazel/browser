//! Glyph outlines as paths in 26.6 fixed-point pixels (phase-5.md item
//! 5.10): the input of the glyph rasterizer (`clazel-glyph-mask`, item
//! 5.17).
//!
//! # Sources
//!
//! - OpenType 1.9, chapter `glyf`
//!   (<https://learn.microsoft.com/en-us/typography/opentype/otspec190/glyf>),
//!   "Simple Glyph Description": a contour is a closed sequence of on-curve
//!   and off-curve points, each off-curve point a quadratic Bézier control
//!   point.
//! - Apple, TrueType Reference Manual, chapter 1, "Digitizing Letterform
//!   Designs" (<https://developer.apple.com/fonts/TrueType-Reference-Manual/RM01/Chap1.html>),
//!   the second text: between two consecutive off-curve points lies an
//!   implied on-curve point midway between them, which the `glyf` chapter
//!   leaves implicit. This module makes those points explicit ([`contour`]).
//! - Composite glyphs are flattened by [`crate::glyf::outline`] (item 5.9),
//!   which applies each component's transform and offset in font units.
//!
//! OpenType numbers no steps; chapter, section and field name are the
//! citation (CLAUDE.md rule 5).
//!
//! # Modelling choices
//!
//! - **26.6 fixed point**, FreeType's convention: a coordinate is an `i32`
//!   counting 1/64 pixel ([`ONE_PIXEL`]). The size is given in the same
//!   units (pixels per em × 64), so 16 px is 1024.
//! - **Scaling rounds once per point**, half away from zero:
//!   `round(v × size ÷ unitsPerEm)` computed exactly in 64-bit integers
//!   ([`scale::scale`]). No hinting and no grid fitting
//!   (`ROUND_XY_TO_GRID` is ignored, as in 5.9).
//! - **Implied points are computed after scaling**, as the floor of the
//!   mean of two scaled points ([`scale::midpoint`]), so they are within
//!   1/128 px of the exact midpoint of the unscaled points scaled.
//! - **A contour's first point is on-curve.** If the glyph's first point is
//!   off-curve, the contour starts at its last point when that is on-curve,
//!   and otherwise at the implied point between its last and first points
//!   (FreeType's `FT_Outline_Decompose` does the same). The closed contour
//!   is the same curve whichever point it starts at.
//! - **The y axis points up**, as in the font: (0, 0) is the glyph origin
//!   on the baseline. Whoever places the glyph on a page flips y.
//! - **Every failure is an empty glyph.** A glyph that cannot be read or
//!   flattened (malformed bytes, a component cycle, nesting beyond
//!   [`crate::glyf::MAX_COMPONENT_DEPTH`], more than
//!   [`crate::glyf::MAX_COMPONENTS`] components or
//!   [`crate::glyf::MAX_POINTS`] points, a bad anchor point) or whose scaled
//!   coordinates leave `i32` (about ±33 million px), or a negative size,
//!   gives [`Path::default`], which draws nothing ([`glyph_path`]). This is
//!   listed for the hostile fonts of item 5.26. [`try_glyph_path`] keeps the
//!   reason, for tests.
//! - **The path type lives here**, not in `clazel-glyph-mask`, which does
//!   not exist yet. The plan's direction is font → raster (5.17 starts "with
//!   5.10's outline type"), and nothing here depends on raster, so
//!   `clazel-glyph-mask` takes [`Path`] from this crate. [`Path`] holds no
//!   font bytes and has no lifetime; the rasterizer may also build one itself
//!   (a box is four on-curve points).

pub mod contour;
pub mod scale;

use crate::glyf::Outline;
use crate::{Error, Face};

/// One pixel in 26.6 fixed point.
pub const ONE_PIXEL: i32 = 64;

/// A point of a [`Path`], in 26.6 fixed-point pixels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PathPoint {
    /// x, in 1/64 px.
    pub x: i32,
    /// y, in 1/64 px, upwards.
    pub y: i32,
    /// On the curve; otherwise the control point of a quadratic Bézier
    /// between the points before and after it.
    pub on_curve: bool,
}

/// Closed contours of lines and quadratic Béziers, filled by the non-zero
/// rule.
///
/// A path from this module is **well formed** ([`Path::is_well_formed`]):
/// every contour has at least one point, starts with an on-curve point and
/// has no two consecutive off-curve points. Each contour is closed: its last
/// point joins its first. So a contour reads as a sequence of segments: an
/// on-curve point followed by an on-curve point is a line, and an on-curve,
/// off-curve, on-curve triple is a quadratic Bézier.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Path {
    /// All points, contour after contour.
    pub points: Vec<PathPoint>,
    /// Where each contour ends in `points` (exclusive), in order.
    pub contour_ends: Vec<usize>,
}

impl Path {
    /// The contours, as slices of `points`. A contour end out of order or
    /// past `points` ends the iteration.
    pub fn contours(&self) -> impl Iterator<Item = &[PathPoint]> {
        let mut start = 0usize;
        self.contour_ends.iter().map_while(move |&end| {
            let c = self.points.get(start..end)?;
            start = end;
            Some(c)
        })
    }

    /// Whether the path has the form [`Path`] describes: contour ends
    /// increasing and the last equal to the number of points, every contour
    /// non-empty and starting on-curve, and no two consecutive off-curve
    /// points (the last and first points of a contour cannot both be
    /// off-curve, since the first is on-curve).
    pub fn is_well_formed(&self) -> bool {
        let mut start = 0usize;
        for &end in &self.contour_ends {
            let Some(c) = self.points.get(start..end) else {
                return false;
            };
            if !c.first().is_some_and(|p| p.on_curve) {
                return false;
            }
            if c.windows(2)
                .any(|w| matches!(w, [a, b] if !a.on_curve && !b.on_curve))
            {
                return false;
            }
            start = end;
        }
        start == self.points.len()
    }
}

/// A flattened outline ([`crate::glyf::outline`], font units) scaled to
/// `size` (26.6 pixels per em) at `units_per_em`, with implied on-curve
/// points made explicit. Points after the last contour end, which a
/// flattened outline never has, are dropped.
pub fn path_from_outline(outline: &Outline, units_per_em: u16, size: i32) -> Result<Path, Error> {
    let mut path = Path::default();
    let mut scaled = Vec::new();
    let mut start = 0usize;
    for &end in &outline.contour_ends {
        let points = outline.points.get(start..end).ok_or(Error::Truncated)?;
        scaled.clear();
        for p in points {
            scaled.push(PathPoint {
                x: scale::scale(p.x, size, units_per_em)?,
                y: scale::scale(p.y, size, units_per_em)?,
                on_curve: p.on_curve,
            });
        }
        if contour::push_contour(&scaled, &mut path.points)? {
            path.contour_ends.push(path.points.len());
        }
        start = end;
    }
    Ok(path)
}

/// Glyph `glyph` of `face` at `size` (26.6 pixels per em), or the reason it
/// cannot be drawn.
pub fn try_glyph_path(face: &Face<'_>, glyph: u16, size: i32) -> Result<Path, Error> {
    let outline = face.outline(glyph)?;
    path_from_outline(&outline, face.units_per_em(), size)
}

/// Glyph `glyph` of `face` at `size` (26.6 pixels per em); an empty path if
/// it cannot be drawn (see the modelling choices above).
pub fn glyph_path(face: &Face<'_>, glyph: u16, size: i32) -> Path {
    try_glyph_path(face, glyph, size).unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::glyf::Point;

    fn on(x: i32, y: i32) -> Point {
        Point {
            x,
            y,
            on_curve: true,
        }
    }

    fn off(x: i32, y: i32) -> Point {
        Point {
            x,
            y,
            on_curve: false,
        }
    }

    #[test]
    fn scales_and_makes_implied_points_explicit() -> Result<(), Error> {
        // One contour: on, off, off, on; 1000 units per em at 10 px (640).
        let o = Outline {
            points: vec![on(0, 0), off(100, 0), off(100, 100), on(0, 100)],
            contour_ends: vec![4],
        };
        let p = path_from_outline(&o, 1000, 640)?;
        let xy: Vec<(i32, i32, bool)> = p.points.iter().map(|q| (q.x, q.y, q.on_curve)).collect();
        // 100 units at 10 px per 1000 units = 1 px = 64.
        assert_eq!(
            xy,
            [
                (0, 0, true),
                (64, 0, false),
                (64, 32, true),
                (64, 64, false),
                (0, 64, true)
            ]
        );
        assert_eq!(p.contour_ends, [5]);
        assert!(p.is_well_formed());
        Ok(())
    }

    #[test]
    fn contours_and_well_formedness() {
        let pt = |on_curve| PathPoint {
            x: 0,
            y: 0,
            on_curve,
        };
        let good = Path {
            points: vec![pt(true), pt(false), pt(true), pt(true)],
            contour_ends: vec![3, 4],
        };
        assert!(good.is_well_formed());
        assert_eq!(good.contours().map(<[_]>::len).collect::<Vec<_>>(), [3, 1]);
        assert!(Path::default().is_well_formed());
        let starts_off = Path {
            points: vec![pt(false), pt(true)],
            contour_ends: vec![2],
        };
        assert!(!starts_off.is_well_formed());
        let two_off = Path {
            points: vec![pt(true), pt(false), pt(false)],
            contour_ends: vec![3],
        };
        assert!(!two_off.is_well_formed());
        let empty_contour = Path {
            points: vec![pt(true)],
            contour_ends: vec![1, 1],
        };
        assert!(!empty_contour.is_well_formed());
        let short = Path {
            points: vec![pt(true), pt(true)],
            contour_ends: vec![1],
        };
        assert!(!short.is_well_formed());
    }

    #[test]
    fn failures_are_errors_here() {
        let o = Outline {
            points: vec![on(i32::MAX, 0)],
            contour_ends: vec![1],
        };
        // i32::MAX units at 2 px per em: past i32 in 26.6.
        assert_eq!(path_from_outline(&o, 16, 128), Err(Error::Overflow));
        let bad_end = Outline {
            points: vec![on(0, 0)],
            contour_ends: vec![2],
        };
        assert_eq!(path_from_outline(&bad_end, 16, 64), Err(Error::Truncated));
        assert_eq!(
            path_from_outline(&Outline::default(), 16, -1),
            Ok(Path::default())
        );
        let one = Outline {
            points: vec![on(1, 1)],
            contour_ends: vec![1],
        };
        assert_eq!(path_from_outline(&one, 16, -1), Err(Error::FontSize));
    }
}
