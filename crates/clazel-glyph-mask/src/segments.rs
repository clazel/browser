//! A contour's segments: lines and quadratic Béziers.
//!
//! OpenType 1.9, chapter `glyf`, "Simple Glyph Description": a contour is a
//! closed sequence of on-curve and off-curve points, each off-curve point
//! a quadratic Bézier control point; Apple's TrueType Reference Manual,
//! chapter 1, "Digitizing Letterform Designs": between two consecutive
//! off-curve points lies an implied on-curve point midway between them.
//!
//! A [`clazel_font::outline::Path`] from `clazel-font` is already well
//! formed (each contour starts on-curve, no two off-curve points in a row),
//! so for it this walk is: an on-curve point after an on-curve point is a
//! line, an on-curve, off-curve, on-curve triple is a Bézier, and the last
//! point joins the first. The path's fields are public, so any contour is
//! accepted: consecutive off-curve points get their implied midpoint, and a
//! contour with no on-curve point starts at the midpoint of its last and
//! first points (FreeType's `FT_Outline_Decompose` does the same). For a
//! well-formed contour no midpoint is ever computed.

use crate::Error;
use crate::accumulate::Point;

/// A segment of a contour, in mask units.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Segment {
    /// A line from the first point to the second.
    Line(Point, Point),
    /// A quadratic Bézier: start, control point, end.
    Quad(Point, Point, Point),
}

/// The implied on-curve point between two off-curve points: the floor of
/// their mean, which lies between them.
pub fn midpoint(a: Point, b: Point) -> Result<Point, Error> {
    let mid = |u: i64, v: i64| -> Result<i64, Error> {
        u.checked_add(v)
            .ok_or(Error::Overflow)?
            .checked_div_euclid(2)
            .ok_or(Error::Overflow)
    };
    Ok(Point {
        x: mid(a.x, b.x)?,
        y: mid(a.y, b.y)?,
    })
}

/// Calls `f` on every segment of the closed contour `points` (each with its
/// on-curve flag), in order, ending with the segment back to the start. An
/// empty contour has no segments.
pub fn for_each_segment(
    points: &[(Point, bool)],
    mut f: impl FnMut(Segment) -> Result<(), Error>,
) -> Result<(), Error> {
    let (Some(&(first, _)), Some(&(last, _))) = (points.first(), points.last()) else {
        return Ok(());
    };
    // Start at the first on-curve point, then walk the rest cyclically.
    let (start, after, before) = match points.iter().position(|&(_, on)| on) {
        Some(s) => (
            first_on(points, s),
            points.get(s.saturating_add(1)..).unwrap_or(&[]),
            points.get(..s).unwrap_or(&[]),
        ),
        None => (midpoint(last, first)?, points, &[][..]),
    };
    let mut current = start;
    let mut control: Option<Point> = None;
    for &(q, on) in after.iter().chain(before) {
        match (on, control) {
            (true, None) => {
                f(Segment::Line(current, q))?;
                current = q;
            }
            (true, Some(c)) => {
                f(Segment::Quad(current, c, q))?;
                current = q;
                control = None;
            }
            (false, None) => control = Some(q),
            (false, Some(c)) => {
                let m = midpoint(c, q)?;
                f(Segment::Quad(current, c, m))?;
                current = m;
                control = Some(q);
            }
        }
    }
    match control {
        None => f(Segment::Line(current, start)),
        Some(c) => f(Segment::Quad(current, c, start)),
    }
}

/// The point at index `s` (known to exist).
fn first_on(points: &[(Point, bool)], s: usize) -> Point {
    points.get(s).map_or(Point { x: 0, y: 0 }, |&(p, _)| p)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(x: i64, y: i64) -> Point {
        Point { x, y }
    }

    fn walk(points: &[(Point, bool)]) -> Result<Vec<Segment>, Error> {
        let mut out = Vec::new();
        for_each_segment(points, |s| {
            out.push(s);
            Ok(())
        })?;
        Ok(out)
    }

    #[test]
    fn well_formed_contour() -> Result<(), Error> {
        let c = [
            (p(0, 0), true),
            (p(4, 0), true),
            (p(4, 4), false),
            (p(0, 4), true),
        ];
        assert_eq!(
            walk(&c)?,
            [
                Segment::Line(p(0, 0), p(4, 0)),
                Segment::Quad(p(4, 0), p(4, 4), p(0, 4)),
                Segment::Line(p(0, 4), p(0, 0)),
            ]
        );
        // A closing Bézier.
        let c = [(p(0, 0), true), (p(4, 0), true), (p(4, 4), false)];
        assert_eq!(
            walk(&c)?,
            [
                Segment::Line(p(0, 0), p(4, 0)),
                Segment::Quad(p(4, 0), p(4, 4), p(0, 0)),
            ]
        );
        Ok(())
    }

    #[test]
    fn any_contour() -> Result<(), Error> {
        assert_eq!(walk(&[])?, []);
        assert_eq!(walk(&[(p(1, 1), true)])?, [Segment::Line(p(1, 1), p(1, 1))]);
        // Starting off-curve: the walk starts at the first on-curve point.
        let c = [(p(4, 4), false), (p(0, 4), true), (p(0, 0), true)];
        assert_eq!(
            walk(&c)?,
            [
                Segment::Line(p(0, 4), p(0, 0)),
                Segment::Quad(p(0, 0), p(4, 4), p(0, 4)),
            ]
        );
        // Two off-curve points in a row: the implied midpoint.
        let c = [(p(0, 0), true), (p(4, 0), false), (p(4, 4), false)];
        assert_eq!(
            walk(&c)?,
            [
                Segment::Quad(p(0, 0), p(4, 0), p(4, 2)),
                Segment::Quad(p(4, 2), p(4, 4), p(0, 0)),
            ]
        );
        // No on-curve point at all: start between the last and the first.
        let c = [
            (p(0, 0), false),
            (p(4, 0), false),
            (p(4, 4), false),
            (p(0, 4), false),
        ];
        assert_eq!(
            walk(&c)?,
            [
                Segment::Quad(p(0, 2), p(0, 0), p(2, 0)),
                Segment::Quad(p(2, 0), p(4, 0), p(4, 2)),
                Segment::Quad(p(4, 2), p(4, 4), p(2, 4)),
                Segment::Quad(p(2, 4), p(0, 4), p(0, 2)),
            ]
        );
        Ok(())
    }

    #[test]
    fn midpoint_floors() -> Result<(), Error> {
        assert_eq!(midpoint(p(0, -3), p(3, 0))?, p(1, -2));
        assert_eq!(midpoint(p(i64::MAX, 0), p(1, 0)), Err(Error::Overflow));
        Ok(())
    }

    #[test]
    fn errors_stop_the_walk() {
        let c = [(p(0, 0), true), (p(4, 0), true), (p(4, 4), true)];
        let mut seen = 0u32;
        let r = for_each_segment(&c, |_| {
            seen = seen.saturating_add(1);
            Err(Error::TooComplex)
        });
        assert_eq!((r, seen), (Err(Error::TooComplex), 1));
    }
}
