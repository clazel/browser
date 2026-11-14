//! One contour with its implied on-curve points made explicit.
//!
//! OpenType 1.9, chapter `glyf`, "Simple Glyph Description": `flags` bit 0,
//! `ON_CURVE_POINT`, "If set, the point is on the curve; otherwise, it is
//! off the curve", and a contour is closed (its last point joins its
//! first). Apple's TrueType Reference Manual, chapter 1, "Digitizing
//! Letterform Designs", gives the rule the `glyf` chapter leaves implicit:
//! between two consecutive off-curve points lies an on-curve point midway
//! between them.

use super::PathPoint;
use super::scale::midpoint;
use crate::Error;

/// The implied on-curve point between two off-curve points.
fn implied(a: &PathPoint, b: &PathPoint) -> PathPoint {
    PathPoint {
        x: midpoint(a.x, b.x),
        y: midpoint(a.y, b.y),
        on_curve: true,
    }
}

/// Append contour `points` (one closed contour, in 26.6) to `out` with
/// every implied on-curve point made explicit and an on-curve point first.
/// Returns whether anything was appended (nothing for an empty contour).
///
/// The start (modelling choice in [`super`]): the first point if it is
/// on-curve; else the last point if that is on-curve (the first point is
/// then the control point of the segment closing the contour); else the
/// implied point between the last and the first. Then each remaining point
/// in order, with an implied point before it when it and the point before it
/// are both off-curve. The closing segment, from the last point appended to
/// the start, needs no implied point because the start is on-curve.
///
/// At most `2 × points.len()` points are appended.
pub fn push_contour(points: &[PathPoint], out: &mut Vec<PathPoint>) -> Result<bool, Error> {
    let (Some(first), Some((last, but_last))) = (points.first(), points.split_last()) else {
        return Ok(false);
    };
    let start = contour_start(first, last);
    let rest = if first.on_curve {
        points.get(1..).ok_or(Error::Truncated)?
    } else if last.on_curve {
        but_last
    } else {
        points
    };
    out.push(start);
    let mut previous = start;
    for p in rest {
        push_point(&previous, p, out);
        previous = *p;
    }
    Ok(true)
}

/// [`push_contour`]'s start: the first point if it is on-curve, else the
/// last if that is, else the implied point between the last and the first.
/// Always on-curve.
pub(crate) fn contour_start(first: &PathPoint, last: &PathPoint) -> PathPoint {
    if first.on_curve {
        *first
    } else if last.on_curve {
        *last
    } else {
        implied(last, first)
    }
}

/// One step of [`push_contour`]'s loop: append `p`, which follows
/// `previous` in the contour, preceded by the implied on-curve point between
/// them when both are off-curve.
pub(crate) fn push_point(previous: &PathPoint, p: &PathPoint, out: &mut Vec<PathPoint>) {
    if !previous.on_curve && !p.on_curve {
        out.push(implied(previous, p));
    }
    out.push(*p);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pt(x: i32, y: i32, on_curve: bool) -> PathPoint {
        PathPoint { x, y, on_curve }
    }

    fn run(points: &[PathPoint]) -> Result<Vec<(i32, i32, bool)>, Error> {
        let mut out = Vec::new();
        push_contour(points, &mut out)?;
        Ok(out.iter().map(|p| (p.x, p.y, p.on_curve)).collect())
    }

    #[test]
    fn starts_on_the_first_on_curve_point() -> Result<(), Error> {
        assert_eq!(run(&[])?, []);
        assert_eq!(run(&[pt(1, 2, true)])?, [(1, 2, true)]);
        assert_eq!(
            run(&[pt(0, 0, true), pt(10, 0, false), pt(10, 10, true)])?,
            [(0, 0, true), (10, 0, false), (10, 10, true)]
        );
        Ok(())
    }

    #[test]
    fn first_off_last_on_starts_at_the_last() -> Result<(), Error> {
        assert_eq!(
            run(&[pt(10, 0, false), pt(10, 10, true), pt(0, 0, true)])?,
            [(0, 0, true), (10, 0, false), (10, 10, true)]
        );
        Ok(())
    }

    #[test]
    fn all_off_curve_is_a_chain_of_implied_points() -> Result<(), Error> {
        // A "circle" of four control points: the start is between the last
        // and the first, and every pair gets an implied point.
        assert_eq!(
            run(&[
                pt(0, 10, false),
                pt(10, 0, false),
                pt(0, -10, false),
                pt(-10, 0, false)
            ])?,
            [
                (-5, 5, true),
                (0, 10, false),
                (5, 5, true),
                (10, 0, false),
                (5, -5, true),
                (0, -10, false),
                (-5, -5, true),
                (-10, 0, false)
            ]
        );
        // One control point alone: a degenerate contour, still well formed.
        assert_eq!(run(&[pt(3, 3, false)])?, [(3, 3, true), (3, 3, false)]);
        Ok(())
    }
}
