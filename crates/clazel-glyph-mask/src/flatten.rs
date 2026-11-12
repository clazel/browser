//! Quadratic Béziers flattened within a quarter pixel (phase-5.md item
//! 5.17, "Method").
//!
//! The curve `B(t) = (1−t)² p0 + 2t(1−t) p1 + t² p2` differs from its chord
//! `(1−t) p0 + t p2` by `t(1−t) (2 p1 − p0 − p2)`, at most `|d| ÷ 4` at
//! `t = ½`, where `d = p0 − 2 p1 + p2`. Cut into `n` pieces of equal
//! parameter length, each piece is a quadratic whose `d` is `d ÷ n²`, so
//! every chord is within `|d| ÷ 4n²` of its piece, and every point of the
//! curve within that of the polyline (and back). We take the least power
//! of two `n` with `|d|₁ ÷ 4n² ≤ TOLERANCE`, with `|d|₁ = |dx| + |dy| ≥
//! |d|`: a power of two, so that the division by `n²` below is a shift (at
//! most twice the pieces the least `n` would need; a 64-bit division by a
//! variable is also what made its Kani harness run past 20 minutes).
//!
//! The points `B(i ÷ n)` are computed exactly in integers and rounded to the
//! nearest mask unit, which adds at most half a unit. `TOLERANCE` is 15/64
//! px, so the polyline is within 15/64 px + 2⁻¹⁵ px < ¼ px of the curve.

use crate::Error;
use crate::accumulate::Point;

/// The flattening tolerance in mask units: 15/64 px (3,840 of 16,384).
pub const TOLERANCE: u64 = 3_840;

/// The most pieces one Bézier is cut into. A Bézier inside a mask of
/// [`crate::MAX_SIDE`] pixels needs at most 128 (each of `d`'s components is
/// at most 2 × 2²⁴ in magnitude, so `|d|₁` ≤ 2²⁶, and 128² × 4 × 3,840 ≥
/// 2²⁶ > 64² × 4 × 3,840); the cap only bounds the count for a Bézier
/// outside the mask, which [`crate::place`] never gives.
pub const MAX_PIECES: u32 = 128;

/// The number of pieces for the Bézier `p0, p1, p2`: the least power of two
/// `n` with `n² × 4 × TOLERANCE ≥ |d|₁`, capped at [`MAX_PIECES`].
pub fn pieces(p0: Point, p1: Point, p2: Point) -> Result<u32, Error> {
    let second = |a: i64, b: i64, c: i64| -> Result<u64, Error> {
        let twice = b.checked_mul(2).ok_or(Error::Overflow)?;
        let d = a
            .checked_sub(twice)
            .ok_or(Error::Overflow)?
            .checked_add(c)
            .ok_or(Error::Overflow)?;
        Ok(d.unsigned_abs())
    };
    let d = second(p0.x, p1.x, p2.x)?
        .checked_add(second(p0.y, p1.y, p2.y)?)
        .ok_or(Error::Overflow)?;
    let per = TOLERANCE.checked_mul(4).ok_or(Error::Overflow)?;
    let mut n: u32 = 1;
    while n < MAX_PIECES {
        let nn = u64::from(n)
            .checked_mul(u64::from(n))
            .ok_or(Error::Overflow)?;
        if nn.checked_mul(per).ok_or(Error::Overflow)? >= d {
            break;
        }
        n = n.checked_mul(2).ok_or(Error::Overflow)?;
    }
    Ok(n)
}

/// `B(i ÷ n)` for the Bézier `p0, p1, p2` and a power of two `n` (as
/// [`pieces`] gives), rounded half up to a mask unit:
/// `⌊((n−i)² p0 + 2i(n−i) p1 + i² p2 + ⌊n² ÷ 2⌋) ÷ n²⌋`, the division an
/// arithmetic shift. For `i` in `0..=n` the weights are non-negative and sum
/// to `n²`, so the point lies in the box of the three control points;
/// `i = n` gives `p2` exactly. Any other `n` or `i` is [`Error::Overflow`].
pub fn point(p0: Point, p1: Point, p2: Point, n: u32, i: u32) -> Result<Point, Error> {
    if !n.is_power_of_two() || i > n {
        return Err(Error::Overflow);
    }
    let shift = n.trailing_zeros().checked_mul(2).ok_or(Error::Overflow)?;
    let n = i64::from(n);
    let i = i64::from(i);
    let j = n.checked_sub(i).ok_or(Error::Overflow)?;
    let w0 = j.checked_mul(j).ok_or(Error::Overflow)?;
    let w1 = i
        .checked_mul(j)
        .ok_or(Error::Overflow)?
        .checked_mul(2)
        .ok_or(Error::Overflow)?;
    let w2 = i.checked_mul(i).ok_or(Error::Overflow)?;
    let nn = n.checked_mul(n).ok_or(Error::Overflow)?;
    let half = nn.checked_div(2).ok_or(Error::Overflow)?;
    let axis = |a: i64, b: i64, c: i64| -> Result<i64, Error> {
        let s = a
            .checked_mul(w0)
            .ok_or(Error::Overflow)?
            .checked_add(b.checked_mul(w1).ok_or(Error::Overflow)?)
            .ok_or(Error::Overflow)?
            .checked_add(c.checked_mul(w2).ok_or(Error::Overflow)?)
            .ok_or(Error::Overflow)?
            .checked_add(half)
            .ok_or(Error::Overflow)?;
        // An arithmetic shift right by log2(n²) is ⌊s ÷ n²⌋.
        s.checked_shr(shift).ok_or(Error::Overflow)
    };
    Ok(Point {
        x: axis(p0.x, p1.x, p2.x)?,
        y: axis(p0.y, p1.y, p2.y)?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::accumulate::ONE;

    fn p(x: i64, y: i64) -> Point {
        Point { x, y }
    }

    #[test]
    fn a_straight_or_short_bezier_is_one_piece() -> Result<(), Error> {
        assert_eq!(pieces(p(0, 0), p(ONE, ONE), p(2 * ONE, 2 * ONE))?, 1);
        assert_eq!(pieces(p(0, 0), p(0, 0), p(0, 0))?, 1);
        // |d|₁ = 2 × 7,680 = 15,360 = 4 × TOLERANCE: still one piece.
        assert_eq!(pieces(p(0, 0), p(7_680, 0), p(0, 0))?, 1);
        assert_eq!(pieces(p(0, 0), p(7_681, 0), p(0, 0))?, 2);
        // Four times that needs n² ≥ 4: still 2; just over, 4.
        assert_eq!(pieces(p(0, 0), p(30_720, 0), p(0, 0))?, 2);
        assert_eq!(pieces(p(0, 0), p(30_721, 0), p(0, 0))?, 4);
        Ok(())
    }

    #[test]
    fn pieces_grow_as_the_square_root() -> Result<(), Error> {
        // |d|₁ = 2 × 100 px; 200 px ÷ (4 × 15/64 px) = 213.3, so n² ≥ 214:
        // 16.
        let n = pieces(p(0, 0), p(100 * ONE, 0), p(0, 0))?;
        assert_eq!(n, 16);
        // The largest Bézier inside a 1024-pixel mask needs 128.
        let m = 1024 * ONE;
        assert_eq!(pieces(p(0, 0), p(m, m), p(0, 0))?, 128);
        assert_eq!(pieces(p(m, m), p(0, 0), p(m, m))?, 128);
        // Half as large needs 64.
        assert_eq!(pieces(p(0, 0), p(m / 2, m / 2), p(0, 0))?, 64);
        // Outside the mask, the count is capped.
        assert_eq!(pieces(p(0, 0), p(i64::MAX / 4, 0), p(0, 0))?, MAX_PIECES);
        Ok(())
    }

    #[test]
    fn points_are_on_the_curve() -> Result<(), Error> {
        let (a, b, c) = (p(0, 0), p(64, 128), p(128, 0));
        assert_eq!(point(a, b, c, 4, 0)?, a);
        assert_eq!(point(a, b, c, 4, 4)?, c);
        // t = ½: (a + 2b + c) ÷ 4.
        assert_eq!(point(a, b, c, 4, 2)?, p(64, 64));
        // t = ¼: (9a + 6b + c) ÷ 16 = (32, 48).
        assert_eq!(point(a, b, c, 4, 1)?, p(32, 48));
        assert_eq!(point(a, b, c, 0, 0), Err(Error::Overflow));
        assert_eq!(point(a, b, c, 2, 3), Err(Error::Overflow));
        assert_eq!(point(a, b, c, 3, 1), Err(Error::Overflow));
        // Rounding: (0 + 2 × 1 × 3 × 1 + 0 + 8) >> 4 = 0 for a control
        // point at 1 and n = 4, i = 1: 6/16 rounds to 0, 10/16 to 1.
        assert_eq!(point(p(0, 0), p(1, 0), p(0, 0), 4, 1)?.x, 0);
        assert_eq!(point(p(0, 0), p(1, 0), p(0, 0), 4, 2)?.x, 1);
        // Negative coordinates shift arithmetically (floor).
        assert_eq!(point(p(-3, 0), p(-3, 0), p(-3, 0), 4, 1)?.x, -3);
        Ok(())
    }

    /// Every polyline is within a quarter pixel of the curve, measured at
    /// 64 parameter values per piece against the exact curve in `f64`.
    #[test]
    fn within_a_quarter_pixel() -> Result<(), Error> {
        let cases = [
            (p(0, 0), p(40 * ONE, 90 * ONE), p(80 * ONE, 0)),
            (p(3, 7), p(1_000_001, 5), p(17, 2_000_003)),
            (p(0, 0), p(ONE, 0), p(ONE, ONE)),
        ];
        for (a, b, c) in cases {
            let n = pieces(a, b, c)?;
            let f = |q: Point| (q.x as f64, q.y as f64);
            let (fa, fb, fc) = (f(a), f(b), f(c));
            let curve = |t: f64| {
                let u = 1.0 - t;
                (
                    u * u * fa.0 + 2.0 * t * u * fb.0 + t * t * fc.0,
                    u * u * fa.1 + 2.0 * t * u * fb.1 + t * t * fc.1,
                )
            };
            for i in 0..n {
                let s = f(point(a, b, c, n, i)?);
                let e = f(point(a, b, c, n, i.saturating_add(1))?);
                for k in 0..=64u32 {
                    let t = (f64::from(i) + f64::from(k) / 64.0) / f64::from(n);
                    let q = curve(t);
                    let dist = segment_distance(q, s, e);
                    assert!(dist <= ONE as f64 / 4.0, "{dist} at t = {t}");
                }
            }
        }
        Ok(())
    }

    fn segment_distance(q: (f64, f64), s: (f64, f64), e: (f64, f64)) -> f64 {
        let (dx, dy) = (e.0 - s.0, e.1 - s.1);
        let len = dx * dx + dy * dy;
        let t = if len == 0.0 {
            0.0
        } else {
            (((q.0 - s.0) * dx + (q.1 - s.1) * dy) / len).clamp(0.0, 1.0)
        };
        let (px, py) = (s.0 + t * dx - q.0, s.1 + t * dy - q.1);
        (px * px + py * py).sqrt()
    }
}
