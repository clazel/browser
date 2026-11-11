//! Quadratic Béziers flattened within a quarter pixel (phase-5.md item
//! 5.17, "Method").
//!
//! The curve `B(t) = (1−t)² p0 + 2t(1−t) p1 + t² p2` differs from its chord
//! `(1−t) p0 + t p2` by `t(1−t) (2 p1 − p0 − p2)`, at most `|d| ÷ 4` at
//! `t = ½`, where `d = p0 − 2 p1 + p2`. Cut into `n` pieces of equal
//! parameter length, each piece is a quadratic whose `d` is `d ÷ n²`, so
//! every chord is within `|d| ÷ 4n²` of its piece, and every point of the
//! curve within that of the polyline (and back). We take the least `n`
//! with `|d|₁ ÷ 4n² ≤ TOLERANCE`, with `|d|₁ = |dx| + |dy| ≥ |d|`.
//!
//! The points `B(i ÷ n)` are computed exactly in integers and rounded to the
//! nearest mask unit, which adds at most half a unit. `TOLERANCE` is 15/64
//! px, so the polyline is within 15/64 px + 2⁻¹⁵ px < ¼ px of the curve.

use crate::Error;
use crate::accumulate::Point;

/// The flattening tolerance in mask units: 15/64 px (3,840 of 16,384).
pub const TOLERANCE: u64 = 3_840;

/// The most pieces one Bézier is cut into. A Bézier inside a mask of
/// [`crate::MAX_SIDE`] pixels needs at most 67 (each of `d`'s components is
/// at most 2 × 2²⁴ in magnitude, so `|d|₁` ≤ 2²⁶, and 67² × 4 × 3,840 ≥
/// 2²⁶); the cap only bounds the count for a Bézier outside the mask, which
/// [`crate::place`] never gives.
pub const MAX_PIECES: u32 = 128;

/// The number of pieces for the Bézier `p0, p1, p2`: the least `n` ≥ 1 with
/// `n² × 4 × TOLERANCE ≥ |d|₁`, capped at [`MAX_PIECES`].
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
    // The least n with n² ≥ ⌈d ÷ 4 TOLERANCE⌉.
    let q = d.div_ceil(per);
    let mut n = q.isqrt();
    if n.checked_mul(n).ok_or(Error::Overflow)? < q {
        n = n.checked_add(1).ok_or(Error::Overflow)?;
    }
    let n = n.clamp(1, u64::from(MAX_PIECES));
    u32::try_from(n).map_err(|_| Error::Overflow)
}

/// `B(i ÷ n)` for the Bézier `p0, p1, p2`, rounded half up to a mask unit:
/// `⌊((n−i)² p0 + 2i(n−i) p1 + i² p2 + ⌊n² ÷ 2⌋) ÷ n²⌋`. For `i` in
/// `0..=n` the weights are non-negative and sum to `n²`, so the point lies
/// in the box of the three control points; `i = n` gives `p2` exactly.
pub fn point(p0: Point, p1: Point, p2: Point, n: u32, i: u32) -> Result<Point, Error> {
    if n == 0 || i > n {
        return Err(Error::Overflow);
    }
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
        s.checked_div_euclid(nn).ok_or(Error::Overflow)
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
        Ok(())
    }

    #[test]
    fn pieces_grow_as_the_square_root() -> Result<(), Error> {
        // |d|₁ = 2 × 100 px; 200 px ÷ (4 × 15/64 px) = 213.3, so n = 15.
        let n = pieces(p(0, 0), p(100 * ONE, 0), p(0, 0))?;
        assert_eq!(n, 15);
        // The largest Bézier inside a 1024-pixel mask needs 67.
        let m = 1024 * ONE;
        assert_eq!(pieces(p(0, 0), p(m, m), p(0, 0))?, 67);
        assert_eq!(pieces(p(m, m), p(0, 0), p(m, m))?, 67);
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
