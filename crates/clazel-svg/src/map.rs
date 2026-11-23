//! The equivalent transform of an SVG viewport (SVG 2 section 8.2), for the
//! only `preserveAspectRatio` in scope, the default `xMidYMid meet`.
//!
//! Section 8.2, with `align` = `xMidYMid` and `meetOrSlice` = `meet`:
//!
//! 1. Let vb-x, vb-y, vb-width, vb-height be the `viewBox`'s numbers and
//!    e-x, e-y, e-width, e-height the viewport (here 0, 0, the size the image
//!    is drawn at: the decoder's [`Config`](clazel_image_shape::Config)).
//! 2. scale-x = e-width / vb-width, scale-y = e-height / vb-height.
//! 3. (`meet`) "set the larger of scale-x and scale-y to the smaller".
//! 4. translate-x = e-x - vb-x * scale-x, translate-y likewise.
//! 5. (`xMid`) add (e-width - vb-width * scale-x) / 2 to translate-x;
//!    (`YMid`) add (e-height - vb-height * scale-y) / 2 to translate-y.
//!
//! The transform is `translate(translate-x, translate-y) scale(scale-x,
//! scale-y)`. Here every number is an integer: user coordinates are fixed
//! point (units of 2^-16), device coordinates are in 1/256 pixel, and the
//! one scale is the exact rational `num / den` (`num` the viewport side in
//! 1/256 pixel, `den` the `viewBox` side in 2^-16), so the only rounding is
//! the floor of one division per coordinate.

use crate::limits::{MAX_DEVICE, UNIT};
use clazel_image_shape::Error;

/// A `viewBox`: fixed-point numbers, `w` and `h` positive.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ViewBox {
    pub x: i64,
    pub y: i64,
    pub w: i64,
    pub h: i64,
}

/// User space to device space (1/256 pixel).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Map {
    x: i64,
    y: i64,
    num: i64,
    den: i64,
    off_x: i64,
    off_y: i64,
}

fn range() -> Error {
    Error::Unsupported("a coordinate out of range")
}

impl Map {
    /// The transform for a viewport of `width` by `height` pixels (each at
    /// most 2^14, which [`Config`](clazel_image_shape::Config) guarantees).
    pub(crate) fn new(vb: ViewBox, width: u32, height: u32) -> Result<Map, Error> {
        let ew = i64::from(width).checked_mul(UNIT).ok_or_else(range)?;
        let eh = i64::from(height).checked_mul(UNIT).ok_or_else(range)?;
        if vb.w <= 0 || vb.h <= 0 {
            return Err(Error::Malformed("a viewBox with no area"));
        }
        // scale-x <= scale-y  <=>  ew / vb.w <= eh / vb.h.
        let lhs = ew.checked_mul(vb.h).ok_or_else(range)?;
        let rhs = eh.checked_mul(vb.w).ok_or_else(range)?;
        let (num, den, off_x, off_y);
        if lhs <= rhs {
            // The width limits the scale; centre vertically.
            num = ew;
            den = vb.w;
            let content =
                vb.h.checked_mul(num)
                    .and_then(|v| v.checked_div(den))
                    .ok_or_else(range)?;
            off_x = 0;
            off_y = eh.saturating_sub(content) / 2;
        } else {
            num = eh;
            den = vb.h;
            let content =
                vb.w.checked_mul(num)
                    .and_then(|v| v.checked_div(den))
                    .ok_or_else(range)?;
            off_x = ew.saturating_sub(content) / 2;
            off_y = 0;
        }
        Ok(Map {
            x: vb.x,
            y: vb.y,
            num,
            den,
            off_x,
            off_y,
        })
    }

    fn axis(&self, v: i64, origin: i64, off: i64) -> Result<i32, Error> {
        let d = v
            .checked_sub(origin)
            .and_then(|a| a.checked_mul(self.num))
            .and_then(|a| a.checked_div_euclid(self.den))
            .and_then(|a| a.checked_add(off))
            .ok_or_else(range)?;
        if d.abs() > MAX_DEVICE {
            return Err(range());
        }
        i32::try_from(d).map_err(|_| range())
    }

    /// A point in user space (fixed point) to device space (1/256 pixel),
    /// within +-2^30 or [`Error::Unsupported`].
    pub(crate) fn apply(&self, x: i64, y: i64) -> Result<(i32, i32), Error> {
        Ok((
            self.axis(x, self.x, self.off_x)?,
            self.axis(y, self.y, self.off_y)?,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::limits::ONE;

    fn vb(x: i64, y: i64, w: i64, h: i64) -> ViewBox {
        ViewBox {
            x: x.saturating_mul(ONE),
            y: y.saturating_mul(ONE),
            w: w.saturating_mul(ONE),
            h: h.saturating_mul(ONE),
        }
    }

    #[test]
    fn same_aspect_scales() -> Result<(), Error> {
        // HN's logo: viewBox 4 4 188 188 into 18 by 18.
        let m = Map::new(vb(4, 4, 188, 188), 18, 18)?;
        assert_eq!(m.apply(4 * ONE, 4 * ONE)?, (0, 0));
        assert_eq!(m.apply(192 * ONE, 192 * ONE)?, (18 * 256, 18 * 256));
        // Triangle: 0 0 32 16 into 10 by 5.
        let m = Map::new(vb(0, 0, 32, 16), 10, 5)?;
        assert_eq!(m.apply(32 * ONE, 16 * ONE)?, (10 * 256, 5 * 256));
        Ok(())
    }

    #[test]
    fn meet_centres() -> Result<(), Error> {
        // A square viewBox into 40 by 20: scale 20/188, centred in x.
        let m = Map::new(vb(0, 0, 100, 100), 40, 20)?;
        assert_eq!(m.apply(0, 0)?, (10 * 256, 0));
        assert_eq!(m.apply(100 * ONE, 100 * ONE)?, (30 * 256, 20 * 256));
        // And a wide one into a square: centred in y.
        let m = Map::new(vb(0, 0, 100, 50), 20, 20)?;
        assert_eq!(m.apply(0, 0)?, (0, 5 * 256));
        assert_eq!(m.apply(100 * ONE, 50 * ONE)?, (20 * 256, 15 * 256));
        Ok(())
    }

    #[test]
    fn far_points_are_refused() -> Result<(), Error> {
        let m = Map::new(vb(0, 0, 1, 1), 16384, 16384)?;
        assert!(m.apply(1 << 36, 0).is_err());
        assert!(m.apply(0, 0).is_ok());
        Ok(())
    }
}
