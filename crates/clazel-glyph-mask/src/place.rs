//! Where a path's mask goes, and the path in mask units.
//!
//! The mask is the smallest box of whole pixels holding the path's control
//! box (every point, on-curve or not; a quadratic Bézier lies inside the
//! triangle of its control points) after the quarter-pixel offset. Its
//! position is in screen pixels, y down, relative to the glyph origin (the
//! pen position on the baseline): pixel (column, row) of the mask is screen
//! pixel (`left` + column, `top` + row).

use clazel_font::outline::Path;

use crate::accumulate::{Point, SHIFT};
use crate::{Error, Offset};

/// A path placed in its mask: the mask's position and size, and the
/// contours' points in mask units (y down).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Placed {
    /// The mask's left edge, in screen pixels from the glyph origin.
    pub left: i32,
    /// The mask's top edge, in screen pixels from the glyph origin, y down
    /// (a glyph standing on the baseline has a negative `top`).
    pub top: i32,
    /// Width in pixels, at most the `max_side` given to [`place`].
    pub width: u32,
    /// Height in pixels, at most the `max_side` given to [`place`].
    pub height: u32,
    /// The points of every contour, in mask units, with their on-curve flag.
    pub points: Vec<(Point, bool)>,
    /// Where each contour ends in `points` (exclusive).
    pub contour_ends: Vec<usize>,
}

/// Places `path` at `offset` in a mask of at most `max_side` × `max_side`
/// pixels. Only the contours [`Path::contours`] yields are read (it stops at
/// a contour end out of order or past the points). An empty path, or one
/// whose control box has no width or no height, gives a 0 × 0 mask.
///
/// Every point of the result lies in the mask: 0 ≤ x ≤ width × ONE and
/// 0 ≤ y ≤ height × ONE ([`mask_box`] contains every screen point and
/// [`to_local`] maps the box onto the mask; the Kani harnesses
/// `place_screen_any`, `place_box_any` and `place_local_any`).
pub fn place(path: &Path, offset: Offset, max_side: u32) -> Result<Placed, Error> {
    let mut bounds: Option<(i64, i64, i64, i64)> = None;
    let mut count = 0usize;
    for contour in path.contours() {
        for q in contour {
            let (x, y) = screen(q.x, q.y, offset)?;
            bounds = Some(match bounds {
                None => (x, y, x, y),
                Some((x0, y0, x1, y1)) => (x0.min(x), y0.min(y), x1.max(x), y1.max(y)),
            });
        }
        count = count.checked_add(contour.len()).ok_or(Error::Overflow)?;
    }
    let empty = |left: i64, top: i64| -> Result<Placed, Error> {
        Ok(Placed {
            left: i32::try_from(left).map_err(|_| Error::Overflow)?,
            top: i32::try_from(top).map_err(|_| Error::Overflow)?,
            width: 0,
            height: 0,
            points: Vec::new(),
            contour_ends: Vec::new(),
        })
    };
    let Some((x0, y0, x1, y1)) = bounds else {
        return empty(0, 0);
    };
    let MaskBox {
        left,
        top,
        width,
        height,
    } = mask_box(x0, y0, x1, y1, max_side)?;
    if width == 0 || height == 0 {
        return empty(left, top);
    }
    let mut points = Vec::with_capacity(count);
    let mut contour_ends = Vec::new();
    for contour in path.contours() {
        for q in contour {
            let (x, y) = screen(q.x, q.y, offset)?;
            points.push((
                Point {
                    x: to_local(x, left)?,
                    y: to_local(y, top)?,
                },
                q.on_curve,
            ));
        }
        contour_ends.push(points.len());
    }
    Ok(Placed {
        left: i32::try_from(left).map_err(|_| Error::Overflow)?,
        top: i32::try_from(top).map_err(|_| Error::Overflow)?,
        width: u32::try_from(width).map_err(|_| Error::Overflow)?,
        height: u32::try_from(height).map_err(|_| Error::Overflow)?,
        points,
        contour_ends,
    })
}

/// A point in screen coordinates, 26.6, y down: `(x + ox, oy − y)`. From
/// `i32` inputs these stay far inside `i64`.
pub fn screen(x: i32, y: i32, offset: Offset) -> Result<(i64, i64), Error> {
    Ok((
        i64::from(x)
            .checked_add(offset.x.units())
            .ok_or(Error::Overflow)?,
        offset
            .y
            .units()
            .checked_sub(i64::from(y))
            .ok_or(Error::Overflow)?,
    ))
}

/// The whole-pixel box around a control box, in pixels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MaskBox {
    /// Left edge, `⌊x0 ÷ 64⌋`.
    pub left: i64,
    /// Top edge, `⌊y0 ÷ 64⌋`.
    pub top: i64,
    /// `⌈x1 ÷ 64⌉ − left`.
    pub width: i64,
    /// `⌈y1 ÷ 64⌉ − top`.
    pub height: i64,
}

/// The whole-pixel box around the control box (`x0..=x1`, `y0..=y1`, screen
/// 26.6, `x0 ≤ x1`, `y0 ≤ y1`): [`Error::TooLarge`] if wider or taller than
/// `max_side`. Floors and ceilings by 64 are arithmetic shifts by 6.
pub fn mask_box(x0: i64, y0: i64, x1: i64, y1: i64, max_side: u32) -> Result<MaskBox, Error> {
    let floor = |v: i64| v.checked_shr(6).ok_or(Error::Overflow);
    let ceil = |v: i64| {
        v.checked_add(63)
            .ok_or(Error::Overflow)?
            .checked_shr(6)
            .ok_or(Error::Overflow)
    };
    let left = floor(x0)?;
    let top = floor(y0)?;
    let width = ceil(x1)?.checked_sub(left).ok_or(Error::Overflow)?;
    let height = ceil(y1)?.checked_sub(top).ok_or(Error::Overflow)?;
    let max = i64::from(max_side);
    if width > max || height > max {
        return Err(Error::TooLarge);
    }
    Ok(MaskBox {
        left,
        top,
        width,
        height,
    })
}

/// A screen coordinate `v` (26.6) in mask units from the mask edge at
/// `edge` pixels: `(v − 64 edge) × 2⁸`.
pub fn to_local(v: i64, edge: i64) -> Result<i64, Error> {
    v.checked_sub(edge.checked_mul(64).ok_or(Error::Overflow)?)
        .ok_or(Error::Overflow)?
        .checked_mul(1i64 << SHIFT)
        .ok_or(Error::Overflow)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Quarter;
    use crate::accumulate::ONE;
    use clazel_font::outline::PathPoint;

    fn on(x: i32, y: i32) -> PathPoint {
        PathPoint {
            x,
            y,
            on_curve: true,
        }
    }

    fn square(x0: i32, y0: i32, x1: i32, y1: i32) -> Path {
        Path {
            points: vec![on(x0, y0), on(x1, y0), on(x1, y1), on(x0, y1)],
            contour_ends: vec![4],
        }
    }

    #[test]
    fn a_box_on_the_baseline() -> Result<(), Error> {
        // 2 px wide, 3 px tall, standing on the baseline at x = 1 px.
        let p = place(&square(64, 0, 192, 192), Offset::default(), 1024)?;
        assert_eq!((p.left, p.top, p.width, p.height), (1, -3, 2, 3));
        let xs: Vec<i64> = p.points.iter().map(|(q, _)| q.x).collect();
        let ys: Vec<i64> = p.points.iter().map(|(q, _)| q.y).collect();
        assert_eq!(xs, [0, 2 * ONE, 2 * ONE, 0]);
        assert_eq!(ys, [3 * ONE, 3 * ONE, 0, 0]);
        assert_eq!(p.contour_ends, [4]);
        Ok(())
    }

    #[test]
    fn quarter_offsets_move_the_box() -> Result<(), Error> {
        // From x = 0 to 1 px; a ¾ px offset spreads it over two pixels.
        let off = Offset {
            x: Quarter::Three,
            y: Quarter::Two,
        };
        let p = place(&square(0, 0, 64, 64), off, 1024)?;
        assert_eq!((p.left, p.top, p.width, p.height), (0, -1, 2, 2));
        let first = p.points.first().map(|(q, _)| *q);
        assert_eq!(
            first,
            Some(Point {
                x: 3 * ONE / 4,
                y: 3 * ONE / 2
            })
        );
        Ok(())
    }

    #[test]
    fn empty_flat_and_too_large() -> Result<(), Error> {
        let e = place(&Path::default(), Offset::default(), 1024)?;
        assert_eq!((e.width, e.height, e.points.len()), (0, 0, 0));
        let flat = place(&square(10, 64, 100, 64), Offset::default(), 1024)?;
        assert_eq!((flat.width, flat.height), (0, 0));
        assert_eq!(
            place(&square(0, 0, 1025 * 64, 64), Offset::default(), 1024),
            Err(Error::TooLarge)
        );
        assert!(place(&square(0, 0, 1024 * 64, 64), Offset::default(), 1024).is_ok());
        assert_eq!(
            place(
                &square(i32::MIN, i32::MIN, i32::MAX, i32::MAX),
                Offset::default(),
                1024
            ),
            Err(Error::TooLarge)
        );
        Ok(())
    }

    #[test]
    fn bad_contour_ends_stop_reading() -> Result<(), Error> {
        let mut p = square(0, 0, 64, 64);
        p.contour_ends = vec![4, 9];
        let placed = place(&p, Offset::default(), 1024)?;
        assert_eq!(placed.contour_ends, [4]);
        Ok(())
    }
}
