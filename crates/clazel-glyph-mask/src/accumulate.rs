//! Exact-area coverage accumulated per scanline: the signed-area method of
//! `font-rs` and of stb_truetype's second rasterizer (phase-5.md item 5.17,
//! "Method").
//!
//! Every line is cut at each pixel row and, within a row, at each pixel
//! column. A piece inside one cell, from (xa, ya) to (xb, yb) with x
//! measured from the cell's left edge, has a signed height `dy = yb − ya`
//! and covers, to its right inside the cell, the trapezoid area
//! `dy × (ONE − (xa + xb) ÷ 2)`; every cell further right in the row gets
//! the whole `dy × ONE`. So the piece adds `dy × 2 ONE − dy × (xa + xb)` to
//! its own cell and `dy × (xa + xb)` to the next one (both doubled, to stay
//! integral), and a running sum along the row gives each cell twice its
//! signed covered area. That sum is the winding number times the area for
//! a cell no edge crosses, and for a crossed cell the exact area of the
//! part of the cell the path covers, signed by orientation.
//!
//! Coverage is that sum's magnitude clamped to one full cell (`FULL`),
//! scaled to 0..=255 and rounded. Taking the magnitude makes either
//! orientation of a contour paint (TrueType's outer contours run clockwise
//! with y up, which is anticlockwise in the mask's y-down rows); the
//! result equals the non-zero rule except where contours overlap with
//! opposite orientation, as phase-5.md says.
//!
//! # Units
//!
//! Coordinates are mask-local, `ONE` (2¹⁴) units per pixel, y down: 26.6
//! shifted left by [`SHIFT`]. The cuts at row and column edges round to a
//! unit (2⁻¹⁴ px), not to 1/64 px: a 1/128 px error at a cut would move a
//! crossed cell's coverage by up to two of the 255 levels.

use crate::Error;

/// 26.6 coordinates are shifted left by this many bits to get mask units.
pub const SHIFT: u32 = 8;

/// One pixel in mask units (64 × 2⁸ = 2¹⁴).
pub const ONE: i64 = 16_384;

/// Twice a full cell's area in mask units squared (2 × 2¹⁴ × 2¹⁴ = 2²⁹):
/// the running sum's value for a fully covered cell.
pub const FULL: i64 = 536_870_912;

/// A point in mask units, y down.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Point {
    /// x, in 1/16384 px from the mask's left edge.
    pub x: i64,
    /// y, in 1/16384 px from the mask's top edge, downwards.
    pub y: i64,
}

/// The accumulation buffer of a `width` × `height` mask: per row, one cell
/// per pixel plus two, for a piece on the right edge (column `width`) and
/// the cell after it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Accumulator {
    width: usize,
    height: usize,
    stride: usize,
    cells: Vec<i64>,
}

impl Accumulator {
    /// An empty buffer for a `width` × `height` mask. The caller bounds the
    /// size ([`crate::MAX_SIDE`]); a size whose buffer length overflows
    /// `usize` is [`Error::TooLarge`].
    pub fn new(width: u32, height: u32) -> Result<Self, Error> {
        let width = usize::try_from(width).map_err(|_| Error::TooLarge)?;
        let height = usize::try_from(height).map_err(|_| Error::TooLarge)?;
        let stride = width.checked_add(2).ok_or(Error::TooLarge)?;
        let len = stride.checked_mul(height).ok_or(Error::TooLarge)?;
        Ok(Accumulator {
            width,
            height,
            stride,
            cells: vec![0; len],
        })
    }

    /// The buffer's cells, row after row (`width + 2` per row).
    pub fn cells(&self) -> &[i64] {
        &self.cells
    }

    /// Replaces the cells (for the Kani harness of [`Self::finish`], which
    /// starts from any state). A slice of the wrong length is refused.
    pub fn set_cells(&mut self, cells: &[i64]) -> bool {
        if cells.len() != self.cells.len() {
            return false;
        }
        self.cells.copy_from_slice(cells);
        true
    }

    /// The mask's right and bottom edges in mask units.
    fn extent(&self) -> Result<(i64, i64), Error> {
        let w = i64::try_from(self.width).map_err(|_| Error::Overflow)?;
        let h = i64::try_from(self.height).map_err(|_| Error::Overflow)?;
        Ok((
            w.checked_mul(ONE).ok_or(Error::Overflow)?,
            h.checked_mul(ONE).ok_or(Error::Overflow)?,
        ))
    }

    /// Accumulates the line from `a` to `b`.
    ///
    /// Each coordinate is first clamped to the mask (x to 0..=width × ONE,
    /// y to 0..=height × ONE). The flattener only gives points inside the
    /// mask ([`crate::place`] sizes the mask to the path's control box), so
    /// the clamp never changes a line of a path; it makes this function
    /// total. Every arithmetic step is checked; [`Error::Overflow`] is not
    /// reachable for a mask up to [`crate::MAX_SIDE`] and up to
    /// [`crate::MAX_LINES`] lines (the Kani harness `line_any_4x4` and the
    /// bounds in the crate's README).
    pub fn line(&mut self, a: Point, b: Point) -> Result<(), Error> {
        let (xmax, ymax) = self.extent()?;
        let a = Point {
            x: a.x.clamp(0, xmax),
            y: a.y.clamp(0, ymax),
        };
        let b = Point {
            x: b.x.clamp(0, xmax),
            y: b.y.clamp(0, ymax),
        };
        if a.y == b.y {
            // No height: no area to the right of it.
            return Ok(());
        }
        let (ylo, yhi) = (a.y.min(b.y), a.y.max(b.y));
        let mut row = ylo.checked_div(ONE).ok_or(Error::Overflow)?;
        loop {
            let top = row.checked_mul(ONE).ok_or(Error::Overflow)?;
            if top >= yhi {
                return Ok(());
            }
            let bottom = top.checked_add(ONE).ok_or(Error::Overflow)?;
            // The piece inside this row, in the line's own direction. Its
            // ends are computed from the whole line, so the piece in the
            // next row starts exactly where this one ends.
            let ys = a.y.clamp(top, bottom);
            let ye = b.y.clamp(top, bottom);
            if ys != ye {
                let s = Point {
                    x: x_at(a, b, ys)?,
                    y: ys.checked_sub(top).ok_or(Error::Overflow)?,
                };
                let e = Point {
                    x: x_at(a, b, ye)?,
                    y: ye.checked_sub(top).ok_or(Error::Overflow)?,
                };
                self.row_piece(row, s, e)?;
            }
            row = row.checked_add(1).ok_or(Error::Overflow)?;
        }
    }

    /// Accumulates a piece inside row `row`, its y relative to the row's top
    /// (0..=ONE), cut at every column edge.
    fn row_piece(&mut self, row: i64, s: Point, e: Point) -> Result<(), Error> {
        let dy = e.y.checked_sub(s.y).ok_or(Error::Overflow)?;
        if s.x == e.x {
            // Vertical: one cell. On the mask's right edge that is column
            // `width`, which is outside the mask and only carries the cover.
            let col = s.x.checked_div(ONE).ok_or(Error::Overflow)?;
            let fx =
                s.x.checked_sub(col.checked_mul(ONE).ok_or(Error::Overflow)?);
            let fx = fx.ok_or(Error::Overflow)?;
            return self.cell(row, col, fx, fx, dy);
        }
        let (xlo, xhi) = (s.x.min(e.x), s.x.max(e.x));
        let mut col = xlo.checked_div(ONE).ok_or(Error::Overflow)?;
        loop {
            let left = col.checked_mul(ONE).ok_or(Error::Overflow)?;
            if left >= xhi {
                return Ok(());
            }
            let right = left.checked_add(ONE).ok_or(Error::Overflow)?;
            let xa = s.x.clamp(left, right);
            let xb = e.x.clamp(left, right);
            // A non-vertical piece meets a column it only touches at one x
            // in one point, which has no height.
            if xa != xb {
                let ya = y_at(s, e, xa)?;
                let yb = y_at(s, e, xb)?;
                let fxa = xa.checked_sub(left).ok_or(Error::Overflow)?;
                let fxb = xb.checked_sub(left).ok_or(Error::Overflow)?;
                let dy = yb.checked_sub(ya).ok_or(Error::Overflow)?;
                self.cell(row, col, fxa, fxb, dy)?;
            }
            col = col.checked_add(1).ok_or(Error::Overflow)?;
        }
    }

    /// Adds a piece of signed height `dy` from x `fxa` to `fxb` (relative to
    /// the cell's left edge) in cell (`col`, `row`): `dy × 2 ONE − a` to the
    /// cell and `a = dy × (fxa + fxb)` to the next, as the module explains.
    fn cell(&mut self, row: i64, col: i64, fxa: i64, fxb: i64, dy: i64) -> Result<(), Error> {
        let a = dy
            .checked_mul(fxa.checked_add(fxb).ok_or(Error::Overflow)?)
            .ok_or(Error::Overflow)?;
        let own = dy
            .checked_mul(ONE.checked_mul(2).ok_or(Error::Overflow)?)
            .ok_or(Error::Overflow)?
            .checked_sub(a)
            .ok_or(Error::Overflow)?;
        let row = usize::try_from(row).map_err(|_| Error::Overflow)?;
        let col = usize::try_from(col).map_err(|_| Error::Overflow)?;
        if row >= self.height || col > self.width {
            return Err(Error::Overflow);
        }
        let at = row
            .checked_mul(self.stride)
            .ok_or(Error::Overflow)?
            .checked_add(col)
            .ok_or(Error::Overflow)?;
        let next = at.checked_add(1).ok_or(Error::Overflow)?;
        let c = self.cells.get_mut(at).ok_or(Error::Overflow)?;
        *c = c.checked_add(own).ok_or(Error::Overflow)?;
        let c = self.cells.get_mut(next).ok_or(Error::Overflow)?;
        *c = c.checked_add(a).ok_or(Error::Overflow)?;
        Ok(())
    }

    /// The 8-bit mask: per row, the running sum of the cells, its magnitude
    /// clamped to [`FULL`] and scaled to 0..=255, rounded half up. Row after
    /// row, top to bottom, `width` bytes each.
    ///
    /// [`Error::Overflow`] if a running sum leaves `i64`, which needs cells
    /// far beyond what [`crate::MAX_LINES`] lines can add (the harness
    /// `finish_any_4x4` checks every state with cells up to ±2⁵⁰).
    pub fn finish(&self) -> Result<Vec<u8>, Error> {
        let len = self.width.checked_mul(self.height).ok_or(Error::Overflow)?;
        let mut out = Vec::with_capacity(len);
        for row in self.cells.chunks_exact(self.stride) {
            let mut run: i64 = 0;
            for &c in row.iter().take(self.width) {
                run = run.checked_add(c).ok_or(Error::Overflow)?;
                out.push(coverage(run)?);
            }
        }
        Ok(out)
    }
}

/// A running sum's coverage: `round(min(|run|, FULL) × 255 ÷ FULL)`.
pub fn coverage(run: i64) -> Result<u8, Error> {
    let full = FULL.unsigned_abs();
    let v = run.unsigned_abs().min(full);
    let scaled = v
        .checked_mul(255)
        .ok_or(Error::Overflow)?
        .checked_add(full.checked_div(2).ok_or(Error::Overflow)?)
        .ok_or(Error::Overflow)?
        .checked_div(full)
        .ok_or(Error::Overflow)?;
    u8::try_from(scaled).map_err(|_| Error::Overflow)
}

/// The x of the line from `a` to `b` (`a.y ≠ b.y`) at height `y`, rounded
/// down: `a.x + ⌊(b.x − a.x)(y − a.y) ÷ (b.y − a.y)⌋`. Exact at `a.y` and
/// `b.y`, and between `a.x` and `b.x` for `y` between `a.y` and `b.y`.
fn x_at(a: Point, b: Point, y: i64) -> Result<i64, Error> {
    let num =
        b.x.checked_sub(a.x)
            .ok_or(Error::Overflow)?
            .checked_mul(y.checked_sub(a.y).ok_or(Error::Overflow)?)
            .ok_or(Error::Overflow)?;
    let den = b.y.checked_sub(a.y).ok_or(Error::Overflow)?;
    a.x.checked_add(floor_div(num, den)?).ok_or(Error::Overflow)
}

/// The y of the line from `a` to `b` (`a.x ≠ b.x`) at `x`, rounded down;
/// [`x_at`] with the axes swapped.
fn y_at(a: Point, b: Point, x: i64) -> Result<i64, Error> {
    let swap = |p: Point| Point { x: p.y, y: p.x };
    x_at(swap(a), swap(b), x)
}

/// `⌊num ÷ den⌋` for `den ≠ 0`.
fn floor_div(num: i64, den: i64) -> Result<i64, Error> {
    let (num, den) = if den < 0 {
        (
            num.checked_neg().ok_or(Error::Overflow)?,
            den.checked_neg().ok_or(Error::Overflow)?,
        )
    } else {
        (num, den)
    };
    num.checked_div_euclid(den).ok_or(Error::Overflow)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(x: i64, y: i64) -> Point {
        Point { x, y }
    }

    /// Accumulates a closed polygon given in pixels × `ONE`.
    fn polygon(w: u32, h: u32, pts: &[(i64, i64)]) -> Result<Vec<u8>, Error> {
        let mut acc = Accumulator::new(w, h)?;
        for (i, &(x, y)) in pts.iter().enumerate() {
            let (nx, ny) = pts.get(i.saturating_add(1)).or(pts.first()).copied().unwrap_or((x, y));
            acc.line(p(x, y), p(nx, ny))?;
        }
        acc.finish()
    }

    #[test]
    fn full_square() -> Result<(), Error> {
        let o = ONE;
        // Clockwise and anticlockwise both paint.
        let cw = polygon(2, 2, &[(0, 0), (2 * o, 0), (2 * o, 2 * o), (0, 2 * o)])?;
        let ccw = polygon(2, 2, &[(0, 0), (0, 2 * o), (2 * o, 2 * o), (2 * o, 0)])?;
        assert_eq!(cw, [255; 4]);
        assert_eq!(ccw, [255; 4]);
        Ok(())
    }

    #[test]
    fn half_pixel_offsets() -> Result<(), Error> {
        let o = ONE;
        let h = o / 2;
        // A 1×1 square at (0.5, 0.5) covers a quarter of each of 4 pixels.
        let m = polygon(2, 2, &[(h, h), (h + o, h), (h + o, h + o), (h, h + o)])?;
        assert_eq!(m, [64; 4]);
        // A vertical edge at x = 0.5 over a full row: half the pixel.
        let m = polygon(1, 1, &[(h, 0), (o, 0), (o, o), (h, o)])?;
        assert_eq!(m, [128]);
        Ok(())
    }

    #[test]
    fn diagonal_triangle() -> Result<(), Error> {
        let o = ONE;
        // The lower-left half of a pixel: 0.5 → 128 (127.5 rounded up).
        let m = polygon(1, 1, &[(0, 0), (o, o), (0, o)])?;
        assert_eq!(m, [128]);
        // A triangle over 2×2 pixels, (0,0) (2,0) (0,2): the cells on the
        // diagonal are half covered, the corner fully, the far one not.
        let m = polygon(2, 2, &[(0, 0), (2 * o, 0), (0, 2 * o)])?;
        assert_eq!(m, [255, 128, 128, 0]);
        Ok(())
    }

    #[test]
    fn overlap_and_holes() -> Result<(), Error> {
        let o = ONE;
        // Two same-direction squares overlapping: clamped to full.
        let mut acc = Accumulator::new(1, 1)?;
        for _ in 0..2 {
            acc.line(p(0, 0), p(o, 0))?;
            acc.line(p(o, 0), p(o, o))?;
            acc.line(p(o, o), p(0, o))?;
            acc.line(p(0, o), p(0, 0))?;
        }
        assert_eq!(acc.finish()?, [255]);
        // An outer 3×3 square and an inner 1×1 square in the opposite
        // direction: a hole in the middle.
        let mut acc = Accumulator::new(3, 3)?;
        let sq = |acc: &mut Accumulator, a: i64, b: i64, rev: bool| -> Result<(), Error> {
            let mut c = [p(a, a), p(b, a), p(b, b), p(a, b)];
            if rev {
                c.reverse();
            }
            for (i, &a) in c.iter().enumerate() {
                let b = c.get(i.saturating_add(1)).unwrap_or(&c[0]);
                acc.line(a, *b)?;
            }
            Ok(())
        };
        sq(&mut acc, 0, 3 * o, false)?;
        sq(&mut acc, o, 2 * o, true)?;
        assert_eq!(acc.finish()?, [255, 255, 255, 255, 0, 255, 255, 255, 255]);
        Ok(())
    }

    #[test]
    fn clamped_outside_and_right_edge() -> Result<(), Error> {
        let o = ONE;
        // A square whose right edge lies on the mask's right edge: the
        // edge's cell is column `width`, outside the mask.
        assert_eq!(polygon(1, 1, &[(0, 0), (o, 0), (o, o), (0, o)])?, [255]);
        // Coordinates outside the mask are clamped, never indexed.
        let mut acc = Accumulator::new(1, 1)?;
        acc.line(p(i64::MIN, i64::MIN), p(i64::MAX, i64::MAX))?;
        acc.line(p(-5, 3), p(9 * o, -2))?;
        assert_eq!(acc.finish()?.len(), 1);
        Ok(())
    }

    #[test]
    fn coverage_scale() -> Result<(), Error> {
        assert_eq!(coverage(0)?, 0);
        assert_eq!(coverage(FULL)?, 255);
        assert_eq!(coverage(-FULL)?, 255);
        assert_eq!(coverage(3 * FULL)?, 255);
        assert_eq!(coverage(i64::MIN)?, 255);
        assert_eq!(coverage(FULL / 2)?, 128);
        // Just under half a level rounds down, half a level rounds up.
        assert_eq!(coverage(FULL / 510)?, 0);
        assert_eq!(coverage(FULL / 510 + 1)?, 1);
        Ok(())
    }

    #[test]
    fn x_at_is_exact_at_the_ends_and_floors() -> Result<(), Error> {
        let a = p(0, 0);
        let b = p(10, 3);
        assert_eq!(x_at(a, b, 0)?, 0);
        assert_eq!(x_at(a, b, 3)?, 10);
        assert_eq!(x_at(a, b, 1)?, 3);
        assert_eq!(x_at(b, a, 1)?, 3);
        let c = p(0, 3);
        let d = p(10, 0);
        // 10 − 10 × 1 ÷ 3 = 6.67, floored.
        assert_eq!(x_at(d, c, 1)?, 6);
        assert_eq!(x_at(c, d, 2)?, 3);
        assert_eq!(floor_div(-7, 2)?, -4);
        assert_eq!(floor_div(7, -2)?, -4);
        assert_eq!(floor_div(-7, -2)?, 3);
        Ok(())
    }

    #[test]
    fn set_cells_checks_the_length() -> Result<(), Error> {
        let mut acc = Accumulator::new(1, 1)?;
        assert!(!acc.set_cells(&[0; 2]));
        assert!(acc.set_cells(&[FULL, 0, 0]));
        assert_eq!(acc.cells(), [FULL, 0, 0]);
        assert_eq!(acc.finish()?, [255]);
        Ok(())
    }
}
