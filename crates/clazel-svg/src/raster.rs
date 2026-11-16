//! The rasterizer: a polygon (a list of [`Edge`]s in device space) filled
//! with the non-zero winding rule, anti-aliased, in integer arithmetic.
//!
//! Fill rule: SVG 2 section 13.4.2, the `fill-rule` property, whose initial
//! value is `nonzero`: a point is inside if a ray from it crosses the path
//! with a non-zero total of signed crossings (+1 for an edge going down,
//! -1 for one going up, in the rule's description).
//!
//! The method. A pixel row is sampled at [`SUB`] = 16 evenly spaced
//! scanlines, at `y + (2k + 1) / 32` for `k` in `0..16`. On each one, an edge
//! is crossed if `y_low <= sample < y_high` (half open, so two edges meeting
//! at a vertex count once); the crossings are sorted by `x`; walking them
//! left to right with the running winding number, every stretch between two
//! crossings where it is non-zero is inside. A stretch's coverage of each
//! pixel is exact horizontally (in 1/256 pixel) and the pixel's alpha is
//! the sum over the 16 scanlines, `round(255 * covered / 4096)`. The
//! stretches are added with a difference array (a stretch costs O(1), not
//! O(its width)), which a prefix sum along the row turns into coverage.
//!
//! The result is composited source-over onto straight RGBA ([`composite`]).

use crate::limits::{MAX_EDGES, SUB, UNIT};
use crate::path::Edge;
use clazel_image_shape::{Error, rgba_len};

/// The bytes of the accumulator for a row of `width` pixels: `width + 2`
/// entries of 4 bytes.
pub(crate) fn acc_len(width: u32) -> Option<usize> {
    usize::try_from(width).ok()?.checked_add(2)?.checked_mul(4)
}

/// Adds `delta` to entry `i` of the accumulator (little-endian `i32`s).
fn acc_add(acc: &mut [u8], i: usize, delta: i64) -> Option<()> {
    let at = i.checked_mul(4)?;
    let cell = acc.get_mut(at..at.checked_add(4)?)?;
    let old = i64::from(i32::from_le_bytes(cell.try_into().ok()?));
    let new = i32::try_from(old.checked_add(delta)?).ok()?;
    cell.copy_from_slice(&new.to_le_bytes());
    Some(())
}

fn acc_get(acc: &[u8], i: usize) -> Option<i64> {
    let at = i.checked_mul(4)?;
    let cell = acc.get(at..at.checked_add(4)?)?;
    Some(i64::from(i32::from_le_bytes(cell.try_into().ok()?)))
}

/// Adds `sign` times the function `F(x)` to the accumulator, where after a
/// prefix sum `F(x)` is, for each pixel `p`, the length in 1/256 pixel of
/// `[0, x)` inside pixel `p`: 256 for `p < x / 256`, `x % 256` at
/// `p = x / 256`, 0 after. A stretch `[a, b)` is then `F(b) - F(a)`.
/// `x` is in `0..=width * 256`.
fn add_f(acc: &mut [u8], x: i64, sign: i64) -> Option<()> {
    let px = usize::try_from(x.div_euclid(UNIT)).ok()?;
    let fr = x.rem_euclid(UNIT);
    acc_add(acc, 0, sign.checked_mul(UNIT)?)?;
    acc_add(acc, px, sign.checked_mul(fr.checked_sub(UNIT)?)?)?;
    acc_add(
        acc,
        px.checked_add(1)?,
        sign.checked_mul(fr.checked_neg()?)?,
    )
}

/// Adds the stretch `[a, b)` (1/256 pixel, clipped to the row).
pub(crate) fn add_span(acc: &mut [u8], width_units: i64, a: i64, b: i64) -> Option<()> {
    let a = a.clamp(0, width_units);
    let b = b.clamp(0, width_units);
    if b > a {
        add_f(acc, b, 1)?;
        add_f(acc, a, -1)?;
    }
    Some(())
}

/// The `x` (1/256 pixel) where `e` crosses the scanline `ys`, if it does,
/// with its direction: +1 if the edge goes down (y increases), -1 if up.
pub(crate) fn crossing(e: &Edge, ys: i64) -> Option<(i64, i64)> {
    let (x0, y0) = (i64::from(e.x0), i64::from(e.y0));
    let (x1, y1) = (i64::from(e.x1), i64::from(e.y1));
    let (dir, lo, hi) = match y0.cmp(&y1) {
        core::cmp::Ordering::Less => (1, y0, y1),
        core::cmp::Ordering::Greater => (-1, y1, y0),
        core::cmp::Ordering::Equal => return None,
    };
    if ys < lo || ys >= hi {
        return None;
    }
    // x0 + (ys - y0) * (x1 - x0) / (y1 - y0): the three differences are
    // below 2^31, so the product is below 2^62.
    let num = ys.checked_sub(y0)?.checked_mul(x1.checked_sub(x0)?)?;
    let x = x0.checked_add(num.checked_div(y1.checked_sub(y0)?)?)?;
    Some((x, dir))
}

/// One channel of source-over: `(s a 255 + d da (255 - a)) / oa255`, rounded
/// half up, where `oa255 = a 255 + da (255 - a)` (the result alpha times
/// 255): a weighted mean of `s` and `d`, so between them.
pub(crate) fn blend(s: u8, d: u8, a: u32, da: u32, oa255: u32) -> u8 {
    let inv = 255u32.saturating_sub(a);
    let n = u32::from(s)
        .saturating_mul(a)
        .saturating_mul(255)
        .saturating_add(u32::from(d).saturating_mul(da).saturating_mul(inv));
    let n = n.saturating_add(oa255 / 2);
    u8::try_from(n.checked_div(oa255).unwrap_or(0)).unwrap_or(255)
}

/// Source-over of an opaque colour with coverage `a` (alpha 0 to 255) onto
/// a straight RGBA pixel:
/// `out_a = a + dst_a (1 - a)`, `out_c = (c a + dst_c dst_a (1 - a)) / out_a`,
/// in integers, rounded half up. Coverage 0 leaves the pixel, 255 replaces
/// it.
pub(crate) fn composite(dst: [u8; 4], rgb: [u8; 3], a: u8) -> [u8; 4] {
    let [dr, dg, db, da] = dst;
    let [sr, sg, sb] = rgb;
    if a == 0 {
        return dst;
    }
    if a == 255 || da == 0 {
        return [sr, sg, sb, a];
    }
    let (a, da) = (u32::from(a), u32::from(da));
    let inv = 255u32.saturating_sub(a);
    // out_a * 255, at least a * 255 > 0.
    let oa255 = a.saturating_mul(255).saturating_add(da.saturating_mul(inv));
    let oa = u8::try_from(oa255.saturating_add(127).checked_div(255).unwrap_or(0)).unwrap_or(255);
    [
        blend(sr, dr, a, da, oa255),
        blend(sg, dg, a, da, oa255),
        blend(sb, db, a, da, oa255),
        oa,
    ]
}

/// One sample scanline `ys` (1/256 pixel): the stretches of it inside the
/// polygon, added to the accumulator. `Some(whether any stretch was
/// added)`, `None` only if `acc` is too short for the row (it never is when
/// called from [`fill`]).
///
/// Works for edges of any coordinates: a crossing whose arithmetic would
/// overflow is not a crossing ([`crossing`] checks it).
pub(crate) fn scanline(edges: &[Edge], ys: i64, width_units: i64, acc: &mut [u8]) -> Option<bool> {
    // The crossings of this scanline, sorted by x (insertion sort).
    let mut cross = [(0i64, 0i64); MAX_EDGES];
    let mut n = 0usize;
    for e in edges {
        let Some(c) = crossing(e, ys) else { continue };
        let slot = cross.get_mut(n)?;
        *slot = c;
        let mut j = n;
        n = n.saturating_add(1);
        while j > 0 {
            let (lo, hi) = (j.saturating_sub(1), j);
            let out_of_order = match (cross.get(lo), cross.get(hi)) {
                (Some(a), Some(b)) => a.0 > b.0,
                _ => false,
            };
            if !out_of_order {
                break;
            }
            cross.swap(lo, hi);
            j = lo;
        }
    }
    let used = cross.get(..n)?;
    let mut touched = false;
    let mut winding = 0i64;
    for (i, &(x, dir)) in used.iter().enumerate() {
        winding = winding.saturating_add(dir);
        if winding != 0
            && let Some(&(next, _)) = used.get(i.saturating_add(1))
        {
            touched = true;
            add_span(acc, width_units, x, next)?;
        }
    }
    Some(touched)
}

/// The accumulated row to pixels: a prefix sum along the row gives each
/// pixel's coverage (0 to 4096), then alpha, then the composite. `None` if
/// `acc` has fewer entries than the row has pixels.
pub(crate) fn resolve_row(acc: &[u8], row: &mut [u8], rgb: [u8; 3]) -> Option<()> {
    let mut running = 0i64;
    for (x, px) in row.as_chunks_mut::<4>().0.iter_mut().enumerate() {
        running = running.checked_add(acc_get(acc, x)?)?;
        let covered = running.clamp(0, FULL);
        let alpha = covered
            .saturating_mul(255)
            .saturating_add(FULL / 2)
            .checked_div(FULL)
            .unwrap_or(0);
        let alpha = u8::try_from(alpha).unwrap_or(255);
        if alpha > 0 {
            *px = composite(*px, rgb, alpha);
        }
    }
    Some(())
}

/// The coverage of a wholly covered pixel: 16 scanlines of 256.
const FULL: i64 = SUB.saturating_mul(UNIT);

/// Fills the polygon `edges` with `rgb` into `pixels` (straight RGBA8,
/// `width * height * 4` bytes), compositing over what is there. `acc` is
/// scratch of [`acc_len`]`(width)` bytes.
pub(crate) fn fill(
    edges: &[Edge],
    width: u32,
    height: u32,
    rgb: [u8; 3],
    pixels: &mut [u8],
    acc: &mut [u8],
) -> Result<(), Error> {
    let w = usize::try_from(width).map_err(|_| Error::Buffers)?;
    if acc.len() != acc_len(width).ok_or(Error::Buffers)?
        || pixels.len() != rgba_len(width, height)?
        || edges.len() > MAX_EDGES
    {
        return Err(Error::Buffers);
    }
    let width_units = i64::from(width).checked_mul(UNIT).ok_or(Error::Buffers)?;
    let step = UNIT.checked_div(SUB).ok_or(Error::Buffers)?;
    let row_bytes = w.checked_mul(4).ok_or(Error::Buffers)?;
    let mut rows = pixels.chunks_exact_mut(row_bytes.max(1));
    for y in 0..height {
        let row = rows.next().ok_or(Error::Buffers)?;
        acc.fill(0);
        let mut touched = false;
        for k in 0..SUB {
            let ys = i64::from(y)
                .checked_mul(UNIT)
                .and_then(|v| v.checked_add(k.checked_mul(step)?))
                .and_then(|v| v.checked_add(step / 2))
                .ok_or(Error::Buffers)?;
            touched |= scanline(edges, ys, width_units, acc).ok_or(Error::Buffers)?;
        }
        if touched {
            resolve_row(acc, row, rgb).ok_or(Error::Buffers)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn edge(x0: i32, y0: i32, x1: i32, y1: i32) -> Edge {
        Edge { x0, y0, x1, y1 }
    }

    /// A rectangle `[x0, x1) x [y0, y1)` in pixels, as 4 edges in 1/256.
    fn rect(x0: i32, y0: i32, x1: i32, y1: i32) -> Vec<Edge> {
        let u = |v: i32| v.saturating_mul(256);
        let (x0, y0, x1, y1) = (u(x0), u(y0), u(x1), u(y1));
        vec![
            edge(x0, y0, x1, y0),
            edge(x1, y0, x1, y1),
            edge(x1, y1, x0, y1),
            edge(x0, y1, x0, y0),
        ]
    }

    fn paint(edges: &[Edge], w: u32, h: u32, rgb: [u8; 3], px: &mut [u8]) -> Result<(), Error> {
        let mut acc = vec![0u8; acc_len(w).ok_or(Error::Buffers)?];
        fill(edges, w, h, rgb, px, &mut acc)
    }

    #[test]
    fn composite_cases() {
        assert_eq!(composite([1, 2, 3, 4], [9, 9, 9], 0), [1, 2, 3, 4]);
        assert_eq!(composite([1, 2, 3, 4], [9, 8, 7], 255), [9, 8, 7, 255]);
        assert_eq!(composite([0, 0, 0, 0], [9, 8, 7], 100), [9, 8, 7, 100]);
        // Half white over opaque black: 50% grey, opaque.
        assert_eq!(
            composite([0, 0, 0, 255], [255, 255, 255], 128),
            [128, 128, 128, 255]
        );
        // Same colour at any coverage keeps the colour.
        for a in 1..=255u8 {
            assert_eq!(
                composite([10, 20, 30, 200], [10, 20, 30], a).get(..3),
                Some(&[10, 20, 30][..])
            );
        }
    }

    #[test]
    fn whole_pixels_are_exact() -> Result<(), Error> {
        let mut px = vec![0u8; 4 * 4 * 3];
        paint(&rect(1, 1, 3, 2), 4, 3, [255, 102, 0], &mut px)?;
        for y in 0..3usize {
            for x in 0..4usize {
                let i = (y * 4 + x) * 4;
                let want: [u8; 4] = if (1..3).contains(&x) && y == 1 {
                    [255, 102, 0, 255]
                } else {
                    [0, 0, 0, 0]
                };
                assert_eq!(px.get(i..i + 4), Some(&want[..]), "{x},{y}");
            }
        }
        Ok(())
    }

    #[test]
    fn half_covered_pixels() -> Result<(), Error> {
        // A rectangle covering the left half of pixel 0 and the top half
        // of the row: x 0..128, y 0..128 in 1/256: a quarter.
        let mut px = vec![0u8; 4];
        let e = [
            edge(0, 0, 128, 0),
            edge(128, 0, 128, 128),
            edge(128, 128, 0, 128),
            edge(0, 128, 0, 0),
        ];
        paint(&e, 1, 1, [255, 255, 255], &mut px)?;
        // 8 of 16 scanlines, half of the width: 1024 / 4096 of the pixel.
        assert_eq!(px, vec![255, 255, 255, 64]);
        Ok(())
    }

    #[test]
    fn non_zero_not_even_odd() -> Result<(), Error> {
        // Two nested squares with the same direction: the inner one has
        // winding 2, which is filled under non-zero (even-odd leaves a hole).
        let mut e = rect(0, 0, 6, 6);
        e.extend(rect(2, 2, 4, 4));
        let mut px = vec![0u8; 6 * 6 * 4];
        paint(&e, 6, 6, [1, 2, 3], &mut px)?;
        assert_eq!(
            px.get(((3 * 6) + 3) * 4..((3 * 6) + 3) * 4 + 4),
            Some(&[1, 2, 3, 255][..])
        );
        // Opposite direction: winding 0, a hole.
        let mut e = rect(0, 0, 6, 6);
        e.extend(
            rect(2, 2, 4, 4)
                .iter()
                .rev()
                .map(|e| edge(e.x1, e.y1, e.x0, e.y0)),
        );
        let mut px = vec![0u8; 6 * 6 * 4];
        paint(&e, 6, 6, [1, 2, 3], &mut px)?;
        assert_eq!(
            px.get(((3 * 6) + 3) * 4..((3 * 6) + 3) * 4 + 4),
            Some(&[0, 0, 0, 0][..])
        );
        assert_eq!(px.get(4..8), Some(&[1, 2, 3, 255][..]));
        Ok(())
    }

    #[test]
    fn shapes_outside_the_image_are_clipped() -> Result<(), Error> {
        let mut px = vec![0u8; 2 * 2 * 4];
        paint(&rect(-50, -50, 50, 50), 2, 2, [7, 7, 7], &mut px)?;
        assert!(px.chunks(4).all(|p| p == [7, 7, 7, 255]));
        let mut px = vec![0u8; 2 * 2 * 4];
        paint(&rect(10, 10, 20, 20), 2, 2, [7, 7, 7], &mut px)?;
        assert!(px.iter().all(|&b| b == 0));
        Ok(())
    }

    #[test]
    fn buffers_must_fit() {
        let mut px = vec![0u8; 3];
        assert_eq!(paint(&[], 1, 1, [0; 3], &mut px), Err(Error::Buffers));
    }
}
