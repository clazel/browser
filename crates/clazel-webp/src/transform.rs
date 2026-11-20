//! The inverse transforms of VP8L (RFC 9649 section 3.5), one row at a time,
//! in place on a pixel buffer of RGBA bytes.
//!
//! A pixel is 4 bytes in the order red, green, blue, alpha (the order of the
//! output, so no reordering at the end); the RFC's ARGB value of a pixel is
//! alpha, red, green, blue from the high byte down, and a channel is 8 bits
//! whatever the order, so every transform here is written per channel.
//!
//! Every function indexes with checked operations only; a position outside
//! the buffer leaves the buffer alone and the function returns `false`
//! (callers size the buffers so that does not happen; the Kani harnesses
//! prove it does not panic for any inputs).

/// A pixel: red, green, blue, alpha.
pub(crate) type Px = [u8; 4];

/// Opaque black: RFC 9649 section 3.5.1, mode 0's "0xff000000".
pub(crate) const BLACK: Px = [0, 0, 0, 255];

/// Pixel `i` of `buf` (transparent black if it is not there).
pub(crate) fn px(buf: &[u8], i: usize) -> Px {
    i.checked_mul(4)
        .and_then(|o| buf.get(o..o.checked_add(4)?))
        .and_then(|s| Px::try_from(s).ok())
        .unwrap_or([0; 4])
}

/// Sets pixel `i` of `buf`; false if it is not there.
pub(crate) fn put(buf: &mut [u8], i: usize, p: Px) -> bool {
    let slot = i
        .checked_mul(4)
        .and_then(|o| buf.get_mut(o..o.checked_add(4)?));
    match slot {
        Some(d) => {
            d.copy_from_slice(&p);
            true
        }
        None => false,
    }
}

/// The channels of `a` plus those of `b`, each modulo 256.
fn add_px(a: Px, b: Px) -> Px {
    let [a0, a1, a2, a3] = a;
    let [b0, b1, b2, b3] = b;
    [
        a0.wrapping_add(b0),
        a1.wrapping_add(b1),
        a2.wrapping_add(b2),
        a3.wrapping_add(b3),
    ]
}

/// Section 3.5.1's `Average2` of one channel: `(a + b) / 2`, without the
/// intermediate overflow.
fn avg(a: u8, b: u8) -> u8 {
    (a & b).wrapping_add((a ^ b) >> 1)
}

/// `Average2` on every channel.
pub(crate) fn avg2(a: Px, b: Px) -> Px {
    let [a0, a1, a2, a3] = a;
    let [b0, b1, b2, b3] = b;
    [avg(a0, b0), avg(a1, b1), avg(a2, b2), avg(a3, b3)]
}

/// Section 3.5.1's `Clamp`.
fn clamp(v: i32) -> u8 {
    u8::try_from(v.clamp(0, 255)).unwrap_or(0)
}

/// The channels of two pixels, paired.
fn zip(a: Px, b: Px) -> impl Iterator<Item = (i32, i32)> {
    a.into_iter()
        .zip(b)
        .map(|(x, y)| (i32::from(x), i32::from(y)))
}

/// Section 3.5.1's `Select(L, T, TL)`: the one of L and T nearer, in the
/// sum of the channels' differences, to `L + T - TL`; T on a tie.
pub(crate) fn select(l: Px, t: Px, tl: Px) -> Px {
    let mut p_l: i32 = 0;
    let mut p_t: i32 = 0;
    for ((lc, tc), tlc) in zip(l, t).zip(tl.into_iter().map(i32::from)) {
        let p = lc.wrapping_add(tc).wrapping_sub(tlc);
        p_l = p_l.wrapping_add(p.wrapping_sub(lc).abs());
        p_t = p_t.wrapping_add(p.wrapping_sub(tc).abs());
    }
    if p_l < p_t { l } else { t }
}

/// `ClampAddSubtractFull(a, b, c)` on every channel: `Clamp(a + b - c)`.
fn clamp_add_sub_full(a: Px, b: Px, c: Px) -> Px {
    let mut out = [0u8; 4];
    for (o, ((x, y), z)) in out
        .iter_mut()
        .zip(zip(a, b).zip(c.into_iter().map(i32::from)))
    {
        *o = clamp(x.wrapping_add(y).wrapping_sub(z));
    }
    out
}

/// `ClampAddSubtractHalf(a, b)` on every channel: `Clamp(a + (a - b) / 2)`,
/// the division truncating toward zero as in C.
fn clamp_add_sub_half(a: Px, b: Px) -> Px {
    let mut out = [0u8; 4];
    for (o, (x, y)) in out.iter_mut().zip(zip(a, b)) {
        *o = clamp(x.wrapping_add(x.wrapping_sub(y) / 2));
    }
    out
}

/// The predicted value of mode `mode` (section 3.5.1, Table 2) from the
/// left, top, top-right and top-left pixels. Modes 14 and 15, which the RFC
/// does not define, predict like mode 0 (a listed choice: libwebp's).
pub(crate) fn predict(mode: u8, l: Px, t: Px, tr: Px, tl: Px) -> Px {
    match mode & 15 {
        1 => l,
        2 => t,
        3 => tr,
        4 => tl,
        5 => avg2(avg2(l, tr), t),
        6 => avg2(l, tl),
        7 => avg2(l, t),
        8 => avg2(tl, t),
        9 => avg2(t, tr),
        10 => avg2(avg2(l, tl), avg2(t, tr)),
        11 => select(l, t, tl),
        12 => clamp_add_sub_full(l, t, tl),
        13 => clamp_add_sub_half(avg2(l, t), tl),
        _ => BLACK,
    }
}

/// `x >> bits`, 0 if `bits` is not a shift.
fn shr(x: usize, bits: u8) -> usize {
    x.checked_shr(u32::from(bits)).unwrap_or(0)
}

/// The inverse predictor transform of row `y` of an image `w` pixels wide
/// (section 3.5.1). `buf` holds the image, rows before `y` already inverted;
/// `modes` is the predictor image, `bw` blocks of `1 << bits` pixels per row,
/// the mode of a block in its pixel's green byte.
///
/// The border rules (section 3.5.1): the top-left pixel is predicted
/// 0xff000000, the rest of the top row by L, and the rest of the left column
/// by T. The rightmost pixel's top-right neighbour is the leftmost pixel of
/// its own row, which is where the linear position `i - w + 1` falls.
pub(crate) fn predictor_row(
    buf: &mut [u8],
    w: usize,
    y: usize,
    bits: u8,
    bw: usize,
    modes: &[u8],
) -> bool {
    predictor_row_checked(buf, w, y, bits, bw, modes).is_some()
}

fn predictor_row_checked(
    buf: &mut [u8],
    w: usize,
    y: usize,
    bits: u8,
    bw: usize,
    modes: &[u8],
) -> Option<()> {
    let row = y.checked_mul(w)?;
    for x in 0..w {
        let i = row.checked_add(x)?;
        let pred = if y == 0 {
            if x == 0 {
                BLACK
            } else {
                px(buf, i.checked_sub(1)?)
            }
        } else if x == 0 {
            px(buf, i.checked_sub(w)?)
        } else {
            let block = shr(y, bits).checked_mul(bw)?.checked_add(shr(x, bits))?;
            let mode = px(modes, block).get(1).copied().unwrap_or(0);
            let up = i.checked_sub(w)?;
            predict(
                mode,
                px(buf, i.checked_sub(1)?),
                px(buf, up),
                px(buf, up.checked_add(1)?),
                px(buf, up.checked_sub(1)?),
            )
        };
        let sum = add_px(px(buf, i), pred);
        if !put(buf, i, sum) {
            return None;
        }
    }
    Some(())
}

/// Section 3.5.2's `ColorTransformDelta(t, c)`: `(t * c) >> 5` for the
/// signed 8-bit values, modulo 256.
fn delta(t: u8, c: u8) -> u8 {
    let p = i32::from(i8::from_ne_bytes([t])).wrapping_mul(i32::from(i8::from_ne_bytes([c])));
    u8::try_from((p >> 5) & 0xFF).unwrap_or(0)
}

/// The inverse colour transform of row `y` of an image `w` pixels wide
/// (section 3.5.2): red gains the green-to-red delta, blue the green-to-blue
/// delta of the green and the red-to-blue delta of the **new** red. `elems`
/// is the colour transform image: per block, red is `red_to_blue`, green
/// `green_to_blue`, blue `green_to_red`.
pub(crate) fn color_row(
    buf: &mut [u8],
    w: usize,
    y: usize,
    bits: u8,
    bw: usize,
    elems: &[u8],
) -> bool {
    color_row_checked(buf, w, y, bits, bw, elems).is_some()
}

fn color_row_checked(
    buf: &mut [u8],
    w: usize,
    y: usize,
    bits: u8,
    bw: usize,
    elems: &[u8],
) -> Option<()> {
    let row = y.checked_mul(w)?;
    for x in 0..w {
        let i = row.checked_add(x)?;
        let block = shr(y, bits).checked_mul(bw)?.checked_add(shr(x, bits))?;
        let [red_to_blue, green_to_blue, green_to_red, _] = px(elems, block);
        let [r, g, b, a] = px(buf, i);
        let new_r = r.wrapping_add(delta(green_to_red, g));
        let new_b = b
            .wrapping_add(delta(green_to_blue, g))
            .wrapping_add(delta(red_to_blue, new_r));
        if !put(buf, i, [new_r, g, new_b, a]) {
            return None;
        }
    }
    Some(())
}

/// The inverse subtract green transform of row `y` of an image `w` wide
/// (section 3.5.3): red and blue gain the green.
pub(crate) fn green_row(buf: &mut [u8], w: usize, y: usize) -> bool {
    let Some(row) = y.checked_mul(w) else {
        return false;
    };
    for x in 0..w {
        let Some(i) = row.checked_add(x) else {
            return false;
        };
        let [r, g, b, a] = px(buf, i);
        if !put(buf, i, [r.wrapping_add(g), g, b.wrapping_add(g), a]) {
            return false;
        }
    }
    true
}

/// The pixel bundling width of a colour table of `n` entries (section
/// 3.5.4, Table 3): `width_bits` 3, 2, 1 or 0.
pub(crate) fn bundle_bits(n: usize) -> u8 {
    match n {
        0..=2 => 3,
        3..=4 => 2,
        5..=16 => 1,
        _ => 0,
    }
}

/// Expands one row of the colour indexing transform (section 3.5.4): the
/// `w` pixels of the row come from the packed row that starts at pixel
/// `src`, written to the row that starts at pixel `dst`; `table` holds
/// `n` colours (4 bytes each), and an index of `n` or more gives
/// transparent black. Pixels are produced from the last to the first and
/// each reads only packed pixels at or before its own position, so with
/// `dst >= src` the row can be expanded in place (rows from the last to the
/// first).
pub(crate) fn palette_row(
    buf: &mut [u8],
    src: usize,
    dst: usize,
    w: usize,
    bits: u8,
    table: &[u8],
    n: usize,
) -> bool {
    palette_row_checked(buf, src, dst, w, bits, table, n).is_some()
}

fn palette_row_checked(
    buf: &mut [u8],
    src: usize,
    dst: usize,
    w: usize,
    bits: u8,
    table: &[u8],
    n: usize,
) -> Option<()> {
    // `1 << bits` pixels per packed pixel, each `8 >> bits` bits wide.
    let per = 1usize.checked_shl(u32::from(bits))?;
    let width = 8usize.checked_shr(u32::from(bits))?;
    let mask = 1usize
        .checked_shl(u32::try_from(width).ok()?)?
        .checked_sub(1)?;
    for x in (0..w).rev() {
        let packed = px(buf, src.checked_add(shr(x, bits))?);
        let g = usize::from(packed.get(1).copied().unwrap_or(0));
        let slot = x.checked_rem(per)?.checked_mul(width)?;
        let index = g.checked_shr(u32::try_from(slot).ok()?)? & mask;
        let colour = if index < n { px(table, index) } else { [0; 4] };
        if !put(buf, dst.checked_add(x)?, colour) {
            return None;
        }
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn averages() {
        assert_eq!(avg(255, 254), 254);
        assert_eq!(avg(1, 2), 1);
        assert_eq!(avg2([0, 10, 20, 255], [2, 11, 20, 255]), [1, 10, 20, 255]);
    }

    #[test]
    fn select_ties_go_to_top() {
        // L == T: both distances equal, T.
        assert_eq!(
            select([1, 2, 3, 4], [1, 2, 3, 4], [0, 0, 0, 0]),
            [1, 2, 3, 4]
        );
        // T == TL: p == L, so L is at distance 0 and T is not.
        assert_eq!(
            select([9, 9, 9, 9], [5, 5, 5, 5], [5, 5, 5, 5]),
            [9, 9, 9, 9]
        );
        // L == TL: p == T: T closer.
        assert_eq!(
            select([5, 5, 5, 5], [9, 9, 9, 9], [5, 5, 5, 5]),
            [9, 9, 9, 9]
        );
    }

    #[test]
    fn clamps() {
        assert_eq!(clamp_add_sub_full([250; 4], [250; 4], [0; 4]), [255; 4]);
        assert_eq!(clamp_add_sub_full([0; 4], [0; 4], [9; 4]), [0; 4]);
        // a + (a - b) / 2 with a - b = -3 truncates to -1.
        assert_eq!(clamp_add_sub_half([10; 4], [13; 4]), [9; 4]);
        assert_eq!(clamp_add_sub_half([10; 4], [14; 4]), [8; 4]);
    }

    #[test]
    fn colour_delta() {
        // 3.5 fixed point: t = 32 is 1.0, so delta(32, c) = c for a signed c.
        assert_eq!(delta(32, 7), 7);
        assert_eq!(delta(32, 0xFF), 0xFF);
        assert_eq!(delta(0xE0, 8), 0xF8);
    }

    #[test]
    fn predictor_borders() {
        // 3 wide, 2 high, all residuals 1; mode 0 everywhere (black).
        let mut buf = vec![1u8; 24];
        let modes = [0u8; 4];
        assert!(predictor_row(&mut buf, 3, 0, 2, 1, &modes));
        assert!(predictor_row(&mut buf, 3, 1, 2, 1, &modes));
        // Top-left: 1 + black = [1, 1, 1, 0] (alpha 255 + 1 wraps).
        assert_eq!(px(&buf, 0), [1, 1, 1, 0]);
        // The rest of the top row: L + residual.
        assert_eq!(px(&buf, 1), [2, 2, 2, 1]);
        // Left column: T + residual.
        assert_eq!(px(&buf, 3), [2, 2, 2, 1]);
    }

    #[test]
    fn rightmost_top_right_is_the_row_start() {
        // Mode 3 (TR) on row 1 of a 2-wide image: the pixel at x = 1 takes
        // the pixel at (0, 1), the first of its own row.
        let mut buf = vec![0u8; 16];
        put(&mut buf, 2, [10, 20, 30, 40]);
        put(&mut buf, 3, [0, 0, 0, 0]);
        let modes = [0u8, 3, 0, 0];
        assert!(predictor_row(&mut buf, 2, 1, 2, 1, &modes));
        assert_eq!(px(&buf, 3), [10, 20, 30, 40]);
    }

    #[test]
    fn colour_and_green() {
        let mut buf = vec![0u8; 4];
        put(&mut buf, 0, [10, 20, 30, 40]);
        assert!(green_row(&mut buf, 1, 0));
        assert_eq!(px(&buf, 0), [30, 20, 50, 40]);
        // green_to_red = 32 (1.0), green_to_blue = 0, red_to_blue = 32.
        let elems = [32u8, 0, 32, 255];
        put(&mut buf, 0, [10, 20, 30, 40]);
        assert!(color_row(&mut buf, 1, 0, 2, 1, &elems));
        // red 10 + 20 = 30; blue 30 + 0 + delta(32, 30) = 60.
        assert_eq!(px(&buf, 0), [30, 20, 60, 40]);
    }

    #[test]
    fn palette_expansion() {
        let table: Vec<u8> = (0..4u8).flat_map(|i| [i, i, i, 255]).collect();
        // 2 bits per index (4 colours, bundle bits 2): packed green 0b11_10_01_00.
        let mut buf = vec![0u8; 16];
        put(&mut buf, 0, [0, 0b1110_0100, 0, 255]);
        assert!(palette_row(&mut buf, 0, 0, 4, 2, &table, 4));
        for x in 0..4u8 {
            assert_eq!(px(&buf, usize::from(x)), [x, x, x, 255]);
        }
        // An index past the table is transparent black.
        let mut buf = vec![0u8; 16];
        put(&mut buf, 0, [0, 0b1110_0100, 0, 255]);
        assert!(palette_row(&mut buf, 0, 0, 4, 2, &table, 3));
        assert_eq!(px(&buf, 3), [0; 4]);
        assert_eq!(bundle_bits(2), 3);
        assert_eq!(bundle_bits(17), 0);
    }
}
