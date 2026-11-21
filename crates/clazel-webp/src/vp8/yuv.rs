//! YUV 4:2:0 to RGBA, a **listed choice** because RFC 6386 does not define
//! it: section 9.2 says the colour space is "YUV color space similar to the
//! YCrCb color space defined in [ITU-R_BT.601]" and nothing of how a decoder
//! turns the planes into RGB or upsamples the chroma. This is what libwebp's
//! `dwebp` does by default, the conversion every WebP-capable browser shows:
//!
//! - **The conversion** (libwebp `src/dsp/yuv.h`, `VP8YUVToR`, `VP8YUVToG`,
//!   `VP8YUVToB`, with `YUV_FIX2` = 6): in fixed point,
//!   `MultHi(v, c) = (v * c) >> 8`, then
//!   `R = Clip8(MultHi(Y, 19077) + MultHi(V, 26149) - 14234)`,
//!   `G = Clip8(MultHi(Y, 19077) - MultHi(U, 6419) - MultHi(V, 13320) + 8708)`,
//!   `B = Clip8(MultHi(Y, 19077) + MultHi(U, 33050) - 17685)`, where `Clip8`
//!   is `v >> 6` for `0 <= v < 2^14` and 0 or 255 outside it. (These
//!   constants are limited-range BT.601: Y 16 to 235 to 0 to 255.)
//! - **"Fancy" upsampling** of the chroma (libwebp `src/dsp/upsampling.c`,
//!   `UpsampleRgbaLinePair`, the default of `dwebp` and of browsers): the
//!   chroma sample of an output pixel is `(9 a + 3 b + 3 c + d + 8) >> 4`,
//!   where `a` is the nearest chroma sample, `b` the one next to it along the
//!   row on the pixel's side, `c` the one next to it along the column on the
//!   side of the pixel's row, and `d` the diagonal one; at the edges the
//!   missing sample is the nearest one (libwebp's "mirror"). Output row 0
//!   and, for an even height, the last row, have only one chroma row (so
//!   `c` = `a` and `d` = `b`).
//!
//! The alpha channel is the `ALPH` plane or 255, straight (not
//! premultiplied).

use super::plane::Plane;

/// `MultHi`.
fn mult_hi(v: i32, coeff: i32) -> i32 {
    v.wrapping_mul(coeff) >> 8
}

/// `VP8Clip8`: "if v is in 0 to 2^14 - 1 then v >> 6, else 0 or 255".
fn clip8(v: i32) -> u8 {
    if v < 0 {
        0
    } else if v > 16383 {
        255
    } else {
        (v >> 6) as u8
    }
}

/// `VP8YUVToR`, `VP8YUVToG`, `VP8YUVToB`.
pub(crate) fn yuv_to_rgb(y: u8, u: u8, v: u8) -> [u8; 3] {
    let (y, u, v) = (i32::from(y), i32::from(u), i32::from(v));
    let luma = mult_hi(y, 19077);
    [
        clip8(luma.wrapping_add(mult_hi(v, 26149)).wrapping_sub(14234)),
        clip8(
            luma.wrapping_sub(mult_hi(u, 6419))
                .wrapping_sub(mult_hi(v, 13320))
                .wrapping_add(8708),
        ),
        clip8(luma.wrapping_add(mult_hi(u, 33050)).wrapping_sub(17685)),
    ]
}

/// The fancy-upsampling weights: `(9 a + 3 b + 3 c + d + 8) >> 4`.
fn fancy(a: u8, b: u8, c: u8, d: u8) -> u8 {
    let s = 9u32
        .wrapping_mul(u32::from(a))
        .wrapping_add(3u32.wrapping_mul(u32::from(b)))
        .wrapping_add(3u32.wrapping_mul(u32::from(c)))
        .wrapping_add(u32::from(d))
        .wrapping_add(8);
    (s >> 4) as u8
}

/// The nearest chroma row and the other one used for output row `r` of an
/// image whose chroma has `chroma_rows` rows: row 0 has only chroma row 0;
/// row `2k + 1` is nearest to chroma row `k` and next to `k + 1` (or only
/// `k` if that is the last); row `2k` (k >= 1) is nearest to `k` and next to
/// `k - 1`.
fn chroma_rows(r: usize, chroma_rows: usize) -> (usize, usize) {
    let k = r >> 1;
    if r == 0 {
        (0, 0)
    } else if r & 1 == 1 {
        let far = k.saturating_add(1);
        (k, if far < chroma_rows { far } else { k })
    } else {
        (k, k.saturating_sub(1))
    }
}

/// Converts the planes (`width` by `height` pixels of luma, half of that,
/// rounded up, of each chroma) to RGBA in `out` (`4 * width * height` bytes),
/// with `alpha` (`width * height` bytes) or 255. `None` if `out`, `alpha` or
/// a plane is too short.
pub(crate) fn to_rgba(
    y: &Plane<'_>,
    u: &Plane<'_>,
    v: &Plane<'_>,
    width: usize,
    height: usize,
    alpha: Option<&[u8]>,
    out: &mut [u8],
) -> Option<()> {
    let pixels = width.checked_mul(height)?;
    let out = out.get_mut(..pixels.checked_mul(4)?)?;
    let alpha = match alpha {
        Some(a) => Some(a.get(..pixels)?),
        None => None,
    };
    let chroma_w = width.div_ceil(2);
    let chroma_h = height.div_ceil(2);
    if y.stride() < width || u.stride() < chroma_w || v.stride() < chroma_w {
        return None;
    }
    let mut dst = out.as_chunks_mut::<4>().0.iter_mut();
    let mut index = 0usize;
    for r in 0..height {
        let (near, far) = chroma_rows(r, chroma_h);
        for x in 0..width {
            let cx = x >> 1;
            // The neighbour along the row, on the side of the pixel.
            let adj = if x & 1 == 0 {
                cx.saturating_sub(1)
            } else {
                cx.saturating_add(1).min(chroma_w.saturating_sub(1))
            };
            let up = fancy(
                u.at(cx, near),
                u.at(adj, near),
                u.at(cx, far),
                u.at(adj, far),
            );
            let vp = fancy(
                v.at(cx, near),
                v.at(adj, near),
                v.at(cx, far),
                v.at(adj, far),
            );
            let [red, green, blue] = yuv_to_rgb(y.at(x, r), up, vp);
            let a = alpha.and_then(|a| a.get(index)).copied().unwrap_or(255);
            let px = dst.next()?;
            *px = [red, green, blue, a];
            index = index.saturating_add(1);
        }
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn black_white_grey() {
        // Limited range: Y 16 is black, 235 white.
        assert_eq!(yuv_to_rgb(16, 128, 128), [0, 0, 0]);
        assert_eq!(yuv_to_rgb(235, 128, 128), [255, 255, 255]);
        let [r, g, b] = yuv_to_rgb(126, 128, 128);
        assert!(r.abs_diff(g) <= 1 && g.abs_diff(b) <= 1);
        // Saturation at both ends.
        assert_eq!(yuv_to_rgb(0, 128, 128), [0, 0, 0]);
        assert_eq!(yuv_to_rgb(255, 128, 128), [255, 255, 255]);
    }

    #[test]
    fn chroma_row_rule() {
        // Height 5: three chroma rows.
        let rows: Vec<_> = (0..5).map(|r| chroma_rows(r, 3)).collect();
        assert_eq!(rows, [(0, 0), (0, 1), (1, 0), (1, 2), (2, 1)]);
        // Height 4: two chroma rows; the last row has only chroma row 1.
        let rows: Vec<_> = (0..4).map(|r| chroma_rows(r, 2)).collect();
        assert_eq!(rows, [(0, 0), (0, 1), (1, 0), (1, 1)]);
    }

    #[test]
    fn flat_chroma_is_flat() {
        // A flat chroma plane upsamples to itself (the weights sum to 16).
        for v in [0u8, 1, 127, 128, 254, 255] {
            assert_eq!(fancy(v, v, v, v), v);
        }
    }
}
