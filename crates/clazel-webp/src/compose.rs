//! Putting a frame on the canvas: alpha blending (RFC 9649 section 2.7.1.1,
//! "Blending method" and the formula in its notes).

use crate::transform::{Px, put, px};

/// Blends `src` over `dst`, neither premultiplied (the formula of
/// section 2.7.1.1: `blend.A = src.A + dst.A * (1 - src.A / 255)`, and the
/// colours weighted by their alphas, divided by `blend.A`).
///
/// Integer arithmetic, listed choices:
/// - a source alpha of 0 gives `dst`, of 255 gives `src`, and a destination
///   alpha of 0 gives `src` (all exact in the formula);
/// - otherwise libwebp's (`anim_decode.c`, `BlendPixelNonPremult`):
///   `dst_factor = dst.A * (256 - src.A) >> 8`, `blend.A = src.A +
///   dst_factor`, `scale = 2^24 / blend.A`, and each colour channel
///   `(src * src.A + dst * dst_factor) * scale >> 24`.
///
/// The RFC says blending "SHOULD be done in linear color space"; browsers
/// (libwebp) do it on the stored values, as here.
pub(crate) fn blend_px(src: Px, dst: Px) -> Px {
    let [sr, sg, sb, sa] = src;
    let [dr, dg, db, da] = dst;
    if sa == 0 {
        return dst;
    }
    if sa == 255 || da == 0 {
        return src;
    }
    let sa = u32::from(sa);
    let factor = u32::from(da).wrapping_mul(256u32.wrapping_sub(sa)) >> 8;
    let blend_a = sa.wrapping_add(factor).clamp(1, 255);
    let scale = (1u32 << 24).checked_div(blend_a).unwrap_or(0);
    let channel = |s: u8, d: u8| -> u8 {
        let sum = u32::from(s)
            .wrapping_mul(sa)
            .wrapping_add(u32::from(d).wrapping_mul(factor));
        u8::try_from(sum.wrapping_mul(scale) >> 24).unwrap_or(255)
    };
    [
        channel(sr, dr),
        channel(sg, dg),
        channel(sb, db),
        u8::try_from(blend_a).unwrap_or(255),
    ]
}

/// Blends each pixel of `src` over the pixel of `dst` at the same place (as
/// many pixels as the shorter of the two holds).
pub(crate) fn blend_row(dst: &mut [u8], src: &[u8]) {
    for i in 0..src.len() / 4 {
        let b = blend_px(px(src, i), px(dst, i));
        put(dst, i, b);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extremes() {
        let dst = [10, 20, 30, 200];
        assert_eq!(blend_px([1, 2, 3, 0], dst), dst);
        assert_eq!(blend_px([1, 2, 3, 255], dst), [1, 2, 3, 255]);
        assert_eq!(blend_px([7, 8, 9, 100], [0, 0, 0, 0]), [7, 8, 9, 100]);
    }

    #[test]
    fn half_over_opaque() {
        // 50% white over opaque black: alpha stays 255 (128 + 255 * 128 >>
        // 8 = 128 + 127), colour 255 * 128 * scale >> 24 about 128.
        let out = blend_px([255, 255, 255, 128], [0, 0, 0, 255]);
        assert_eq!(out[3], 255);
        assert!((127..=128).contains(&out[0]));
        assert_eq!(out[0], out[1]);
    }

    #[test]
    fn never_exceeds() {
        for sa in [1u8, 2, 3, 100, 254] {
            for da in [1u8, 128, 255] {
                let out = blend_px([255, 255, 255, sa], [255, 255, 255, da]);
                assert!(out[0] >= 254, "{sa} {da} {out:?}");
            }
        }
    }
}
