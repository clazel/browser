//! Premultiplication: straight RGBA8 to premultiplied RGBA8.
//!
//! Each colour channel `c` of a pixel with alpha `a` becomes
//! `round(c * a / 255)`. Ties cannot occur (`c * a / 255` has a fractional
//! part of exactly one half only if `255` were even), so `(c * a + 127) / 255`
//! is the rounding, exactly (`floor((2x + 254) / 510)` and
//! `floor((2x + 255) / 510)` agree because `2x + 255` is odd, never a
//! multiple of 510). Alpha is unchanged. The result is at most `c` and at
//! most `a`; `a = 255` is the identity and `a = 0` gives black.

/// Premultiplies one channel.
pub(crate) fn channel(c: u8, a: u8) -> u8 {
    // At most 255 * 255 + 127 = 65,152: no saturation happens; the bound
    // is what the Kani harness `premultiply_channel_any` proves.
    let x = u32::from(c)
        .saturating_mul(u32::from(a))
        .saturating_add(127);
    u8::try_from(x / 255).unwrap_or(u8::MAX)
}

/// One straight RGBA pixel to premultiplied.
pub fn premultiply(pixel: [u8; 4]) -> [u8; 4] {
    let [r, g, b, a] = pixel;
    [channel(r, a), channel(g, a), channel(b, a), a]
}

/// Premultiplies every pixel of `pixels` in place. A trailing partial pixel
/// (a length not a multiple of 4; never one from [`crate::Buffers`]) is left
/// as it is.
pub fn premultiply_in_place(pixels: &mut [u8]) {
    for px in pixels.as_chunks_mut::<4>().0 {
        *px = premultiply(*px);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_values() {
        assert_eq!(premultiply([10, 20, 30, 255]), [10, 20, 30, 255]);
        assert_eq!(premultiply([10, 20, 30, 0]), [0, 0, 0, 0]);
        assert_eq!(premultiply([255, 255, 255, 128]), [128, 128, 128, 128]);
        assert_eq!(premultiply([255, 0, 100, 1]), [1, 0, 0, 1]);
        assert_eq!(premultiply([200, 100, 50, 127]), [100, 50, 25, 127]);
    }

    #[test]
    fn equals_exact_rounding_everywhere() {
        for c in 0..=255u32 {
            for a in 0..=255u32 {
                // round(c * a / 255), half up, from the rational value.
                let want = (2 * c * a + 255) / 510;
                assert_eq!(u32::from(channel(c as u8, a as u8)), want, "{c} {a}");
            }
        }
    }

    #[test]
    fn in_place() {
        let mut v = [255, 255, 255, 128, 9, 9, 9, 0, 7, 7];
        premultiply_in_place(&mut v);
        assert_eq!(v, [128, 128, 128, 128, 0, 0, 0, 0, 7, 7]);
    }
}
