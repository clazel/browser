//! Colour types, samples and the conversion of a scanline to RGBA8 (PNG 3rd
//! edition, 6.1 "Color types and values", 6.2 "Alpha representation", 11.2.1
//! IHDR, 11.2.2 PLTE, 11.3.1 tRNS, 13.12 "Sample depth rescaling", 13.16
//! "Alpha channel processing").
//!
//! Listed choices, which are the `png` crate's (so the differential is
//! exact), each with its place in the standard:
//!
//! - **Sample depth 1, 2 and 4 are scaled to 8 bits by multiplying by
//!   255 / (2^depth - 1)** (255, 85, 17), which is exact for these depths
//!   (13.12's left bit replication gives the same values).
//! - **Depth 16 is reduced to 8 by truncation: the high byte** (13.12
//!   suggests rounding, `(v * 255 + 32767) / 65535`; truncation differs
//!   from it in at most 1 of 255 for any sample). The transparent colour of
//!   `tRNS` is compared with the full 16-bit samples before the reduction
//!   (11.3.1: pixels of the stated colour are fully transparent).
//! - **`tRNS` values for depths below 16** are the low byte of the chunk's
//!   16-bit field (11.3.1 says the unused high bits must be zero, and this
//!   reads them as such), compared with the unscaled sample.
//! - **A palette index past the palette's entries** is black and opaque
//!   (11.2.2 makes it an error; `png` and browsers draw it).
//! - **Gamma, chromaticities, ICC profiles, sRGB and cICP are ignored**:
//!   `gAMA`, `cHRM`, `iCCP`, `sRGB` and `cICP` are read as chunks (their
//!   length and CRC are checked) and their contents are not used; the
//!   output is the stored sample values, as browsers' defaults draw them
//!   without colour management.

/// 6.1, Table 6.1: the five colour types, by their IHDR code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ColorType {
    /// 0: greyscale.
    Gray,
    /// 2: truecolour.
    Rgb,
    /// 3: indexed-colour.
    Indexed,
    /// 4: greyscale with alpha.
    GrayAlpha,
    /// 6: truecolour with alpha.
    Rgba,
}

impl ColorType {
    /// 11.2.1: the colour type of an IHDR code, if it is one of 0, 2, 3, 4, 6.
    pub fn from_code(code: u8) -> Option<ColorType> {
        match code {
            0 => Some(ColorType::Gray),
            2 => Some(ColorType::Rgb),
            3 => Some(ColorType::Indexed),
            4 => Some(ColorType::GrayAlpha),
            6 => Some(ColorType::Rgba),
            _ => None,
        }
    }

    /// 6.1: samples per pixel (an indexed pixel has one, the index).
    pub fn channels(self) -> u8 {
        match self {
            ColorType::Gray | ColorType::Indexed => 1,
            ColorType::GrayAlpha => 2,
            ColorType::Rgb => 3,
            ColorType::Rgba => 4,
        }
    }

    /// 11.2.1, Table 11.1: whether `depth` is allowed for this colour type.
    pub fn allows(self, depth: u8) -> bool {
        match self {
            ColorType::Gray => matches!(depth, 1 | 2 | 4 | 8 | 16),
            ColorType::Indexed => matches!(depth, 1 | 2 | 4 | 8),
            ColorType::Rgb | ColorType::GrayAlpha | ColorType::Rgba => matches!(depth, 8 | 16),
        }
    }
}

/// The transparent colour of colour types 0 and 2 (11.3.1), or none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Trns {
    /// No `tRNS` chunk (or one that does not apply).
    None,
    /// Colour type 0: this grey sample value is fully transparent.
    Gray(u16),
    /// Colour type 2: this red, green and blue is fully transparent.
    Rgb(u16, u16, u16),
}

/// What IHDR (11.2.1) says of the samples.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Layout {
    /// The colour type.
    pub color: ColorType,
    /// Bits per sample: 1, 2, 4, 8 or 16, allowed for the colour type.
    pub depth: u8,
}

impl Layout {
    /// 6.1: bits per pixel, `channels * depth`, at most 64.
    pub fn bits_per_pixel(&self) -> u32 {
        u32::from(self.color.channels()).saturating_mul(u32::from(self.depth))
    }

    /// 7.2: the bytes a scanline of `width` pixels takes without its
    /// filter-type byte: `ceil(width * bits_per_pixel / 8)`.
    pub fn row_bytes(&self, width: u32) -> u32 {
        width
            .saturating_mul(self.bits_per_pixel())
            .saturating_add(7)
            / 8
    }

    /// 9.2: "bpp", the bytes per complete pixel rounded up to 1.
    pub fn filter_bpp(&self) -> usize {
        usize::try_from(self.bits_per_pixel().saturating_add(7) / 8)
            .unwrap_or(1)
            .max(1)
    }
}

/// The value of sample number `index` of a scanline (without its
/// filter-type byte). 7.2: samples of depth below 8 are packed first sample
/// in the high bits; depth 16 is big-endian (7.1). Reads 0 past the row.
pub fn sample(row: &[u8], depth: u8, index: usize) -> u16 {
    let at = |i: usize| u16::from(row.get(i).copied().unwrap_or(0));
    match depth {
        8 => at(index),
        16 => {
            let i = index.saturating_mul(2);
            (at(i) << 8) | at(i.saturating_add(1))
        }
        _ => {
            let d = u32::from(depth.clamp(1, 4));
            let bit = index.saturating_mul(usize::try_from(d).unwrap_or(1));
            let byte = at(bit / 8);
            // High bits first: the shift is 8 - depth - (bit mod 8).
            let within = u32::try_from(bit % 8).unwrap_or(0);
            let shift = 8u32.saturating_sub(d).saturating_sub(within);
            (byte >> shift) & ((1u16 << d).saturating_sub(1))
        }
    }
}

/// 13.12: a sample of `depth` bits as 8 bits (see the listed choices).
fn to8(value: u16, depth: u8) -> u8 {
    let v = match depth {
        16 => value >> 8,
        1 => value.saturating_mul(255),
        2 => value.saturating_mul(85),
        4 => value.saturating_mul(17),
        _ => value,
    };
    u8::try_from(v & 0xFF).unwrap_or(0)
}

/// One pixel of a scanline as straight RGBA8. `palette` is 4 bytes per entry
/// (colour type 3), `trns` the transparent colour (types 0 and 2). 6.1 for
/// the channel order; 13.16 for alpha.
pub fn rgba(layout: &Layout, trns: Trns, palette: &[u8], row: &[u8], i: usize) -> [u8; 4] {
    let depth = layout.depth;
    let ch = usize::from(layout.color.channels());
    let s = |k: usize| sample(row, depth, i.saturating_mul(ch).saturating_add(k));
    match layout.color {
        ColorType::Gray => {
            let v = s(0);
            let g = to8(v, depth);
            let a = if trns == Trns::Gray(v) { 0 } else { 255 };
            [g, g, g, a]
        }
        ColorType::GrayAlpha => {
            let g = to8(s(0), depth);
            [g, g, g, to8(s(1), depth)]
        }
        ColorType::Rgb => {
            let (r, g, b) = (s(0), s(1), s(2));
            let a = if trns == Trns::Rgb(r, g, b) { 0 } else { 255 };
            [to8(r, depth), to8(g, depth), to8(b, depth), a]
        }
        ColorType::Rgba => [
            to8(s(0), depth),
            to8(s(1), depth),
            to8(s(2), depth),
            to8(s(3), depth),
        ],
        ColorType::Indexed => {
            // 11.2.2 (listed): an index past the entries is opaque black,
            // which is also what an entry never set holds.
            let at = usize::from(s(0)).saturating_mul(4);
            let get = |k: usize| palette.get(at.saturating_add(k)).copied();
            match (get(0), get(1), get(2), get(3)) {
                (Some(r), Some(g), Some(b), Some(a)) => [r, g, b, a],
                _ => [0, 0, 0, 255],
            }
        }
    }
}

/// 4.9 (APNG's `APNG_BLEND_OP_OVER`, "a simple OVER operation as described
/// in Alpha Channel Processing", 6.2 and 13.16): the straight-alpha RGBA of
/// `src` composited over `dst`.
///
/// Listed choice (the text gives the operation, not the rounding): with
/// `sa`, `da` the alphas out of 255, the result alpha is
/// `sa + round(da * (255 - sa) / 255)` and each colour channel is
/// `round((cs * sa * 255 + cd * da * (255 - sa)) / (alpha * 255))`, all in
/// integers with ties rounding up; `sa = 255` gives `src` and `sa = 0`
/// gives `dst`.
pub fn over(src: [u8; 4], dst: [u8; 4]) -> [u8; 4] {
    let [sr, sg, sb, sa] = src;
    let [dr, dg, db, da] = dst;
    if sa == 255 {
        return src;
    }
    if sa == 0 {
        return dst;
    }
    let (sa32, da32) = (u32::from(sa), u32::from(da));
    let inv = 255u32.saturating_sub(sa32);
    // The destination's contribution to coverage, rounded.
    let behind = da32.saturating_mul(inv).saturating_add(127) / 255;
    let alpha = sa32.saturating_add(behind).min(255);
    let den = alpha.saturating_mul(255);
    let channel = |cs: u8, cd: u8| -> u8 {
        let num = u32::from(cs)
            .saturating_mul(sa32)
            .saturating_mul(255)
            .saturating_add(u32::from(cd).saturating_mul(da32).saturating_mul(inv));
        let v = num
            .saturating_add(den / 2)
            .checked_div(den)
            .unwrap_or(0)
            .min(255);
        u8::try_from(v).unwrap_or(u8::MAX)
    };
    [
        channel(sr, dr),
        channel(sg, dg),
        channel(sb, db),
        u8::try_from(alpha).unwrap_or(u8::MAX),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    const PAL: [u8; 8] = [1, 2, 3, 255, 9, 8, 7, 128];

    fn lay(color: ColorType, depth: u8) -> Layout {
        Layout { color, depth }
    }

    #[test]
    fn row_bytes_and_bpp() {
        assert_eq!(lay(ColorType::Gray, 1).row_bytes(9), 2);
        assert_eq!(lay(ColorType::Rgba, 16).row_bytes(3), 24);
        assert_eq!(lay(ColorType::Gray, 2).filter_bpp(), 1);
        assert_eq!(lay(ColorType::Rgb, 16).filter_bpp(), 6);
    }

    #[test]
    fn packed_samples_are_high_bits_first() {
        let row = [0b1010_0110u8];
        assert_eq!(sample(&row, 1, 0), 1);
        assert_eq!(sample(&row, 1, 1), 0);
        assert_eq!(sample(&row, 2, 0), 0b10);
        assert_eq!(sample(&row, 2, 3), 0b10);
        assert_eq!(sample(&row, 4, 1), 0b0110);
        assert_eq!(sample(&row, 4, 5), 0);
        assert_eq!(sample(&[0x12, 0x34], 16, 0), 0x1234);
    }

    #[test]
    fn grey_scaling_and_trns() {
        let l = lay(ColorType::Gray, 2);
        let row = [0b1101_0000u8];
        assert_eq!(rgba(&l, Trns::None, &[], &row, 0), [255, 255, 255, 255]);
        assert_eq!(rgba(&l, Trns::Gray(1), &[], &row, 1), [85, 85, 85, 0]);
        let l16 = lay(ColorType::Gray, 16);
        assert_eq!(
            rgba(&l16, Trns::Gray(0xABCD), &[], &[0xAB, 0xCD], 0),
            [0xAB, 0xAB, 0xAB, 0]
        );
    }

    #[test]
    fn palette_lookup_and_out_of_range() {
        let l = lay(ColorType::Indexed, 8);
        assert_eq!(rgba(&l, Trns::None, &PAL, &[1], 0), [9, 8, 7, 128]);
        assert_eq!(rgba(&l, Trns::None, &PAL, &[2], 0), [0, 0, 0, 255]);
    }

    #[test]
    fn over_edges() {
        let d = [10, 20, 30, 200];
        assert_eq!(over([1, 2, 3, 255], d), [1, 2, 3, 255]);
        assert_eq!(over([1, 2, 3, 0], d), d);
        assert_eq!(over([255, 0, 0, 128], [0, 0, 0, 0]), [255, 0, 0, 128]);
        // Opaque destination: the usual blend.
        assert_eq!(
            over([255, 255, 255, 128], [0, 0, 0, 255]),
            [128, 128, 128, 255]
        );
    }
}
