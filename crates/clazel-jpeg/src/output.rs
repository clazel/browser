//! From decoded component planes to RGBA pixels: chroma upsampling, colour
//! conversion and EXIF orientation.
//!
//! Everything here is a pure function of one output position, so that the
//! decoder needs no row buffers and each function is a Kani harness over
//! every geometry.

/// A decoded component plane and how it is sampled relative to the image.
///
/// `width` by `height` is the component's own size, `ceil(X * Hi / Hmax)`
/// by `ceil(Y * Vi / Vmax)` (T.81 A.1.1, Equation A.1), inside a plane
/// whose rows are `stride` samples apart (the plane is padded to whole
/// MCUs, and the padding is never read). `hs` and `vs` are `Hmax / Hi` and
/// `Vmax / Vi`.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Plane<'a> {
    /// The plane's samples, row-major.
    pub data: &'a [u8],
    /// Samples from one row to the next.
    pub stride: usize,
    /// The component's width in samples.
    pub width: usize,
    /// The component's height in samples.
    pub height: usize,
    /// Horizontal replication factor, 1 to 4.
    pub hs: usize,
    /// Vertical replication factor, 1 to 4.
    pub vs: usize,
}

impl Plane<'_> {
    /// The sample at column `x`, row `y` of the component, `None` outside.
    fn at(&self, x: usize, y: usize) -> Option<i32> {
        if x >= self.width || y >= self.height {
            return None;
        }
        let i = y.checked_mul(self.stride)?.checked_add(x)?;
        Some(i32::from(*self.data.get(i)?))
    }

    /// The component's value at full-resolution position `(x, y)` of the
    /// image (`x < X`, `y < Y`), after upsampling.
    ///
    /// **Listed choice:** libjpeg-turbo's default "fancy" upsampling
    /// (`jdsample.c`, `do_fancy_upsampling = TRUE`). T.81 does not specify
    /// the reconstruction of subsampled components (A.1.1 only defines the
    /// sampling grid). For a plane twice as wide (`hs = 2`) it is the
    /// triangle filter of `h2v1_fancy_upsample`: an output sample is 3/4 of
    /// the nearer input sample and 1/4 of the next nearer, the first and
    /// last columns copying their input; twice as tall too (`vs = 2`) is
    /// `h2v2_fancy_upsample`, the same in both dimensions on column sums,
    /// rows beyond the first and last repeating them; only twice as tall is
    /// `h1v2_fancy_upsample`. These need the component to be more than 2
    /// samples wide (h2v1, h2v2), as in libjpeg-turbo, which then falls back
    /// to replication, as it does for every other ratio (`int_upsample`:
    /// each sample repeated `hs` by `vs` times).
    pub(crate) fn sample(&self, x: usize, y: usize) -> Option<u8> {
        let v = match (self.hs, self.vs) {
            (1, 1) => self.at(x, y)?,
            // h2v1_fancy_upsample.
            (2, 1) if self.width > 2 => {
                let j = x / 2;
                let cur = self.at(j, y)?;
                if x.is_multiple_of(2) {
                    if j == 0 {
                        cur
                    } else {
                        lin(cur, 3, self.at(j.checked_sub(1)?, y)?, 1, 1, 2)?
                    }
                } else if j == self.width.checked_sub(1)? {
                    cur
                } else {
                    lin(cur, 3, self.at(j.checked_add(1)?, y)?, 1, 2, 2)?
                }
            }
            // h2v2_fancy_upsample.
            (2, 2) if self.width > 2 => {
                let r = y / 2;
                // The nearer row is `r`; the other is above for an even
                // output row and below for an odd one, the first and last
                // rows repeating.
                let r2 = if y.is_multiple_of(2) {
                    r.saturating_sub(1)
                } else {
                    r.checked_add(1)?.min(self.height.checked_sub(1)?)
                };
                let colsum =
                    |j: usize| -> Option<i32> { lin(self.at(j, r)?, 3, self.at(j, r2)?, 1, 0, 0) };
                let j = x / 2;
                let this = colsum(j)?;
                if x.is_multiple_of(2) {
                    if j == 0 {
                        lin(this, 4, 0, 0, 8, 4)?
                    } else {
                        lin(this, 3, colsum(j.checked_sub(1)?)?, 1, 8, 4)?
                    }
                } else if j == self.width.checked_sub(1)? {
                    lin(this, 4, 0, 0, 7, 4)?
                } else {
                    lin(this, 3, colsum(j.checked_add(1)?)?, 1, 7, 4)?
                }
            }
            // h1v2_fancy_upsample.
            (1, 2) => {
                let r = y / 2;
                let (r2, bias) = if y.is_multiple_of(2) {
                    (r.saturating_sub(1), 1)
                } else {
                    (r.checked_add(1)?.min(self.height.checked_sub(1)?), 2)
                };
                lin(self.at(x, r)?, 3, self.at(x, r2)?, 1, bias, 2)?
            }
            // int_upsample: replication.
            (hs, vs) => self.at(x.checked_div(hs)?, y.checked_div(vs)?)?,
        };
        u8::try_from(v).ok()
    }
}

/// `(a * ka + b * kb + bias) >> shift`, checked.
fn lin(a: i32, ka: i32, b: i32, kb: i32, bias: i32, shift: u32) -> Option<i32> {
    a.checked_mul(ka)?
        .checked_add(b.checked_mul(kb)?)?
        .checked_add(bias)?
        .checked_shr(shift)
}

/// `FIX(1.40200)`, `FIX(1.77200)`, `FIX(0.71414)` and `FIX(0.34414)` of
/// libjpeg-turbo's `jdcolor.c`, with 16 bits of fraction.
const FIX_1_40200: i32 = 91881;
const FIX_1_77200: i32 = 116130;
const FIX_0_71414: i32 = 46802;
const FIX_0_34414: i32 = 22554;
/// `ONE_HALF`: rounding for the 16-bit fraction.
const ONE_HALF: i32 = 32768;

/// The red, green and blue of a YCbCr triple, JFIF 1.02 §7 ("Conversion to
/// and from RGB"):
///
/// ```text
/// R = Y                      + 1.40200 * (Cr - 128)
/// G = Y - 0.34414 * (Cb - 128) - 0.71414 * (Cr - 128)
/// B = Y + 1.77200 * (Cb - 128)
/// ```
///
/// **Listed choice:** in libjpeg-turbo's fixed point (`ycc_rgb_convert`,
/// constants of 16 fractional bits, each term rounded as `jdcolor.c`'s
/// tables do), clamped to 0 to 255.
pub(crate) fn ycc_to_rgb(y: u8, cb: u8, cr: u8) -> [u8; 3] {
    let y = i32::from(y);
    let cb = i32::from(cb).saturating_sub(128);
    let cr = i32::from(cr).saturating_sub(128);
    let r_off = FIX_1_40200
        .saturating_mul(cr)
        .saturating_add(ONE_HALF)
        .checked_shr(16)
        .unwrap_or(0);
    let b_off = FIX_1_77200
        .saturating_mul(cb)
        .saturating_add(ONE_HALF)
        .checked_shr(16)
        .unwrap_or(0);
    let g_off = 0i32
        .saturating_sub(FIX_0_34414.saturating_mul(cb))
        .saturating_add(ONE_HALF)
        .saturating_sub(FIX_0_71414.saturating_mul(cr))
        .checked_shr(16)
        .unwrap_or(0);
    let clamp = |v: i32| u8::try_from(v.clamp(0, 255)).unwrap_or(0);
    [
        clamp(y.saturating_add(r_off)),
        clamp(y.saturating_add(g_off)),
        clamp(y.saturating_add(b_off)),
    ]
}

/// Adobe-style YCCK to CMYK (libjpeg-turbo `ycck_cmyk_convert`): the YCbCr
/// part becomes `R = 1 - C` and so on, with the same conversion as above,
/// and K passes through.
pub(crate) fn ycck_to_cmyk(y: u8, cb: u8, cr: u8, k: u8) -> [u8; 4] {
    let [r, g, b] = ycc_to_rgb(y, cb, cr);
    [
        255u8.saturating_sub(r),
        255u8.saturating_sub(g),
        255u8.saturating_sub(b),
        k,
    ]
}

/// CMYK as Adobe writes it (inverted: 255 is no ink, so the four values
/// are each the fraction of light that gets through) to RGB:
/// `R = C * K / 255`, rounded, and likewise G and B. **Listed choice:** the
/// plan lists "inverted CMYK as Adobe writes it", and every 4-component
/// image is read as that (libjpeg-turbo only does so with an Adobe marker;
/// it leaves the choice to the caller, and without a marker a browser
/// cannot know either).
pub(crate) fn cmyk_to_rgb(c: u8, m: u8, y: u8, k: u8) -> [u8; 3] {
    let f = |a: u8| -> u8 {
        let p = u32::from(a).saturating_mul(u32::from(k));
        u8::try_from(p.saturating_add(127).checked_div(255).unwrap_or(0)).unwrap_or(255)
    };
    [f(c), f(m), f(y)]
}

/// The EXIF orientation applied to a pixel: where source pixel `(x, y)` of a
/// `w` by `h` image lands in the oriented image (EXIF 2.32, tag 0x0112, the
/// values 1 to 8 as `image-orientation: from-image` applies them), whose
/// width is `h` for the values 5 to 8 (the rotations by a quarter turn and
/// the two reflections about a diagonal) and `w` otherwise. Returns the
/// destination column and row.
///
/// 1 identity; 2 mirrored horizontally; 3 rotated 180 degrees; 4 mirrored
/// vertically; 5 transposed (mirrored about the main diagonal); 6 rotated
/// 90 degrees clockwise to display; 7 transversed (mirrored about the
/// anti-diagonal); 8 rotated 90 degrees counter-clockwise to display.
pub(crate) fn orient(o: u8, w: usize, h: usize, x: usize, y: usize) -> Option<(usize, usize)> {
    if x >= w || y >= h {
        return None;
    }
    let (rx, ry) = (
        w.checked_sub(1)?.checked_sub(x)?,
        h.checked_sub(1)?.checked_sub(y)?,
    );
    Some(match o {
        1 => (x, y),
        2 => (rx, y),
        3 => (rx, ry),
        4 => (x, ry),
        5 => (y, x),
        6 => (ry, x),
        7 => (ry, rx),
        8 => (y, rx),
        _ => return None,
    })
}

/// True for the orientations that swap width and height (5 to 8).
pub(crate) fn swaps(o: u8) -> bool {
    (5..=8).contains(&o)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn plane(data: &[u8], width: usize, height: usize, hs: usize, vs: usize) -> Plane<'_> {
        Plane {
            data,
            stride: width,
            width,
            height,
            hs,
            vs,
        }
    }

    fn row(p: &Plane<'_>, y: usize, n: usize) -> Vec<u8> {
        (0..n).filter_map(|x| p.sample(x, y)).collect()
    }

    #[test]
    fn h2v1_is_the_triangle_filter() {
        let data = [0u8, 100, 200, 40];
        let p = plane(&data, 4, 1, 2, 1);
        // First column copies; interior 3/4 + 1/4 with the rounding of
        // jdsample.c (+1 on the left of a pixel, +2 on its right).
        assert_eq!(row(&p, 0, 8), [0, 25, 75, 125, 175, 160, 80, 40]);
    }

    #[test]
    fn h2v2_uses_rows_above_and_below_with_edges_repeating() {
        // Constant plane stays constant, whatever the edges do.
        let data = [90u8; 12];
        let p = plane(&data, 4, 3, 2, 2);
        for y in 0..6 {
            assert!(row(&p, y, 8).iter().all(|&v| v == 90), "row {y}");
        }
        // A step in rows: row 0 is 0, row 1 is 160.
        let data = [0u8, 0, 0, 160, 160, 160];
        let p = plane(&data, 3, 2, 2, 2);
        // Output row 0 is nearest input row 0 only (above repeats row 0).
        assert_eq!(row(&p, 0, 6), [0; 6]);
        // Output row 1: 3/4 of row 0 and 1/4 of row 1.
        assert_eq!(row(&p, 1, 6), [40; 6]);
        assert_eq!(row(&p, 2, 6), [120; 6]);
        assert_eq!(row(&p, 3, 6), [160; 6]);
    }

    #[test]
    fn narrow_planes_replicate() {
        let data = [10u8, 200];
        let p = plane(&data, 2, 1, 2, 1);
        assert_eq!(row(&p, 0, 4), [10, 10, 200, 200]);
    }

    #[test]
    fn h1v2_is_vertical_only() {
        let data = [0u8, 0, 160, 160];
        let p = plane(&data, 2, 2, 1, 2);
        // y=0: row 0 and the row above (row 0, repeated): 0.
        assert_eq!(row(&p, 0, 2), [0, 0]);
        // y=1: (0*3 + 160 + 2) >> 2 = 40.
        assert_eq!(row(&p, 1, 2), [40, 40]);
        // y=2: (160*3 + 0 + 1) >> 2 = 120.
        assert_eq!(row(&p, 2, 2), [120, 120]);
        assert_eq!(row(&p, 3, 2), [160, 160]);
    }

    #[test]
    fn integral_ratios_replicate() {
        let data = [1u8, 2, 3, 4];
        let p = plane(&data, 2, 2, 4, 2);
        assert_eq!(row(&p, 0, 8), [1, 1, 1, 1, 2, 2, 2, 2]);
        assert_eq!(row(&p, 1, 8), [1, 1, 1, 1, 2, 2, 2, 2]);
        assert_eq!(row(&p, 2, 8), [3, 3, 3, 3, 4, 4, 4, 4]);
    }

    #[test]
    fn colour_of_primaries() {
        assert_eq!(ycc_to_rgb(128, 128, 128), [128, 128, 128]);
        assert_eq!(ycc_to_rgb(0, 128, 128), [0, 0, 0]);
        assert_eq!(ycc_to_rgb(255, 128, 128), [255, 255, 255]);
        // JFIF's red: Y 76, Cb 85, Cr 255.
        assert_eq!(ycc_to_rgb(76, 85, 255), [254, 0, 0]);
        assert_eq!(cmyk_to_rgb(255, 255, 255, 255), [255, 255, 255]);
        assert_eq!(cmyk_to_rgb(255, 0, 0, 255), [255, 0, 0]);
        assert_eq!(cmyk_to_rgb(255, 255, 255, 0), [0, 0, 0]);
    }

    #[test]
    fn orientation_maps_corners() {
        // A 3 by 2 image: the top left pixel (0, 0) goes to:
        let at = |o, x, y| orient(o, 3, 2, x, y);
        assert_eq!(at(1, 0, 0), Some((0, 0)));
        assert_eq!(at(2, 0, 0), Some((2, 0)));
        assert_eq!(at(3, 0, 0), Some((2, 1)));
        assert_eq!(at(4, 0, 0), Some((0, 1)));
        assert_eq!(at(5, 0, 0), Some((0, 0)));
        // 6: rotated clockwise: the top left goes to the top right of the
        // 2 wide, 3 tall result.
        assert_eq!(at(6, 0, 0), Some((1, 0)));
        assert_eq!(at(7, 0, 0), Some((1, 2)));
        assert_eq!(at(8, 0, 0), Some((0, 2)));
        assert_eq!(at(9, 0, 0), None);
        assert_eq!(at(1, 3, 0), None);
    }
}
