//! Two screenshots' difference and WPT's fuzzy rule.
//!
//! Source: wptrunner's `get_differences` (both images `convert("RGB")`,
//! `ImageChops.difference`, a mask of the difference `convert("L")`, then the
//! per-channel maximum and the pixel count over the mask) and `check_pass`
//! (with no fuzziness, equal means no difference at all; with it, the three
//! conditions joined by `or`). Modelling choices: `mod.rs`.

use super::meta::{Fuzzy, Relation};

/// A screenshot: `width` by `height` pixels of RGBA, row after row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Image {
    /// Width in pixels.
    pub width: u32,
    /// Height in pixels.
    pub height: u32,
    /// `4 · width · height` bytes.
    pub rgba: Vec<u8>,
}

/// PIL's RGB to luminance (`L24(rgb) >> 16`).
fn luminance(r: u8, g: u8, b: u8) -> u32 {
    // At most 255 · 65536 + 0x8000: far inside `u32`.
    u32::from(r)
        .saturating_mul(19595)
        .saturating_add(u32::from(g).saturating_mul(38470))
        .saturating_add(u32::from(b).saturating_mul(7471))
        .saturating_add(0x8000)
        >> 16
}

/// wptrunner's `(max_per_channel, pixels_different)` of two screenshots of
/// the same size; `None` if their sizes differ or a buffer is short.
pub fn differences(a: &Image, b: &Image) -> Option<(u8, u64)> {
    if a.width != b.width || a.height != b.height {
        return None;
    }
    let n = usize::try_from(
        u64::from(a.width)
            .checked_mul(u64::from(a.height))?
            .checked_mul(4)?,
    )
    .ok()?;
    let (pa, pb) = (a.rgba.get(..n)?, b.rgba.get(..n)?);
    let mut max = 0u8;
    let mut count = 0u64;
    for (x, y) in pa.as_chunks::<4>().0.iter().zip(pb.as_chunks::<4>().0) {
        let (r, g, bl) = (
            x[0].abs_diff(y[0]),
            x[1].abs_diff(y[1]),
            x[2].abs_diff(y[2]),
        );
        if luminance(r, g, bl) > 0 {
            count = count.saturating_add(1);
            max = max.max(r).max(g).max(bl);
        }
    }
    Some((max, count))
}

/// `check_pass`'s "equal" for a maximum per-channel difference `max` and a
/// count `count`, under `fuzzy`.
pub fn equal(max: u8, count: u64, fuzzy: Option<Fuzzy>) -> bool {
    let max = u64::from(max);
    match fuzzy {
        // "if not fuzzy or fuzzy == ((0, 0), (0, 0)): equal = pixels_different
        // == 0 and max_per_channel == 0".
        None => count == 0 && max == 0,
        Some(f) if f.max_difference == (0, 0) && f.total_pixels == (0, 0) => count == 0 && max == 0,
        Some(f) => {
            let (pc, dif) = (f.max_difference, f.total_pixels);
            (count == 0 && dif.0 == 0)
                || (max == 0 && pc.0 == 0)
                || ((pc.0..=pc.1).contains(&max) && (dif.0..=dif.1).contains(&count))
        }
    }
}

/// Whether a test whose screenshot is `test` passes against one reference
/// of relation `relation` whose screenshot is `reference`, under `fuzzy`.
/// Screenshots of different sizes are not equal.
pub fn passes(test: &Image, reference: &Image, relation: Relation, fuzzy: Option<Fuzzy>) -> bool {
    let same = differences(test, reference).is_some_and(|(max, count)| equal(max, count, fuzzy));
    match relation {
        Relation::Match => same,
        Relation::Mismatch => !same,
    }
}
