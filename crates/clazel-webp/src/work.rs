//! The layout of the work buffer, and the bounds that fix it.
//!
//! `work_len(width, height, animated)` is the sum of these parts, in this
//! order:
//!
//! | part | bytes | holds |
//! |------|-------|-------|
//! | `cache` | `4 * CACHE_ENTRIES` | the colour cache, RGBA |
//! | `lens` | `MAX_GREEN` | the code lengths of the prefix code being read |
//! | `cl_lens` | 19 | the code length code's lengths |
//! | `cl_counts` | 32 | the code length code's counts per length, `u16` little-endian |
//! | `cl_syms` | 38 | its symbols sorted by length, `u16` |
//! | `palette` | 1024 | the colour table, up to 256 RGBA entries |
//! | `pred` | `sub` | the predictor transform's image |
//! | `color` | `sub` | the colour transform's image |
//! | `meta` | `sub` | the entropy image (meta prefix codes) |
//! | `groups` | `cap * GROUP_BYTES` | the prefix code groups |
//! | `frame` | the canvas, if animated, else 0 | a frame before it is composited |
//!
//! `sub` is 4 bytes for each block of 4 by 4 pixels of the image (the
//! sub-resolution images' blocks are at least 4 by 4: RFC 9649 sections
//! 3.5.1 and 3.7.2.2.1, "ReadBits(3) + 2"). `cap` is the number of prefix
//! code groups held: the blocks of 4 by 4, at most [`MAX_GROUPS`] (a listed
//! choice: an entropy image naming more groups is refused as unsupported).

/// The largest colour cache, in bits: RFC 9649 section 3.6.2.3, "[1..11]".
/// (Under Kani the cache, and so every alphabet, is smaller: README.)
pub(crate) const MAX_CACHE_BITS: u8 = if cfg!(kani) { 3 } else { 11 };

/// The colour cache's entries at that size.
pub(crate) const CACHE_ENTRIES: usize = if cfg!(kani) { 8 } else { 2048 };

/// The green alphabet without a cache: 256 literals and 24 length prefix
/// codes (section 3.7.2.3).
pub(crate) const GREEN_BASE: usize = 280;

/// The green alphabet at its largest: it holds the colour cache's indexes.
pub(crate) const MAX_GREEN: usize = GREEN_BASE + CACHE_ENTRIES;

/// The distance alphabet: 40 prefix codes (section 3.6.2.2).
pub(crate) const DIST_ALPHABET: usize = 40;

/// The code length code's alphabet (section 3.7.2.1.2, `kCodeLengthCodes`).
pub(crate) const CL_ALPHABET: usize = 19;

/// The bytes of one prefix code's counts: 16 `u16`.
pub(crate) const COUNTS_BYTES: usize = 32;

/// Where each of a group's five codes' symbols start, in symbols: green,
/// red, blue, alpha, distance (the order of section 3.7.2).
pub(crate) const SYMBOL_BASE: [usize; 5] = [
    0,
    MAX_GREEN,
    MAX_GREEN + 256,
    MAX_GREEN + 512,
    MAX_GREEN + 768,
];

/// Bytes of one group: five counts arrays and the symbols of the five codes.
pub(crate) const GROUP_BYTES: usize = 5 * COUNTS_BYTES + 2 * (MAX_GREEN + 768 + DIST_ALPHABET);

/// The most prefix code groups held (a listed choice).
pub(crate) const MAX_GROUPS: usize = 1024;

/// The bytes of the colour table.
pub(crate) const PALETTE_BYTES: usize = 1024;

/// The blocks of 4 by 4 pixels of a `width` by `height` image.
fn blocks(width: u32, height: u32) -> Option<usize> {
    let bw = usize::try_from(width.checked_add(3)? / 4).ok()?;
    let bh = usize::try_from(height.checked_add(3)? / 4).ok()?;
    bw.checked_mul(bh)
}

/// The bytes of each sub-resolution image's region.
pub(crate) fn sub_len(width: u32, height: u32) -> Option<usize> {
    blocks(width, height)?.checked_mul(4)
}

/// The prefix code groups held for an image of this size.
pub(crate) fn group_cap(width: u32, height: u32) -> Option<usize> {
    Some(blocks(width, height)?.clamp(1, MAX_GROUPS))
}

/// The bytes of the work buffer for a canvas of `width` by `height`.
pub(crate) fn work_len(width: u32, height: u32, animated: bool) -> Option<usize> {
    let sub = sub_len(width, height)?;
    let canvas = if animated {
        usize::try_from(width)
            .ok()?
            .checked_mul(usize::try_from(height).ok()?)?
            .checked_mul(4)?
    } else {
        0
    };
    CACHE_ENTRIES
        .checked_mul(4)?
        .checked_add(MAX_GREEN)?
        .checked_add(CL_ALPHABET)?
        .checked_add(COUNTS_BYTES)?
        .checked_add(CL_ALPHABET.checked_mul(2)?)?
        .checked_add(PALETTE_BYTES)?
        .checked_add(sub.checked_mul(3)?)?
        .checked_add(group_cap(width, height)?.checked_mul(GROUP_BYTES)?)?
        .checked_add(canvas)
}

/// The scratch regions of the lossless decoder, cut from the work buffer.
#[derive(Debug)]
pub(crate) struct Scratch<'a> {
    /// The colour cache.
    pub cache: &'a mut [u8],
    /// Code lengths being read.
    pub lens: &'a mut [u8],
    /// The code length code's lengths.
    pub cl_lens: &'a mut [u8],
    /// The code length code's counts.
    pub cl_counts: &'a mut [u8],
    /// The code length code's symbols.
    pub cl_syms: &'a mut [u8],
    /// The colour table.
    pub palette: &'a mut [u8],
    /// The predictor image.
    pub pred: &'a mut [u8],
    /// The colour transform image.
    pub color: &'a mut [u8],
    /// The entropy image.
    pub meta: &'a mut [u8],
    /// The prefix code groups.
    pub groups: &'a mut [u8],
}

/// The pixel buffer, the scratch and the frame buffer.
#[derive(Debug)]
pub(crate) struct Parts<'a> {
    /// The canvas.
    pub pixels: &'a mut [u8],
    /// The lossless decoder's regions.
    pub scratch: Scratch<'a>,
    /// A frame as decoded, before compositing (empty unless animated).
    pub frame: &'a mut [u8],
}

impl<'a> Parts<'a> {
    /// Cuts `work` (exactly `work_len(width, height, animated)` bytes) into
    /// its parts; `None` if it has another length.
    pub(crate) fn new(
        pixels: &'a mut [u8],
        work: &'a mut [u8],
        width: u32,
        height: u32,
        animated: bool,
    ) -> Option<Parts<'a>> {
        if work.len() != work_len(width, height, animated)? {
            return None;
        }
        let sub = sub_len(width, height)?;
        let (cache, rest) = work.split_at_mut_checked(CACHE_ENTRIES.checked_mul(4)?)?;
        let (lens, rest) = rest.split_at_mut_checked(MAX_GREEN)?;
        let (cl_lens, rest) = rest.split_at_mut_checked(CL_ALPHABET)?;
        let (cl_counts, rest) = rest.split_at_mut_checked(COUNTS_BYTES)?;
        let (cl_syms, rest) = rest.split_at_mut_checked(CL_ALPHABET.checked_mul(2)?)?;
        let (palette, rest) = rest.split_at_mut_checked(PALETTE_BYTES)?;
        let (pred, rest) = rest.split_at_mut_checked(sub)?;
        let (color, rest) = rest.split_at_mut_checked(sub)?;
        let (meta, rest) = rest.split_at_mut_checked(sub)?;
        let (groups, frame) =
            rest.split_at_mut_checked(group_cap(width, height)?.checked_mul(GROUP_BYTES)?)?;
        Some(Parts {
            pixels,
            scratch: Scratch {
                cache,
                lens,
                cl_lens,
                cl_counts,
                cl_syms,
                palette,
                pred,
                color,
                meta,
                groups,
            },
            frame,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cuts_exactly() {
        for (w, h, animated) in [(1u32, 1u32, false), (5, 3, true), (64, 64, false)] {
            let wl = work_len(w, h, animated).unwrap_or(0);
            assert!(wl > 0);
            let mut pixels = vec![0u8; usize::try_from(w * h * 4).unwrap_or(0)];
            let mut work = vec![0u8; wl];
            let parts = Parts::new(&mut pixels, &mut work, w, h, animated);
            assert!(
                parts.is_some_and(|p| p.frame.len() == if animated { p.pixels.len() } else { 0 })
            );
            let mut work = vec![0u8; wl.saturating_add(1)];
            assert!(Parts::new(&mut pixels, &mut work, w, h, animated).is_none());
        }
    }

    #[test]
    fn caps() {
        assert_eq!(group_cap(1, 1), Some(1));
        assert_eq!(group_cap(16384, 16384), Some(MAX_GROUPS));
        assert_eq!(sub_len(5, 5), Some(16));
    }
}
