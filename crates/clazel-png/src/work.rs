//! The work buffer's layout: where the window, the two scanlines, the palette
//! and the saved canvas live. Cutting it is plain `split_at_mut_checked`;
//! `Png::inv` says the buffers have the lengths this cuts to.
//!
//! ```text
//! window   E::WINDOW bytes          the zlib engine's history (32 KiB)
//! cur      8 * width + 1 bytes      the scanline being received: filter type, then its bytes
//! prev     8 * width bytes          the previous scanline, unfiltered
//! palette  4 * E::PALETTE_ENTRIES   RGBA of every palette entry (11.2.2, 11.3.1)
//! saved    4 * width * height       the canvas before a frame that is disposed to "previous"
//! ```
//!
//! A scanline of 16-bit RGBA is 8 bytes a pixel, the widest there is (7.2),
//! so `8 * width` holds any scanline of any colour type and depth, and the
//! work buffer's size is a function of the config alone (the `Decoder`
//! contract), though the colour type is not known until IHDR is read.

use clazel_image_shape::Config;

/// The bytes of a scanline's data at most, for an image `width` wide.
pub(crate) fn row_cap(width: u32) -> Option<usize> {
    usize::try_from(width).ok()?.checked_mul(8)
}

/// Bytes per palette entry (R, G, B, A).
const ENTRY: usize = 4;

/// The work buffer's length for `config`, with a window of `window` bytes
/// and a palette of `entries` entries.
pub(crate) fn work_len(config: &Config, window: usize, entries: usize) -> Option<usize> {
    let cap = row_cap(config.width())?;
    window
        .checked_add(cap)?
        .checked_add(1)?
        .checked_add(cap)?
        .checked_add(entries.checked_mul(ENTRY)?)?
        .checked_add(config.rgba_len().ok()?)
}

/// The buffers of one `step`, cut from the caller's.
pub(crate) struct Parts<'a> {
    pub pixels: &'a mut [u8],
    pub window: &'a mut [u8],
    pub cur: &'a mut [u8],
    pub prev: &'a mut [u8],
    pub palette: &'a mut [u8],
    pub saved: &'a mut [u8],
}

impl<'a> Parts<'a> {
    /// Cuts `work` as the module documentation shows; `None` if it is not
    /// exactly `work_len` long.
    pub(crate) fn new(
        config: &Config,
        window: usize,
        entries: usize,
        pixels: &'a mut [u8],
        work: &'a mut [u8],
    ) -> Option<Parts<'a>> {
        let cap = row_cap(config.width())?;
        if work.len() != work_len(config, window, entries)? {
            return None;
        }
        let (win, rest) = work.split_at_mut_checked(window)?;
        let (cur, rest) = rest.split_at_mut_checked(cap.checked_add(1)?)?;
        let (prev, rest) = rest.split_at_mut_checked(cap)?;
        let (palette, saved) = rest.split_at_mut_checked(entries.checked_mul(ENTRY)?)?;
        Some(Parts {
            pixels,
            window: win,
            cur,
            prev,
            palette,
            saved,
        })
    }
}
