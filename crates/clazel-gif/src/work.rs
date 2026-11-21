//! The layout of the work buffer.
//!
//! `work_len(config)` is [`FIXED`] plus the canvas's size in bytes; the
//! buffer is cut into these parts, in this order:
//!
//! | part | bytes | holds |
//! |------|-------|-------|
//! | `global` | 768 | the global colour table, RGB triples |
//! | `local` | 768 | the current frame's local colour table |
//! | `prefix` | `2 * TABLE_LEN` | LZW's prefix codes, little-endian `u16` |
//! | `suffix` | `TABLE_LEN` | LZW's last bytes |
//! | `stack` | `TABLE_LEN` | a string being spelt out, last byte first |
//! | `saved` | the canvas | the canvas before a frame whose disposal is "restore to previous" |
//!
//! `saved` is a copy of the whole canvas, so the work buffer is as large as
//! the pixel buffer plus 17 kB (a listed choice: restoring only the frame's
//! rectangle would need the rectangle's size, which is not known when the
//! buffer is sized, and may be the whole canvas).

use crate::lzw::{TABLE_LEN, Tables};

/// The bytes of a colour table of 256 entries.
pub(crate) const PALETTE: usize = 768;

/// The bytes of the work buffer before `saved`.
pub(crate) const FIXED: usize = PALETTE * 2 + TABLE_LEN * 2 + TABLE_LEN + TABLE_LEN;

/// The work buffer, cut into its parts, and the pixel buffer.
#[derive(Debug)]
pub(crate) struct Parts<'a> {
    /// The canvas.
    pub pixels: &'a mut [u8],
    /// The global colour table's bytes (`PALETTE` of them).
    pub global: &'a mut [u8],
    /// The local colour table's bytes (`PALETTE` of them).
    pub local: &'a mut [u8],
    /// LZW's arrays.
    pub tables: Tables<'a>,
    /// The canvas as it was before the current frame, as long as `pixels`.
    pub saved: &'a mut [u8],
}

impl<'a> Parts<'a> {
    /// Cuts `work` (exactly `FIXED` plus `pixels.len()` bytes) into its
    /// parts; `None` if it has another length.
    pub(crate) fn new(pixels: &'a mut [u8], work: &'a mut [u8]) -> Option<Parts<'a>> {
        let (global, rest) = work.split_at_mut_checked(PALETTE)?;
        let (local, rest) = rest.split_at_mut_checked(PALETTE)?;
        let (prefix, rest) = rest.split_at_mut_checked(TABLE_LEN.checked_mul(2)?)?;
        let (suffix, rest) = rest.split_at_mut_checked(TABLE_LEN)?;
        let (stack, saved) = rest.split_at_mut_checked(TABLE_LEN)?;
        if saved.len() != pixels.len() {
            return None;
        }
        Some(Parts {
            pixels,
            global,
            local,
            tables: Tables {
                prefix,
                suffix,
                stack,
            },
            saved,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cuts_exactly() {
        let mut pixels = [0u8; 8];
        let mut work = vec![0u8; FIXED.saturating_add(8)];
        let parts = Parts::new(&mut pixels, &mut work);
        assert!(parts.is_some_and(|p| p.tables.stack.len() == TABLE_LEN && p.saved.len() == 8));
        let mut work = vec![0u8; FIXED.saturating_add(9)];
        assert!(Parts::new(&mut pixels, &mut work).is_none());
        let mut work = vec![0u8; FIXED.saturating_add(7)];
        assert!(Parts::new(&mut pixels, &mut work).is_none());
    }
}
