//! `OS/2`, OS/2 and Windows metrics (OpenType 1.9, chapter `os2`).
//!
//! <https://learn.microsoft.com/en-us/typography/opentype/otspec190/os2>.
//! Apple's manual lists `OS/2` among its optional tables and adds nothing
//! this crate reads.

use crate::read::{i16_at, u16_at};
use crate::{Error, Tag};

/// Size of each version's table, by `version` (0 to 5): the offset at
/// which its last field ends ("OS/2 Table Formats").
pub const SIZES: [usize; 6] = [78, 86, 96, 96, 96, 100];
/// `fsSelection` bit 7, `USE_TYPO_METRICS`: "If set, it is strongly
/// recommended that applications use OS/2.sTypoAscender -
/// OS/2.sTypoDescender + OS/2.sTypoLineGap as the default line spacing".
pub const USE_TYPO_METRICS: u16 = 1 << 7;
/// `fsSelection` bit 0, `ITALIC`.
pub const ITALIC: u16 = 1 << 0;
/// `fsSelection` bit 5, `BOLD`.
pub const BOLD: u16 = 1 << 5;

/// The fields of `OS/2` a face uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Os2 {
    /// `version`: 0 to 5.
    pub version: u16,
    /// `usWeightClass`: 1 to 1000, 400 normal, 700 bold.
    pub weight_class: u16,
    /// `usWidthClass`: 1 to 9, 5 normal.
    pub width_class: u16,
    /// `fsSelection`.
    pub fs_selection: u16,
    /// `sTypoAscender`.
    pub typo_ascender: i16,
    /// `sTypoDescender`.
    pub typo_descender: i16,
    /// `sTypoLineGap`.
    pub typo_line_gap: i16,
    /// `usWinAscent`.
    pub win_ascent: u16,
    /// `usWinDescent`.
    pub win_descent: u16,
    /// `yStrikeoutSize`.
    pub strikeout_size: i16,
    /// `yStrikeoutPosition`.
    pub strikeout_position: i16,
    /// `sxHeight` (version 2 and later).
    pub x_height: Option<i16>,
    /// `sCapHeight` (version 2 and later).
    pub cap_height: Option<i16>,
}

impl Os2 {
    /// Parse `OS/2`: `version` 0 to 5, and at least that version's size
    /// (its trailing fields are not read, so a longer table is fine).
    /// Apple's manual mentions a shorter 68-byte version 0 table from before
    /// the typo metrics; it is refused as [`Error::Truncated`], since the
    /// face can do without `OS/2`.
    pub fn parse(data: &[u8]) -> Result<Self, Error> {
        let version = u16_at(data, 0)?;
        let size = *SIZES
            .get(usize::from(version))
            .ok_or(Error::UnsupportedVersion(Tag::OS2))?;
        if data.len() < size {
            return Err(Error::Truncated);
        }
        // `sxHeight` 86, `sCapHeight` 88: "This field was defined in
        // version 2 of the OS/2 table."
        let (x_height, cap_height) = if version >= 2 {
            (Some(i16_at(data, 86)?), Some(i16_at(data, 88)?))
        } else {
            (None, None)
        };
        Ok(Self {
            version,
            // `usWeightClass` 4, `usWidthClass` 6.
            weight_class: u16_at(data, 4)?,
            width_class: u16_at(data, 6)?,
            // `fsSelection` 62.
            fs_selection: u16_at(data, 62)?,
            // `sTypoAscender` 68, `sTypoDescender` 70, `sTypoLineGap` 72,
            // `usWinAscent` 74, `usWinDescent` 76.
            typo_ascender: i16_at(data, 68)?,
            typo_descender: i16_at(data, 70)?,
            typo_line_gap: i16_at(data, 72)?,
            win_ascent: u16_at(data, 74)?,
            win_descent: u16_at(data, 76)?,
            // `yStrikeoutSize` 26, `yStrikeoutPosition` 28.
            strikeout_size: i16_at(data, 26)?,
            strikeout_position: i16_at(data, 28)?,
            x_height,
            cap_height,
        })
    }

    /// `fsSelection` bit 7, `USE_TYPO_METRICS`, which "Applications should
    /// ignore … in a font that has a version 0 to version 3 OS/2 table"
    /// ("Bits 7 to 9 were defined in version 4").
    pub fn use_typo_metrics(&self) -> bool {
        self.version >= 4 && self.fs_selection & USE_TYPO_METRICS != 0
    }
}
