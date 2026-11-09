//! `post`, PostScript information (OpenType 1.9, chapter `post`; Apple's
//! manual, "'post' table").
//!
//! <https://learn.microsoft.com/en-us/typography/opentype/otspec190/post>.
//!
//! Only the header is read. Glyph names (versions 2.0 and 2.5) are not:
//! nothing in a browser needs them, so the version is not checked either.

use crate::Error;
use crate::read::{fixed_at, i16_at, u32_at};

/// The header's size: `maxMemType1` ends at byte 32.
pub const SIZE: usize = 32;

/// The fields of `post` a face uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Post {
    /// `version` (`Version16Dot16`).
    pub version: u32,
    /// `italicAngle` (`Fixed`, raw 16.16): "Italic angle in
    /// counter-clockwise degrees from the vertical."
    pub italic_angle: i32,
    /// `underlinePosition`: "the suggested distance of the top of the
    /// underline from the baseline (negative values indicate below
    /// baseline)".
    pub underline_position: i16,
    /// `underlineThickness`.
    pub underline_thickness: i16,
    /// `isFixedPitch`: "Set to 0 if the font is proportionally spaced,
    /// non-zero if the font is not proportionally spaced (i.e. monospaced)."
    pub is_fixed_pitch: bool,
}

impl Post {
    /// Parse the header.
    pub fn parse(data: &[u8]) -> Result<Self, Error> {
        if data.len() < SIZE {
            return Err(Error::Truncated);
        }
        Ok(Self {
            version: u32_at(data, 0)?,
            italic_angle: fixed_at(data, 4)?,
            underline_position: i16_at(data, 8)?,
            underline_thickness: i16_at(data, 10)?,
            is_fixed_pitch: u32_at(data, 12)? != 0,
        })
    }
}
