//! `hhea`, the horizontal header table (OpenType 1.9, chapter `hhea`;
//! Apple's manual, "'hhea' table").
//!
//! <https://learn.microsoft.com/en-us/typography/opentype/otspec190/hhea>.

use crate::read::{i16_at, u16_at};
use crate::{Error, Tag};

/// The table's size: `numberOfHMetrics` ends at byte 36.
pub const SIZE: usize = 36;

/// The fields of `hhea` a face uses. The chapter notes that "the ascender,
/// descender and linegap values in this table are Apple specific" and that
/// `OS/2`'s typo metrics are used on Windows; which a layout uses is item
/// 5.10's choice, so both are exposed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Hhea {
    /// `ascender`: "Typographic ascent".
    pub ascender: i16,
    /// `descender`: "Typographic descent".
    pub descender: i16,
    /// `lineGap`: "Typographic line gap".
    pub line_gap: i16,
    /// `advanceWidthMax`: "Maximum advance width value in 'hmtx' table."
    pub advance_width_max: u16,
    /// `numberOfHMetrics`: "Number of hMetric entries in 'hmtx' table".
    pub number_of_h_metrics: u16,
}

impl Hhea {
    /// Parse `hhea`. Checked: `majorVersion` "set to 1" (Apple: `version`
    /// `Fixed` 0x00010000). Not checked: `minorVersion`, the caret and extent
    /// fields, `metricDataFormat` ("0 for current format").
    pub fn parse(data: &[u8]) -> Result<Self, Error> {
        if data.len() < SIZE {
            return Err(Error::Truncated);
        }
        if u16_at(data, 0)? != 1 {
            return Err(Error::UnsupportedVersion(Tag::HHEA));
        }
        Ok(Self {
            // `ascender` 4, `descender` 6, `lineGap` 8, `advanceWidthMax` 10,
            // `numberOfHMetrics` 34.
            ascender: i16_at(data, 4)?,
            descender: i16_at(data, 6)?,
            line_gap: i16_at(data, 8)?,
            advance_width_max: u16_at(data, 10)?,
            number_of_h_metrics: u16_at(data, 34)?,
        })
    }
}
