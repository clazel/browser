//! `head`, the font header table (OpenType 1.9, chapter `head`;
//! Apple's manual, "'head' table").
//!
//! <https://learn.microsoft.com/en-us/typography/opentype/otspec190/head>.

use crate::read::{fixed_at, i16_at, u16_at, u32_at};
use crate::{Error, Tag};

/// `magicNumber`: "Set to 0x5F0F3CF5."
pub const MAGIC: u32 = 0x5F0F_3CF5;
/// The table's size: its last field, `glyphDataFormat`, ends at byte 54.
pub const SIZE: usize = 54;

/// `indexToLocFormat`: "0 for short offsets (Offset16), 1 for long
/// (Offset32)."
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LocaFormat {
    /// 0: `Offset16`, the local offset divided by 2.
    Short,
    /// 1: `Offset32`.
    Long,
}

/// The fields of `head` a face uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Head {
    /// `fontRevision` (`Fixed`, raw 16.16).
    pub font_revision: i32,
    /// `flags`.
    pub flags: u16,
    /// `unitsPerEm`: "Set to a value from 16 to 16384."
    pub units_per_em: u16,
    /// `xMin`, `yMin`, `xMax`, `yMax`: "for all glyph bounding boxes".
    pub bbox: [i16; 4],
    /// `macStyle`: bit 0 bold, bit 1 italic, ….
    pub mac_style: u16,
    /// `lowestRecPPEM`: "Smallest readable size in pixels."
    pub lowest_rec_ppem: u16,
    /// `indexToLocFormat`.
    pub index_to_loc_format: LocaFormat,
}

impl Head {
    /// Parse `head`. Checked: `majorVersion` 1 (Apple: `version` `Fixed`
    /// 0x00010000, the same two bytes), `magicNumber`, `unitsPerEm` in 16 to
    /// 16384, `indexToLocFormat` 0 or 1. Not checked: `minorVersion`,
    /// `checksumAdjustment` (a collection invalidates it), the dates,
    /// `fontDirectionHint` ("Deprecated") and `glyphDataFormat`.
    pub fn parse(data: &[u8]) -> Result<Self, Error> {
        if data.len() < SIZE {
            return Err(Error::Truncated);
        }
        // `majorVersion` at 0: "set to 1".
        if u16_at(data, 0)? != 1 {
            return Err(Error::UnsupportedVersion(Tag::HEAD));
        }
        // `magicNumber` at 12.
        if u32_at(data, 12)? != MAGIC {
            return Err(Error::InvalidValue(Tag::HEAD));
        }
        // `unitsPerEm` at 18: "Any value in this range is valid."
        let units_per_em = u16_at(data, 18)?;
        if !(16..=16384).contains(&units_per_em) {
            return Err(Error::InvalidValue(Tag::HEAD));
        }
        // `indexToLocFormat` at 50.
        let index_to_loc_format = match i16_at(data, 50)? {
            0 => LocaFormat::Short,
            1 => LocaFormat::Long,
            _ => return Err(Error::InvalidValue(Tag::HEAD)),
        };
        Ok(Self {
            // `fontRevision` at 4, `flags` at 16.
            font_revision: fixed_at(data, 4)?,
            flags: u16_at(data, 16)?,
            units_per_em,
            // `xMin` 36, `yMin` 38, `xMax` 40, `yMax` 42.
            bbox: [
                i16_at(data, 36)?,
                i16_at(data, 38)?,
                i16_at(data, 40)?,
                i16_at(data, 42)?,
            ],
            // `macStyle` 44, `lowestRecPPEM` 46.
            mac_style: u16_at(data, 44)?,
            lowest_rec_ppem: u16_at(data, 46)?,
            index_to_loc_format,
        })
    }
}
