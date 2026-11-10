//! `maxp`, the maximum profile (OpenType 1.9, chapter `maxp`; Apple's
//! manual, "'maxp' table").
//!
//! <https://learn.microsoft.com/en-us/typography/opentype/otspec190/maxp>.
//!
//! Only `numGlyphs` is read. Version 1.0's other fields describe the
//! TrueType instruction machine (zones, storage, function definitions, stack
//! size), which this crate never runs, and maximums for composites
//! (`maxComponentElements`, `maxComponentDepth`) that a hostile font may
//! state falsely, so the outline decoder uses its own bounds instead.

use crate::read::{u16_at, u32_at};
use crate::{Error, Tag};

/// `version` "0x00005000 for version 0.5".
pub const VERSION_0_5: u32 = 0x0000_5000;
/// `version` "0x00010000 for version 1.0".
pub const VERSION_1_0: u32 = 0x0001_0000;

/// The fields of `maxp` a face uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Maxp {
    /// `version` (`Version16Dot16`): 0.5 or 1.0.
    pub version: u32,
    /// `numGlyphs`: "The number of glyphs in the font."
    pub num_glyphs: u16,
}

impl Maxp {
    /// Parse `maxp`: version 0.5 is 6 bytes, version 1.0 is 32. A table
    /// with `numGlyphs` 0 is refused: index zero is "the missing character"
    /// (`loca`), which every font has.
    pub fn parse(data: &[u8]) -> Result<Self, Error> {
        let version = u32_at(data, 0)?;
        let size = match version {
            VERSION_0_5 => 6,
            VERSION_1_0 => 32,
            _ => return Err(Error::UnsupportedVersion(Tag::MAXP)),
        };
        if data.len() < size {
            return Err(Error::Truncated);
        }
        let num_glyphs = u16_at(data, 4)?;
        if num_glyphs == 0 {
            return Err(Error::InvalidValue(Tag::MAXP));
        }
        Ok(Self {
            version,
            num_glyphs,
        })
    }
}
