//! `loca`, the index to location (OpenType 1.9, chapter `loca`; Apple's
//! manual, "'loca' table").
//!
//! <https://learn.microsoft.com/en-us/typography/opentype/otspec190/loca>.

use crate::head::LocaFormat;
use crate::read::{element, u16_at, u32_at, us};
use crate::{Error, Tag};

/// The `loca` table, with `head.indexToLocFormat` and `maxp.numGlyphs`.
#[derive(Debug, Clone, Copy)]
pub struct Loca<'a> {
    data: &'a [u8],
    format: LocaFormat,
    num_glyphs: u16,
}

impl<'a> Loca<'a> {
    /// Check that `data` holds `offsets[n]` with "n is numGlyphs + 1", of
    /// `Offset16` or `Offset32` as `format` says.
    pub fn parse(data: &'a [u8], format: LocaFormat, num_glyphs: u16) -> Result<Self, Error> {
        let n = usize::from(num_glyphs)
            .checked_add(1)
            .ok_or(Error::Overflow)?;
        if data.len() < element(0, n, entry_size(format))? {
            return Err(Error::Truncated);
        }
        Ok(Self {
            data,
            format,
            num_glyphs,
        })
    }

    /// `offsets[index]` as a byte offset into `glyf`: short entries hold
    /// "the actual local offset divided by 2".
    fn offset(&self, index: usize) -> Result<usize, Error> {
        match self.format {
            LocaFormat::Short => {
                let half = u16_at(self.data, element(0, index, 2)?)?;
                usize::from(half).checked_mul(2).ok_or(Error::Overflow)
            }
            LocaFormat::Long => Ok(us(u32_at(self.data, element(0, index, 4)?)?)),
        }
    }

    /// The byte range of glyph `glyph` in `glyf`: from `offsets[glyph]` to
    /// `offsets[glyph + 1]` ("there is an extra entry after the last valid
    /// index" to give the last glyph's length). Equal offsets are a glyph
    /// without an outline. A decreasing pair is malformed: the chapter
    /// gives lengths only as differences, so it cannot mean anything.
    pub fn glyph_range(&self, glyph: u16) -> Result<(usize, usize), Error> {
        if glyph >= self.num_glyphs {
            return Err(Error::GlyphIndex);
        }
        let start = self.offset(usize::from(glyph))?;
        let end = self.offset(usize::from(glyph).checked_add(1).ok_or(Error::Overflow)?)?;
        if end < start {
            return Err(Error::InvalidValue(Tag::LOCA));
        }
        Ok((start, end))
    }
}

/// Bytes per entry.
fn entry_size(format: LocaFormat) -> usize {
    match format {
        LocaFormat::Short => 2,
        LocaFormat::Long => 4,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn short_offsets_are_halved() -> Result<(), Error> {
        let data = [0, 0, 0, 5, 0, 5, 0, 9];
        let l = Loca::parse(&data, LocaFormat::Short, 3)?;
        assert_eq!(l.glyph_range(0)?, (0, 10));
        assert_eq!(l.glyph_range(1)?, (10, 10));
        assert_eq!(l.glyph_range(2)?, (10, 18));
        assert_eq!(l.glyph_range(3), Err(Error::GlyphIndex));
        let long = [0, 0, 0, 8, 0, 0, 0, 4];
        let l = Loca::parse(&long, LocaFormat::Long, 1)?;
        assert_eq!(l.glyph_range(0), Err(Error::InvalidValue(Tag::LOCA)));
        assert_eq!(
            Loca::parse(&long, LocaFormat::Long, 2).err(),
            Some(Error::Truncated)
        );
        Ok(())
    }
}
