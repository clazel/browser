//! `hmtx`, horizontal metrics (OpenType 1.9, chapter `hmtx`; Apple's
//! manual, "'hmtx' table").
//!
//! <https://learn.microsoft.com/en-us/typography/opentype/otspec190/hmtx>.

use crate::read::{add, element, i16_at, u16_at};
use crate::{Error, Tag};

/// Size of a `longHorMetric`: `advanceWidth` (uint16), `lsb` (int16).
const LONG_HOR_METRIC: usize = 4;

/// The `hmtx` table, with the counts `hhea` and `maxp` give it.
#[derive(Debug, Clone, Copy)]
pub struct Hmtx<'a> {
    data: &'a [u8],
    /// `numberOfHMetrics` (from `hhea`), at least 1.
    number_of_h_metrics: u16,
    /// `numGlyphs` (from `maxp`).
    num_glyphs: u16,
}

impl<'a> Hmtx<'a> {
    /// Check that `data` holds `hMetrics[numberOfHMetrics]` and, "if
    /// numberOfHMetrics is less than the total number of glyphs",
    /// `leftSideBearings[numGlyphs - numberOfHMetrics]`.
    ///
    /// `numberOfHMetrics` 0 is refused: the chapter's lookup, "the advance
    /// width value of the last record applies to all remaining glyph IDs",
    /// needs a last record. One above `numGlyphs` is accepted, and only the
    /// first `numGlyphs` records are ever read.
    pub fn parse(data: &'a [u8], number_of_h_metrics: u16, num_glyphs: u16) -> Result<Self, Error> {
        if number_of_h_metrics == 0 {
            return Err(Error::InvalidValue(Tag::HMTX));
        }
        let bearings = num_glyphs.saturating_sub(number_of_h_metrics);
        let metrics = element(0, usize::from(number_of_h_metrics), LONG_HOR_METRIC)?;
        let size = element(metrics, usize::from(bearings), 2)?;
        if data.len() < size {
            return Err(Error::Truncated);
        }
        Ok(Self {
            data,
            number_of_h_metrics,
            num_glyphs,
        })
    }

    /// Glyph `glyph`'s `advanceWidth`: its own record's, or "the advance
    /// width value of the last record" for glyph IDs at or above
    /// `numberOfHMetrics`.
    pub fn advance(&self, glyph: u16) -> Result<u16, Error> {
        if glyph >= self.num_glyphs {
            return Err(Error::GlyphIndex);
        }
        let last = self.number_of_h_metrics.saturating_sub(1);
        let record = element(0, usize::from(glyph.min(last)), LONG_HOR_METRIC)?;
        u16_at(self.data, record)
    }

    /// Glyph `glyph`'s left side bearing: `hMetrics[glyph].lsb`, or
    /// `leftSideBearings[glyph - numberOfHMetrics]` ("Left side bearings for
    /// glyph IDs greater than or equal to numberOfHMetrics").
    pub fn left_side_bearing(&self, glyph: u16) -> Result<i16, Error> {
        if glyph >= self.num_glyphs {
            return Err(Error::GlyphIndex);
        }
        match glyph.checked_sub(self.number_of_h_metrics) {
            None => i16_at(
                self.data,
                add(element(0, usize::from(glyph), LONG_HOR_METRIC)?, 2)?,
            ),
            Some(i) => {
                let metrics = element(0, usize::from(self.number_of_h_metrics), LONG_HOR_METRIC)?;
                i16_at(self.data, element(metrics, usize::from(i), 2)?)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn last_record_applies_to_the_rest() -> Result<(), Error> {
        // Two records (500, 10), (600, 20), then bearings 30 and -40 for
        // glyphs 2 and 3.
        let data = [1, 0xF4, 0, 10, 2, 0x58, 0, 20, 0, 30, 0xFF, 0xD8];
        let h = Hmtx::parse(&data, 2, 4)?;
        assert_eq!(h.advance(0)?, 500);
        assert_eq!(h.advance(1)?, 600);
        assert_eq!(h.advance(3)?, 600);
        assert_eq!(h.left_side_bearing(1)?, 20);
        assert_eq!(h.left_side_bearing(2)?, 30);
        assert_eq!(h.left_side_bearing(3)?, -40);
        assert_eq!(h.advance(4), Err(Error::GlyphIndex));
        assert_eq!(Hmtx::parse(&data, 2, 5).err(), Some(Error::Truncated));
        assert_eq!(
            Hmtx::parse(&data, 0, 4).err(),
            Some(Error::InvalidValue(Tag::HMTX))
        );
        Ok(())
    }
}
