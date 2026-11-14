//! `cmap`, character to glyph index mapping (OpenType 1.9, chapter `cmap`;
//! Apple's manual, "'cmap' table").
//!
//! <https://learn.microsoft.com/en-us/typography/opentype/otspec190/cmap>.
//!
//! Formats 0, 4, 6 and 12 are read: 4 and 12 are the chapter's "standard"
//! subtables for the BMP and the full repertoire, and the vendored fonts
//! also carry 6 (DejaVu Serif, Source Serif 4, fontations' `cmap6.ttf`).
//! Formats 2, 8, 10, 13 and 14 are [`Subtable::Unsupported`].

use crate::read::{add, element, lower_bound, slice, tail, u8_at, u16_at, u32_at, us};
use crate::{Error, Tag};

/// Size of the `cmap` header: `version`, `numTables`.
const HEADER: usize = 4;
/// Size of one EncodingRecord: `platformID`, `encodingID`,
/// `subtableOffset`.
const ENCODING_RECORD: usize = 8;

/// One EncodingRecord (chapter `cmap`, "'cmap' Header").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EncodingRecord {
    /// `platformID`: 0 Unicode, 1 Macintosh, 2 ISO (deprecated), 3
    /// Windows, 4 Custom.
    pub platform_id: u16,
    /// `encodingID`: "Platform-specific encoding ID."
    pub encoding_id: u16,
    /// `subtableOffset`: "Byte offset from beginning of table to the
    /// subtable for this encoding."
    pub offset: u32,
}

impl EncodingRecord {
    /// Whether the record's encoding is Unicode: platform 0 with encoding
    /// 0 to 4 or 6 (5 is "Unicode Variation Sequences—for use with subtable
    /// format 14", not a mapping), or Windows (3) with encoding 1 ("Unicode
    /// BMP") or 10 ("Unicode full repertoire").
    pub fn is_unicode(&self) -> bool {
        match self.platform_id {
            0 => self.encoding_id <= 4 || self.encoding_id == 6,
            3 => self.encoding_id == 1 || self.encoding_id == 10,
            _ => false,
        }
    }

    /// Whether the encoding covers the full repertoire: (3,10), or platform
    /// 0 encodings 4 ("Unicode full repertoire") and 6.
    pub fn is_full_repertoire(&self) -> bool {
        matches!(
            (self.platform_id, self.encoding_id),
            (3, 10) | (0, 4) | (0, 6)
        )
    }
}

/// The `cmap` table.
#[derive(Debug, Clone, Copy)]
pub struct Cmap<'a> {
    data: &'a [u8],
    num_tables: u16,
}

impl<'a> Cmap<'a> {
    /// The header: `version` "Table version number (0)", `numTables`, and
    /// `numTables` EncodingRecords, all in the table.
    pub fn parse(data: &'a [u8]) -> Result<Self, Error> {
        if u16_at(data, 0)? != 0 {
            return Err(Error::UnsupportedVersion(Tag::CMAP));
        }
        let num_tables = u16_at(data, 2)?;
        if element(HEADER, usize::from(num_tables), ENCODING_RECORD)? > data.len() {
            return Err(Error::Truncated);
        }
        Ok(Self { data, num_tables })
    }

    /// `numTables`.
    pub fn num_tables(&self) -> u16 {
        self.num_tables
    }

    /// `encodingRecords[index]`.
    pub fn record(&self, index: u16) -> Result<EncodingRecord, Error> {
        let at = element(HEADER, usize::from(index), ENCODING_RECORD)?;
        Ok(EncodingRecord {
            platform_id: u16_at(self.data, at)?,
            encoding_id: u16_at(self.data, add(at, 2)?)?,
            offset: u32_at(self.data, add(at, 4)?)?,
        })
    }

    /// The subtable `record` points to. A `subtableOffset` of 0 would put
    /// the subtable on the `cmap` header itself; it is read as no subtable
    /// (a NULL offset), [`Error::InvalidValue`].
    pub fn subtable(&self, record: &EncodingRecord) -> Result<Subtable<'a>, Error> {
        if record.offset == 0 {
            return Err(Error::InvalidValue(Tag::CMAP));
        }
        Subtable::parse(tail(self.data, us(record.offset))?)
    }

    /// The subtable a face maps characters with: among the Unicode
    /// records, a format 12 subtable of the full repertoire, else a format
    /// 4 or 12 subtable, else a format 6 or 0 one; the first record wins
    /// among equals. Records whose subtable does not parse are skipped.
    /// Returns the record's index with the subtable, or `Ok(None)` if no
    /// Unicode subtable is readable.
    pub fn best_subtable(&self) -> Result<Option<(u16, Subtable<'a>)>, Error> {
        let mut best: Option<(u8, u16, Subtable<'a>)> = None;
        for i in 0..self.num_tables {
            let record = self.record(i)?;
            if !record.is_unicode() {
                continue;
            }
            let Ok(subtable) = self.subtable(&record) else {
                continue;
            };
            let rank = match subtable {
                Subtable::Format12(_) if record.is_full_repertoire() => 0,
                Subtable::Format4(_) | Subtable::Format12(_) => 1,
                Subtable::Format6(_) | Subtable::Format0(_) => 2,
                Subtable::Unsupported(_) => continue,
            };
            if best.as_ref().is_none_or(|(r, _, _)| rank < *r) {
                best = Some((rank, i, subtable));
            }
        }
        Ok(best.map(|(_, i, s)| (i, s)))
    }
}

/// One mapping subtable, from its offset to the end of `cmap`.
#[derive(Debug, Clone, Copy)]
pub enum Subtable<'a> {
    /// Format 0: "Byte encoding table".
    Format0(Format0<'a>),
    /// Format 4: "Segment mapping to delta values".
    Format4(Format4<'a>),
    /// Format 6: "Trimmed table mapping".
    Format6(Format6<'a>),
    /// Format 12: "Segmented coverage".
    Format12(Format12<'a>),
    /// Any other `format`, not read.
    Unsupported(u16),
}

impl<'a> Subtable<'a> {
    /// Read the `format` field and the format's header.
    pub fn parse(data: &'a [u8]) -> Result<Self, Error> {
        Ok(match u16_at(data, 0)? {
            0 => Self::Format0(Format0::parse(data)?),
            4 => Self::Format4(Format4::parse(data)?),
            6 => Self::Format6(Format6::parse(data)?),
            12 => Self::Format12(Format12::parse(data)?),
            other => Self::Unsupported(other),
        })
    }

    /// The glyph for `c`, or `None` for "missingGlyph" (glyph 0) and for
    /// characters the subtable does not cover.
    pub fn map(&self, c: u32) -> Result<Option<u16>, Error> {
        let glyph = match self {
            Self::Format0(t) => t.map(c)?,
            Self::Format4(t) => t.map(c)?,
            Self::Format6(t) => t.map(c)?,
            Self::Format12(t) => t.map(c)?,
            Self::Unsupported(_) => 0,
        };
        Ok((glyph != 0).then_some(glyph))
    }

    /// Call `f(first, last)` for every range of character codes the
    /// subtable describes, in its order; [`Self::map`] decides which of
    /// them map to a glyph. Ranges are clamped to U+10FFFF.
    pub fn ranges(&self, mut f: impl FnMut(u32, u32)) -> Result<(), Error> {
        match self {
            Self::Format0(_) => f(0, 255),
            Self::Format4(t) => {
                for i in 0..t.seg_count {
                    let start = t.array(START_CODE, i)?;
                    let end = t.array(END_CODE, i)?;
                    if start <= end {
                        f(u32::from(start), u32::from(end));
                    }
                }
            }
            Self::Format6(t) => {
                if let Some(last) = u32::from(t.entry_count).checked_sub(1) {
                    f(
                        u32::from(t.first_code),
                        u32::from(t.first_code).saturating_add(last),
                    );
                }
            }
            Self::Format12(t) => {
                for i in 0..t.num_groups {
                    let (start, end, _) = t.group(i)?;
                    let end = end.min(MAX_CODE_POINT);
                    if start <= end {
                        f(start, end);
                    }
                }
            }
            Self::Unsupported(_) => {}
        }
        Ok(())
    }
}

impl Subtable<'_> {
    /// Whether the subtable's ranges are in the order the chapter requires:
    /// format 4's segments "sorted in order of increasing endCode values",
    /// each starting after the previous one ends (and not after its own
    /// end), and format 12's groups "sorted by increasing startCharCode",
    /// with "A group's endCharCode … less than the startCharCode of the
    /// following group". Formats 0 and 6 have one range. A lookup in an
    /// unordered subtable still terminates and reads only inside it, but
    /// which segment the search finds is then not defined by the chapter.
    pub fn is_ordered(&self) -> Result<bool, Error> {
        let mut previous_end: Option<u32> = None;
        let mut ok = true;
        let mut visit = |start: u32, end: u32| {
            if start > end || previous_end.is_some_and(|p| start <= p) {
                ok = false;
            }
            previous_end = Some(end);
        };
        match self {
            Self::Format4(t) => {
                for i in 0..t.seg_count {
                    visit(
                        u32::from(t.array(START_CODE, i)?),
                        u32::from(t.array(END_CODE, i)?),
                    );
                }
            }
            Self::Format12(t) => {
                for i in 0..t.num_groups {
                    let (start, end, _) = t.group(i)?;
                    visit(start, end);
                }
            }
            Self::Format0(_) | Self::Format6(_) | Self::Unsupported(_) => {}
        }
        Ok(ok)
    }
}

/// The last Unicode code point.
const MAX_CODE_POINT: u32 = 0x10_FFFF;

/// Format 0: `format`, `length`, `language`, then `glyphIdArray[256]`,
/// "An array that maps character codes to glyph index values".
#[derive(Debug, Clone, Copy)]
pub struct Format0<'a> {
    data: &'a [u8],
}

impl<'a> Format0<'a> {
    fn parse(data: &'a [u8]) -> Result<Self, Error> {
        Ok(Self {
            data: slice(data, 6, 256)?,
        })
    }

    fn map(&self, c: u32) -> Result<u16, Error> {
        match usize::try_from(c) {
            Ok(i) if i < 256 => Ok(u16::from(u8_at(self.data, i)?)),
            _ => Ok(0),
        }
    }
}

/// Which of format 4's four parallel arrays.
#[derive(Clone, Copy)]
struct Array(usize);
/// `endCode[segCount]`, at 14.
const END_CODE: Array = Array(0);
/// `startCode[segCount]`, after `reservedPad`.
const START_CODE: Array = Array(1);
/// `idDelta[segCount]`.
const ID_DELTA: Array = Array(2);
/// `idRangeOffsets[segCount]`.
const ID_RANGE_OFFSETS: Array = Array(3);

/// Format 4: a four-word header (`segCountX2` and the search fields), then
/// `endCode`, `reservedPad`, `startCode`, `idDelta`, `idRangeOffsets`
/// (`segCount` each) and `glyphIdArray`.
#[derive(Debug, Clone, Copy)]
pub struct Format4<'a> {
    /// From the subtable's start to the end of `cmap` (see the crate's
    /// modelling choices: `length` is not trusted).
    data: &'a [u8],
    /// `segCountX2 / 2`.
    seg_count: u16,
}

impl<'a> Format4<'a> {
    /// `segCountX2` at 6; the four arrays must fit. "segCount, which is not
    /// given directly in the header but is readily derived from
    /// segCountX2".
    fn parse(data: &'a [u8]) -> Result<Self, Error> {
        let seg_count = u16_at(data, 6)? / 2;
        let f = Self { data, seg_count };
        // The last element of the last array must be readable.
        let end = f.array_at(ID_RANGE_OFFSETS, usize::from(seg_count))?;
        if end > data.len() {
            return Err(Error::Truncated);
        }
        Ok(f)
    }

    /// Byte offset of element `index` of `array`. `endCode` starts at 14;
    /// `reservedPad` (2 bytes) separates it from `startCode`.
    fn array_at(&self, array: Array, index: usize) -> Result<usize, Error> {
        let seg = usize::from(self.seg_count)
            .checked_mul(2)
            .ok_or(Error::Overflow)?;
        let start = match array.0 {
            0 => 14,
            n => add(add(14, 2)?, seg.checked_mul(n).ok_or(Error::Overflow)?)?,
        };
        element(start, index, 2)
    }

    fn array(&self, array: Array, index: u16) -> Result<u16, Error> {
        u16_at(self.data, self.array_at(array, usize::from(index))?)
    }

    /// "You search for the first endCode that is greater than or equal to
    /// the character code you want to map. If the corresponding startCode
    /// is less than or equal to the character code, then you use the
    /// corresponding idDelta and idRangeOffset to map the character code to
    /// a glyph index (otherwise, the missingGlyph is returned)."
    fn map(&self, c: u32) -> Result<u16, Error> {
        let Ok(c) = u16::try_from(c) else {
            return Ok(0);
        };
        let i = lower_bound(usize::from(self.seg_count), &c, |i| {
            self.array(END_CODE, u16::try_from(i).map_err(|_| Error::Overflow)?)
        })?;
        let Ok(i) = u16::try_from(i) else {
            return Ok(0);
        };
        if i >= self.seg_count {
            return Ok(0);
        }
        let start = self.array(START_CODE, i)?;
        if start > c {
            return Ok(0);
        }
        let id_delta = self.array(ID_DELTA, i)?;
        let range_offset = self.array(ID_RANGE_OFFSETS, i)?;
        // `c - startCode[i]`, non-negative here.
        let offset = c.wrapping_sub(start);
        if range_offset == 0 {
            // "If the idRangeOffset is 0, the idDelta value is added directly
            // to the character code … the idDelta arithmetic is modulo
            // 65536."
            return Ok(c.wrapping_add(id_delta));
        }
        // "glyphId = *(idRangeOffset[i]/2 + (c - startCode[i]) +
        // &idRangeOffset[i])": in bytes, the address of idRangeOffset[i] plus
        // idRangeOffset[i] plus twice the character's offset.
        let at = add(
            add(
                self.array_at(ID_RANGE_OFFSETS, usize::from(i))?,
                usize::from(range_offset),
            )?,
            usize::from(offset).checked_mul(2).ok_or(Error::Overflow)?,
        )?;
        // An address outside the table maps to missingGlyph rather than
        // failing the lookup (or the whole subtable).
        let Ok(glyph) = u16_at(self.data, at) else {
            return Ok(0);
        };
        // "If the value obtained from the indexing operation is not 0
        // (which indicates missingGlyph), idDelta[i] is added to it".
        Ok(if glyph == 0 {
            0
        } else {
            glyph.wrapping_add(id_delta)
        })
    }
}

/// Format 6: `format`, `length`, `language`, `firstCode`, `entryCount`,
/// `glyphIdArray[entryCount]`.
#[derive(Debug, Clone, Copy)]
pub struct Format6<'a> {
    glyphs: &'a [u8],
    first_code: u16,
    entry_count: u16,
}

impl<'a> Format6<'a> {
    fn parse(data: &'a [u8]) -> Result<Self, Error> {
        let first_code = u16_at(data, 6)?;
        let entry_count = u16_at(data, 8)?;
        let len = usize::from(entry_count)
            .checked_mul(2)
            .ok_or(Error::Overflow)?;
        Ok(Self {
            glyphs: slice(data, 10, len)?,
            first_code,
            entry_count,
        })
    }

    /// "firstCode: First character code of subrange. entryCount: Number of
    /// character codes in subrange."
    fn map(&self, c: u32) -> Result<u16, Error> {
        let Some(i) = c.checked_sub(u32::from(self.first_code)) else {
            return Ok(0);
        };
        if i >= u32::from(self.entry_count) {
            return Ok(0);
        }
        u16_at(self.glyphs, element(0, us(i), 2)?)
    }
}

/// Format 12: `format`, `reserved`, `length`, `language`, `numGroups`, then
/// `groups[numGroups]` SequentialMapGroup records.
#[derive(Debug, Clone, Copy)]
pub struct Format12<'a> {
    groups: &'a [u8],
    num_groups: u32,
}

impl<'a> Format12<'a> {
    fn parse(data: &'a [u8]) -> Result<Self, Error> {
        let num_groups = u32_at(data, 12)?;
        let len = us(num_groups).checked_mul(12).ok_or(Error::Overflow)?;
        Ok(Self {
            groups: slice(data, 16, len)?,
            num_groups,
        })
    }

    /// SequentialMapGroup `i`: `startCharCode`, `endCharCode`,
    /// `startGlyphID`.
    fn group(&self, i: u32) -> Result<(u32, u32, u32), Error> {
        let at = element(0, us(i), 12)?;
        Ok((
            u32_at(self.groups, at)?,
            u32_at(self.groups, add(at, 4)?)?,
            u32_at(self.groups, add(at, 8)?)?,
        ))
    }

    /// "Groups must be sorted by increasing startCharCode. A group's
    /// endCharCode must be less than the startCharCode of the following
    /// group": the first group whose `endCharCode` is not below `c` is the
    /// only one that can hold it. A glyph ID above 65535 cannot name a glyph
    /// (`maxp.numGlyphs` is a `uint16`) and maps to missingGlyph.
    fn map(&self, c: u32) -> Result<u16, Error> {
        let i = lower_bound(us(self.num_groups), &c, |i| {
            Ok(self
                .group(u32::try_from(i).map_err(|_| Error::Overflow)?)?
                .1)
        })?;
        let Ok(i) = u32::try_from(i) else {
            return Ok(0);
        };
        if i >= self.num_groups {
            return Ok(0);
        }
        let (start, _, start_glyph) = self.group(i)?;
        let Some(offset) = c.checked_sub(start) else {
            return Ok(0);
        };
        Ok(start_glyph
            .checked_add(offset)
            .and_then(|g| u16::try_from(g).ok())
            .unwrap_or(0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A format 4 subtable from its four arrays (no glyphIdArray).
    fn format4(end: &[u16], start: &[u16], delta: &[i16], range: &[u16]) -> Vec<u8> {
        let seg = u16::try_from(end.len()).unwrap_or(0);
        let mut d = Vec::new();
        for v in [4, 0, 0, seg.saturating_mul(2), 0, 0, 0] {
            d.extend_from_slice(&u16::to_be_bytes(v));
        }
        end.iter()
            .for_each(|v| d.extend_from_slice(&v.to_be_bytes()));
        d.extend_from_slice(&[0, 0]);
        start
            .iter()
            .for_each(|v| d.extend_from_slice(&v.to_be_bytes()));
        delta
            .iter()
            .for_each(|v| d.extend_from_slice(&v.to_be_bytes()));
        range
            .iter()
            .for_each(|v| d.extend_from_slice(&v.to_be_bytes()));
        d
    }

    /// The chapter's format 4 example: "the variant part of the table to
    /// map characters 10-20, 30-90, and 153-480 onto a contiguous range of
    /// glyph indices". Its mappings: 10 ⇒ 1, 20 ⇒ 11, 30 ⇒ 12, 90 ⇒ 72,
    /// 153 ⇒ 73, 480 ⇒ 400. (The example's header gives entrySelector 4,
    /// which by the chapter's own formula is 2; we read neither:
    /// docs/ERRATA.md.)
    #[test]
    fn opentype_format4_example() -> Result<(), Error> {
        let d = format4(
            &[20, 90, 480, 0xFFFF],
            &[10, 30, 153, 0xFFFF],
            &[-9, -18, -80, 1],
            &[0, 0, 0, 0],
        );
        let t = Subtable::parse(&d)?;
        for (c, g) in [(10, 1), (20, 11), (30, 12), (90, 72), (153, 73), (480, 400)] {
            assert_eq!(t.map(c)?, Some(g), "U+{c:04X}");
        }
        // Holes between segments, the 0xFFFF segment (0xFFFF + 1 = 0 mod
        // 65536), and beyond the BMP.
        for c in [9, 21, 29, 91, 152, 481, 0xFFFF, 0x1_0000] {
            assert_eq!(t.map(c)?, None, "U+{c:04X}");
        }
        Ok(())
    }

    /// idRangeOffset indexing: segment 0 (65 to 67) reads glyphIdArray
    /// through its offset, and a zero entry stays missingGlyph.
    #[test]
    fn format4_id_range_offset() -> Result<(), Error> {
        // Two segments; idRangeOffset[0] = 4 points 4 bytes past itself,
        // that is, past idRangeOffset[1], at glyphIdArray[0].
        let mut d = format4(&[67, 0xFFFF], &[65, 0xFFFF], &[5, 1], &[4, 0]);
        for g in [100u16, 0, 102] {
            d.extend_from_slice(&g.to_be_bytes());
        }
        let t = Subtable::parse(&d)?;
        assert_eq!(t.map(65)?, Some(105));
        assert_eq!(t.map(66)?, None);
        assert_eq!(t.map(67)?, Some(107));
        // Truncate glyphIdArray: the address is outside, so missingGlyph.
        d.truncate(d.len().saturating_sub(2));
        assert_eq!(Subtable::parse(&d)?.map(67)?, None);
        Ok(())
    }

    #[test]
    fn format12_groups() -> Result<(), Error> {
        let mut d = Vec::new();
        d.extend_from_slice(&[0, 12, 0, 0, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 2]);
        for v in [0x41u32, 0x43, 1, 0x1_F600, 0x1_F601, 0xFFFF] {
            d.extend_from_slice(&v.to_be_bytes());
        }
        let t = Subtable::parse(&d)?;
        assert_eq!(t.map(0x41)?, Some(1));
        assert_eq!(t.map(0x43)?, Some(3));
        assert_eq!(t.map(0x44)?, None);
        assert_eq!(t.map(0x1_F600)?, Some(0xFFFF));
        // 0xFFFF + 1 is not a glyph ID.
        assert_eq!(t.map(0x1_F601)?, None);
        Ok(())
    }

    #[test]
    fn format6_and_0() -> Result<(), Error> {
        let d = [0, 6, 0, 0, 0, 0, 0, 0x20, 0, 2, 0, 3, 0, 4];
        let t = Subtable::parse(&d)?;
        assert_eq!(t.map(0x1F)?, None);
        assert_eq!(t.map(0x20)?, Some(3));
        assert_eq!(t.map(0x21)?, Some(4));
        assert_eq!(t.map(0x22)?, None);
        let mut z = vec![0, 0, 1, 6, 0, 0];
        z.extend((0..=255u8).rev());
        let t = Subtable::parse(&z)?;
        assert_eq!(t.map(0)?, Some(255));
        assert_eq!(t.map(255)?, None);
        assert_eq!(t.map(256)?, None);
        Ok(())
    }

    #[test]
    fn best_subtable_prefers_full_repertoire() -> Result<(), Error> {
        // Records: (1,0) format 6, (3,1) format 6, (3,10) format 12.
        let mut d = vec![0, 0, 0, 3];
        for (p, e, off) in [(1u16, 0u16, 28u32), (3, 1, 28), (3, 10, 42)] {
            d.extend_from_slice(&p.to_be_bytes());
            d.extend_from_slice(&e.to_be_bytes());
            d.extend_from_slice(&off.to_be_bytes());
        }
        d.extend_from_slice(&[0, 6, 0, 0, 0, 0, 0, 0x41, 0, 1, 0, 7]);
        d.extend_from_slice(&[0, 0]);
        d.extend_from_slice(&[0, 12, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 1]);
        for v in [0x41u32, 0x41, 9] {
            d.extend_from_slice(&v.to_be_bytes());
        }
        let cmap = Cmap::parse(&d)?;
        let (index, best) = cmap.best_subtable()?.ok_or(Error::Truncated)?;
        assert_eq!(index, 2);
        assert_eq!(best.map(0x41)?, Some(9));
        Ok(())
    }
}
