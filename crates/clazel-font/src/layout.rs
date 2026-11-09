//! OpenType Layout: the Common Table Formats (OpenType 1.9, chapter
//! `chapter2`) that `GPOS` pair adjustment needs, and `GPOS` LookupTypes 2
//! and 9 (chapter `gpos`).
//!
//! <https://learn.microsoft.com/en-us/typography/opentype/otspec190/chapter2>,
//! <https://learn.microsoft.com/en-us/typography/opentype/otspec190/gpos>.
//! Apple's manual has no chapter on `GPOS` (Apple's layout tables are
//! `morx` and `kerx`), so the second text here is the chapters' worked
//! examples, which are the unit tests.
//!
//! Every offset in these tables is relative to the table that holds it
//! ("from beginning of …"), so each table below is a slice starting at its
//! own first byte, made from its parent's slice by [`sub`].

use crate::read::{add, element, i16_at, lower_bound, tail, u16_at, u32_at, us};
use crate::{Error, Tag};

/// The sub-table at `offset` from the start of `parent`.
fn sub(parent: &[u8], offset: usize) -> Result<&[u8], Error> {
    tail(parent, offset)
}

/// Checks that `count` records of `size` bytes, starting at `start`, are
/// inside `data`, and returns `count`. Every loop over a record array goes
/// through this first, so its iterations are bounded by `data.len()`.
fn checked_count(data: &[u8], start: usize, count: u16, size: usize) -> Result<u16, Error> {
    if element(start, usize::from(count), size)? > data.len() {
        return Err(Error::Truncated);
    }
    Ok(count)
}

/// The `kern` feature tag.
pub const KERN: Tag = Tag(*b"kern");
/// The `DFLT` script tag: "the default script", used when a script is not
/// listed.
pub const DFLT: Tag = Tag(*b"DFLT");
/// `requiredFeatureIndex` "if no required features = 0xFFFF".
const NO_REQUIRED_FEATURE: u16 = 0xFFFF;

/// A Coverage table (chapter2, "Coverage Table").
#[derive(Debug, Clone, Copy)]
pub struct Coverage<'a> {
    data: &'a [u8],
}

impl<'a> Coverage<'a> {
    /// The table at the start of `data`.
    pub fn new(data: &'a [u8]) -> Self {
        Self { data }
    }

    /// The Coverage Index of `glyph`, if it is covered.
    ///
    /// - Format 1, "Individual glyph indices": `coverageFormat`,
    ///   `glyphCount`, `glyphArray[glyphCount]` "in numerical order"; the
    ///   index is the glyph's position in the array.
    /// - Format 2, "Range of glyphs": `coverageFormat`, `rangeCount`,
    ///   RangeRecords (`startGlyphID`, `endGlyphID`, `startCoverageIndex`)
    ///   "in Start glyph ID order"; the index is `startCoverageIndex +
    ///   glyph − startGlyphID`.
    ///
    /// Any other format covers nothing.
    pub fn index(&self, glyph: u16) -> Result<Option<u16>, Error> {
        let d = self.data;
        match u16_at(d, 0)? {
            1 => {
                let n = checked_count(d, 4, u16_at(d, 2)?, 2)?;
                let i = lower_bound(usize::from(n), &glyph, |i| u16_at(d, element(4, i, 2)?))?;
                if i >= usize::from(n) || u16_at(d, element(4, i, 2)?)? != glyph {
                    return Ok(None);
                }
                Ok(u16::try_from(i).ok())
            }
            2 => {
                let n = checked_count(d, 4, u16_at(d, 2)?, 6)?;
                // The first range whose endGlyphID is not below the glyph.
                let i = lower_bound(usize::from(n), &glyph, |i| {
                    u16_at(d, add(element(4, i, 6)?, 2)?)
                })?;
                if i >= usize::from(n) {
                    return Ok(None);
                }
                let at = element(4, i, 6)?;
                let start = u16_at(d, at)?;
                if glyph < start {
                    return Ok(None);
                }
                let start_index = u16_at(d, add(at, 4)?)?;
                Ok(start_index.checked_add(glyph.wrapping_sub(start)))
            }
            _ => Ok(None),
        }
    }
}

impl Coverage<'_> {
    /// Whether the table is in the order chapter2 requires (format 1's
    /// glyphs "in numerical order", format 2's ranges "in Start glyph ID
    /// order", disjoint, each with start not after end). A lookup in an
    /// unordered table still reads only inside it.
    pub fn is_ordered(&self) -> Result<bool, Error> {
        let d = self.data;
        match u16_at(d, 0)? {
            1 => {
                let n = checked_count(d, 4, u16_at(d, 2)?, 2)?;
                let mut previous: Option<u16> = None;
                for i in 0..n {
                    let g = u16_at(d, element(4, usize::from(i), 2)?)?;
                    if previous.is_some_and(|p| g <= p) {
                        return Ok(false);
                    }
                    previous = Some(g);
                }
                Ok(true)
            }
            2 => ranges_ordered(d),
            _ => Ok(true),
        }
    }
}

/// Whether the six-byte range records of a Coverage or ClassDef format 2
/// table (`startGlyphID`, `endGlyphID`, …) are sorted and disjoint.
fn ranges_ordered(d: &[u8]) -> Result<bool, Error> {
    let n = checked_count(d, 4, u16_at(d, 2)?, 6)?;
    let mut previous: Option<u16> = None;
    for i in 0..n {
        let at = element(4, usize::from(i), 6)?;
        let (start, end) = (u16_at(d, at)?, u16_at(d, add(at, 2)?)?);
        if start > end || previous.is_some_and(|p| start <= p) {
            return Ok(false);
        }
        previous = Some(end);
    }
    Ok(true)
}

/// A Class Definition table (chapter2, "Class Definition Table").
#[derive(Debug, Clone, Copy)]
pub struct ClassDef<'a> {
    data: &'a [u8],
}

impl<'a> ClassDef<'a> {
    /// The table at the start of `data`.
    pub fn new(data: &'a [u8]) -> Self {
        Self { data }
    }

    /// The class of `glyph`: "Any glyph not included in the range of
    /// covered glyph IDs automatically belongs to Class 0."
    ///
    /// - Format 1: `classFormat`, `startGlyphID`, `glyphCount`,
    ///   `classValueArray[glyphCount]`.
    /// - Format 2: `classFormat`, `classRangeCount`, ClassRangeRecords
    ///   (`startGlyphID`, `endGlyphID`, `class`) "ordered by startGlyphID".
    ///
    /// Any other format assigns class 0 to everything.
    pub fn class(&self, glyph: u16) -> Result<u16, Error> {
        let d = self.data;
        match u16_at(d, 0)? {
            1 => {
                let start = u16_at(d, 2)?;
                let n = checked_count(d, 6, u16_at(d, 4)?, 2)?;
                match glyph.checked_sub(start) {
                    Some(i) if i < n => u16_at(d, element(6, usize::from(i), 2)?),
                    _ => Ok(0),
                }
            }
            2 => {
                let n = checked_count(d, 4, u16_at(d, 2)?, 6)?;
                let i = lower_bound(usize::from(n), &glyph, |i| {
                    u16_at(d, add(element(4, i, 6)?, 2)?)
                })?;
                if i >= usize::from(n) {
                    return Ok(0);
                }
                let at = element(4, i, 6)?;
                if glyph < u16_at(d, at)? {
                    return Ok(0);
                }
                u16_at(d, add(at, 4)?)
            }
            _ => Ok(0),
        }
    }
}

impl ClassDef<'_> {
    /// Whether a format 2 table's ranges are sorted and disjoint (format 1
    /// has one range).
    pub fn is_ordered(&self) -> Result<bool, Error> {
        match u16_at(self.data, 0)? {
            2 => ranges_ordered(self.data),
            _ => Ok(true),
        }
    }
}

/// A ValueRecord's values (gpos, "Value Record"). The four Device or
/// VariationIndex offsets are skipped: they adjust values per size or per
/// variation instance, which this crate does not model.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ValueRecord {
    /// `xPlacement`: "Horizontal adjustment for placement, in design
    /// units."
    pub x_placement: i16,
    /// `yPlacement`.
    pub y_placement: i16,
    /// `xAdvance`: "Horizontal adjustment for advance, in design units —
    /// only used for horizontal layout."
    pub x_advance: i16,
    /// `yAdvance`.
    pub y_advance: i16,
}

/// The size in bytes of a ValueRecord with `format`: two bytes per flag
/// set ("ValueFormat flags"). The chapter marks 0xFF00 "Reserved for future
/// use (set to zero)" and does not say how a reader sizes a record that sets
/// them; we count each as one more two-byte field, skipped, as HarfBuzz,
/// `ttf-parser` and `read-fonts` do, so record arrays have the same stride
/// in all of them.
pub fn value_record_size(format: u16) -> usize {
    us(format.count_ones()).saturating_mul(2)
}

impl ValueRecord {
    /// Read a ValueRecord of `format` at `at`: present fields appear in the
    /// order `xPlacement`, `yPlacement`, `xAdvance`, `yAdvance`, then the
    /// four device offsets.
    pub fn read(data: &[u8], at: usize, format: u16) -> Result<Self, Error> {
        let mut v = Self::default();
        let mut at = at;
        let mut field = |bit: u16| -> Result<i16, Error> {
            if format & bit == 0 {
                return Ok(0);
            }
            let x = i16_at(data, at)?;
            at = add(at, 2)?;
            Ok(x)
        };
        v.x_placement = field(0x0001)?;
        v.y_placement = field(0x0002)?;
        v.x_advance = field(0x0004)?;
        v.y_advance = field(0x0008)?;
        for bit in [0x0010, 0x0020, 0x0040, 0x0080] {
            field(bit)?;
        }
        Ok(v)
    }
}

/// What a pair adjustment does to the two glyphs.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct PairValue {
    /// `valueRecord1`: "Positioning data for the first glyph in the pair".
    pub first: ValueRecord,
    /// `valueRecord2`: "Positioning data for the second glyph".
    pub second: ValueRecord,
}

/// The `GPOS` table.
#[derive(Debug, Clone, Copy)]
pub struct Gpos<'a> {
    script_list: &'a [u8],
    feature_list: &'a [u8],
    lookup_list: &'a [u8],
}

impl<'a> Gpos<'a> {
    /// The header: `majorVersion` 1, `minorVersion` 0 or 1 (1.1 adds
    /// `featureVariationsOffset`, not read: no variations), and the three
    /// `Offset16`s "from beginning of GPOS table".
    pub fn parse(data: &'a [u8]) -> Result<Self, Error> {
        if u16_at(data, 0)? != 1 || u16_at(data, 2)? > 1 {
            return Err(Error::UnsupportedVersion(Tag::GPOS));
        }
        Ok(Self {
            script_list: sub(data, usize::from(u16_at(data, 4)?))?,
            feature_list: sub(data, usize::from(u16_at(data, 6)?))?,
            lookup_list: sub(data, usize::from(u16_at(data, 8)?))?,
        })
    }

    /// The default LangSys table of script `script`, or of `DFLT` if
    /// `script` is not listed: "An application should use a DFLT script
    /// table if there is not a script table associated with the specific
    /// script of the text being formatted" (chapter2, "Script Table and
    /// Language System Record"). `Ok(None)` if neither is listed or the
    /// script has no `defaultLangSysOffset`. Language-specific LangSys
    /// tables are not used (the default one only; listed in the crate's
    /// modelling choices).
    fn default_lang_sys(&self, script: Tag) -> Result<Option<&'a [u8]>, Error> {
        let d = self.script_list;
        // ScriptList: `scriptCount`, ScriptRecords (`scriptTag`,
        // `scriptOffset` "from beginning of ScriptList").
        let n = checked_count(d, 2, u16_at(d, 0)?, 6)?;
        let mut found = None;
        for wanted in [script, DFLT] {
            for i in 0..n {
                let at = element(2, usize::from(i), 6)?;
                if crate::read::tag_at(d, at)? == wanted {
                    found = Some(usize::from(u16_at(d, add(at, 4)?)?));
                    break;
                }
            }
            if found.is_some() {
                break;
            }
        }
        let Some(offset) = found else {
            return Ok(None);
        };
        // Script: `defaultLangSysOffset` "from beginning of Script table —
        // may be NULL".
        let script = sub(d, offset)?;
        match u16_at(script, 0)? {
            0 => Ok(None),
            o => sub(script, usize::from(o)).map(Some),
        }
    }

    /// The LookupList indices of the `kern` features of `script`'s default
    /// LangSys (with its required feature, if that is `kern`), sorted and
    /// without repeats: "Next, the client arranges the indices numerically
    /// into their LookupList order" (chapter2, "Feature List Table").
    /// Indices not below `lookupCount` are dropped.
    pub fn kern_lookups(&self, script: Tag) -> Result<Vec<u16>, Error> {
        let mut out = Vec::new();
        let Some(lang_sys) = self.default_lang_sys(script)? else {
            return Ok(out);
        };
        // LangSys: `lookupOrderOffset` (reserved), `requiredFeatureIndex`,
        // `featureIndexCount`, `featureIndices[featureIndexCount]`.
        let required = u16_at(lang_sys, 2)?;
        let n = checked_count(lang_sys, 6, u16_at(lang_sys, 4)?, 2)?;
        let fl = self.feature_list;
        // FeatureList: `featureCount`, FeatureRecords (`featureTag`,
        // `featureOffset` "from beginning of FeatureList").
        let feature_count = checked_count(fl, 2, u16_at(fl, 0)?, 6)?;
        let lookup_count = u16_at(self.lookup_list, 0)?;
        let indices = (0..n)
            .map(|i| u16_at(lang_sys, element(6, usize::from(i), 2)?))
            .chain((required != NO_REQUIRED_FEATURE).then_some(Ok(required)));
        for index in indices {
            let index = index?;
            if index >= feature_count {
                continue;
            }
            let at = element(2, usize::from(index), 6)?;
            if crate::read::tag_at(fl, at)? != KERN {
                continue;
            }
            // Feature: `featureParamsOffset`, `lookupIndexCount`,
            // `lookupListIndices[lookupIndexCount]`.
            let feature = sub(fl, usize::from(u16_at(fl, add(at, 4)?)?))?;
            let m = checked_count(feature, 4, u16_at(feature, 2)?, 2)?;
            for j in 0..m {
                let lookup = u16_at(feature, element(4, usize::from(j), 2)?)?;
                if lookup < lookup_count {
                    out.push(lookup);
                }
            }
        }
        out.sort_unstable();
        out.dedup();
        Ok(out)
    }

    /// Lookup `index` of the LookupList: `lookupType` and its subtables.
    fn lookup(&self, index: u16) -> Result<(u16, &'a [u8], u16), Error> {
        let ll = self.lookup_list;
        // LookupList: `lookupCount`, `lookupOffsets[lookupCount]` "from
        // beginning of LookupList".
        let n = checked_count(ll, 2, u16_at(ll, 0)?, 2)?;
        if index >= n {
            return Err(Error::Truncated);
        }
        let lookup = sub(
            ll,
            usize::from(u16_at(ll, element(2, usize::from(index), 2)?)?),
        )?;
        // Lookup: `lookupType`, `lookupFlag`, `subTableCount`,
        // `subtableOffsets[subTableCount]` "from beginning of Lookup table".
        let kind = u16_at(lookup, 0)?;
        let count = checked_count(lookup, 6, u16_at(lookup, 4)?, 2)?;
        Ok((kind, lookup, count))
    }

    /// Apply lookup `index` to the pair (`first`, `second`): its subtables
    /// in order, and the first that applies decides. chapter2 says "If a
    /// glyph does not appear in a Coverage table, the client can skip that
    /// subtable and move immediately to the next subtable"; that a format 1
    /// subtable whose PairSet lacks the second glyph also passes to the next
    /// is our reading, as HarfBuzz's and `ttf-parser`'s. Lookups other than
    /// type 2, or type 9 extensions of type 2, never apply.
    pub fn pair_adjustment(
        &self,
        index: u16,
        first: u16,
        second: u16,
    ) -> Result<Option<PairValue>, Error> {
        let (kind, lookup, count) = self.lookup(index)?;
        for i in 0..count {
            let subtable = sub(
                lookup,
                usize::from(u16_at(lookup, element(6, usize::from(i), 2)?)?),
            )?;
            let pair_pos = match kind {
                2 => subtable,
                9 => match extension(subtable)? {
                    Some(s) => s,
                    None => continue,
                },
                _ => return Ok(None),
            };
            if let Some(v) = pair_pos_apply(pair_pos, first, second)? {
                return Ok(Some(v));
            }
        }
        Ok(None)
    }

    /// Whether every Coverage, ClassDef and PairSet that lookup `index`'s
    /// pair adjustment subtables use is in the order the chapters require;
    /// on unordered data each engine's bisection finds different elements.
    pub fn lookup_is_ordered(&self, index: u16) -> Result<bool, Error> {
        let (kind, lookup, count) = self.lookup(index)?;
        for i in 0..count {
            let subtable = sub(
                lookup,
                usize::from(u16_at(lookup, element(6, usize::from(i), 2)?)?),
            )?;
            let data = match kind {
                2 => subtable,
                9 => match extension(subtable)? {
                    Some(s) => s,
                    None => continue,
                },
                _ => return Ok(true),
            };
            if !pair_pos_is_ordered(data)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// The horizontal kerning for (`first`, `second`) from `lookups`, in
    /// font units: the sum of `valueRecord1.xAdvance` over the lookups that
    /// apply. The other values (placements, the second glyph's record) are
    /// in [`Self::pair_adjustment`] for the shaper to use.
    pub fn kerning(&self, lookups: &[u16], first: u16, second: u16) -> Result<i32, Error> {
        let mut total = 0i32;
        for &l in lookups {
            if let Some(v) = self.pair_adjustment(l, first, second)? {
                total = total
                    .checked_add(i32::from(v.first.x_advance))
                    .ok_or(Error::Overflow)?;
            }
        }
        Ok(total)
    }
}

/// LookupType 9, "Extension Positioning": `posFormat` 1,
/// `extensionLookupType`, `extensionOffset` (`Offset32` "from beginning of
/// ExtensionPosFormat1 subtable"). Only extensions of type 2 are followed;
/// "The extensionLookupType field must be set to any lookup type other
/// than 9", so a nested extension is never followed.
fn extension(data: &[u8]) -> Result<Option<&[u8]>, Error> {
    if u16_at(data, 0)? != 1 || u16_at(data, 2)? != 2 {
        return Ok(None);
    }
    sub(data, us(u32_at(data, 4)?)).map(Some)
}

/// Whether a PairPos subtable's Coverage, ClassDefs and PairSets are
/// ordered (see [`Gpos::lookup_is_ordered`]).
fn pair_pos_is_ordered(data: &[u8]) -> Result<bool, Error> {
    let coverage = match u16_at(data, 2)? {
        0 => return Ok(true),
        o => Coverage::new(sub(data, usize::from(o))?),
    };
    if !coverage.is_ordered()? {
        return Ok(false);
    }
    match u16_at(data, 0)? {
        1 => {
            let record = add(
                add(2, value_record_size(u16_at(data, 4)?))?,
                value_record_size(u16_at(data, 6)?),
            )?;
            let n = checked_count(data, 10, u16_at(data, 8)?, 2)?;
            for i in 0..n {
                let o = u16_at(data, element(10, usize::from(i), 2)?)?;
                if o == 0 {
                    continue;
                }
                let set = sub(data, usize::from(o))?;
                let m = checked_count(set, 2, u16_at(set, 0)?, record)?;
                let mut previous: Option<u16> = None;
                for j in 0..m {
                    let g = u16_at(set, element(2, usize::from(j), record)?)?;
                    if previous.is_some_and(|p| g <= p) {
                        return Ok(false);
                    }
                    previous = Some(g);
                }
            }
            Ok(true)
        }
        2 => Ok(
            ClassDef::new(sub(data, usize::from(u16_at(data, 8)?))?).is_ordered()?
                && ClassDef::new(sub(data, usize::from(u16_at(data, 10)?))?).is_ordered()?,
        ),
        _ => Ok(true),
    }
}

/// A PairPos subtable applied to (`first`, `second`), or `Ok(None)` if it
/// does not apply.
pub fn pair_pos_apply(data: &[u8], first: u16, second: u16) -> Result<Option<PairValue>, Error> {
    let format = u16_at(data, 0)?;
    // Both formats: `posFormat`, `coverageOffset` "from beginning of PairPos
    // subtable", `valueFormat1`, `valueFormat2`.
    // A NULL (zero) coverage offset covers nothing.
    let coverage = match u16_at(data, 2)? {
        0 => return Ok(None),
        o => Coverage::new(sub(data, usize::from(o))?),
    };
    let Some(coverage_index) = coverage.index(first)? else {
        return Ok(None);
    };
    let vf1 = u16_at(data, 4)?;
    let vf2 = u16_at(data, 6)?;
    let (size1, size2) = (value_record_size(vf1), value_record_size(vf2));
    match format {
        // "Pair Adjustment Positioning Format 1: Adjustments for Glyph
        // Pairs": `pairSetCount`, `pairSetOffsets[pairSetCount]`, indexed by
        // Coverage Index.
        1 => {
            let n = checked_count(data, 10, u16_at(data, 8)?, 2)?;
            if coverage_index >= n {
                return Ok(None);
            }
            // A NULL (zero) PairSet offset has no pairs.
            let set = match u16_at(data, element(10, usize::from(coverage_index), 2)?)? {
                0 => return Ok(None),
                o => sub(data, usize::from(o))?,
            };
            // PairSet: `pairValueCount`, PairValueRecords (`secondGlyph`,
            // `valueRecord1`, `valueRecord2`) "ordered by glyph ID of the
            // second glyph".
            let record = add(add(2, size1)?, size2)?;
            let m = checked_count(set, 2, u16_at(set, 0)?, record)?;
            let i = lower_bound(usize::from(m), &second, |i| {
                u16_at(set, element(2, i, record)?)
            })?;
            if i >= usize::from(m) {
                return Ok(None);
            }
            let at = element(2, i, record)?;
            if u16_at(set, at)? != second {
                return Ok(None);
            }
            let v1_at = add(at, 2)?;
            Ok(Some(PairValue {
                first: ValueRecord::read(set, v1_at, vf1)?,
                second: ValueRecord::read(set, add(v1_at, size1)?, vf2)?,
            }))
        }
        // "Pair Adjustment Positioning Format 2: Class Pair Adjustment":
        // `classDef1Offset`, `classDef2Offset`, `class1Count`,
        // `class2Count`, then `class1Records[class1Count]`, each
        // `class2Records[class2Count]` of (`valueRecord1`, `valueRecord2`).
        // A class not below its count does not apply (it has no record).
        2 => {
            let class_def1 = ClassDef::new(sub(data, usize::from(u16_at(data, 8)?))?);
            let class_def2 = ClassDef::new(sub(data, usize::from(u16_at(data, 10)?))?);
            let class1_count = u16_at(data, 12)?;
            let class2_count = u16_at(data, 14)?;
            let c1 = class_def1.class(first)?;
            let c2 = class_def2.class(second)?;
            if c1 >= class1_count || c2 >= class2_count {
                return Ok(None);
            }
            let record = add(size1, size2)?;
            let cell = usize::from(c1)
                .checked_mul(usize::from(class2_count))
                .and_then(|r| r.checked_add(usize::from(c2)))
                .ok_or(Error::Overflow)?;
            let at = element(16, cell, record)?;
            Ok(Some(PairValue {
                first: ValueRecord::read(data, at, vf1)?,
                second: ValueRecord::read(data, add(at, size1)?, vf2)?,
            }))
        }
        _ => Ok(None),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Big-endian bytes of `words`.
    fn words(words: &[u16]) -> Vec<u8> {
        words.iter().flat_map(|w| w.to_be_bytes()).collect()
    }

    /// chapter2, Example 5: CoverageFormat1, the lowercase descenders
    /// g, j, p, q, y (glyph IDs 0x38, 0x3B, 0x41, 0x42, 0x4A).
    #[test]
    fn chapter2_example_5_coverage_format_1() -> Result<(), Error> {
        let d = words(&[1, 5, 0x38, 0x3B, 0x41, 0x42, 0x4A]);
        let c = Coverage::new(&d);
        assert_eq!(c.index(0x38)?, Some(0));
        assert_eq!(c.index(0x42)?, Some(3));
        assert_eq!(c.index(0x4A)?, Some(4));
        assert_eq!(c.index(0x39)?, None);
        assert_eq!(c.index(0x4B)?, None);
        Ok(())
    }

    /// chapter2, Example 6: CoverageFormat2, the numerals 0x4E to 0x57
    /// with StartCoverageIndex 0.
    #[test]
    fn chapter2_example_6_coverage_format_2() -> Result<(), Error> {
        let d = words(&[2, 1, 0x4E, 0x57, 0]);
        let c = Coverage::new(&d);
        assert_eq!(c.index(0x4E)?, Some(0));
        assert_eq!(c.index(0x57)?, Some(9));
        assert_eq!(c.index(0x4D)?, None);
        assert_eq!(c.index(0x58)?, None);
        Ok(())
    }

    /// chapter2, Example 7: ClassDefFormat1 over the 26 lowercase glyphs
    /// from 0x32 ("a"), x-height 0, ascender 1, descender 2. The hex data
    /// gives class 0 to "i", whose comment says "Ascender Class 1"; we
    /// follow the data.
    #[test]
    fn chapter2_example_7_class_def_format_1() -> Result<(), Error> {
        let classes = [
            0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 1, 1, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 2, 0,
        ];
        let mut w = vec![1, 0x32, 26];
        w.extend_from_slice(&classes);
        let d = words(&w);
        let c = ClassDef::new(&d);
        assert_eq!(c.class(0x32)?, 0); // a
        assert_eq!(c.class(0x33)?, 1); // b
        assert_eq!(c.class(0x38)?, 2); // g
        assert_eq!(c.class(0x4B)?, 0); // z
        assert_eq!(c.class(0x4C)?, 0); // past the array
        assert_eq!(c.class(0x31)?, 0); // before it
        Ok(())
    }

    /// chapter2, Example 8: ClassDefFormat2, three ranges.
    #[test]
    fn chapter2_example_8_class_def_format_2() -> Result<(), Error> {
        let d = words(&[2, 3, 0x30, 0x31, 2, 0x40, 0x41, 3, 0xD2, 0xD3, 1]);
        let c = ClassDef::new(&d);
        assert_eq!(c.class(0x30)?, 2);
        assert_eq!(c.class(0x41)?, 3);
        assert_eq!(c.class(0xD3)?, 1);
        assert_eq!(c.class(0x32)?, 0);
        assert_eq!(c.class(0xD4)?, 0);
        Ok(())
    }

    /// gpos, Example 4: PairPosFormat1 kerning "Po" and "To": P (0x2D) and
    /// T (0x31) followed by o (0x59).
    #[test]
    fn gpos_example_4_pair_pos_format_1() -> Result<(), Error> {
        let d = words(&[
            1, 0x1E, 0x0004, 0x0001, 2, 0x0E, 0x16, // PairPosFormat1
            1, 0x59, 0xFFE2, 0xFFEC, // PairSet for P
            1, 0x59, 0xFFD8, 0xFFE7, // PairSet for T
            1, 2, 0x2D, 0x31, // Coverage
        ]);
        let po = pair_pos_apply(&d, 0x2D, 0x59)?.ok_or(Error::Truncated)?;
        assert_eq!(po.first.x_advance, -30);
        assert_eq!(po.second.x_placement, -20);
        let to = pair_pos_apply(&d, 0x31, 0x59)?.ok_or(Error::Truncated)?;
        assert_eq!(to.first.x_advance, -40);
        assert_eq!(to.second.x_placement, -25);
        assert_eq!(pair_pos_apply(&d, 0x2D, 0x5A)?, None);
        assert_eq!(pair_pos_apply(&d, 0x2E, 0x59)?, None);
        Ok(())
    }

    /// gpos, Example 5: PairPosFormat2, v, w, y (0x46, 0x47, 0x49) before
    /// period or comma (0x6A, 0x6B) get xAdvance -50.
    #[test]
    fn gpos_example_5_pair_pos_format_2() -> Result<(), Error> {
        let d = words(&[
            2, 0x18, 0x0004, 0x0000, 0x22, 0x32, 2, 2, // PairPosFormat2
            0, 0, 0, 0xFFCE, // class1Records
            1, 3, 0x46, 0x47, 0x49, // Coverage
            2, 2, 0x46, 0x47, 1, 0x49, 0x49, 1, // LowercaseClassDef
            2, 1, 0x6A, 0x6B, 1, // PunctuationClassDef
        ]);
        for first in [0x46, 0x47, 0x49] {
            for second in [0x6A, 0x6B] {
                let v = pair_pos_apply(&d, first, second)?.ok_or(Error::Truncated)?;
                assert_eq!(v.first.x_advance, -50);
                assert_eq!(v.second, ValueRecord::default());
            }
            // Covered, so the subtable applies, with class 0's zero record.
            let v = pair_pos_apply(&d, first, 0x20)?.ok_or(Error::Truncated)?;
            assert_eq!(v.first.x_advance, 0);
        }
        assert_eq!(pair_pos_apply(&d, 0x48, 0x6A)?, None);
        Ok(())
    }
}
