//! Pair kerning over a run of glyphs: `GPOS` LookupType 2 for the `kern`
//! feature, or the `kern` table (OpenType 1.9, chapters `gpos` and `kern`,
//! read by `clazel-font`).
//!
//! `clazel-font` answers for one pair; this module decides which pairs of
//! a run are asked, in which order, and what the answer does to the run.
//! Both passes pair each glyph with the next one that is not a combining
//! mark, and every failure to read a pair is no adjustment.

use clazel_font::kern::Kern;
use clazel_font::layout::{Gpos, PairValue, ValueRecord};

use super::UnitGlyph;

/// Where a face's pair kerning comes from.
#[derive(Debug, Clone)]
pub enum PairSource<'a> {
    /// `GPOS`, with the LookupList indices of the script's `kern` feature
    /// (never empty).
    Gpos(Gpos<'a>, Vec<u16>),
    /// The `kern` table.
    Kern(Kern<'a>),
    /// Neither: no kerning.
    None,
}

/// The index of the first glyph after `i` that is not a mark, if any.
///
/// This is how every pair is formed: as if each `kern` lookup had the
/// `lookupFlag` `IGNORE_MARKS` ("If set, skips over combining marks",
/// chapter2, "Lookup Table"), which is what HarfBuzz uses for the `kern`
/// table. `lookupFlag` itself is not read (`clazel-font` does not expose it).
pub fn next_base(glyphs: &[UnitGlyph], i: usize) -> Option<usize> {
    let start = i.checked_add(1)?;
    let rest = glyphs.get(start..)?;
    let k = rest.iter().position(|g| !g.mark)?;
    start.checked_add(k)
}

/// The first glyph at or after `i` that is not a mark, if any.
pub fn base_at_or_after(glyphs: &[UnitGlyph], i: usize) -> Option<usize> {
    match glyphs.get(i) {
        Some(g) if !g.mark => Some(i),
        Some(_) => next_base(glyphs, i),
        None => None,
    }
}

/// Add a ValueRecord to a glyph: `xAdvance` to its advance, `xPlacement`
/// and `yPlacement` to its offsets (gpos, "Value Record"). `yAdvance` is
/// "only used for vertical layout" and is not applied. Sums saturate.
pub fn add_value(g: &mut UnitGlyph, v: &ValueRecord) {
    g.x_advance = g.x_advance.saturating_add(i32::from(v.x_advance));
    g.x_offset = g.x_offset.saturating_add(i32::from(v.x_placement));
    g.y_offset = g.y_offset.saturating_add(i32::from(v.y_placement));
}

/// One `GPOS` pair lookup applied along the run (gpos, "Lookup Type 2:
/// Pair Adjustment Positioning Subtable"): from the first glyph, each
/// glyph is paired with the next non-mark glyph; where `pair` gives a
/// [`PairValue`], `valueRecord1` goes to the first glyph and
/// `valueRecord2` to the second.
///
/// Where the pass goes next: the chapter does not say. We follow
/// HarfBuzz's reading (listed in [`super`]): after a pair whose second
/// record is non-zero, the second glyph has been positioned and the pass
/// resumes after it; otherwise it resumes at the second glyph, which then
/// starts the next pair.
pub fn pair_pass(glyphs: &mut [UnitGlyph], mut pair: impl FnMut(u16, u16) -> Option<PairValue>) {
    let mut i = base_at_or_after(glyphs, 0);
    while let Some(first) = i {
        let Some(second) = next_base(glyphs, first) else {
            break;
        };
        let (a, b) = match (glyphs.get(first), glyphs.get(second)) {
            (Some(a), Some(b)) => (a.glyph, b.glyph),
            _ => break,
        };
        i = match pair(a, b) {
            Some(v) => {
                if let Some(g) = glyphs.get_mut(first) {
                    add_value(g, &v.first);
                }
                if let Some(g) = glyphs.get_mut(second) {
                    add_value(g, &v.second);
                }
                if v.second == ValueRecord::default() {
                    Some(second)
                } else {
                    second
                        .checked_add(1)
                        .and_then(|n| base_at_or_after(glyphs, n))
                }
            }
            None => Some(second),
        };
    }
}

/// The `kern` table along the run: each glyph and the next non-mark glyph
/// get the table's value for the pair ([`Kern::kerning`], in font units)
/// added to the first glyph's advance: "If this value is greater than zero,
/// the characters will be moved apart" (chapter `kern`, "Format 0").
pub fn kern_pass(glyphs: &mut [UnitGlyph], mut value: impl FnMut(u16, u16) -> i32) {
    let mut i = base_at_or_after(glyphs, 0);
    while let Some(first) = i {
        let Some(second) = next_base(glyphs, first) else {
            break;
        };
        let right = match glyphs.get(second) {
            Some(b) => b.glyph,
            None => break,
        };
        if let Some(a) = glyphs.get_mut(first) {
            a.x_advance = a.x_advance.saturating_add(value(a.glyph, right));
        }
        i = Some(second);
    }
}

/// Kern the run from `source`: each `GPOS` lookup in LookupList order
/// ("the client arranges the indices numerically into their LookupList
/// order", chapter2, "Feature List Table"), each a pass of its own, or the
/// `kern` table once.
pub fn apply(glyphs: &mut [UnitGlyph], source: &PairSource<'_>) {
    match source {
        PairSource::Gpos(gpos, lookups) => {
            for &l in lookups {
                pair_pass(glyphs, |a, b| gpos.pair_adjustment(l, a, b).ok().flatten());
            }
        }
        PairSource::Kern(kern) => kern_pass(glyphs, |a, b| kern.kerning(a, b).unwrap_or(0)),
        PairSource::None => {}
    }
}
