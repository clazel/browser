//! Shaping (phase-5.md item 5.11): a run of characters in one face to
//! glyphs with advances and offsets, then to 26.6 positions at a size.
//!
//! # Sources
//!
//! - **OpenType specification version 1.9** (Microsoft), as pinned by
//!   `clazel-font`
//!   (<https://learn.microsoft.com/en-us/typography/opentype/otspec190/>):
//!   chapters `cmap` (characters to glyphs), `hmtx` ("advanceWidth"),
//!   `head` (`unitsPerEm`), `gpos` ("Lookup Type 2: Pair Adjustment
//!   Positioning Subtable", "Value Record"), `kern` ("Format 0") and
//!   chapter2, "OpenType Layout Common Table Formats" (script and feature
//!   selection, LookupList order, `lookupFlag`). The tables are parsed by
//!   `clazel-font`; this module cites the chapter and field for what it
//!   does with them. OpenType numbers no steps, so chapter, section and
//!   field name are the citation (CLAUDE.md rule 5).
//! - **Decision 5.0(c)** of `docs/phases/phase-5.md`, H1: Latin, Greek and
//!   Cyrillic with `cmap`, `hmtx` and pair kerning (`GPOS` type 2, `kern`),
//!   no `GSUB`. **Decision 5.0(b)**, A: the CSS subset of the exit page,
//!   which has neither `letter-spacing` nor `word-spacing`.
//!
//! # What a run becomes
//!
//! [`Shaper::shape`] maps each character to one glyph through the face's
//! `cmap` subtable (an unmapped character is glyph 0, `.notdef`, as
//! chapter `cmap` says of "missing glyph"), gives it its `hmtx`
//! `advanceWidth`, a combining mark a zero advance, and then applies pair
//! kerning ([`kerning`]). Results are in font units ([`UnitGlyph`]), which
//! are exact. [`place`] then scales a run to 26.6 at the used size
//! ([`PlacedRun`]).
//!
//! # Modelling choices and deviations
//!
//! - **One glyph per character, no `GSUB`** (H1). CSS Fonts 3's default
//!   `font-variant-ligatures: normal` asks for the `liga` feature
//!   (§6.4); we never form ligatures. A listed deviation.
//! - **Kerning source.** `GPOS` when the face has one whose default
//!   language system of the chosen script table ("Script" below) lists
//!   the `kern` feature with at least one lookup; otherwise the `kern`
//!   table, if it
//!   is the OpenType version 0 table; otherwise none. The plan says "`GPOS`
//!   … when the font has `GPOS` … and `kern` otherwise"; a face whose
//!   `GPOS` has no `kern` lookups (only mark positioning, say) but has a
//!   `kern` table is kerned from `kern`, which is the plan's evident intent
//!   and what HarfBuzz does. A `GPOS` that does not parse counts as absent.
//! - **`GPOS` lookups are applied one after another**, each along the whole
//!   run, in LookupList order (chapter2). Within a lookup, `clazel-font`
//!   applies the first subtable that covers the pair. Lookups of other
//!   types that a font puts under `kern` (single adjustment, say) are not
//!   applied: H1 is pair kerning. Listed.
//! - **Where a pair pass resumes** after a pair: at the second glyph, or
//!   after it when `valueRecord2` is non-zero (the second glyph "has been
//!   positioned"). The `gpos` chapter does not say; HarfBuzz resumes after
//!   the second glyph whenever `valueFormat2` is non-zero, which
//!   `clazel-font` does not expose, so a record with a non-zero format and
//!   all-zero values resumes at the second glyph here (listed; the
//!   differential test would show it).
//! - **Marks are skipped when forming pairs**, as if every `kern` lookup
//!   had `IGNORE_MARKS`; `lookupFlag` is not read (`clazel-font` does not
//!   expose it), and no `GDEF` glyph classes are read: a mark is a
//!   character in the combining-mark blocks of [`script`].
//! - **Combining marks are placed at the base's advance with zero
//!   advance**: no `mark` or `mkmk` feature, so a mark is drawn where its
//!   glyph's own outline puts it relative to the pen after its base
//!   (fonts design spacing marks with negative side bearings for this).
//!   Listed.
//! - **Value records**: `xAdvance` to the advance, `xPlacement` and
//!   `yPlacement` to the offsets; `yAdvance` (vertical layout) and Device
//!   and VariationIndex tables (no hinting, no variations) are not applied.
//! - **The `kern` table's value goes to the first glyph's advance.**
//!   HarfBuzz splits it between the two glyphs (half to the first glyph's
//!   advance, the rest to the second's advance and offset), which places
//!   every glyph at the same position; the differential test compares
//!   positions for those faces.
//! - **Script**: [`Script::of_text`] takes the first character with a
//!   script of H1 (block tables, approximating Unicode's `Scripts.txt`);
//!   the `GPOS` script table is the first one listed of that script's,
//!   `DFLT` ("An application should use a DFLT script table if there is
//!   not a script table associated with the specific script of the text
//!   being formatted", chapter2), and then `dflt` and `latn`, which
//!   HarfBuzz tries for fonts that list neither (a run of punctuation,
//!   script `DFLT`, is then kerned like Latin in a face that lists only
//!   `latn`, as PT Sans does). The chosen table decides even when its
//!   default LangSys has no `kern` feature: the font then asks for no
//!   `GPOS` kerning for that text, and the `kern` table applies, as in
//!   HarfBuzz. Liberation Serif Italic 2.1.5 lists `DFLT` with only `mark`
//!   and `latn` with `kern`, so digits are kerned from its `kern` table.
//! - **Right-to-left runs are shaped in logical order**: there is no
//!   UAX #9 bidirectional reordering (Phase 8). Listed.
//! - **No `letter-spacing` or `word-spacing`**: decision 5.0(b) A's subset
//!   has neither (phase-5.md, "What the exit page needs"), so the plan's
//!   "if 5.0(b) has them" leaves them out.
//! - **No normalization, no default-ignorable handling, no space
//!   fallback**: HarfBuzz composes or decomposes a character when the face
//!   maps only the other form, hides default-ignorable characters (soft
//!   hyphen, joiners) and draws a missing space character with the space
//!   glyph; we map each character as it is.
//! - **26.6 positions round once per position**, half away from zero, with
//!   item 5.10's scaling ([`clazel_font::outline::scale::scale`]): a
//!   glyph's origin is its pen position plus its offset, scaled; its
//!   advance is the difference of the scaled pen positions after and
//!   before it, so the advances of a run sum to its scaled width and
//!   rounding never accumulates. No hinting. A position outside `i32`
//!   (about ±33 million pixels) is clamped, as is a pen beyond `i32` font
//!   units.
//! - **Every failure degrades**: a `cmap` that cannot be read maps to glyph
//!   0, an advance that cannot be read (a glyph id at or past `numGlyphs`)
//!   is 0, and a pair that cannot be read is not adjusted. Nothing panics.

pub mod fixed;
pub mod kerning;
pub mod script;

#[cfg(kani)]
mod proofs;

use clazel_font::{Face, Tag};

pub use fixed::place;
pub use kerning::PairSource;
pub use script::{Script, is_combining_mark};

/// A shaped glyph, in font units.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnitGlyph {
    /// The glyph id.
    pub glyph: u16,
    /// The byte offset in the run's text of the character it draws.
    pub cluster: usize,
    /// Whether that character is a combining mark.
    pub mark: bool,
    /// How far the pen moves after the glyph.
    pub x_advance: i32,
    /// Where the glyph is drawn relative to the pen, horizontally.
    pub x_offset: i32,
    /// And vertically, y up.
    pub y_offset: i32,
}

/// A glyph placed in 26.6 fixed point (1/64 px).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PlacedGlyph {
    /// The glyph id.
    pub glyph: u16,
    /// The byte offset in the run's text of the character it draws.
    pub cluster: usize,
    /// The glyph's origin, from the run's start.
    pub x: i32,
    /// The glyph's origin above the baseline (y up, as the outline of
    /// item 5.10).
    pub y: i32,
    /// How far the next glyph's pen position is from this one's.
    pub advance: i32,
}

/// A run placed in 26.6 fixed point.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct PlacedRun {
    /// The glyphs, in logical order.
    pub glyphs: Vec<PlacedGlyph>,
    /// The run's width: the pen position after its last glyph.
    pub advance: i32,
}

/// Which table a face's pair kerning comes from ([`PairSource`] without
/// the data).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KerningTable {
    /// `GPOS` LookupType 2 for the `kern` feature.
    Gpos,
    /// The `kern` table.
    Kern,
    /// No kerning.
    None,
}

/// A face ready to shape runs of one script.
#[derive(Debug, Clone)]
pub struct Shaper<'a> {
    face: Face<'a>,
    pairs: PairSource<'a>,
}

impl<'a> Shaper<'a> {
    /// A shaper for runs of `script` in `face`, with its kerning source
    /// chosen as [`self`]'s modelling choices say.
    pub fn new(face: Face<'a>, script: Script) -> Self {
        let gpos = face.gpos().ok().flatten().and_then(|g| {
            // The first script table listed of: the run's script, `DFLT`
            // (chapter2), then `dflt` and `latn` (HarfBuzz's fallbacks for
            // a font that lists neither). The chosen table decides, even
            // when its LangSys has no `kern` feature.
            let chosen = [
                script.tag(),
                clazel_font::layout::DFLT,
                Tag(*b"dflt"),
                Script::Latin.tag(),
            ]
            .into_iter()
            .find(|&tag| g.lists_script(tag).unwrap_or(false))?;
            match g.kern_lookups(chosen) {
                Ok(lookups) if !lookups.is_empty() => Some(PairSource::Gpos(g, lookups)),
                _ => None,
            }
        });
        let pairs = gpos.unwrap_or_else(|| match face.kern() {
            Ok(Some(k)) => PairSource::Kern(k),
            _ => PairSource::None,
        });
        Self { face, pairs }
    }

    /// A shaper with a given kerning source (for tests of the passes).
    pub fn with_pairs(face: Face<'a>, pairs: PairSource<'a>) -> Self {
        Self { face, pairs }
    }

    /// The face.
    pub fn face(&self) -> &Face<'a> {
        &self.face
    }

    /// Which table kerns this face.
    pub fn kerning_table(&self) -> KerningTable {
        match self.pairs {
            PairSource::Gpos(..) => KerningTable::Gpos,
            PairSource::Kern(_) => KerningTable::Kern,
            PairSource::None => KerningTable::None,
        }
    }

    /// The glyph of each character of `text`, with its advance, before
    /// kerning.
    pub fn glyphs(&self, text: &str) -> Vec<UnitGlyph> {
        text.char_indices()
            .map(|(cluster, c)| {
                // cmap: "Character codes that do not correspond to any
                // glyph in the font should be mapped to glyph index 0."
                let glyph = self.face.glyph_index(c).ok().flatten().unwrap_or(0);
                let mark = is_combining_mark(c);
                let x_advance = if mark {
                    0
                } else {
                    self.face.advance_width(glyph).map(i32::from).unwrap_or(0)
                };
                UnitGlyph {
                    glyph,
                    cluster,
                    mark,
                    x_advance,
                    x_offset: 0,
                    y_offset: 0,
                }
            })
            .collect()
    }

    /// Shape `text`: its glyphs, kerned, in font units.
    pub fn shape(&self, text: &str) -> Vec<UnitGlyph> {
        let mut glyphs = self.glyphs(text);
        kerning::apply(&mut glyphs, &self.pairs);
        glyphs
    }

    /// Shape `text` and place it at `size` (26.6 pixels per em: 16 px is
    /// 1024).
    pub fn shape_at(&self, text: &str, size: i32) -> PlacedRun {
        place(&self.shape(text), size, self.face.units_per_em())
    }
}

#[cfg(test)]
mod tests;
