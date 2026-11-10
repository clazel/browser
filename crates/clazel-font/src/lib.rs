//! OpenType font files and the TrueType tables a face needs (phase-5.md
//! item 5.9).
//!
//! # Sources
//!
//! - **OpenType specification version 1.9** (Microsoft), the version this
//!   crate is pinned to, read at
//!   <https://learn.microsoft.com/en-us/typography/opentype/otspec190/>.
//!   Each module cites its chapter by the page name under that address
//!   (`otff`, `head`, `hhea`, `maxp`, `hmtx`, `loca`, `glyf`, `cmap`,
//!   `name`, `os2`, `post`, `kern`, `gpos`, and `chapter2`, "OpenType Layout
//!   Common Table Formats") and every field by the name the chapter gives it.
//!   OpenType numbers no steps, so chapter, table and field name are the
//!   citation (CLAUDE.md rule 5).
//! - **Apple, TrueType Reference Manual**, chapter 6, "Font Tables"
//!   (<https://developer.apple.com/fonts/TrueType-Reference-Manual/RM06/Chap6.html>),
//!   the second text, written by another body about the same tables. Where
//!   it says something OpenType does not (the `'true'` `sfntVersion`, the
//!   composite glyph transformation), the module cites it.
//!
//! # Modelling choices
//!
//! Where the code's form differs from the chapters', and why the meaning is
//! unchanged or the difference is deliberate:
//!
//! - **Slices, not copies.** A table is the byte slice its TableRecord gives,
//!   checked against the file when it is fetched; every read inside it is
//!   checked against that slice ([`read`]). A record outside the file is an
//!   error for that table only, not for the directory.
//! - **Search fields are ignored.** `searchRange`, `entrySelector` and
//!   `rangeShift` (table directory, `cmap` format 4, `kern` format 0) are not
//!   read: `cmap` asks parsers to "derive them independently". Directory
//!   lookups are linear and take the first record with the tag; sorted
//!   arrays inside tables are searched by bisection over the count the table
//!   gives ([`read::lower_bound`]), which on unsorted data returns some
//!   element, never one outside the array.
//! - **Checksums are recorded, not enforced.**
//!   [`file::TableDirectory::checksum_matches`] reports a mismatch; no parser
//!   refuses a table for it, as no shipping engine does.
//! - **`'true'` is TrueType.** Apple's manual allows `sfntVersion` `'true'`
//!   for TrueType outlines; we accept it as `0x00010000`. Apple's `'typ1'`
//!   and anything else is not a font this crate reads.
//! - **CFF is out (decision 5.0(c), C1).** A face whose directory has `CFF `
//!   or `CFF2` and no `glyf` is [`Error::CffOutlines`]; those tables are never
//!   parsed. So are `GSUB`, `GDEF`, variations (`fvar`, `gvar`, …; a variable
//!   font is read at its default instance, which is what `glyf` holds),
//!   colour and bitmap tables, and every instruction table (`fpgm`, `prep`,
//!   `cvt `, glyph instructions): **no bytecode ever runs on font bytes**, and
//!   glyph instructions are skipped by their length.
//! - **Glyphs are decoded on demand.** Nothing is expanded when a face is
//!   opened; a glyph is decoded when asked for, and a flattened composite
//!   is bounded by [`glyf::MAX_COMPONENT_DEPTH`], [`glyf::MAX_COMPONENTS`] and
//!   [`glyf::MAX_POINTS`]. Beyond a bound the glyph is an error, which item
//!   5.10 turns into an empty glyph.
//! - **Composite transforms in fixed point.** The chapters give the
//!   transformation in `F2DOT14` and real arithmetic; we compute each term
//!   exactly in `i64` and round the sum to whole font units, half away from
//!   zero, so a composite's points are integers like a simple glyph's.
//!   FreeType also rounds to whole units when it loads unscaled outlines;
//!   `ttf-parser` keeps `f32`, so the differential test compares transformed
//!   points within one unit (listed there).
//! - **`cmap`: one subtable.** The chapter recommends a Unicode subtable and
//!   lists the encodings; we choose one per face, preferring the full
//!   repertoire ((3,10), or platform 0 encodings 4 and 6, in format 12), then
//!   the BMP ((3,1) and platform 0 encodings 0 to 3, in formats 4, 12, 6 or
//!   0), first record first among equals. Macintosh (platform 1) and Windows
//!   Symbol (3,0) subtables are not Unicode and are not used; formats 2, 8,
//!   10, 13 and 14 are not read.
//! - **`cmap` format 4's `length` is not trusted**: its arrays are read up to
//!   the end of the `cmap` table, because a 16-bit `length` cannot describe a
//!   large subtable and fonts with wrong lengths ship.
//! - **`kern`: the OpenType (Windows) version 0 table, format 0 only.**
//!   Apple's version 1 table is [`Error::UnsupportedVersion`]; format 2
//!   subtables and subtables that are not horizontal, are minimum values or
//!   are cross-stream are skipped. A format 0 subtable's pairs are bounded by
//!   the `kern` table's end, not by the subtable's 16-bit `length`, which
//!   overflows for large subtables; `length` only finds the next subtable.
//! - **`GPOS`: pair adjustment for the `kern` feature only.** Lookups of type
//!   2, directly or through type 9 extensions, from the `kern` features of
//!   one script's default language system, in LookupList order. Within a
//!   lookup the first subtable that applies wins. `lookupFlag` (which glyphs
//!   to skip) and Device and VariationIndex tables are not applied; that is
//!   shaping (item 5.11), which sees glyph sequences, not pairs.
//! - **`name`: UTF-16BE records only** (platform 0, and platform 3 encodings 1
//!   and 10), preferring Windows English (United States, 0x0409).
//!   Macintosh-encoded names are not decoded. An unpaired surrogate decodes
//!   to U+FFFD.
//! - **Lengths and counts are checked before loops**, so every loop's bound
//!   comes from a count already checked against the bytes that hold its
//!   elements; that is what makes the Kani harnesses' unwinding bounded by
//!   the input's length.
//!
//! # Modules
//!
//! - [`file`]: the table directory, table records, checksums, collections.
//! - [`head`], [`hhea`], [`maxp`], [`hmtx`], [`loca`], [`glyf`], [`cmap`],
//!   [`name`], [`os2`], [`post`], [`kern`]: one module per table.
//! - [`layout`]: the Common Table Formats and `GPOS` pair adjustment.
//! - [`face`]: a face, tying the tables together.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod cmap;
pub mod face;
pub mod file;
pub mod glyf;
pub mod head;
pub mod hhea;
pub mod hmtx;
pub mod kern;
pub mod layout;
pub mod loca;
pub mod maxp;
pub mod name;
pub mod os2;
pub mod post;

mod error;
mod read;

#[cfg(kani)]
mod proofs;

pub use error::Error;
pub use face::Face;

/// A four-byte table or feature tag (otff, "Data Types": "Tag: Array of
/// four uint8s (length = 32 bits) used to identify a table, design-variation
/// axis, script, language system, feature, or baseline").
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Tag(pub [u8; 4]);

impl Tag {
    /// `head`.
    pub const HEAD: Self = Self(*b"head");
    /// `hhea`.
    pub const HHEA: Self = Self(*b"hhea");
    /// `maxp`.
    pub const MAXP: Self = Self(*b"maxp");
    /// `hmtx`.
    pub const HMTX: Self = Self(*b"hmtx");
    /// `loca`.
    pub const LOCA: Self = Self(*b"loca");
    /// `glyf`.
    pub const GLYF: Self = Self(*b"glyf");
    /// `cmap`.
    pub const CMAP: Self = Self(*b"cmap");
    /// `name`.
    pub const NAME: Self = Self(*b"name");
    /// `OS/2`.
    pub const OS2: Self = Self(*b"OS/2");
    /// `post`.
    pub const POST: Self = Self(*b"post");
    /// `kern`.
    pub const KERN: Self = Self(*b"kern");
    /// `GPOS`.
    pub const GPOS: Self = Self(*b"GPOS");
    /// `CFF `.
    pub const CFF: Self = Self(*b"CFF ");
    /// `CFF2`.
    pub const CFF2: Self = Self(*b"CFF2");
    /// `ttcf`, the collection header's tag (named in errors about it).
    pub const TTCF: Self = Self(*b"ttcf");
}

impl core::fmt::Display for Tag {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        for b in self.0 {
            if b.is_ascii_graphic() || b == b' ' {
                f.write_str(char::from(b).encode_utf8(&mut [0; 4]))?;
            } else {
                write!(f, "\\x{b:02x}")?;
            }
        }
        Ok(())
    }
}

impl core::fmt::Debug for Tag {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Tag('{self}')")
    }
}
