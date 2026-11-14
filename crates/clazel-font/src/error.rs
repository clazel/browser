//! What can go wrong reading a font.
//!
//! Every parser returns one of these instead of panicking. None carries
//! font bytes, so an error is cheap to copy and safe to log.

use crate::Tag;

/// Why a font, a table or a glyph could not be read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// A read went past the end of the slice it was made from: a table
    /// shorter than its fields, or an offset or count pointing outside it.
    Truncated,
    /// Offset arithmetic overflowed `usize`, or a decoded coordinate
    /// overflowed `i32`.
    Overflow,
    /// The first four bytes are neither an `sfntVersion` we read
    /// (`0x00010000`, `OTTO`, `true`) nor `ttcf`.
    UnknownMagic,
    /// A collection's face index is not below its `numFonts`.
    FaceIndex,
    /// A version field this crate does not read (the table is named).
    UnsupportedVersion(Tag),
    /// A field outside the range its chapter allows (the table is named).
    InvalidValue(Tag),
    /// A table the face needs is not in its directory.
    MissingTable(Tag),
    /// The face has CFF or CFF2 outlines and no `glyf`: decision 5.0(c)
    /// (C1) reads TrueType outlines only, so the face is unsupported.
    CffOutlines,
    /// A glyph index not below `maxp.numGlyphs`.
    GlyphIndex,
    /// A composite glyph nests components deeper than
    /// [`crate::glyf::MAX_COMPONENT_DEPTH`] (which a cycle always does).
    ComponentDepth,
    /// A composite glyph refers to more components in all than
    /// [`crate::glyf::MAX_COMPONENTS`].
    ComponentCount,
    /// A flattened outline would have more points than
    /// [`crate::glyf::MAX_POINTS`].
    PointCount,
    /// A composite's point-matching arguments name a point that does not
    /// exist in the parent or the child.
    AnchorPoint,
    /// A glyph was asked for at a negative size ([`crate::outline`]).
    FontSize,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Truncated => f.write_str("font data is truncated"),
            Self::Overflow => f.write_str("arithmetic overflow in font data"),
            Self::UnknownMagic => f.write_str("not a TrueType font or collection"),
            Self::FaceIndex => f.write_str("face index out of range"),
            Self::UnsupportedVersion(t) => write!(f, "unsupported '{t}' version"),
            Self::InvalidValue(t) => write!(f, "invalid value in '{t}'"),
            Self::MissingTable(t) => write!(f, "missing '{t}' table"),
            Self::CffOutlines => f.write_str("CFF outlines are not supported"),
            Self::GlyphIndex => f.write_str("glyph index out of range"),
            Self::ComponentDepth => f.write_str("composite glyph nested too deeply"),
            Self::ComponentCount => f.write_str("composite glyph has too many components"),
            Self::PointCount => f.write_str("glyph has too many points"),
            Self::AnchorPoint => f.write_str("composite anchor point out of range"),
            Self::FontSize => f.write_str("negative font size"),
        }
    }
}

impl std::error::Error for Error {}
