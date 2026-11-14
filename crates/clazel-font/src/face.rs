//! A face: one font of a file, with the tables a browser reads from it.
//!
//! Opening a face parses the directory and the seven tables every TrueType
//! face needs (`head`, `hhea`, `maxp`, `hmtx`, `loca`, `glyf`, `cmap`,
//! as listed by otff, "Tables Related to TrueType Outlines" and "Required
//! Tables", less `name`, `OS/2` and `post`, which a face can do without);
//! the optional tables are parsed when asked for, and glyphs when drawn.

use crate::cmap::{Cmap, Subtable};
use crate::file::{FontFile, SfntVersion, TableDirectory};
use crate::glyf::{Glyf, Glyph, Outline};
use crate::head::Head;
use crate::hhea::Hhea;
use crate::hmtx::Hmtx;
use crate::kern::Kern;
use crate::layout::Gpos;
use crate::loca::Loca;
use crate::maxp::Maxp;
use crate::name::Name;
use crate::os2::Os2;
use crate::post::Post;
use crate::{Error, Tag};

/// One face of a font file.
#[derive(Debug, Clone, Copy)]
pub struct Face<'a> {
    directory: TableDirectory<'a>,
    /// `head`.
    pub head: Head,
    /// `hhea`.
    pub hhea: Hhea,
    /// `maxp`.
    pub maxp: Maxp,
    hmtx: Hmtx<'a>,
    loca: Loca<'a>,
    glyf: Glyf<'a>,
    /// The chosen `cmap` subtable and its EncodingRecord's index.
    cmap: Option<(u16, Subtable<'a>)>,
}

impl<'a> Face<'a> {
    /// Open face `index` of `file` (0 for a file that is not a collection).
    ///
    /// A face whose `sfntVersion` is `OTTO`, or which has `CFF ` or `CFF2`
    /// and no `glyf`, is [`Error::CffOutlines`] (decision 5.0(c)).
    pub fn parse(file: &'a [u8], index: u32) -> Result<Self, Error> {
        let directory = FontFile::parse(file)?.directory(index)?;
        let has = |tag| directory.find(tag).map(|r| r.is_some());
        if !has(Tag::GLYF)?
            && (directory.sfnt_version() == SfntVersion::Cff || has(Tag::CFF)? || has(Tag::CFF2)?)
        {
            return Err(Error::CffOutlines);
        }
        let required = |tag| directory.table(tag)?.ok_or(Error::MissingTable(tag));
        let head = Head::parse(required(Tag::HEAD)?)?;
        let hhea = Hhea::parse(required(Tag::HHEA)?)?;
        let maxp = Maxp::parse(required(Tag::MAXP)?)?;
        let hmtx = Hmtx::parse(
            required(Tag::HMTX)?,
            hhea.number_of_h_metrics,
            maxp.num_glyphs,
        )?;
        let loca = Loca::parse(
            required(Tag::LOCA)?,
            head.index_to_loc_format,
            maxp.num_glyphs,
        )?;
        let glyf = Glyf::new(required(Tag::GLYF)?);
        let cmap = Cmap::parse(required(Tag::CMAP)?)?.best_subtable()?;
        Ok(Self {
            directory,
            head,
            hhea,
            maxp,
            hmtx,
            loca,
            glyf,
            cmap,
        })
    }

    /// The face's table directory.
    pub fn directory(&self) -> &TableDirectory<'a> {
        &self.directory
    }

    /// `maxp.numGlyphs`.
    pub fn num_glyphs(&self) -> u16 {
        self.maxp.num_glyphs
    }

    /// `head.unitsPerEm`.
    pub fn units_per_em(&self) -> u16 {
        self.head.units_per_em
    }

    /// The `cmap` subtable the face maps with, if it has a Unicode one,
    /// with the index of its EncodingRecord.
    pub fn cmap(&self) -> Option<(u16, &Subtable<'a>)> {
        self.cmap.as_ref().map(|(i, s)| (*i, s))
    }

    /// The glyph for character `c`, or `None` if the face does not map it
    /// (glyph 0, "missingGlyph", included).
    pub fn glyph_index(&self, c: char) -> Result<Option<u16>, Error> {
        match &self.cmap {
            Some((_, s)) => s.map(u32::from(c)),
            None => Ok(None),
        }
    }

    /// `hmtx` advance width of `glyph`, in font units.
    pub fn advance_width(&self, glyph: u16) -> Result<u16, Error> {
        self.hmtx.advance(glyph)
    }

    /// `hmtx` left side bearing of `glyph`, in font units.
    pub fn left_side_bearing(&self, glyph: u16) -> Result<i16, Error> {
        self.hmtx.left_side_bearing(glyph)
    }

    /// The `loca` table.
    pub fn loca(&self) -> &Loca<'a> {
        &self.loca
    }

    /// The `glyf` table.
    pub fn glyf(&self) -> &Glyf<'a> {
        &self.glyf
    }

    /// Glyph `glyph`'s description, undecoded.
    pub fn glyph(&self, glyph: u16) -> Result<Glyph<'a>, Error> {
        self.glyf.glyph(&self.loca, glyph)
    }

    /// Glyph `glyph` flattened to quadratic contours, in font units.
    pub fn outline(&self, glyph: u16) -> Result<Outline, Error> {
        crate::glyf::outline(&self.glyf, &self.loca, glyph)
    }

    /// Glyph `glyph` as a path at `size` (26.6 pixels per em), or an empty
    /// path if it cannot be drawn ([`crate::outline::glyph_path`]).
    pub fn path(&self, glyph: u16, size: i32) -> crate::outline::Path {
        crate::outline::glyph_path(self, glyph, size)
    }

    /// An optional table's bytes.
    fn optional(&self, tag: Tag) -> Result<Option<&'a [u8]>, Error> {
        self.directory.table(tag)
    }

    /// `name`, if present.
    pub fn name(&self) -> Result<Option<Name<'a>>, Error> {
        self.optional(Tag::NAME)?.map(Name::parse).transpose()
    }

    /// `OS/2`, if present.
    pub fn os2(&self) -> Result<Option<Os2>, Error> {
        self.optional(Tag::OS2)?.map(Os2::parse).transpose()
    }

    /// `post`, if present.
    pub fn post(&self) -> Result<Option<Post>, Error> {
        self.optional(Tag::POST)?.map(Post::parse).transpose()
    }

    /// `kern`, if present.
    pub fn kern(&self) -> Result<Option<Kern<'a>>, Error> {
        self.optional(Tag::KERN)?.map(Kern::parse).transpose()
    }

    /// `GPOS`, if present.
    pub fn gpos(&self) -> Result<Option<Gpos<'a>>, Error> {
        self.optional(Tag::GPOS)?.map(Gpos::parse).transpose()
    }
}
