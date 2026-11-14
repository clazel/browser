//! "The OpenType Font File" chapter (OpenType 1.9, `otff`): the table
//! directory, its table records, table checksums and the font collection
//! header.
//!
//! <https://learn.microsoft.com/en-us/typography/opentype/otspec190/otff>.
//! Second text: Apple, TrueType Reference Manual, chapter 6, "The Font
//! Directory"
//! (<https://developer.apple.com/fonts/TrueType-Reference-Manual/RM06/Chap6.html>);
//! collections are OpenType's alone here.
//!
//! Nothing here copies font bytes: a [`TableDirectory`] is the whole file
//! plus the offset of one face's directory, and [`TableDirectory::table`]
//! hands out the slice a record gives, after checking the record against the
//! file.

use crate::read::{self, add, element, tag_at, u16_at, u32_at, us};
use crate::{Error, Tag};

/// `sfntVersion` 0x00010000: "OpenType fonts that contain TrueType outlines
/// should use the value of 0x00010000 for the sfntVersion."
pub const SFNT_TRUETYPE: u32 = 0x0001_0000;
/// `sfntVersion` `'OTTO'`: "OpenType fonts containing CFF data (version 1
/// or 2) should use 0x4F54544F ('OTTO', when re-interpreted as a Tag)".
pub const SFNT_OTTO: u32 = u32::from_be_bytes(*b"OTTO");
/// `sfntVersion` `'true'`, which Apple's manual allows for TrueType
/// outlines ("The values 'true' (0x74727565) and 0x00010000 are recognized
/// by OS X and iOS as referring to TrueType fonts"); OpenType's chapter
/// notes Apple's 'true' and 'typ1' and says "These version tags should not
/// be used for OpenType fonts", so we accept `'true'` as TrueType and
/// nothing more.
pub const SFNT_APPLE_TRUE: u32 = u32::from_be_bytes(*b"true");
/// `ttcTag` of the TTC Header, "Font Collection ID string: 'ttcf'".
pub const TTC_TAG: u32 = u32::from_be_bytes(*b"ttcf");

/// Size of the TableDirectory header before its `tableRecords`:
/// `sfntVersion` (4), `numTables`, `searchRange`, `entrySelector`,
/// `rangeShift` (2 each).
const DIRECTORY_HEADER: usize = 12;
/// Size of one TableRecord: `tableTag`, `checksum`, `offset`, `length`.
const TABLE_RECORD: usize = 16;
/// Offset of `tableDirectoryOffsets` in the TTC Header (after `ttcTag`,
/// `majorVersion`, `minorVersion`, `numFonts`).
const TTC_OFFSETS: usize = 12;

/// What kind of outlines a face's `sfntVersion` announces.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SfntVersion {
    /// `0x00010000`, or Apple's `'true'`: TrueType outlines.
    TrueType,
    /// `'OTTO'`: CFF or CFF2 outlines.
    Cff,
}

/// One TableRecord, as stored (otff, "Table Directory", TableRecord).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TableRecord {
    /// `tableTag`: "Table identifier."
    pub tag: Tag,
    /// `checksum`: "Checksum for this table."
    pub checksum: u32,
    /// `offset`: "Offset from beginning of font file."
    pub offset: u32,
    /// `length`: "Length of this table."
    pub length: u32,
}

/// One face's table directory, over the whole font file.
#[derive(Debug, Clone, Copy)]
pub struct TableDirectory<'a> {
    /// The whole file. Table offsets are "from beginning of font file",
    /// in a collection too ("The table offsets in all table directories
    /// within a TTC file are measured from the beginning of the TTC file").
    file: &'a [u8],
    /// Where this directory starts in `file`.
    at: usize,
    /// `sfntVersion`.
    version: SfntVersion,
    /// `numTables`: "Number of tables."
    num_tables: u16,
}

impl<'a> TableDirectory<'a> {
    /// Read the TableDirectory at offset `at` of `file`.
    ///
    /// otff, "Table Directory": `sfntVersion`, then `numTables`, then the
    /// three search fields, which we do not read (the `cmap` chapter says of
    /// the same fields in format 4 that "it is strongly recommended that
    /// parsing implementations not rely on the searchRange, entrySelector
    /// and rangeShift fields in the font"; we apply that here too and search
    /// linearly), then `numTables` TableRecords. All of them must lie in the
    /// file.
    pub fn parse_at(file: &'a [u8], at: usize) -> Result<Self, Error> {
        let version = match u32_at(file, at)? {
            SFNT_TRUETYPE | SFNT_APPLE_TRUE => SfntVersion::TrueType,
            SFNT_OTTO => SfntVersion::Cff,
            _ => return Err(Error::UnknownMagic),
        };
        let num_tables = u16_at(file, add(at, 4)?)?;
        let records = element(
            add(at, DIRECTORY_HEADER)?,
            usize::from(num_tables),
            TABLE_RECORD,
        )?;
        if records > file.len() {
            return Err(Error::Truncated);
        }
        Ok(Self {
            file,
            at,
            version,
            num_tables,
        })
    }

    /// `sfntVersion`.
    pub fn sfnt_version(&self) -> SfntVersion {
        self.version
    }

    /// `numTables`.
    pub fn num_tables(&self) -> u16 {
        self.num_tables
    }

    /// The whole font file this directory is part of.
    pub fn file(&self) -> &'a [u8] {
        self.file
    }

    /// TableRecord `index` (`tableRecords[index]`).
    pub fn record(&self, index: u16) -> Result<TableRecord, Error> {
        let r = element(
            add(self.at, DIRECTORY_HEADER)?,
            usize::from(index),
            TABLE_RECORD,
        )?;
        Ok(TableRecord {
            tag: tag_at(self.file, r)?,
            checksum: u32_at(self.file, add(r, 4)?)?,
            offset: u32_at(self.file, add(r, 8)?)?,
            length: u32_at(self.file, add(r, 12)?)?,
        })
    }

    /// The first record with tag `tag`, if any. The chapter says records
    /// are "sorted in ascending order by tag"; we do not rely on it (a linear
    /// search finds the first match whatever the order).
    pub fn find(&self, tag: Tag) -> Result<Option<TableRecord>, Error> {
        for i in 0..self.num_tables {
            let r = self.record(i)?;
            if r.tag == tag {
                return Ok(Some(r));
            }
        }
        Ok(None)
    }

    /// The bytes record `r` names: `length` bytes at `offset` from the
    /// start of the file, which must lie wholly inside it.
    pub fn record_data(&self, r: &TableRecord) -> Result<&'a [u8], Error> {
        read::slice(self.file, us(r.offset), us(r.length))
    }

    /// The table tagged `tag`: `Ok(None)` if the directory has no such
    /// record, an error if its record points outside the file.
    pub fn table(&self, tag: Tag) -> Result<Option<&'a [u8]>, Error> {
        match self.find(tag)? {
            Some(r) => self.record_data(&r).map(Some),
            None => Ok(None),
        }
    }

    /// Whether record `r`'s `checksum` matches its table's bytes
    /// ("Calculating Checksums"; [`table_checksum`]). A mismatch is
    /// recorded, never fatal: nothing else in the crate looks at it.
    pub fn checksum_matches(&self, r: &TableRecord) -> Result<bool, Error> {
        let data = self.record_data(r)?;
        Ok(table_checksum(data, r.tag == Tag::HEAD) == r.checksum)
    }
}

/// "Calculating Checksums": "the unsigned sum of the uint32 units of a given
/// table", as though zero-padded to a multiple of four ("the above algorithm
/// must be modified to treat the data as though it contains zero padding").
/// For `head`, "calculate the checksum for that table assuming the
/// checksumAdjustment value is zero": `is_head` zeroes bytes 8 to 11.
///
/// The chapter's C sample declares `Endptr` and tests `EndPtr`; we follow
/// the prose (docs/ERRATA.md).
pub fn table_checksum(data: &[u8], is_head: bool) -> u32 {
    let mut sum = 0u32;
    for (i, chunk) in data.chunks(4).enumerate() {
        let mut word = [0u8; 4];
        for (dst, src) in word.iter_mut().zip(chunk) {
            *dst = *src;
        }
        // `checkSumAdjustment` is the third uint32 of `head` (offset 8).
        if is_head && i == 2 {
            word = [0; 4];
        }
        sum = sum.wrapping_add(u32::from_be_bytes(word));
    }
    sum
}

/// The TTC Header (otff, "Font Collections", "TTC Header").
#[derive(Debug, Clone, Copy)]
pub struct Collection<'a> {
    /// The whole file.
    file: &'a [u8],
    /// `majorVersion`: 1 or 2.
    major_version: u16,
    /// `numFonts`: "Number of fonts in TTC".
    num_fonts: u32,
}

impl<'a> Collection<'a> {
    /// Read a TTC Header at the start of `file`: `ttcTag` `'ttcf'`,
    /// `majorVersion` 1 or 2 (the two header versions; a version 2.0
    /// header's DSIG fields come after the offsets and are not read), and
    /// `numFonts` `Offset32`s, all inside the file. `minorVersion` "Minor
    /// version of the TTC Header, = 0" is not checked.
    pub fn parse(file: &'a [u8]) -> Result<Self, Error> {
        if u32_at(file, 0)? != TTC_TAG {
            return Err(Error::UnknownMagic);
        }
        let major_version = u16_at(file, 4)?;
        if major_version != 1 && major_version != 2 {
            return Err(Error::UnsupportedVersion(Tag::TTCF));
        }
        let num_fonts = u32_at(file, 8)?;
        if element(TTC_OFFSETS, us(num_fonts), 4)? > file.len() {
            return Err(Error::Truncated);
        }
        Ok(Self {
            file,
            major_version,
            num_fonts,
        })
    }

    /// `majorVersion`.
    pub fn major_version(&self) -> u16 {
        self.major_version
    }

    /// `numFonts`.
    pub fn num_fonts(&self) -> u32 {
        self.num_fonts
    }

    /// `tableDirectoryOffsets[index]`: "Array of offsets to the
    /// TableDirectory for each font from the beginning of the file".
    pub fn directory_offset(&self, index: u32) -> Result<u32, Error> {
        if index >= self.num_fonts {
            return Err(Error::FaceIndex);
        }
        u32_at(self.file, element(TTC_OFFSETS, us(index), 4)?)
    }

    /// The table directory of face `index`. A directory inside a collection
    /// must itself be a TableDirectory, so a nested `'ttcf'` is
    /// [`Error::UnknownMagic`].
    pub fn directory(&self, index: u32) -> Result<TableDirectory<'a>, Error> {
        TableDirectory::parse_at(self.file, us(self.directory_offset(index)?))
    }
}

/// A font file: one face, or a collection of them.
#[derive(Debug, Clone, Copy)]
pub enum FontFile<'a> {
    /// A single TableDirectory at offset 0 ("If the font file contains only
    /// one font, the table directory will begin at byte 0 of the file").
    Single(TableDirectory<'a>),
    /// A TTC Header at offset 0.
    Collection(Collection<'a>),
}

impl<'a> FontFile<'a> {
    /// Read the file's first four bytes and parse what they announce.
    pub fn parse(file: &'a [u8]) -> Result<Self, Error> {
        if u32_at(file, 0)? == TTC_TAG {
            Collection::parse(file).map(Self::Collection)
        } else {
            TableDirectory::parse_at(file, 0).map(Self::Single)
        }
    }

    /// How many faces the file holds.
    pub fn num_faces(&self) -> u32 {
        match self {
            Self::Single(_) => 1,
            Self::Collection(c) => c.num_fonts(),
        }
    }

    /// Face `index`'s directory.
    pub fn directory(&self, index: u32) -> Result<TableDirectory<'a>, Error> {
        match self {
            Self::Single(d) if index == 0 => Ok(*d),
            Self::Single(_) => Err(Error::FaceIndex),
            Self::Collection(c) => c.directory(index),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A directory with `records` (tag, offset, length) and checksum 0.
    fn directory(version: &[u8; 4], records: &[(&[u8; 4], u32, u32)]) -> Vec<u8> {
        let mut d = version.to_vec();
        d.extend_from_slice(&u16::try_from(records.len()).unwrap_or(0).to_be_bytes());
        d.extend_from_slice(&[0; 6]);
        for (tag, off, len) in records {
            d.extend_from_slice(*tag);
            d.extend_from_slice(&0u32.to_be_bytes());
            d.extend_from_slice(&off.to_be_bytes());
            d.extend_from_slice(&len.to_be_bytes());
        }
        d
    }

    #[test]
    fn directory_and_tables() -> Result<(), Error> {
        let mut f = directory(&[0, 1, 0, 0], &[(b"abcd", 44, 4), (b"efgh", 46, 4)]);
        f.extend_from_slice(&[1, 2, 3, 4, 5, 6]);
        let d = TableDirectory::parse_at(&f, 0)?;
        assert_eq!(d.sfnt_version(), SfntVersion::TrueType);
        assert_eq!(d.table(Tag(*b"abcd"))?, Some(&[1, 2, 3, 4][..]));
        assert_eq!(d.table(Tag(*b"efgh"))?, Some(&[3, 4, 5, 6][..]));
        assert_eq!(d.table(Tag(*b"none"))?, None);
        // A record one byte past the end is refused, not truncated.
        let mut g = directory(b"OTTO", &[(b"abcd", 44, 5)]);
        g.extend_from_slice(&[0; 4]);
        let d = TableDirectory::parse_at(&g, 0)?;
        assert_eq!(d.sfnt_version(), SfntVersion::Cff);
        assert_eq!(d.table(Tag(*b"abcd")), Err(Error::Truncated));
        Ok(())
    }

    #[test]
    fn directory_must_fit() {
        let mut f = directory(&[0, 1, 0, 0], &[(b"abcd", 0, 0)]);
        f.pop();
        assert_eq!(
            TableDirectory::parse_at(&f, 0).err(),
            Some(Error::Truncated)
        );
        assert_eq!(
            TableDirectory::parse_at(b"typ1\0\0\0\0\0\0\0\0", 0).err(),
            Some(Error::UnknownMagic)
        );
    }

    #[test]
    fn checksum_pads_and_skips_adjustment() {
        // "treat the data as though it contains zero padding".
        assert_eq!(table_checksum(&[0, 0, 0, 1, 0x80], false), 0x8000_0001);
        // Wrapping sum.
        assert_eq!(table_checksum(&[0xFF; 8], false), 0xFFFF_FFFE);
        // `head`: the third uint32 counts as zero.
        let head = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 1];
        assert_eq!(table_checksum(&head, true), 1);
        assert_eq!(table_checksum(&head, false), 8);
    }

    #[test]
    fn collection_header() -> Result<(), Error> {
        let face = directory(&[0, 1, 0, 0], &[]);
        let mut f = b"ttcf".to_vec();
        f.extend_from_slice(&[0, 1, 0, 0, 0, 0, 0, 2]);
        f.extend_from_slice(&20u32.to_be_bytes());
        f.extend_from_slice(&20u32.to_be_bytes());
        f.extend_from_slice(&face);
        let file = FontFile::parse(&f)?;
        assert_eq!(file.num_faces(), 2);
        assert_eq!(file.directory(1)?.num_tables(), 0);
        assert_eq!(file.directory(2).err(), Some(Error::FaceIndex));
        // numFonts larger than the offsets the file holds.
        let mut g = f.clone();
        if let Some(b) = g.get_mut(11) {
            *b = 9;
        }
        assert_eq!(FontFile::parse(&g).err(), Some(Error::Truncated));
        Ok(())
    }
}
