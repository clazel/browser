//! `name`, the naming table (OpenType 1.9, chapter `name`; Apple's
//! manual, "'name' table").
//!
//! <https://learn.microsoft.com/en-us/typography/opentype/otspec190/name>.

use crate::read::{add, element, slice, u16_at};
use crate::{Error, Tag};

/// Name ID 1, "Font Family name".
pub const FAMILY: u16 = 1;
/// Name ID 2, "Font Subfamily name".
pub const SUBFAMILY: u16 = 2;
/// Name ID 16, "Typographic Family name".
pub const TYPOGRAPHIC_FAMILY: u16 = 16;
/// Name ID 17, "Typographic Subfamily name".
pub const TYPOGRAPHIC_SUBFAMILY: u16 = 17;

/// Size of the header before `nameRecord`: `version`, `count`,
/// `storageOffset`.
const HEADER: usize = 6;
/// Size of one NameRecord.
const NAME_RECORD: usize = 12;
/// Windows language ID for English (United States).
const EN_US: u16 = 0x0409;

/// One NameRecord.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NameRecord {
    /// `platformID`.
    pub platform_id: u16,
    /// `encodingID`.
    pub encoding_id: u16,
    /// `languageID`.
    pub language_id: u16,
    /// `nameID`.
    pub name_id: u16,
    /// `length`: "String length (in bytes)."
    pub length: u16,
    /// `stringOffset`: "String offset from start of storage area (in
    /// bytes)."
    pub offset: u16,
}

impl NameRecord {
    /// Whether the string is UTF-16BE: platform 0 (Unicode), and Windows
    /// (3) with encodings 1 and 10 ("All string data for platform 3 must be
    /// encoded in UTF-16BE"; only the Unicode encodings are text we can
    /// name). Platform 3 encoding 0 (Symbol) strings are UTF-16BE too and
    /// are accepted.
    pub fn is_utf16be(&self) -> bool {
        match self.platform_id {
            0 => true,
            3 => matches!(self.encoding_id, 0 | 1 | 10),
            _ => false,
        }
    }
}

/// The `name` table.
#[derive(Debug, Clone, Copy)]
pub struct Name<'a> {
    data: &'a [u8],
    count: u16,
    storage_offset: u16,
}

impl<'a> Name<'a> {
    /// "Naming table version 0" and "version 1": `version` (0 or 1),
    /// `count`, `storageOffset`, then `count` NameRecords. Version 1's
    /// language-tag records, after them, are not read.
    pub fn parse(data: &'a [u8]) -> Result<Self, Error> {
        if u16_at(data, 0)? > 1 {
            return Err(Error::UnsupportedVersion(Tag::NAME));
        }
        let count = u16_at(data, 2)?;
        let storage_offset = u16_at(data, 4)?;
        if element(HEADER, usize::from(count), NAME_RECORD)? > data.len() {
            return Err(Error::Truncated);
        }
        Ok(Self {
            data,
            count,
            storage_offset,
        })
    }

    /// `count`.
    pub fn count(&self) -> u16 {
        self.count
    }

    /// `storageOffset`: "Offset to start of string storage (from start of
    /// table)". Used as given, even if it points into the records.
    pub fn storage_offset(&self) -> u16 {
        self.storage_offset
    }

    /// `nameRecord[index]`.
    pub fn record(&self, index: u16) -> Result<NameRecord, Error> {
        let at = element(HEADER, usize::from(index), NAME_RECORD)?;
        let field = |i: usize| {
            u16_at(
                self.data,
                add(at, i.checked_mul(2).ok_or(Error::Overflow)?)?,
            )
        };
        Ok(NameRecord {
            platform_id: field(0)?,
            encoding_id: field(1)?,
            language_id: field(2)?,
            name_id: field(3)?,
            length: field(4)?,
            offset: field(5)?,
        })
    }

    /// The bytes of `record`'s string, inside the table.
    pub fn string_bytes(&self, record: &NameRecord) -> Result<&'a [u8], Error> {
        let at = add(usize::from(self.storage_offset), usize::from(record.offset))?;
        slice(self.data, at, usize::from(record.length))
    }

    /// The string with ID `name_id`, decoded from UTF-16BE: the first
    /// record for it in Windows English (United States), else the first in
    /// any UTF-16BE encoding. Records whose string is outside the table are
    /// skipped.
    pub fn get(&self, name_id: u16) -> Result<Option<String>, Error> {
        let mut fallback = None;
        for i in 0..self.count {
            let r = self.record(i)?;
            if r.name_id != name_id || !r.is_utf16be() {
                continue;
            }
            let Ok(bytes) = self.string_bytes(&r) else {
                continue;
            };
            if r.platform_id == 3 && r.language_id == EN_US {
                return Ok(Some(decode_utf16be(bytes)));
            }
            if fallback.is_none() {
                fallback = Some(bytes);
            }
        }
        Ok(fallback.map(decode_utf16be))
    }
}

/// UTF-16BE to a `String`: an unpaired surrogate becomes U+FFFD, and an odd
/// final byte is dropped.
pub fn decode_utf16be(bytes: &[u8]) -> String {
    let (pairs, _) = bytes.as_chunks::<2>();
    let units = pairs.iter().map(|p| u16::from_be_bytes(*p));
    char::decode_utf16(units)
        .map(|c| c.unwrap_or(char::REPLACEMENT_CHARACTER))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prefers_windows_english() -> Result<(), Error> {
        // Two records for ID 1: (0,3,0) "Ab" and (3,1,0x409) "Cd".
        let mut d = vec![0, 0, 0, 2, 0, 30];
        for r in [[0u16, 3, 0, 1, 4, 0], [3, 1, 0x409, 1, 4, 4]] {
            r.iter().for_each(|v| d.extend_from_slice(&v.to_be_bytes()));
        }
        d.extend_from_slice(&[0, b'A', 0, b'b', 0, b'C', 0, b'd']);
        let n = Name::parse(&d)?;
        assert_eq!(n.get(FAMILY)?.as_deref(), Some("Cd"));
        assert_eq!(n.get(SUBFAMILY)?, None);
        assert_eq!(
            decode_utf16be(&[0xD8, 0x3D, 0xDE, 0x00, 0xD8, 0x00]),
            "😀\u{FFFD}"
        );
        Ok(())
    }
}
