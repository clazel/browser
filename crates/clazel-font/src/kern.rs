//! `kern`, kerning (OpenType 1.9, chapter `kern`; Apple's manual, "'kern'
//! table").
//!
//! <https://learn.microsoft.com/en-us/typography/opentype/otspec190/kern>.
//!
//! The OpenType (Windows) table, version 0, with format 0 subtables:
//! "Format 0 is the only subtable format supported by Windows." Apple's
//! version 1.0 table (a `Fixed` 0x00010000 version and 32-bit header) and
//! its state-machine formats are not read.

use crate::read::{add, element, i16_at, lower_bound, u16_at, u32_at};
use crate::{Error, Tag};

/// Subtable header: `version`, `length`, `coverage`.
const SUBTABLE_HEADER: usize = 6;
/// Format 0 header after the subtable header: `nPairs`, `searchRange`,
/// `entrySelector`, `rangeShift`.
const FORMAT0_HEADER: usize = 8;
/// One pair: `left`, `right`, `value`.
const PAIR: usize = 6;

/// `coverage` bits (chapter `kern`, the coverage sub-fields).
pub mod coverage {
    /// `horizontal`, bit 0: "1 if table has horizontal data, 0 if
    /// vertical."
    pub const HORIZONTAL: u16 = 1 << 0;
    /// `minimum`, bit 1: "the table has minimum values".
    pub const MINIMUM: u16 = 1 << 1;
    /// `cross-stream`, bit 2.
    pub const CROSS_STREAM: u16 = 1 << 2;
    /// `override`, bit 3: "the value in this table should replace the value
    /// currently being accumulated."
    pub const OVERRIDE: u16 = 1 << 3;
}

/// One subtable's header.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Subtable {
    /// Where the subtable starts in `kern`.
    pub offset: usize,
    /// `length`: "Length of the subtable, in bytes (including this
    /// header)."
    pub length: u16,
    /// `coverage`.
    pub coverage: u16,
}

impl Subtable {
    /// `format`, bits 8 to 15 of `coverage`.
    pub fn format(&self) -> u8 {
        let [format, _] = self.coverage.to_be_bytes();
        format
    }
}

/// The `kern` table, version 0.
#[derive(Debug, Clone, Copy)]
pub struct Kern<'a> {
    data: &'a [u8],
    n_tables: u16,
}

impl<'a> Kern<'a> {
    /// The header: `version` "Table version number (0)" and `nTables`. A
    /// `uint32` version 0x00010000 is Apple's table and is
    /// [`Error::UnsupportedVersion`].
    pub fn parse(data: &'a [u8]) -> Result<Self, Error> {
        if u16_at(data, 0)? != 0 {
            return Err(Error::UnsupportedVersion(Tag::KERN));
        }
        Ok(Self {
            data,
            n_tables: u16_at(data, 2)?,
        })
    }

    /// Call `f` on each subtable header in order. Each subtable starts
    /// `length` bytes after the previous one; a `length` shorter than the
    /// header would not advance and is refused.
    pub fn subtables(
        &self,
        mut f: impl FnMut(&Subtable) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let mut at = 4usize;
        for _ in 0..self.n_tables {
            let length = u16_at(self.data, add(at, 2)?)?;
            let coverage = u16_at(self.data, add(at, 4)?)?;
            if usize::from(length) < SUBTABLE_HEADER {
                return Err(Error::InvalidValue(Tag::KERN));
            }
            f(&Subtable {
                offset: at,
                length,
                coverage,
            })?;
            at = add(at, usize::from(length))?;
        }
        Ok(())
    }

    /// Format 0's `nPairs` and where its pairs start, checked to fit in the
    /// table (not in `length`, which a large subtable overflows).
    fn format0(&self, s: &Subtable) -> Result<(usize, usize), Error> {
        let header = add(s.offset, SUBTABLE_HEADER)?;
        let n_pairs = usize::from(u16_at(self.data, header)?);
        let pairs = add(header, FORMAT0_HEADER)?;
        if element(pairs, n_pairs, PAIR)? > self.data.len() {
            return Err(Error::Truncated);
        }
        Ok((n_pairs, pairs))
    }

    /// The value for (`left`, `right`) in format 0 subtable `s`, if listed:
    /// "The left and right halves of the kerning pair make an unsigned
    /// 32-bit number, which is then used to order the kerning pairs
    /// numerically."
    pub fn format0_value(&self, s: &Subtable, left: u16, right: u16) -> Result<Option<i16>, Error> {
        let (n_pairs, pairs) = self.format0(s)?;
        let ([l0, l1], [r0, r1]) = (left.to_be_bytes(), right.to_be_bytes());
        let key = u32::from_be_bytes([l0, l1, r0, r1]);
        let i = lower_bound(n_pairs, &key, |i| {
            u32_at(self.data, element(pairs, i, PAIR)?)
        })?;
        if i >= n_pairs {
            return Ok(None);
        }
        let at = element(pairs, i, PAIR)?;
        if u32_at(self.data, at)? != key {
            return Ok(None);
        }
        Ok(Some(i16_at(self.data, add(at, 4)?)?))
    }

    /// Every pair of format 0 subtable `s`, in order.
    pub fn format0_pairs(
        &self,
        s: &Subtable,
        mut f: impl FnMut(u16, u16, i16),
    ) -> Result<(), Error> {
        let (n_pairs, pairs) = self.format0(s)?;
        for i in 0..n_pairs {
            let at = element(pairs, i, PAIR)?;
            f(
                u16_at(self.data, at)?,
                u16_at(self.data, add(at, 2)?)?,
                i16_at(self.data, add(at, 4)?)?,
            );
        }
        Ok(())
    }

    /// The horizontal kerning for (`left`, `right`), in font units: the sum
    /// over the format 0 subtables that are horizontal kerning values (not
    /// minimum values, not cross-stream) of their value for the pair, where
    /// an `override` subtable replaces the sum so far. "Because the
    /// adjustments are additive, the order of the subtables containing
    /// kerning values is not important" (except for `override`).
    pub fn kerning(&self, left: u16, right: u16) -> Result<i32, Error> {
        let mut total = 0i32;
        self.subtables(|s| {
            let usable = s.format() == 0
                && s.coverage & coverage::HORIZONTAL != 0
                && s.coverage & (coverage::MINIMUM | coverage::CROSS_STREAM) == 0;
            if !usable {
                return Ok(());
            }
            if let Some(v) = self.format0_value(s, left, right)? {
                total = if s.coverage & coverage::OVERRIDE != 0 {
                    i32::from(v)
                } else {
                    total.checked_add(i32::from(v)).ok_or(Error::Overflow)?
                };
            }
            Ok(())
        })?;
        Ok(total)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A version 0 table with one format 0 subtable of `pairs`.
    fn table(coverage: u16, pairs: &[(u16, u16, i16)]) -> Vec<u8> {
        let n = u16::try_from(pairs.len()).unwrap_or(0);
        let mut d = vec![0, 0, 0, 1];
        let length = n.saturating_mul(6).saturating_add(14);
        for v in [0, length, coverage, n, 0, 0, 0] {
            d.extend_from_slice(&v.to_be_bytes());
        }
        for (l, r, v) in pairs {
            d.extend_from_slice(&l.to_be_bytes());
            d.extend_from_slice(&r.to_be_bytes());
            d.extend_from_slice(&v.to_be_bytes());
        }
        d
    }

    #[test]
    fn format0_lookup() -> Result<(), Error> {
        let d = table(0x0001, &[(1, 2, -50), (1, 5, 10), (3, 0, -7)]);
        let k = Kern::parse(&d)?;
        assert_eq!(k.kerning(1, 2)?, -50);
        assert_eq!(k.kerning(1, 5)?, 10);
        assert_eq!(k.kerning(3, 0)?, -7);
        assert_eq!(k.kerning(2, 1)?, 0);
        // A minimum-values subtable is not kerning.
        let d = table(0x0003, &[(1, 2, -50)]);
        assert_eq!(Kern::parse(&d)?.kerning(1, 2)?, 0);
        // Apple's version 1.0.
        assert_eq!(
            Kern::parse(&[0, 1, 0, 0, 0, 0, 0, 0]).err(),
            Some(Error::UnsupportedVersion(Tag::KERN))
        );
        Ok(())
    }
}
