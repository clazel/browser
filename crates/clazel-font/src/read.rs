//! Big-endian reads from a byte slice, every one bounds-checked.
//!
//! OpenType "Data types" (otff chapter): every multi-byte value is
//! big-endian ("Motorola-style byte ordering"). These are the only functions
//! in the crate that touch bytes; every table parser goes through them, so
//! a read outside a slice is an [`Error::Truncated`], never a panic.

use crate::Error;

/// `start + len`, or [`Error::Overflow`].
pub(crate) fn add(start: usize, len: usize) -> Result<usize, Error> {
    start.checked_add(len).ok_or(Error::Overflow)
}

/// `a * b`, or [`Error::Overflow`].
pub(crate) fn mul(a: usize, b: usize) -> Result<usize, Error> {
    a.checked_mul(b).ok_or(Error::Overflow)
}

/// `data[start..start + len]`.
pub(crate) fn slice(data: &[u8], start: usize, len: usize) -> Result<&[u8], Error> {
    data.get(start..add(start, len)?).ok_or(Error::Truncated)
}

/// `data[start..]`.
pub(crate) fn tail(data: &[u8], start: usize) -> Result<&[u8], Error> {
    data.get(start..).ok_or(Error::Truncated)
}

/// The `N` bytes at `offset`.
fn bytes<const N: usize>(data: &[u8], offset: usize) -> Result<[u8; N], Error> {
    slice(data, offset, N)?
        .try_into()
        .map_err(|_| Error::Truncated)
}

/// `uint8` at `offset`.
pub(crate) fn u8_at(data: &[u8], offset: usize) -> Result<u8, Error> {
    data.get(offset).copied().ok_or(Error::Truncated)
}

/// `int8` at `offset`.
pub(crate) fn i8_at(data: &[u8], offset: usize) -> Result<i8, Error> {
    Ok(i8::from_be_bytes(bytes(data, offset)?))
}

/// `uint16` (also `Offset16`, `UFWORD`) at `offset`.
pub(crate) fn u16_at(data: &[u8], offset: usize) -> Result<u16, Error> {
    Ok(u16::from_be_bytes(bytes(data, offset)?))
}

/// `int16` (also `FWORD`, `F2DOT14`) at `offset`.
pub(crate) fn i16_at(data: &[u8], offset: usize) -> Result<i16, Error> {
    Ok(i16::from_be_bytes(bytes(data, offset)?))
}

/// `uint32` (also `Offset32`, `Version16Dot16`) at `offset`.
pub(crate) fn u32_at(data: &[u8], offset: usize) -> Result<u32, Error> {
    Ok(u32::from_be_bytes(bytes(data, offset)?))
}

/// `Fixed` (32-bit signed 16.16) at `offset`, as its raw `i32`.
pub(crate) fn fixed_at(data: &[u8], offset: usize) -> Result<i32, Error> {
    Ok(i32::from_be_bytes(bytes(data, offset)?))
}

/// `Tag` at `offset`.
pub(crate) fn tag_at(data: &[u8], offset: usize) -> Result<crate::Tag, Error> {
    Ok(crate::Tag(bytes(data, offset)?))
}

/// A `u16` or `u32` as `usize`. Both fit on every target this crate builds
/// for (it needs at least 32-bit pointers).
pub(crate) fn us(v: u32) -> usize {
    // `usize` is at least 32 bits on every supported target; on a 16-bit
    // one the conversion fails and the value saturates, which only makes
    // a later bounds check fail.
    usize::try_from(v).unwrap_or(usize::MAX)
}

/// Element `index` of an array of `size`-byte records starting at `start`.
pub(crate) fn element(start: usize, index: usize, size: usize) -> Result<usize, Error> {
    add(start, mul(index, size)?)
}

/// Binary search over `count` records for the first one whose key is not
/// below `target`: returns its index (or `count` if every key is below).
/// `key(i)` reads record `i`. Used for the chapters' sorted arrays; on an
/// unsorted array it still terminates and returns some index in range,
/// never reading outside `0..count`.
pub(crate) fn lower_bound<K: Ord>(
    count: usize,
    target: &K,
    mut key: impl FnMut(usize) -> Result<K, Error>,
) -> Result<usize, Error> {
    let mut lo = 0usize;
    let mut hi = count;
    while lo < hi {
        // lo < hi, so hi - lo > 0 and mid < hi; no overflow.
        let mid = lo.saturating_add(hi.saturating_sub(lo) / 2);
        if key(mid)? < *target {
            lo = mid.saturating_add(1);
        } else {
            hi = mid;
        }
    }
    Ok(lo)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_are_big_endian_and_checked() {
        let d = [0x12, 0x34, 0x56, 0x78, 0xFF];
        assert_eq!(u16_at(&d, 0), Ok(0x1234));
        assert_eq!(u32_at(&d, 0), Ok(0x1234_5678));
        assert_eq!(i16_at(&d, 3), Ok(0x78FF));
        assert_eq!(i8_at(&d, 4), Ok(-1));
        assert_eq!(u16_at(&d, 4), Err(Error::Truncated));
        assert_eq!(u32_at(&d, usize::MAX), Err(Error::Overflow));
        assert_eq!(slice(&d, 5, 0), Ok(&[][..]));
        assert_eq!(slice(&d, 6, 0), Err(Error::Truncated));
    }

    #[test]
    fn lower_bound_finds_first_not_below() {
        let keys = [1u16, 3, 3, 7];
        let find = |t: u16| {
            lower_bound(keys.len(), &t, |i| {
                keys.get(i).copied().ok_or(Error::Truncated)
            })
        };
        assert_eq!(find(0), Ok(0));
        assert_eq!(find(3), Ok(1));
        assert_eq!(find(4), Ok(3));
        assert_eq!(find(8), Ok(4));
    }
}
