//! Strings and interned property keys (phase-7.md item 7.5).
//!
//! ECMA-262 §6.1.4, The String Type: a String is a finite ordered sequence
//! of 16-bit code units, with no requirement that surrogates pair up. A
//! [`JsString`] stores such a sequence either as Latin-1 bytes, when every
//! unit is under 256, or as UTF-16 units. The representation is
//! **canonical**: `Utf16` is used only when some unit is 256 or more, so two
//! strings are equal exactly when their derived representations are, and the
//! derived `Eq` and `Hash` are the standard's equality of sequences. Every
//! constructor and operation re-narrows its result, so the invariant is not
//! the caller's to keep.
//!
//! Ropes are a later optimization, measured first (7.5).
//!
//! [`Interner`] maps a string to a [`Key`], a `u32`: equal strings get equal
//! keys, so a property lookup compares integers. Index keys (canonical
//! array indices) are a later slice.

use std::cmp::Ordering;
use std::collections::HashMap;

/// The longest string, in code units. The standard allows 2^53 - 1; an
/// engine may refuse longer (and every engine does). 2^30 - 1 units keeps
/// byte sizes in a `u32`-friendly range and a length an int32 value.
pub const MAX_LENGTH: usize = (1 << 30) - 1;

/// A string longer than [`MAX_LENGTH`] was asked for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TooLong;

/// A String value: a sequence of 16-bit code units, canonically stored.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct JsString(Repr);

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Repr {
    /// Every unit is under 256.
    Latin1(Box<[u8]>),
    /// Some unit is 256 or more.
    Utf16(Box<[u16]>),
}

impl JsString {
    /// The empty string.
    #[must_use]
    pub fn empty() -> Self {
        Self(Repr::Latin1(Box::default()))
    }

    /// From code units, in the narrowest representation.
    ///
    /// # Errors
    /// [`TooLong`] past [`MAX_LENGTH`] units.
    pub fn from_units(units: &[u16]) -> Result<Self, TooLong> {
        if units.len() > MAX_LENGTH {
            return Err(TooLong);
        }
        let narrow: Option<Vec<u8>> = units.iter().map(|&u| u8::try_from(u).ok()).collect();
        Ok(Self(match narrow {
            Some(bytes) => Repr::Latin1(bytes.into_boxed_slice()),
            None => Repr::Utf16(units.into()),
        }))
    }

    /// From Latin-1 bytes: each byte is the code unit of that value.
    ///
    /// # Errors
    /// [`TooLong`] past [`MAX_LENGTH`] units.
    pub fn from_latin1(bytes: &[u8]) -> Result<Self, TooLong> {
        if bytes.len() > MAX_LENGTH {
            return Err(TooLong);
        }
        Ok(Self(Repr::Latin1(bytes.into())))
    }

    /// From a Rust string: its UTF-16 encoding.
    ///
    /// # Errors
    /// [`TooLong`] past [`MAX_LENGTH`] units.
    pub fn from_rust_str(s: &str) -> Result<Self, TooLong> {
        let units: Vec<u16> = s.encode_utf16().collect();
        Self::from_units(&units)
    }

    /// The length in code units.
    #[must_use]
    pub fn len(&self) -> usize {
        match &self.0 {
            Repr::Latin1(b) => b.len(),
            Repr::Utf16(u) => u.len(),
        }
    }

    /// Whether the string is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Whether the string is stored as Latin-1.
    #[must_use]
    pub const fn is_latin1(&self) -> bool {
        matches!(self.0, Repr::Latin1(_))
    }

    /// The code unit at `index`, if there is one.
    #[must_use]
    pub fn unit(&self, index: usize) -> Option<u16> {
        match &self.0 {
            Repr::Latin1(b) => b.get(index).map(|&x| u16::from(x)),
            Repr::Utf16(u) => u.get(index).copied(),
        }
    }

    /// The code units, in order.
    pub fn units(&self) -> impl Iterator<Item = u16> + '_ {
        let (a, b) = match &self.0 {
            Repr::Latin1(b) => (Some(b.iter().map(|&x| u16::from(x))), None),
            Repr::Utf16(u) => (None, Some(u.iter().copied())),
        };
        a.into_iter().flatten().chain(b.into_iter().flatten())
    }

    /// The code units from `start` up to `end` (clamped to the length;
    /// empty if `start >= end`), as a new string.
    #[must_use]
    pub fn substring(&self, start: usize, end: usize) -> Self {
        let end = end.min(self.len());
        let units: Vec<u16> = self
            .units()
            .skip(start)
            .take(end.saturating_sub(start))
            .collect();
        // A substring of a valid string is within the length limit.
        Self::from_units(&units).unwrap_or_else(|_| Self::empty())
    }

    /// `self` followed by `other`.
    ///
    /// # Errors
    /// [`TooLong`] if the result would pass [`MAX_LENGTH`] units.
    pub fn concat(&self, other: &Self) -> Result<Self, TooLong> {
        let len = self.len().checked_add(other.len()).ok_or(TooLong)?;
        if len > MAX_LENGTH {
            return Err(TooLong);
        }
        if let (Repr::Latin1(a), Repr::Latin1(b)) = (&self.0, &other.0) {
            let mut v = Vec::with_capacity(len);
            v.extend_from_slice(a);
            v.extend_from_slice(b);
            return Ok(Self(Repr::Latin1(v.into_boxed_slice())));
        }
        let units: Vec<u16> = self.units().chain(other.units()).collect();
        Self::from_units(&units)
    }

    /// The order of two strings by code unit, lexicographically: the
    /// String case of IsLessThan, ECMA-262 §7.2.12 ("the code unit
    /// sequences are compared by code unit values, not by code points").
    #[must_use]
    pub fn compare(&self, other: &Self) -> Ordering {
        self.units().cmp(other.units())
    }

    /// A Rust string, with each lone surrogate replaced by U+FFFD.
    #[must_use]
    pub fn to_string_lossy(&self) -> String {
        char::decode_utf16(self.units())
            .map(|r| r.unwrap_or(char::REPLACEMENT_CHARACTER))
            .collect()
    }
}

/// An interned property key: an index into an [`Interner`].
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct Key(pub u32);

/// A table of property-key strings: each distinct string once.
#[derive(Debug, Default)]
pub struct Interner {
    keys: HashMap<JsString, Key>,
    strings: Vec<JsString>,
}

impl Interner {
    /// An empty table.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// The key for `s`, adding it if it is new. Equal strings, whatever
    /// their origin, get one key.
    ///
    /// # Errors
    /// [`TooLong`] if the table already holds `u32::MAX` strings.
    pub fn intern(&mut self, s: &JsString) -> Result<Key, TooLong> {
        if let Some(&k) = self.keys.get(s) {
            return Ok(k);
        }
        let key = Key(u32::try_from(self.strings.len()).map_err(|_| TooLong)?);
        self.keys.insert(s.clone(), key);
        self.strings.push(s.clone());
        Ok(key)
    }

    /// The key for `s` if it was interned, without adding it.
    #[must_use]
    pub fn find(&self, s: &JsString) -> Option<Key> {
        self.keys.get(s).copied()
    }

    /// The string a key stands for.
    #[must_use]
    pub fn resolve(&self, k: Key) -> Option<&JsString> {
        usize::try_from(k.0).ok().and_then(|i| self.strings.get(i))
    }

    /// The number of distinct keys.
    #[must_use]
    pub fn len(&self) -> usize {
        self.strings.len()
    }

    /// Whether no key has been interned.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(x: &str) -> Result<JsString, TooLong> {
        JsString::from_rust_str(x)
    }

    #[test]
    fn latin1_when_every_unit_is_under_256() -> Result<(), TooLong> {
        assert!(s("")?.is_latin1());
        assert!(s("abc\u{e9}\u{ff}")?.is_latin1());
        assert!(!s("\u{100}")?.is_latin1());
        assert!(!s("a\u{1F600}")?.is_latin1());
        assert!(JsString::from_units(&[0x61, 0xFF])?.is_latin1());
        assert!(!JsString::from_units(&[0x61, 0x100])?.is_latin1());
        Ok(())
    }

    #[test]
    fn the_representation_is_canonical_so_equality_is_by_units() -> Result<(), TooLong> {
        let a = JsString::from_units(&[0x61, 0xE9])?;
        let b = JsString::from_latin1(&[0x61, 0xE9])?;
        let c = s("a\u{e9}")?;
        assert_eq!(a, b);
        assert_eq!(a, c);
        // Operations re-narrow: dropping the wide unit gives Latin-1 again.
        let wide = s("a\u{100}b")?;
        let narrow = wide.substring(2, 3);
        assert!(narrow.is_latin1());
        assert_eq!(narrow, s("b")?);
        assert_eq!(s("x\u{100}")?.substring(0, 1), s("x")?);
        Ok(())
    }

    #[test]
    fn units_length_and_indexing() -> Result<(), TooLong> {
        let x = s("a\u{1F600}")?; // a, then the pair D83D DE00
        assert_eq!(x.len(), 3);
        assert_eq!(x.units().collect::<Vec<_>>(), [0x61, 0xD83D, 0xDE00]);
        assert_eq!(x.unit(1), Some(0xD83D));
        assert_eq!(x.unit(3), None);
        assert_eq!(s("\u{e9}")?.unit(0), Some(0xE9));
        assert!(JsString::empty().is_empty());
        Ok(())
    }

    #[test]
    fn lone_surrogates_are_kept_and_made_lossy_only_on_output() -> Result<(), TooLong> {
        let x = JsString::from_units(&[0x61, 0xD800, 0x62])?;
        assert_eq!(x.len(), 3);
        assert_eq!(x.to_string_lossy(), "a\u{FFFD}b");
        Ok(())
    }

    #[test]
    fn concat_narrows_and_widens() -> Result<(), TooLong> {
        let a = s("ab")?;
        let b = s("\u{e9}")?;
        let ab = a.concat(&b)?;
        assert!(ab.is_latin1());
        assert_eq!(ab, s("ab\u{e9}")?);
        let w = a.concat(&s("\u{4e2d}")?)?;
        assert!(!w.is_latin1());
        assert_eq!(w.len(), 3);
        assert_eq!(
            JsString::empty().concat(&JsString::empty())?,
            JsString::empty()
        );
        // Two halves of a surrogate pair join into the pair.
        let hi = JsString::from_units(&[0xD83D])?;
        let lo = JsString::from_units(&[0xDE00])?;
        assert_eq!(hi.concat(&lo)?, s("\u{1F600}")?);
        Ok(())
    }

    #[test]
    fn comparison_is_by_code_unit_not_code_point() -> Result<(), TooLong> {
        // U+FF5E (one unit, FF5E) is above U+1F600's lead surrogate D83D by
        // code unit, but below it by code point.
        let bmp = s("\u{FF5E}")?;
        let astral = s("\u{1F600}")?;
        assert_eq!(bmp.compare(&astral), Ordering::Greater);
        assert_eq!(s("a")?.compare(&s("ab")?), Ordering::Less);
        assert_eq!(s("b")?.compare(&s("ab")?), Ordering::Greater);
        assert_eq!(s("ab")?.compare(&s("ab")?), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn the_length_limit_is_refused() {
        let big = vec![0u8; MAX_LENGTH];
        let Ok(x) = JsString::from_latin1(&big) else {
            return;
        };
        assert_eq!(
            x.concat(&JsString::from_latin1(b"a").unwrap_or_else(|_| JsString::empty())),
            Err(TooLong)
        );
        assert_eq!(x.len(), MAX_LENGTH);
    }

    #[test]
    fn interning_gives_one_key_per_distinct_string() -> Result<(), TooLong> {
        let mut t = Interner::new();
        let a = t.intern(&s("foo")?)?;
        let b = t.intern(&s("bar")?)?;
        // The same string from a different constructor and representation.
        let a2 = t.intern(&JsString::from_units(&[0x66, 0x6F, 0x6F])?)?;
        let a3 = t.intern(&JsString::from_latin1(b"foo")?)?;
        assert_eq!((a, a2, a3), (a, a, a));
        assert_ne!(a, b);
        assert_eq!(t.len(), 2);
        assert_eq!(t.resolve(b), Some(&s("bar")?));
        assert_eq!(t.resolve(Key(9)), None);
        assert_eq!(t.find(&s("baz")?), None);
        assert_eq!(t.find(&s("foo")?), Some(a));
        // A wide key and a Latin-1 key with the same low bytes differ.
        let w = t.intern(&s("\u{166}oo")?)?;
        assert_ne!(w, a);
        Ok(())
    }
}
