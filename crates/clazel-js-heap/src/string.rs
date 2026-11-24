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
use std::hash::{BuildHasher, RandomState};

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
        if units.iter().all(|&u| u < 256) {
            // Every unit is under 256: its low byte is its value.
            let bytes: Box<[u8]> = units
                .iter()
                .map(|&u| {
                    let [low, _] = u.to_le_bytes();
                    low
                })
                .collect();
            return Ok(Self(Repr::Latin1(bytes)));
        }
        Ok(Self(Repr::Utf16(units.into())))
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
        // ASCII (every name the engine and the bindings intern) is its own
        // Latin-1 encoding, one byte per unit, with no UTF-16 detour.
        if s.is_ascii() {
            return Self::from_latin1(s.as_bytes());
        }
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

/// A table of property-key strings: each distinct live string once.
///
/// A collection may free keys ([`Interner::sweep`]). **A key id is never
/// reused** (GC13): a freed key resolves to nothing from then on, and
/// interning its string again makes a new key, so a stale key is a defined
/// miss, not another property. The table keeps a tombstone per freed key.
///
/// The strings are stored once, by key, with their hashes. The search
/// table is open addressing with linear probing over key ids, at most half
/// full, so a search ends at an empty slot; growing it and a sweep rebuild it
/// from the stored hashes, never hashing a string twice. The hash is std's
/// keyed SipHash (`RandomState`), so a page cannot choose names that collide.
#[derive(Debug, Default)]
pub struct Interner {
    /// Indexed by key: the string and its hash; `None` once freed.
    strings: Vec<Option<(JsString, u64)>>,
    /// The search table: [`EMPTY`] or a live key's id. Its length is zero or
    /// a power of two, and at most half of it is in use.
    table: Vec<u32>,
    hasher: RandomState,
    live: usize,
}

/// An unused slot of the interner's search table (never a key id: ids stop
/// below it).
const EMPTY: u32 = u32::MAX;

/// The search table's length for the first key.
const FIRST_TABLE: usize = 64;

impl Interner {
    /// An empty table.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// The first slot to probe for `hash` in a table of `len` slots (a power
    /// of two), and the mask that wraps a probe.
    fn start(hash: u64, len: usize) -> (usize, usize) {
        let mask = len.saturating_sub(1);
        // Only the low bits are used; the truncation is the point.
        let low = usize::try_from(hash & u64::from(u32::MAX)).unwrap_or(0);
        (low & mask, mask)
    }

    /// The search-table slot holding `s` (hash `hash`), or the empty slot
    /// where it would go. `None` only for an empty table.
    fn probe(&self, s: &JsString, hash: u64) -> Option<(usize, Option<Key>)> {
        let (mut at, mask) = Self::start(hash, self.table.len());
        // The table is at most half full, so an empty slot comes within
        // `len` steps; the bound only makes that visible.
        for _ in 0..self.table.len() {
            let id = *self.table.get(at)?;
            if id == EMPTY {
                return Some((at, None));
            }
            let hit = usize::try_from(id)
                .ok()
                .and_then(|i| self.strings.get(i))
                .and_then(Option::as_ref)
                .is_some_and(|(t, h)| *h == hash && t == s);
            if hit {
                return Some((at, Some(Key(id))));
            }
            at = at.wrapping_add(1) & mask;
        }
        None
    }

    /// Rebuilds the search table at `len` slots (a power of two, more than
    /// twice the live keys) from the stored hashes.
    fn rebuild(&mut self, len: usize) {
        let mut table = vec![EMPTY; len];
        for (id, entry) in self.strings.iter().enumerate() {
            let (Some((_, hash)), Ok(id)) = (entry, u32::try_from(id)) else {
                continue;
            };
            let (mut at, mask) = Self::start(*hash, len);
            while let Some(slot) = table.get_mut(at) {
                if *slot == EMPTY {
                    *slot = id;
                    break;
                }
                at = at.wrapping_add(1) & mask;
            }
        }
        self.table = table;
    }

    /// The key for `s`, adding it if it is new. Equal strings, whatever
    /// their origin, get one key (while it is live).
    ///
    /// # Errors
    /// [`TooLong`] if `u32::MAX` keys have been issued.
    pub fn intern(&mut self, s: &JsString) -> Result<Key, TooLong> {
        let hash = self.hasher.hash_one(s);
        if let Some((_, Some(k))) = self.probe(s, hash) {
            return Ok(k);
        }
        let id = u32::try_from(self.strings.len()).map_err(|_| TooLong)?;
        if id == EMPTY {
            return Err(TooLong);
        }
        // Keep the table at most half full after this key.
        let need = self.live.saturating_add(1).saturating_mul(2);
        if self.table.len() < need {
            let len = need.checked_next_power_of_two().ok_or(TooLong)?;
            self.rebuild(len.max(FIRST_TABLE));
        }
        let Some((at, None)) = self.probe(s, hash) else {
            return Err(TooLong);
        };
        let slot = self.table.get_mut(at).ok_or(TooLong)?;
        *slot = id;
        self.strings.push(Some((s.clone(), hash)));
        self.live = self.live.saturating_add(1);
        Ok(Key(id))
    }

    /// The key for `s` if it was interned and is live, without adding it.
    #[must_use]
    pub fn find(&self, s: &JsString) -> Option<Key> {
        if self.table.is_empty() {
            return None;
        }
        self.probe(s, self.hasher.hash_one(s))?.1
    }

    /// The string a live key stands for.
    #[must_use]
    pub fn resolve(&self, k: Key) -> Option<&JsString> {
        usize::try_from(k.0)
            .ok()
            .and_then(|i| self.strings.get(i))
            .and_then(Option::as_ref)
            .map(|(s, _)| s)
    }

    /// The number of live keys.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.live
    }

    /// Whether no key is live.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.live == 0
    }

    /// The number of keys ever issued, freed ones included: the size of the
    /// table `sweep` and the collector index by key.
    #[must_use]
    pub fn issued(&self) -> usize {
        self.strings.len()
    }

    /// Free every live key whose flag in `keep` is false (a key past the end
    /// of `keep` is freed too); returns how many were freed. Freed keys are
    /// never issued again (GC13).
    pub fn sweep(&mut self, keep: &[bool]) -> usize {
        let mut freed = 0usize;
        for (i, slot) in self.strings.iter_mut().enumerate() {
            if slot.is_some() && !keep.get(i).copied().unwrap_or(false) {
                *slot = None;
                freed = freed.saturating_add(1);
            }
        }
        self.live = self.live.saturating_sub(freed);
        if freed > 0 {
            // Freed ids leave the search table; its length stays.
            self.rebuild(self.table.len());
        }
        freed
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

    #[test]
    fn the_search_table_grows_and_sweeps_keep_every_live_key() -> Result<(), TooLong> {
        let n: u32 = if cfg!(miri) { 150 } else { 3000 };
        let mut t = Interner::new();
        let name = |i: u32| s(&format!("k{i}"));
        for i in 0..n {
            assert_eq!(t.intern(&name(i)?)?, Key(i));
        }
        for i in 0..n {
            assert_eq!(t.find(&name(i)?), Some(Key(i)));
            assert_eq!(t.intern(&name(i)?)?, Key(i));
            assert_eq!(t.resolve(Key(i)), Some(&name(i)?));
        }
        // Free the odd keys: the even ones stay found, the odd ones are
        // gone, and interning an odd one again makes a new key.
        let keep: Vec<bool> = (0..n).map(|i| i % 2 == 0).collect();
        assert_eq!(t.sweep(&keep), usize::try_from(n / 2).unwrap_or(0));
        for i in 0..n {
            let found = t.find(&name(i)?);
            assert_eq!(found, (i % 2 == 0).then_some(Key(i)));
        }
        assert_eq!(t.intern(&name(1)?)?, Key(n));
        assert_eq!(t.find(&name(1)?), Some(Key(n)));
        assert_eq!(t.find(&s("absent")?), None);
        assert_eq!(Interner::new().find(&s("absent")?), None);
        Ok(())
    }

    #[test]
    fn a_swept_key_is_gone_for_good_and_its_id_is_never_reused() -> Result<(), TooLong> {
        let mut t = Interner::new();
        let (a, b, c) = (
            t.intern(&s("a")?)?,
            t.intern(&s("b")?)?,
            t.intern(&s("c")?)?,
        );
        assert_eq!(t.sweep(&[true, false, true]), 1);
        assert_eq!((t.len(), t.issued()), (2, 3));
        assert_eq!(t.resolve(b), None);
        assert_eq!(t.find(&s("b")?), None);
        assert_eq!(t.resolve(a), Some(&s("a")?));
        assert_eq!(t.find(&s("c")?), Some(c));
        // The string again is a new key, not the old one.
        let b2 = t.intern(&s("b")?)?;
        assert_ne!(b2, b);
        assert_eq!(b2, Key(3));
        assert_eq!(t.resolve(b), None);
        assert_eq!((t.len(), t.issued()), (3, 4));
        // A flag list that is short frees what it does not name; a second
        // sweep of the freed key frees nothing.
        assert_eq!(t.sweep(&[true]), 2);
        assert_eq!(t.sweep(&[true]), 0);
        assert_eq!((t.len(), t.issued()), (1, 4));
        assert!(!t.is_empty());
        assert_eq!(t.sweep(&[]), 1);
        assert!(t.is_empty());
        Ok(())
    }
}
