//! The contract of element storage (phase-7.md item 7.5, "Elements"), stated
//! before the implementation (CLAUDE.md rule 3).
//!
//! # What is modelled
//!
//! The indexed properties of an Array exotic object, ECMA-262 §10.4.2: a
//! `length` (a `u32`, §10.4.2.1) and, for some array indices below it, a
//! value. This is [`Spec`]. The implementation ([`super::Elements`]) must
//! behave exactly as `Spec` does, whichever representation it holds.
//!
//! Modelling choices (SPEC-STYLE.md):
//!
//! - **Values are `u64` bit patterns.** A value is a NaN-boxed
//!   [`crate::value::Value`]; this module does not look inside, except that
//!   [`HOLE_BITS`] means "no element here".
//! - **Every element is a plain data property** with all three attributes
//!   true. Elements with other attributes, accessors, and a non-writable
//!   `length` are a later slice (they need a place for the attributes); an
//!   array that needs one will leave this storage.
//! - **A hole is the absence of an element.** [`Spec`] stores no hole;
//!   a [`Spec::set`] of the hole value is refused rather than treated as a
//!   delete, so a caller cannot make an element that reads as absent while
//!   being present.
//! - **Prototype lookups are not here.** `get` of a hole is `None`; reading
//!   up the prototype chain is the caller's job (§10.1.8.1 OrdinaryGet).
//! - **Failure is a result, not a throw.** A `RangeError` for an invalid
//!   length (§10.4.2.4 ArraySetLength) is the caller's job; here every
//!   `u32` is a valid length.
//! - **Step numbers** below are those of ECMA-262 as the author remembers
//!   them; no copy of the standard is vendored, so they have not been
//!   checked against the text in this session.
//!
//! # The spec
//!
//! [`Spec`] is a length and a map from array index to value.
//!
//! - **S1.** Every key is below the length.
//! - **S2.** No stored value is [`HOLE_BITS`].
//! - **[`Spec::set`]**, §10.4.2.1 \[\[DefineOwnProperty\]\] step 3 (P is an
//!   array index), sub-step g: the element is stored, and if
//!   `index >= length` the length becomes `index + 1`.
//!   `u32::MAX` is not an array index (§6.1.7 "array index": an integer
//!   index whose numeric value is below 2^32 - 1), so it is refused.
//! - **[`Spec::delete`]**, §10.1.10.1 OrdinaryDelete as reached from
//!   §10.4.2: the element is removed; the length does not change.
//! - **[`Spec::set_length`]**, §10.4.2.4 ArraySetLength, the loop that
//!   deletes elements from the end (step 17): every element at or above the
//!   new length is gone, and the length is the new one. Growing the length
//!   adds holes only.
//! - **[`Spec::get`]**: the element, or `None` for a hole or an index at or
//!   above the length.
//!
//! # What the implementation must meet
//!
//! - **E1. Refinement.** After every operation, [`Repr::to_spec`] of the
//!   storage equals the `Spec` that the same operations produce from
//!   [`Spec::new`], and every operation returns what the `Spec`'s does.
//! - **E2. Well-formed representation** ([`repr_well_formed`]). Dense: the
//!   vector is no longer than the length and no longer than [`MAX_DENSE`].
//!   Sparse: every key is below the length and no stored value is a hole.
//! - **E3. The fallback rule** ([`choose`]). A `set` at `index` on dense
//!   storage of `n` slots stays dense unless `index >= n` and either
//!   `index >= MAX_DENSE` or `index - n > MAX_GAP`, in which case the
//!   storage becomes sparse. Nothing else changes the representation:
//!   in particular sparse storage never becomes dense again (so an array
//!   that went sparse once stays sparse, a stated and measurable cost), and
//!   `set_length` and `delete` never switch it.
//! - **E4. Bounded dense memory.** Dense storage never holds more than
//!   [`MAX_DENSE`] slots, and `set_length` never allocates: growing a
//!   length costs nothing, so `new Array(4294967295)` is one `u32`.

use std::collections::BTreeMap;

/// The bit pattern of [`crate::value::Value::HOLE`]: no element.
pub const HOLE_BITS: u64 = 0xFFFA_0000_0000_0004;

/// The most slots dense storage may hold: 2^24, which is 128 MiB of `u64`.
pub const MAX_DENSE: u32 = 1 << 24;

/// The most holes a single `set` may add to dense storage by writing past
/// its end. A write further out makes the storage sparse.
pub const MAX_GAP: u32 = 1024;

/// An array index is below this (§6.1.7).
pub const INDEX_LIMIT: u32 = u32::MAX;

/// Why an element operation was refused.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Error {
    /// `u32::MAX`, which is not an array index.
    NotAnIndex,
    /// The value is the hole; use `delete`.
    HoleValue,
    /// Memory for the storage could not be reserved.
    OutOfMemory,
}

/// The abstract array (see the module header).
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Spec {
    /// The array's `length`.
    pub length: u32,
    /// The elements that exist.
    pub entries: BTreeMap<u32, u64>,
}

impl Spec {
    /// An empty array with the given length: all holes.
    #[must_use]
    pub fn new(length: u32) -> Self {
        Self {
            length,
            entries: BTreeMap::new(),
        }
    }

    /// S1 and S2.
    #[must_use]
    pub fn well_formed(&self) -> bool {
        self.entries
            .iter()
            .all(|(&k, &v)| k < self.length && v != HOLE_BITS)
    }

    /// The element at `index`, or `None` for a hole.
    #[must_use]
    pub fn get(&self, index: u32) -> Option<u64> {
        self.entries.get(&index).copied()
    }

    /// §10.4.2.1 \[\[DefineOwnProperty\]\], array-index case.
    ///
    /// # Errors
    /// [`Error::NotAnIndex`] for `u32::MAX`; [`Error::HoleValue`] for the
    /// hole. Nothing changes on error.
    pub fn set(&mut self, index: u32, value: u64) -> Result<(), Error> {
        if index == INDEX_LIMIT {
            return Err(Error::NotAnIndex);
        }
        if value == HOLE_BITS {
            return Err(Error::HoleValue);
        }
        self.entries.insert(index, value);
        // 3.g "If index >= length, then ... Set lengthDesc.[[Value]] to
        // index + 1" (no overflow: index < u32::MAX).
        if index >= self.length {
            self.length = index.saturating_add(1);
        }
        Ok(())
    }

    /// Remove the element at `index`; the length stays. Returns whether an
    /// element was there.
    pub fn delete(&mut self, index: u32) -> bool {
        self.entries.remove(&index).is_some()
    }

    /// §10.4.2.4 ArraySetLength, deleting from the end (step 17).
    pub fn set_length(&mut self, new_length: u32) {
        self.entries.retain(|&k, _| k < new_length);
        self.length = new_length;
    }
}

/// Which representation an element store holds.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    /// A vector indexed by element index, holes stored as [`HOLE_BITS`].
    Dense,
    /// An ordered map of the elements that exist.
    Sparse,
}

/// A representation's contents, as the contract sees them.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Repr {
    /// Dense: the slots.
    Dense(Vec<u64>),
    /// Sparse: the elements.
    Sparse(BTreeMap<u32, u64>),
}

impl Repr {
    /// The abstract array this representation stands for, with the given
    /// `length` (E1).
    #[must_use]
    pub fn to_spec(&self, length: u32) -> Spec {
        let entries = match self {
            Self::Dense(v) => v
                .iter()
                .enumerate()
                .filter(|&(_, &x)| x != HOLE_BITS)
                .filter_map(|(i, &x)| u32::try_from(i).ok().map(|i| (i, x)))
                .collect(),
            Self::Sparse(m) => m.clone(),
        };
        Spec { length, entries }
    }
}

/// E2.
#[must_use]
pub fn repr_well_formed(repr: &Repr, length: u32) -> bool {
    match repr {
        Repr::Dense(v) => {
            let n = u32::try_from(v.len()).ok();
            n.is_some_and(|n| n <= length && n <= MAX_DENSE)
        }
        Repr::Sparse(m) => m.iter().all(|(&k, &v)| k < length && v != HOLE_BITS),
    }
}

/// E3: the representation after a `set` at `index`, given the one before
/// and, for dense storage, its slot count `slots`.
#[must_use]
pub fn choose(mode: Mode, slots: u32, index: u32) -> Mode {
    match mode {
        Mode::Sparse => Mode::Sparse,
        Mode::Dense => {
            if index < slots {
                Mode::Dense
            } else if index >= MAX_DENSE || index.saturating_sub(slots) > MAX_GAP {
                Mode::Sparse
            } else {
                Mode::Dense
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spec_set_grows_length() {
        let mut s = Spec::new(0);
        assert_eq!(s.set(5, 7), Ok(()));
        assert_eq!(s.length, 6);
        assert_eq!(s.get(5), Some(7));
        assert_eq!(s.get(0), None);
        assert!(s.well_formed());
        assert_eq!(s.set(2, 1), Ok(()));
        assert_eq!(s.length, 6);
    }

    #[test]
    fn spec_refuses() {
        let mut s = Spec::new(3);
        assert_eq!(s.set(u32::MAX, 1), Err(Error::NotAnIndex));
        assert_eq!(s.set(0, HOLE_BITS), Err(Error::HoleValue));
        assert_eq!(s, Spec::new(3));
        assert_eq!(s.set(u32::MAX - 1, 1), Ok(()));
        assert_eq!(s.length, u32::MAX);
    }

    #[test]
    fn spec_set_length_truncates() {
        let mut s = Spec::new(0);
        for i in 0..10 {
            let _ = s.set(i, u64::from(i));
        }
        s.set_length(4);
        assert_eq!(s.length, 4);
        assert_eq!(s.get(3), Some(3));
        assert_eq!(s.get(4), None);
        s.set_length(100);
        assert_eq!(s.get(4), None, "growing adds holes only");
        assert!(s.well_formed());
        assert!(s.delete(1));
        assert!(!s.delete(1));
        assert_eq!(s.length, 100);
    }

    #[test]
    fn choose_rule() {
        assert_eq!(choose(Mode::Dense, 0, 0), Mode::Dense);
        assert_eq!(choose(Mode::Dense, 0, MAX_GAP), Mode::Dense);
        assert_eq!(choose(Mode::Dense, 0, MAX_GAP + 1), Mode::Sparse);
        assert_eq!(choose(Mode::Dense, 10, 3), Mode::Dense);
        assert_eq!(choose(Mode::Dense, MAX_DENSE - 1, MAX_DENSE), Mode::Sparse);
        assert_eq!(
            choose(Mode::Dense, MAX_DENSE - 1, MAX_DENSE - 1),
            Mode::Dense
        );
        assert_eq!(choose(Mode::Sparse, 0, 0), Mode::Sparse);
    }

    #[test]
    fn repr_view() {
        let r = Repr::Dense(vec![1, HOLE_BITS, 3]);
        let s = r.to_spec(5);
        assert_eq!(s.entries.len(), 2);
        assert!(repr_well_formed(&r, 5));
        assert!(!repr_well_formed(&r, 2));
        assert!(!repr_well_formed(
            &Repr::Sparse(BTreeMap::from([(7, 1)])),
            7
        ));
    }
}
