//! Elements: the indexed properties of an array (phase-7.md item 7.5).
//!
//! [`contract`] states what element storage must do (E1 to E4) and when it
//! falls back from dense to sparse (E3). [`Elements`] follows it:
//!
//! - **Dense:** a `Vec<u64>` of NaN-boxed values indexed by element index,
//!   with [`Value::HOLE`] in the slots that have no element. Reads and
//!   writes within it are one bounds-checked access, which is the shape the
//!   interpreter's element ops and the JIT's templates want.
//! - **Sparse:** a `BTreeMap` of the elements that exist.
//!
//! The `length` is a separate `u32`, so growing it (`new Array(n)`) costs
//! nothing and a sparse array of length 2^32 - 1 is a few words.
//!
//! The collector (7.6) will need to enumerate the values: [`Elements::values`]
//! does, in index order, for either representation.

pub mod contract;

use crate::value::Value;
use contract::{Error, MAX_DENSE, Mode, Repr, Spec, choose, repr_well_formed};
use std::collections::BTreeMap;

pub use contract::{INDEX_LIMIT, MAX_GAP};

/// The elements of one array.
#[derive(Clone, Debug)]
pub struct Elements {
    length: u32,
    repr: Repr,
}

impl Default for Elements {
    fn default() -> Self {
        Self::new()
    }
}

impl Elements {
    /// An empty array of length 0, dense.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            length: 0,
            repr: Repr::Dense(Vec::new()),
        }
    }

    /// An array of the given length with no elements (all holes), `new
    /// Array(length)`. Dense and empty: nothing is allocated for the holes
    /// (E4).
    #[must_use]
    pub const fn with_length(length: u32) -> Self {
        Self {
            length,
            repr: Repr::Dense(Vec::new()),
        }
    }

    /// The array's `length`.
    #[must_use]
    pub const fn len(&self) -> u32 {
        self.length
    }

    /// Whether `length` is 0.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.length == 0
    }

    /// Which representation is in use (E3).
    #[must_use]
    pub const fn mode(&self) -> Mode {
        match self.repr {
            Repr::Dense(_) => Mode::Dense,
            Repr::Sparse(_) => Mode::Sparse,
        }
    }

    /// The element at `index`; `None` for a hole or an index at or past the
    /// length (the caller then goes up the prototype chain).
    #[must_use]
    pub fn get(&self, index: u32) -> Option<Value> {
        let bits = match &self.repr {
            Repr::Dense(v) => {
                let i = usize::try_from(index).ok()?;
                *v.get(i)?
            }
            Repr::Sparse(m) => *m.get(&index)?,
        };
        if bits == contract::HOLE_BITS {
            return None;
        }
        Value::from_bits(bits)
    }

    /// Whether an element exists at `index`.
    #[must_use]
    pub fn has(&self, index: u32) -> bool {
        self.get(index).is_some()
    }

    /// Store `value` at `index`, growing the length if `index >= length`
    /// (contract: `Spec::set`). May turn dense storage sparse (E3).
    ///
    /// # Errors
    /// [`Error::NotAnIndex`] for `u32::MAX`; [`Error::HoleValue`] for
    /// [`Value::HOLE`]; [`Error::OutOfMemory`] if dense storage could not
    /// grow. Nothing changes on error.
    pub fn set(&mut self, index: u32, value: Value) -> Result<(), Error> {
        if index == INDEX_LIMIT {
            return Err(Error::NotAnIndex);
        }
        if value == Value::HOLE {
            return Err(Error::HoleValue);
        }
        let bits = value.bits();
        let slots = match &self.repr {
            Repr::Dense(v) => u32::try_from(v.len()).unwrap_or(u32::MAX),
            Repr::Sparse(_) => 0,
        };
        let before = self.mode();
        if choose(before, slots, index) == Mode::Sparse && before == Mode::Dense {
            self.make_sparse();
        }
        match &mut self.repr {
            Repr::Dense(v) => {
                let i = usize::try_from(index).map_err(|_| Error::NotAnIndex)?;
                if let Some(slot) = v.get_mut(i) {
                    *slot = bits;
                } else {
                    // `choose` kept it dense: the gap is at most MAX_GAP and
                    // `index < MAX_DENSE`, so this reserves at most MAX_DENSE
                    // slots in all (E4).
                    let need = i.saturating_add(1).saturating_sub(v.len());
                    v.try_reserve(need).map_err(|_| Error::OutOfMemory)?;
                    v.resize(i, contract::HOLE_BITS);
                    v.push(bits);
                }
            }
            Repr::Sparse(m) => {
                m.insert(index, bits);
            }
        }
        if index >= self.length {
            self.length = index.saturating_add(1);
        }
        Ok(())
    }

    /// Remove the element at `index`, leaving a hole; the length stays.
    /// Returns whether an element was there.
    pub fn delete(&mut self, index: u32) -> bool {
        match &mut self.repr {
            Repr::Dense(v) => {
                let Some(slot) = usize::try_from(index).ok().and_then(|i| v.get_mut(i)) else {
                    return false;
                };
                let was = *slot != contract::HOLE_BITS;
                *slot = contract::HOLE_BITS;
                was
            }
            Repr::Sparse(m) => m.remove(&index).is_some(),
        }
    }

    /// Set `length`, dropping every element at or past it (contract:
    /// `Spec::set_length`). Never allocates, and never changes the
    /// representation (E3, E4).
    pub fn set_length(&mut self, new_length: u32) {
        match &mut self.repr {
            Repr::Dense(v) => {
                let keep = usize::try_from(new_length).unwrap_or(usize::MAX);
                v.truncate(keep);
            }
            Repr::Sparse(m) => {
                // `split_off` keeps keys below the bound in `m`.
                drop(m.split_off(&new_length));
            }
        }
        self.length = new_length;
    }

    /// The existing elements as `(index, value)`, in index order.
    pub fn entries(&self) -> Box<dyn Iterator<Item = (u32, Value)> + '_> {
        match &self.repr {
            Repr::Dense(v) => Box::new(v.iter().enumerate().filter_map(|(i, &b)| {
                let i = u32::try_from(i).ok()?;
                (b != contract::HOLE_BITS)
                    .then(|| Value::from_bits(b))
                    .flatten()
                    .map(|x| (i, x))
            })),
            Repr::Sparse(m) => Box::new(
                m.iter()
                    .filter_map(|(&i, &b)| Value::from_bits(b).map(|x| (i, x))),
            ),
        }
    }

    /// The existing values, in index order: what the collector scans.
    pub fn values(&self) -> impl Iterator<Item = Value> + '_ {
        self.entries().map(|(_, v)| v)
    }

    /// The abstract array this storage stands for (E1).
    #[must_use]
    pub fn to_spec(&self) -> Spec {
        self.repr.to_spec(self.length)
    }

    /// E2 for the current state.
    #[must_use]
    pub fn is_well_formed(&self) -> bool {
        repr_well_formed(&self.repr, self.length)
    }

    fn make_sparse(&mut self) {
        if let Repr::Dense(v) = &self.repr {
            let m: BTreeMap<u32, u64> = v
                .iter()
                .enumerate()
                .filter(|&(_, &b)| b != contract::HOLE_BITS)
                .filter_map(|(i, &b)| u32::try_from(i).ok().map(|i| (i, b)))
                .collect();
            self.repr = Repr::Sparse(m);
        }
    }

    /// The most slots dense storage may hold (E4).
    pub const DENSE_LIMIT: u32 = MAX_DENSE;
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(i: i32) -> Value {
        Value::int32(i)
    }

    fn put(e: &mut Elements, index: u32, v: Value) {
        assert_eq!(e.set(index, v), Ok(()));
    }

    #[test]
    fn push_get_length() {
        let mut e = Elements::new();
        assert!(e.is_empty());
        for i in 0..5u32 {
            assert_eq!(e.set(i, n(i32::try_from(i).unwrap_or(0))), Ok(()));
        }
        assert_eq!(e.len(), 5);
        assert_eq!(e.get(3), Some(n(3)));
        assert_eq!(e.get(5), None);
        assert_eq!(e.mode(), Mode::Dense);
        assert!(e.is_well_formed());
    }

    #[test]
    fn holes_in_dense() {
        let mut e = Elements::new();
        put(&mut e, 0, n(1));
        put(&mut e, 10, n(2));
        assert_eq!(e.mode(), Mode::Dense);
        assert_eq!(e.len(), 11);
        assert!(!e.has(5));
        assert!(e.has(10));
        assert!(e.delete(10));
        assert!(!e.delete(10));
        assert_eq!(e.len(), 11, "delete leaves the length");
        assert_eq!(e.entries().count(), 1);
    }

    #[test]
    fn falls_back_past_the_gap() {
        let mut e = Elements::new();
        put(&mut e, 0, n(1));
        put(&mut e, MAX_GAP + 1, n(2));
        assert_eq!(e.mode(), Mode::Dense, "slots is 1, so the gap is MAX_GAP");
        put(&mut e, MAX_GAP + 1 + MAX_GAP + 2, n(3));
        assert_eq!(e.mode(), Mode::Sparse);
        assert_eq!(e.get(0), Some(n(1)));
        assert_eq!(e.get(MAX_GAP + 1), Some(n(2)));
        assert_eq!(e.entries().count(), 3);
        assert!(e.is_well_formed());
    }

    #[test]
    fn sparse_stays_sparse() {
        let mut e = Elements::new();
        put(&mut e, 1_000_000, n(1));
        assert_eq!(e.mode(), Mode::Sparse);
        e.set_length(0);
        assert_eq!(e.mode(), Mode::Sparse);
        put(&mut e, 0, n(2));
        assert_eq!(e.mode(), Mode::Sparse);
        assert_eq!(e.len(), 1);
    }

    #[test]
    fn huge_length_costs_nothing() {
        let mut e = Elements::with_length(u32::MAX);
        assert_eq!(e.len(), u32::MAX);
        assert_eq!(e.mode(), Mode::Dense);
        assert_eq!(e.get(7), None);
        assert_eq!(e.set(u32::MAX, n(1)), Err(Error::NotAnIndex));
        assert_eq!(e.set(u32::MAX - 1, n(1)), Ok(()));
        assert_eq!(e.mode(), Mode::Sparse);
        assert_eq!(e.len(), u32::MAX);
        assert!(e.is_well_formed());
    }

    #[test]
    fn dense_limit_makes_sparse() {
        let mut e = Elements::new();
        // Reaching MAX_DENSE by index, with every set in range of the gap
        // rule, is not feasible to do slot by slot in a test; jump instead.
        put(&mut e, MAX_DENSE, n(1));
        assert_eq!(e.mode(), Mode::Sparse);
    }

    #[test]
    fn refuses_hole_value_and_changes_nothing() {
        let mut e = Elements::new();
        put(&mut e, 0, n(1));
        let before = e.to_spec();
        assert_eq!(e.set(1, Value::HOLE), Err(Error::HoleValue));
        assert_eq!(e.set(u32::MAX, n(1)), Err(Error::NotAnIndex));
        assert_eq!(e.to_spec(), before);
        assert_eq!(e.len(), 1);
    }

    #[test]
    fn set_length_truncates_both() {
        for sparse in [false, true] {
            let mut e = Elements::new();
            if sparse {
                put(&mut e, 100_000, n(9));
                e.delete(100_000);
            }
            for i in 0..10u32 {
                put(&mut e, i, n(i32::try_from(i).unwrap_or(0)));
            }
            assert_eq!(e.mode() == Mode::Sparse, sparse);
            e.set_length(4);
            assert_eq!(e.len(), 4);
            assert_eq!(e.get(3), Some(n(3)));
            assert_eq!(e.get(4), None);
            e.set_length(50);
            assert_eq!(e.get(4), None);
            assert_eq!(e.values().count(), 4);
            assert!(e.is_well_formed());
        }
    }

    /// A small deterministic generator, so the test needs no dependency.
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            self.0 >> 33
        }
    }

    /// E1, E2 and E3 over random operation sequences against `Spec`.
    #[test]
    fn matches_the_spec_on_random_sequences() {
        let mut rng = Lcg(0x5EED);
        for _ in 0..300 {
            let mut e = Elements::new();
            let mut s = Spec::new(0);
            for _ in 0..200 {
                let op = rng.next() % 8;
                // Mostly small indices, some far, some at the edge.
                let index = match rng.next() % 10 {
                    0 => u32::try_from(rng.next() % 5000).unwrap_or(0) + 2000,
                    1 => u32::MAX - u32::try_from(rng.next() % 3).unwrap_or(0),
                    _ => u32::try_from(rng.next() % 40).unwrap_or(0),
                };
                let before = (
                    e.mode(),
                    match &e.repr {
                        Repr::Dense(v) => u32::try_from(v.len()).unwrap_or(0),
                        Repr::Sparse(_) => 0,
                    },
                );
                match op {
                    0..=3 => {
                        let v = if rng.next().is_multiple_of(9) {
                            Value::HOLE
                        } else {
                            n(i32::try_from(rng.next() % 1000).unwrap_or(0))
                        };
                        let got = e.set(index, v);
                        let want = s.set(index, v.bits());
                        assert_eq!(got, want);
                        if got.is_ok() {
                            assert_eq!(e.mode(), choose(before.0, before.1, index));
                        }
                    }
                    4 | 5 => assert_eq!(e.delete(index), s.delete(index)),
                    6 => {
                        let l = u32::try_from(rng.next() % 60).unwrap_or(0);
                        let mode = e.mode();
                        e.set_length(l);
                        s.set_length(l);
                        assert_eq!(e.mode(), mode);
                    }
                    _ => assert_eq!(e.get(index).map(Value::bits), s.get(index)),
                }
                assert!(e.is_well_formed());
                assert!(s.well_formed());
                assert_eq!(e.to_spec(), s);
                assert_eq!(e.len(), s.length);
            }
        }
    }
}
