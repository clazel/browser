//! The generational arena (phase-7.md item 7.5). [`contract`] states what
//! it must satisfy; this is the implementation, and `src/proofs.rs` holds
//! the Kani harnesses for the contract.
//!
//! A [`Ref`] is a `u32` index and a `u16` generation, the pair a NaN-boxed
//! heap reference carries (`crate::value`). Freeing a slot raises its
//! generation, so every older `Ref` to it is stale and a lookup reports
//! [`Error::Stale`] instead of returning whatever lives there now.
//!
//! For the collector (item 7.6): [`Arena::iter`] enumerates the live slots
//! in index order, and [`Arena::free`] frees one by reference. Sweeping is
//! a loop of the two.

pub mod contract;

use contract::{Kind, SlotView};

/// A reference into an [`Arena`]: a slot index and the generation the slot
/// had when the reference was made.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Ref {
    /// The slot.
    pub index: u32,
    /// The slot's generation when this reference was made.
    pub generation: u16,
}

/// Why an arena operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The arena holds its limit of slots and none is free.
    Full,
    /// The reference's index is past the end of the arena.
    OutOfRange,
    /// The slot is free or retired, or its generation is not the
    /// reference's: the object the reference named is gone.
    Stale,
    /// The arena's own invariants do not hold ([`contract::well_formed`]).
    /// Unreachable by construction; reported rather than panicking.
    Corrupt,
}

/// The most slots an arena may hold: a reference's index is a `u32`, and
/// the last index is kept out so that `len` fits one too.
pub const MAX_SLOTS: usize = u32::MAX as usize;

/// Slots an arena reserves room for up front.
const INITIAL_CAPACITY: usize = 16;

#[derive(Debug)]
enum Entry<T> {
    Live(T),
    Free(Option<u32>),
    Retired,
}

#[derive(Debug)]
struct Slot<T> {
    generation: u16,
    entry: Entry<T>,
}

impl<T> Slot<T> {
    const fn view(&self) -> SlotView {
        SlotView {
            generation: self.generation,
            kind: match self.entry {
                Entry::Live(_) => Kind::Live,
                Entry::Free(next) => Kind::Free(next),
                Entry::Retired => Kind::Retired,
            },
        }
    }
}

/// An index-based arena with generations.
#[derive(Debug)]
pub struct Arena<T> {
    slots: Vec<Slot<T>>,
    head: Option<u32>,
    live: usize,
    limit: usize,
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Arena<T> {
    /// An empty arena that may grow to [`MAX_SLOTS`].
    #[must_use]
    pub fn new() -> Self {
        Self::with_limit(MAX_SLOTS)
    }

    /// An empty arena that may hold at most `limit` slots (capped at
    /// [`MAX_SLOTS`]): the heap's memory limit, and the harnesses' bound.
    #[must_use]
    pub fn with_limit(limit: usize) -> Self {
        let limit = limit.min(MAX_SLOTS);
        Self {
            // Room for the first slots, so the common small arena never
            // reallocates (and a bounded harness's growth is not a path).
            slots: Vec::with_capacity(limit.min(INITIAL_CAPACITY)),
            head: None,
            live: 0,
            limit,
        }
    }

    /// The number of live slots.
    #[must_use]
    pub const fn live(&self) -> usize {
        self.live
    }

    /// The number of slots, live, free and retired.
    #[must_use]
    pub const fn slots(&self) -> usize {
        self.slots.len()
    }

    /// Store `value` and return a reference to it. Reuses the most
    /// recently freed slot, else grows by one.
    ///
    /// # Errors
    /// [`Error::Full`] when no slot is free and the arena is at its limit.
    pub fn alloc(&mut self, value: T) -> Result<Ref, Error> {
        if let Some(index) = self.head {
            let slot = usize::try_from(index)
                .ok()
                .and_then(|i| self.slots.get_mut(i))
                .ok_or(Error::Corrupt)?;
            let Entry::Free(next) = slot.entry else {
                return Err(Error::Corrupt);
            };
            slot.entry = Entry::Live(value);
            self.head = next;
            self.live = self.live.saturating_add(1);
            return Ok(Ref {
                index,
                generation: slot.generation,
            });
        }
        if self.slots.len() >= self.limit {
            return Err(Error::Full);
        }
        let index = u32::try_from(self.slots.len()).map_err(|_| Error::Full)?;
        self.slots.push(Slot {
            generation: 0,
            entry: Entry::Live(value),
        });
        self.live = self.live.saturating_add(1);
        Ok(Ref {
            index,
            generation: 0,
        })
    }

    fn slot(&self, r: Ref) -> Result<&Slot<T>, Error> {
        let slot = usize::try_from(r.index)
            .ok()
            .and_then(|i| self.slots.get(i))
            .ok_or(Error::OutOfRange)?;
        if slot.generation == r.generation {
            Ok(slot)
        } else {
            Err(Error::Stale)
        }
    }

    /// The value `r` names.
    ///
    /// # Errors
    /// [`Error::OutOfRange`], or [`Error::Stale`] if the slot has been
    /// freed since `r` was made.
    pub fn get(&self, r: Ref) -> Result<&T, Error> {
        match &self.slot(r)?.entry {
            Entry::Live(v) => Ok(v),
            _ => Err(Error::Stale),
        }
    }

    /// The value `r` names, mutably.
    ///
    /// # Errors
    /// As [`Arena::get`].
    pub fn get_mut(&mut self, r: Ref) -> Result<&mut T, Error> {
        self.slot(r)?;
        let slot = usize::try_from(r.index)
            .ok()
            .and_then(|i| self.slots.get_mut(i))
            .ok_or(Error::OutOfRange)?;
        match &mut slot.entry {
            Entry::Live(v) => Ok(v),
            _ => Err(Error::Stale),
        }
    }

    /// Whether `r` names a live value.
    #[must_use]
    pub fn is_live(&self, r: Ref) -> bool {
        self.get(r).is_ok()
    }

    /// Free the slot `r` names and return its value. Every reference to the
    /// slot made so far becomes stale. A slot whose generation is exhausted
    /// is retired instead of being put on the free list.
    ///
    /// # Errors
    /// [`Error::OutOfRange`], or [`Error::Stale`] (so a double free is an
    /// error, not a second free).
    pub fn free(&mut self, r: Ref) -> Result<T, Error> {
        self.get(r)?;
        let slot = usize::try_from(r.index)
            .ok()
            .and_then(|i| self.slots.get_mut(i))
            .ok_or(Error::OutOfRange)?;
        let next_generation = slot.generation.checked_add(1);
        let new = match next_generation {
            Some(g) => {
                slot.generation = g;
                Entry::Free(self.head)
            }
            None => Entry::Retired,
        };
        let old = std::mem::replace(&mut slot.entry, new);
        if next_generation.is_some() {
            self.head = Some(r.index);
        }
        self.live = self.live.saturating_sub(1);
        match old {
            Entry::Live(v) => Ok(v),
            _ => Err(Error::Corrupt),
        }
    }

    /// The live slots, in index order: each one's reference and value.
    pub fn iter(&self) -> impl Iterator<Item = (Ref, &T)> {
        self.slots
            .iter()
            .enumerate()
            .filter_map(|(i, s)| match &s.entry {
                Entry::Live(v) => Some((
                    Ref {
                        index: u32::try_from(i).ok()?,
                        generation: s.generation,
                    },
                    v,
                )),
                _ => None,
            })
    }

    /// The slots as the contract sees them.
    #[must_use]
    pub fn view(&self) -> Vec<SlotView> {
        self.slots.iter().map(Slot::view).collect()
    }

    /// Whether [`contract::well_formed`] holds of this arena.
    #[must_use]
    pub fn is_well_formed(&self) -> bool {
        contract::well_formed(&self.view(), self.head, self.live)
    }

    /// Set a slot's generation, for the harnesses: they start from any
    /// generation, so that retirement is reachable within a small bound.
    #[cfg(kani)]
    pub(crate) fn set_generation(&mut self, index: usize, generation: u16) {
        if let Some(s) = self.slots.get_mut(index) {
            s.generation = generation;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alloc_get_free() -> Result<(), Error> {
        let mut a = Arena::new();
        let x = a.alloc("x")?;
        let y = a.alloc("y")?;
        assert_eq!((a.get(x)?, a.get(y)?), (&"x", &"y"));
        assert_eq!(a.free(x)?, "x");
        assert_eq!(a.get(x), Err(Error::Stale));
        assert_eq!(a.free(x), Err(Error::Stale));
        assert_eq!((a.live(), a.slots()), (1, 2));
        assert!(a.is_well_formed());
        Ok(())
    }

    #[test]
    fn a_reused_slot_does_not_alias_a_stale_reference() -> Result<(), Error> {
        let mut a = Arena::new();
        let old = a.alloc(1)?;
        a.free(old)?;
        let new = a.alloc(2)?;
        assert_eq!(new.index, old.index);
        assert_eq!(new.generation, old.generation.wrapping_add(1));
        assert_eq!(a.get(old), Err(Error::Stale));
        assert_eq!(a.get(new), Ok(&2));
        *a.get_mut(new)? = 3;
        assert_eq!(a.get_mut(old), Err(Error::Stale));
        assert_eq!(a.get(new), Ok(&3));
        Ok(())
    }

    #[test]
    fn out_of_range_is_not_stale() {
        let a: Arena<u8> = Arena::new();
        let r = Ref {
            index: 5,
            generation: 0,
        };
        assert_eq!(a.get(r), Err(Error::OutOfRange));
    }

    #[test]
    fn the_limit_is_enforced_and_freeing_makes_room() -> Result<(), Error> {
        let mut a = Arena::with_limit(2);
        let x = a.alloc(0)?;
        a.alloc(1)?;
        assert_eq!(a.alloc(2), Err(Error::Full));
        a.free(x)?;
        assert!(a.alloc(2).is_ok());
        assert!(a.is_well_formed());
        Ok(())
    }

    #[test]
    fn the_free_list_is_last_in_first_out() -> Result<(), Error> {
        let mut a = Arena::new();
        let r: Vec<Ref> = (0..3).map(|i| a.alloc(i)).collect::<Result<_, _>>()?;
        let (r0, r1) = (
            r.first().copied().ok_or(Error::Corrupt)?,
            r.get(1).copied().ok_or(Error::Corrupt)?,
        );
        a.free(r0)?;
        a.free(r1)?;
        assert_eq!(a.alloc(9)?.index, r1.index);
        assert_eq!(a.alloc(9)?.index, r0.index);
        assert!(a.is_well_formed());
        Ok(())
    }

    #[test]
    fn a_slot_is_retired_when_its_generation_runs_out() -> Result<(), Error> {
        let mut a = Arena::new();
        let mut r = a.alloc(0u32)?;
        // Free and reallocate the one slot until its generation is the last.
        for _ in 0..u16::MAX {
            a.free(r)?;
            r = a.alloc(0)?;
        }
        assert_eq!(r.generation, u16::MAX);
        a.free(r)?;
        assert_eq!(a.get(r), Err(Error::Stale));
        assert!(a.is_well_formed());
        // The retired slot is never handed out again: a new slot is used.
        let n = a.alloc(1)?;
        assert_ne!(n.index, r.index);
        assert_eq!(a.slots(), 2);
        assert_eq!(a.view().first().map(|s| s.kind), Some(Kind::Retired));
        Ok(())
    }

    #[test]
    fn iteration_lists_live_slots_in_order() -> Result<(), Error> {
        let mut a = Arena::new();
        let x = a.alloc('a')?;
        let y = a.alloc('b')?;
        let z = a.alloc('c')?;
        a.free(y)?;
        let seen: Vec<(Ref, char)> = a.iter().map(|(r, c)| (r, *c)).collect();
        assert_eq!(seen, [(x, 'a'), (z, 'c')]);
        Ok(())
    }
}
