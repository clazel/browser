//! Shapes: hidden classes with transitions (phase-7.md item 7.5), so that an
//! inline cache has a key: a (shape id, slot index) pair per site
//! (phase-7.md, "Shapes fixed here for the JIT").
//!
//! A shape maps property keys to slot indices (and attributes). Objects that
//! gain the same properties in the same order share one shape, because a
//! shape is reached from its parent by a **transition** on `(key,
//! attributes)`. [`ROOT`] is the shape of an object with no properties.
//!
//! - **Shared shapes are immutable.** A property's slot and attributes in a
//!   shared shape never change, so an inline cache that saw `(shape, slot)`
//!   stays right for every object of that shape, forever.
//! - **Id 0 is never a shape.** `clazel-js-vm`'s spec uses shape id 0 for an
//!   empty inline-cache entry, which must never hit.
//! - **Dictionary mode.** Past [`MAX_FAST_PROPERTIES`] properties, an object
//!   gets a *dictionary* shape of its own, which is mutated in place and
//!   shared by no other object. Its id is not a stable key (the same id can
//!   gain properties), so inline caches must not cache on it
//!   ([`Shapes::is_dictionary`]). Slots of a dictionary are never reused in
//!   this slice, since property deletion is a later slice.
//!
//! Lookups walk the parent chain, at most [`MAX_FAST_PROPERTIES`] long.
//!
//! # Collection (7.6, GC10, GC12, GC13)
//!
//! The collector frees shapes ([`Shapes::sweep`]). A shape keeps its parent
//! alive (a lookup walks the chain), but a parent's *transitions* are weak:
//! a child no object has is freed, and the transition to it is removed, so
//! the same property added again makes a new shape. **A shape id is never
//! reused**: the table keeps a tombstone, and a freed id resolves to nothing
//! (so an inline cache that cached it cannot hit another shape). [`ROOT`] is
//! never freed.

use crate::gc::contract::ShapeGraph;
use crate::string::Key;
use std::collections::HashMap;

/// A shape's id. `0` is reserved and never names a shape.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ShapeId(pub u32);

/// The shape of an object with no properties.
pub const ROOT: ShapeId = ShapeId(1);

/// The most properties a shared (non-dictionary) shape has. An object that
/// gains a property beyond this many goes to dictionary mode.
pub const MAX_FAST_PROPERTIES: usize = 128;

/// Property attributes, as the bit set `WRITABLE | ENUMERABLE |
/// CONFIGURABLE` (ECMA-262 §6.1.7.1, the data property attributes).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Attrs(pub u8);

impl Attrs {
    /// `[[Writable]]`.
    pub const WRITABLE: u8 = 1;
    /// `[[Enumerable]]`.
    pub const ENUMERABLE: u8 = 2;
    /// `[[Configurable]]`.
    pub const CONFIGURABLE: u8 = 4;
    /// All three: the attributes of a property made by assignment.
    pub const ALL: Self = Self(7);
}

/// Why a shape operation failed.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Error {
    /// The id names no shape.
    Unknown,
    /// The shape already has the key.
    Exists,
    /// A shape id or a slot index no longer fits in a `u32`.
    TooMany,
}

#[derive(Debug)]
struct Shape {
    /// The shape this one was reached from, for a shared shape.
    parent: Option<ShapeId>,
    /// The property the transition from the parent added.
    added: Option<(Key, Attrs)>,
    /// The next free slot: the number of slots an object of this shape has.
    slots: u32,
    /// Transitions out of this shape (shared shapes only).
    transitions: HashMap<(Key, Attrs), ShapeId>,
    /// All properties, for a dictionary shape.
    dictionary: Option<HashMap<Key, (u32, Attrs)>>,
}

/// The table of shapes.
#[derive(Debug)]
pub struct Shapes {
    /// The shape with id `i` is at index `i - 1`; `None` once freed.
    table: Vec<Option<Shape>>,
    /// How many entries are `Some`.
    live: usize,
}

impl Default for Shapes {
    fn default() -> Self {
        Self::new()
    }
}

impl Shapes {
    /// A table holding only [`ROOT`].
    #[must_use]
    pub fn new() -> Self {
        Self {
            table: vec![Some(Shape {
                parent: None,
                added: None,
                slots: 0,
                transitions: HashMap::new(),
                dictionary: None,
            })],
            live: 1,
        }
    }

    fn get(&self, id: ShapeId) -> Option<&Shape> {
        usize::try_from(id.0)
            .ok()
            .and_then(|i| i.checked_sub(1))
            .and_then(|i| self.table.get(i))
            .and_then(Option::as_ref)
    }

    fn get_mut(&mut self, id: ShapeId) -> Option<&mut Shape> {
        usize::try_from(id.0)
            .ok()
            .and_then(|i| i.checked_sub(1))
            .and_then(|i| self.table.get_mut(i))
            .and_then(Option::as_mut)
    }

    fn push(&mut self, shape: Shape) -> Result<ShapeId, Error> {
        let id = u32::try_from(self.table.len())
            .ok()
            .and_then(|n| n.checked_add(1))
            .ok_or(Error::TooMany)?;
        self.table.push(Some(shape));
        self.live = self.live.saturating_add(1);
        Ok(ShapeId(id))
    }

    /// The number of live shapes, [`ROOT`] included.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.live
    }

    /// Always false: [`ROOT`] is never freed.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.live == 0
    }

    /// The number of shape ids ever issued, freed ones included: the size
    /// of the table the collector indexes by shape (id `n` is entry `n - 1`).
    #[must_use]
    pub fn issued(&self) -> usize {
        self.table.len()
    }

    /// Whether `id` names a live shape.
    #[must_use]
    pub fn is_live(&self, id: ShapeId) -> bool {
        self.get(id).is_some()
    }

    /// The shape `id` was reached from (a shared shape's parent; a
    /// dictionary shape and [`ROOT`] have none).
    #[must_use]
    pub fn parent(&self, id: ShapeId) -> Option<ShapeId> {
        self.get(id).and_then(|s| s.parent)
    }

    /// Free every shape but [`ROOT`] whose flag in `keep` is false (by table
    /// entry, so shape id `n` is `keep[n - 1]`; one past the end of `keep`
    /// counts as false), and remove the transitions to the freed shapes
    /// from the survivors; returns how many were freed. The caller keeps
    /// every parent of a kept shape (GC10); freed ids are never issued again
    /// (GC13).
    pub fn sweep(&mut self, keep: &[bool]) -> usize {
        let mut freed = 0usize;
        for (i, slot) in self.table.iter_mut().enumerate() {
            if i != 0 && slot.is_some() && !keep.get(i).copied().unwrap_or(false) {
                *slot = None;
                freed = freed.saturating_add(1);
            }
        }
        self.live = self.live.saturating_sub(freed);
        let alive: Vec<bool> = self.table.iter().map(Option::is_some).collect();
        for shape in self.table.iter_mut().flatten() {
            shape.transitions.retain(|_, to| {
                usize::try_from(to.0)
                    .ok()
                    .and_then(|i| i.checked_sub(1))
                    .and_then(|i| alive.get(i).copied())
                    .unwrap_or(false)
            });
        }
        freed
    }

    /// Whether `id` is a dictionary shape: unshared, mutated in place, and
    /// not to be used as an inline-cache key.
    #[must_use]
    pub fn is_dictionary(&self, id: ShapeId) -> bool {
        self.get(id).is_some_and(|s| s.dictionary.is_some())
    }

    /// How many slots an object of this shape has.
    #[must_use]
    pub fn slot_count(&self, id: ShapeId) -> Option<u32> {
        self.get(id).map(|s| s.slots)
    }

    /// The slot and attributes of `key` in the shape.
    #[must_use]
    pub fn lookup(&self, id: ShapeId, key: Key) -> Option<(u32, Attrs)> {
        let shape = self.get(id)?;
        if let Some(d) = &shape.dictionary {
            return d.get(&key).copied();
        }
        let mut at = Some(id);
        while let Some(i) = at {
            let s = self.get(i)?;
            if let Some((k, attrs)) = s.added
                && k == key
            {
                // The property added by the transition into `s` has the slot
                // numbered one less than `s`'s slot count.
                return Some((s.slots.checked_sub(1)?, attrs));
            }
            at = s.parent;
        }
        None
    }

    /// Every property of the shape in the order it was added: key, slot and
    /// attributes.
    #[must_use]
    pub fn properties(&self, id: ShapeId) -> Vec<(Key, u32, Attrs)> {
        let Some(shape) = self.get(id) else {
            return Vec::new();
        };
        let mut out: Vec<(Key, u32, Attrs)> = if let Some(d) = &shape.dictionary {
            d.iter().map(|(&k, &(slot, a))| (k, slot, a)).collect()
        } else {
            let mut v = Vec::new();
            let mut at = Some(id);
            while let Some(i) = at {
                let Some(s) = self.get(i) else { break };
                if let (Some((k, a)), Some(slot)) = (s.added, s.slots.checked_sub(1)) {
                    v.push((k, slot, a));
                }
                at = s.parent;
            }
            v
        };
        out.sort_by_key(|&(_, slot, _)| slot);
        out
    }

    /// The shape an object of shape `id` has after gaining `key` with
    /// `attrs`, and the slot the new property takes.
    ///
    /// For a shared shape, the result is the shape's transition on
    /// `(key, attrs)`, made on the first use, so objects that gain the same
    /// properties in the same order share a shape. If the shape already has
    /// [`MAX_FAST_PROPERTIES`] properties, the result is a new dictionary
    /// shape holding all of them and the new one. For a dictionary shape,
    /// the property is added in place and the id is unchanged.
    ///
    /// # Errors
    /// [`Error::Unknown`] for a bad id, [`Error::Exists`] if the shape has
    /// `key` already, [`Error::TooMany`] on overflow.
    pub fn add_property(
        &mut self,
        id: ShapeId,
        key: Key,
        attrs: Attrs,
    ) -> Result<(ShapeId, u32), Error> {
        if self.lookup(id, key).is_some() {
            return Err(Error::Exists);
        }
        let shape = self.get_mut(id).ok_or(Error::Unknown)?;
        let slot = shape.slots;
        let next = slot.checked_add(1).ok_or(Error::TooMany)?;
        if let Some(d) = &mut shape.dictionary {
            d.insert(key, (slot, attrs));
            shape.slots = next;
            return Ok((id, slot));
        }
        if let Some(&to) = shape.transitions.get(&(key, attrs)) {
            return Ok((to, slot));
        }
        let fast = usize::try_from(slot).is_ok_and(|n| n < MAX_FAST_PROPERTIES);
        if !fast {
            // Dictionary mode: copy the properties out, then add the new one.
            let mut d: HashMap<Key, (u32, Attrs)> = self
                .properties(id)
                .into_iter()
                .map(|(k, s, a)| (k, (s, a)))
                .collect();
            d.insert(key, (slot, attrs));
            let dict = self.push(Shape {
                parent: None,
                added: None,
                slots: next,
                transitions: HashMap::new(),
                dictionary: Some(d),
            })?;
            return Ok((dict, slot));
        }
        let child = self.push(Shape {
            parent: Some(id),
            added: Some((key, attrs)),
            slots: next,
            transitions: HashMap::new(),
            dictionary: None,
        })?;
        self.get_mut(id)
            .ok_or(Error::Unknown)?
            .transitions
            .insert((key, attrs), child);
        Ok((child, slot))
    }
}

impl ShapeGraph for Shapes {
    fn len(&self) -> usize {
        self.table.len()
    }

    fn exists(&self, i: usize) -> bool {
        self.table.get(i).is_some_and(Option::is_some)
    }

    fn parent(&self, i: usize) -> Option<usize> {
        let p = self.table.get(i)?.as_ref()?.parent?;
        usize::try_from(p.0).ok()?.checked_sub(1)
    }

    fn each_key(&self, i: usize, f: &mut dyn FnMut(usize)) {
        let Some(Some(shape)) = self.table.get(i) else {
            return;
        };
        let mut key = |k: Key| {
            if let Ok(k) = usize::try_from(k.0) {
                f(k);
            }
        };
        if let Some(d) = &shape.dictionary {
            d.keys().copied().for_each(&mut key);
        } else if let Some((k, _)) = shape.added {
            key(k);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const A: Key = Key(0);
    const B: Key = Key(1);
    const C: Key = Key(2);

    #[test]
    fn the_root_has_no_properties_and_id_zero_is_no_shape() {
        let t = Shapes::new();
        assert_eq!(t.slot_count(ROOT), Some(0));
        assert_eq!(t.lookup(ROOT, A), None);
        assert_eq!(t.slot_count(ShapeId(0)), None);
        assert!(!t.is_dictionary(ROOT));
    }

    #[test]
    fn same_properties_in_the_same_order_share_a_shape() -> Result<(), Error> {
        let mut t = Shapes::new();
        let (s1, _) = t.add_property(ROOT, A, Attrs::ALL)?;
        let (s2, _) = t.add_property(s1, B, Attrs::ALL)?;
        let (u1, _) = t.add_property(ROOT, A, Attrs::ALL)?;
        let (u2, _) = t.add_property(u1, B, Attrs::ALL)?;
        assert_eq!((s1, s2), (u1, u2));
        assert_eq!(t.len(), 3);
        // The other order is another shape, with the same keys.
        let (v1, _) = t.add_property(ROOT, B, Attrs::ALL)?;
        let (v2, _) = t.add_property(v1, A, Attrs::ALL)?;
        assert_ne!(v2, s2);
        assert_eq!(t.lookup(s2, A), Some((0, Attrs::ALL)));
        assert_eq!(t.lookup(s2, B), Some((1, Attrs::ALL)));
        assert_eq!(t.lookup(v2, A), Some((1, Attrs::ALL)));
        assert_eq!(t.lookup(v2, B), Some((0, Attrs::ALL)));
        Ok(())
    }

    #[test]
    fn attributes_are_part_of_the_transition() -> Result<(), Error> {
        let mut t = Shapes::new();
        let ro = Attrs(Attrs::ENUMERABLE);
        let (a, _) = t.add_property(ROOT, A, Attrs::ALL)?;
        let (b, _) = t.add_property(ROOT, A, ro)?;
        assert_ne!(a, b);
        assert_eq!(t.lookup(b, A), Some((0, ro)));
        Ok(())
    }

    #[test]
    fn a_shared_shape_is_not_changed_by_later_transitions() -> Result<(), Error> {
        let mut t = Shapes::new();
        let (s1, _) = t.add_property(ROOT, A, Attrs::ALL)?;
        let before = t.properties(s1);
        t.add_property(s1, B, Attrs::ALL)?;
        t.add_property(s1, C, Attrs::ALL)?;
        assert_eq!(t.properties(s1), before);
        assert_eq!(t.slot_count(s1), Some(1));
        assert_eq!(t.lookup(s1, B), None);
        Ok(())
    }

    #[test]
    fn a_duplicate_key_and_a_bad_id_are_errors() -> Result<(), Error> {
        let mut t = Shapes::new();
        let (s1, _) = t.add_property(ROOT, A, Attrs::ALL)?;
        assert_eq!(t.add_property(s1, A, Attrs::ALL), Err(Error::Exists));
        assert_eq!(
            t.add_property(ShapeId(99), A, Attrs::ALL),
            Err(Error::Unknown)
        );
        assert_eq!(
            t.add_property(ShapeId(0), A, Attrs::ALL),
            Err(Error::Unknown)
        );
        Ok(())
    }

    #[test]
    fn properties_come_back_in_insertion_order() -> Result<(), Error> {
        let mut t = Shapes::new();
        let (s1, _) = t.add_property(ROOT, C, Attrs::ALL)?;
        let (s2, _) = t.add_property(s1, A, Attrs::ALL)?;
        let (s3, _) = t.add_property(s2, B, Attrs::ALL)?;
        let keys: Vec<Key> = t.properties(s3).into_iter().map(|(k, _, _)| k).collect();
        assert_eq!(keys, [C, A, B]);
        Ok(())
    }

    #[test]
    fn past_the_cutoff_an_object_gets_its_own_dictionary_shape() -> Result<(), Error> {
        let mut t = Shapes::new();
        let mut s = ROOT;
        for i in 0..MAX_FAST_PROPERTIES {
            let k = Key(u32::try_from(i).map_err(|_| Error::TooMany)?);
            s = t.add_property(s, k, Attrs::ALL)?.0;
            assert!(!t.is_dictionary(s));
        }
        let shared = s;
        let extra = Key(1000);
        // Two objects crossing the cutoff do not share a shape.
        let (d1, slot1) = t.add_property(shared, extra, Attrs::ALL)?;
        let (d2, slot2) = t.add_property(shared, extra, Attrs::ALL)?;
        assert!(t.is_dictionary(d1) && t.is_dictionary(d2));
        assert_ne!(d1, d2);
        assert_eq!(
            slot1,
            u32::try_from(MAX_FAST_PROPERTIES).map_err(|_| Error::TooMany)?
        );
        assert_eq!(slot1, slot2);
        // The shared shape is untouched and every property survived.
        assert_eq!(t.lookup(shared, extra), None);
        assert_eq!(t.lookup(d1, extra), Some((slot1, Attrs::ALL)));
        assert_eq!(t.lookup(d1, Key(0)), Some((0, Attrs::ALL)));
        assert_eq!(t.properties(d1).len(), MAX_FAST_PROPERTIES + 1);
        // A dictionary shape is mutated in place, keeping its id.
        let (d1b, slot) = t.add_property(d1, Key(1001), Attrs::ALL)?;
        assert_eq!(d1b, d1);
        assert_eq!(slot, slot1 + 1);
        assert_eq!(t.lookup(d2, Key(1001)), None);
        assert_eq!(t.add_property(d1, extra, Attrs::ALL), Err(Error::Exists));
        Ok(())
    }

    #[test]
    fn a_swept_shape_is_gone_its_transition_too_and_the_root_stays() -> Result<(), Error> {
        let mut t = Shapes::new();
        let (s1, _) = t.add_property(ROOT, A, Attrs::ALL)?;
        let (s2, _) = t.add_property(s1, B, Attrs::ALL)?;
        let (s3, _) = t.add_property(s1, C, Attrs::ALL)?;
        assert_eq!((t.len(), t.issued()), (4, 4));
        assert_eq!(t.parent(s2), Some(s1));
        // Keep {a} and {a, c}; ask to free the root too, which is refused.
        assert_eq!(t.sweep(&[false, true, false, true]), 1);
        assert_eq!((t.len(), t.issued()), (3, 4));
        assert!(t.is_live(ROOT) && t.is_live(s1) && t.is_live(s3));
        assert!(!t.is_live(s2));
        assert_eq!(t.slot_count(s2), None);
        assert_eq!(t.lookup(s3, A), Some((0, Attrs::ALL)));
        // Adding `b` to {a} again makes a new shape with a new id.
        let (again, slot) = t.add_property(s1, B, Attrs::ALL)?;
        assert_ne!(again, s2);
        assert_eq!(again, ShapeId(5));
        assert_eq!(slot, 1);
        // The surviving transition is still shared.
        assert_eq!(t.add_property(s1, C, Attrs::ALL)?.0, s3);
        // A freed shape cannot gain properties.
        assert_eq!(t.add_property(s2, C, Attrs::ALL), Err(Error::Unknown));
        Ok(())
    }
}
