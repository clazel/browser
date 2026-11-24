//! The storage of `Map`, `Set`, `WeakMap` and `WeakSet` (§24.1†, §24.2†,
//! §24.3†, §24.4†): an insertion-ordered table of values keyed by
//! SameValueZero (§7.2.12†), attached to a host object ([`Vm::attach_table`]).
//!
//! # Modelling choices
//!
//! - **`[[MapData]]` and `[[SetData]]`** are the standard's Lists of records
//!   whose deleted entries become *empty* (§24.1.3.3† `Map.prototype.delete`
//!   step 5.a: "Set p.[[Key]] to empty"), so that an iterator that is part
//!   way through the List keeps its place. The table is the same: a vector
//!   of optional entries, a deleted entry `None`, and a hash index from the
//!   normalized key to its position for the lookups. The position of an entry
//!   never changes, so an iterator is a position.
//! - **The key of the index** is the Number's value (every NaN one key, `-0`
//!   as `+0`: SameValueZero), the code units of a String (strings are
//!   compared by content), or the identity of anything else.
//! - **Entries are not compacted.** A table that has had many entries
//!   deleted keeps their empty slots, as the standard's List does (an
//!   implementation may compact when no iterator is live; this one does not
//!   know which are). A loop that adds and deletes without end grows the
//!   vector by one pointer-pair per round; the step budget and the heap
//!   limit of the embedder bound the rounds. This is a listed deviation.
//! - **Weak collections hold their keys strongly**, as nothing is collected
//!   yet (item 7.6); the ephemeron semantics arrive with the collector.

use crate::interp::Vm;
use crate::numeric::num;
use clazel_js_heap::value::Value;
use std::collections::HashMap;

/// The key of the hash index: SameValueZero's classes of equal values.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum HKey {
    /// A Number, as the bits of its value with `-0` as `+0` and one NaN.
    Number(u64),
    /// A String, by its code units.
    String(Vec<u16>),
    /// Anything else, by identity (the bits of the value).
    Identity(u64),
}

/// An insertion-ordered table of key-value pairs (see the module header).
#[derive(Debug, Default)]
pub(crate) struct Table {
    entries: Vec<Option<(Value, Value)>>,
    index: HashMap<HKey, usize>,
}

/// The state of the VM's tables: they live in the host object table's rows.
impl Vm {
    /// The index key of `v` under SameValueZero (§7.2.12†).
    fn hash_key(&self, v: Value) -> HKey {
        if let Some(n) = num(v) {
            let x = n.to_f64();
            let x = if x == 0.0 { 0.0 } else { x };
            let bits = if x.is_nan() {
                f64::NAN.to_bits()
            } else {
                x.to_bits()
            };
            return HKey::Number(bits);
        }
        if let Some(s) = self.heap.string(v) {
            return HKey::String(s.units().collect());
        }
        HKey::Identity(v.bits())
    }

    /// Gives the host object `obj` an empty table (its `[[MapData]]` or
    /// `[[SetData]]`); `false` if `obj` is not a host object.
    pub fn attach_table(&mut self, obj: Value) -> bool {
        match self.host_table_mut(obj) {
            Some(slot) => {
                *slot = Some(Table::default());
                true
            }
            None => false,
        }
    }

    fn host_table(&self, obj: Value) -> Option<&Table> {
        self.host_object_table(obj)?.as_ref()
    }

    /// `Get` of the table: the value stored under `key`.
    #[must_use]
    pub fn table_get(&self, obj: Value, key: Value) -> Option<Value> {
        let t = self.host_table(obj)?;
        let i = *t.index.get(&self.hash_key(key))?;
        t.entries.get(i)?.map(|(_, v)| v)
    }

    /// Whether the table has an entry for `key` (SameValueZero).
    #[must_use]
    pub fn table_has(&self, obj: Value, key: Value) -> bool {
        self.host_table(obj)
            .is_some_and(|t| t.index.contains_key(&self.hash_key(key)))
    }

    /// Stores `value` under `key` (§24.1.3.9† `Map.prototype.set` steps 4 to
    /// 7: an existing entry's value is replaced, else the pair is appended,
    /// with `-0` as `+0`); `false` if `obj` has no table.
    pub fn table_set(&mut self, obj: Value, key: Value, value: Value) -> bool {
        let hk = self.hash_key(key);
        let key = if num(key).is_some_and(|n| n.to_f64() == 0.0) {
            Value::int32(0)
        } else {
            key
        };
        let Some(t) = self.host_table_mut(obj).and_then(Option::as_mut) else {
            return false;
        };
        if let Some(&i) = t.index.get(&hk)
            && let Some(Some(e)) = t.entries.get_mut(i)
        {
            e.1 = value;
            return true;
        }
        t.entries.push(Some((key, value)));
        let i = t.entries.len().saturating_sub(1);
        t.index.insert(hk, i);
        true
    }

    /// Removes the entry for `key`, leaving its place empty (§24.1.3.3†);
    /// whether there was one.
    pub fn table_delete(&mut self, obj: Value, key: Value) -> bool {
        let hk = self.hash_key(key);
        let Some(t) = self.host_table_mut(obj).and_then(Option::as_mut) else {
            return false;
        };
        let Some(i) = t.index.remove(&hk) else {
            return false;
        };
        if let Some(e) = t.entries.get_mut(i) {
            *e = None;
        }
        true
    }

    /// Empties every entry, keeping the places (§24.1.3.1† step 4).
    pub fn table_clear(&mut self, obj: Value) -> bool {
        let Some(t) = self.host_table_mut(obj).and_then(Option::as_mut) else {
            return false;
        };
        t.entries.fill(None);
        t.index.clear();
        true
    }

    /// The number of entries that are not empty.
    #[must_use]
    pub fn table_size(&self, obj: Value) -> Option<usize> {
        self.host_table(obj).map(|t| t.index.len())
    }

    /// The number of places, empty ones included (the standard's "number of
    /// elements in the List", which an `index` loop reads again each round).
    #[must_use]
    pub fn table_places(&self, obj: Value) -> Option<usize> {
        self.host_table(obj).map(|t| t.entries.len())
    }

    /// The entry at place `pos`, if there is one that is not empty.
    #[must_use]
    pub fn table_entry(&self, obj: Value, pos: usize) -> Option<(Value, Value)> {
        self.host_table(obj)?.entries.get(pos).copied().flatten()
    }

    /// The first entry that is not empty at a place `>= pos`: its place plus
    /// one (where to go on), its key and its value.
    #[must_use]
    pub fn table_next(&self, obj: Value, pos: usize) -> Option<(usize, Value, Value)> {
        let t = self.host_table(obj)?;
        let mut i = pos;
        while let Some(e) = t.entries.get(i) {
            if let Some((k, v)) = e {
                return Some((i.saturating_add(1), *k, *v));
            }
            i = i.saturating_add(1);
        }
        None
    }
}
