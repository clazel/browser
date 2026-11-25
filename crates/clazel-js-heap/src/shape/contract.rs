//! The contract of the shape property index, stated before the
//! implementation (CLAUDE.md rule 3).
//!
//! # What is modelled
//!
//! A shared shape is reached from [`super::ROOT`] by a chain of transitions,
//! each adding one property. Its properties, in slot order, are the keys and
//! attributes those transitions added, oldest first: the property added by
//! the `i`-th transition has slot `i`. This sequence is the shape's
//! **chain**. The spec of a lookup is [`spec_lookup`]: the slot and
//! attributes of the key's entry in the chain, or nothing.
//!
//! Before the index, [`super::Shapes::lookup`] walked the parent links from
//! the shape back to the root, comparing each added key: the spec run
//! backwards, `O(n)` per lookup, and the hot spot of building a runtime.
//! The index makes the lookup a binary search, and must give exactly what
//! the walk gave.
//!
//! Modelling choices:
//!
//! - **The spec is the chain, not ECMA-262.** Shapes are an engine
//!   structure with no standard behind them; what is specified is agreement
//!   with the parent walk, which the unit tests of `shape` also pin down.
//! - **Dictionary shapes are not indexed.** A dictionary shape keeps its own
//!   map (`super`'s module docs) and does not use a table.
//! - **Keys in a chain are distinct.** `add_property` refuses a key the shape
//!   has, so a chain never holds a key twice; [`spec_lookup`] takes the
//!   first match, which is then the only one.
//!
//! # The index
//!
//! The index is a set of **tables**. A table is a sequence of entries
//! `(key, attrs)` in slot order, plus the same keys sorted, each with its
//! slot. Every shared shape names one table, and only the first `n` entries
//! of it count for the shape, where `n` is the shape's slot count. Shapes on
//! one line of transitions share a table: a child that extends the parent's
//! table at its end appends to it in place; a child of a shape whose table
//! already runs past it (a branch) gets a new table, a copy of the parent's
//! first `n` entries with the new one appended.
//!
//! # What the implementation must meet
//!
//! - **X1. Prefix.** For every live shared shape of slot count `n` and table
//!   `t`: `t` has at least `n` entries, and its first `n` are the shape's
//!   chain.
//! - **X2. Well-formed table** ([`table_well_formed`]). The keys of a
//!   table's entries are distinct, and its sorted list is those keys in
//!   strictly increasing order, each with the slot of its entry, and
//!   nothing else.
//! - **X3. Lookup.** The index's lookup of `key` in table `t` for slot count
//!   `n` returns [`spec_lookup`] of `t`'s first `n` entries: by X1, the
//!   chain's answer. A slot it returns is below `n`, and no lookup indexes
//!   past the end of a vector.
//! - **X4. Extension.** Extending table `t` at `n` (with a key not among its
//!   first `n` entries) gives a table whose first `n + 1` entries are `t`'s
//!   first `n` followed by the new entry. It changes `t` only by appending
//!   when `t` has exactly `n` entries, so the first `m <= n` entries of `t`,
//!   which are all any other shape of `t` sees, are unchanged.
//! - **X5. Retention.** Given the `(table, n)` pairs of the live shapes
//!   after a collection, the index frees every table no live shape names,
//!   and shortens every other one to the largest `n` naming it. Every live
//!   shape's first `n` entries are unchanged (so X1 still holds), and X2
//!   holds of the shortened table.

use crate::shape::Attrs;
use crate::string::Key;

/// The slot and attributes of `key` among `props`, the properties of a shape
/// in slot order (its chain): entry `i` has slot `i`.
#[must_use]
pub fn spec_lookup(props: &[(Key, Attrs)], key: Key) -> Option<(u32, Attrs)> {
    for (i, &(k, a)) in props.iter().enumerate() {
        if k == key {
            return u32::try_from(i).ok().map(|slot| (slot, a));
        }
    }
    None
}

/// X2: `entries` (in slot order) have distinct keys, and `sorted` is
/// exactly those keys in strictly increasing order, each paired with its
/// entry's slot.
#[must_use]
pub fn table_well_formed(entries: &[(Key, Attrs)], sorted: &[(Key, u32)]) -> bool {
    if entries.len() != sorted.len() {
        return false;
    }
    // Strictly increasing, so distinct.
    for pair in sorted.windows(2) {
        let (Some(a), Some(b)) = (pair.first(), pair.get(1)) else {
            return false;
        };
        if a.0 >= b.0 {
            return false;
        }
    }
    // Each sorted pair names an entry with that key; with equal lengths and
    // distinct sorted keys, that makes the keys of the entries distinct and
    // the sorted list a permutation of them.
    sorted.iter().all(|&(k, slot)| {
        usize::try_from(slot)
            .ok()
            .and_then(|i| entries.get(i))
            .is_some_and(|&(ek, _)| ek == k)
    })
}
