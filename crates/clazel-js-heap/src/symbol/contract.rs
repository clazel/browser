//! The contract of symbols and property keys (phase-7.md item 7.5, "The
//! rest"), stated before the implementation (CLAUDE.md rule 3).
//!
//! # What is modelled
//!
//! ECMA-262 §6.1.5, The Symbol Type: a Symbol is a primitive value that is
//! unique and immutable, and may hold a *description* (a String or
//! `undefined`); and §6.1.7, property keys: a property key is a String or a
//! Symbol.
//!
//! Modelling choices (SPEC-STYLE.md):
//!
//! - **A symbol is its id.** [`SymbolId`] is a `u32` into a table; two
//!   symbols are the same value exactly when their ids are equal, however
//!   their descriptions compare (§6.1.5: "each Symbol value immutably holds
//!   an associated value called [[Description]]"; identity is not the
//!   description).
//! - **Symbols are never freed in this slice.** Reclaiming one needs the
//!   collector (7.6); until then a table only grows, so an id is never
//!   reused (Y2).
//! - **The global symbol registry** (`Symbol.for`, §20.4.2.2 and the
//!   GlobalSymbolRegistry of §20.4.2) is a built-in's state, not the
//!   heap's, and is absent here.
//! - **A symbol as a value** (its NaN-boxed form, a heap reference or a
//!   tagged id) is not decided here; this slice is the table and the key.
//! - **Step numbers** are not cited: the clauses used have none to quote.
//!
//! # Well-known symbols (§6.1.5.1, Table 1)
//!
//! The standard's thirteen well-known symbols are the **fixed ids 0 to
//! 12**, in the order of [`WELL_KNOWN`], and exist in every table from the
//! start. Their description is `"Symbol."` followed by the name, as the
//! standard gives them (`@@iterator` is described `Symbol.iterator`).
//!
//! # Invariants
//!
//! - **Y1. Fixed ids.** In every table, the symbol with id `i < 13` is the
//!   well-known symbol `WELL_KNOWN[i]`, with that description. Created
//!   symbols have ids from 13 up, in creation order.
//! - **Y2. Unique and never reused.** Creating a symbol returns the id equal
//!   to the table's length before, so no created symbol has the id of any
//!   earlier one, and the table's length grows by exactly one.
//! - **Y3. Immutable description.** A symbol's description (a string, or
//!   none) is what it was created with, in every later state. A symbol
//!   created with the empty-string description is distinct from one with no
//!   description: [`Description`] has two cases, not an `Option` collapsed
//!   to empty.
//! - **Y4. Keys do not collide.** [`encode`] maps a [`PropertyKey`] to the
//!   shapes' [`Key`], a `u32`, as follows: a string key `k` with `k < 2^31`
//!   to itself; a symbol `s` with `s < 2^31` to `s | 2^31`. It is
//!   injective, so a string and a symbol never share a key, and [`decode`]
//!   is its inverse: `decode(encode(p)) == p` for every `p` it accepts, and
//!   `encode(decode(k)) == Some(k)` for every key.
//! - **Y5. Capacity.** Strings interned as keys and symbols created are
//!   each limited to `2^31` by Y4's encoding; one more is an error, never a
//!   wrapped id.

use crate::string::Key;

/// A symbol: an index into a symbol table.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct SymbolId(pub u32);

/// A property key: a String (interned) or a Symbol (§6.1.7).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PropertyKey {
    /// An interned string.
    String(Key),
    /// A symbol.
    Symbol(SymbolId),
}

/// A symbol's `[[Description]]` (§6.1.5): `undefined`, or a String. The
/// empty string and `undefined` differ (Y3).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Description<S> {
    /// `undefined`.
    Undefined,
    /// A String.
    Text(S),
}

/// The bit that marks a symbol's key (Y4); string keys are below it.
pub const SYMBOL_BIT: u32 = 1 << 31;

/// §6.1.5.1 Table 1, in id order (Y1): the names of `Symbol.<name>`.
pub const WELL_KNOWN: [&str; 13] = [
    "asyncIterator",
    "hasInstance",
    "isConcatSpreadable",
    "iterator",
    "match",
    "matchAll",
    "replace",
    "search",
    "species",
    "split",
    "toPrimitive",
    "toStringTag",
    "unscopables",
];

/// How many well-known symbols there are.
pub const WELL_KNOWN_COUNT: u32 = 13;

/// Y4: the key for a property key, or `None` if its number is too large
/// for the encoding (Y5).
#[must_use]
pub const fn encode(p: PropertyKey) -> Option<Key> {
    match p {
        PropertyKey::String(k) => {
            if k.0 < SYMBOL_BIT {
                Some(k)
            } else {
                None
            }
        }
        PropertyKey::Symbol(s) => {
            if s.0 < SYMBOL_BIT {
                Some(Key(s.0 | SYMBOL_BIT))
            } else {
                None
            }
        }
    }
}

/// Y4: the property key a key stands for.
#[must_use]
pub const fn decode(k: Key) -> PropertyKey {
    if k.0 & SYMBOL_BIT == 0 {
        PropertyKey::String(k)
    } else {
        PropertyKey::Symbol(SymbolId(k.0 & !SYMBOL_BIT))
    }
}

/// Y1: the description text of the well-known symbol `id`, or `None` if
/// `id` is not one.
#[must_use]
pub fn well_known_description(id: SymbolId) -> Option<String> {
    let i = usize::try_from(id.0).ok()?;
    WELL_KNOWN.get(i).map(|n| format!("Symbol.{n}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn table_is_thirteen_distinct_names() {
        assert_eq!(WELL_KNOWN.len(), 13);
        assert_eq!(usize::try_from(WELL_KNOWN_COUNT), Ok(WELL_KNOWN.len()));
        for (i, a) in WELL_KNOWN.iter().enumerate() {
            for b in WELL_KNOWN.iter().skip(i.saturating_add(1)) {
                assert_ne!(a, b);
            }
        }
    }

    #[test]
    fn descriptions() {
        assert_eq!(
            well_known_description(SymbolId(3)).as_deref(),
            Some("Symbol.iterator")
        );
        assert_eq!(well_known_description(SymbolId(13)), None);
    }

    #[test]
    fn encoding_edges() {
        let s = PropertyKey::String(Key(SYMBOL_BIT - 1));
        let y = PropertyKey::Symbol(SymbolId(0));
        assert_eq!(encode(s), Some(Key(SYMBOL_BIT - 1)));
        assert_eq!(encode(y), Some(Key(SYMBOL_BIT)));
        assert_eq!(encode(PropertyKey::String(Key(SYMBOL_BIT))), None);
        assert_eq!(encode(PropertyKey::Symbol(SymbolId(SYMBOL_BIT))), None);
        assert_eq!(decode(Key(SYMBOL_BIT)), y);
        assert_eq!(
            decode(Key(u32::MAX)),
            PropertyKey::Symbol(SymbolId(SYMBOL_BIT - 1))
        );
        for p in [s, y, PropertyKey::String(Key(0))] {
            assert_eq!(encode(p).map(decode), Some(p));
        }
    }
}
