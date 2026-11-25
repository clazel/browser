//! The shape property index: tables shared along lines of transitions, so a
//! lookup is a binary search instead of a walk up the parent chain.
//! [`super::contract`] states what it must meet (X1 to X5); the Kani
//! harnesses (`proofs`) and the unit tests check it.

use super::{Attrs, Error};
use crate::string::Key;

/// A table's number in the [`Index`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct TableId(u32);

/// The table of [`super::ROOT`], which is never freed.
pub const ROOT_TABLE: TableId = TableId(0);

/// Binary search of `sorted` (increasing keys) for `key`: `Ok` with its
/// position, or `Err` with the position it would be inserted at. Written
/// out rather than `slice::binary_search_by`, whose closure calls dominate
/// unoptimised and Miri runs, where every lookup of building a runtime is.
pub(crate) fn search(sorted: &[(Key, u32)], key: Key) -> Result<usize, usize> {
    let (mut lo, mut hi) = (0usize, sorted.len());
    // `lo <= at <= hi` for the answer `at`; each step halves `hi - lo`.
    while lo < hi {
        let mid = lo.midpoint(hi);
        let Some(&(k, _)) = sorted.get(mid) else {
            return Err(lo);
        };
        if k.0 < key.0 {
            lo = mid.saturating_add(1);
        } else if k.0 > key.0 {
            hi = mid;
        } else {
            return Ok(mid);
        }
    }
    Err(lo)
}

/// One table: entries in slot order, and their keys sorted (X2).
#[derive(Debug, Default, Clone)]
pub(crate) struct Table {
    /// `(key, attrs)` of slot `i` at index `i`.
    entries: Vec<(Key, Attrs)>,
    /// Every entry's key with its slot, in increasing order of key.
    sorted: Vec<(Key, u32)>,
}

impl Table {
    /// Appends `(key, attrs)` as slot `entries.len()`, unless the table has
    /// `key` already.
    pub(crate) fn push(&mut self, key: Key, attrs: Attrs) -> Result<(), Error> {
        let slot = u32::try_from(self.entries.len()).map_err(|_| Error::TooMany)?;
        match search(&self.sorted, key) {
            Ok(_) => Err(Error::Exists),
            Err(at) => {
                self.sorted.insert(at, (key, slot));
                self.entries.push((key, attrs));
                Ok(())
            }
        }
    }

    /// X3: the slot and attributes of `key` among the first `n` entries.
    pub(crate) fn lookup(&self, n: u32, key: Key) -> Option<(u32, Attrs)> {
        let at = search(&self.sorted, key).ok()?;
        let &(_, slot) = self.sorted.get(at)?;
        if slot >= n {
            return None;
        }
        let &(_, attrs) = self.entries.get(usize::try_from(slot).ok()?)?;
        Some((slot, attrs))
    }

    /// The entries, in slot order.
    pub(crate) fn entries(&self) -> &[(Key, Attrs)] {
        &self.entries
    }

    /// X2 of this table.
    pub(crate) fn well_formed(&self) -> bool {
        super::contract::table_well_formed(&self.entries, &self.sorted)
    }

    /// Keeps the first `n` entries (X5).
    pub(crate) fn truncate(&mut self, n: u32) {
        let keep = usize::try_from(n).unwrap_or(usize::MAX);
        self.entries.truncate(keep);
        self.sorted.retain(|&(_, slot)| slot < n);
    }
}

/// The tables. Table ids are never reused: a freed table is a tombstone.
#[derive(Debug)]
pub struct Index {
    tables: Vec<Option<Table>>,
}

impl Default for Index {
    fn default() -> Self {
        Self::new()
    }
}

impl Index {
    /// An index holding only [`ROOT_TABLE`], empty.
    #[must_use]
    pub fn new() -> Self {
        Self {
            tables: vec![Some(Table::default())],
        }
    }

    fn table(&self, t: TableId) -> Option<&Table> {
        usize::try_from(t.0)
            .ok()
            .and_then(|i| self.tables.get(i))
            .and_then(Option::as_ref)
    }

    fn table_mut(&mut self, t: TableId) -> Option<&mut Table> {
        usize::try_from(t.0)
            .ok()
            .and_then(|i| self.tables.get_mut(i))
            .and_then(Option::as_mut)
    }

    /// X3: the slot and attributes of `key` among the first `n` entries of
    /// table `t`.
    #[must_use]
    pub fn lookup(&self, t: TableId, n: u32, key: Key) -> Option<(u32, Attrs)> {
        self.table(t)?.lookup(n, key)
    }

    /// The first `n` entries of table `t`, in slot order (empty for a freed
    /// table or one shorter than `n`, which X1 rules out for a live shape).
    #[must_use]
    pub fn entries(&self, t: TableId, n: u32) -> &[(Key, Attrs)] {
        let n = usize::try_from(n).unwrap_or(usize::MAX);
        self.table(t)
            .and_then(|table| table.entries().get(..n))
            .unwrap_or(&[])
    }

    /// X4: the table of a shape whose parent has table `t` and slot count
    /// `n` and which adds `(key, attrs)` as slot `n`: `t` itself, appended
    /// to, if `t` has exactly `n` entries; otherwise a new table, a copy of
    /// `t`'s first `n` entries with the new one appended.
    ///
    /// # Errors
    /// [`Error::Unknown`] if `t` is freed or shorter than `n`,
    /// [`Error::Exists`] if `key` is among the first `n` entries,
    /// [`Error::TooMany`] past `u32::MAX` tables or slots.
    pub fn extend(&mut self, t: TableId, n: u32, key: Key, attrs: Attrs) -> Result<TableId, Error> {
        let len = usize::try_from(n).map_err(|_| Error::TooMany)?;
        let table = self.table_mut(t).ok_or(Error::Unknown)?;
        if table.entries.len() == len {
            table.push(key, attrs)?;
            return Ok(t);
        }
        let entries = table.entries.get(..len).ok_or(Error::Unknown)?.to_vec();
        let sorted = table
            .sorted
            .iter()
            .filter(|&&(_, slot)| slot < n)
            .copied()
            .collect();
        let mut copy = Table { entries, sorted };
        copy.push(key, attrs)?;
        let id = TableId(u32::try_from(self.tables.len()).map_err(|_| Error::TooMany)?);
        self.tables.push(Some(copy));
        Ok(id)
    }

    /// X5: given the `(table, slot count)` of every live shared shape, frees
    /// every table but [`ROOT_TABLE`] that none names and shortens every
    /// other to the largest slot count naming it.
    pub fn retain(&mut self, users: &[(TableId, u32)]) {
        let mut longest: Vec<Option<u32>> = vec![None; self.tables.len()];
        for &(t, n) in users {
            if let Some(m) = usize::try_from(t.0).ok().and_then(|i| longest.get_mut(i)) {
                *m = Some(m.map_or(n, |m| m.max(n)));
            }
        }
        for (i, (slot, keep)) in self.tables.iter_mut().zip(longest).enumerate() {
            match keep {
                Some(n) => {
                    if let Some(table) = slot.as_mut() {
                        table.truncate(n);
                    }
                }
                None if i == 0 => {
                    if let Some(table) = slot.as_mut() {
                        table.truncate(0);
                    }
                }
                None => *slot = None,
            }
        }
    }

    /// Whether table `t` exists and is well formed (X2), for the tests and
    /// harnesses.
    #[must_use]
    pub fn well_formed(&self, t: TableId) -> bool {
        self.table(t).is_some_and(Table::well_formed)
    }

    /// The number of tables that are not freed.
    #[must_use]
    pub fn live_tables(&self) -> usize {
        self.tables.iter().filter(|t| t.is_some()).count()
    }
}
