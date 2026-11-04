//! One bucket's state in memory, proven to meet [`super::contract`]'s
//! bucket contracts: `get`, `usage` (exactly [`usage`]) and `commit`,
//! which applies a transaction whole when the state it leads to is within
//! the quota and changes nothing otherwise (the note's theorem 4).
//!
//! The entries are an unordered vector with distinct keys, searched
//! linearly; `commit` builds the new state beside the old one (a copy of
//! the bucket per commit, and a pass over it per operation) and swaps it in
//! only once it is admitted. That is enough for Phase 3's small buckets; an
//! ordered index with range scans can replace it under the same contracts.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A key of the state: its bottle and the key's octets.
pub type Key = (nat, Seq<u8>);

/// One stored entry: its key and value.
pub struct Stored {
    /// The bottle's number.
    pub bottle: u32,
    /// The key.
    pub key: Vec<u8>,
    /// The value.
    pub value: Vec<u8>,
}

impl View for Stored {
    type V = (Key, Seq<u8>);

    open spec fn view(&self) -> (Key, Seq<u8>) {
        ((self.bottle as nat, self.key@), self.value@)
    }
}

/// The entries the executable vector stands for.
pub open spec fn stored_view(v: Seq<Stored>) -> Seq<(Key, Seq<u8>)> {
    v.map_values(|e: Stored| e@)
}

/// The state holding the entries `v`, a later one replacing an earlier one
/// with the same key.
pub open spec fn as_state(v: Seq<(Key, Seq<u8>)>) -> State
    decreases v.len(),
{
    if v.len() == 0 {
        Map::empty()
    } else {
        as_state(v.drop_last()).insert(v.last().0, v.last().1)
    }
}

/// No two entries of `v` share a key.
pub open spec fn distinct(v: Seq<(Key, Seq<u8>)>) -> bool
    decreases v.len(),
{
    v.len() == 0 || (distinct(v.drop_last()) && !as_state(v.drop_last()).dom().contains(v.last().0))
}

/// The octets of the keys and values of `v`.
pub open spec fn entries_size(v: Seq<(Key, Seq<u8>)>) -> nat
    decreases v.len(),
{
    if v.len() == 0 {
        0
    } else {
        entries_size(v.drop_last()) + entry_size(v.last().0, v.last().1)
    }
}

/// Whether operation `op` leaves key `k` as it is (a put or delete of
/// another key, a clear of another bottle).
pub open spec fn keeps(k: Key, op: Op) -> bool {
    match op {
        Op::Put { bottle, key, .. } => k != (bottle, key),
        Op::Delete { bottle, key } => k != (bottle, key),
        Op::Clear { bottle } => k.0 != bottle,
    }
}

/// The state `s` without the keys `op` touches.
pub open spec fn without(s: State, op: Op) -> State {
    s.restrict(s.dom().filter(|k: Key| keeps(k, op)))
}

/// The entries of `v` whose keys `op` leaves alone.
pub open spec fn kept(v: Seq<(Key, Seq<u8>)>, op: Op) -> Seq<(Key, Seq<u8>)>
    decreases v.len(),
{
    if v.len() == 0 {
        seq![]
    } else if keeps(v.last().0, op) {
        kept(v.drop_last(), op).push(v.last())
    } else {
        kept(v.drop_last(), op)
    }
}

// ---------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------

/// The keys of `as_state(v)` are the keys of `v`; with distinct keys, each
/// one's value is its entry's.
proof fn lemma_as_state(v: Seq<(Key, Seq<u8>)>)
    ensures
        forall|i: int| 0 <= i < v.len() ==> as_state(v).dom().contains(#[trigger] v[i].0),
        forall|k: Key| as_state(v).dom().contains(k) ==> exists|i: int| 0 <= i < v.len() && #[trigger] v[i].0 == k,
        distinct(v) ==> forall|i: int| 0 <= i < v.len() ==> as_state(v)[#[trigger] v[i].0] == v[i].1,
    decreases v.len(),
{
    if v.len() > 0 {
        let d = v.drop_last();
        lemma_as_state(d);
        assert forall|i: int| 0 <= i < v.len() implies as_state(v).dom().contains(#[trigger] v[i].0) by {
            if i < d.len() {
                assert(v[i] == d[i]);
            }
        }
        assert forall|k: Key| as_state(v).dom().contains(k) implies exists|i: int| 0 <= i < v.len() && #[trigger] v[i].0 == k by {
            if k != v.last().0 {
                assert(as_state(v) == as_state(d).insert(v.last().0, v.last().1));
                assert(as_state(d).dom().contains(k));
                assert(exists|i: int| 0 <= i < d.len() && #[trigger] d[i].0 == k);
                let i = choose|i: int| 0 <= i < d.len() && #[trigger] d[i].0 == k;
                assert(v[i] == d[i]);
                assert(v[i].0 == k);
            } else {
                assert(v[v.len() - 1].0 == k);
            }
        }
        if distinct(v) {
            assert forall|i: int| 0 <= i < v.len() implies as_state(v)[#[trigger] v[i].0] == v[i].1 by {
                if i < d.len() {
                    assert(v[i] == d[i]);
                    assert(as_state(d).dom().contains(d[i].0));
                }
            }
        }
    }
}

/// Usage taken apart at any key: the key's size plus the rest's usage. (So
/// [`usage`] does not depend on the order `choose` takes the keys in.)
pub proof fn lemma_usage_remove(s: State, k: Key)
    requires
        s.dom().contains(k),
    ensures
        usage(s) == entry_size(k, s[k]) + usage(s.remove(k)),
    decreases s.dom().len(),
{
    vstd::set::lemma_set_contains_len(s.dom(), k);
    let c = s.dom().choose();
    vstd::set::lemma_set_choose_len(s.dom());
    if c != k {
        let sc = s.remove(c);
        let sk = s.remove(k);
        assert(sc.dom() =~= s.dom().remove(c));
        assert(sk.dom() =~= s.dom().remove(k));
        vstd::set::lemma_set_remove_len(s.dom(), c);
        vstd::set::lemma_set_remove_len(s.dom(), k);
        assert(sc.dom().contains(k));
        assert(sk.dom().contains(c));
        lemma_usage_remove(sc, k);
        lemma_usage_remove(sk, c);
        assert(sc.remove(k) =~= sk.remove(c));
        assert(sc[k] == s[k]);
        assert(sk[c] == s[c]);
    }
}

/// Adding a new key adds its size.
proof fn lemma_usage_insert(s: State, k: Key, x: Seq<u8>)
    requires
        !s.dom().contains(k),
    ensures
        usage(s.insert(k, x)) == usage(s) + entry_size(k, x),
{
    lemma_usage_remove(s.insert(k, x), k);
    assert(s.insert(k, x).remove(k) =~= s);
}

/// The usage of distinct entries is their size.
proof fn lemma_usage_entries(v: Seq<(Key, Seq<u8>)>)
    requires
        distinct(v),
    ensures
        usage(as_state(v)) == entries_size(v),
    decreases v.len(),
{
    if v.len() == 0 {
        broadcast use vstd::set::lemma_set_empty_len;
        assert(as_state(v).dom() =~= Set::<Key>::empty());
    } else {
        lemma_usage_entries(v.drop_last());
        lemma_usage_insert(as_state(v.drop_last()), v.last().0, v.last().1);
    }
}

/// A prefix's size is no more than the whole's.
proof fn lemma_entries_size_take(v: Seq<(Key, Seq<u8>)>, i: int)
    requires
        0 <= i <= v.len(),
    ensures
        entries_size(v.take(i)) <= entries_size(v),
    decreases v.len() - i,
{
    if i < v.len() {
        lemma_entries_size_take(v, i + 1);
        assert(v.take(i + 1).drop_last() =~= v.take(i));
    } else {
        assert(v.take(i) =~= v);
    }
}

/// Keeping the entries `op` leaves alone gives the state without the keys
/// `op` touches, and keeps the keys distinct.
proof fn lemma_kept(v: Seq<(Key, Seq<u8>)>, op: Op)
    ensures
        as_state(kept(v, op)) == without(as_state(v), op),
        distinct(v) ==> distinct(kept(v, op)),
        forall|k: Key| #[trigger] as_state(kept(v, op)).dom().contains(k) ==> keeps(k, op),
    decreases v.len(),
{
    if v.len() == 0 {
        assert(as_state(v) =~= Map::<Key, Seq<u8>>::empty());
        assert(without(as_state(v), op) =~= Map::<Key, Seq<u8>>::empty());
    } else {
        let d = v.drop_last();
        lemma_kept(d, op);
        let m = as_state(d);
        let e = v.last();
        let w = without(as_state(v), op);
        if keeps(e.0, op) {
            assert(kept(v, op).drop_last() =~= kept(d, op));
            assert(w =~= without(m, op).insert(e.0, e.1));
            if distinct(v) {
                assert(!without(m, op).dom().contains(e.0));
            }
        } else {
            assert(w =~= without(m, op));
        }
    }
}

/// An operation is its keys removed, then a put's key added.
proof fn lemma_apply_op(s: State, op: Op)
    ensures
        apply_op(s, op) == match op {
            Op::Put { bottle, key, value } => without(s, op).insert((bottle, key), value),
            _ => without(s, op),
        },
{
    match op {
        Op::Put { bottle, key, value } => {
            assert(apply_op(s, op) =~= without(s, op).insert((bottle, key), value));
        },
        Op::Delete { bottle, key } => {
            assert(apply_op(s, op) =~= without(s, op));
        },
        Op::Clear { bottle } => {
            assert(apply_op(s, op) =~= without(s, op));
        },
    }
}

// ---------------------------------------------------------------------------
// Executable
// ---------------------------------------------------------------------------

/// A copy of one entry.
fn copy_stored(e: &Stored) -> (out: Stored)
    ensures
        out@ == e@,
{
    let mut key: Vec<u8> = Vec::new();
    key.extend_from_slice(e.key.as_slice());
    let mut value: Vec<u8> = Vec::new();
    value.extend_from_slice(e.value.as_slice());
    assert(key@ =~= e.key@);
    assert(value@ =~= e.value@);
    Stored { bottle: e.bottle, key, value }
}

/// Whether `op` leaves the entry's key alone.
fn keeps_exec(e: &Stored, op: &super::exec::OpRef) -> (r: bool)
    ensures
        r == keeps(e@.0, op@),
{
    match op {
        super::exec::OpRef::Put { bottle, key, .. } => !(e.bottle == *bottle && super::read::same(e.key.as_slice(), key)),
        super::exec::OpRef::Delete { bottle, key } => !(e.bottle == *bottle && super::read::same(e.key.as_slice(), key)),
        super::exec::OpRef::Clear { bottle } => e.bottle != *bottle,
    }
}

/// Copies of the entries of `v` that `op` leaves alone.
fn kept_exec(v: &[Stored], op: &super::exec::OpRef) -> (out: Vec<Stored>)
    ensures
        stored_view(out@) == kept(stored_view(v@), op@),
{
    let ghost sv = stored_view(v@);
    let mut out: Vec<Stored> = Vec::new();
    let mut i: usize = 0;
    assert(sv.take(0) =~= Seq::<(Key, Seq<u8>)>::empty());
    assert(stored_view(out@) =~= kept(sv.take(0), op@));
    while i < v.len()
        invariant
            i <= v.len(),
            sv == stored_view(v@),
            stored_view(out@) == kept(sv.take(i as int), op@),
        ensures
            i == v.len(),
            stored_view(out@) == kept(sv.take(i as int), op@),
        decreases v.len() - i,
    {
        let e = match v.get(i) {
            Some(e) => e,
            None => break,
        };
        let ghost t = sv.take(i as int + 1);
        assert(t.drop_last() =~= sv.take(i as int));
        assert(t.last() == e@);
        if keeps_exec(e, op) {
            let c = copy_stored(e);
            out.push(c);
            assert(stored_view(out@) =~= kept(sv.take(i as int), op@).push(e@));
        }
        // Never saturates: i < v.len().
        i = i.saturating_add(1);
    }
    assert(sv.take(i as int) =~= sv);
    out
}

/// The size of the entries of `v` when it is at most `quota`.
fn size_within(v: &[Stored], quota: u64) -> (r: Option<u64>)
    ensures
        r == if entries_size(stored_view(v@)) <= quota as nat {
            Some(entries_size(stored_view(v@)) as u64)
        } else {
            None::<u64>
        },
{
    let ghost sv = stored_view(v@);
    let mut total: u64 = 0;
    let mut i: usize = 0;
    assert(sv.take(0) =~= Seq::<(Key, Seq<u8>)>::empty());
    while i < v.len()
        invariant
            i <= v.len(),
            sv == stored_view(v@),
            total as nat == entries_size(sv.take(i as int)),
            total <= quota,
        ensures
            i == v.len(),
            total as nat == entries_size(sv.take(i as int)),
            total <= quota,
        decreases v.len() - i,
    {
        let e = match v.get(i) {
            Some(e) => e,
            None => break,
        };
        let ghost t = sv.take(i as int + 1);
        assert(t.drop_last() =~= sv.take(i as int));
        assert(t.last() == e@);
        // total <= quota.
        let room = quota.saturating_sub(total);
        let k = e.key.len() as u64;
        let x = e.value.len() as u64;
        if k > room || x > room.saturating_sub(k) {
            proof {
                lemma_entries_size_take(sv, i as int + 1);
            }
            return None;
        }
        // k + x <= room = quota - total, so neither addition overflows.
        total = total.saturating_add(k).saturating_add(x);
        i = i.saturating_add(1);
    }
    assert(sv.take(i as int) =~= sv);
    Some(total)
}

/// One bucket's entries and their usage.
#[derive(Default)]
pub struct Bucket {
    entries: Vec<Stored>,
    used: u64,
}

impl View for Bucket {
    type V = State;

    closed spec fn view(&self) -> State {
        as_state(stored_view(self.entries@))
    }
}

impl Bucket {
    /// The bucket's invariant: distinct keys, and `used` its usage.
    pub closed spec fn wf(&self) -> bool {
        &&& distinct(stored_view(self.entries@))
        &&& self.used as nat == usage(self@)
    }

    /// An empty bucket.
    pub fn new() -> (b: Bucket)
        ensures
            b.wf(),
            b@ == Map::<Key, Seq<u8>>::empty(),
    {
        let b = Bucket { entries: Vec::new(), used: 0 };
        proof {
            assert(stored_view(b.entries@) =~= Seq::<(Key, Seq<u8>)>::empty());
            lemma_usage_entries(stored_view(b.entries@));
        }
        b
    }

    /// The bucket's usage, in octets.
    pub fn usage(&self) -> (out: u64)
        requires
            self.wf(),
        ensures
            super::contract::bucket_usage_ensures(self@, out as nat),
    {
        self.used
    }

    /// The value of `key` in `bottle`, if it has one.
    pub fn get(&self, bottle: u32, key: &[u8]) -> (out: Option<&[u8]>)
        requires
            self.wf(),
        ensures
            super::contract::bucket_get_ensures(
                self@,
                bottle as nat,
                key@,
                match out {
                    Some(v) => Some(v@),
                    None => None,
                },
            ),
    {
        let ghost sv = stored_view(self.entries@);
        proof {
            lemma_as_state(sv);
        }
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries.len(),
                sv == stored_view(self.entries@),
                distinct(sv),
                forall|j: int| 0 <= j < i ==> #[trigger] sv[j].0 != (bottle as nat, key@),
            decreases self.entries.len() - i,
        {
            let e = self.entries.get(i)?;
            assert(sv[i as int] == e@);
            if e.bottle == bottle && super::read::same(e.key.as_slice(), key) {
                proof {
                    lemma_as_state(sv);
                    assert(sv[i as int].0 == (bottle as nat, key@));
                    assert(self@.dom().contains(sv[i as int].0));
                    assert(self@[sv[i as int].0] == e.value@);
                }
                return Some(e.value.as_slice());
            }
            i = i.saturating_add(1);
        }
        proof {
            lemma_as_state(sv);
            if self@.dom().contains((bottle as nat, key@)) {
                let j = choose|j: int| 0 <= j < sv.len() && #[trigger] sv[j].0 == (bottle as nat, key@);
                assert(sv[j].0 != (bottle as nat, key@));
            }
        }
        None
    }

    /// Commit the transaction `ops` under a quota of `quota` octets: apply
    /// it whole and return `true` when the state it leads to is within the
    /// quota, and otherwise change nothing and return `false`.
    pub fn commit(&mut self, ops: &[super::exec::OpRef], quota: u64) -> (out: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            super::contract::bucket_commit_ensures(old(self)@, super::exec::ops_view(ops@), quota as nat, final(self)@, out),
    {
        let ghost start = self@;
        let ghost view = super::exec::ops_view(ops@);
        // Start from an exact copy of the entries.
        let mut cur: Vec<Stored> = Vec::new();
        let mut j: usize = 0;
        while j < self.entries.len()
            invariant
                j <= self.entries.len(),
                stored_view(cur@) == stored_view(self.entries@).take(j as int),
            ensures
                j == self.entries.len(),
                stored_view(cur@) == stored_view(self.entries@).take(j as int),
            decreases self.entries.len() - j,
        {
            let e = match self.entries.get(j) {
                Some(e) => e,
                None => break,
            };
            let c = copy_stored(e);
            assert(stored_view(self.entries@)[j as int] == e@);
            assert(stored_view(self.entries@).take(j as int + 1) =~= stored_view(self.entries@).take(j as int).push(e@));
            cur.push(c);
            assert(stored_view(cur@) =~= stored_view(self.entries@).take(j as int + 1));
            j = j.saturating_add(1);
        }
        assert(stored_view(self.entries@).take(j as int) =~= stored_view(self.entries@));
        let mut i: usize = 0;
        assert(view.take(0) =~= Seq::<Op>::empty());
        while i < ops.len()
            invariant
                i <= ops.len(),
                view == super::exec::ops_view(ops@),
                distinct(stored_view(cur@)),
                as_state(stored_view(cur@)) == apply_transaction(start, view.take(i as int)),
            ensures
                i == ops.len(),
                distinct(stored_view(cur@)),
                as_state(stored_view(cur@)) == apply_transaction(start, view.take(i as int)),
            decreases ops.len() - i,
        {
            let op = match ops.get(i) {
                Some(op) => op,
                None => break,
            };
            let ghost before = stored_view(cur@);
            let mut next = kept_exec(cur.as_slice(), op);
            proof {
                lemma_kept(before, op@);
                lemma_apply_op(as_state(before), op@);
                let t = view.take(i as int + 1);
                assert(t.drop_last() =~= view.take(i as int));
                assert(t.last() == op@);
            }
            if let super::exec::OpRef::Put { bottle, key, value } = op {
                let mut k: Vec<u8> = Vec::new();
                k.extend_from_slice(key);
                let mut x: Vec<u8> = Vec::new();
                x.extend_from_slice(value);
                assert(k@ =~= key@);
                assert(x@ =~= value@);
                let ghost kept_view = stored_view(next@);
                next.push(Stored { bottle: *bottle, key: k, value: x });
                proof {
                    assert(stored_view(next@) =~= kept_view.push(((*bottle as nat, key@), value@)));
                    assert(stored_view(next@).drop_last() =~= kept_view);
                    assert(!keeps((*bottle as nat, key@), op@));
                }
            }
            cur = next;
            i = i.saturating_add(1);
        }
        assert(view.take(i as int) =~= view);
        proof {
            lemma_usage_entries(stored_view(cur@));
        }
        match size_within(cur.as_slice(), quota) {
            Some(used) => {
                self.entries = cur;
                self.used = used;
                true
            },
            None => false,
        }
    }
}

} // verus!
