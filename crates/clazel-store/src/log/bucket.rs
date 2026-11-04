//! One bucket's state in memory, proven to meet [`super::contract`]'s
//! bucket contracts: `get`, `usage` (exactly [`usage`]) and `commit`,
//! which applies a transaction whole when the state it leads to is within
//! the quota and changes nothing otherwise (the note's theorem 4).
//!
//! The entries are a vector sorted by bottle and then key, so `get` and the
//! start of a `scan` are binary searches. `commit` builds the new state
//! beside the old one (a copy of the bucket per commit, and a pass over it
//! per operation) and swaps it in only once it is admitted. That is enough
//! for Phase 3's small buckets; a tree can replace the vector under the same
//! contracts.

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

/// The order of entries: by bottle, then by key.
pub open spec fn less(a: Key, b: Key) -> bool {
    a.0 < b.0 || (a.0 == b.0 && key_less(a.1, b.1))
}

/// The entries of `v` strictly increase.
pub open spec fn sorted(v: Seq<(Key, Seq<u8>)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> less(#[trigger] v[i].0, #[trigger] v[j].0)
}

/// The entries as compaction takes them: bottle, key, value.
pub open spec fn as_entries(v: Seq<(Key, Seq<u8>)>) -> Seq<Entry> {
    v.map_values(|e: (Key, Seq<u8>)| (e.0.0, e.0.1, e.1))
}

// ---------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------

/// Compaction's view of the entries is the same state.
proof fn lemma_as_entries(v: Seq<(Key, Seq<u8>)>)
    ensures
        entries_state(as_entries(v)) == as_state(v),
    decreases v.len(),
{
    if v.len() > 0 {
        lemma_as_entries(v.drop_last());
        assert(as_entries(v).drop_last() =~= as_entries(v.drop_last()));
        assert(as_entries(v).last() == (v.last().0.0, v.last().0.1, v.last().1));
    } else {
        assert(as_entries(v) =~= Seq::<Entry>::empty());
    }
}

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

/// No key comes before itself.
proof fn lemma_key_less_irreflexive(a: Seq<u8>)
    ensures
        !key_less(a, a),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_key_less_irreflexive(a.drop_first());
    }
}

/// The order of keys is transitive.
proof fn lemma_key_less_trans(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires
        key_less(a, b),
        key_less(b, c),
    ensures
        key_less(a, c),
    decreases a.len(),
{
    if a.len() > 0 && a[0] == b[0] && b[0] == c[0] {
        lemma_key_less_trans(a.drop_first(), b.drop_first(), c.drop_first());
    }
}

/// Of two different keys, one comes first.
proof fn lemma_key_less_total(a: Seq<u8>, b: Seq<u8>)
    ensures
        a == b || key_less(a, b) || key_less(b, a),
    decreases a.len(),
{
    if a.len() == 0 && b.len() == 0 {
        assert(a =~= b);
    } else if a.len() > 0 && b.len() > 0 && a[0] == b[0] {
        lemma_key_less_total(a.drop_first(), b.drop_first());
        if a.drop_first() == b.drop_first() {
            assert(a =~= seq![a[0]] + a.drop_first());
            assert(b =~= seq![b[0]] + b.drop_first());
        }
    }
}

/// The order of entries is transitive.
proof fn lemma_less_trans(a: Key, b: Key, c: Key)
    requires
        less(a, b),
        less(b, c),
    ensures
        less(a, c),
{
    if a.0 == b.0 && b.0 == c.0 {
        lemma_key_less_trans(a.1, b.1, c.1);
    }
}

/// Strictly increasing entries have distinct keys.
proof fn lemma_sorted_distinct(v: Seq<(Key, Seq<u8>)>)
    requires
        sorted(v),
    ensures
        distinct(v),
    decreases v.len(),
{
    if v.len() > 0 {
        let d = v.drop_last();
        assert forall|i: int, j: int| 0 <= i < j < d.len() implies less(#[trigger] d[i].0, #[trigger] d[j].0) by {
            assert(d[i] == v[i]);
            assert(d[j] == v[j]);
        }
        lemma_sorted_distinct(d);
        lemma_as_state(d);
        if as_state(d).dom().contains(v.last().0) {
            let i = choose|i: int| 0 <= i < d.len() && #[trigger] d[i].0 == v.last().0;
            assert(d[i] == v[i]);
            assert(less(v[i].0, v[v.len() - 1].0));
            lemma_key_less_irreflexive(v.last().0.1);
        }
    }
}

/// Keeping entries keeps them in order.
proof fn lemma_kept_sorted(v: Seq<(Key, Seq<u8>)>, op: Op)
    requires
        sorted(v),
    ensures
        sorted(kept(v, op)),
        forall|i: int|
            0 <= i < kept(v, op).len() ==> exists|j: int| 0 <= j < v.len() && #[trigger] v[j] == #[trigger] kept(v, op)[i],
    decreases v.len(),
{
    if v.len() > 0 {
        let d = v.drop_last();
        assert forall|i: int, j: int| 0 <= i < j < d.len() implies less(#[trigger] d[i].0, #[trigger] d[j].0) by {
            assert(d[i] == v[i]);
            assert(d[j] == v[j]);
        }
        lemma_kept_sorted(d, op);
        let k = kept(d, op);
        assert forall|i: int| #![trigger k[i]] 0 <= i < k.len() implies exists|j: int| 0 <= j < d.len() && j < v.len() - 1 && #[trigger] v[j] == k[i] by {
            let j = choose|j: int| 0 <= j < d.len() && #[trigger] d[j] == k[i];
            assert(d[j] == v[j]);
        }
        if keeps(v.last().0, op) {
            let n = kept(v, op);
            assert(n == k.push(v.last()));
            assert forall|a: int, b: int| 0 <= a < b < n.len() implies less(#[trigger] n[a].0, #[trigger] n[b].0) by {
                assert(n[a] == k[a]);
                let j = choose|j: int| 0 <= j < d.len() && j < v.len() - 1 && #[trigger] v[j] == k[a];
                if b == k.len() {
                    assert(n[b] == v[v.len() - 1]);
                    assert(less(v[j].0, v[v.len() - 1].0));
                } else {
                    assert(n[b] == k[b]);
                }
            }
            assert forall|i: int| 0 <= i < n.len() implies exists|j: int| 0 <= j < v.len() && #[trigger] v[j] == #[trigger] n[i] by {
                if i == k.len() {
                    assert(v[v.len() - 1] == n[i]);
                } else {
                    assert(n[i] == k[i]);
                    let j = choose|j: int| 0 <= j < d.len() && j < v.len() - 1 && #[trigger] v[j] == k[i];
                    assert(v[j] == n[i]);
                }
            }
        } else {
            let n = kept(v, op);
            assert(n == k);
            assert forall|i: int| 0 <= i < n.len() implies exists|j: int| 0 <= j < v.len() && #[trigger] v[j] == #[trigger] n[i] by {
                let j = choose|j: int| 0 <= j < d.len() && j < v.len() - 1 && #[trigger] v[j] == k[i];
                assert(v[j] == n[i]);
            }
        }
    }
}

/// A new key inserted at its place keeps the entries in order, and the state
/// is the old one with the new key.
proof fn lemma_insert_sorted(v: Seq<(Key, Seq<u8>)>, p: int, e: (Key, Seq<u8>))
    requires
        sorted(v),
        0 <= p <= v.len(),
        forall|i: int| 0 <= i < p ==> less(#[trigger] v[i].0, e.0),
        forall|i: int| p <= i < v.len() ==> !less(#[trigger] v[i].0, e.0),
        !as_state(v).dom().contains(e.0),
    ensures
        sorted(v.insert(p, e)),
        as_state(v.insert(p, e)) == as_state(v).insert(e.0, e.1),
{
    let w = v.insert(p, e);
    lemma_as_state(v);
    assert(w.len() == v.len() + 1);
    assert forall|i: int| p <= i < v.len() implies less(e.0, #[trigger] v[i].0) by {
        assert(as_state(v).dom().contains(v[i].0));
        lemma_key_less_total(v[i].0.1, e.0.1);
        assert(!less(v[i].0, e.0));
    }
    assert forall|a: int, b: int| 0 <= a < b < w.len() implies less(#[trigger] w[a].0, #[trigger] w[b].0) by {
        if a < p {
            assert(w[a] == v[a]);
            if b < p {
                assert(w[b] == v[b]);
            } else if b == p {
                assert(w[b] == e);
            } else {
                assert(w[b] == v[b - 1]);
                assert(less(v[a].0, e.0));
                assert(less(e.0, v[b - 1].0));
                lemma_less_trans(v[a].0, e.0, v[b - 1].0);
            }
        } else if a == p {
            assert(w[a] == e);
            assert(w[b] == v[b - 1]);
        } else {
            assert(w[a] == v[a - 1]);
            assert(w[b] == v[b - 1]);
        }
    }
    lemma_sorted_distinct(v);
    lemma_sorted_distinct(w);
    lemma_as_state(w);
    let m = as_state(v).insert(e.0, e.1);
    assert(w[p] == e);
    assert forall|k: Key| #[trigger] as_state(w).dom().contains(k) <==> m.dom().contains(k) by {
        if as_state(w).dom().contains(k) {
            let i = choose|i: int| 0 <= i < w.len() && #[trigger] w[i].0 == k;
            if i < p {
                assert(w[i] == v[i]);
            } else if i > p {
                assert(w[i] == v[i - 1]);
            }
        }
        if m.dom().contains(k) && k != e.0 {
            let i = choose|i: int| 0 <= i < v.len() && #[trigger] v[i].0 == k;
            if i < p {
                assert(w[i] == v[i]);
            } else {
                assert(w[i + 1] == v[i]);
            }
        }
    }
    assert forall|k: Key| #[trigger] m.dom().contains(k) implies as_state(w)[k] == m[k] by {
        if k == e.0 {
            assert(as_state(w)[w[p].0] == w[p].1);
        } else {
            let i = choose|i: int| 0 <= i < v.len() && #[trigger] v[i].0 == k;
            assert(as_state(v)[v[i].0] == v[i].1);
            if i < p {
                assert(w[i] == v[i]);
                assert(as_state(w)[w[i].0] == w[i].1);
            } else {
                assert(w[i + 1] == v[i]);
                assert(as_state(w)[w[i + 1].0] == w[i + 1].1);
            }
        }
    }
    assert(as_state(w) =~= m);
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
pub proof fn lemma_usage_insert(s: State, k: Key, x: Seq<u8>)
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

/// Whether `a` comes before `b` ([`key_less`]).
fn key_less_exec(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == key_less(a@, b@),
{
    let mut i: usize = 0;
    assert(a@.skip(0) =~= a@);
    assert(b@.skip(0) =~= b@);
    loop
        invariant
            i <= a.len(),
            i <= b.len(),
            key_less(a@, b@) == key_less(a@.skip(i as int), b@.skip(i as int)),
        decreases a.len() - i,
    {
        let ghost (x, y) = (a@.skip(i as int), b@.skip(i as int));
        let p = a.get(i);
        let q = b.get(i);
        match (p, q) {
            (None, None) => return false,
            (None, Some(_)) => return true,
            (Some(_), None) => return false,
            (Some(&m), Some(&n)) => {
                assert(x[0] == m && y[0] == n);
                if m != n {
                    return m < n;
                }
                assert(x.drop_first() =~= a@.skip(i as int + 1));
                assert(y.drop_first() =~= b@.skip(i as int + 1));
                // Never saturates: i < a.len().
                i = i.saturating_add(1);
            },
        }
    }
}

/// Whether the entry comes before `(bottle, key)` ([`less`]).
fn less_exec(e: &Stored, bottle: u32, key: &[u8]) -> (r: bool)
    ensures
        r == less(e@.0, (bottle as nat, key@)),
{
    e.bottle < bottle || (e.bottle == bottle && key_less_exec(e.key.as_slice(), key))
}

/// The first index of sorted `v` that does not come before `(bottle, key)`.
fn lower_bound(v: &[Stored], bottle: u32, key: &[u8]) -> (r: usize)
    requires
        sorted(stored_view(v@)),
    ensures
        r <= v.len(),
        forall|i: int| 0 <= i < r ==> less(#[trigger] stored_view(v@)[i].0, (bottle as nat, key@)),
        forall|i: int| r <= i < v.len() ==> !less(#[trigger] stored_view(v@)[i].0, (bottle as nat, key@)),
{
    let ghost sv = stored_view(v@);
    let ghost t = (bottle as nat, key@);
    let mut lo: usize = 0;
    let mut hi: usize = v.len();
    while lo < hi
        invariant
            lo <= hi <= v.len(),
            sv == stored_view(v@),
            sorted(sv),
            t == (bottle as nat, key@),
            forall|i: int| 0 <= i < lo ==> less(#[trigger] sv[i].0, t),
            forall|i: int| hi <= i < v.len() ==> !less(#[trigger] sv[i].0, t),
        decreases hi - lo,
    {
        // lo < hi, so neither step saturates and mid is in [lo, hi).
        let mid = lo.saturating_add(hi.saturating_sub(lo) / 2);
        let e = match v.get(mid) {
            Some(e) => e,
            None => return lo,
        };
        assert(sv[mid as int] == e@);
        if less_exec(e, bottle, key) {
            proof {
                assert forall|i: int| 0 <= i < mid + 1 implies less(#[trigger] sv[i].0, t) by {
                    if i < mid {
                        assert(less(sv[i].0, sv[mid as int].0));
                        lemma_less_trans(sv[i].0, sv[mid as int].0, t);
                    }
                }
            }
            lo = mid.saturating_add(1);
        } else {
            proof {
                assert forall|i: int| mid <= i < v.len() implies !less(#[trigger] sv[i].0, t) by {
                    if i > mid {
                        assert(less(sv[mid as int].0, sv[i].0));
                        if less(sv[i].0, t) {
                            lemma_less_trans(sv[mid as int].0, sv[i].0, t);
                        }
                    }
                }
            }
            hi = mid;
        }
    }
    lo
}

/// The view of an optional upper bound.
pub open spec fn hi_view(hi: Option<&[u8]>) -> Option<Seq<u8>> {
    match hi {
        Some(h) => Some(h@),
        None => None,
    }
}

/// The keys and values a scan returns.
pub open spec fn scan_view(out: Seq<(&[u8], &[u8])>) -> Seq<(Seq<u8>, Seq<u8>)> {
    out.map_values(|p: (&[u8], &[u8])| (p.0@, p.1@))
}

/// Result `k` of a scan begun at index `start` is the entry `k` places on, of
/// the bottle and in the range.
pub open spec fn scan_entry(
    o: Seq<(Seq<u8>, Seq<u8>)>,
    sv: Seq<(Key, Seq<u8>)>,
    start: int,
    k: int,
    b: nat,
    lo: Seq<u8>,
    h: Option<Seq<u8>>,
) -> bool {
    &&& o[k].0 == sv[start + k].0.1
    &&& o[k].1 == sv[start + k].1
    &&& sv[start + k].0.0 == b
    &&& in_range(sv[start + k].0.1, lo, h)
}

/// Entry `e` ends a scan of `bottle` up to `hi`.
pub open spec fn ends_scan(e: (Key, Seq<u8>), bottle: nat, hi: Option<Seq<u8>>) -> bool {
    e.0.0 != bottle || match hi {
        Some(h) => !key_less(e.0.1, h),
        None => false,
    }
}

/// When a scan stopped at `i`, having begun at the lower bound `start` of
/// `lo`, every entry of the bottle in the range lies in `[start, i)`.
proof fn lemma_scan_complete(
    sv: Seq<(Key, Seq<u8>)>,
    bottle: nat,
    lo: Seq<u8>,
    hi: Option<Seq<u8>>,
    start: int,
    i: int,
    j: int,
)
    requires
        sorted(sv),
        0 <= start <= i <= sv.len(),
        forall|m: int| 0 <= m < start ==> less(#[trigger] sv[m].0, (bottle, lo)),
        forall|m: int| start <= m < sv.len() ==> !less(#[trigger] sv[m].0, (bottle, lo)),
        i == sv.len() || ends_scan(sv[i], bottle, hi),
        0 <= j < sv.len(),
        sv[j].0.0 == bottle,
        in_range(sv[j].0.1, lo, hi),
    ensures
        start <= j < i,
{
    if j < start {
        assert(less(sv[j].0, (bottle, lo)));
    }
    if j >= i {
        assert(i < sv.len());
        if j == i {
            assert(!ends_scan(sv[i], bottle, hi));
        } else {
            assert(less(sv[i].0, sv[j].0));
            assert(!less(sv[i].0, (bottle, lo)));
            if sv[i].0.0 == bottle {
                if let Some(h) = hi {
                    lemma_key_less_trans(sv[i].0.1, sv[j].0.1, h);
                }
            }
        }
    }
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
    /// The bucket's invariant: entries in order, and `used` its usage.
    pub closed spec fn wf(&self) -> bool {
        &&& sorted(stored_view(self.entries@))
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
        let ghost t = (bottle as nat, key@);
        let r = lower_bound(self.entries.as_slice(), bottle, key);
        proof {
            lemma_sorted_distinct(sv);
            lemma_as_state(sv);
            lemma_key_less_irreflexive(key@);
        }
        if let Some(e) = self.entries.get(r) {
            assert(sv[r as int] == e@);
            if e.bottle == bottle && super::read::same(e.key.as_slice(), key) {
                proof {
                    assert(sv[r as int].0 == t);
                    assert(self@.dom().contains(sv[r as int].0));
                    assert(self@[sv[r as int].0] == e.value@);
                }
                return Some(e.value.as_slice());
            }
        }
        proof {
            if self@.dom().contains(t) {
                let j = choose|j: int| 0 <= j < sv.len() && #[trigger] sv[j].0 == t;
                if j < r {
                    assert(less(sv[j].0, t));
                } else if j > r {
                    assert(less(sv[r as int].0, sv[j].0));
                    assert(!less(sv[r as int].0, t));
                }
            }
        }
        None
    }

    /// The entries of `bottle` with keys from `lo` up to but not including
    /// `hi` (no upper bound when `hi` is `None`), in key order.
    pub fn scan<'a>(&'a self, bottle: u32, lo: &[u8], hi: Option<&[u8]>) -> (out: Vec<(&'a [u8], &'a [u8])>)
        requires
            self.wf(),
        ensures
            super::contract::bucket_scan_ensures(self@, bottle as nat, lo@, hi_view(hi), scan_view(out@)),
    {
        let ghost sv = stored_view(self.entries@);
        let ghost b = bottle as nat;
        let ghost h = hi_view(hi);
        let start = lower_bound(self.entries.as_slice(), bottle, lo);
        let mut out: Vec<(&'a [u8], &'a [u8])> = Vec::new();
        let mut i = start;
        while i < self.entries.len()
            invariant
                start <= i <= self.entries.len(),
                sv == stored_view(self.entries@),
                sorted(sv),
                b == bottle as nat,
                h == hi_view(hi),
                out@.len() == i - start,
                forall|m: int| start <= m < sv.len() ==> !less(#[trigger] sv[m].0, (b, lo@)),
                forall|k: int|
                    0 <= k < out@.len() ==> #[trigger] scan_entry(scan_view(out@), sv, start as int, k, b, lo@, h),
            ensures
                start <= i <= self.entries.len(),
                out@.len() == i - start,
                i == self.entries.len() || ends_scan(sv[i as int], b, h),
                forall|k: int|
                    0 <= k < out@.len() ==> #[trigger] scan_entry(scan_view(out@), sv, start as int, k, b, lo@, h),
            decreases self.entries.len() - i,
        {
            let e = match self.entries.get(i) {
                Some(e) => e,
                None => break,
            };
            assert(sv[i as int] == e@);
            let past_hi = match hi {
                Some(end) => !key_less_exec(e.key.as_slice(), end),
                None => false,
            };
            if e.bottle != bottle || past_hi {
                break;
            }
            let ghost before = scan_view(out@);
            out.push((e.key.as_slice(), e.value.as_slice()));
            proof {
                assert(!less(sv[i as int].0, (b, lo@)));
                assert(scan_view(out@) =~= before.push((e.key@, e.value@)));
                assert forall|k: int| 0 <= k < out@.len() implies #[trigger] scan_entry(
                    scan_view(out@),
                    sv,
                    start as int,
                    k,
                    b,
                    lo@,
                    h,
                ) by {
                    if k < before.len() {
                        assert(scan_entry(before, sv, start as int, k, b, lo@, h));
                        assert(scan_view(out@)[k] == before[k]);
                    } else {
                        assert(start + k == i);
                        assert(scan_view(out@)[k] == (e.key@, e.value@));
                    }
                }
            }
            // Never saturates: i < self.entries.len().
            i = i.saturating_add(1);
        }
        proof {
            let o = scan_view(out@);
            lemma_sorted_distinct(sv);
            lemma_as_state(sv);
            assert(o.len() == out@.len());
            assert forall|x: int, y: int| 0 <= x < y < o.len() implies key_less(#[trigger] o[x].0, #[trigger] o[y].0) by {
                assert(scan_entry(o, sv, start as int, x, b, lo@, h));
                assert(scan_entry(o, sv, start as int, y, b, lo@, h));
                assert(less(sv[start + x].0, sv[start + y].0));
                lemma_key_less_irreflexive(o[x].0);
            }
            assert forall|x: int| 0 <= x < o.len() implies {
                &&& in_range(#[trigger] o[x].0, lo@, h)
                &&& self@.dom().contains((b, o[x].0))
                &&& self@[(b, o[x].0)] == o[x].1
            } by {
                assert(scan_entry(o, sv, start as int, x, b, lo@, h));
                assert(sv[start + x].0 == (b, o[x].0));
                assert(self@.dom().contains(sv[start + x].0));
                assert(self@[sv[start + x].0] == sv[start + x].1);
            }
            assert forall|k: Seq<u8>| #[trigger] self@.dom().contains((b, k)) && in_range(k, lo@, h) implies exists|x: int|
                0 <= x < o.len() && #[trigger] o[x].0 == k by {
                let j = choose|j: int| 0 <= j < sv.len() && #[trigger] sv[j].0 == (b, k);
                lemma_scan_complete(sv, b, lo@, h, start as int, i as int, j);
                assert(scan_entry(o, sv, start as int, j - start, b, lo@, h));
                assert(o[j - start].0 == k);
            }
        }
        out
    }

    /// The entries, borrowed, as [`super::compact::compact`] takes them.
    pub fn entry_refs(&self) -> (out: Vec<super::compact::EntryRef<'_>>)
        requires
            self.wf(),
        ensures
            entries_state(super::compact::entries_view(out@)) == self@,
    {
        let ghost sv = stored_view(self.entries@);
        let mut out: Vec<super::compact::EntryRef<'_>> = Vec::new();
        let mut i: usize = 0;
        assert(as_entries(sv.take(0)) =~= super::compact::entries_view(out@));
        while i < self.entries.len()
            invariant
                i <= self.entries.len(),
                sv == stored_view(self.entries@),
                super::compact::entries_view(out@) == as_entries(sv.take(i as int)),
            ensures
                i == self.entries.len(),
                super::compact::entries_view(out@) == as_entries(sv.take(i as int)),
            decreases self.entries.len() - i,
        {
            let e = match self.entries.get(i) {
                Some(e) => e,
                None => break,
            };
            out.push(super::compact::EntryRef { bottle: e.bottle, key: e.key.as_slice(), value: e.value.as_slice() });
            proof {
                assert(sv[i as int] == e@);
                assert(as_entries(sv.take(i as int + 1)) =~= as_entries(sv.take(i as int)).push(
                    (e.bottle as nat, e.key@, e.value@),
                ));
                assert(super::compact::entries_view(out@) =~= as_entries(sv.take(i as int + 1)));
            }
            i = i.saturating_add(1);
        }
        proof {
            assert(sv.take(i as int) =~= sv);
            lemma_as_entries(sv);
        }
        out
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
                sorted(stored_view(cur@)),
                as_state(stored_view(cur@)) == apply_transaction(start, view.take(i as int)),
            ensures
                i == ops.len(),
                sorted(stored_view(cur@)),
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
                lemma_kept_sorted(before, op@);
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
                let at = lower_bound(next.as_slice(), *bottle, key);
                next.insert(at, Stored { bottle: *bottle, key: k, value: x });
                proof {
                    let e = ((*bottle as nat, key@), value@);
                    assert(stored_view(next@) =~= kept_view.insert(at as int, e));
                    assert(!keeps(e.0, op@));
                    lemma_insert_sorted(kept_view, at as int, e);
                }
            }
            cur = next;
            i = i.saturating_add(1);
        }
        assert(view.take(i as int) =~= view);
        proof {
            lemma_sorted_distinct(stored_view(cur@));
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
