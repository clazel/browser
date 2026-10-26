//! The exec `step`, proven to meet [`crate::contract::step_ensures`] under
//! [`crate::contract::step_requires`] (and the exec state's own
//! [`StateRecord::exec_wf`]). Each function here is the exec twin of one
//! function of [`crate::spec`], and its `ensures` clause says that it equals
//! it on the views.

use super::fetch::*;
use super::frames::*;
use super::locks::*;
use super::records::*;
#[allow(unused_imports)]
use super::spec::*;
use super::storage::*;
use super::urls::*;
use clazel_cookie::storage::exec::{
    CookieRecord, RequestContextRecord, RequestUrlRecord, evict_expired_exec, is_public_suffix_string_exec,
    retrieve_a_cookie_string_exec, store_a_set_cookie_string_exec,
};
use clazel_fetch::transducer::contract::HttpFnsExec;
use clazel_fetch::transducer::types::{ActionBuf, InputBuf, JarOpBuf};
use clazel_ipc::message::codec::Msg;
use clazel_origin::exec::ParsedOrigin;
use clazel_url::host::record::copy;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The result of a step, viewed as the spec's `(State, Seq<Output>)`.
pub open spec fn result_view(out: (StateRecord, Vec<OutputRecord>)) -> (State, Seq<Output>) {
    (out.0@, outputs_view(out.1@))
}

// ---------------------------------------------------------------------
// Looking renderers up.
// ---------------------------------------------------------------------

/// Skipping renderers that do not have the id does not change [`find_by_id`].
proof fn lemma_find_by_id_skip(rs: Seq<Renderer>, id: nat, i: nat, k: nat)
    requires
        i <= k <= rs.len(),
        forall|j: int| i <= j < k ==> (#[trigger] rs[j]).id != id,
    ensures
        find_by_id(rs, id, i) == find_by_id(rs, id, k),
    decreases k - i,
{
    if i < k {
        lemma_find_by_id_skip(rs, id, i + 1, k);
    }
}

/// Skipping renderers that are not in the tab does not change [`find_by_tab`].
proof fn lemma_find_by_tab_skip(rs: Seq<Renderer>, tab: nat, i: nat, k: nat)
    requires
        i <= k <= rs.len(),
        forall|j: int| i <= j < k ==> (#[trigger] rs[j]).tab != tab,
    ensures
        find_by_tab(rs, tab, i) == find_by_tab(rs, tab, k),
    decreases k - i,
{
    if i < k {
        lemma_find_by_tab_skip(rs, tab, i + 1, k);
    }
}

/// [`find_by_id`] from the start.
pub fn find_by_id_exec(rs: &[RendererRecord], id: u64) -> (r: Option<usize>)
    ensures
        match r {
            Some(k) => k < rs.len() && find_by_id(renderers_view(rs@), id as nat, 0) == Some(k as int),
            None => find_by_id(renderers_view(rs@), id as nat, 0) == None::<int>,
        },
{
    let ghost rv = renderers_view(rs@);
    let mut i: usize = 0;
    while i < rs.len()
        invariant
            i <= rs.len(),
            rv == renderers_view(rs@),
            forall|j: int| 0 <= j < i ==> (#[trigger] rv[j]).id != id as nat,
        decreases rs.len() - i,
    {
        if let Some(r) = rs.get(i) {
            proof {
                assert(rv[i as int] == rs@[i as int]@);
            }
            if r.id == id {
                proof {
                    lemma_find_by_id_skip(rv, id as nat, 0, i as nat);
                }
                return Some(i);
            }
        }
        // Never saturates: i < rs.len().
        i = i.saturating_add(1);
    }
    proof {
        lemma_find_by_id_skip(rv, id as nat, 0, rs.len() as nat);
    }
    None
}

/// [`find_by_tab`] from the start.
pub fn find_by_tab_exec(rs: &[RendererRecord], tab: u64) -> (r: Option<usize>)
    ensures
        match r {
            Some(k) => k < rs.len() && find_by_tab(renderers_view(rs@), tab as nat, 0) == Some(k as int),
            None => find_by_tab(renderers_view(rs@), tab as nat, 0) == None::<int>,
        },
{
    let ghost rv = renderers_view(rs@);
    let mut i: usize = 0;
    while i < rs.len()
        invariant
            i <= rs.len(),
            rv == renderers_view(rs@),
            forall|j: int| 0 <= j < i ==> (#[trigger] rv[j]).tab != tab as nat,
        decreases rs.len() - i,
    {
        if let Some(r) = rs.get(i) {
            proof {
                assert(rv[i as int] == rs@[i as int]@);
            }
            if r.tab == tab {
                proof {
                    lemma_find_by_tab_skip(rv, tab as nat, 0, i as nat);
                }
                return Some(i);
            }
        }
        // Never saturates: i < rs.len().
        i = i.saturating_add(1);
    }
    proof {
        lemma_find_by_tab_skip(rv, tab as nat, 0, rs.len() as nat);
    }
    None
}

/// A copy of renderer `i` without its navigation: the transducer's parser
/// cannot be copied, and the functions that read a renderer by value (the
/// handling of a message, the commit) never read it.
pub fn renderer_at(rs: &[RendererRecord], i: usize) -> (r: RendererRecord)
    requires
        i < rs.len(),
    ensures
        r@ == (Renderer { pending: None, ..renderers_view(rs@)[i as int] }),
        r.pending is None,
{
    match rs.get(i) {
        Some(r) => RendererRecord { id: r.id, tab: r.tab, url: copy(r.url.as_slice()), lock: clone_origin(&r.lock), pending: None },
        None => RendererRecord { id: 0, tab: 0, url: Vec::new(), lock: ParsedOrigin::Opaque(0), pending: None },
    }
}

/// Every navigation in flight in the table keeps the parser invariant of `h`
/// ([`StateRecord::exec_wf`]).
pub open spec fn renderers_ok<F: FetchFnsExec>(rs: Seq<RendererRecord>) -> bool {
    forall|i: int|
        0 <= i < rs.len() ==> match #[trigger] rs[i].pending {
            Some(n) => F::nav_ok(&n.fetch),
            None => true,
        }
}

/// Replacing a renderer by one that is not navigating keeps the invariant.
pub proof fn lemma_ok_set_idle<F: FetchFnsExec>(rs: Seq<RendererRecord>, i: int, r: RendererRecord)
    requires
        renderers_ok::<F>(rs),
        0 <= i < rs.len(),
        r.pending is None,
    ensures
        renderers_ok::<F>(rs.update(i, r)),
{
    assert forall|j: int| 0 <= j < rs.update(i, r).len() implies match #[trigger] rs.update(i, r)[j].pending {
        Some(n) => F::nav_ok(&n.fetch),
        None => true,
    } by {
        if j != i {
            assert(rs.update(i, r)[j] == rs[j]);
        }
    }
}

/// Removing a renderer keeps the invariant.
pub proof fn lemma_ok_remove<F: FetchFnsExec>(rs: Seq<RendererRecord>, i: int)
    requires
        renderers_ok::<F>(rs),
        0 <= i < rs.len(),
    ensures
        renderers_ok::<F>(rs.remove(i)),
{
    assert forall|j: int| 0 <= j < rs.remove(i).len() implies match #[trigger] rs.remove(i)[j].pending {
        Some(n) => F::nav_ok(&n.fetch),
        None => true,
    } by {
        assert(rs.remove(i)[j] == rs[if j < i { j } else { j + 1 }]);
    }
}

/// Adding an idle renderer keeps the invariant.
pub proof fn lemma_ok_push_idle<F: FetchFnsExec>(rs: Seq<RendererRecord>, r: RendererRecord)
    requires
        renderers_ok::<F>(rs),
        r.pending is None,
    ensures
        renderers_ok::<F>(rs.push(r)),
{
    assert forall|j: int| 0 <= j < rs.push(r).len() implies match #[trigger] rs.push(r)[j].pending {
        Some(n) => F::nav_ok(&n.fetch),
        None => true,
    } by {
        if j < rs.len() {
            assert(rs.push(r)[j] == rs[j]);
        }
    }
}

/// Putting back, at index `i`, a renderer whose navigation is in order
/// keeps the invariant of the table without it.
pub proof fn lemma_ok_insert<F: FetchFnsExec>(rs: Seq<RendererRecord>, i: int, r: RendererRecord)
    requires
        renderers_ok::<F>(rs),
        0 <= i <= rs.len(),
        match r.pending {
            Some(n) => F::nav_ok(&n.fetch),
            None => true,
        },
    ensures
        renderers_ok::<F>(rs.insert(i, r)),
{
    assert forall|j: int| 0 <= j < rs.insert(i, r).len() implies match #[trigger] rs.insert(i, r)[j].pending {
        Some(n) => F::nav_ok(&n.fetch),
        None => true,
    } by {
        if j < i {
            assert(rs.insert(i, r)[j] == rs[j]);
        } else if j > i {
            assert(rs.insert(i, r)[j] == rs[j - 1]);
        }
    }
}

/// Taking renderer `i` out and putting back `r` in its place is an update
/// of the view.
pub proof fn lemma_renderers_view_replace(v: Seq<RendererRecord>, i: int, r: RendererRecord)
    requires
        0 <= i < v.len(),
    ensures
        renderers_view(v.remove(i).insert(i, r)) =~= renderers_view(v).update(i, r@),
{
    assert(v.remove(i).insert(i, r).len() == v.len());
    assert forall|j: int| 0 <= j < v.len() implies renderers_view(v.remove(i).insert(i, r))[j] == renderers_view(v).update(i, r@)[j] by {
        if j < i {
            assert(v.remove(i).insert(i, r)[j] == v[j]);
        } else if j > i {
            assert(v.remove(i).insert(i, r)[j] == v.remove(i)[j - 1]);
            assert(v.remove(i)[j - 1] == v[j]);
        }
    }
}

// ---------------------------------------------------------------------
// Outputs.
// ---------------------------------------------------------------------

/// [`reply`]: a `ToRenderer` of the frame of `m` to renderer `r`.
pub fn reply_exec(r: &RendererRecord, m: &Msg) -> (out: Vec<OutputRecord>)
    ensures
        outputs_view(out@) == reply(r@, m@),
{
    let bytes = reply_frame_exec(m);
    one_output(OutputRecord::ToRenderer { id: r.id, bytes })
}

/// The three outputs of a spawn.
fn three_outputs(a: OutputRecord, b: OutputRecord, c: OutputRecord) -> (v: Vec<OutputRecord>)
    ensures
        outputs_view(v@) == seq![a@, b@, c@],
{
    let ghost (ga, gb, gc) = (a@, b@, c@);
    let v = vec![a, b, c];
    assert(outputs_view(v@) =~= seq![ga, gb, gc]);
    v
}

/// The two outputs of a spawn without a kill.
fn two_outputs(a: OutputRecord, b: OutputRecord) -> (v: Vec<OutputRecord>)
    ensures
        outputs_view(v@) == seq![a@, b@],
{
    let ghost (ga, gb) = (a@, b@);
    let v = vec![a, b];
    assert(outputs_view(v@) =~= seq![ga, gb]);
    v
}

// ---------------------------------------------------------------------
// Web Storage calls.
// ---------------------------------------------------------------------

/// The message a read-only storage call replies with, as a function of the
/// map.
pub open spec fn read_reply(list: Seq<StorageEntry>, m: clazel_ipc::message::spec::Message) -> clazel_ipc::message::spec::Message {
    match m {
        clazel_ipc::message::spec::Message::StorageGetItem { key } => clazel_ipc::message::spec::Message::StorageValue {
            value: match find_key(list, key, 0) {
                None => None,
                Some(i) => Some(list[i].value),
            },
        },
        clazel_ipc::message::spec::Message::StorageKey { index } => clazel_ipc::message::spec::Message::StorageValue {
            value: if index as int >= list.len() {
                None
            } else {
                Some(list[index as int].key)
            },
        },
        _ => clazel_ipc::message::spec::Message::StorageLengthValue { length: list.len() as u64 },
    }
}

/// A read-only storage call.
pub open spec fn is_read(m: clazel_ipc::message::spec::Message) -> bool {
    m is StorageGetItem || m is StorageKey || m is StorageLength
}

/// The reply to a read-only storage call over a list.
pub fn read_reply_exec(list: &[StorageEntryRecord], m: &Msg) -> (out: Msg)
    requires
        is_read(m@),
    ensures
        out@ == read_reply(entries_view(list@), m@),
{
    match m {
        Msg::StorageGetItem { key } => {
            let found = find_key_exec(list, key.as_slice());
            let value = match found {
                None => None,
                Some(k) => match list.get(k) {
                    Some(e) => Some(vstd::slice::slice_to_vec(e.value.as_slice())),
                    None => None,
                },
            };
            proof {
                if let Some(k) = found {
                    assert(entries_view(list@)[k as int] == list@[k as int]@);
                }
            }
            Msg::StorageValue { value }
        },
        Msg::StorageKey { index } => {
            let value = if *index >= list.len() as u64 {
                None
            } else {
                match list.get(*index as usize) {
                    Some(e) => Some(vstd::slice::slice_to_vec(e.key.as_slice())),
                    None => None,
                }
            };
            Msg::StorageValue { value }
        },
        _ => Msg::StorageLengthValue { length: list.len() as u64 },
    }
}

/// A read-only call is answered from the list and changes nothing.
proof fn lemma_storage_call_read(s: State, r: Renderer, m: clazel_ipc::message::spec::Message)
    requires
        is_read(m),
    ensures
        storage_call(s, r, m) == (s, reply(r, read_reply(list_in(s.storage, r.lock), m))),
{
    assert(storage_of(s, r.lock) == list_in(s.storage, r.lock));
}

/// `setItem` as a function of the map.
proof fn lemma_storage_call_set(s: State, r: Renderer, key: Seq<u8>, value: Seq<u8>)
    ensures
        storage_call(s, r, clazel_ipc::message::spec::Message::StorageSetItem { key, value }) == ({
            let (m2, q) = set_item_map(s.storage, r.lock, key, value);
            (
                State { storage: m2, ..s },
                if q {
                    reply(r, clazel_ipc::message::spec::Message::Error { code: error_quota() })
                } else {
                    seq![]
                },
            )
        }),
{
    assert(storage_of(s, r.lock) == list_in(s.storage, r.lock));
    let list = list_in(s.storage, r.lock);
    match find_key(list, key, 0) {
        Some(i) => {
            if list[i].value != value {
                let new_list = list.update(i, StorageEntry { key, value });
                assert(set_storage(s, r.lock, new_list) == State { storage: set_map(s.storage, r.lock, new_list), ..s });
            }
        },
        None => {
            let new_list = list.push(StorageEntry { key, value });
            assert(set_storage(s, r.lock, new_list) == State { storage: set_map(s.storage, r.lock, new_list), ..s });
        },
    }
}

/// `removeItem` as a function of the map.
proof fn lemma_storage_call_remove(s: State, r: Renderer, key: Seq<u8>)
    ensures
        storage_call(s, r, clazel_ipc::message::spec::Message::StorageRemoveItem { key }) == (
            State { storage: remove_item_map(s.storage, r.lock, key), ..s },
            Seq::<Output>::empty(),
        ),
{
    assert(storage_of(s, r.lock) == list_in(s.storage, r.lock));
    let list = list_in(s.storage, r.lock);
    match find_key(list, key, 0) {
        Some(i) => {
            assert(set_storage(s, r.lock, list.remove(i)) == State { storage: set_map(s.storage, r.lock, list.remove(i)), ..s });
        },
        None => {},
    }
}

/// `clear` as a function of the map.
proof fn lemma_storage_call_clear(s: State, r: Renderer)
    ensures
        storage_call(s, r, clazel_ipc::message::spec::Message::StorageClear) == (
            State { storage: set_map(s.storage, r.lock, Seq::empty()), ..s },
            Seq::<Output>::empty(),
        ),
{
}

/// A `localStorage` call by renderer `r` on a tuple lock ([`storage_call`]).
pub fn storage_call_exec(s: StateRecord, r: &RendererRecord, m: &Msg) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        buckets_wf(s.storage@),
        crate::invariant::storage_wf(s@.storage),
    ensures
        result_view(out) == storage_call(s@, r@, m@),
        buckets_wf(out.0.storage@),
        out.0.renderers@ == s.renderers@,
        out.0.jar@ == s.jar@,
        out.0.next_id == s.next_id,
        out.0.conns@ == s.conns@,
        out.0.next_conn == s.next_conn,
        out.0.now == s.now,
{
    let ghost sv = s@;
    match m {
        Msg::StorageGetItem { .. } | Msg::StorageKey { .. } | Msg::StorageLength => {
            let idx = find_bucket(s.storage.as_slice(), &r.lock);
            proof {
                lemma_list_in_bucket(s.storage@, r.lock@, idx);
                lemma_storage_call_read(sv, r@, m@);
            }
            let empty: Vec<StorageEntryRecord> = Vec::new();
            let list: &[StorageEntryRecord] = match idx {
                Some(b) => match s.storage.get(b) {
                    Some(bucket) => bucket.entries.as_slice(),
                    None => empty.as_slice(),
                },
                None => empty.as_slice(),
            };
            proof {
                assert(entries_view(list@) == list_in(sv.storage, r@.lock));
            }
            let reply_msg = read_reply_exec(list, m);
            let outs = reply_exec(r, &reply_msg);
            (s, outs)
        },
        Msg::StorageSetItem { key, value } => {
            let mut s = s;
            proof {
                lemma_buckets_quota(s.storage@);
                lemma_storage_call_set(sv, r@, key@, value@);
            }
            let quota = set_item_exec(&mut s.storage, &r.lock, key.as_slice(), value.as_slice());
            if quota {
                let e = Msg::Error { code: 2 };
                let outs = reply_exec(r, &e);
                (s, outs)
            } else {
                (s, no_outputs())
            }
        },
        Msg::StorageRemoveItem { key } => {
            let mut s = s;
            proof {
                lemma_storage_call_remove(sv, r@, key@);
            }
            remove_item_exec(&mut s.storage, &r.lock, key.as_slice());
            (s, no_outputs())
        },
        Msg::StorageClear => {
            let mut s = s;
            proof {
                lemma_storage_call_clear(sv, r@);
            }
            clear_exec(&mut s.storage, &r.lock);
            (s, no_outputs())
        },
        _ => (s, no_outputs()),
    }
}

// ---------------------------------------------------------------------
// Connections.
// ---------------------------------------------------------------------

/// The facts a step that leaves storage, jar and time alone gives about its
/// result.
pub open spec fn keeps_storage_jar_now(before: StateRecord, after: StateRecord) -> bool {
    &&& after.storage@ == before.storage@
    &&& after.jar@ == before.jar@
    &&& after.now == before.now
}

/// The facts a step that leaves the connections alone gives about its
/// result.
pub open spec fn keeps_conns(before: StateRecord, after: StateRecord) -> bool {
    &&& after.conns@ == before.conns@
    &&& after.next_conn == before.next_conn
}

/// The number of connection ids a step may use: the transducer's budget of
/// `Connect`s for a fetch (`start` gives one, a step gives at most 20).
pub open spec fn conn_headroom() -> nat {
    21
}

/// The `Close`s of `closes_of_tab` over a concatenation.
proof fn lemma_closes_concat(a: Seq<Connection>, b: Seq<Connection>, tab: nat)
    ensures
        closes_of_tab(a + b, tab) == closes_of_tab(a, tab) + closes_of_tab(b, tab),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
        assert(closes_of_tab(a, tab) =~= Seq::<Output>::empty());
    } else {
        let rest = a.drop_first();
        lemma_closes_concat(rest, b, tab);
        assert((a + b).drop_first() =~= rest + b);
        assert((a + b)[0] == a[0]);
        let first = if a[0].tab == tab {
            seq![Output::Close { conn: a[0].id }]
        } else {
            seq![]
        };
        assert(closes_of_tab(a + b, tab) =~= first + closes_of_tab(rest + b, tab));
        assert(closes_of_tab(a, tab) =~= first + closes_of_tab(rest, tab));
        assert(closes_of_tab(a + b, tab) =~= closes_of_tab(a, tab) + closes_of_tab(b, tab));
    }
}

/// [`closes_of_tab`].
pub fn closes_of_tab_exec(conns: &[ConnectionRecord], tab: u64) -> (out: Vec<OutputRecord>)
    ensures
        outputs_view(out@) == closes_of_tab(conns_view(conns@), tab as nat),
{
    let ghost cv = conns_view(conns@);
    let mut out: Vec<OutputRecord> = Vec::new();
    let mut k: usize = 0;
    proof {
        assert(cv.take(0) =~= Seq::<Connection>::empty());
        assert(closes_of_tab(Seq::<Connection>::empty(), tab as nat) =~= Seq::<Output>::empty());
    }
    while k < conns.len()
        invariant
            k <= conns.len(),
            cv == conns_view(conns@),
            outputs_view(out@) == closes_of_tab(cv.take(k as int), tab as nat),
        decreases conns.len() - k,
    {
        if let Some(c) = conns.get(k) {
            proof {
                assert(cv[k as int] == c@);
                assert(cv.take(k as int + 1) =~= cv.take(k as int) + seq![c@]);
                lemma_closes_concat(cv.take(k as int), seq![c@], tab as nat);
                assert(seq![c@].drop_first() =~= Seq::<Connection>::empty());
                assert(closes_of_tab(Seq::<Connection>::empty(), tab as nat) =~= Seq::<Output>::empty());
            }
            if c.tab == tab {
                let ghost before = out@;
                out.push(OutputRecord::Close { conn: c.id });
                proof {
                    lemma_outputs_view_push(before, OutputRecord::Close { conn: c.id });
                    assert(closes_of_tab(seq![c@], tab as nat) =~= seq![Output::Close { conn: c.id as nat }]);
                    assert(closes_of_tab(cv.take(k as int + 1), tab as nat) =~= closes_of_tab(cv.take(k as int), tab as nat) + seq![Output::Close { conn: c.id as nat }]);
                }
            } else {
                proof {
                    assert(closes_of_tab(seq![c@], tab as nat) =~= Seq::<Output>::empty());
                    assert(closes_of_tab(cv.take(k as int + 1), tab as nat) =~= closes_of_tab(cv.take(k as int), tab as nat));
                }
            }
        }
        // Never saturates: k < conns.len().
        k = k.saturating_add(1);
    }
    proof {
        assert(cv.take(conns.len() as int) =~= cv);
    }
    out
}

/// [`close_tab_conns`]: every connection of the tab is closed.
pub fn close_tab_conns_exec(s: StateRecord, tab: u64) -> (out: (StateRecord, Vec<OutputRecord>))
    ensures
        result_view(out) == close_tab_conns(s@, tab as nat),
        out.0.renderers@ == s.renderers@,
        out.0.storage@ == s.storage@,
        out.0.jar@ == s.jar@,
        out.0.next_id == s.next_id,
        out.0.next_conn == s.next_conn,
        out.0.now == s.now,
{
    let outs = closes_of_tab_exec(s.conns.as_slice(), tab);
    let conns = without_tab_exec(s.conns.as_slice(), tab);
    let mut s = s;
    s.conns = conns;
    (s, outs)
}

/// Skipping connections that do not have the id does not change [`find_conn`].
proof fn lemma_find_conn_skip(cs: Seq<Connection>, id: nat, i: nat, k: nat)
    requires
        i <= k <= cs.len(),
        forall|j: int| i <= j < k ==> (#[trigger] cs[j]).id != id,
    ensures
        find_conn(cs, id, i) == find_conn(cs, id, k),
    decreases k - i,
{
    if i < k {
        lemma_find_conn_skip(cs, id, i + 1, k);
    }
}

/// [`find_conn`] from the start.
pub fn find_conn_exec(cs: &[ConnectionRecord], id: u64) -> (r: Option<usize>)
    ensures
        match r {
            Some(k) => k < cs.len() && find_conn(conns_view(cs@), id as nat, 0) == Some(k as int),
            None => find_conn(conns_view(cs@), id as nat, 0) == None::<int>,
        },
{
    let ghost cv = conns_view(cs@);
    let mut i: usize = 0;
    while i < cs.len()
        invariant
            i <= cs.len(),
            cv == conns_view(cs@),
            forall|j: int| 0 <= j < i ==> (#[trigger] cv[j]).id != id as nat,
        decreases cs.len() - i,
    {
        if let Some(c) = cs.get(i) {
            proof {
                assert(cv[i as int] == cs@[i as int]@);
            }
            if c.id == id {
                proof {
                    lemma_find_conn_skip(cv, id as nat, 0, i as nat);
                }
                return Some(i);
            }
        }
        // Never saturates: i < cs.len().
        i = i.saturating_add(1);
    }
    proof {
        lemma_find_conn_skip(cv, id as nat, 0, cs.len() as nat);
    }
    None
}

/// [`open_connection`]: a new connection for a transducer `Connect`.
pub fn open_connection_exec(s: StateRecord, tab: u64, partition: &DomainRecord, endpoint: EndpointRecord) -> (out: (
    StateRecord,
    u64,
    Vec<OutputRecord>,
))
    requires
        s.next_conn < 0xFFFF_FFFF_FFFF_FFFFu64,
    ensures
        (out.0@, out.1 as nat, outputs_view(out.2@)) == open_connection(s@, tab as nat, partition@, endpoint@),
        out.0.renderers@ == s.renderers@,
        keeps_storage_jar_now(s, out.0),
        out.0.next_id == s.next_id,
        out.0.next_conn == s.next_conn + 1,
{
    let id = s.next_conn;
    let host = vstd::slice::slice_to_vec(endpoint.host.as_slice());
    let port = endpoint.port;
    let tls = endpoint.tls;
    let ghost ev = endpoint@;
    let mut s = s;
    let ghost old_conns = s.conns@;
    let rec = ConnectionRecord { id, tab, endpoint, partition: clone_domain(partition) };
    s.conns.push(rec);
    s.next_conn = id.saturating_add(1);
    proof {
        lemma_conns_view_push(old_conns, rec);
        assert(rec@ == Connection { id: id as nat, tab: tab as nat, endpoint: ev, partition: partition@ });
    }
    let outs = one_output(OutputRecord::Connect { conn: id, host, port, tls });
    (s, id, outs)
}

// ---------------------------------------------------------------------
// Navigation.
// ---------------------------------------------------------------------

/// [`navigate_tab`]: the renderer of tab `tab` commits the document at `url`.
pub fn navigate_tab_exec<U: UrlFnsExec, F: FetchFnsExec>(urls: &U, s: StateRecord, tab: u64, url: &[u32], script: &[u8]) -> (out: (
    StateRecord,
    Vec<OutputRecord>,
))
    requires
        s.next_id < 0xFFFF_FFFF_FFFF_FFFFu64,
        clazel_encoding::utf8::spec::all_scalar_values(url@),
        renderers_ok::<F>(s.renderers@),
    ensures
        result_view(out) == navigate_tab(urls.urls(), s@, tab as nat, url@, script@),
        keeps_storage_jar_now(s, out.0),
        keeps_conns(s, out.0),
        out.0.next_id <= s.next_id + 1,
        renderers_ok::<F>(out.0.renderers@),
{
    let ghost sv = s@;
    match find_by_tab_exec(s.renderers.as_slice(), tab) {
        None => (s, no_outputs()),
        Some(i) => {
            let old = renderer_at(s.renderers.as_slice(), i);
            let ghost ov = old@;
            match lock_of_url_exec(urls, url, s.next_id) {
                None => (s, no_outputs()),
                Some(lock) => {
                    let same = match lock {
                        ParsedOrigin::Tuple { .. } => origin_eq_exec(&lock, &old.lock),
                        ParsedOrigin::Opaque(_) => false,
                    };
                    let frame = commit_frame_exec(url, script);
                    let mut s = s;
                    if same {
                        let ghost old_renderers = s.renderers@;
                        let rec = RendererRecord { id: old.id, tab: old.tab, url: copy(url), lock: old.lock, pending: None };
                        let ghost rv = rec@;
                        s.renderers.set(i, rec);
                        proof {
                            lemma_renderers_view_update(old_renderers, i as int, rec);
                            lemma_ok_set_idle::<F>(old_renderers, i as int, rec);
                        }
                        let outs = one_output(OutputRecord::ToRenderer { id: old.id, bytes: frame });
                        (s, outs)
                    } else {
                        let id = s.next_id;
                        let ghost old_renderers = s.renderers@;
                        let rec = RendererRecord { id, tab, url: copy(url), lock, pending: None };
                        s.renderers.set(i, rec);
                        proof {
                            lemma_renderers_view_update(old_renderers, i as int, rec);
                            lemma_ok_set_idle::<F>(old_renderers, i as int, rec);
                        }
                        s.next_id = id.saturating_add(1);
                        let outs = three_outputs(
                            OutputRecord::Kill { id: old.id },
                            OutputRecord::Spawn { id },
                            OutputRecord::ToRenderer { id, bytes: frame },
                        );
                        (s, outs)
                    }
                },
            }
        },
    }
}

/// [`open_tab`]: a new tab with a new renderer.
pub fn open_tab_exec<U: UrlFnsExec, F: FetchFnsExec>(urls: &U, s: StateRecord, url: &[u32], script: &[u8]) -> (out: (
    StateRecord,
    Vec<OutputRecord>,
))
    requires
        s.next_id < 0xFFFF_FFFF_FFFF_FFFFu64,
        clazel_encoding::utf8::spec::all_scalar_values(url@),
        renderers_ok::<F>(s.renderers@),
    ensures
        result_view(out) == open_tab(urls.urls(), s@, url@, script@),
        keeps_storage_jar_now(s, out.0),
        keeps_conns(s, out.0),
        out.0.next_id <= s.next_id + 1,
        renderers_ok::<F>(out.0.renderers@),
{
    let id = s.next_id;
    match lock_of_url_exec(urls, url, id) {
        None => (s, no_outputs()),
        Some(lock) => {
            let frame = commit_frame_exec(url, script);
            let mut s = s;
            let ghost old_renderers = s.renderers@;
            let rec = RendererRecord { id, tab: id, url: copy(url), lock, pending: None };
            s.renderers.push(rec);
            proof {
                lemma_renderers_view_push(old_renderers, rec);
                lemma_ok_push_idle::<F>(old_renderers, rec);
            }
            s.next_id = id.saturating_add(1);
            let outs = two_outputs(OutputRecord::Spawn { id }, OutputRecord::ToRenderer { id, bytes: frame });
            (s, outs)
        },
    }
}

/// [`fail_navigation`]: the navigation of the renderer at index `i` ends
/// without a commit: it stays, no longer navigating, and is sent an `Error`.
pub fn fail_navigation_exec<F: FetchFnsExec>(s: StateRecord, i: usize, code: u64) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        i < s.renderers.len(),
        renderers_ok::<F>(s.renderers@),
    ensures
        result_view(out) == fail_navigation(s@, i as int, s@.renderers[i as int], code),
        keeps_storage_jar_now(s, out.0),
        keeps_conns(s, out.0),
        out.0.next_id == s.next_id,
        renderers_ok::<F>(out.0.renderers@),
{
    let old = renderer_at(s.renderers.as_slice(), i);
    let mut s = s;
    let ghost old_renderers = s.renderers@;
    let rec = RendererRecord { id: old.id, tab: old.tab, url: copy(old.url.as_slice()), lock: clone_origin(&old.lock), pending: None };
    let e = Msg::Error { code };
    let outs = reply_exec(&old, &e);
    s.renderers.set(i, rec);
    proof {
        lemma_renderers_view_update(old_renderers, i as int, rec);
        lemma_ok_set_idle::<F>(old_renderers, i as int, rec);
    }
    (s, outs)
}

/// [`commit_navigation`]: the navigation of `tab` ends with the document at
/// `href` and the response's `body`.
pub fn commit_navigation_exec<U: UrlFnsExec, F: FetchFnsExec>(urls: &U, s: StateRecord, tab: u64, href: &[u32], body: &[u8]) -> (out: (
    StateRecord,
    Vec<OutputRecord>,
))
    requires
        s.next_id < 0xFFFF_FFFF_FFFF_FFFFu64,
        renderers_ok::<F>(s.renderers@),
    ensures
        result_view(out) == commit_navigation(urls.urls(), s@, tab as nat, href@, body@),
        keeps_storage_jar_now(s, out.0),
        out.0.next_conn == s.next_conn,
        out.0.next_id <= s.next_id + 1,
        renderers_ok::<F>(out.0.renderers@),
{
    let (s1, closes) = close_tab_conns_exec(s, tab);
    match find_by_tab_exec(s1.renderers.as_slice(), tab) {
        None => (s1, closes),
        Some(i) => {
            proof {
                crate::invariant::lemma_scalar_url(href@);
            }
            let (s2, out) = if super::real_urls::all_scalar_values_exec(href) && lock_of_url_exec(urls, href, s1.next_id).is_some() {
                navigate_tab_exec::<U, F>(urls, s1, tab, href, body)
            } else {
                fail_navigation_exec::<F>(s1, i, 3)
            };
            (s2, append_outputs(closes, out))
        },
    }
}

/// [`abort_navigation`]: the navigation of `tab` fails with `code`.
pub fn abort_navigation_exec<F: FetchFnsExec>(s: StateRecord, tab: u64, code: u64) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        renderers_ok::<F>(s.renderers@),
    ensures
        result_view(out) == abort_navigation(s@, tab as nat, code),
        keeps_storage_jar_now(s, out.0),
        out.0.next_conn == s.next_conn,
        out.0.next_id == s.next_id,
        renderers_ok::<F>(out.0.renderers@),
{
    let (s1, closes) = close_tab_conns_exec(s, tab);
    match find_by_tab_exec(s1.renderers.as_slice(), tab) {
        None => (s1, closes),
        Some(i) => {
            let (s2, out) = fail_navigation_exec::<F>(s1, i, code);
            (s2, append_outputs(closes, out))
        },
    }
}

// ---------------------------------------------------------------------
// The jar operations of the transducer.
// ---------------------------------------------------------------------

/// [`store_allowed`], over the generated Public Suffix List.
pub fn store_allowed_exec(url: &RequestUrlRecord) -> (r: bool)
    ensures
        r == store_allowed(crate::contract::psl(), url@),
{
    match &url.host {
        Some(h) => !h.name.is_empty() && (h.is_ip_address || !is_public_suffix_string_exec(h.name.as_slice())),
        None => false,
    }
}

/// [`apply_net_ops`]: the jar after each jar operation of a transducer step,
/// in order.
pub fn apply_net_ops_exec(jar: Vec<CookieRecord>, ops: &[JarOpBuf], now: u64) -> (out: Vec<CookieRecord>)
    requires
        clazel_cookie::storage::contract::jar_in_range(clazel_cookie::storage::exec::jar_view(jar@)),
        clazel_cookie::set_cookie::contract::now_in_range(now as int),
        clazel_fetch::transducer::contract::ops_at(clazel_fetch::transducer::types::ops_view(ops@), now as int),
    ensures
        clazel_cookie::storage::exec::jar_view(out@) == apply_net_ops(
            crate::contract::psl(),
            clazel_cookie::storage::exec::jar_view(jar@),
            clazel_fetch::transducer::types::ops_view(ops@),
        ),
        clazel_cookie::storage::contract::jar_in_range(clazel_cookie::storage::exec::jar_view(out@)),
{
    let ghost rules = crate::contract::psl();
    let ghost ov = clazel_fetch::transducer::types::ops_view(ops@);
    let ghost jar0 = clazel_cookie::storage::exec::jar_view(jar@);
    let mut cur = jar;
    let mut i: usize = 0;
    proof {
        assert(ov.skip(0) =~= ov);
    }
    while i < ops.len()
        invariant
            i <= ops.len(),
            ov == clazel_fetch::transducer::types::ops_view(ops@),
            rules == crate::contract::psl(),
            clazel_cookie::set_cookie::contract::now_in_range(now as int),
            clazel_fetch::transducer::contract::ops_at(ov, now as int),
            clazel_cookie::storage::contract::jar_in_range(clazel_cookie::storage::exec::jar_view(cur@)),
            apply_net_ops(rules, clazel_cookie::storage::exec::jar_view(cur@), ov.skip(i as int)) == apply_net_ops(rules, jar0, ov),
        decreases ops.len() - i,
    {
        let ghost before = clazel_cookie::storage::exec::jar_view(cur@);
        proof {
            assert(ov[i as int] == ops@[i as int]@);
            assert(ov.skip(i as int).drop_first() =~= ov.skip(i as int + 1));
            assert(ov.skip(i as int)[0] == ov[i as int]);
            assert(clazel_fetch::transducer::contract::op_now(ov[i as int]) == now as int);
        }
        if let Some(op) = ops.get(i) {
            match op {
                JarOpBuf::Retrieved { url, ctx, now: t } => {
                    let _ = retrieve_a_cookie_string_exec(&mut cur, url, ctx, *t);
                },
                JarOpBuf::Stored { line, url, ctx, now: t } => {
                    if store_allowed_exec(url) {
                        cur = store_a_set_cookie_string_exec(cur.as_slice(), line.as_slice(), url, ctx, *t);
                    }
                },
            }
            proof {
                clazel_cookie::storage::exec::lemma_jar_view_in_range(cur@);
                assert(clazel_cookie::storage::exec::jar_view(cur@) == apply_net_op(rules, before, ov[i as int]));
            }
        }
        // Never saturates: i < ops.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(ov.skip(ops.len() as int) =~= Seq::<clazel_fetch::transducer::spec::JarOp>::empty());
    }
    cur
}

// ---------------------------------------------------------------------
// Carrying out the transducer's actions.
// ---------------------------------------------------------------------

/// The view of an optional connection id.
pub open spec fn conn_opt_view(c: Option<u64>) -> Option<nat> {
    match c {
        Some(c) => Some(c as nat),
        None => None,
    }
}

/// Counting the `Connect`s of a list of actions by its first.
proof fn lemma_count_head(av: Seq<clazel_fetch::transducer::spec::Action>)
    requires
        av.len() > 0,
    ensures
        clazel_fetch::transducer::contract::count_connects(av) == (if av[0] is Connect {
            1nat
        } else {
            0nat
        }) + clazel_fetch::transducer::contract::count_connects(av.drop_first()),
{
    let one = seq![av[0]];
    assert(av =~= one + av.drop_first());
    clazel_fetch::transducer::theorems::lemma_count_concat(one, av.drop_first());
    clazel_fetch::transducer::theorems::lemma_count_one(av[0]);
}

/// One step of [`carry_out`], by the first action.
proof fn lemma_carry_out_head(urls: UrlFns, s: State, tab: nat, partition: crate::domain::Domain, cur: Option<nat>, actions: Seq<NetAction>)
    requires
        actions.len() > 0,
    ensures
        ({
            let rest = actions.drop_first();
            match actions[0] {
                clazel_fetch::transducer::spec::Action::Connect { host, port, tls } => {
                    let (s1, id, out) = open_connection(s, tab, partition, Endpoint { host, port, tls });
                    let (s2, out2) = carry_out(urls, s1, tab, partition, Some(id), rest);
                    carry_out(urls, s, tab, partition, cur, actions) == (s2, out + out2)
                },
                clazel_fetch::transducer::spec::Action::Send(bytes) => match cur {
                    Some(c) => {
                        let (s1, out) = carry_out(urls, s, tab, partition, cur, rest);
                        carry_out(urls, s, tab, partition, cur, actions) == (s1, seq![Output::Send { conn: c, bytes }] + out)
                    },
                    None => carry_out(urls, s, tab, partition, cur, actions) == carry_out(urls, s, tab, partition, cur, rest),
                },
                clazel_fetch::transducer::spec::Action::Close => match cur {
                    Some(c) => {
                        let (s1, out) = carry_out(urls, State { conns: without_conn(s.conns, c), ..s }, tab, partition, None, rest);
                        carry_out(urls, s, tab, partition, cur, actions) == (s1, seq![Output::Close { conn: c }] + out)
                    },
                    None => carry_out(urls, s, tab, partition, cur, actions) == carry_out(urls, s, tab, partition, cur, rest),
                },
                clazel_fetch::transducer::spec::Action::Done { url, response } => carry_out(urls, s, tab, partition, cur, actions) == commit_navigation(
                    urls,
                    s,
                    tab,
                    clazel_url::url::spec::url_serializer(url, false),
                    response.body,
                ),
                clazel_fetch::transducer::spec::Action::Fail(_) => carry_out(urls, s, tab, partition, cur, actions) == abort_navigation(s, tab, error_fetch()),
            }
        }),
{
    reveal_with_fuel(carry_out, 2);
}

/// [`carry_out`]: what the kernel does for the actions the transducer gave
/// the navigation of `tab`, in order.
pub fn carry_out_exec<U: UrlFnsExec, F: FetchFnsExec>(
    urls: &U,
    s: StateRecord,
    tab: u64,
    partition: &DomainRecord,
    cur: Option<u64>,
    actions: Vec<ActionBuf>,
) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        renderers_ok::<F>(s.renderers@),
        s.next_id < 0xFFFF_FFFF_FFFF_FFFFu64,
        s.next_conn as nat + clazel_fetch::transducer::contract::count_connects(clazel_fetch::transducer::types::actions_view(actions@)) <= 0xFFFF_FFFF_FFFF_FFFFnat,
    ensures
        result_view(out) == carry_out(urls.urls(), s@, tab as nat, partition@, conn_opt_view(cur), clazel_fetch::transducer::types::actions_view(actions@)),
        renderers_ok::<F>(out.0.renderers@),
        keeps_storage_jar_now(s, out.0),
        out.0.next_id <= s.next_id + 1,
        out.0.next_conn as nat <= s.next_conn as nat + clazel_fetch::transducer::contract::count_connects(clazel_fetch::transducer::types::actions_view(actions@)),
    decreases actions.len(),
{
    let ghost av = clazel_fetch::transducer::types::actions_view(actions@);
    let ghost sk = s@;
    let ghost curk = conn_opt_view(cur);
    if actions.len() == 0 {
        proof {
            assert(av =~= Seq::<NetAction>::empty());
        }
        return (s, no_outputs());
    }
    let mut actions = actions;
    let act = actions.remove(0);
    let ghost rest = av.drop_first();
    proof {
        assert(clazel_fetch::transducer::types::actions_view(actions@) =~= rest);
        lemma_count_head(av);
        assert(av[0] == act@);
        lemma_carry_out_head(urls.urls(), sk, tab as nat, partition@, curk, av);
    }
    match act {
        ActionBuf::Connect { host, port, tls } => {
            let (s1, id, out) = open_connection_exec(s, tab, partition, EndpointRecord { host, port: port as u64, tls });
            let (s2, out2) = carry_out_exec::<U, F>(urls, s1, tab, partition, Some(id), actions);
            (s2, append_outputs(out, out2))
        },
        ActionBuf::Send(bytes) => match cur {
            Some(c) => {
                let (s1, out) = carry_out_exec::<U, F>(urls, s, tab, partition, cur, actions);
                let piece = one_output(OutputRecord::Send { conn: c, bytes });
                (s1, append_outputs(piece, out))
            },
            None => carry_out_exec::<U, F>(urls, s, tab, partition, cur, actions),
        },
        ActionBuf::Close => match cur {
            Some(c) => {
                let mut s = s;
                let conns = without_conn_exec(s.conns.as_slice(), c);
                s.conns = conns;
                let (s1, out) = carry_out_exec::<U, F>(urls, s, tab, partition, None, actions);
                let piece = one_output(OutputRecord::Close { conn: c });
                (s1, append_outputs(piece, out))
            },
            None => carry_out_exec::<U, F>(urls, s, tab, partition, cur, actions),
        },
        ActionBuf::Done { url, response } => {
            let href = url.serialize(false);
            commit_navigation_exec::<U, F>(urls, s, tab, href.as_slice(), response.body.as_slice())
        },
        ActionBuf::Fail(_) => abort_navigation_exec::<F>(s, tab, 5),
    }
}

// ---------------------------------------------------------------------
// A navigation starts, and the network answers.
// ---------------------------------------------------------------------

/// [`begin_navigation`]: the renderer of tab `tab` starts navigating to
/// `url`, and the transducer asks for the first connection.
pub fn begin_navigation_exec<U: UrlFnsExec, F: FetchFnsExec>(urls: &U, fetch: &F, s: StateRecord, tab: u64, url: &[u32]) -> (out: (
    StateRecord,
    Vec<OutputRecord>,
))
    requires
        renderers_ok::<F>(s.renderers@),
        s.next_id < 0xFFFF_FFFF_FFFF_FFFFu64,
        s.next_conn as nat + conn_headroom() <= 0xFFFF_FFFF_FFFF_FFFFnat,
    ensures
        result_view(out) == begin_navigation(crate::contract::psl(), urls.urls(), fetch.fetch(), s@, tab as nat, url@),
        renderers_ok::<F>(out.0.renderers@),
        keeps_storage_jar_now(s, out.0),
        out.0.next_id <= s.next_id + 1,
        out.0.next_conn as nat <= s.next_conn as nat + conn_headroom(),
{
    let h = fetch.http_fns();
    match find_by_tab_exec(s.renderers.as_slice(), tab) {
        None => (s, no_outputs()),
        Some(i) => match lock_of_url_exec(urls, url, s.next_id) {
            None => (s, no_outputs()),
            Some(_) => {
                let (s0, closes) = close_tab_conns_exec(s, tab);
                match fetch.parse(url) {
                    None => {
                        let (s1, out) = fail_navigation_exec::<F>(s0, i, 3);
                        (s1, append_outputs(closes, out))
                    },
                    Some(parsed) => {
                        let (fs, actions) = clazel_fetch::transducer::step::start(&parsed);
                        proof {
                            F::nav_ok_idle(&fs);
                            clazel_fetch::transducer::theorems::lemma_begin_budget(parsed@, 0, false);
                        }
                        let partition = match s0.renderers.get(i) {
                            Some(r) => domain_of_lock_exec(&r.lock),
                            None => DomainRecord::Opaque(0),
                        };
                        let mut s1 = s0;
                        let ghost old_renderers = s1.renderers@;
                        let old = s1.renderers.remove(i);
                        let rec = RendererRecord {
                            id: old.id,
                            tab: old.tab,
                            url: old.url,
                            lock: old.lock,
                            pending: Some(NavigationRecord { url: copy(url), fetch: fs, partition: clone_domain(&partition) }),
                        };
                        s1.renderers.insert(i, rec);
                        proof {
                            lemma_renderers_view_replace(old_renderers, i as int, rec);
                            lemma_ok_remove::<F>(old_renderers, i as int);
                            lemma_ok_insert::<F>(old_renderers.remove(i as int), i as int, rec);
                        }
                        let (s2, out2) = carry_out_exec::<U, F>(urls, s1, tab, &partition, None, actions);
                        (s2, append_outputs(closes, out2))
                    },
                }
            },
        },
    }
}

/// `Net { conn, input }` ([`net`]): the transducer of the navigation the
/// connection belongs to takes a step.
pub fn net_exec<U: UrlFnsExec, F: FetchFnsExec>(urls: &U, fetch: &F, s: StateRecord, conn: u64, input: &InputBuf) -> (out: (
    StateRecord,
    Vec<OutputRecord>,
))
    requires
        crate::invariant::navigations_wf(crate::contract::psl(), s@.renderers),
        renderers_ok::<F>(s.renderers@),
        clazel_cookie::set_cookie::contract::now_in_range(s.now as int),
        s.next_id < 0xFFFF_FFFF_FFFF_FFFFu64,
        s.next_conn as nat + conn_headroom() <= 0xFFFF_FFFF_FFFF_FFFFnat,
    ensures
        result_view(out) == net(crate::contract::psl(), urls.urls(), fetch.fetch(), s@, conn as nat, input@),
        renderers_ok::<F>(out.0.renderers@),
        out.0.storage@ == s.storage@,
        out.0.now == s.now,
        out.0.next_id <= s.next_id + 1,
        out.0.next_conn as nat <= s.next_conn as nat + conn_headroom(),
{
    let h = fetch.http_fns();
    let ghost sv = s@;
    proof {
        clazel_cookie::storage::exec::lemma_jar_view_in_range(s.jar@);
    }
    match find_conn_exec(s.conns.as_slice(), conn) {
        None => (s, no_outputs()),
        Some(ci) => {
            let ctab = match s.conns.get(ci) {
                Some(c) => c.tab,
                None => 0,
            };
            match find_by_tab_exec(s.renderers.as_slice(), ctab) {
                None => (s, no_outputs()),
                Some(i) => {
                    let navigating = match s.renderers.get(i) {
                        Some(r) => r.pending.is_some(),
                        None => false,
                    };
                    if !navigating {
                        return (s, no_outputs());
                    }
                    let StateRecord { renderers, jar, storage, next_id, conns, next_conn, now } = s;
                    let mut renderers = renderers;
                    let ghost old_renderers = renderers@;
                    let rec = renderers.remove(i);
                    let RendererRecord { id, tab, url, lock, pending } = rec;
                    match pending {
                        None => {
                            proof {
                                assert(false);
                            }
                            (StateRecord { renderers, jar, storage, next_id, conns, next_conn, now }, no_outputs())
                        },
                        Some(nav) => {
                            let NavigationRecord { url: nurl, fetch: fstate, partition } = nav;
                            proof {
                                assert(old_renderers[i as int].pending is Some);
                            }
                            let (fs, actions, ops) = clazel_fetch::transducer::step::step(h, fetch.url_fns(), fstate, input, jar.as_slice(), now);
                            proof {
                                clazel_fetch::transducer::theorems::lemma_step_budget(
                                    fetch.fetch().http,
                                    fetch.fetch().urls,
                                    sv.renderers[i as int].pending->Some_0.fetch,
                                    input@,
                                    sv.jar,
                                    sv.now,
                                );
                            }
                            let jar1 = apply_net_ops_exec(jar, ops.as_slice(), now);
                            let conns1 = match input {
                                InputBuf::Closed | InputBuf::Error => without_conn_exec(conns.as_slice(), conn),
                                _ => conns,
                            };
                            let rec2 = RendererRecord {
                                id,
                                tab,
                                url,
                                lock,
                                pending: Some(NavigationRecord { url: nurl, fetch: fs, partition: clone_domain(&partition) }),
                            };
                            renderers.insert(i, rec2);
                            proof {
                                lemma_renderers_view_replace(old_renderers, i as int, rec2);
                                lemma_ok_remove::<F>(old_renderers, i as int);
                                lemma_ok_insert::<F>(old_renderers.remove(i as int), i as int, rec2);
                            }
                            let s1 = StateRecord { renderers, jar: jar1, storage, next_id, conns: conns1, next_conn, now };
                            carry_out_exec::<U, F>(urls, s1, ctab, &partition, Some(conn), actions)
                        },
                    }
                },
            }
        },
    }
}

/// [`tick`]: time moves forward and expired cookies are evicted.
pub fn tick_exec(s: StateRecord, time: u64) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        clazel_cookie::set_cookie::contract::now_in_range(s.now as int),
        clazel_cookie::set_cookie::contract::now_in_range(time as int),
    ensures
        result_view(out) == tick(s@, time as int),
        out.0.storage@ == s.storage@,
        out.0.renderers@ == s.renderers@,
        out.0.next_id == s.next_id,
        out.0.next_conn == s.next_conn,
        clazel_cookie::set_cookie::contract::now_in_range(out.0.now as int),
{
    let now = if time > s.now { time } else { s.now };
    let mut s = s;
    let jar = evict_expired_exec(s.jar.as_slice(), now);
    s.jar = jar;
    s.now = now;
    (s, no_outputs())
}

/// [`renderer_exited`]: the renderer and its tab are gone, and the
/// connections of its navigation are closed.
pub fn renderer_exited_exec<F: FetchFnsExec>(s: StateRecord, id: u64) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        renderers_ok::<F>(s.renderers@),
    ensures
        result_view(out) == renderer_exited(s@, id as nat),
        out.0.storage@ == s.storage@,
        out.0.jar@ == s.jar@,
        out.0.now == s.now,
        out.0.next_id == s.next_id,
        out.0.next_conn == s.next_conn,
        renderers_ok::<F>(out.0.renderers@),
{
    match find_by_id_exec(s.renderers.as_slice(), id) {
        None => (s, no_outputs()),
        Some(i) => {
            let tab = match s.renderers.get(i) {
                Some(r) => r.tab,
                None => 0,
            };
            let (s0, closes) = close_tab_conns_exec(s, tab);
            let mut s0 = s0;
            let ghost old_renderers = s0.renderers@;
            let _removed = s0.renderers.remove(i);
            proof {
                lemma_renderers_view_remove(old_renderers, i as int);
                lemma_ok_remove::<F>(old_renderers, i as int);
            }
            (s0, closes)
        },
    }
}

// ---------------------------------------------------------------------
// Messages from renderers.
// ---------------------------------------------------------------------

/// What `handle_message_exec` and the later functions need of the state: the
/// contract's precondition and the exec state's own invariant.
pub open spec fn state_ok<F: FetchFnsExec>(urls: UrlFns, s: StateRecord) -> bool {
    &&& crate::invariant::kernel_wf(crate::contract::psl(), urls, s@)
    &&& clazel_cookie::set_cookie::contract::now_in_range(s.now as int)
    &&& s.next_id < 0xFFFF_FFFF_FFFF_FFFFu64
    &&& s.next_conn as nat + conn_headroom() <= 0xFFFF_FFFF_FFFF_FFFFnat
    &&& s.exec_wf::<F>()
}

/// A message is handled by a renderer's fields, not by its navigation (which
/// only `Navigate` starts, through its tab).
proof fn lemma_handle_message_idle(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, r: Renderer, m: clazel_ipc::message::spec::Message)
    ensures
        handle_message(rules, urls, fetch, s, Renderer { pending: None, ..r }, m) == handle_message(rules, urls, fetch, s, r, m),
{
}

/// [`handle_message`]: a message that decoded, from the renderer at index `i`.
pub fn handle_message_exec<U: UrlFnsExec, F: FetchFnsExec>(urls: &U, fetch: &F, s: StateRecord, i: usize, m: Msg) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        state_ok::<F>(urls.urls(), s),
        crate::contract::urls_resolve_scalar(urls.urls()),
        i < s.renderers.len(),
    ensures
        result_view(out) == handle_message(crate::contract::psl(), urls.urls(), fetch.fetch(), s@, s@.renderers[i as int], m@),
        out.0.exec_wf::<F>(),
        out.0.now == s.now,
        out.0.next_id <= s.next_id + 1,
        out.0.next_conn as nat <= s.next_conn as nat + conn_headroom(),
{
    let ghost sv = s@;
    let r = renderer_at(s.renderers.as_slice(), i);
    proof {
        lemma_handle_message_idle(crate::contract::psl(), urls.urls(), fetch.fetch(), sv, sv.renderers[i as int], m@);
    }
    match m {
        Msg::CookieGet => {
            if cookie_averse_exec(&r.lock) {
                let reply_msg = Msg::CookieValue { cookie_string: Vec::new() };
                let outs = reply_exec(&r, &reply_msg);
                (s, outs)
            } else {
                let mut s = s;
                let url = request_url_exec(urls, &r);
                let ctx = document_context_exec(&r.lock);
                proof {
                    clazel_cookie::storage::exec::lemma_jar_view_in_range(s.jar@);
                }
                let cookie_string = retrieve_a_cookie_string_exec(&mut s.jar, &url, &ctx, s.now);
                let reply_msg = Msg::CookieValue { cookie_string };
                let outs = reply_exec(&r, &reply_msg);
                (s, outs)
            }
        },
        Msg::CookieSet { cookie_string } => {
            if cookie_averse_exec(&r.lock) {
                (s, no_outputs())
            } else {
                let mut s = s;
                let url = request_url_exec(urls, &r);
                let ctx = document_context_exec(&r.lock);
                proof {
                    clazel_cookie::storage::exec::lemma_jar_view_in_range(s.jar@);
                }
                let jar = store_a_set_cookie_string_exec(s.jar.as_slice(), cookie_string.as_slice(), &url, &ctx, s.now);
                s.jar = jar;
                (s, no_outputs())
            }
        },
        Msg::StorageGetItem { .. }
        | Msg::StorageSetItem { .. }
        | Msg::StorageRemoveItem { .. }
        | Msg::StorageClear
        | Msg::StorageKey { .. }
        | Msg::StorageLength => match r.lock {
            ParsedOrigin::Opaque(_) => {
                let e = Msg::Error { code: 1 };
                let outs = reply_exec(&r, &e);
                (s, outs)
            },
            ParsedOrigin::Tuple { .. } => {
                storage_call_exec(s, &r, &m)
            },
        },
        Msg::Navigate { url } => match clazel_encoding::utf8::decode::decode_without_bom_or_fail(url.as_slice()) {
            None => {
                let e = Msg::Error { code: 3 };
                let outs = reply_exec(&r, &e);
                (s, outs)
            },
            Some(relative) => match urls.resolve(r.url.as_slice(), relative.as_slice()) {
                None => {
                    let e = Msg::Error { code: 3 };
                    let outs = reply_exec(&r, &e);
                    (s, outs)
                },
                Some(resolved) => {
                    if lock_of_url_exec(urls, resolved.as_slice(), s.next_id).is_none() {
                        let e = Msg::Error { code: 3 };
                        let outs = reply_exec(&r, &e);
                        (s, outs)
                    } else {
                        begin_navigation_exec(urls, fetch, s, r.tab, resolved.as_slice())
                    }
                },
            },
        },
        _ => (s, no_outputs()),
    }
}

/// A frame a renderer may not send: the renderer at index `i` (with id `id`)
/// is killed, its record, with its tab, removed and its connections closed.
fn kill_renderer_exec<F: FetchFnsExec>(s: StateRecord, i: usize, id: u64) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        i < s.renderers.len(),
        renderers_ok::<F>(s.renderers@),
    ensures
        result_view(out) == ({
            let (s0, closes) = close_tab_conns(s@, s@.renderers[i as int].tab);
            (State { renderers: s@.renderers.remove(i as int), ..s0 }, seq![Output::Kill { id: id as nat }] + closes)
        }),
        keeps_storage_jar_now(s, out.0),
        out.0.next_id == s.next_id,
        out.0.next_conn == s.next_conn,
        renderers_ok::<F>(out.0.renderers@),
{
    let tab = match s.renderers.get(i) {
        Some(r) => r.tab,
        None => 0,
    };
    let (s0, closes) = close_tab_conns_exec(s, tab);
    let mut s0 = s0;
    let ghost old_renderers = s0.renderers@;
    let _removed = s0.renderers.remove(i);
    proof {
        lemma_renderers_view_remove(old_renderers, i as int);
        lemma_ok_remove::<F>(old_renderers, i as int);
    }
    let kill = one_output(OutputRecord::Kill { id });
    (s0, append_outputs(kill, closes))
}

/// `FromRenderer(id, bytes)` ([`from_renderer`]).
pub fn from_renderer_exec<U: UrlFnsExec, F: FetchFnsExec>(urls: &U, fetch: &F, s: StateRecord, id: u64, bytes: &[u8]) -> (out: (
    StateRecord,
    Vec<OutputRecord>,
))
    requires
        state_ok::<F>(urls.urls(), s),
        crate::contract::urls_resolve_scalar(urls.urls()),
    ensures
        result_view(out) == from_renderer(crate::contract::psl(), urls.urls(), fetch.fetch(), s@, id as nat, bytes@),
        out.0.exec_wf::<F>(),
        out.0.now == s.now,
        out.0.next_id <= s.next_id + 1,
        out.0.next_conn as nat <= s.next_conn as nat + conn_headroom(),
{
    match find_by_id_exec(s.renderers.as_slice(), id) {
        None => (s, no_outputs()),
        Some(i) => {
            match clazel_ipc::message::codec::decode_framed(bytes) {
                Some(m) => {
                    if clazel_ipc::message::codec::is_from_renderer(&m) {
                        handle_message_exec(urls, fetch, s, i, m)
                    } else {
                        kill_renderer_exec::<F>(s, i, id)
                    }
                },
                None => kill_renderer_exec::<F>(s, i, id),
            }
        },
    }
}

/// The kernel's step function ([`step`]): the one entry point of the
/// executable kernel. Pure: bytes, ids and time come in as arguments, and
/// the outputs go out as a value for the host to act on.
pub fn step_exec<U: UrlFnsExec, F: FetchFnsExec>(urls: &U, fetch: &F, s: StateRecord, e: &EventRecord) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        crate::contract::step_requires(urls.urls(), fetch.fetch(), s@, e@),
        s.exec_wf::<F>(),
    ensures
        crate::contract::step_ensures(urls.urls(), fetch.fetch(), s@, e@, result_view(out)),
        out.0.exec_wf::<F>(),
        clazel_cookie::storage::contract::jar_in_range(out.0@.jar),
        clazel_cookie::set_cookie::contract::now_in_range(out.0@.now),
        out.0@.next_id <= s@.next_id + 1,
        out.0@.next_conn <= s@.next_conn + conn_headroom(),
{
    proof {
        clazel_cookie::storage::exec::lemma_jar_view_in_range(s.jar@);
    }
    let h = fetch.http_fns();
    let out = match e {
        EventRecord::FromRenderer { id, bytes } => from_renderer_exec(urls, fetch, s, *id, bytes.as_slice()),
        EventRecord::OpenTab { url, script } => open_tab_exec::<U, F>(urls, s, url.as_slice(), script.as_slice()),
        EventRecord::NavigateTab { tab, url } => begin_navigation_exec(urls, fetch, s, *tab, url.as_slice()),
        EventRecord::Net { conn, input } => net_exec(urls, fetch, s, *conn, input),
        EventRecord::RendererExited { id } => renderer_exited_exec::<F>(s, *id),
        EventRecord::Tick { time } => tick_exec(s, *time),
    };
    proof {
        clazel_cookie::storage::exec::lemma_jar_view_in_range(out.0.jar@);
    }
    out
}

} // verus!
