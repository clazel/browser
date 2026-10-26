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
    CookieRecord, RequestUrlRecord, evict_expired_exec, is_public_suffix_string_exec,
    retrieve_a_cookie_string_exec, store_a_set_cookie_string_exec,
};
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

/// A copy of a renderer's pending URL.
fn copy_pending(p: &Option<Vec<u32>>) -> (out: Option<Vec<u32>>)
    ensures
        code_points_opt_view(out) == code_points_opt_view(*p),
{
    let p = p.as_ref()?;
    Some(copy(p.as_slice()))
}

/// A copy of renderer `i`.
pub fn renderer_at(rs: &[RendererRecord], i: usize) -> (r: RendererRecord)
    requires
        i < rs.len(),
    ensures
        r@ == renderers_view(rs@)[i as int],
{
    match rs.get(i) {
        Some(r) => RendererRecord {
            id: r.id,
            tab: r.tab,
            url: copy(r.url.as_slice()),
            lock: clone_origin(&r.lock),
            pending: copy_pending(&r.pending),
        },
        None => RendererRecord { id: 0, tab: 0, url: Vec::new(), lock: ParsedOrigin::Opaque(0), pending: None },
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
        s.exec_wf(),
        crate::invariant::storage_wf(s@.storage),
    ensures
        result_view(out) == storage_call(s@, r@, m@),
        out.0.exec_wf(),
        out.0.renderers@ == s.renderers@,
        out.0.jar@ == s.jar@,
        out.0.next_id == s.next_id,
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
// Navigation.
// ---------------------------------------------------------------------

/// The facts a step that leaves storage, jar and time alone gives about its
/// result.
pub open spec fn keeps_storage_jar_now(before: StateRecord, after: StateRecord) -> bool {
    &&& after.storage@ == before.storage@
    &&& after.jar@ == before.jar@
    &&& after.now == before.now
}

/// [`navigate_tab`]: the renderer of tab `tab` commits the document at `url`.
pub fn navigate_tab_exec<U: UrlFnsExec>(urls: &U, s: StateRecord, tab: u64, url: &[u32], script: &[u8]) -> (out: (
    StateRecord,
    Vec<OutputRecord>,
))
    requires
        s.next_id < 0xFFFF_FFFF_FFFF_FFFFu64,
        clazel_encoding::utf8::spec::all_scalar_values(url@),
    ensures
        result_view(out) == navigate_tab(urls.urls(), s@, tab as nat, url@, script@),
        keeps_storage_jar_now(s, out.0),
        out.0.next_id <= s.next_id + 1,
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
pub fn open_tab_exec<U: UrlFnsExec>(urls: &U, s: StateRecord, url: &[u32], script: &[u8]) -> (out: (
    StateRecord,
    Vec<OutputRecord>,
))
    requires
        s.next_id < 0xFFFF_FFFF_FFFF_FFFFu64,
        clazel_encoding::utf8::spec::all_scalar_values(url@),
    ensures
        result_view(out) == open_tab(urls.urls(), s@, url@, script@),
        keeps_storage_jar_now(s, out.0),
        out.0.next_id <= s.next_id + 1,
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
            }
            s.next_id = id.saturating_add(1);
            let outs = two_outputs(OutputRecord::Spawn { id }, OutputRecord::ToRenderer { id, bytes: frame });
            (s, outs)
        },
    }
}

/// [`begin_navigation`]: the renderer of tab `tab` starts navigating to
/// `url`, and the kernel asks for it to be fetched.
pub fn begin_navigation_exec<U: UrlFnsExec>(urls: &U, s: StateRecord, tab: u64, url: &[u32]) -> (out: (
    StateRecord,
    Vec<OutputRecord>,
))
    ensures
        result_view(out) == begin_navigation(urls.urls(), s@, tab as nat, url@),
        keeps_storage_jar_now(s, out.0),
        out.0.next_id == s.next_id,
{
    match find_by_tab_exec(s.renderers.as_slice(), tab) {
        None => (s, no_outputs()),
        Some(i) => match lock_of_url_exec(urls, url, s.next_id) {
            None => (s, no_outputs()),
            Some(_) => {
                let old = renderer_at(s.renderers.as_slice(), i);
                let mut s = s;
                let ghost old_renderers = s.renderers@;
                let rec = RendererRecord { id: old.id, tab: old.tab, url: old.url, lock: old.lock, pending: Some(copy(url)) };
                s.renderers.set(i, rec);
                proof {
                    lemma_renderers_view_update(old_renderers, i as int, rec);
                }
                let outs = one_output(OutputRecord::Fetch { tab, url: copy(url) });
                (s, outs)
            },
        },
    }
}

/// [`fail_navigation`]: the navigation of the renderer at index `i` ends
/// without a commit: it stays, no longer navigating, and is sent an `Error`.
pub fn fail_navigation_exec(s: StateRecord, i: usize, code: u64) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        i < s.renderers.len(),
    ensures
        result_view(out) == fail_navigation(s@, i as int, s@.renderers[i as int], code),
        keeps_storage_jar_now(s, out.0),
        out.0.next_id == s.next_id,
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
    }
    (s, outs)
}

// ---------------------------------------------------------------------
// The fetch's answer.
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

/// [`store_one`]: the jar after one `Set-Cookie` line of a response.
pub fn store_one_exec(jar: Vec<CookieRecord>, st: &HttpStoreRecord, now: u64) -> (out: Vec<CookieRecord>)
    requires
        clazel_cookie::storage::contract::jar_in_range(clazel_cookie::storage::exec::jar_view(jar@)),
        clazel_cookie::set_cookie::contract::now_in_range(now as int),
    ensures
        clazel_cookie::storage::exec::jar_view(out@) == store_one(crate::contract::psl(), clazel_cookie::storage::exec::jar_view(jar@), st@, now as int),
{
    if store_allowed_exec(&st.url) {
        store_a_set_cookie_string_exec(jar.as_slice(), st.line.as_slice(), &st.url, &st.ctx, now)
    } else {
        jar
    }
}

/// Dropping the first element of the remaining stores is the next
/// `apply_stores` step.
proof fn lemma_apply_stores_tail(jar: Seq<clazel_cookie::storage::spec::Cookie>, stores: Seq<HttpStore>, k: int, now: int)
    requires
        0 <= k < stores.len(),
    ensures
        apply_stores(crate::contract::psl(), jar, stores.subrange(k, stores.len() as int), now) == apply_stores(
            crate::contract::psl(),
            store_one(crate::contract::psl(), jar, stores[k], now),
            stores.subrange(k + 1, stores.len() as int),
            now,
        ),
{
    let rest = stores.subrange(k, stores.len() as int);
    assert(rest[0] == stores[k]);
    assert(rest.drop_first() =~= stores.subrange(k + 1, stores.len() as int));
}

/// [`apply_stores`]: the jar after the `Set-Cookie` lines of a fetch.
pub fn apply_stores_exec(jar: Vec<CookieRecord>, stores: &[HttpStoreRecord], now: u64) -> (out: Vec<CookieRecord>)
    requires
        clazel_cookie::storage::contract::jar_in_range(clazel_cookie::storage::exec::jar_view(jar@)),
        clazel_cookie::set_cookie::contract::now_in_range(now as int),
    ensures
        clazel_cookie::storage::exec::jar_view(out@) == apply_stores(crate::contract::psl(), clazel_cookie::storage::exec::jar_view(jar@), stores_view(stores@), now as int),
{
    let ghost jar0 = clazel_cookie::storage::exec::jar_view(jar@);
    let ghost sv = stores_view(stores@);
    let mut cur = jar;
    let mut k: usize = 0;
    proof {
        assert(sv.subrange(0, sv.len() as int) =~= sv);
    }
    while k < stores.len()
        invariant
            k <= stores.len(),
            clazel_cookie::set_cookie::contract::now_in_range(now as int),
            sv == stores_view(stores@),
            clazel_cookie::storage::contract::jar_in_range(clazel_cookie::storage::exec::jar_view(cur@)),
            apply_stores(crate::contract::psl(), clazel_cookie::storage::exec::jar_view(cur@), sv.subrange(k as int, sv.len() as int), now as int) == apply_stores(
                crate::contract::psl(),
                jar0,
                sv,
                now as int,
            ),
        decreases stores.len() - k,
    {
        if let Some(st) = stores.get(k) {
            proof {
                lemma_apply_stores_tail(clazel_cookie::storage::exec::jar_view(cur@), sv, k as int, now as int);
                assert(sv[k as int] == st@);
            }
            cur = store_one_exec(cur, st, now);
            proof {
                clazel_cookie::storage::exec::lemma_jar_view_in_range(cur@);
            }
        }
        // Never saturates: k < stores.len().
        k = k.saturating_add(1);
    }
    proof {
        assert(sv.subrange(stores.len() as int, sv.len() as int) =~= Seq::<HttpStore>::empty());
    }
    cur
}

/// [`fetched`]: a `Fetched` event for tab `tab`, whose fetch was started for
/// `url`, over what the network delivered (`net`).
pub fn fetched_exec<U: UrlFnsExec, F: FetchFnsExec>(urls: &U, fetch: &F, s: StateRecord, tab: u64, url: &[u32], net: &[u8]) -> (out: (
    StateRecord,
    Vec<OutputRecord>,
))
    requires
        state_ok(urls.urls(), s),
    ensures
        result_view(out) == fetched(crate::contract::psl(), urls.urls(), fetch.fetch(), s@, tab as nat, NetOutcome { url: url@, net: net@ }),
        out.0.exec_wf(),
        out.0.now == s.now,
        out.0.next_id <= s.next_id + 1,
{
    let ghost sv = s@;
    match find_by_tab_exec(s.renderers.as_slice(), tab) {
        None => (s, no_outputs()),
        Some(i) => {
            let navigating_here = match s.renderers.get(i) {
                Some(r) => match &r.pending {
                    Some(p) => u32s_eq(p.as_slice(), url),
                    None => false,
                },
                None => false,
            };
            if !navigating_here {
                proof {
                    assert(fetched_run(fetch.fetch(), sv, tab as nat, NetOutcome { url: url@, net: net@ }) is None);
                }
                (s, no_outputs())
            } else {
                let run = fetch.run(url, net);
                let jar = s.jar;
                let renderers = s.renderers;
                let storage = s.storage;
                let next_id = s.next_id;
                let now = s.now;
                proof {
                    clazel_cookie::storage::exec::lemma_jar_view_in_range(jar@);
                }
                let jar1 = apply_stores_exec(jar, run.stores.as_slice(), now);
                let s1 = StateRecord { renderers, jar: jar1, storage, next_id, now };
                proof {
                    assert(s1@ == State { jar: apply_stores(crate::contract::psl(), sv.jar, stores_view(run.stores@), sv.now), ..sv });
                    clazel_cookie::storage::exec::lemma_jar_view_in_range(s1.jar@);
                }
                match run.result {
                    FetchResultRecord::Done { url: furl, body } => {
                        proof {
                            crate::invariant::lemma_scalar_url(furl@);
                        }
                        if super::real_urls::all_scalar_values_exec(furl.as_slice()) && lock_of_url_exec(urls, furl.as_slice(), s1.next_id).is_some() {
                            navigate_tab_exec(urls, s1, tab, furl.as_slice(), body.as_slice())
                        } else {
                            fail_navigation_exec(s1, i, 3)
                        }
                    },
                    FetchResultRecord::Failed => fail_navigation_exec(s1, i, 5),
                }
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
        clazel_cookie::set_cookie::contract::now_in_range(out.0.now as int),
{
    let now = if time > s.now { time } else { s.now };
    let mut s = s;
    let jar = evict_expired_exec(s.jar.as_slice(), now);
    s.jar = jar;
    s.now = now;
    (s, no_outputs())
}

/// [`renderer_exited`]: the renderer and its tab are gone.
pub fn renderer_exited_exec(s: StateRecord, id: u64) -> (out: (StateRecord, Vec<OutputRecord>))
    ensures
        result_view(out) == renderer_exited(s@, id as nat),
        out.0.storage@ == s.storage@,
        out.0.jar@ == s.jar@,
        out.0.now == s.now,
        out.0.next_id == s.next_id,
{
    match find_by_id_exec(s.renderers.as_slice(), id) {
        None => (s, no_outputs()),
        Some(i) => {
            let mut s = s;
            let ghost old_renderers = s.renderers@;
            let _removed = s.renderers.remove(i);
            proof {
                lemma_renderers_view_remove(old_renderers, i as int);
            }
            (s, no_outputs())
        },
    }
}

// ---------------------------------------------------------------------
// Messages from renderers.
// ---------------------------------------------------------------------

/// What `handle_message_exec` and the later functions need of the state: the
/// contract's precondition and the exec state's own invariant.
pub open spec fn state_ok(urls: UrlFns, s: StateRecord) -> bool {
    &&& crate::invariant::kernel_wf(crate::contract::psl(), urls, s@)
    &&& clazel_cookie::set_cookie::contract::now_in_range(s.now as int)
    &&& s.next_id < 0xFFFF_FFFF_FFFF_FFFFu64
    &&& s.exec_wf()
}

/// [`handle_message`]: a message that decoded, from the renderer at index `i`.
pub fn handle_message_exec<U: UrlFnsExec>(urls: &U, s: StateRecord, i: usize, m: Msg) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        state_ok(urls.urls(), s),
        crate::contract::urls_resolve_scalar(urls.urls()),
        i < s.renderers.len(),
    ensures
        result_view(out) == handle_message(crate::contract::psl(), urls.urls(), s@, s@.renderers[i as int], m@),
        out.0.exec_wf(),
        out.0.now == s.now,
        out.0.next_id <= s.next_id + 1,
{
    let ghost sv = s@;
    let r = renderer_at(s.renderers.as_slice(), i);
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
                        begin_navigation_exec(urls, s, r.tab, resolved.as_slice())
                    }
                },
            },
        },
        _ => (s, no_outputs()),
    }
}

/// A frame a renderer may not send: the renderer at index `i` (with id `id`)
/// is killed and its record, with its tab, removed.
fn kill_renderer_exec(s: StateRecord, i: usize, id: u64) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        i < s.renderers.len(),
    ensures
        result_view(out) == (State { renderers: renderers_view(s.renderers@).remove(i as int), ..s@ }, seq![Output::Kill { id: id as nat }]),
        keeps_storage_jar_now(s, out.0),
        out.0.next_id == s.next_id,
{
    let mut s = s;
    let ghost old_renderers = s.renderers@;
    let _removed = s.renderers.remove(i);
    proof {
        lemma_renderers_view_remove(old_renderers, i as int);
    }
    (s, one_output(OutputRecord::Kill { id }))
}

/// `FromRenderer(id, bytes)` ([`from_renderer`]).
pub fn from_renderer_exec<U: UrlFnsExec>(urls: &U, s: StateRecord, id: u64, bytes: &[u8]) -> (out: (
    StateRecord,
    Vec<OutputRecord>,
))
    requires
        state_ok(urls.urls(), s),
        crate::contract::urls_resolve_scalar(urls.urls()),
    ensures
        result_view(out) == from_renderer(crate::contract::psl(), urls.urls(), s@, id as nat, bytes@),
        out.0.exec_wf(),
        out.0.now == s.now,
        out.0.next_id <= s.next_id + 1,
{
    match find_by_id_exec(s.renderers.as_slice(), id) {
        None => (s, no_outputs()),
        Some(i) => {
            match clazel_ipc::message::codec::decode_framed(bytes) {
                Some(m) => {
                    if clazel_ipc::message::codec::is_from_renderer(&m) {
                        handle_message_exec(urls, s, i, m)
                    } else {
                        kill_renderer_exec(s, i, id)
                    }
                },
                None => kill_renderer_exec(s, i, id),
            }
        },
    }
}

/// The kernel's step function ([`step`]): the one entry point of the
/// executable kernel. Pure: bytes, ids and time come in as arguments, and
/// the outputs go out as a value for the host to act on.
pub fn step_exec<U: UrlFnsExec, F: FetchFnsExec>(urls: &U, fetch: &F, s: StateRecord, e: &EventRecord) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        crate::contract::step_requires(urls.urls(), s@, e@),
        s.exec_wf(),
    ensures
        crate::contract::step_ensures(urls.urls(), fetch.fetch(), s@, e@, result_view(out)),
        out.0.exec_wf(),
        clazel_cookie::storage::contract::jar_in_range(out.0@.jar),
        clazel_cookie::set_cookie::contract::now_in_range(out.0@.now),
        out.0@.next_id <= s@.next_id + 1,
{
    proof {
        clazel_cookie::storage::exec::lemma_jar_view_in_range(s.jar@);
    }
    let out = match e {
        EventRecord::FromRenderer { id, bytes } => from_renderer_exec(urls, s, *id, bytes.as_slice()),
        EventRecord::OpenTab { url, script } => open_tab_exec(urls, s, url.as_slice(), script.as_slice()),
        EventRecord::NavigateTab { tab, url } => begin_navigation_exec(urls, s, *tab, url.as_slice()),
        EventRecord::Fetched { tab, outcome } => fetched_exec(urls, fetch, s, *tab, outcome.url.as_slice(), outcome.net.as_slice()),
        EventRecord::RendererExited { id } => renderer_exited_exec(s, *id),
        EventRecord::Tick { time } => tick_exec(s, *time),
    };
    proof {
        clazel_cookie::storage::exec::lemma_jar_view_in_range(out.0.jar@);
    }
    out
}

} // verus!
