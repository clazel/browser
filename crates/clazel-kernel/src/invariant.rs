//! The reachable-state invariant `kernel_wf` and what is proven about it.
//!
//! `kernel_wf` is what item 2.11's isolation theorems assume of a state. It
//! holds of [`init_state`] (`lemma_init_wf`), `step` preserves it
//! (`lemma_step_preserves_wf`, proven here from `clazel-cookie`'s
//! `lemma_store_bounds`, `lemma_store_preserves_domains_nonempty` and
//! `lemma_evict_expired_props`), and so it holds of every reachable state
//! (`lemma_reachable_wf`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {


/// The renderers' ids and tabs are distinct and below the counter, and each
/// lock is the one the kernel chooses for the committed URL
/// ([`lock_of_url`]): "each renderer's lock is the origin of its committed
/// URL".
pub open spec fn renderers_wf(urls: UrlFns, rs: Seq<Renderer>, next_id: nat) -> bool {
    &&& forall|i: int| 0 <= i < rs.len() ==> (#[trigger] rs[i]).id < next_id && rs[i].tab < next_id
    &&& forall|i: int, j: int| 0 <= i < j < rs.len() ==> (#[trigger] rs[i]).id != (#[trigger] rs[j]).id && rs[i].tab != rs[j].tab
    &&& forall|i: int| 0 <= i < rs.len() ==> lock_of_url(urls, (#[trigger] rs[i]).url, rs[i].id) == Some(rs[i].lock)
}

/// Each key occurs once in the list.
pub open spec fn storage_keys_unique(list: Seq<StorageEntry>) -> bool {
    forall|i: int, j: int| 0 <= i < j < list.len() ==> (#[trigger] list[i]).key != (#[trigger] list[j]).key
}

/// Web Storage: only valid tuple origins have a map, which is non-empty, has
/// unique keys and is within the quota.
pub open spec fn storage_wf(storage: Map<clazel_origin::spec::Origin, Seq<StorageEntry>>) -> bool {
    forall|o: clazel_origin::spec::Origin|
        #[trigger] storage.dom().contains(o) ==> valid_tuple_origin(o) && storage[o].len() > 0 && storage_keys_unique(storage[o])
            && within_quota(storage[o])
}

/// No cookie of the jar has a public suffix as its domain (an IP address is
/// not one). The kernel never creates one: a document on a public-suffix host
/// is cookie-averse (`cookie_averse`), and step 9 of RFC 6265bis rejects a
/// `Domain` attribute that is a public suffix.
pub open spec fn jar_no_public_suffix(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>) -> bool {
    forall|i: int|
        0 <= i < jar.len() ==> (#[trigger] jar[i]).domain.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, jar[i].domain.name)
}

/// The invariant of every reachable state.
///
/// - the jar: `jar_domains_nonempty` (the hypothesis of `clazel-cookie`'s
///   retrieval isolation lemmas `lemma_retrieve_within_root` and
///   `lemma_retrieve_frame`, which hold only under it), at most 180 cookies
///   per root, and unique keys (§5.7 step 23's invariant);
/// - the renderers: [`renderers_wf`];
/// - Web Storage: [`storage_wf`].
pub open spec fn kernel_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, s: State) -> bool {
    &&& clazel_cookie::storage::isolation::jar_domains_nonempty(s.jar)
    &&& clazel_cookie::storage::spec::jar_within_root_limit(rules, s.jar)
    &&& clazel_cookie::storage::spec::jar_keys_unique(s.jar)
    &&& jar_no_public_suffix(rules, s.jar)
    &&& renderers_wf(urls, s.renderers, s.next_id)
    &&& storage_wf(s.storage)
}

/// The initial state satisfies the invariant.
pub proof fn lemma_init_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns)
    ensures
        kernel_wf(rules, urls, init_state()),
{
    let s = init_state();
    assert forall|root: clazel_cookie::matching::spec::CanonicalHost|
        clazel_cookie::storage::spec::root_count(rules, s.jar, root) <= clazel_cookie::storage::spec::max_cookies_per_root() by {
        assert(clazel_cookie::storage::spec::cookies_of_root(rules, s.jar, root) =~= Seq::<clazel_cookie::storage::spec::Cookie>::empty());
    }
}


// ---------------------------------------------------------------------
// Looking things up.
// ---------------------------------------------------------------------

/// `find_by_id` finds the first renderer with the id, or there is none from
/// `i` on.
pub proof fn lemma_find_by_id(rs: Seq<Renderer>, id: nat, i: nat)
    ensures
        match find_by_id(rs, id, i) {
            Some(k) => i <= k < rs.len() && rs[k].id == id,
            None => forall|k: int| i <= k < rs.len() ==> (#[trigger] rs[k]).id != id,
        },
    decreases rs.len() - i,
{
    if i < rs.len() && rs[i as int].id != id {
        lemma_find_by_id(rs, id, i + 1);
    }
}

/// `find_by_tab`, likewise.
pub proof fn lemma_find_by_tab(rs: Seq<Renderer>, tab: nat, i: nat)
    ensures
        match find_by_tab(rs, tab, i) {
            Some(k) => i <= k < rs.len() && rs[k].tab == tab,
            None => forall|k: int| i <= k < rs.len() ==> (#[trigger] rs[k]).tab != tab,
        },
    decreases rs.len() - i,
{
    if i < rs.len() && rs[i as int].tab != tab {
        lemma_find_by_tab(rs, tab, i + 1);
    }
}

/// `find_key`, likewise.
pub proof fn lemma_find_key(list: Seq<StorageEntry>, key: Seq<u8>, i: nat)
    ensures
        match find_key(list, key, i) {
            Some(k) => i <= k < list.len() && list[k].key == key,
            None => forall|k: int| i <= k < list.len() ==> (#[trigger] list[k]).key != key,
        },
    decreases list.len() - i,
{
    if i < list.len() && list[i as int].key != key {
        lemma_find_key(list, key, i + 1);
    }
}

// ---------------------------------------------------------------------
// The renderer table.
// ---------------------------------------------------------------------

/// Removing a renderer keeps the invariant.
pub proof fn lemma_renderers_wf_remove(urls: UrlFns, rs: Seq<Renderer>, next_id: nat, i: int)
    requires
        renderers_wf(urls, rs, next_id),
        0 <= i < rs.len(),
    ensures
        renderers_wf(urls, rs.remove(i), next_id),
{
    let r2 = rs.remove(i);
    assert forall|k: int| 0 <= k < r2.len() implies #[trigger] r2[k] == rs[if k < i { k } else { k + 1 }] by {}
    assert forall|k: int| 0 <= k < r2.len() implies (#[trigger] r2[k]).id < next_id && r2[k].tab < next_id by {
        let m = if k < i { k } else { k + 1 };
        assert(r2[k] == rs[m]);
    }
    assert forall|a: int, b: int| 0 <= a < b < r2.len() implies (#[trigger] r2[a]).id != (#[trigger] r2[b]).id && r2[a].tab
        != r2[b].tab by {
        let ma = if a < i { a } else { a + 1 };
        let mb = if b < i { b } else { b + 1 };
        assert(r2[a] == rs[ma]);
        assert(r2[b] == rs[mb]);
        assert(ma < mb);
    }
    assert forall|k: int| 0 <= k < r2.len() implies lock_of_url(urls, (#[trigger] r2[k]).url, r2[k].id) == Some(r2[k].lock) by {
        let m = if k < i { k } else { k + 1 };
        assert(r2[k] == rs[m]);
    }
}

/// A new renderer for a new tab keeps the invariant.
pub proof fn lemma_renderers_wf_push(urls: UrlFns, rs: Seq<Renderer>, next_id: nat, r: Renderer)
    requires
        renderers_wf(urls, rs, next_id),
        r.id == next_id,
        r.tab == next_id,
        lock_of_url(urls, r.url, r.id) == Some(r.lock),
    ensures
        renderers_wf(urls, rs.push(r), next_id + 1),
{
    let r2 = rs.push(r);
    assert forall|k: int| 0 <= k < r2.len() implies (#[trigger] r2[k]).id < next_id + 1 && r2[k].tab < next_id + 1 by {
        if k < rs.len() {
            assert(r2[k] == rs[k]);
        }
    }
    assert forall|a: int, b: int| 0 <= a < b < r2.len() implies (#[trigger] r2[a]).id != (#[trigger] r2[b]).id && r2[a].tab
        != r2[b].tab by {
        assert(r2[a] == rs[a]);
    }
    assert forall|k: int| 0 <= k < r2.len() implies lock_of_url(urls, (#[trigger] r2[k]).url, r2[k].id) == Some(r2[k].lock) by {
        if k < rs.len() {
            assert(r2[k] == rs[k]);
        }
    }
}

/// Replacing the renderer at `i` by a renderer of the same tab, whose id is
/// the old one's (a new committed URL) or a fresh one, keeps the invariant.
pub proof fn lemma_renderers_wf_update(urls: UrlFns, rs: Seq<Renderer>, next_id: nat, i: int, r: Renderer, new_next_id: nat)
    requires
        renderers_wf(urls, rs, next_id),
        0 <= i < rs.len(),
        r.tab == rs[i].tab,
        r.id == rs[i].id || (r.id == next_id && new_next_id == next_id + 1),
        r.id == rs[i].id ==> new_next_id == next_id,
        lock_of_url(urls, r.url, r.id) == Some(r.lock),
    ensures
        renderers_wf(urls, rs.update(i, r), new_next_id),
{
    let r2 = rs.update(i, r);
    assert forall|k: int| 0 <= k < r2.len() implies (#[trigger] r2[k]).id < new_next_id && r2[k].tab < new_next_id by {
        if k != i {
            assert(r2[k] == rs[k]);
        }
    }
    assert forall|a: int, b: int| 0 <= a < b < r2.len() implies (#[trigger] r2[a]).id != (#[trigger] r2[b]).id && r2[a].tab
        != r2[b].tab by {
        if a != i {
            assert(r2[a] == rs[a]);
        }
        if b != i {
            assert(r2[b] == rs[b]);
        }
    }
    assert forall|k: int| 0 <= k < r2.len() implies lock_of_url(urls, (#[trigger] r2[k]).url, r2[k].id) == Some(r2[k].lock) by {
        if k != i {
            assert(r2[k] == rs[k]);
        }
    }
}

/// A renderer's lock is a valid tuple origin if it is a tuple.
pub proof fn lemma_lock_valid(urls: UrlFns, url: Seq<u32>, id: nat, lock: clazel_origin::spec::Origin)
    requires
        lock_of_url(urls, url, id) == Some(lock),
        lock is Tuple,
    ensures
        valid_tuple_origin(lock),
{
}


// ---------------------------------------------------------------------
// The cookie jar.
// ---------------------------------------------------------------------

/// The jar part of `kernel_wf`.
pub open spec fn jar_wf(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>) -> bool {
    clazel_cookie::storage::isolation::jar_domains_nonempty(jar) && clazel_cookie::storage::spec::jar_within_root_limit(rules, jar) && clazel_cookie::storage::spec::jar_keys_unique(jar)
}

/// Evicting expired cookies keeps the jar well formed (`Tick`, and the
/// first step of every cookie call).
pub proof fn lemma_jar_wf_evict_expired(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, now: int)
    requires
        jar_wf(rules, jar),
    ensures
        jar_wf(rules, clazel_cookie::storage::spec::evict_expired(jar, now)),
{
    let live = clazel_cookie::storage::spec::evict_expired(jar, now);
    let any_root = clazel_cookie::matching::spec::CanonicalHost { name: seq![], is_ip_address: false };
    clazel_cookie::storage::isolation::lemma_evict_expired_props(rules, jar, now, any_root);
    assert forall|root: clazel_cookie::matching::spec::CanonicalHost| clazel_cookie::storage::spec::root_count(rules, live, root) <= clazel_cookie::storage::spec::max_cookies_per_root() by {
        clazel_cookie::storage::isolation::lemma_evict_expired_props(rules, jar, now, root);
    }
    assert forall|i: int| 0 <= i < live.len() implies clazel_cookie::storage::isolation::cookie_domain_nonempty(#[trigger] live[i]) by {
        assert(live.contains(live[i]));
        assert(jar.contains(live[i]));
        let k = choose|k: int| 0 <= k < jar.len() && jar[k] == live[i];
    }
}

/// Mapping a function that does not change whether `p` holds over a
/// sequence does not change how many elements `p` keeps.
pub proof fn lemma_map_filter_len<A>(s: Seq<A>, f: spec_fn(A) -> A, p: spec_fn(A) -> bool)
    requires
        forall|c: A| #[trigger] p(f(c)) == p(c),
    ensures
        s.map_values(f).filter(p).len() == s.filter(p).len(),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let t = s.drop_last();
        lemma_map_filter_len(t, f, p);
        assert(s.map_values(f).drop_last() =~= t.map_values(f));
        assert(s.map_values(f).last() == f(s.last()));
    }
}

/// `document.cookie`'s getter keeps the jar well formed.
pub proof fn lemma_jar_wf_retrieval(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    url: clazel_cookie::storage::spec::RequestUrl,
    ctx: clazel_cookie::storage::spec::RequestContext,
    now: int,
)
    requires
        jar_wf(rules, jar),
    ensures
        jar_wf(rules, clazel_cookie::storage::spec::jar_after_retrieval(rules, jar, url, ctx, now)),
{
    let live = clazel_cookie::storage::spec::evict_expired(jar, now);
    lemma_jar_wf_evict_expired(rules, jar, now);
    if let Some(host) = url.host {
        let f = clazel_cookie::storage::spec::update_last_access_time(rules, url, ctx, host, now);
        let out = live.map_values(f);
        assert forall|c: clazel_cookie::storage::spec::Cookie| #[trigger] f(c).domain == c.domain && f(c).name == c.name && f(c).host_only_flag == c.host_only_flag
            && f(c).path == c.path by {
            if clazel_cookie::storage::spec::cookie_is_retrieved(rules, url, ctx, host, c) {
                assert(f(c) == clazel_cookie::storage::spec::with_last_access_time(c, now));
            }
        }
        assert forall|i: int| 0 <= i < out.len() implies clazel_cookie::storage::isolation::cookie_domain_nonempty(#[trigger] out[i]) by {
            assert(out[i] == f(live[i]));
        }
        assert forall|a: int, b: int| 0 <= a < b < out.len() implies !clazel_cookie::storage::spec::same_key(#[trigger] out[a], #[trigger] out[b]) by {
            assert(out[a] == f(live[a]));
            assert(out[b] == f(live[b]));
        }
        assert forall|root: clazel_cookie::matching::spec::CanonicalHost| clazel_cookie::storage::spec::root_count(rules, out, root) <= clazel_cookie::storage::spec::max_cookies_per_root() by {
            let p = clazel_cookie::storage::spec::in_root(rules, root);
            assert forall|c: clazel_cookie::storage::spec::Cookie| #[trigger] p(f(c)) == p(c) by {
                assert(clazel_cookie::storage::spec::cookie_root_of(rules, f(c)) == clazel_cookie::storage::spec::cookie_root_of(rules, c));
            }
            lemma_map_filter_len(live, f, p);
            assert(clazel_cookie::storage::spec::root_count(rules, live, root) <= clazel_cookie::storage::spec::max_cookies_per_root());
        }
    }
}

/// `document.cookie`'s setter keeps the jar well formed, for a request whose
/// host is not empty.
pub proof fn lemma_jar_wf_store_string(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    s: Seq<u8>,
    url: clazel_cookie::storage::spec::RequestUrl,
    ctx: clazel_cookie::storage::spec::RequestContext,
    now: int,
)
    requires
        jar_wf(rules, jar),
        clazel_cookie::storage::isolation::url_host_nonempty(url),
    ensures
        jar_wf(rules, clazel_cookie::storage::spec::store_a_set_cookie_string(rules, jar, s, url, ctx, now)),
{
    match clazel_cookie::set_cookie::spec::parse_a_set_cookie_string(s, url.path, now) {
        None => lemma_jar_wf_evict_expired(rules, jar, now),
        Some(received) => {
            clazel_cookie::storage::isolation::lemma_store_bounds(rules, jar, url, ctx, received, now);
            clazel_cookie::storage::isolation::lemma_store_preserves_domains_nonempty(rules, jar, url, ctx, received, now);
        },
    }
}

/// The request URL of a renderer that is not cookie-averse has a non-empty
/// host, so the jar calls above apply.
pub proof fn lemma_request_url_host_nonempty(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, r: Renderer)
    requires
        lock_of_url(urls, r.url, r.id) == Some(r.lock),
        !cookie_averse(rules, r.lock),
    ensures
        clazel_cookie::storage::isolation::url_host_nonempty(request_url_of(urls, r)),
{
}


// ---------------------------------------------------------------------
// Web Storage.
// ---------------------------------------------------------------------

/// The size of the first `n` entries is at most that of the first `m`, for
/// `n <= m`.
pub proof fn lemma_entries_size_mono(list: Seq<StorageEntry>, n: nat, m: nat)
    requires
        n <= m <= list.len(),
    ensures
        entries_size(list, n) <= entries_size(list, m),
    decreases m - n,
{
    if n < m {
        lemma_entries_size_mono(list, n, (m - 1) as nat);
    }
}

/// Removing an entry does not grow the map: the size of the first `n'`
/// entries of the shortened list is at most that of the first `n` of the
/// list, where `n'` is `n` less the entry if it is among them.
pub proof fn lemma_entries_size_remove(list: Seq<StorageEntry>, i: int, n: nat)
    requires
        0 <= i < list.len(),
        n <= list.len(),
    ensures
        entries_size(list.remove(i), (if i < n { n - 1 } else { n as int }) as nat) <= entries_size(list, n),
    decreases n,
{
    let r = list.remove(i);
    if n > 0 {
        lemma_entries_size_remove(list, i, (n - 1) as nat);
        if i > n - 1 {
            assert(r[n - 1] == list[n - 1]);
        } else if i == n - 1 {
        } else {
            assert(r[n - 2] == list[n - 1]);
        }
    }
}

/// The empty map is within the quota and has unique keys.
pub proof fn lemma_empty_storage_ok()
    ensures
        within_quota(seq![]),
        storage_keys_unique(seq![]),
{
}

/// `storage_of` is always within the quota and has unique keys, for a
/// well-formed storage.
pub proof fn lemma_storage_of_ok(s: State, lock: clazel_origin::spec::Origin)
    requires
        storage_wf(s.storage),
    ensures
        within_quota(storage_of(s, lock)),
        storage_keys_unique(storage_of(s, lock)),
{
    if !s.storage.dom().contains(lock) {
        lemma_empty_storage_ok();
    }
}

/// Setting the map of a valid tuple origin to a list that is unique and
/// within the quota keeps the storage well formed.
pub proof fn lemma_set_storage_wf(s: State, lock: clazel_origin::spec::Origin, list: Seq<StorageEntry>)
    requires
        storage_wf(s.storage),
        valid_tuple_origin(lock),
        storage_keys_unique(list),
        within_quota(list),
    ensures
        storage_wf(set_storage(s, lock, list).storage),
{
    broadcast use vstd::map::group_map_lemmas;
    let st = set_storage(s, lock, list).storage;
    assert forall|o: clazel_origin::spec::Origin| #[trigger] st.dom().contains(o) implies valid_tuple_origin(o) && st[o].len() > 0
        && storage_keys_unique(st[o]) && within_quota(st[o]) by {
        if list.len() == 0 {
            assert(o != lock);
            assert(s.storage.dom().contains(o));
            assert(st[o] == s.storage[o]);
        } else if o == lock {
            assert(st[o] == list);
        } else {
            assert(s.storage.dom().contains(o));
            assert(st[o] == s.storage[o]);
        }
    }
    assert(st == set_storage(s, lock, list).storage);
    assert(storage_wf(st));
}

/// A `localStorage` call by a renderer with a valid tuple lock keeps the
/// storage well formed.
pub proof fn lemma_storage_call_wf(s: State, r: Renderer, m: clazel_ipc::message::spec::Message)
    requires
        storage_wf(s.storage),
        valid_tuple_origin(r.lock),
    ensures
        storage_wf(storage_call(s, r, m).0.storage),
{
    let list = storage_of(s, r.lock);
    lemma_storage_of_ok(s, r.lock);
    match m {
        clazel_ipc::message::spec::Message::StorageSetItem { key, value } => {
            lemma_find_key(list, key, 0);
            match find_key(list, key, 0) {
                Some(i) => {
                    if list[i].value != value {
                        let new_list = list.update(i, StorageEntry { key, value });
                        assert forall|a: int, b: int| 0 <= a < b < new_list.len() implies (#[trigger] new_list[a]).key
                            != (#[trigger] new_list[b]).key by {
                            if a != i {
                                assert(new_list[a] == list[a]);
                            }
                            if b != i {
                                assert(new_list[b] == list[b]);
                            }
                        }
                        if within_quota(new_list) {
                            lemma_set_storage_wf(s, r.lock, new_list);
                        }
                    }
                },
                None => {
                    let new_list = list.push(StorageEntry { key, value });
                    assert forall|a: int, b: int| 0 <= a < b < new_list.len() implies (#[trigger] new_list[a]).key
                        != (#[trigger] new_list[b]).key by {
                        if b < list.len() {
                            assert(new_list[a] == list[a]);
                            assert(new_list[b] == list[b]);
                        } else {
                            assert(new_list[a] == list[a]);
                        }
                    }
                    if within_quota(new_list) {
                        lemma_set_storage_wf(s, r.lock, new_list);
                    }
                },
            }
        },
        clazel_ipc::message::spec::Message::StorageRemoveItem { key } => {
            lemma_find_key(list, key, 0);
            if let Some(i) = find_key(list, key, 0) {
                let new_list = list.remove(i);
                assert forall|a: int, b: int| 0 <= a < b < new_list.len() implies (#[trigger] new_list[a]).key
                    != (#[trigger] new_list[b]).key by {
                    let ma = if a < i { a } else { a + 1 };
                    let mb = if b < i { b } else { b + 1 };
                    assert(new_list[a] == list[ma]);
                    assert(new_list[b] == list[mb]);
                }
                lemma_entries_size_remove(list, i, list.len());
                lemma_set_storage_wf(s, r.lock, new_list);
            }
        },
        clazel_ipc::message::spec::Message::StorageClear => {
            lemma_empty_storage_ok();
            lemma_set_storage_wf(s, r.lock, seq![]);
        },
        _ => {},
    }
}


// ---------------------------------------------------------------------
// `step` preserves `kernel_wf`.
// ---------------------------------------------------------------------

/// `navigate_tab` (a `NavigateTab`, and a renderer's `Navigate`) keeps the
/// invariant.
pub proof fn lemma_navigate_tab_wf(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    s: State,
    tab: nat,
    url: Seq<u32>,
    script: Seq<u8>,
)
    requires
        kernel_wf(rules, urls, s),
    ensures
        kernel_wf(rules, urls, navigate_tab(urls, s, tab, url, script).0),
{
    lemma_find_by_tab(s.renderers, tab, 0);
    if let Some(i) = find_by_tab(s.renderers, tab, 0) {
        let old = s.renderers[i];
        if let Some(lock) = lock_of_url(urls, url, s.next_id) {
            if lock is Tuple && lock == old.lock {
                let r = Renderer { url, pending: None, ..old };
                // `lock` is `old.lock`, a tuple, so the origin of `url` is that tuple
                // whatever id the lock is asked for.
                assert(lock_of_url(urls, url, old.id) == Some(old.lock));
                lemma_renderers_wf_update(urls, s.renderers, s.next_id, i, r, s.next_id);
            } else {
                let id = s.next_id;
                let r = Renderer { id, tab, url, lock, pending: None };
                lemma_renderers_wf_update(urls, s.renderers, s.next_id, i, r, id + 1);
            }
        }
    }
}

/// `begin_navigation` (a `NavigateTab`, and a renderer's `Navigate`) keeps
/// the invariant: it only records the URL the renderer is navigating to.
pub proof fn lemma_begin_navigation_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, s: State, tab: nat, url: Seq<u32>)
    requires
        kernel_wf(rules, urls, s),
    ensures
        kernel_wf(rules, urls, begin_navigation(urls, s, tab, url).0),
{
    lemma_find_by_tab(s.renderers, tab, 0);
    if let Some(i) = find_by_tab(s.renderers, tab, 0) {
        if lock_of_url(urls, url, s.next_id) is Some {
            let old = s.renderers[i];
            assert(lock_of_url(urls, old.url, old.id) == Some(old.lock));
            let r = Renderer { pending: Some(url), ..old };
            lemma_renderers_wf_update(urls, s.renderers, s.next_id, i, r, s.next_id);
        }
    }
}

/// One `Set-Cookie` line of a fetch keeps the jar well formed and free of
/// public-suffix domains: it is stored only for a request whose host is not
/// empty and not a public suffix ([`store_allowed`]).
pub proof fn lemma_store_one_wf(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, st: HttpStore, now: int)
    requires
        jar_wf(rules, jar),
        jar_no_public_suffix(rules, jar),
    ensures
        jar_wf(rules, store_one(rules, jar, st, now)),
        jar_no_public_suffix(rules, store_one(rules, jar, st, now)),
{
    if store_allowed(rules, st.url) {
        let host = st.url.host->Some_0;
        assert(st.url.host == Some(host));
        lemma_jar_wf_store_string(rules, jar, st.line, st.url, st.ctx, now);
        crate::unwind_base::lemma_store_no_public_suffix(rules, jar, st.line, st.url, st.ctx, now, host);
    }
}

/// The `Set-Cookie` lines of a fetch keep the jar well formed and free of
/// public-suffix domains.
pub proof fn lemma_apply_stores_wf(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, stores: Seq<HttpStore>, now: int)
    requires
        jar_wf(rules, jar),
        jar_no_public_suffix(rules, jar),
    ensures
        jar_wf(rules, apply_stores(rules, jar, stores, now)),
        jar_no_public_suffix(rules, apply_stores(rules, jar, stores, now)),
    decreases stores.len(),
{
    if stores.len() > 0 {
        let jar1 = store_one(rules, jar, stores[0], now);
        lemma_store_one_wf(rules, jar, stores[0], now);
        lemma_apply_stores_wf(rules, jar1, stores.drop_first(), now);
    }
}

/// A navigation that ends without a commit keeps the invariant.
pub proof fn lemma_fail_navigation_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, s: State, i: int, old: Renderer, code: u64)
    requires
        kernel_wf(rules, urls, s),
        0 <= i < s.renderers.len(),
        old == s.renderers[i],
    ensures
        kernel_wf(rules, urls, fail_navigation(s, i, old, code).0),
{
    assert(lock_of_url(urls, old.url, old.id) == Some(old.lock));
    lemma_renderers_wf_update(urls, s.renderers, s.next_id, i, Renderer { pending: None, ..old }, s.next_id);
}

/// `fetched` keeps the invariant.
pub proof fn lemma_fetched_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, outcome: NetOutcome)
    requires
        kernel_wf(rules, urls, s),
    ensures
        kernel_wf(rules, urls, fetched(rules, urls, fetch, s, tab, outcome).0),
{
    lemma_find_by_tab(s.renderers, tab, 0);
    if let Some(run) = fetched_run(fetch, s, tab, outcome) {
        let i = find_by_tab(s.renderers, tab, 0)->Some_0;
        let old = s.renderers[i];
        let jar1 = apply_stores(rules, s.jar, run.stores, s.now);
        lemma_apply_stores_wf(rules, s.jar, run.stores, s.now);
        let s1 = State { jar: jar1, ..s };
        assert(kernel_wf(rules, urls, s1));
        match run.result {
            FetchResult::Done { url, body } => {
                if clazel_encoding::utf8::spec::all_scalar_values(url) && lock_of_url(urls, url, s1.next_id) is Some {
                    lemma_navigate_tab_wf(rules, urls, s1, tab, url, body);
                } else {
                    lemma_fail_navigation_wf(rules, urls, s1, i, old, error_bad_url());
                }
            },
            FetchResult::Failed => {
                lemma_fail_navigation_wf(rules, urls, s1, i, old, error_fetch());
            },
        }
    }
}

/// **`step` preserves `kernel_wf`.** For every Public Suffix List, every
/// instantiation of the URL functions, every state satisfying the invariant
/// and every event.
pub proof fn lemma_step_preserves_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        kernel_wf(rules, urls, s),
    ensures
        kernel_wf(rules, urls, step(rules, urls, fetch, s, e).0),
{
    crate::unwind_base::lemma_jar_no_public_suffix_step(rules, urls, fetch, s, e);
    match e {
        Event::Tick { time } => {
            let now = if time > s.now { time } else { s.now };
            lemma_jar_wf_evict_expired(rules, s.jar, now);
        },
        Event::RendererExited { id } => {
            lemma_find_by_id(s.renderers, id, 0);
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                lemma_renderers_wf_remove(urls, s.renderers, s.next_id, i);
            }
        },
        Event::OpenTab { url, script } => {
            let id = s.next_id;
            if let Some(lock) = lock_of_url(urls, url, id) {
                lemma_renderers_wf_push(urls, s.renderers, s.next_id, Renderer { id, tab: id, url, lock, pending: None });
            }
        },
        Event::NavigateTab { tab, url } => {
            lemma_begin_navigation_wf(rules, urls, s, tab, url);
        },
        Event::Fetched { tab, outcome } => {
            lemma_fetched_wf(rules, urls, fetch, s, tab, outcome);
        },
        Event::FromRenderer { id, bytes } => {
            lemma_find_by_id(s.renderers, id, 0);
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                let r = s.renderers[i];
                assert(lock_of_url(urls, r.url, r.id) == Some(r.lock));
                match decode_renderer_frame(bytes) {
                    None => lemma_renderers_wf_remove(urls, s.renderers, s.next_id, i),
                    Some(m) => match m {
                        clazel_ipc::message::spec::Message::CookieGet => {
                            if !cookie_averse(rules, r.lock) {
                                let url = request_url_of(urls, r);
                                lemma_jar_wf_retrieval(rules, s.jar, url, document_context(r.lock), s.now);
                            }
                        },
                        clazel_ipc::message::spec::Message::CookieSet { cookie_string } => {
                            if !cookie_averse(rules, r.lock) {
                                let url = request_url_of(urls, r);
                                lemma_request_url_host_nonempty(rules, urls, r);
                                lemma_jar_wf_store_string(rules, s.jar, cookie_string, url, document_context(r.lock), s.now);
                            }
                        },
                        clazel_ipc::message::spec::Message::StorageGetItem { .. }
                        | clazel_ipc::message::spec::Message::StorageSetItem { .. }
                        | clazel_ipc::message::spec::Message::StorageRemoveItem { .. }
                        | clazel_ipc::message::spec::Message::StorageClear
                        | clazel_ipc::message::spec::Message::StorageKey { .. }
                        | clazel_ipc::message::spec::Message::StorageLength => {
                            if r.lock is Tuple {
                                lemma_lock_valid(urls, r.url, r.id, r.lock);
                                lemma_storage_call_wf(s, r, m);
                            }
                        },
                        clazel_ipc::message::spec::Message::Navigate { url } => {
                            if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                                if let Some(resolved) = (urls.resolve)(r.url, relative) {
                                    if lock_of_url(urls, resolved, s.next_id) is Some {
                                        lemma_begin_navigation_wf(rules, urls, s, r.tab, resolved);
                                    }
                                }
                            }
                        },
                        _ => {},
                    },
                }
            }
        },
    }
}

/// Running a trace from a state that satisfies the invariant ends in one
/// that does.
pub proof fn lemma_run_state_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, t: Seq<Event>)
    requires
        kernel_wf(rules, urls, s),
    ensures
        kernel_wf(rules, urls, run_state(rules, urls, fetch, s, t)),
    decreases t.len(),
{
    if t.len() > 0 {
        lemma_step_preserves_wf(rules, urls, fetch, s, t[0]);
        lemma_run_state_wf(rules, urls, fetch, step(rules, urls, fetch, s, t[0]).0, t.drop_first());
    }
}

/// **Every reachable state satisfies the invariant.**
pub proof fn lemma_reachable_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        kernel_wf(rules, urls, s),
{
    lemma_init_wf(rules, urls);
    let t = choose|t: Seq<Event>| run_state(rules, urls, fetch, init_state(), t) == s;
    lemma_run_state_wf(rules, urls, fetch, init_state(), t);
}

} // verus!
