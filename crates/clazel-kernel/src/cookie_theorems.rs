//! `theorem_cookie_confidentiality`, `theorem_cookie_integrity` and
//! `theorem_storage_same_origin` (item 2.11).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Sorting keeps the cookies.
// ---------------------------------------------------------------------

/// A cookie of `insert_sorted(sorted, c)` is `c` or was in `sorted`.
pub proof fn lemma_insert_sorted_contains(sorted: Seq<clazel_cookie::storage::spec::Cookie>, c: clazel_cookie::storage::spec::Cookie, x: clazel_cookie::storage::spec::Cookie)
    requires
        clazel_cookie::storage::spec::insert_sorted(sorted, c).contains(x),
    ensures
        x == c || sorted.contains(x),
    decreases sorted.len(),
{
    if sorted.len() == 0 {
        assert(clazel_cookie::storage::spec::insert_sorted(sorted, c) == seq![c]);
        assert(clazel_cookie::storage::spec::insert_sorted(sorted, c)[0] == c);
    } else if clazel_cookie::storage::spec::cookie_listed_before(c, sorted[0]) {
        let l = clazel_cookie::storage::spec::insert_sorted(sorted, c);
        assert(l == seq![c] + sorted);
        let k = choose|k: int| 0 <= k < l.len() && l[k] == x;
        if k > 0 {
            assert(sorted[k - 1] == x);
        }
    } else {
        let rest = sorted.skip(1);
        let l = clazel_cookie::storage::spec::insert_sorted(sorted, c);
        assert(l == seq![sorted[0]] + clazel_cookie::storage::spec::insert_sorted(rest, c));
        let k = choose|k: int| 0 <= k < l.len() && l[k] == x;
        if k == 0 {
            assert(sorted[0] == x);
        } else {
            let inner = clazel_cookie::storage::spec::insert_sorted(rest, c);
            assert(inner[k - 1] == x);
            assert(inner.contains(x));
            lemma_insert_sorted_contains(rest, c, x);
            if rest.contains(x) {
                let m = choose|m: int| 0 <= m < rest.len() && rest[m] == x;
                assert(sorted[m + 1] == x);
            }
        }
    }
}

/// A cookie of the sorted list was in the list.
pub proof fn lemma_sort_from_contains(
    list: Seq<clazel_cookie::storage::spec::Cookie>,
    i: nat,
    sorted: Seq<clazel_cookie::storage::spec::Cookie>,
    x: clazel_cookie::storage::spec::Cookie,
)
    requires
        clazel_cookie::storage::spec::sort_from(list, i, sorted).contains(x),
    ensures
        sorted.contains(x) || (exists|k: int| i <= k < list.len() && list[k] == x),
    decreases list.len() - i,
{
    if i < list.len() {
        let next = clazel_cookie::storage::spec::insert_sorted(sorted, list[i as int]);
        lemma_sort_from_contains(list, i + 1, next, x);
        if next.contains(x) {
            lemma_insert_sorted_contains(sorted, list[i as int], x);
            if x == list[i as int] {
                assert(list[i as int] == x);
            }
        }
    }
}

// ---------------------------------------------------------------------
// theorem_cookie_confidentiality
// ---------------------------------------------------------------------

/// A renderer of a well-formed table with a tuple lock has a lock host.
pub proof fn lemma_tuple_lock_host(urls: UrlFns, rs: Seq<Renderer>, next_id: nat, i: int)
    requires
        crate::invariant::renderers_wf(urls, rs, next_id),
        0 <= i < rs.len(),
        rs[i].lock is Tuple,
    ensures
        lock_host(rs[i].lock) is Some,
{
    let r = rs[i];
    assert(lock_of_url(urls, r.url, r.id) == Some(r.lock));
    assert(valid_tuple_origin(r.lock));
}

/// **`theorem_cookie_confidentiality`.**
pub proof fn theorem_cookie_confidentiality(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::cookie_confidentiality_statement(rules, urls, fetch, s, id, bytes),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
    if let Some(i) = find_by_id(s.renderers, id, 0) {
        let r = s.renderers[i];
        if let Some(clazel_ipc::message::spec::Message::CookieGet) = decode_renderer_frame(bytes) {
            if !cookie_averse(rules, r.lock) {
                lemma_tuple_lock_host(urls, s.renderers, s.next_id, i);
                let live = clazel_cookie::storage::spec::evict_expired(s.jar, s.now);
                let url = request_url_of(urls, r);
                let ctx = document_context(r.lock);
                let host = lock_host(r.lock)->Some_0;
                let list = clazel_cookie::storage::spec::retrieval_cookie_list(rules, live, url, ctx);
                let p = |c: clazel_cookie::storage::spec::Cookie| clazel_cookie::storage::spec::cookie_is_retrieved(rules, url, ctx, host, c);
                assert forall|k: int| 0 <= k < list.len() implies (!(#[trigger] list[k]).http_only_flag && lock_host(r.lock) is Some
                    && clazel_cookie::storage::spec::cookie_is_retrieved(rules, url, ctx, host, list[k])
                    && live.contains(list[k])) by {
                    let x = list[k];
                    assert(list.contains(x));
                    assert(url.host == Some(host));
                    lemma_sort_from_contains(live.filter(p), 0, seq![], x);
                    assert(live.filter(p).contains(x));
                    clazel_cookie::storage::isolation::lemma_filter_elem(live, p, x);
                    assert(clazel_cookie::storage::spec::is_non_http(ctx));
                }
            }
        }
    }
}

// ---------------------------------------------------------------------
// theorem_cookie_integrity
// ---------------------------------------------------------------------

/// **`theorem_cookie_integrity`.**
pub proof fn theorem_cookie_integrity(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::cookie_integrity_statement(rules, urls, fetch, s, e),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    match e {
        Event::FromRenderer { id, bytes } => {
            crate::invariant::lemma_find_by_id(s.renderers, id, 0);
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                let r = s.renderers[i];
                if let Some(m) = decode_renderer_frame(bytes) {
                    crate::lock::lemma_storage_call_frame(s, r, m);
                    if let clazel_ipc::message::spec::Message::Navigate { url } = m {
                        if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                            if let Some(resolved) = (urls.resolve)(r.url, relative) {
                                if lock_of_url(urls, resolved, s.next_id) is Some {
                                    crate::unwind_base::lemma_navigation_frame(urls, s, r.tab, resolved, seq![]);
                                }
                            }
                        }
                    }
                }
            }
        },
        Event::Fetched { tab, outcome } => {
            crate::unwind_base::lemma_fetched_frame(rules, urls, fetch, s, tab, outcome);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------
// theorem_storage_same_origin
// ---------------------------------------------------------------------

/// The outputs of a storage call, and the map of its lock afterwards, are a
/// function of the lock's map and the renderer's id.
pub proof fn lemma_storage_call_local(s: State, s2: State, r: Renderer, r2: Renderer, m: clazel_ipc::message::spec::Message)
    requires
        r.id == r2.id,
        r.lock == r2.lock,
        storage_of(s, r.lock) == storage_of(s2, r.lock),
    ensures
        storage_call(s, r, m).1 == storage_call(s2, r2, m).1,
        storage_of(storage_call(s, r, m).0, r.lock) == storage_of(storage_call(s2, r2, m).0, r.lock),
        forall|o: clazel_origin::spec::Origin| o != r.lock ==> storage_of(storage_call(s, r, m).0, o) == storage_of(s, o),
{
    let list = storage_of(s, r.lock);
    match m {
        clazel_ipc::message::spec::Message::StorageSetItem { key, value } => {
            match find_key(list, key, 0) {
                Some(i) => {},
                None => {},
            }
        },
        _ => {},
    }
}

/// **`theorem_storage_same_origin`.**
pub proof fn theorem_storage_same_origin(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, s2: State, id: nat, bytes: Seq<u8>)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::storage_same_origin_statement(rules, urls, fetch, s, s2, id, bytes),
{
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
    crate::invariant::lemma_find_by_id(s2.renderers, id, 0);
    if let (Some(i), Some(i2)) = (find_by_id(s.renderers, id, 0), find_by_id(s2.renderers, id, 0)) {
        let r = s.renderers[i];
        let r2 = s2.renderers[i2];
        if let Some(m) = decode_renderer_frame(bytes) {
            if crate::statements::is_storage_message(m) && r.lock is Tuple {
                crate::lock::lemma_storage_call_frame(s, r, m);
                if r2.lock == r.lock && storage_of(s2, r.lock) == storage_of(s, r.lock) {
                    lemma_storage_call_local(s, s2, r, r2, m);
                    crate::lock::lemma_storage_call_frame(s2, r2, m);
                }
            }
        }
    }
}

} // verus!
