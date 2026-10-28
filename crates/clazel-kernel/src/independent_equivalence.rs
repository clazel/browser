//! The independent transcription (`independent.rs`, written by a separate
//! agent from the HTML Standard without reading `spec.rs`) of HTML's
//! `document.cookie` getter and setter and of the Web Storage methods the
//! kernel uses, **proven equal** to what the kernel does (item 2.11).
//!
//! The class on which they are equal: the lock's host is not a public suffix
//! (the kernel makes documents on public-suffix hosts cookie-averse, as
//! Chrome and Firefox do; HTML has no such condition, so there the two
//! deliberately differ), a renderer's document is a top-level
//! document whose URL is built as the kernel builds it (`request_url_of`: the
//! lock's scheme and host, the committed URL's path), and the lock's scheme
//! is an ASCII string (an origin's scheme is "an ASCII string"). Under it
//! HTML's cookie-averse test on the URL's scheme and the kernel's on the
//! lock agree, and the opaque-origin `SecurityError` branch is never reached
//! for a document that is not cookie-averse (an opaque lock has the empty
//! scheme). The storage side is equal for any state, with the quota the
//! kernel uses as HTML's implementation-defined limit.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// document.cookie.
// ---------------------------------------------------------------------

/// The independent transcription's document for a renderer.
pub open spec fn doc_of(urls: UrlFns, r: Renderer) -> crate::independent::Document {
    crate::independent::Document { url: request_url_of(urls, r), origin: r.lock }
}

/// The lock's scheme is ASCII.
pub open spec fn lock_scheme_ascii(lock: clazel_origin::spec::Origin) -> bool {
    forall|i: int| 0 <= i < lock_scheme(lock).len() ==> (#[trigger] lock_scheme(lock)[i]) < 128
}

/// `narrow` of an ASCII string is `narrow` of another exactly when they are equal.
pub proof fn lemma_narrow_ascii(a: Seq<u32>, b: Seq<u32>)
    requires
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]) < 128,
        forall|i: int| 0 <= i < b.len() ==> (#[trigger] b[i]) < 128,
    ensures
        (clazel_cookie::matching::spec::narrow(a) == clazel_cookie::matching::spec::narrow(b)) == (a == b),
{
    if clazel_cookie::matching::spec::narrow(a) == clazel_cookie::matching::spec::narrow(b) {
        assert(clazel_cookie::matching::spec::narrow(a).len() == a.len());
        assert(clazel_cookie::matching::spec::narrow(b).len() == b.len());
        assert(a.len() == b.len());
        assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
            assert(clazel_cookie::matching::spec::narrow(a)[i] == a[i] as u8);
            assert(clazel_cookie::matching::spec::narrow(b)[i] == b[i] as u8);
        }
        assert(a =~= b);
    }
}

/// HTML's cookie-averse test on the document's URL scheme is the kernel's on the lock.
pub proof fn lemma_cookie_averse_equal(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, r: Renderer)
    requires
        lock_scheme_ascii(r.lock),
        !lock_on_public_suffix(rules, r.lock),
    ensures
        crate::independent::cookie_averse(doc_of(urls, r)) == cookie_averse(rules, r.lock),
{
    let sc = lock_scheme(r.lock);
    let n = clazel_cookie::matching::spec::narrow(sc);
    assert(clazel_cookie::matching::spec::narrow(clazel_url::url::spec::http_str()) =~= crate::independent::scheme_http());
    assert(clazel_cookie::matching::spec::narrow(clazel_url::url::spec::https_str()) =~= crate::independent::scheme_https());
    lemma_narrow_ascii(sc, clazel_url::url::spec::http_str());
    lemma_narrow_ascii(sc, clazel_url::url::spec::https_str());
    if r.lock is Opaque {
        assert(sc =~= Seq::<u32>::empty());
        assert(n =~= Seq::<u8>::empty());
    }
}

/// **The getter.** For a renderer on a lock of ASCII scheme the independent
/// `document.cookie` getter returns what the kernel replies, and leaves the
/// jar as the kernel does.
pub proof fn lemma_independent_cookie_get(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, r: Renderer)
    requires
        lock_scheme_ascii(r.lock),
        !lock_on_public_suffix(rules, r.lock),
    ensures
        ({
            let (res, jar2) = crate::independent::document_cookie_get(rules, doc_of(urls, r), s.jar, s.now);
            res is Value && handle_message(rules, urls, fetch, s, r, clazel_ipc::message::spec::Message::CookieGet) == (State { jar: jar2, ..s }, reply(
                r,
                clazel_ipc::message::spec::Message::CookieValue { cookie_string: res->Value_0 },
            ))
        }),
{
    lemma_cookie_averse_equal(rules, urls, r);
    if !cookie_averse(rules, r.lock) {
        assert(r.lock is Tuple);
    }
}

/// **The setter.** The independent `document.cookie` setter leaves the jar as the kernel does.
pub proof fn lemma_independent_cookie_set(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, r: Renderer, cs: Seq<u8>)
    requires
        lock_scheme_ascii(r.lock),
        !lock_on_public_suffix(rules, r.lock),
    ensures
        ({
            let (res, jar2) = crate::independent::document_cookie_set(rules, doc_of(urls, r), s.jar, cs, s.now);
            res is Done && handle_message(rules, urls, fetch, s, r, clazel_ipc::message::spec::Message::CookieSet { cookie_string: cs }) == (
                State { jar: jar2, ..s },
                Seq::<Output>::empty(),
            )
        }),
{
    lemma_cookie_averse_equal(rules, urls, r);
    if !cookie_averse(rules, r.lock) {
        assert(r.lock is Tuple);
    }
}

// ---------------------------------------------------------------------
// Web Storage.
// ---------------------------------------------------------------------

/// The independent transcription's map for the kernel's list.
pub open spec fn view_list(list: Seq<StorageEntry>) -> crate::independent::StorageMap {
    crate::independent::StorageMap { entries: list.map_values(|e: StorageEntry| crate::independent::Entry { key: e.key, value: e.value }) }
}

/// The kernel's key search is the independent one on the view.
pub proof fn lemma_find_key_view(list: Seq<StorageEntry>, key: Seq<u8>, i: nat)
    ensures
        match find_key(list, key, i) {
            Some(k) => crate::independent::find_key_from(view_list(list).entries, key, i) == Some(k as nat),
            None => crate::independent::find_key_from(view_list(list).entries, key, i) is None,
        },
    decreases list.len() - i,
{
    let v = view_list(list).entries;
    assert(v.len() == list.len());
    if i < list.len() {
        assert(v[i as int].key == list[i as int].key);
        if list[i as int].key != key {
            lemma_find_key_view(list, key, i + 1);
        }
    }
}

/// The kernel's size of a prefix is the independent size of the prefix.
pub proof fn lemma_entries_size_view(list: Seq<StorageEntry>, n: nat)
    requires
        n <= list.len(),
    ensures
        entries_size(list, n) == crate::independent::entries_size(view_list(list).entries.subrange(0, n as int)),
    decreases n,
{
    let v = view_list(list).entries;
    if n > 0 {
        lemma_entries_size_view(list, (n - 1) as nat);
        assert(v.subrange(0, n as int).drop_last() =~= v.subrange(0, (n - 1) as int));
        assert(v.subrange(0, n as int)[n - 1] == v[n - 1]);
        assert(v[n - 1].key == list[n - 1].key && v[n - 1].value == list[n - 1].value);
    }
}

/// The kernel's quota is the independent one with the same limit.
pub proof fn lemma_quota_view(list: Seq<StorageEntry>)
    ensures
        within_quota(list) == crate::independent::can_be_stored(view_list(list), max_storage_size()),
{
    lemma_entries_size_view(list, list.len());
    assert(view_list(list).entries.subrange(0, list.len() as int) =~= view_list(list).entries);
}

/// The view of an updated list.
pub proof fn lemma_view_update(list: Seq<StorageEntry>, i: int, e: StorageEntry)
    requires
        0 <= i < list.len(),
    ensures
        view_list(list.update(i, e)) == (crate::independent::StorageMap { entries: view_list(list).entries.update(i, crate::independent::Entry { key: e.key, value: e.value }) }),
{
    assert(view_list(list.update(i, e)).entries =~= view_list(list).entries.update(i, crate::independent::Entry { key: e.key, value: e.value }));
}

/// The view of a list with an entry pushed.
pub proof fn lemma_view_push(list: Seq<StorageEntry>, e: StorageEntry)
    ensures
        view_list(list.push(e)) == (crate::independent::StorageMap { entries: view_list(list).entries.push(crate::independent::Entry { key: e.key, value: e.value }) }),
{
    assert(view_list(list.push(e)).entries =~= view_list(list).entries.push(crate::independent::Entry { key: e.key, value: e.value }));
}

/// The view of a list with an entry removed.
pub proof fn lemma_view_remove(list: Seq<StorageEntry>, i: int)
    requires
        0 <= i < list.len(),
    ensures
        view_list(list.remove(i)) == (crate::independent::StorageMap { entries: view_list(list).entries.remove(i) }),
{
    assert(view_list(list.remove(i)).entries =~= view_list(list).entries.remove(i));
}

/// **`getItem`, `key` and `length`.**
pub proof fn lemma_independent_storage_reads(s: State, r: Renderer, key: Seq<u8>, index: u64)
    ensures
        ({
            let m = view_list(storage_of(s, r.lock));
            &&& storage_call(s, r, clazel_ipc::message::spec::Message::StorageGetItem { key }) == (s, reply(
                r,
                clazel_ipc::message::spec::Message::StorageValue { value: crate::independent::storage_get_item(m, key) },
            ))
            &&& storage_call(s, r, clazel_ipc::message::spec::Message::StorageKey { index }) == (s, reply(
                r,
                clazel_ipc::message::spec::Message::StorageValue { value: crate::independent::storage_key(m, index as nat) },
            ))
            &&& storage_call(s, r, clazel_ipc::message::spec::Message::StorageLength) == (s, reply(
                r,
                clazel_ipc::message::spec::Message::StorageLengthValue { length: crate::independent::storage_length(m) as u64 },
            ))
        }),
{
    let list = storage_of(s, r.lock);
    lemma_find_key_view(list, key, 0);
    crate::invariant::lemma_find_key(list, key, 0);
    let v = view_list(list).entries;
    assert(v.len() == list.len());
    if (index as int) < list.len() {
        assert(crate::independent::get_the_keys(view_list(list))[index as int] == list[index as int].key);
    }
}

/// **`setItem`.** The independent method with the kernel's quota as the
/// limit: on success the kernel stores the new map and replies nothing; on
/// the quota exception it replies with the quota error and keeps the map.
pub proof fn lemma_independent_storage_set(s: State, r: Renderer, key: Seq<u8>, value: Seq<u8>)
    ensures
        ({
            let list = storage_of(s, r.lock);
            let (m2, res) = crate::independent::storage_set_item(view_list(list), key, value, max_storage_size());
            let out = storage_call(s, r, clazel_ipc::message::spec::Message::StorageSetItem { key, value });
            match res {
                crate::independent::SetItemResult::Done => out.1 == Seq::<Output>::empty() && view_list(storage_of(out.0, r.lock)) == m2 && out.0.renderers == s.renderers,
                crate::independent::SetItemResult::QuotaExceeded => out.0 == s && out.1 == reply(r, clazel_ipc::message::spec::Message::Error { code: error_quota() }),
            }
        }),
{
    let list = storage_of(s, r.lock);
    lemma_find_key_view(list, key, 0);
    crate::invariant::lemma_find_key(list, key, 0);
    match find_key(list, key, 0) {
        Some(i) => {
            if list[i].value != value {
                let nl = list.update(i, StorageEntry { key, value });
                lemma_view_update(list, i, StorageEntry { key, value });
                lemma_quota_view(nl);
                if within_quota(nl) {
                    lemma_set_storage_view(s, r.lock, nl);
                }
            }
        },
        None => {
            let nl = list.push(StorageEntry { key, value });
            lemma_view_push(list, StorageEntry { key, value });
            lemma_quota_view(nl);
            if within_quota(nl) {
                lemma_set_storage_view(s, r.lock, nl);
            }
        },
    }
}

/// A nonempty list is what `set_storage` stores; the empty one removes the key.
pub proof fn lemma_set_storage_view(s: State, lock: clazel_origin::spec::Origin, list: Seq<StorageEntry>)
    ensures
        storage_of(set_storage(s, lock, list), lock) == list,
{
    if list.len() == 0 {
        assert(list =~= Seq::<StorageEntry>::empty());
    }
}

/// **`removeItem`.**
pub proof fn lemma_independent_storage_remove(s: State, r: Renderer, key: Seq<u8>)
    ensures
        storage_call(s, r, clazel_ipc::message::spec::Message::StorageRemoveItem { key }).1 == Seq::<Output>::empty(),
        view_list(storage_of(storage_call(s, r, clazel_ipc::message::spec::Message::StorageRemoveItem { key }).0, r.lock)) == crate::independent::storage_remove_item(
            view_list(storage_of(s, r.lock)),
            key,
        ),
{
    let list = storage_of(s, r.lock);
    lemma_find_key_view(list, key, 0);
    crate::invariant::lemma_find_key(list, key, 0);
    if let Some(i) = find_key(list, key, 0) {
        lemma_view_remove(list, i);
        lemma_set_storage_view(s, r.lock, list.remove(i));
        assert(crate::independent::find_key(view_list(list), key) == Some(i as nat));
    }
}

/// **`clear`.**
pub proof fn lemma_independent_storage_clear(s: State, r: Renderer)
    ensures
        storage_call(s, r, clazel_ipc::message::spec::Message::StorageClear).1 == Seq::<Output>::empty(),
        view_list(storage_of(storage_call(s, r, clazel_ipc::message::spec::Message::StorageClear).0, r.lock)) == crate::independent::storage_clear(
            view_list(storage_of(s, r.lock)),
        ),
{
    let list = storage_of(s, r.lock);
    lemma_set_storage_view(s, r.lock, Seq::<StorageEntry>::empty());
    assert(view_list(Seq::<StorageEntry>::empty()).entries =~= Seq::<crate::independent::Entry>::empty());
    assert(view_list(list).entries.len() == list.len());
    assert(view_list(storage_of(set_storage(s, r.lock, Seq::<StorageEntry>::empty()), r.lock)) == crate::independent::StorageMap { entries: Seq::<crate::independent::Entry>::empty() });
    if list.len() == 0 {
        assert(list =~= Seq::<StorageEntry>::empty());
        assert(list == Seq::<StorageEntry>::empty());
    }
}

/// **`localStorage`'s origin check.** The kernel answers a storage call of an
/// opaque lock with the `SecurityError`, and serves any other.
pub proof fn lemma_independent_local_storage(lock: clazel_origin::spec::Origin)
    ensures
        (crate::independent::local_storage_access(lock) is SecurityError) == (lock is Opaque),
{
}

} // verus!
