//! Lemmas the kill certificates of `mutations.json` instantiate: small
//! consequences of `spec.rs` that item 2.11's theorems rest on, phrased so
//! that a concrete instance can be evaluated by Verus's `compute_only`
//! (which evaluates sequences and enums but not maps or quantifiers).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A renderer with the given id and lock, committed to the URL `a`.
pub open spec fn ml_renderer(id: nat, lock: clazel_origin::spec::Origin) -> Renderer {
    Renderer { id, tab: id, url: seq![0x61u32], lock, pending: None }
}

/// A tuple origin of host `a` with the given scheme.
pub open spec fn ml_tuple(scheme: Seq<u32>) -> clazel_origin::spec::Origin {
    clazel_origin::spec::Origin::Tuple { scheme, host: clazel_url::host::spec::Host::Domain(seq![0x61u32]), port: None, domain: None }
}

/// URL functions under which every URL has the tuple origin of scheme `a`.
pub open spec fn ml_urls_a() -> UrlFns {
    UrlFns {
        origin_of: |u: Seq<u32>| Some(ml_tuple(seq![0x61u32])),
        path_of: |u: Seq<u32>| Seq::<u8>::empty(),
        resolve: |b: Seq<u32>, i: Seq<u32>| None::<Seq<u32>>,
    }
}

/// A state with one renderer (id 0, opaque lock 0) and counter 1.
pub open spec fn ml_state_one() -> State {
    State {
        renderers: seq![ml_renderer(0, clazel_origin::spec::Origin::Opaque(0nat))],
        jar: Seq::empty(),
        storage: Map::empty(),
        next_id: 1,
        now: 0,
    }
}

/// A reply names its sender and carries exactly the frame of its message.
pub proof fn ml_reply_for_sender(r: Renderer, m: clazel_ipc::message::spec::Message)
    ensures
        reply(r, m).len() == 1,
        reply(r, m)[0] == (Output::ToRenderer { id: r.id, bytes: reply_frame(m) }),
{
}

/// The request URL of a cookie call has the lock's scheme.
pub proof fn ml_request_scheme(urls: UrlFns, r: Renderer)
    ensures
        request_url_of(urls, r).scheme == clazel_cookie::matching::spec::narrow(lock_scheme(r.lock)),
{
}

/// A cookie call from a document is a "non-HTTP" API call.
pub proof fn ml_document_context_non_http(lock: clazel_origin::spec::Origin)
    ensures
        clazel_cookie::storage::spec::is_non_http(document_context(lock)),
{
}

/// A tuple lock of scheme `ftp` is cookie-averse, whatever its host.
pub proof fn ml_ftp_is_cookie_averse(on_public_suffix: bool)
    ensures
        cookie_averse_given(ml_tuple(seq![0x66u32, 0x74, 0x70]), on_public_suffix),
{
}

/// A document on a public-suffix host is cookie-averse: the getter returns
/// the empty string and the setter does nothing (so no cookie with a
/// public-suffix domain is ever created, and RFC 6265bis §5.7 step 16 never
/// reads across cookie roots). `cookie_averse(rules, lock)` is
/// `cookie_averse_given(lock, lock_on_public_suffix(rules, lock))`.
pub proof fn ml_public_suffix_is_cookie_averse(lock: clazel_origin::spec::Origin)
    ensures
        cookie_averse_given(lock, true),
{
}

/// Navigating to a different lock gives the new renderer that lock.
pub proof fn ml_navigate_new_lock(urls: UrlFns, s: State, tab: nat, url: Seq<u32>, script: Seq<u8>, i: int, l: clazel_origin::spec::Origin)
    requires
        0 <= i < s.renderers.len(),
        find_by_tab(s.renderers, tab, 0) == Some(i),
        lock_of_url(urls, url, s.next_id) == Some(l),
        !(l is Tuple && l == s.renderers[i].lock),
    ensures
        navigate_tab(urls, s, tab, url, script).0.renderers[i].lock == l,
{
}

/// The `Commit` to a spawned renderer is for the URL and script given.
pub proof fn ml_navigate_commit(urls: UrlFns, s: State, tab: nat, url: Seq<u32>, script: Seq<u8>, i: int, l: clazel_origin::spec::Origin)
    requires
        0 <= i < s.renderers.len(),
        find_by_tab(s.renderers, tab, 0) == Some(i),
        lock_of_url(urls, url, s.next_id) == Some(l),
        !(l is Tuple && l == s.renderers[i].lock),
    ensures
        navigate_tab(urls, s, tab, url, script).1[2] == (Output::ToRenderer { id: s.next_id, bytes: commit_frame(url, script) }),
{
}

/// `find_key` finds a key that is the one asked for.
pub proof fn ml_find_key(list: Seq<StorageEntry>, key: Seq<u8>)
    ensures
        find_key(list, key, 0) matches Some(k) ==> (0 <= k < list.len() && list[k].key == key),
{
    super::invariant::lemma_find_key(list, key, 0);
}

} // verus!
