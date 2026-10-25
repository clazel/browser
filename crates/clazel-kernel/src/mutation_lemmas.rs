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
        conns: Seq::empty(),
        next_conn: 0,
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

// ---------------------------------------------------------------------
// Item 3.7: a navigation is a fetch.
//
// The certified mutations of the join's decisions (connection ownership,
// stale events, the jar-operation application, the commit) are written
// with its proofs; those of the stand-in fetch are gone with it.
// ---------------------------------------------------------------------

/// A `Set-Cookie` line that does not parse, for `https://a.com/x`.
pub open spec fn ml_store() -> HttpStore {
    HttpStore {
        line: Seq::<u8>::empty(),
        url: clazel_cookie::storage::examples::https_url(clazel_cookie::storage::examples::s_a_com(), clazel_cookie::storage::examples::p_x()),
        ctx: clazel_cookie::storage::examples::http_request(),
    }
}

/// The same line for the public suffix `com`.
pub open spec fn ml_store_com() -> HttpStore {
    HttpStore {
        url: clazel_cookie::storage::examples::https_url(clazel_cookie::storage::examples::s_com(), clazel_cookie::storage::examples::p_x()),
        ..ml_store()
    }
}

/// A URL record with nothing in it: the transducer state of
/// [`ml_s_nav`] needs one.
pub open spec fn ml_url0() -> clazel_url::url::spec::Url {
    clazel_url::url::spec::Url {
        scheme: Seq::<u32>::empty(),
        username: Seq::<u32>::empty(),
        password: Seq::<u32>::empty(),
        host: None,
        port: None,
        path: clazel_url::url::spec::UrlPath::List(Seq::<Seq<u32>>::empty()),
        query: None,
        fragment: None,
    }
}

/// A navigation to `c`, just started.
pub open spec fn ml_nav(c: u32) -> Navigation {
    Navigation {
        url: seq![c],
        fetch: clazel_fetch::transducer::spec::State { url: ml_url0(), redirects: 0, phase: clazel_fetch::transducer::spec::Phase::Connecting, tainted: false },
        partition: crate::domain::Domain::Opaque(0),
    }
}

/// A state with one renderer (id 0, opaque lock 0) navigating to `c`, and
/// the counter 1.
pub open spec fn ml_s_nav(c: u32) -> State {
    State { renderers: seq![Renderer { pending: Some(ml_nav(c)), ..ml_renderer(0, clazel_origin::spec::Origin::Opaque(0nat)) }], ..ml_state_one() }
}

/// A request URL with the given host.
pub open spec fn ml_req(host: Option<clazel_cookie::matching::spec::CanonicalHost>) -> clazel_cookie::storage::spec::RequestUrl {
    clazel_cookie::storage::spec::RequestUrl { scheme: seq![0x61u8], host, path: Seq::<u8>::empty() }
}

/// A navigation that ends without a commit leaves the renderer no longer
/// navigating.
pub proof fn ml_fail_clears_pending(s: State, i: int, code: u64)
    requires
        0 <= i < s.renderers.len(),
    ensures
        fail_navigation(s, i, s.renderers[i], code).0.renderers[i].pending is None,
{
}

/// A commit to another origin gives a new renderer that is not navigating.
pub proof fn ml_commit_clears_pending(urls: UrlFns, s: State, tab: nat, url: Seq<u32>, script: Seq<u8>, i: int, l: clazel_origin::spec::Origin)
    requires
        0 <= i < s.renderers.len(),
        find_by_tab(s.renderers, tab, 0) == Some(i),
        lock_of_url(urls, url, s.next_id) == Some(l),
        !(l is Tuple && l == s.renderers[i].lock),
    ensures
        navigate_tab(urls, s, tab, url, script).0.renderers[i].pending is None,
{
}

/// A response's cookie is never stored for a request to a public suffix.
pub proof fn ml_store_public_suffix_refused(url: clazel_cookie::storage::spec::RequestUrl)
    ensures
        !store_allowed_given(url, true),
{
}

/// ... nor for a request with an empty host name.
pub proof fn ml_store_empty_host_refused(url: clazel_cookie::storage::spec::RequestUrl, on_public_suffix: bool)
    requires
        url.host matches Some(h) && h.name.len() == 0,
    ensures
        !store_allowed_given(url, on_public_suffix),
{
}

/// ... nor for a request with no host.
pub proof fn ml_store_no_host_refused(url: clazel_cookie::storage::spec::RequestUrl, on_public_suffix: bool)
    requires
        url.host is None,
    ensures
        !store_allowed_given(url, on_public_suffix),
{
}

/// A line that may not be stored leaves the jar as it was.
pub proof fn ml_store_one_refused(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, st: HttpStore, now: int)
    requires
        !store_allowed(rules, st.url),
    ensures
        store_one(rules, jar, st, now) == jar,
{
}

} // verus!
