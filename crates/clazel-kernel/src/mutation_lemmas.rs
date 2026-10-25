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

// ---------------------------------------------------------------------
// Item 3.7: a navigation is a fetch.
// ---------------------------------------------------------------------

/// The one-code-point string `c`.
pub open spec fn ml_u(c: u32) -> Seq<u32> {
    seq![c]
}

/// The report of a fetch started for the URL `c`, with no octets delivered.
pub open spec fn ml_out(c: u32) -> NetOutcome {
    NetOutcome { url: seq![c], net: Seq::empty() }
}

/// A fetch that answers with the URL it was asked for and the octets as the
/// body, and sets no cookie.
pub open spec fn ml_f_echo() -> FetchFns {
    FetchFns { run: |u: Seq<u32>, n: Seq<u8>| FetchRun { result: FetchResult::Done { url: u, body: n }, stores: Seq::<HttpStore>::empty() } }
}

/// A fetch that answers with the URL `c` and a body of the octet `0x7a`, and
/// sets no cookie (a redirect).
pub open spec fn ml_f_at(c: u32) -> FetchFns {
    FetchFns { run: |u: Seq<u32>, n: Seq<u8>| FetchRun { result: FetchResult::Done { url: seq![c], body: seq![0x7au8] }, stores: Seq::<HttpStore>::empty() } }
}

/// A fetch that answers with the empty URL and an empty body, and sets the
/// cookie of [`ml_store`].
pub open spec fn ml_f_cookie() -> FetchFns {
    FetchFns { run: |u: Seq<u32>, n: Seq<u8>| FetchRun { result: FetchResult::Done { url: Seq::<u32>::empty(), body: Seq::<u8>::empty() }, stores: seq![ml_store()] } }
}

/// A fetch that fails after a response that sets the cookie of [`ml_store`].
pub open spec fn ml_f_failed() -> FetchFns {
    FetchFns { run: |u: Seq<u32>, n: Seq<u8>| FetchRun { result: FetchResult::Failed, stores: seq![ml_store()] } }
}

/// A fetch that answers with a final URL that is not a scalar value string.
pub open spec fn ml_f_surrogate() -> FetchFns {
    FetchFns { run: |u: Seq<u32>, n: Seq<u8>| FetchRun { result: FetchResult::Done { url: seq![0xD800u32], body: Seq::<u8>::empty() }, stores: Seq::<HttpStore>::empty() } }
}

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

/// A state with one renderer (id 0, opaque lock 0) navigating to `c`, and
/// the counter 1.
pub open spec fn ml_s_nav(c: u32) -> State {
    State { renderers: seq![Renderer { pending: Some(seq![c]), ..ml_renderer(0, clazel_origin::spec::Origin::Opaque(0nat)) }], ..ml_state_one() }
}

/// [`ml_s_nav`] with a jar of one cookie that has expired by the time 6.
pub open spec fn ml_s_nav_jar(c: u32) -> State {
    State { jar: seq![clazel_cookie::storage::examples::cookie_expiring()], now: 6, ..ml_s_nav(c) }
}

/// A request URL with the given host.
pub open spec fn ml_req(host: Option<clazel_cookie::matching::spec::CanonicalHost>) -> clazel_cookie::storage::spec::RequestUrl {
    clazel_cookie::storage::spec::RequestUrl { scheme: seq![0x61u8], host, path: Seq::<u8>::empty() }
}

/// A fetch's answer is for a navigation in flight to that URL only: a
/// different URL is ignored.
pub proof fn ml_fetched_stale_ignored(fetch: FetchFns, s: State, tab: nat, outcome: NetOutcome, i: int, p: Seq<u32>)
    requires
        0 <= i < s.renderers.len(),
        find_by_tab(s.renderers, tab, 0) == Some(i),
        s.renderers[i].pending == Some(p),
        p != outcome.url,
    ensures
        fetched_run(fetch, s, tab, outcome) is None,
{
}

/// ... and a renderer that is not navigating ignores an answer.
pub proof fn ml_fetched_unsolicited_ignored(fetch: FetchFns, s: State, tab: nat, outcome: NetOutcome, i: int)
    requires
        0 <= i < s.renderers.len(),
        find_by_tab(s.renderers, tab, 0) == Some(i),
        s.renderers[i].pending is None,
    ensures
        fetched_run(fetch, s, tab, outcome) is None,
{
}

/// ... and a tab that is not open does.
pub proof fn ml_fetched_unknown_tab(fetch: FetchFns, s: State, tab: nat, outcome: NetOutcome)
    requires
        find_by_tab(s.renderers, tab, 0) is None,
    ensures
        fetched_run(fetch, s, tab, outcome) is None,
{
}

/// A fetch that ends at `url` commits that URL and the body to a renderer of
/// the new lock.
pub proof fn ml_fetched_commit(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    s: State,
    tab: nat,
    outcome: NetOutcome,
    i: int,
    url: Seq<u32>,
    body: Seq<u8>,
    l: clazel_origin::spec::Origin,
)
    requires
        0 <= i < s.renderers.len(),
        find_by_tab(s.renderers, tab, 0) == Some(i),
        s.renderers[i].pending == Some(outcome.url),
        (fetch.run)(outcome.url, outcome.net).result == (FetchResult::Done { url, body }),
        scalar_url(url),
        lock_of_url(urls, url, s.next_id) == Some(l),
        !(l is Tuple && l == s.renderers[i].lock),
    ensures
        fetched(rules, urls, fetch, s, tab, outcome).1[2] == (Output::ToRenderer { id: s.next_id, bytes: commit_frame(url, body) }),
{
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

/// `begin_navigation` records the URL the renderer is navigating to.
pub proof fn ml_begin_records_url(urls: UrlFns, s: State, tab: nat, url: Seq<u32>, i: int)
    requires
        0 <= i < s.renderers.len(),
        find_by_tab(s.renderers, tab, 0) == Some(i),
        lock_of_url(urls, url, s.next_id) is Some,
    ensures
        begin_navigation(urls, s, tab, url).0.renderers[i].pending == Some(url),
{
}

/// ... and asks for exactly that URL to be fetched, for the tab.
pub proof fn ml_begin_asks_fetch(urls: UrlFns, s: State, tab: nat, url: Seq<u32>, i: int)
    requires
        0 <= i < s.renderers.len(),
        find_by_tab(s.renderers, tab, 0) == Some(i),
        lock_of_url(urls, url, s.next_id) is Some,
    ensures
        begin_navigation(urls, s, tab, url).1 == seq![Output::Fetch { tab, url }],
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

/// One line is stored by §5.7 with the request's own URL and context.
pub proof fn ml_apply_stores_one(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, st: HttpStore, now: int)
    requires
        store_allowed(rules, st.url),
    ensures
        apply_stores(rules, jar, seq![st], now) == clazel_cookie::storage::spec::store_a_set_cookie_string(rules, jar, st.line, st.url, st.ctx, now),
{
    assert(seq![st].drop_first() =~= Seq::<HttpStore>::empty());
    assert(seq![st][0] == st);
    reveal_with_fuel(apply_stores, 2);
}

/// A line that may not be stored leaves the jar as it was.
pub proof fn ml_store_one_refused(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, st: HttpStore, now: int)
    requires
        !store_allowed(rules, st.url),
    ensures
        store_one(rules, jar, st, now) == jar,
{
}

/// A fetch's cookies enter the jar, whether the fetch succeeds or not.
pub proof fn ml_fetched_jar(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, outcome: NetOutcome, run: FetchRun)
    requires
        fetched_run(fetch, s, tab, outcome) == Some(run),
    ensures
        fetched(rules, urls, fetch, s, tab, outcome).0.jar == apply_stores(rules, s.jar, run.stores, s.now),
{
    let s1 = State { jar: apply_stores(rules, s.jar, run.stores, s.now), ..s };
    if let FetchResult::Done { url, body } = run.result {
        crate::unwind_base::lemma_navigation_frame(urls, s1, tab, url, body);
    }
}

/// An answer that is ignored changes nothing, the jar included.
pub proof fn ml_fetched_stale_unchanged(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, outcome: NetOutcome)
    requires
        fetched_run(fetch, s, tab, outcome) is None,
    ensures
        fetched(rules, urls, fetch, s, tab, outcome) == (s, Seq::<Output>::empty()),
{
}

/// A failed fetch sends the renderer the fetch error.
pub proof fn ml_fetch_failed_error(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, outcome: NetOutcome, i: int)
    requires
        0 <= i < s.renderers.len(),
        find_by_tab(s.renderers, tab, 0) == Some(i),
        s.renderers[i].pending == Some(outcome.url),
        (fetch.run)(outcome.url, outcome.net).result is Failed,
    ensures
        fetched(rules, urls, fetch, s, tab, outcome).1 == reply(s.renderers[i], clazel_ipc::message::spec::Message::Error { code: error_fetch() }),
{
}

/// A final URL that is not a string of scalar values is refused.
pub proof fn ml_fetched_non_scalar_refused(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    s: State,
    tab: nat,
    outcome: NetOutcome,
    i: int,
    url: Seq<u32>,
    body: Seq<u8>,
    k: int,
)
    requires
        0 <= i < s.renderers.len(),
        find_by_tab(s.renderers, tab, 0) == Some(i),
        s.renderers[i].pending == Some(outcome.url),
        (fetch.run)(outcome.url, outcome.net).result == (FetchResult::Done { url, body }),
        0 <= k < url.len(),
        !clazel_encoding::utf8::spec::is_scalar_value(url[k]),
    ensures
        fetched(rules, urls, fetch, s, tab, outcome).1 == reply(s.renderers[i], clazel_ipc::message::spec::Message::Error { code: error_bad_url() }),
{
    crate::invariant::lemma_not_scalar_url(url, k);
}


} // verus!
