//! An independent transcription of the parts of the Fetch Standard the
//! client state machine implements, and a proof that the transducer
//! (`super::spec`) agrees with it, step by step and over whole runs (any
//! number of redirects), on a stated class of requests. It is written from the Fetch text, not from `spec.rs`, and
//! shares with it only the functions the standards themselves call
//! (the URL parser, `clazel-cookie`'s algorithms, and the HTTP field
//! functions): what is compared is the control flow and the state.
//!
//! Source (pinned): the Fetch Standard, Living Standard last updated 19
//! October 2026, commit `59afe349913d56898c947576216f1c2579308be7`:
//! - §4.5 "HTTP-redirect fetch", steps 1 to 22 (below, step by step);
//! - §2.2.3 "redirect status", §2.2.6 "location URL";
//! - §4.6 "HTTP-network-or-cache fetch" step 8.21.1 ("If includeCredentials
//!   is true, then append a request `Cookie` header") and §3.1.1 "append a
//!   request `Cookie` header" (steps 5 to 8);
//! - §4.7 "HTTP-network fetch" step 17 and §3.1.2 "parse and store response
//!   `Set-Cookie` headers" (step 6);
//! - §3.1.3 "determine the same-site mode".
//!
//! The text was read from the commit snapshot at
//! `https://fetch.spec.whatwg.org/commit-snapshots/59afe349…/`; the
//! repository holds no copy of it.
//!
//! # The class
//!
//! The equivalence is for a request that is a **navigation GET with no
//! body**, no caching (so HTTP-network-or-cache fetch always asks the
//! network), **no CORS** (mode "navigate", response tainting "basic", no
//! CORS-preflight, no CORS headers to remove), redirect mode "follow",
//! credentials mode "include" (so `includeCredentials` is true, §4.6 step
//! 8.3), no timing info, no referrer, and a response that is a complete,
//! final one (no 1xx). Outside the class (a body, POST, `cors`, caching)
//! `spec.rs` says nothing.
//!
//! # Differences in form from `spec.rs` (so that the comparison means something)
//!
//! - The request is its **URL list** ([`FetchRequest`]), as in Fetch: the
//!   "current URL" is its last item, the **redirect count** is its length
//!   minus one (step 8 "Increase request's redirect count by 1" and step 18
//!   "Append locationURL to request's URL list" are one operation here), and
//!   the **redirect-taint** is *computed* from the list ([`list_taint`]);
//!   `spec.rs` keeps a counter, a URL and a sticky flag.
//! - The cookie store is a `Seq<Cookie>` threaded through, and "parse and
//!   store each `Set-Cookie`" is a `fold_left` over it; `spec.rs` returns
//!   jar operations, compared here by applying them (`apply_ops`).
//! - The result of HTTP-redirect fetch is Fetch's: a response, a network
//!   error, or the request to fetch next ([`FetchResult`]); `spec.rs`'s
//!   `Reason`s (why it failed) do not exist in Fetch.
//! - Which decisions are the transducer's and not Fetch's (connections,
//!   closing, interim responses, how the bytes become a response) are not
//!   transcribed; the step-level equivalence is for the decision taken on a
//!   final response, and for the request built when the connection is open.
//!   The whole-run equivalence ([`theorem_independent_run`], at the end)
//!   chains them with Fetch's own loop (below it, "Whole runs") over
//!   responses a well-behaved shell delivers whole.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A request, in the class (see the header): its URL list. "A request has
/// an associated URL list (a list of one or more URLs)."
pub struct FetchRequest {
    /// the URL list
    pub url_list: Seq<Url>,
}

/// "A request's current URL is its URL list's last item."
pub open spec fn current_url(r: FetchRequest) -> Url
    recommends r.url_list.len() > 0
{
    r.url_list[r.url_list.len() - 1]
}

/// "request's redirect count": the number of redirects followed, which is
/// the number of URLs added to the list after the first.
pub open spec fn redirect_count(r: FetchRequest) -> nat {
    if r.url_list.len() == 0 { 0 } else { (r.url_list.len() - 1) as nat }
}

/// Fetch §3.1.3 "request's redirect-taint" is "cross-site": some hop of the
/// URL list is to a URL whose origin is not same site with the one before
/// it. (The `spec.rs` reading of the name: see the modelling choices there.)
pub open spec fn list_taint(urls: UrlFns, l: Seq<Url>) -> bool
    decreases l.len()
{
    if l.len() < 2 {
        false
    } else {
        list_taint(urls, l.drop_last()) || !clazel_origin::spec::same_site(urls.rules, (urls.origin)(l[l.len() - 2]), (urls.origin)(l[l.len() - 1]))
    }
}

/// What HTTP-redirect fetch returns.
pub enum FetchResult {
    /// "return response" (step 4)
    Response(Response),
    /// "return a network error" (steps 5 to 7)
    NetworkError,
    /// "return the result of running main fetch": the request to fetch
    /// next, after steps 8 and 18 (step 22)
    Follow(FetchRequest),
}

/// Fetch §2.2.3: "A redirect status is a status that is 301, 302, 303, 307,
/// or 308."
pub open spec fn redirect_status_list() -> Seq<nat> {
    seq![301nat, 302, 303, 307, 308]
}

/// Fetch §2.2.6 "location URL" of `response` given the fragment of the
/// request's current URL: `None` is null, `Some(None)` is failure.
pub open spec fn indep_location_url(urls: UrlFns, response: Response, current: Url) -> Option<Option<Url>> {
    // 1. "If response's status is not a redirect status, then return null."
    if !redirect_status_list().contains(response.status_line.status) {
        None
    } else {
        // 2. "Let location be the result of extracting header list values
        // given `Location` and response's header list."
        let location = clazel_http::field::spec::field_values_named(response.fields, seq![0x4Cu8, 0x6F, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E]);
        if location.len() == 0 {
            // (nothing extracted: null)
            None
        } else if location.len() > 1 {
            // (a single-value header with several values: failure)
            Some(None)
        } else {
            // 3. "If location is a header value, then set location to the
            // result of parsing location with response's URL."
            match (urls.location)(current, location[0]) {
                None => Some(None),
                // 4. "If location is a URL whose fragment is null, then set
                // location's fragment to requestFragment."
                // 5. "Return location."
                Some(parsed) => Some(Some(clazel_url::url::spec::Url {
                    fragment: if parsed.fragment is None { current.fragment } else { parsed.fragment },
                    ..parsed
                })),
            }
        }
    }
}

/// Fetch §4.5 HTTP-redirect fetch, for a request in the class and a final
/// `response` (the response is its own internal response: not filtered).
pub open spec fn http_redirect_fetch(urls: UrlFns, request: FetchRequest, response: Response) -> FetchResult {
    // 3. "Let locationURL be internalResponse's location URL given request's
    // current URL's fragment."
    match indep_location_url(urls, response, current_url(request)) {
        // 4. "If locationURL is null, then return response."
        None => FetchResult::Response(response),
        // 5. "If locationURL is failure, then return a network error."
        Some(None) => FetchResult::NetworkError,
        Some(Some(location)) => if !(location.scheme == seq![0x68u32, 0x74, 0x74, 0x70] || location.scheme == seq![0x68u32, 0x74, 0x74, 0x70, 0x73]) {
            // 6. "If locationURL's scheme is not an HTTP(S) scheme, then
            // return a network error."
            FetchResult::NetworkError
        } else if redirect_count(request) == 20 {
            // 7. "If request's redirect count is 20, then return a network
            // error."
            FetchResult::NetworkError
        } else {
            // 8. "Increase request's redirect count by 1." 9 to 17: nothing
            // for a request in the class (no CORS, no body, GET stays GET,
            // no timing info). 18. "Append locationURL to request's URL
            // list." 19 to 21: nothing (no referrer, redirect mode
            // "follow"). 22. "Return the result of running main fetch with
            // fetchParams and recursive."
            FetchResult::Follow(FetchRequest { url_list: request.url_list.push(location) })
        },
    }
}

/// The request context of Fetch §3.1.3 for a request in the class, as
/// RFC 6265bis §5.2 reads it (see `spec.rs`'s modelling choices).
pub open spec fn indep_context(urls: UrlFns, r: FetchRequest) -> RequestContext {
    RequestContext::Http(clazel_cookie::storage::spec::HttpRequest {
        url_origin: (urls.origin)(current_url(r)),
        site_for_cookies: if list_taint(urls, r.url_list) { Some(clazel_origin::spec::Origin::Opaque(0)) } else { None },
        is_reload_navigation: false,
        reloaded_document_was_same_site: false,
        navigates_top_level_traversable: true,
        method_is_safe: true,
        target_is_active_or_top_level: true,
    })
}

/// Fetch §3.1.1 "append a request `Cookie` header", steps 5 and 7: the
/// cookies "retrieved" for the current URL and serialized.
pub open spec fn indep_cookie_value(urls: UrlFns, jar: Seq<Cookie>, now: int, r: FetchRequest) -> Seq<u8> {
    clazel_cookie::storage::spec::retrieve_cookie_string(urls.rules, jar, (urls.request_url)(current_url(r)), indep_context(urls, r), now)
}

/// Fetch §3.1.1 steps 6 and 8: "If no cookies were returned, stop";
/// otherwise append a `Cookie` header: the header list (after the headers
/// the network layer sets) with it appended.
pub open spec fn indep_header_list(base: Seq<clazel_http::field::spec::FieldLine>, cookies: Seq<u8>) -> Seq<clazel_http::field::spec::FieldLine> {
    if cookies.len() == 0 {
        base
    } else {
        base.push(clazel_http::field::spec::FieldLine { name: seq![0x43u8, 0x6F, 0x6F, 0x6B, 0x69, 0x65], value: cookies })
    }
}

/// §4.6 step 8.21.1 for a request in the class: the bytes of the request
/// sent to the network, for the cookie jar `jar` at `now`.
pub open spec fn indep_request_bytes(urls: UrlFns, jar: Seq<Cookie>, now: int, r: FetchRequest) -> Option<Seq<u8>> {
    match crate::request::spec::request_for(current_url(r)) {
        Some(base) => {
            let request = clazel_http::message::spec::Request {
                method: base.method,
                target: base.target,
                fields: indep_header_list(base.fields, indep_cookie_value(urls, jar, now, r)),
            };
            if clazel_http::message::spec::is_valid_request(request) {
                Some(clazel_http::message::spec::serialize_request(request))
            } else {
                None
            }
        },
        None => None,
    }
}

/// §4.7 step 17 and §3.1.2 step 6 for a request in the class: the cookie
/// jar after "parse and store" of each `Set-Cookie` header of `response`.
pub open spec fn indep_store_cookies(urls: UrlFns, jar: Seq<Cookie>, now: int, r: FetchRequest, response: Response) -> Seq<Cookie> {
    clazel_http::field::spec::field_values_named(response.fields, seq![0x53u8, 0x65, 0x74, 0x2D, 0x43, 0x6F, 0x6F, 0x6B, 0x69, 0x65]).fold_left(
        jar,
        |j: Seq<Cookie>, line: Seq<u8>|
            clazel_cookie::storage::spec::store_a_set_cookie_string(urls.rules, j, line, (urls.request_url)(current_url(r)), indep_context(urls, r), now),
    )
}

// ===========================================================================
// The equivalence.
// ===========================================================================

/// The state `s` is the request `r` after the same history: the same
/// current URL, the redirect count of the list, the taint computed from it.
pub open spec fn corresponds(urls: UrlFns, s: State, r: FetchRequest) -> bool {
    r.url_list.len() > 0 && s.url == current_url(r) && s.redirects == redirect_count(r) && s.tainted == list_taint(urls, r.url_list)
}

/// Applying `stored_ops` is the fold of storage.
pub proof fn lemma_stored_ops_is_fold(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<Cookie>, lines: Seq<Seq<u8>>, url: RequestUrl, ctx: RequestContext, now: int)
    ensures
        apply_ops(rules, jar, stored_ops(lines, url, ctx, now))
            == lines.fold_left(jar, |j: Seq<Cookie>, line: Seq<u8>| clazel_cookie::storage::spec::store_a_set_cookie_string(rules, j, line, url, ctx, now)),
    decreases lines.len()
{
    reveal_with_fuel(Seq::fold_left, 2);
    if lines.len() > 0 {
        let step_jar = clazel_cookie::storage::spec::store_a_set_cookie_string(rules, jar, lines[0], url, ctx, now);
        lemma_stored_ops_is_fold(rules, step_jar, lines.drop_first(), url, ctx, now);
        let ops = stored_ops(lines, url, ctx, now);
        let rest = stored_ops(lines.drop_first(), url, ctx, now);
        assert(ops[0] == (JarOp::Stored { line: lines[0], url: url, ctx: ctx, now: now }));
        assert(ops.drop_first() =~= rest);
        assert(lines.drop_first() == lines.subrange(1, lines.len() as int));
        lemma_fold_left_drop_first(lines, jar, |j: Seq<Cookie>, line: Seq<u8>| clazel_cookie::storage::spec::store_a_set_cookie_string(rules, j, line, url, ctx, now));
    }
}

/// `fold_left` over a non-empty sequence is `fold_left` of the tail from
/// the first step.
pub proof fn lemma_fold_left_drop_first<A, B>(s: Seq<A>, b: B, f: spec_fn(B, A) -> B)
    requires
        s.len() > 0,
    ensures
        s.fold_left(b, f) == s.drop_first().fold_left(f(b, s[0]), f),
    decreases s.len()
{
    reveal_with_fuel(Seq::fold_left, 2);
    if s.len() > 1 {
        lemma_fold_left_drop_first(s.drop_last(), b, f);
        assert(s.drop_last().drop_first() == s.drop_first().drop_last());
        assert(s.drop_first().last() == s.last());
    } else {
        assert(s.drop_first() =~= Seq::<A>::empty());
    }
}

/// `list_taint` of a list with one more URL.
pub proof fn lemma_taint_push(urls: UrlFns, l: Seq<Url>, u: Url)
    requires
        l.len() > 0,
    ensures
        list_taint(urls, l.push(u)) == (list_taint(urls, l) || !clazel_origin::spec::same_site(urls.rules, (urls.origin)(l[l.len() - 1]), (urls.origin)(u))),
{
    assert(l.push(u).drop_last() =~= l);
    assert(l.push(u)[l.len() as int] == u);
    assert(l.push(u)[l.len() - 1] == l[l.len() - 1]);
}

/// **The cookie header agrees**: for a state and a request in
/// correspondence, the cookie-string and the request bytes of the
/// transducer, from the jar `jar` at `now`, are Fetch's; when Fetch's
/// request is valid, it is what the transducer sends.
pub proof fn theorem_independent_request(urls: UrlFns, s: State, r: FetchRequest, jar: Seq<Cookie>, now: int)
    requires
        corresponds(urls, s, r),
    ensures
        cookie_string(urls, s, jar, now) == indep_cookie_value(urls, jar, now, r),
        crate::request::spec::request_bytes_cookie(s.url, cookie_string(urls, s, jar, now)) == indep_request_bytes(urls, jar, now, r),
        forall|plain: Seq<u8>| #[trigger] indep_request_bytes(urls, jar, now, r) == Some(wire_bytes(s.url, cookie_string(urls, s, jar, now), plain))
            || indep_request_bytes(urls, jar, now, r) is None,
{
    assert(request_context(urls, s) == indep_context(urls, r));
    let cs = cookie_string(urls, s, jar, now);
    match crate::request::spec::request_for(s.url) {
        Some(base) => {
            assert(crate::request::spec::cookie_field_lines(cs) =~= indep_header_list(seq![], cs) || cs.len() == 0);
            assert(base.fields + crate::request::spec::cookie_field_lines(cs) =~= indep_header_list(base.fields, cs));
        },
        None => {},
    }
}

/// **The decision on a final response is Fetch's**: for a state and a
/// request in correspondence and a final response, what `on_final` does is
/// what HTTP-redirect fetch returns, after §4.7 step 17's storage:
/// - its jar operations, applied to any jar, are Fetch's storage;
/// - a response: `Done` for the request's URL;
/// - a network error: `Fail`;
/// - a request to fetch next: a new state in correspondence with it,
///   asking for its connection.
pub proof fn theorem_independent_redirect(urls: UrlFns, s: State, r: FetchRequest, response: Response, open: bool, jar: Seq<Cookie>, now: int)
    requires
        corresponds(urls, s, r),
        s.redirects <= 20,
    ensures
        apply_ops(urls.rules, jar, on_final(urls, s, response, open, now).2) == indep_store_cookies(urls, jar, now, r, response),
        match http_redirect_fetch(urls, r, response) {
            FetchResult::Response(resp) => on_final(urls, s, response, open, now).1 == close_if(open) + seq![Action::Done { url: current_url(r), response: resp }],
            FetchResult::NetworkError => exists|reason: Reason| on_final(urls, s, response, open, now).1 == close_if(open) + seq![Action::Fail(reason)],
            FetchResult::Follow(r2) => {
                let after = on_final(urls, s, response, open, now);
                corresponds(urls, after.0, r2) && after.1 == close_if(open) + begin(after.0.url, after.0.redirects, after.0.tainted).1
            },
        },
{
    super::theorems::lemma_on_final_ops(urls, s, response, open, now);
    lemma_stored_ops_is_fold(urls.rules, jar, set_cookie_values(response), (urls.request_url)(s.url), request_context(urls, s), now);
    assert(request_context(urls, s) == indep_context(urls, r));
    match location_url(urls, response, s.url) {
        LocationUrl::Null => {},
        LocationUrl::Failure => {
            assert(exists|reason: Reason| on_final(urls, s, response, open, now).1 == close_if(open) + seq![Action::Fail(reason)]) by {
                assert(on_final(urls, s, response, open, now).1 == close_if(open) + seq![Action::Fail(Reason::RedirectLocation)]);
            }
        },
        LocationUrl::Url(location) => {
            if !is_http_s_scheme(location.scheme) {
                assert(on_final(urls, s, response, open, now).1 == close_if(open) + seq![Action::Fail(Reason::RedirectScheme)]);
            } else if s.redirects == max_redirects() {
                assert(on_final(urls, s, response, open, now).1 == close_if(open) + seq![Action::Fail(Reason::RedirectLimit)]);
            } else {
                lemma_taint_push(urls, r.url_list, location);
                let r2 = FetchRequest { url_list: r.url_list.push(location) };
                assert(current_url(r2) == location);
                assert(redirect_count(r2) == s.redirects + 1);
            }
        },
    }
}

// ===========================================================================
// Whole runs.
// ===========================================================================
//
// The step-by-step theorems above compare one decision. A fetch is a chain
// of them: each hop's jar is the one the hop before left, and each hop's
// request is the one the redirect before it asked for. The theorem below
// compares the chains: the transducer driven by a well-behaved shell, over
// any number of redirects, against Fetch's own loop (main fetch, HTTP-
// network-or-cache fetch, HTTP-redirect fetch, main fetch, ...), written
// as a recursion over the URL list. Induction over the hops lifts each
// step's agreement to the run.
//
// The shell is well behaved when, for each connection it is asked for, it
// reports `Connected` and then the octets of one final response in one
// `Bytes` (a [`Hop`]), and the HTTP function reads those octets as that
// response ([`delivers`]; `real`'s join is tested to, and Fetch does not
// say how bytes become a response, so this is the interface of the class).
// Other shell behaviour (a split delivery, a close, an error) is
// `theorem_split_invariant`'s and the failure cases' in `contract.rs`; here
// the comparison is of what Fetch decides.

/// One connection of a run, as a well-behaved shell has it: the octets the
/// server sends, and the final response they are.
pub struct Hop {
    /// the octets delivered in one `Bytes`
    pub bytes: Seq<u8>,
    /// the response they are
    pub response: Response,
}

/// The parser reads `h.bytes`, delivered whole, as the final response
/// `h.response`.
pub open spec fn delivers(http: HttpFns, h: Hop) -> bool {
    settle(http, h.bytes) == Settled::Final(h.response)
}

/// Every hop of `hops` is delivered.
pub open spec fn all_deliver(http: HttpFns, hops: Seq<Hop>) -> bool {
    forall|i: int| 0 <= i < hops.len() ==> #[trigger] delivers(http, hops[i])
}

/// A URL for which the client asks for a connection and has a request
/// (those of `crate::request::spec`, which the step-level theorems share).
pub open spec fn indep_fetchable(url: Url) -> bool {
    crate::request::spec::connect_to(url) is Some && crate::request::spec::request_bytes(url) is Some
}

/// How a run ends, in Fetch's terms.
pub enum RunOutcome {
    /// HTTP-redirect fetch returned the response (step 4), the response to
    /// the request for `url`
    Response {
        /// the request's current URL
        url: Url,
        /// the response
        response: Response,
    },
    /// a network error: the request is not one the client sends, or steps
    /// 5 to 7 of HTTP-redirect fetch
    NetworkError,
    /// the connection was asked for and the hops ran out
    Unanswered,
}

/// What Fetch's loop did: the bytes of the requests sent to the network, in
/// order, the cookie jar after, and how it ended.
pub struct IndepRun {
    /// the request sent for each hop
    pub sent: Seq<Seq<u8>>,
    /// the cookie jar at the end
    pub jar: Seq<Cookie>,
    /// how it ended
    pub outcome: RunOutcome,
}

/// §4.6 step 8.21.1 as sent: the request with its `Cookie` header, or, when
/// no header value can carry the cookies, without (the choice the modelling
/// choices of `spec.rs` state).
pub open spec fn indep_wire(urls: UrlFns, jar: Seq<Cookie>, now: int, r: FetchRequest) -> Seq<u8> {
    match indep_request_bytes(urls, jar, now, r) {
        Some(bytes) => bytes,
        None => crate::request::spec::request_bytes(current_url(r)).unwrap(),
    }
}

/// Fetch's loop for the request `r`, the cookie jar `jar` at `now`, and the
/// responses the network gives, one per connection.
pub open spec fn indep_fetch(urls: UrlFns, jar: Seq<Cookie>, now: int, r: FetchRequest, hops: Seq<Hop>) -> IndepRun
    decreases hops.len()
{
    if !indep_fetchable(current_url(r)) {
        IndepRun { sent: seq![], jar: jar, outcome: RunOutcome::NetworkError }
    } else {
        // §3.1.1 step 5 (RFC 6265bis §5.8.3 step 5): retrieval updates the jar.
        let jar1 = clazel_cookie::storage::spec::jar_after_retrieval(urls.rules, jar, (urls.request_url)(current_url(r)), indep_context(urls, r), now);
        let wire = indep_wire(urls, jar, now, r);
        if hops.len() == 0 {
            IndepRun { sent: seq![wire], jar: jar1, outcome: RunOutcome::Unanswered }
        } else {
            let response = hops[0].response;
            let jar2 = indep_store_cookies(urls, jar1, now, r, response);
            match http_redirect_fetch(urls, r, response) {
                FetchResult::Response(resp) => IndepRun { sent: seq![wire], jar: jar2, outcome: RunOutcome::Response { url: current_url(r), response: resp } },
                FetchResult::NetworkError => IndepRun { sent: seq![wire], jar: jar2, outcome: RunOutcome::NetworkError },
                FetchResult::Follow(r2) => {
                    let rest = indep_fetch(urls, jar2, now, r2, hops.drop_first());
                    IndepRun { sent: seq![wire] + rest.sent, jar: rest.jar, outcome: rest.outcome }
                },
            }
        }
    }
}

/// The transducer driven through the hops of a well-behaved shell from the
/// state `s`: for each connection asked for, `Connected` and then the
/// hop's `Bytes`, each step given the jar the steps before left (their
/// operations applied). The state, every action after `s`, the jar.
pub open spec fn tx_fetch(http: HttpFns, urls: UrlFns, s: State, jar: Seq<Cookie>, now: int, hops: Seq<Hop>) -> (State, Seq<Action>, Seq<Cookie>)
    decreases hops.len()
{
    match s.phase {
        Phase::Connecting => {
            let s1 = step(http, urls, s, Input::Connected, jar, now);
            let j1 = apply_ops(urls.rules, jar, s1.2);
            if hops.len() == 0 {
                (s1.0, s1.1, j1)
            } else {
                let s2 = step(http, urls, s1.0, Input::Bytes(hops[0].bytes), j1, now);
                let j2 = apply_ops(urls.rules, j1, s2.2);
                let rest = tx_fetch(http, urls, s2.0, j2, now, hops.drop_first());
                (rest.0, s1.1 + s2.1 + rest.1, rest.2)
            }
        },
        _ => (s, seq![], jar),
    }
}

/// The octets of the `Send`s of `a`, in order.
pub open spec fn sent_bytes(a: Seq<Action>) -> Seq<Seq<u8>>
    decreases a.len()
{
    if a.len() == 0 {
        seq![]
    } else {
        sent_bytes(a.drop_last()) + match a.last() {
            Action::Send(bytes) => seq![bytes],
            _ => seq![],
        }
    }
}

/// How the run ended, as the last action and the state say.
pub open spec fn outcome_matches(o: RunOutcome, s: State, acts: Seq<Action>) -> bool {
    match o {
        RunOutcome::Response { url, response } => s.phase is Finished && acts.len() > 0 && acts.last() == (Action::Done { url: url, response: response }),
        RunOutcome::NetworkError => s.phase is Finished && acts.len() > 0 && acts.last() is Fail,
        RunOutcome::Unanswered => !(s.phase is Finished),
    }
}

/// `sent_bytes` adds over concatenation.
pub proof fn lemma_sent_bytes_concat(a: Seq<Action>, b: Seq<Action>)
    ensures
        sent_bytes(a + b) == sent_bytes(a) + sent_bytes(b),
    decreases b.len()
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(sent_bytes(a) + sent_bytes(b) =~= sent_bytes(a));
    } else {
        lemma_sent_bytes_concat(a, b.drop_last());
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        assert(sent_bytes(a + b) =~= sent_bytes(a) + sent_bytes(b)) by {
            assert(sent_bytes(a + b) == sent_bytes(a + b.drop_last()) + match b.last() {
                Action::Send(bytes) => seq![bytes],
                _ => seq![],
            });
            assert(sent_bytes(b) == sent_bytes(b.drop_last()) + match b.last() {
                Action::Send(bytes) => seq![bytes],
                _ => seq![],
            });
        }
    }
}

/// Actions with no `Send` have no sent bytes.
pub proof fn lemma_sent_bytes_none(a: Seq<Action>)
    requires
        super::theorems::no_sends(a),
    ensures
        sent_bytes(a) == Seq::<Seq<u8>>::empty(),
    decreases a.len()
{
    if a.len() > 0 {
        assert(super::theorems::no_sends(a.drop_last())) by {
            assert forall|k: int| 0 <= k < a.drop_last().len() implies !(#[trigger] a.drop_last()[k] is Send) by {
                assert(a.drop_last()[k] == a[k]);
            }
        }
        lemma_sent_bytes_none(a.drop_last());
        assert(!(a.last() is Send));
    }
}

/// The sent bytes of one `Send`.
pub proof fn lemma_sent_bytes_one(bytes: Seq<u8>)
    ensures
        sent_bytes(seq![Action::Send(bytes)]) == seq![bytes],
{
    let a = seq![Action::Send(bytes)];
    assert(a.drop_last() =~= Seq::<Action>::empty());
    assert(a.last() == Action::Send(bytes));
    assert(sent_bytes(Seq::<Action>::empty()) =~= Seq::<Seq<u8>>::empty());
    assert(Seq::<Seq<u8>>::empty() + seq![bytes] =~= seq![bytes]);
}

/// The state and the request of a correspondence give the same context.
pub proof fn lemma_corresponds_context(urls: UrlFns, s: State, r: FetchRequest)
    requires
        corresponds(urls, s, r),
    ensures
        request_context(urls, s) == indep_context(urls, r),
{
}

/// `begin` gives a connection exactly for a fetchable URL, and otherwise
/// ends the fetch with `NotFetched`.
pub proof fn lemma_begin_fetchable(url: Url, redirects: nat, tainted: bool)
    ensures
        begin(url, redirects, tainted).0.url == url,
        begin(url, redirects, tainted).0.redirects == redirects,
        begin(url, redirects, tainted).0.tainted == tainted,
        begin(url, redirects, tainted).0.phase is Connecting <==> indep_fetchable(url),
        !indep_fetchable(url) ==> begin(url, redirects, tainted).0.phase is Finished && begin(url, redirects, tainted).1 == seq![Action::Fail(Reason::NotFetched)],
{
}

/// A decision that ends the fetch leaves the state finished.
pub proof fn lemma_independent_redirect_finished(urls: UrlFns, s: State, r: FetchRequest, response: Response, open: bool, now: int)
    requires
        corresponds(urls, s, r),
    ensures
        match http_redirect_fetch(urls, r, response) {
            FetchResult::Follow(_) => true,
            _ => on_final(urls, s, response, open, now).0.phase is Finished,
        },
{
    match location_url(urls, response, s.url) {
        LocationUrl::Null => {},
        LocationUrl::Failure => {},
        LocationUrl::Url(location) => {
            if !is_http_s_scheme(location.scheme) {
            } else if s.redirects == max_redirects() {
            } else {
            }
        },
    }
}

/// The first step of a hop: the connection is open, and the request goes
/// out as Fetch's, with its retrieval applied to the jar.
pub proof fn lemma_run_connected(http: HttpFns, urls: UrlFns, s: State, r: FetchRequest, jar: Seq<Cookie>, now: int)
    requires
        corresponds(urls, s, r),
        s.phase is Connecting,
        indep_fetchable(s.url),
    ensures
        step(http, urls, s, Input::Connected, jar, now).1 == seq![Action::Send(indep_wire(urls, jar, now, r))],
        step(http, urls, s, Input::Connected, jar, now).0 == (State { phase: Phase::Reading { received: Seq::<u8>::empty() }, ..s }),
        apply_ops(urls.rules, jar, step(http, urls, s, Input::Connected, jar, now).2)
            == clazel_cookie::storage::spec::jar_after_retrieval(urls.rules, jar, (urls.request_url)(current_url(r)), indep_context(urls, r), now),
{
    reveal_with_fuel(apply_ops, 2);
    lemma_corresponds_context(urls, s, r);
    let plain = crate::request::spec::request_bytes(s.url).unwrap();
    theorem_independent_request(urls, s, r, jar, now);
    let s1 = step(http, urls, s, Input::Connected, jar, now);
    assert(s1.2 == seq![retrieval_op(urls, s, now)]);
    assert(s1.2.drop_first() =~= Seq::<JarOp>::empty());
    assert(wire_bytes(s.url, cookie_string(urls, s, jar, now), plain) == indep_wire(urls, jar, now, r));
}

/// The second step of a hop: the hop's bytes arrive and are the final
/// response, which the transducer decides as HTTP-redirect fetch does,
/// storing its cookies as Fetch does.
pub proof fn lemma_run_bytes(http: HttpFns, urls: UrlFns, s: State, r: FetchRequest, jar: Seq<Cookie>, now: int, d: Hop)
    requires
        corresponds(urls, s, r),
        s.redirects <= 20,
        s.phase == (Phase::Reading { received: Seq::<u8>::empty() }),
        delivers(http, d),
    ensures
        step(http, urls, s, Input::Bytes(d.bytes), jar, now) == on_final(urls, s, d.response, true, now),
        apply_ops(urls.rules, jar, on_final(urls, s, d.response, true, now).2) == indep_store_cookies(urls, jar, now, r, d.response),
        super::theorems::no_sends(on_final(urls, s, d.response, true, now).1),
        on_final(urls, s, d.response, true, now).1.len() > 0,
        match http_redirect_fetch(urls, r, d.response) {
            FetchResult::Response(resp) => on_final(urls, s, d.response, true, now).0.phase is Finished
                && on_final(urls, s, d.response, true, now).1.last() == (Action::Done { url: current_url(r), response: resp }),
            FetchResult::NetworkError => on_final(urls, s, d.response, true, now).0.phase is Finished
                && on_final(urls, s, d.response, true, now).1.last() is Fail,
            FetchResult::Follow(r2) => {
                let after = on_final(urls, s, d.response, true, now);
                corresponds(urls, after.0, r2) && after.0.redirects <= 20 && after.1 == close_if(true) + begin(after.0.url, after.0.redirects, after.0.tainted).1
                    && after.0 == begin(after.0.url, after.0.redirects, after.0.tainted).0
            },
        },
{
    assert((Seq::<u8>::empty() + d.bytes) =~= d.bytes);
    theorem_independent_redirect(urls, s, r, d.response, true, jar, now);
    lemma_independent_redirect_finished(urls, s, r, d.response, true, now);
    super::theorems::lemma_on_final_no_sends(urls, s, d.response, true, now);
    match http_redirect_fetch(urls, r, d.response) {
        FetchResult::Response(resp) => {
            let a = on_final(urls, s, d.response, true, now).1;
            assert(a == close_if(true) + seq![Action::Done { url: current_url(r), response: resp }]);
            assert(a.last() == (Action::Done { url: current_url(r), response: resp }));
        },
        FetchResult::NetworkError => {
            let a = on_final(urls, s, d.response, true, now).1;
            assert(exists|reason: Reason| a == close_if(true) + seq![Action::Fail(reason)]);
            let reason = choose|reason: Reason| a == close_if(true) + seq![Action::Fail(reason)];
            assert(a.last() == Action::Fail(reason));
        },
        FetchResult::Follow(r2) => {
            assert(r.url_list.len() - 1 != 20);
            let after = on_final(urls, s, d.response, true, now);
            lemma_begin_fetchable(after.0.url, after.0.redirects, after.0.tainted);
        },
    }
}

/// **The run agrees**: from a state asking for the connection of a
/// fetchable URL, in correspondence with the request `r`, the transducer
/// driven through any hops the parser delivers sends the requests Fetch's
/// loop sends, leaves the cookie jar Fetch's loop leaves, and ends as Fetch
/// does.
pub proof fn lemma_independent_run(http: HttpFns, urls: UrlFns, s: State, r: FetchRequest, jar: Seq<Cookie>, now: int, hops: Seq<Hop>)
    requires
        corresponds(urls, s, r),
        s.redirects <= 20,
        s.phase is Connecting,
        indep_fetchable(s.url),
        all_deliver(http, hops),
    ensures
        sent_bytes(tx_fetch(http, urls, s, jar, now, hops).1) == indep_fetch(urls, jar, now, r, hops).sent,
        tx_fetch(http, urls, s, jar, now, hops).2 == indep_fetch(urls, jar, now, r, hops).jar,
        tx_fetch(http, urls, s, jar, now, hops).1.len() > 0,
        outcome_matches(indep_fetch(urls, jar, now, r, hops).outcome, tx_fetch(http, urls, s, jar, now, hops).0, tx_fetch(http, urls, s, jar, now, hops).1),
    decreases hops.len()
{
    reveal_with_fuel(tx_fetch, 2);
    reveal_with_fuel(indep_fetch, 2);
    lemma_run_connected(http, urls, s, r, jar, now);
    let s1 = step(http, urls, s, Input::Connected, jar, now);
    let wire = indep_wire(urls, jar, now, r);
    let jar1 = clazel_cookie::storage::spec::jar_after_retrieval(urls.rules, jar, (urls.request_url)(current_url(r)), indep_context(urls, r), now);
    let j1 = apply_ops(urls.rules, jar, s1.2);
    assert(j1 == jar1);
    lemma_sent_bytes_one(wire);
    if hops.len() > 0 {
        let d = hops[0];
        assert(delivers(http, d));
        let st1 = s1.0;
        assert(corresponds(urls, st1, r));
        lemma_run_bytes(http, urls, st1, r, j1, now, d);
        let s2 = step(http, urls, st1, Input::Bytes(d.bytes), j1, now);
        let j2 = apply_ops(urls.rules, j1, s2.2);
        lemma_sent_bytes_none(s2.1);
        let rest_hops = hops.drop_first();
        assert(all_deliver(http, rest_hops)) by {
            assert forall|i: int| 0 <= i < rest_hops.len() implies #[trigger] delivers(http, rest_hops[i]) by {
                assert(rest_hops[i] == hops[i + 1]);
            }
        }
        let rest = tx_fetch(http, urls, s2.0, j2, now, rest_hops);
        lemma_sent_bytes_concat(s1.1, s2.1);
        lemma_sent_bytes_concat(s1.1 + s2.1, rest.1);
        assert(sent_bytes(s1.1 + s2.1) =~= seq![wire]);
        let ind = indep_fetch(urls, jar, now, r, hops);
        match http_redirect_fetch(urls, r, d.response) {
            FetchResult::Response(resp) => {
                assert(s1.1 + s2.1 + rest.1 =~= s1.1 + s2.1);
                assert((s1.1 + s2.1)[(s1.1 + s2.1).len() - 1] == s2.1[s2.1.len() - 1]);
            },
            FetchResult::NetworkError => {
                assert(s1.1 + s2.1 + rest.1 =~= s1.1 + s2.1);
                assert((s1.1 + s2.1)[(s1.1 + s2.1).len() - 1] == s2.1[s2.1.len() - 1]);
            },
            FetchResult::Follow(r2) => {
                lemma_begin_fetchable(s2.0.url, s2.0.redirects, s2.0.tainted);
                let nb = begin(s2.0.url, s2.0.redirects, s2.0.tainted);
                if indep_fetchable(s2.0.url) {
                    lemma_independent_run(http, urls, s2.0, r2, j2, now, rest_hops);
                    let all = s1.1 + s2.1 + rest.1;
                    assert(all[all.len() - 1] == rest.1[rest.1.len() - 1]);
                    assert(sent_bytes(all) =~= seq![wire] + sent_bytes(rest.1));
                } else {
                    assert(s1.1 + s2.1 + rest.1 =~= s1.1 + s2.1);
                    assert((s1.1 + s2.1)[(s1.1 + s2.1).len() - 1] == s2.1[s2.1.len() - 1]);
                    assert(s2.1[s2.1.len() - 1] == nb.1[nb.1.len() - 1]);
                }
            },
        }
    }
}

/// **The whole run is Fetch's** (see the class in the header): for any URL
/// and cookie jar, driven through any hops that the parser delivers, the
/// transducer from `start(url)` sends exactly the request bytes Fetch's
/// loop sends (the same `Cookie` field at every hop, from the jar the
/// hops before it left), leaves the cookie jar Fetch's loop leaves, and
/// ends the way Fetch does: with the response HTTP-redirect fetch returns,
/// with a network error, or with the connection waiting for an answer.
pub proof fn theorem_independent_run(http: HttpFns, urls: UrlFns, url: Url, jar: Seq<Cookie>, now: int, hops: Seq<Hop>)
    requires
        all_deliver(http, hops),
    ensures
        sent_bytes(start(url).1 + tx_fetch(http, urls, start(url).0, jar, now, hops).1)
            == indep_fetch(urls, jar, now, FetchRequest { url_list: seq![url] }, hops).sent,
        tx_fetch(http, urls, start(url).0, jar, now, hops).2 == indep_fetch(urls, jar, now, FetchRequest { url_list: seq![url] }, hops).jar,
        outcome_matches(
            indep_fetch(urls, jar, now, FetchRequest { url_list: seq![url] }, hops).outcome,
            tx_fetch(http, urls, start(url).0, jar, now, hops).0,
            start(url).1 + tx_fetch(http, urls, start(url).0, jar, now, hops).1,
        ),
{
    let r = FetchRequest { url_list: seq![url] };
    let b = start(url);
    lemma_begin_fetchable(url, 0, false);
    assert(current_url(r) == url);
    if indep_fetchable(url) {
        assert(r.url_list.drop_last() =~= Seq::<Url>::empty());
        assert(corresponds(urls, b.0, r));
        lemma_independent_run(http, urls, b.0, r, jar, now, hops);
        let t = tx_fetch(http, urls, b.0, jar, now, hops);
        lemma_sent_bytes_concat(b.1, t.1);
        assert(super::theorems::no_sends(b.1));
        lemma_sent_bytes_none(b.1);
        assert(sent_bytes(b.1) + sent_bytes(t.1) =~= sent_bytes(t.1));
        let all = b.1 + t.1;
        assert(all[all.len() - 1] == t.1[t.1.len() - 1]);
    } else {
        assert(tx_fetch(http, urls, b.0, jar, now, hops) == (b.0, Seq::<Action>::empty(), jar));
        assert(b.1 + Seq::<Action>::empty() =~= b.1);
        assert(b.1 == seq![Action::Fail(Reason::NotFetched)]);
        assert(b.1.drop_last() =~= Seq::<Action>::empty());
        assert(sent_bytes(Seq::<Action>::empty()) =~= Seq::<Seq<u8>>::empty());
        assert(sent_bytes(b.1) =~= Seq::<Seq<u8>>::empty());
    }
}

} // verus!
