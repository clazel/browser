//! Quark's security properties (Jang, Tatlock and Lerner, "Establishing
//! Browser Security Guarantees through Formal Shim Verification", USENIX
//! Security 2012), restated for this state model and proven to follow from
//! item 2.11's theorems.
//!
//! Source. The text was read on 23 October 2026 from
//! `https://www.usenix.org/system/files/conference/usenixsecurity12/sec12-final217.pdf`
//! (extracted from the PDF, so the Coq of Figure 7 is read from a text dump
//! without spacing). The properties are in §5, "Security Properties of
//! Quark" (not §4: §4 of that text is Quark's implementation), Figure 7:
//!
//! ```text
//! Theorem tab_NI: forall tr1 tr2 t req rsp1 rsp2,
//!   tcorrect tr1 -> tcorrect tr2 -> from_tab t req ->
//!   (cur_tab tr1 = Some t <-> cur_tab tr2 = Some t) ->
//!   step_correct tr1 req rsp1 -> step_correct tr2 req rsp2 ->
//!   rsp1 = rsp2 \/ (exists m, rsp1 = WroteCMsg (cproc_for t tr1) m
//!                          /\ rsp2 = WroteCMsg (cproc_for t tr2) m).
//! Theorem no_xdom_cookie_set: forall tr1 tr2 cproc, tcorrect
//!   (tr1 ++ SetCookie key value cproc :: tr2) ->
//!   exists tr t, (tr2 = (SetCookieRequest t key value :: tr) /\
//!                 is_safe_cook (domain cproc) (domain_suffix t)).
//! ```
//!
//! and in prose: tab non-interference says "the kernel's response to a tab
//! is not affected by any other tab"; the kernel responds to the same request
//! "in the context of any other valid trace [...] which also contains tab t,
//! irrespective of what other tabs are present in tr2 or what actions they
//! take" (so also if all other tabs did not exist); cookie integrity says a
//! cookie process "is only ever asked to set a cookie in immediate response to
//! a cookie set request for the same exact cookie from a tab whose domain
//! matches that of the cookie process"; the confidentiality theorem
//! `no_xdom_cookie_get` is described the same way and "not shown" in the
//! paper.
//!
//! What changes for this model, each a difference in the kernel, not in the
//! meaning:
//!
//! - Quark's cookie processes hold the cookies and answer; ours hold them in
//!   the jar the kernel owns, so "the kernel forwards to the cookie process of
//!   the tab's domain" becomes "the kernel retrieves from, and stores into,
//!   the jar for the sender's lock host". The matching of domains is Quark's
//!   `is_safe_cook` (domain suffix); ours is RFC 6265bis's cookie root.
//! - Quark's principal is the *tab*; the paper names the move to domains as
//!   future work ("refine our notion of non-interference to be between domains
//!   instead of tabs"). Tabs of one cookie root share cookies by RFC 6265bis,
//!   which Quark's per-tab model forbids, so tab non-interference holds here
//!   *between domains* (item 2.11's `theorem_cookie_noninterference`) and not
//!   between two tabs of one root. The two-trace form below is Quark's.
//! - Quark's `tab_NI` says the responses are equal "or the same message to
//!   t's cookie process"; ours are equal outright, since the answer to a
//!   `CookieGet` is a function of the domain's own cookies.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Quark's `tab_NI`, in its two-trace form, between domains: two runs from
/// the initial state in which the observer's own events and the navigations
/// of the others are the same (the same purge for `d`), whatever the other
/// domains do otherwise, send the same bytes to the renderers of `d`.
pub proof fn quark_tab_non_interference(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, t1: Seq<Event>, t2: Seq<Event>)
    requires
        crate::noninterference::user_tabs_open(rules, urls, fetch, init_state(), t1),
        crate::noninterference::user_tabs_open(rules, urls, fetch, init_state(), t2),
        crate::domain::purge(rules, urls, fetch, d, t1) == crate::domain::purge(rules, urls, fetch, d, t2),
    ensures
        crate::noninterference::run_outputs_for(rules, urls, fetch, d, init_state(), t1) == crate::noninterference::run_outputs_for(rules, urls, fetch, d, init_state(), t2),
{
    crate::ni_theorem::theorem_cookie_noninterference(rules, urls, fetch, d, t1);
    crate::ni_theorem::theorem_cookie_noninterference(rules, urls, fetch, d, t2);
}

/// ... in particular as if every other domain did not exist (Quark's
/// corollary): the run of `t` and the run of its purge agree for `d`.
pub proof fn quark_tab_non_interference_alone(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, t: Seq<Event>)
    requires
        crate::noninterference::user_tabs_open(rules, urls, fetch, init_state(), t),
    ensures
        crate::noninterference::run_outputs_for(rules, urls, fetch, d, init_state(), t) == crate::noninterference::run_outputs_for(rules, urls, fetch, d, init_state(), crate::domain::purge(rules, urls, fetch, d, t)),
{
    crate::ni_theorem::theorem_cookie_noninterference(rules, urls, fetch, d, t);
}

// ---------------------------------------------------------------------
// Cookie integrity.
// ---------------------------------------------------------------------

/// A cookie of the jar after the cookie call was stored for the request host.
pub proof fn lemma_store_elements(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    s: Seq<u8>,
    url: clazel_cookie::storage::spec::RequestUrl,
    ctx: clazel_cookie::storage::spec::RequestContext,
    now: int,
    host: clazel_cookie::matching::spec::CanonicalHost,
    c: clazel_cookie::storage::spec::Cookie,
)
    requires
        url.host == Some(host),
        clazel_cookie::storage::spec::store_a_set_cookie_string(rules, jar, s, url, ctx, now).contains(c),
    ensures
        jar.contains(c) || clazel_cookie::storage::spec::cookie_root_of(rules, c) == clazel_cookie::storage::spec::cookie_root(rules, host),
{
    let live = clazel_cookie::storage::spec::evict_expired(jar, now);
    let any_root = clazel_cookie::matching::spec::CanonicalHost { name: seq![], is_ip_address: false };
    clazel_cookie::storage::isolation::lemma_evict_expired_props(rules, jar, now, any_root);
    if let Some(received) = clazel_cookie::set_cookie::spec::parse_a_set_cookie_string(s, url.path, now) {
        if let Some(new) = clazel_cookie::storage::spec::create_a_cookie(rules, live, url, ctx, received, now) {
            clazel_cookie::storage::isolation::lemma_store_within_root(rules, live, url, ctx, received, now, host, new);
            let ins = clazel_cookie::storage::spec::insert_a_cookie(live, new);
            let e = clazel_cookie::storage::spec::evict_expired(ins, now);
            clazel_cookie::storage::isolation::lemma_evict_expired_props(rules, ins, now, any_root);
            clazel_cookie::storage::isolation::lemma_evict_over_limit_props(rules, e, clazel_cookie::storage::spec::cookie_root_of(rules, new));
            assert(e.contains(c));
            assert(ins.contains(c));
            crate::unwind_base::lemma_insert_contains(live, new, c);
        }
    }
}

/// **Quark's cookie integrity** (`no_xdom_cookie_set`), for this model: a
/// cookie that appears in the jar, or changes, in a step is there because a
/// renderer asked to set it (`CookieSet`), and then its cookie root is the
/// root of the sender's lock host; or because a retrieval updated its
/// last-access-time (§5.8.3 step 5, which Quark has no analogue of); or
/// because a fetch's response chain set it (item 3.7: a `Fetched` event that
/// answers its tab's navigation), and then its cookie root is that of the
/// host of a request of the chain that may store.
pub open spec fn quark_cookie_integrity_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event) -> bool {
    let s1 = step(rules, urls, fetch, s, e).0;
    forall|c: clazel_cookie::storage::spec::Cookie|
        s1.jar.contains(c) ==> (s.jar.contains(c) || (exists|c0: clazel_cookie::storage::spec::Cookie| s.jar.contains(c0) && c == clazel_cookie::storage::spec::with_last_access_time(c0, s.now)) || (e is FromRenderer && (
        find_by_id(s.renderers, e->FromRenderer_id, 0) matches Some(i) && decode_renderer_frame(e->FromRenderer_bytes) matches Some(
            clazel_ipc::message::spec::Message::CookieSet { .. },
        ) && lock_host(s.renderers[i].lock) is Some && clazel_cookie::storage::spec::cookie_root_of(rules, c) == clazel_cookie::storage::spec::cookie_root(rules, lock_host(s.renderers[i].lock)->Some_0)))
            || fetch_stored_root(rules, fetch, s, e, c))
}

/// A `Fetched` event that answers its tab's navigation, one of whose
/// `Set-Cookie` lines may be stored and has the cookie root of `c`.
pub open spec fn fetch_stored_root(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns, s: State, e: Event, c: clazel_cookie::storage::spec::Cookie) -> bool {
    e is Fetched && (match fetched_run(fetch, s, e->Fetched_tab, e->Fetched_outcome) {
        Some(run) => exists|k: int|
            0 <= k < run.stores.len() && store_allowed(rules, (#[trigger] run.stores[k]).url) && clazel_cookie::storage::spec::cookie_root_of(rules, c) == clazel_cookie::storage::spec::cookie_root(
                rules,
                run.stores[k].url.host->Some_0,
            ),
        None => false,
    })
}

/// A cookie of the jar after a fetch's `Set-Cookie` lines was there before, or
/// has the cookie root of the host of a line's request, for a line that may
/// be stored.
pub proof fn lemma_apply_stores_elements(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    stores: Seq<HttpStore>,
    now: int,
    c: clazel_cookie::storage::spec::Cookie,
)
    requires
        apply_stores(rules, jar, stores, now).contains(c),
    ensures
        jar.contains(c) || exists|k: int|
            0 <= k < stores.len() && store_allowed(rules, (#[trigger] stores[k]).url) && clazel_cookie::storage::spec::cookie_root_of(rules, c) == clazel_cookie::storage::spec::cookie_root(
                rules,
                stores[k].url.host->Some_0,
            ),
    decreases stores.len(),
{
    if stores.len() > 0 {
        let st = stores[0];
        let jar1 = store_one(rules, jar, st, now);
        let rest = stores.drop_first();
        lemma_apply_stores_elements(rules, jar1, rest, now, c);
        if jar1.contains(c) && !jar.contains(c) {
            assert(store_allowed(rules, st.url));
            let host = st.url.host->Some_0;
            assert(st.url.host == Some(host));
            lemma_store_elements(rules, jar, st.line, st.url, st.ctx, now, host, c);
            assert(store_allowed(rules, stores[0].url));
        }
        if exists|k: int| 0 <= k < rest.len() && store_allowed(rules, (#[trigger] rest[k]).url) && clazel_cookie::storage::spec::cookie_root_of(rules, c) == clazel_cookie::storage::spec::cookie_root(
            rules,
            rest[k].url.host->Some_0,
        ) {
            let k = choose|k: int| 0 <= k < rest.len() && store_allowed(rules, (#[trigger] rest[k]).url) && clazel_cookie::storage::spec::cookie_root_of(rules, c) == clazel_cookie::storage::spec::cookie_root(
                rules,
                rest[k].url.host->Some_0,
            );
            assert(stores[k + 1] == rest[k]);
        }
    }
}

/// **Quark's cookie integrity follows from `theorem_cookie_integrity`.**
pub proof fn quark_cookie_integrity(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        quark_cookie_integrity_statement(rules, urls, fetch, s, e),
{
    crate::cookie_theorems::theorem_cookie_integrity(rules, urls, fetch, s, e);
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    let s1 = step(rules, urls, fetch, s, e).0;
    let any_root = clazel_cookie::matching::spec::CanonicalHost { name: seq![], is_ip_address: false };
    assert forall|c: clazel_cookie::storage::spec::Cookie| s1.jar.contains(c) implies (s.jar.contains(c) || (exists|c0: clazel_cookie::storage::spec::Cookie| s.jar.contains(c0) && c == clazel_cookie::storage::spec::with_last_access_time(c0, s.now))
        || (e is FromRenderer && (find_by_id(s.renderers, e->FromRenderer_id, 0) matches Some(i) && decode_renderer_frame(e->FromRenderer_bytes) matches Some(
        clazel_ipc::message::spec::Message::CookieSet { .. },
    ) && lock_host(s.renderers[i].lock) is Some && clazel_cookie::storage::spec::cookie_root_of(rules, c) == clazel_cookie::storage::spec::cookie_root(rules, lock_host(s.renderers[i].lock)->Some_0)))
        || fetch_stored_root(rules, fetch, s, e, c)) by {
        match e {
            Event::Fetched { tab, outcome } => {
                crate::unwind_base::lemma_fetched_frame(rules, urls, fetch, s, tab, outcome);
                if let Some(run) = fetched_run(fetch, s, tab, outcome) {
                    lemma_apply_stores_elements(rules, s.jar, run.stores, s.now, c);
                }
            },
            Event::Tick { time } => {
                let now = if time > s.now { time } else { s.now };
                clazel_cookie::storage::isolation::lemma_evict_expired_props(rules, s.jar, now, any_root);
            },
            Event::FromRenderer { id, bytes } => {
                crate::invariant::lemma_find_by_id(s.renderers, id, 0);
                if let Some(i) = find_by_id(s.renderers, id, 0) {
                    let r = s.renderers[i];
                    match decode_renderer_frame(bytes) {
                        Some(clazel_ipc::message::spec::Message::CookieSet { cookie_string }) => {
                            if !cookie_averse(rules, r.lock) {
                                crate::cookie_theorems::lemma_tuple_lock_host(urls, s.renderers, s.next_id, i);
                                let url = request_url_of(urls, r);
                                assert(url.host == lock_host(r.lock));
                                lemma_store_elements(rules, s.jar, cookie_string, url, document_context(r.lock), s.now, lock_host(r.lock)->Some_0, c);
                            }
                        },
                        Some(clazel_ipc::message::spec::Message::CookieGet) => {
                            if !cookie_averse(rules, r.lock) {
                                let url = request_url_of(urls, r);
                                let live = clazel_cookie::storage::spec::evict_expired(s.jar, s.now);
                                clazel_cookie::storage::isolation::lemma_evict_expired_props(rules, s.jar, s.now, any_root);
                                if let Some(h) = url.host {
                                    let g = clazel_cookie::storage::spec::update_last_access_time(rules, url, document_context(r.lock), h, s.now);
                                    let k = choose|k: int| 0 <= k < s1.jar.len() && s1.jar[k] == c;
                                    assert(s1.jar[k] == g(live[k]));
                                    assert(live.contains(live[k]));
                                    assert(s.jar.contains(live[k]));
                                    if clazel_cookie::storage::spec::cookie_is_retrieved(rules, url, document_context(r.lock), h, live[k]) {
                                        assert(c == clazel_cookie::storage::spec::with_last_access_time(live[k], s.now));
                                    } else {
                                        assert(c == live[k]);
                                    }
                                }
                            }
                        },
                        _ => {},
                    }
                }
            },
            _ => {},
        }
    }
}

// ---------------------------------------------------------------------
// Cookie confidentiality.
// ---------------------------------------------------------------------

/// **Quark's cookie confidentiality** (`no_xdom_cookie_get`, "not shown"
/// in the paper): every cookie the kernel puts in a `CookieValue` for a
/// renderer is under the cookie root of that renderer's lock host (and is not
/// HttpOnly): it follows from `theorem_cookie_confidentiality` and 2.9's
/// `lemma_retrieve_within_root`.
pub open spec fn quark_cookie_confidentiality_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, s: State, id: nat, bytes: Seq<u8>) -> bool {
    find_by_id(s.renderers, id, 0) matches Some(i) ==> (decode_renderer_frame(bytes) matches Some(clazel_ipc::message::spec::Message::CookieGet) && !cookie_averse(rules, s.renderers[i].lock,
    ) ==> {
        let r = s.renderers[i];
        let list = clazel_cookie::storage::spec::retrieval_cookie_list(rules, clazel_cookie::storage::spec::evict_expired(s.jar, s.now), request_url_of(urls, r), document_context(r.lock));
        forall|k: int|
            0 <= k < list.len() ==> clazel_cookie::storage::spec::cookie_root_of(rules, #[trigger] list[k]) == clazel_cookie::storage::spec::cookie_root(rules, lock_host(r.lock)->Some_0) && !list[k].http_only_flag
    })
}

/// **Quark's cookie confidentiality follows from `theorem_cookie_confidentiality`.**
pub proof fn quark_cookie_confidentiality(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        quark_cookie_confidentiality_statement(rules, urls, s, id, bytes),
{
    crate::cookie_theorems::theorem_cookie_confidentiality(rules, urls, fetch, s, id, bytes);
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
    if let Some(i) = find_by_id(s.renderers, id, 0) {
        let r = s.renderers[i];
        if decode_renderer_frame(bytes) matches Some(clazel_ipc::message::spec::Message::CookieGet) && !cookie_averse(rules, r.lock) {
            crate::cookie_theorems::lemma_tuple_lock_host(urls, s.renderers, s.next_id, i);
            let live = clazel_cookie::storage::spec::evict_expired(s.jar, s.now);
            let list = clazel_cookie::storage::spec::retrieval_cookie_list(rules, live, request_url_of(urls, r), document_context(r.lock));
            let host = lock_host(r.lock)->Some_0;
            assert forall|k: int| 0 <= k < list.len() implies clazel_cookie::storage::spec::cookie_root_of(rules, #[trigger] list[k]) == clazel_cookie::storage::spec::cookie_root(rules, host) && !list[k].http_only_flag by {
                assert(live.contains(list[k]));
                clazel_cookie::storage::isolation::lemma_filter_elem(s.jar, clazel_cookie::storage::spec::not_expired(s.now), list[k]);
                let q = choose|q: int| 0 <= q < s.jar.len() && s.jar[q] == list[k];
                assert(clazel_cookie::storage::isolation::cookie_domain_nonempty(list[k]));
                clazel_cookie::storage::isolation::lemma_retrieve_within_root(rules, request_url_of(urls, r), document_context(r.lock), host, list[k]);
            }
        }
    }
}

} // verus!
