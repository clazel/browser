//! The statements of item 2.11's theorems, as predicates, committed before
//! their proofs (CLAUDE.md rule 3). `theorems.rs` proves each one as a
//! `theorem_*` lemma whose `ensures` is exactly the predicate here; this file
//! is what a reader checks.
//!
//! Corrections to the plan's text, each with its argument (the
//! counterexamples are `example_*` lemmas in `counterexamples.rs`):
//!
//! - `theorem_cookie_integrity`: the plan says the jar is "either unchanged
//!   or 6265bis storage applied". A `CookieGet` also updates the
//!   last-access-time of the cookies it returns (§5.8.3 step 5), which is
//!   neither; so a third alternative, the retrieval's own
//!   `jar_after_retrieval`, is allowed. Every cookie call also evicts expired
//!   cookies first, which the plan's "except expiry at Tick" omits.
//! - `theorem_cookie_noninterference`: see `noninterference.rs` and
//!   `counterexamples.rs`: the user may only navigate a tab that is open, and
//!   the network shell may only report the fetch of a tab that is open
//!   (`user_tabs_open`). (A second correction, that no renderer is on a
//!   public-suffix host, was first a hypothesis and is now closed in the
//!   kernel: such documents are cookie-averse.)

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `theorem_reply_only_to_sender`: the `ToRenderer` outputs of a
/// `FromRenderer(id, _)` event are for `id`, or for the renderer spawned in
/// that step (id `next_id`, with a `Spawn` among the outputs); a `Spawn` is
/// for `next_id`; a `Kill` is for `id`.
pub open spec fn reply_only_to_sender_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>) -> bool {
    let out = step(rules, urls, fetch, s, Event::FromRenderer { id, bytes }).1;
    forall|k: int|
        0 <= k < out.len() ==> match #[trigger] out[k] {
            Output::ToRenderer { id: x, .. } => x == id || (x == s.next_id && out.contains(Output::Spawn { id: x, policy: Policy::Renderer })),
            Output::Spawn { id: x, .. } => x == s.next_id,
            Output::Kill { id: x } => x == id,
            Output::Fetch { tab: x, .. } => exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].id == id && s.renderers[i].tab == x,
        }
}

/// `theorem_fetched_only_to_tab` (item 3.7): a `Fetched { tab, _ }` event is
/// attributed to the renderer of its tab, as a frame is to its socket's: its
/// outputs are `ToRenderer`s for that renderer or for the renderer spawned in
/// that step (id `next_id`, with a `Spawn` among the outputs), a `Spawn` for
/// `next_id`, and a `Kill` of that renderer; and no `Fetch` (a fetch's answer
/// does not start another fetch).
pub open spec fn fetched_only_to_tab_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, outcome: NetOutcome) -> bool {
    let out = step(rules, urls, fetch, s, Event::Fetched { tab, outcome }).1;
    forall|k: int|
        0 <= k < out.len() ==> match #[trigger] out[k] {
            Output::ToRenderer { id: x, .. } => (exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x) || (x == s.next_id && out.contains(
                Output::Spawn { id: x, policy: Policy::Renderer },
            )),
            Output::Spawn { id: x, .. } => x == s.next_id,
            Output::Kill { id: x } => exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x,
            Output::Fetch { .. } => false,
        }
}

/// `theorem_fetched_answers_navigation` (item 3.7): a `Fetched { tab, outcome
/// }` event does nothing (no state change, no output) unless it answers the
/// navigation in flight ([`fetched_run`]: its tab is open, its renderer is
/// navigating, and to the URL the outcome was fetched for); and one that
/// does leaves the tab's renderer no longer navigating, so a second answer
/// to the same navigation is ignored.
pub open spec fn fetched_answers_navigation_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, outcome: NetOutcome) -> bool {
    let (s1, out) = step(rules, urls, fetch, s, Event::Fetched { tab, outcome });
    &&& (fetched_run(fetch, s, tab, outcome) is None ==> s1 == s && out == Seq::<Output>::empty())
    &&& (fetched_run(fetch, s, tab, outcome) is Some ==> forall|j: int| 0 <= j < s1.renderers.len() && (#[trigger] s1.renderers[j]).tab == tab ==> s1.renderers[j].pending is None)
}

/// The event is handled by the kernel's own parsing of a URL: `OpenTab`,
/// `NavigateTab`, a renderer's frame that decodes to a `Navigate`, or the
/// `Fetched` that commits a navigation (or ends it: it changes the
/// renderer's `pending`).
pub open spec fn navigation_event(e: Event) -> bool {
    match e {
        Event::OpenTab { .. } => true,
        Event::NavigateTab { .. } => true,
        Event::Fetched { .. } => true,
        Event::FromRenderer { bytes, .. } => decode_renderer_frame(bytes) matches Some(clazel_ipc::message::spec::Message::Navigate { .. }),
        _ => false,
    }
}

/// `theorem_lock_is_committed_origin`, part 1 (a state): every renderer's
/// lock is the origin of its committed URL: `lock_of_url`, i.e. a tuple
/// origin itself, or `Opaque(renderer id)` for an opaque one.
pub open spec fn lock_is_committed_origin_statement(urls: UrlFns, s: State) -> bool {
    forall|i: int|
        0 <= i < s.renderers.len() ==> (lock_of_url(urls, (#[trigger] s.renderers[i]).url, s.renderers[i].id) == Some(s.renderers[i].lock)
            && match (urls.origin_of)(s.renderers[i].url) {
            Some(o) => match o {
                clazel_origin::spec::Origin::Tuple { .. } => s.renderers[i].lock == o,
                clazel_origin::spec::Origin::Opaque(_) => s.renderers[i].lock == clazel_origin::spec::Origin::Opaque(s.renderers[i].id),
            },
            None => false,
        })
}

/// `theorem_lock_is_committed_origin`, part 2 (a step): a renderer's lock
/// never changes while its id lives, and an event that is not a navigation
/// event creates no renderer (every renderer after the step was there
/// before, unchanged). A `Fetched` is a navigation event: the lock its
/// commit gives is `lock_of_url` of the final URL, the kernel's to lock.
pub open spec fn lock_set_only_by_navigation_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event) -> bool {
    let s1 = step(rules, urls, fetch, s, e).0;
    &&& forall|i: int, j: int|
        0 <= i < s.renderers.len() && 0 <= j < s1.renderers.len() && (#[trigger] s.renderers[i]).id == (#[trigger] s1.renderers[j]).id
            ==> s.renderers[i].lock == s1.renderers[j].lock
    &&& (!navigation_event(e) ==> forall|j: int| 0 <= j < s1.renderers.len() ==> s.renderers.contains(#[trigger] s1.renderers[j]))
}

/// The cookie string of HTML's `document.cookie` getter for a document with
/// lock `lock` and committed URL `url`: "if the document is a cookie-averse
/// Document object, then return the empty string; otherwise the cookie-string
/// for the document's URL for a non-HTTP API". The document's URL is its
/// lock's scheme and host and the committed URL's path.
pub open spec fn html_cookie_getter(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    now: int,
    lock: clazel_origin::spec::Origin,
    url: Seq<u32>,
) -> Seq<u8> {
    if cookie_averse(rules, lock) {
        seq![]
    } else {
        clazel_cookie::storage::spec::retrieve_cookie_string(
            rules,
            jar,
            clazel_cookie::storage::spec::RequestUrl {
                scheme: clazel_cookie::matching::spec::narrow(lock_scheme(lock)),
                host: lock_host(lock),
                path: (urls.path_of)(url),
            },
            document_context(lock),
            now,
        )
    }
}

/// `theorem_cookie_confidentiality`: if renderer `id` sends `CookieGet`, the
/// kernel's only output is a `CookieValue` to it holding exactly the getter's
/// string over the jar at that moment, and every cookie in it is not
/// HttpOnly, is one the lock's host and the committed path get
/// (`cookie_is_retrieved`), and is in the live jar.
pub open spec fn cookie_confidentiality_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>) -> bool {
    match find_by_id(s.renderers, id, 0) {
        None => true,
        Some(i) => {
            let r = s.renderers[i];
            decode_renderer_frame(bytes) matches Some(clazel_ipc::message::spec::Message::CookieGet) ==> {
                &&& step(rules, urls, fetch, s, Event::FromRenderer { id, bytes }).1 == reply(
                    r,
                    clazel_ipc::message::spec::Message::CookieValue { cookie_string: html_cookie_getter(rules, urls, s.jar, s.now, r.lock, r.url) },
                )
                &&& (!cookie_averse(rules, r.lock) ==> {
                    let list = clazel_cookie::storage::spec::retrieval_cookie_list(
                        rules,
                        clazel_cookie::storage::spec::evict_expired(s.jar, s.now),
                        request_url_of(urls, r),
                        document_context(r.lock),
                    );
                    forall|k: int|
                        0 <= k < list.len() ==> (!(#[trigger] list[k]).http_only_flag && lock_host(r.lock) is Some
                            && clazel_cookie::storage::spec::cookie_is_retrieved(
                            rules,
                            request_url_of(urls, r),
                            document_context(r.lock),
                            lock_host(r.lock)->Some_0,
                            list[k],
                        ) && clazel_cookie::storage::spec::evict_expired(s.jar, s.now).contains(list[k]))
                })
            }
        },
    }
}

/// `theorem_cookie_integrity`: after an event the jar is: for a
/// `FromRenderer(id, bytes)` of a renderer found whose frame is `CookieSet`,
/// 6265bis storage applied to its string; for `CookieGet`, the retrieval's
/// own update (§5.8.3 step 5); both with the sender's request URL and the
/// non-HTTP API flag (and unchanged for a cookie-averse lock); for `Tick`,
/// the old jar after the eviction of expired cookies; for a `Fetched` that
/// answers its tab's navigation in flight ([`fetched_run`]), the jar after
/// [`apply_stores`] of the `Set-Cookie` lines of the fetch's responses, each
/// with the request it answers (so only §5.7 storage, for the hosts of those
/// requests, and never for a public suffix); for anything else, unchanged.
pub open spec fn cookie_integrity_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event) -> bool {
    let s1 = step(rules, urls, fetch, s, e).0;
    match e {
        Event::FromRenderer { id, bytes } => match find_by_id(s.renderers, id, 0) {
            None => s1.jar == s.jar,
            Some(i) => {
                let r = s.renderers[i];
                match decode_renderer_frame(bytes) {
                    Some(clazel_ipc::message::spec::Message::CookieSet { cookie_string }) => if cookie_averse(rules, r.lock) {
                        s1.jar == s.jar
                    } else {
                        s1.jar == clazel_cookie::storage::spec::store_a_set_cookie_string(
                            rules,
                            s.jar,
                            cookie_string,
                            request_url_of(urls, r),
                            document_context(r.lock),
                            s.now,
                        )
                    },
                    Some(clazel_ipc::message::spec::Message::CookieGet) => if cookie_averse(rules, r.lock) {
                        s1.jar == s.jar
                    } else {
                        s1.jar == clazel_cookie::storage::spec::jar_after_retrieval(rules, s.jar, request_url_of(urls, r), document_context(r.lock), s.now)
                    },
                    _ => s1.jar == s.jar,
                }
            },
        },
        Event::Tick { time } => s1.jar == clazel_cookie::storage::spec::evict_expired(s.jar, if time > s.now { time } else { s.now }),
        Event::Fetched { tab, outcome } => match fetched_run(fetch, s, tab, outcome) {
            Some(run) => s1.jar == apply_stores(rules, s.jar, run.stores, s.now),
            None => s1.jar == s.jar,
        },
        _ => s1.jar == s.jar,
    }
}

/// A `localStorage` call.
pub open spec fn is_storage_message(m: clazel_ipc::message::spec::Message) -> bool {
    m is StorageGetItem || m is StorageSetItem || m is StorageRemoveItem || m is StorageClear || m is StorageKey || m is StorageLength
}

/// `theorem_storage_same_origin`: a storage request of renderer `id` (of a
/// tuple lock) changes only the map of its lock, nothing else of the state,
/// and its outputs and the new map of its lock are a function of the old map
/// of its lock alone: another state whose renderer `id` has the same lock
/// and whose map for that lock is the same gives the same outputs and the
/// same map.
pub open spec fn storage_same_origin_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, s2: State, id: nat, bytes: Seq<u8>) -> bool {
    match (find_by_id(s.renderers, id, 0), find_by_id(s2.renderers, id, 0)) {
        (Some(i), Some(i2)) => {
            let r = s.renderers[i];
            (decode_renderer_frame(bytes) matches Some(m) && is_storage_message(m) && r.lock is Tuple) ==> {
                let out = step(rules, urls, fetch, s, Event::FromRenderer { id, bytes });
                &&& forall|o: clazel_origin::spec::Origin| o != r.lock ==> storage_of(out.0, o) == storage_of(s, o)
                &&& out.0.renderers == s.renderers && out.0.jar == s.jar && out.0.next_id == s.next_id && out.0.now == s.now
                &&& (s2.renderers[i2].lock == r.lock && storage_of(s2, r.lock) == storage_of(s, r.lock) ==> step(rules, urls, fetch, s2, Event::FromRenderer { id, bytes }).1
                    == out.1 && storage_of(step(rules, urls, fetch, s2, Event::FromRenderer { id, bytes }).0, r.lock) == storage_of(out.0, r.lock))
            }
        },
        _ => true,
    }
}

} // verus!
