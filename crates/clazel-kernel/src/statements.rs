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
//!   the network shell may only report on a connection that is open
//!   (`user_tabs_open`; item 3.7). (A second correction, that no renderer is on a
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
/// for `next_id`; a `Kill` is for `id`. Item 3.7: it never gives a `Send` (a
/// frame from a renderer is never a wire byte); a `Connect` is for a
/// connection opened in this step (an id from `next_conn` on, below the new
/// counter); and a `Close` is for a connection of the sender's own tab (a
/// navigation it starts replaces its tab's in-flight one, or it is killed and
/// takes its tab's connections with it).
pub open spec fn reply_only_to_sender_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>) -> bool {
    let (s1, out) = step(rules, urls, fetch, s, Event::FromRenderer { id, bytes });
    forall|k: int|
        0 <= k < out.len() ==> match #[trigger] out[k] {
            Output::ToRenderer { id: x, .. } => x == id || (x == s.next_id && out.contains(Output::Spawn { id: x, policy: Policy::Renderer })),
            Output::Spawn { id: x, .. } => x == s.next_id,
            Output::Kill { id: x } => x == id,
            Output::Connect { conn: x, .. } => s.next_conn <= x < s1.next_conn,
            Output::Send { .. } => false,
            Output::Close { conn: x } => exists|i: int, j: int|
                0 <= i < s.renderers.len() && 0 <= j < s.conns.len() && s.renderers[i].id == id && s.conns[j].id == x && s.conns[j].tab == s.renderers[i].tab,
        }
}

/// `theorem_net_only_to_tab` (item 3.7; replaces `theorem_fetched_only_to_tab`):
/// a `Net { conn, _ }` event is attributed to the renderer of its connection's
/// tab, as a frame is to its socket's: its renderer-bound outputs are
/// `ToRenderer`s for that renderer or for the renderer spawned in that step (id
/// `next_id`, with a `Spawn` among the outputs), a `Spawn` for `next_id`, and a
/// `Kill` of that renderer. (Its `Connect`, `Send` and `Close` outputs concern
/// only that tab's connections: `connection_ownership_statement`.)
pub open spec fn net_only_to_tab_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput) -> bool {
    let out = step(rules, urls, fetch, s, Event::Net { conn, input }).1;
    match net_target(s, conn) {
        None => true,
        Some((c, _, _)) => forall|k: int|
            0 <= k < out.len() ==> match #[trigger] out[k] {
                Output::ToRenderer { id: x, .. } => (exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == c.tab && s.renderers[i].id == x) || (x == s.next_id && out.contains(
                    Output::Spawn { id: x, policy: Policy::Renderer },
                )),
                Output::Spawn { id: x, .. } => x == s.next_id,
                Output::Kill { id: x } => exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == c.tab && s.renderers[i].id == x,
                Output::Connect { .. } => true,
                Output::Send { .. } => true,
                Output::Close { .. } => true,
            },
    }
}

/// `theorem_net_answers_connection` (item 3.7; replaces
/// `theorem_fetched_answers_navigation`): a `Net { conn, _ }` event does
/// nothing (no state change, no output) unless it is about an open connection
/// ([`net_target`]: the connection is in the table, its tab is open and its
/// renderer is navigating); and a step that leaves a tab's renderer no longer
/// navigating leaves the tab no connection, so a late event of a finished
/// fetch is ignored. And a step on which the transducer ends the fetch
/// (`Done` or `Fail` among its actions) leaves the tab's renderer not
/// navigating and the tab without connections, whether the navigation
/// committed or failed (`commit_navigation`, `abort_navigation`).
pub open spec fn net_answers_connection_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput) -> bool {
    let (s1, out) = step(rules, urls, fetch, s, Event::Net { conn, input });
    &&& (net_target(s, conn) is None ==> s1 == s && out == Seq::<Output>::empty())
    &&& (net_target(s, conn) matches Some((c, _, _)) ==> forall|j: int, k: int|
        0 <= j < s1.renderers.len() && 0 <= k < s1.conns.len() && (#[trigger] s1.renderers[j]).tab == c.tab && (#[trigger] s1.conns[k]).tab == c.tab
            ==> s1.renderers[j].pending is Some)
    &&& (net_target(s, conn) matches Some((c, _, nav)) ==> {
        let actions = net_transducer_step(fetch, s, nav, input).1;
        (exists|a: int|
            0 <= a < actions.len() && ((#[trigger] actions[a]) is Done || actions[a] is Fail)) ==> {
            &&& forall|j: int| 0 <= j < s1.renderers.len() && (#[trigger] s1.renderers[j]).tab == c.tab ==> s1.renderers[j].pending is None
            &&& forall|k: int| 0 <= k < s1.conns.len() ==> (#[trigger] s1.conns[k]).tab != c.tab
        }
    })
}

/// `theorem_wire_cookies`, kernel level (item 3.7): every `Send` the kernel
/// outputs for a `Net` event is on the event's connection and is a `Send`
/// action of that connection's fetch's transducer at that step (nothing on
/// the wire is made anywhere else); so, by item 3.6's `theorem_wire_cookies`,
/// it is a valid request for the fetch's current URL whose only part derived
/// from the jar is its `Cookie` field, and that field is RFC 6265bis §5.8.3's
/// cookie-string for that request, from the kernel's jar at the step, at
/// its time, for the request's context (or no field, if no valid request can
/// carry that string).
///
/// The transducer reads the jar with its own Public Suffix List
/// (`fetch.urls.rules`), the kernel applies the jar operations with `rules`;
/// the statement is about a transducer whose list is the kernel's
/// (`fetch.urls.rules == rules`), which the shipped instantiation satisfies
/// (`real_theorems::corollary_real_wire_cookies`, and the exec kernel's
/// `fetch.urls.rules == psl()` precondition).
pub open spec fn wire_cookies_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput) -> bool {
    let out = step(rules, urls, fetch, s, Event::Net { conn, input }).1;
    fetch.urls.rules == rules ==> match net_target(s, conn) {
        None => true,
        Some((c, _, nav)) => {
            let actions = net_transducer_step(fetch, s, nav, input).1;
            forall|k: int|
                0 <= k < out.len() ==> match #[trigger] out[k] {
                    Output::Send { conn: x, bytes } => x == conn && (exists|a: int| 0 <= a < actions.len() && actions[a] == clazel_fetch::transducer::spec::Action::Send(bytes))
                        && clazel_fetch::transducer::contract::is_wire_request(
                        nav.fetch.url,
                        clazel_fetch::transducer::contract::carried(
                            nav.fetch.url,
                            clazel_cookie::storage::spec::retrieve_cookie_string(
                                rules,
                                s.jar,
                                (fetch.urls.request_url)(nav.fetch.url),
                                clazel_fetch::transducer::spec::request_context(fetch.urls, nav.fetch),
                                s.now,
                            ),
                        ),
                        bytes,
                    ),
                    _ => true,
                }
        },
    }
}

/// `theorem_net_jar_frame` (item 3.7): a `Net` event changes the jar only by
/// its fetch's jar operations: the jar after it is the jar before with the
/// operations of the transducer's step applied in order ([`apply_net_ops`]:
/// retrieval, and §5.7 storage behind [`store_allowed`]); and, by item 3.6's
/// `theorem_jar_frame` and `theorem_ops_name_request`, those operations are
/// the retrieval for the request the step builds and the storage of the
/// final response's own `Set-Cookie` lines, each naming only the fetch's
/// current request and the step's time. An event that is not about an open
/// connection leaves the jar as it is.
pub open spec fn net_jar_frame_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput) -> bool {
    let s1 = step(rules, urls, fetch, s, Event::Net { conn, input }).0;
    match net_target(s, conn) {
        None => s1.jar == s.jar,
        Some((c, _, nav)) => {
            let ops = net_transducer_step(fetch, s, nav, input).2;
            &&& s1.jar == apply_net_ops(rules, s.jar, ops)
            &&& clazel_fetch::transducer::contract::jar_frame(fetch.http, fetch.urls, nav.fetch, input, s.jar, s.now)
            &&& clazel_fetch::transducer::contract::ops_name_request(fetch.urls, nav.fetch, s.now, ops)
        },
    }
}

/// The tab an event is about, for connections: the sender's tab for a
/// `FromRenderer` of a renderer that exists, the tab of a `NavigateTab`, the
/// tab of the renderer that exits, and the owner of the connection of a `Net`
/// (when it is open). Other events are about no tab.
pub open spec fn event_tab(s: State, e: Event) -> Option<nat> {
    match e {
        Event::FromRenderer { id, .. } => match find_by_id(s.renderers, id, 0) {
            Some(i) => Some(s.renderers[i].tab),
            None => None,
        },
        Event::NavigateTab { tab, .. } => Some(tab),
        Event::RendererExited { id } => match find_by_id(s.renderers, id, 0) {
            Some(i) => Some(s.renderers[i].tab),
            None => None,
        },
        Event::Net { conn, .. } => match net_target(s, conn) {
            Some((c, _, _)) => Some(c.tab),
            None => None,
        },
        _ => None,
    }
}

/// `theorem_connection_ownership` (item 3.7): connections belong to the tab
/// whose fetch opened them, and an event concerns only its own tab's. For
/// every event, with `t` the tab it is about ([`event_tab`]):
///
/// - an event about no tab changes no connection and gives no `Connect`,
///   `Send` or `Close`;
/// - the connections of every other tab are still there, unchanged;
/// - a connection that is new (an id from `next_conn` on) belongs to `t`
///   and carries the partition key of `t`'s renderer's domain;
/// - a connection the old connections keep, they keep unchanged;
/// - every `Send` and `Close` names a connection of `t` in the old table or a
///   connection of this step; every `Connect` names a connection of this step
///   (which is `t`'s if it is still open);
/// - connection ids are allocated in order, never reused: the counter does
///   not go down, and a connection of the new table below the old counter is
///   in the old table.
pub open spec fn connection_ownership_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event) -> bool {
    let (s1, out) = step(rules, urls, fetch, s, e);
    &&& s.next_conn <= s1.next_conn
    &&& forall|j: int| 0 <= j < s1.conns.len() && (#[trigger] s1.conns[j]).id < s.next_conn ==> s.conns.contains(s1.conns[j])
    &&& (event_tab(s, e) is None ==> s1.conns == s.conns && s1.next_conn == s.next_conn && forall|k: int|
        0 <= k < out.len() ==> !((#[trigger] out[k]) is Connect || out[k] is Send || out[k] is Close))
    &&& (event_tab(s, e) matches Some(t) ==> {
        &&& forall|j: int| 0 <= j < s.conns.len() && (#[trigger] s.conns[j]).tab != t ==> s1.conns.contains(s.conns[j])
        &&& forall|j: int|
            0 <= j < s1.conns.len() && (#[trigger] s1.conns[j]).id >= s.next_conn ==> s1.conns[j].tab == t && exists|i: int|
                0 <= i < s1.renderers.len() && s1.renderers[i].tab == t && (s1.renderers[i].pending matches Some(nav) && nav.partition == s1.conns[j].partition)
        &&& forall|k: int|
            0 <= k < out.len() ==> match #[trigger] out[k] {
                Output::Connect { conn: x, .. } => s.next_conn <= x < s1.next_conn,
                Output::Send { conn: x, .. } => (exists|j: int| 0 <= j < s.conns.len() && s.conns[j].id == x && s.conns[j].tab == t) || (s.next_conn <= x < s1.next_conn),
                Output::Close { conn: x } => (exists|j: int| 0 <= j < s.conns.len() && s.conns[j].id == x && s.conns[j].tab == t) || (s.next_conn <= x < s1.next_conn),
                _ => true,
            }
    })
}

/// The event is handled by the kernel's own parsing of a URL: `OpenTab`,
/// `NavigateTab`, a renderer's frame that decodes to a `Navigate`, or the
/// `Net` event that commits a navigation (or ends it, or steps it: it
/// changes the renderer's `pending`).
pub open spec fn navigation_event(e: Event) -> bool {
    match e {
        Event::OpenTab { .. } => true,
        Event::NavigateTab { .. } => true,
        Event::Net { .. } => true,
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
/// the old jar after the eviction of expired cookies; for a `Net` about an
/// open connection ([`net_target`]), the jar after the jar operations of the
/// transducer's step ([`apply_net_ops`]: §5.8.3 retrieval for the request it
/// builds and §5.7 storage of the final response's `Set-Cookie` lines, each
/// with the request it answers, never for a public suffix); for anything else,
/// unchanged.
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
        Event::Net { conn, input } => match net_target(s, conn) {
            Some((_, _, nav)) => s1.jar == apply_net_ops(rules, s.jar, net_transducer_step(fetch, s, nav, input).2),
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
