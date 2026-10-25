//! Domains, observations and the intransitive purge: the definitions item
//! 2.11's `theorem_cookie_noninterference` is stated with (Rushby, "Noninter-
//! ference, Transitivity, and Channel-Control Security Policies", 1992, §5).
//! The theorem and its unwinding lemmas are item 2.11's; these belong with
//! the state.
//!
//! The theorem, as restated in phase-2.md 2.11: for every domain `D`, every
//! trace `t` and every URL functions `urls`, the outputs addressed to
//! renderers whose domain is `D` (including their `Spawn` and `Kill`) are
//! the same from running `t` and from running `ipurge(t, D)`, up to a
//! bijection on renderer ids.
//!
//! Modelling choices:
//! - **A domain** ([`Domain`]) is a cookie root (`Root`), or one
//!   opaque-origin renderer on its own (`Opaque(id)`: the lock of such a
//!   renderer is `Opaque(its id)`, see `spec.rs`). The domain of a
//!   renderer is that of its lock ([`domain_of_renderer`]); a tuple lock
//!   with a host that does not canonicalize cannot arise in a state that
//!   satisfies `kernel_wf`, and gets the root of the empty host in this
//!   total function.
//! - **A `FromRenderer(r, _)` event belongs to the domain of `r`'s lock at
//!   that point in the trace** ([`event_domain`]), so the purge runs the
//!   original trace's states alongside, as the intransitive purge does. An
//!   event for an id that names no renderer belongs to no domain, changes
//!   nothing and has no output, and is dropped.
//! - **The declassified part of a `FromRenderer` event** ([`declassified`])
//!   is the `NavigateTab(tab, resolved, no_script())` that the kernel
//!   resolves a `Navigate` message into (the same function `navigate_tab`
//!   runs), and nothing for any other message, malformed frames included.
//!   It carries no script: that is the only thing it can carry into the new
//!   renderer besides the resolved URL.
//! - **The observation** ([`obs`]) is everything of the state that a
//!   renderer of the domain, or a later step on its behalf, can read or
//!   depend on: its renderers' records (ids included: item 2.11 compares up
//!   to a bijection of ids), the cookies under its root, the storage maps of
//!   its origins, and the time. Not the other domains' renderers and
//!   cookies, and not the id counter or the other domains' storage.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {


/// A security domain: the unit that must not interfere with another.
pub enum Domain {
    /// The renderers locked to origins whose hosts have this cookie root
    /// (`clazel_psl::spec::cookie_root`), they share cookies by RFC 6265bis.
    Root(clazel_cookie::matching::spec::CanonicalHost),
    /// One renderer whose lock is the opaque origin of this id.
    Opaque(nat),
}

/// The domain of a lock.
pub open spec fn domain_of_lock(rules: Seq<clazel_psl::spec::Rule>, lock: clazel_origin::spec::Origin) -> Domain {
    match lock {
        clazel_origin::spec::Origin::Opaque(id) => Domain::Opaque(id),
        clazel_origin::spec::Origin::Tuple { .. } => Domain::Root(match lock_host(lock) {
            Some(h) => clazel_cookie::storage::spec::cookie_root(rules, h),
            None => clazel_cookie::matching::spec::CanonicalHost { name: seq![], is_ip_address: false },
        }),
    }
}

/// The domain of a renderer: a cookie root, or the renderer itself for an
/// opaque lock.
pub open spec fn domain_of_renderer(rules: Seq<clazel_psl::spec::Rule>, r: Renderer) -> Domain {
    domain_of_lock(rules, r.lock)
}

/// The renderers of `s` in domain `d`.
pub open spec fn renderers_of_domain(rules: Seq<clazel_psl::spec::Rule>, s: State, d: Domain) -> Set<Renderer> {
    s.renderers.to_set().filter(|r: Renderer| domain_of_renderer(rules, r) == d)
}

/// The storage maps of `s` for the tuple origins in domain `d`.
pub open spec fn storage_of_domain(rules: Seq<clazel_psl::spec::Rule>, s: State, d: Domain) -> Map<clazel_origin::spec::Origin, Seq<StorageEntry>> {
    Map::new(
        s.storage.dom().filter(|o: clazel_origin::spec::Origin| o is Tuple && domain_of_lock(rules, o) == d),
        |o: clazel_origin::spec::Origin| s.storage[o],
    )
}

/// The cookies of domain `d`: those under its root; none for an
/// opaque-origin renderer.
pub open spec fn cookies_of_domain(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, d: Domain) -> Seq<clazel_cookie::storage::spec::Cookie> {
    match d {
        Domain::Root(root) => clazel_cookie::storage::spec::cookies_of_root(rules, jar, root),
        Domain::Opaque(_) => seq![],
    }
}

/// What domain `d` can observe of the state.
///
/// Changed by item 2.11 from the 2.10 definition, each for a reason the
/// proof found: the renderers are a *set* (the table's order is not
/// observable: every lookup is by id or tab, which are unique), and the
/// cookies are the *live* ones (cookies not yet evicted but expired are
/// invisible, and another domain's cookie call evicts them).
pub struct Observation {
    /// The records of its renderers.
    pub renderers: Set<Renderer>,
    /// The unexpired cookies under its root.
    pub cookies: Seq<clazel_cookie::storage::spec::Cookie>,
    /// The storage maps of its origins.
    pub storage: Map<clazel_origin::spec::Origin, Seq<StorageEntry>>,
    /// The time.
    pub now: int,
}

/// `obs(s, D)`.
pub open spec fn obs(rules: Seq<clazel_psl::spec::Rule>, s: State, d: Domain) -> Observation {
    Observation {
        renderers: renderers_of_domain(rules, s, d),
        cookies: cookies_of_domain(rules, clazel_cookie::storage::spec::evict_expired(s.jar, s.now), d),
        storage: storage_of_domain(rules, s, d),
        now: s.now,
    }
}

/// The domain a `FromRenderer(id, _)` event belongs to in state `s`: that
/// of the renderer `id`; a `Net { conn, _ }` event (item 3.7), that of the
/// renderer of the connection's tab, whose lock the fetch was started under
/// (as a frame is attributed to its socket's renderer). Other events, an id
/// that names no renderer and a connection that is not open belong to none.
pub open spec fn event_domain(rules: Seq<clazel_psl::spec::Rule>, s: State, e: Event) -> Option<Domain> {
    match e {
        Event::FromRenderer { id, .. } => match find_by_id(s.renderers, id, 0) {
            Some(i) => Some(domain_of_renderer(rules, s.renderers[i])),
            None => None,
        },
        Event::Net { conn, .. } => match net_target(s, conn) {
            Some((_, i, _)) => Some(domain_of_renderer(rules, s.renderers[i])),
            None => None,
        },
        _ => None,
    }
}

/// The declassified part of a `FromRenderer(id, bytes)` event in state `s`:
/// `NavigateTab(its tab, resolved URL)` if the frame decodes to a
/// `Navigate` that decodes and resolves, and nothing otherwise. (A
/// `Net` event has no declassified part of its own: it is kept whole for
/// every observer, see [`ipurge_event`].)
pub open spec fn declassified(urls: UrlFns, s: State, e: Event) -> Option<Event> {
    match e {
        Event::FromRenderer { id, bytes } => match find_by_id(s.renderers, id, 0) {
            None => None,
            Some(i) => {
                let r = s.renderers[i];
                match super::spec::decode_renderer_frame(bytes) {
                    Some(clazel_ipc::message::spec::Message::Navigate { url }) => match clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                        None => None,
                        Some(relative) => match (urls.resolve)(r.url, relative) {
                            None => None,
                            Some(resolved) => Some(Event::NavigateTab { tab: r.tab, url: resolved }),
                        },
                    },
                    _ => None,
                }
            },
        },
        _ => None,
    }
}

/// What the purge leaves of event `e` for observer `d`, in state `s`: the
/// event itself if it is not a renderer's or belongs to `d`, its
/// declassified part if it belongs to another domain.
///
/// A `Net` event is kept for every observer, whichever domain it is
/// attributed to (item 3.7). What it carries came from the network, not from
/// the renderer of its tab: that renderer contributed only the URL it
/// navigated to, which is the declassified part of its `Navigate` (a
/// `NavigateTab`, kept), and the kernel's decision to follow a redirect to
/// anywhere is the user's navigation, as item 2.11 treats a `Navigate`. So a
/// redirect from another domain's tab into `d`'s domain, and the cookies the
/// response chain sets under `d`'s root, are things `d` is allowed to see
/// depend on; what the other domain's renderer did otherwise is not. (The
/// network is outside every renderer domain: a server can echo the cookies
/// of the request it received into a body that a redirect hands to another
/// site's tab. That is the web, not a flow through the kernel; see `spec.rs`.)
pub open spec fn ipurge_event(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    s: State,
    d: Domain,
    e: Event,
) -> Option<Event> {
    match e {
        Event::FromRenderer { .. } => match event_domain(rules, s, e) {
            Some(d2) => if d2 == d { Some(e) } else { declassified(urls, s, e) },
            None => None,
        },
        _ => Some(e),
    }
}

/// `ipurge(t, D)` from state `s`: the trace `t` with every event of another
/// domain replaced by its declassified part, the states being those of `t`
/// itself.
pub open spec fn ipurge(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, d: Domain, t: Seq<Event>) -> Seq<Event>
    decreases t.len(),
{
    if t.len() == 0 {
        seq![]
    } else {
        let e = t[0];
        let kept = match ipurge_event(rules, urls, s, d, e) {
            Some(pe) => seq![pe],
            None => seq![],
        };
        kept + ipurge(rules, urls, fetch, step(rules, urls, fetch, s, e).0, d, t.drop_first())
    }
}

/// `purge(t, D)`: [`ipurge`] from the initial state.
pub open spec fn purge(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: Domain, t: Seq<Event>) -> Seq<Event> {
    ipurge(rules, urls, fetch, init_state(), d, t)
}

/// The renderer id an output is addressed to. (Which domain that renderer is
/// in is read in the state after the step for a `Spawn`, and before it for a
/// `Kill`; stating that is item 2.11's.) `Connect`, `Send` and `Close` are
/// addressed to the network shell, not to a renderer
/// (`noninterference::addressed_to` is false for them); their connection is
/// returned only to make the function total.
pub open spec fn output_id(o: Output) -> nat {
    match o {
        Output::ToRenderer { id, .. } => id,
        Output::Spawn { id, .. } => id,
        Output::Kill { id } => id,
        Output::Connect { conn, .. } => conn,
        Output::Send { conn, .. } => conn,
        Output::Close { conn } => conn,
    }
}


/// A renderer's `Navigate` that the kernel accepts does exactly what its
/// declassified part, a `NavigateTab`, does: the same state and the same
/// outputs (it starts the navigation and its fetch). (`lemma_navigate_declassify` of item 2.11 builds on this.) The
/// event is accepted when the resolved URL has a lock; otherwise the kernel
/// only replies with an error to the sender.
pub proof fn lemma_declassified_is_navigate_tab(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    s: State,
    e: Event,
    d: Event,
)
    requires
        declassified(urls, s, e) == Some(d),
        d is NavigateTab,
        lock_of_url(urls, d->NavigateTab_url, s.next_id) is Some,
    ensures
        step(rules, urls, fetch, s, e) == step(rules, urls, fetch, s, d),
{
    let id = e->FromRenderer_id;
    let i = find_by_id(s.renderers, id, 0)->Some_0;
    let r = s.renderers[i];
    match decode_renderer_frame(e->FromRenderer_bytes) {
        Some(clazel_ipc::message::spec::Message::Navigate { url }) => {},
        _ => {},
    }
}

} // verus!
