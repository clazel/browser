//! The isolation theorems of item 2.11 stated for the shipped kernel (item
//! 2.13): the Public Suffix List the kernel runs with ([`crate::contract::psl`]) and the real
//! URL functions ([`crate::urls::real_urls`]), whose exec counterpart is
//! `exec::real_urls::RealUrls`.
//!
//! None of these needs a proof of its own: each theorem is proven for every
//! `rules`, every [`UrlFns`] and every [`FetchFns`] (item 3.7), and a corollary
//! is that theorem at `real_urls()`, for any fetch: the shipped kernel's fetch
//! is a stand-in until item 3.6's transducer is joined (`exec::fetch`), and the
//! corollaries need no change when it is. They exist so that the guarantee of the shipped kernel is
//! stated, with the real parser, in one place. Each is also the guarantee
//! of `exec::real_urls::step_real`, which is proven to equal `step(psl(),
//! real_urls(), ..)`.
//!
//! What they say of URLs, for the real parser: a renderer's lock is the
//! URL §4.7 origin of the URL parsed from the string the kernel committed
//! (an opaque one replaced by the renderer's id); a `Navigate` from a
//! renderer is resolved by the basic URL parser against the committed URL,
//! started by `begin_navigation` and committed only by a `Net` event's
//! `Done` through `commit_navigation` and `navigate_tab`; and document.cookie is answered for
//! the lock's scheme and host and the committed URL's path.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Reachable states of the shipped kernel: from `init_state` by `step` over
/// the Public Suffix List and the real URL functions.
pub open spec fn real_reachable(fetch: FetchFns, s: State) -> bool {
    reachable(crate::contract::psl(), crate::urls::real_urls(), fetch, s)
}

/// Theorem `theorem_reply_only_to_sender` for the shipped kernel.
pub proof fn corollary_real_reply_only_to_sender(fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>)
    requires
        real_reachable(fetch, s),
    ensures
        crate::statements::reply_only_to_sender_statement(crate::contract::psl(), crate::urls::real_urls(), fetch, s, id, bytes),
{
    crate::theorems::theorem_reply_only_to_sender(crate::contract::psl(), crate::urls::real_urls(), fetch, s, id, bytes);
}

/// Theorems `theorem_lock_is_committed_origin` and
/// `theorem_lock_set_only_by_navigation` for the shipped kernel: every
/// renderer's lock is the origin of the URL string it committed, as the real
/// URL parser reads it, and only a navigation sets one.
pub proof fn corollary_real_lock_is_committed_origin(fetch: FetchFns, s: State)
    requires
        real_reachable(fetch, s),
    ensures
        crate::statements::lock_is_committed_origin_statement(crate::urls::real_urls(), s),
        forall|e: Event| #[trigger] crate::statements::lock_set_only_by_navigation_statement(crate::contract::psl(), crate::urls::real_urls(), fetch, s, e),
{
    crate::lock::theorem_lock_is_committed_origin(crate::contract::psl(), crate::urls::real_urls(), fetch, s);
}

/// Theorem `theorem_cookie_confidentiality` for the shipped kernel.
pub proof fn corollary_real_cookie_confidentiality(fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>)
    requires
        real_reachable(fetch, s),
    ensures
        crate::statements::cookie_confidentiality_statement(crate::contract::psl(), crate::urls::real_urls(), fetch, s, id, bytes),
{
    crate::cookie_theorems::theorem_cookie_confidentiality(crate::contract::psl(), crate::urls::real_urls(), fetch, s, id, bytes);
}

/// Theorem `theorem_cookie_integrity` for the shipped kernel.
pub proof fn corollary_real_cookie_integrity(fetch: FetchFns, s: State, e: Event)
    requires
        real_reachable(fetch, s),
    ensures
        crate::statements::cookie_integrity_statement(crate::contract::psl(), crate::urls::real_urls(), fetch, s, e),
{
    crate::cookie_theorems::theorem_cookie_integrity(crate::contract::psl(), crate::urls::real_urls(), fetch, s, e);
}

/// Item 3.7's `wire_cookies_statement` for the shipped kernel: the transducer
/// the shipped kernel steps reads the jar with the Public Suffix List the
/// kernel applies jar operations with (`psl()`), so the hypothesis of the
/// statement holds, for any other fetch parameter.
///
/// Stage 2 of the join writes this proof.
pub proof fn corollary_real_wire_cookies(fetch: FetchFns, s: State, conn: nat, input: NetInput)
    requires
        real_reachable(fetch, s),
        fetch.urls.rules == crate::contract::psl(),
    ensures
        crate::statements::wire_cookies_statement(crate::contract::psl(), crate::urls::real_urls(), fetch, s, conn, input),
{
}

/// Theorem `theorem_storage_same_origin` for the shipped kernel.
pub proof fn corollary_real_storage_same_origin(fetch: FetchFns, s: State, s2: State, id: nat, bytes: Seq<u8>)
    requires
        real_reachable(fetch, s),
    ensures
        crate::statements::storage_same_origin_statement(crate::contract::psl(), crate::urls::real_urls(), fetch, s, s2, id, bytes),
{
    crate::cookie_theorems::theorem_storage_same_origin(crate::contract::psl(), crate::urls::real_urls(), fetch, s, s2, id, bytes);
}

/// Theorem `theorem_cookie_noninterference` for the shipped kernel: the
/// outputs a domain `d` sees from the initial state on a trace in which the
/// user opens the tabs are those of the trace with every event `d` may not
/// see purged.
pub proof fn corollary_real_cookie_noninterference(fetch: FetchFns, d: crate::domain::Domain, t: Seq<Event>)
    requires
        crate::noninterference::user_tabs_open(crate::contract::psl(), crate::urls::real_urls(), fetch, init_state(), t),
    ensures
        crate::noninterference::run_outputs_for(crate::contract::psl(), crate::urls::real_urls(), fetch, d, init_state(), t) == crate::noninterference::run_outputs_for(
            crate::contract::psl(),
            crate::urls::real_urls(),
            fetch,
            d,
            init_state(),
            crate::domain::purge(crate::contract::psl(), crate::urls::real_urls(), fetch, d, t),
        ),
{
    crate::ni_theorem::theorem_cookie_noninterference(crate::contract::psl(), crate::urls::real_urls(), fetch, d, t);
}

} // verus!
