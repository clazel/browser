//! The definitions and statements of `theorem_cookie_noninterference` (item
//! 2.11), committed before their proofs (`unwinding.rs`, `projection.rs`).
//!
//! The theorem, as proven (it differs from the plan's text in two places,
//! each shown necessary by an `example_*` lemma in `counterexamples.rs`; a
//! third, a hypothesis that no renderer is on a public-suffix host, was
//! removed by making such documents cookie-averse in the kernel, see
//! `spec.rs`):
//!
//! For every Public Suffix List `rules`, every `UrlFns`, every reachable
//! state `s`, every domain `d` and every trace `t` such that
//!
//! - `user_tabs_open(s, t)`: every `NavigateTab` of `t` names a tab that is
//!   open at that point of the run of `t` (a user types a URL into a tab they
//!   can see; without it, a renderer that kills itself closes its tab in
//!   one run and not in the run without its events), and so does every
//!   `Net` names an open connection (item 3.7: the network shell reports on
//!   a connection it was asked to open and not to close; a tab whose renderer
//!   killed itself in one run is closed in it, and its connections with it,
//!   and open in the purged run, where the same event would step the fetch
//!   and commit into `d`'s domain;
//!   `counterexamples::example_dead_tab_breaks_noninterference`);
//!
//! the outputs addressed to the renderers of `d` ([`run_outputs_for`], their
//! `Spawn` and `Kill` included) are the same from running `t` as from running
//! `ipurge(s, d, t)` (`domain.rs`), up to a bijection on renderer ids that is
//! the identity (the declassified `NavigateTab` takes the same id from the
//! shared counter as the `Navigate` it replaces).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The two hypotheses on traces.
// ---------------------------------------------------------------------

/// Every `NavigateTab` of the trace names a tab that is open when it runs,
/// and every `Net` an open connection ([`net_target`]).
pub open spec fn user_tabs_open(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, t: Seq<Event>) -> bool
    decreases t.len(),
{
    if t.len() == 0 {
        true
    } else {
        &&& (t[0] is NavigateTab ==> find_by_tab(s.renderers, t[0]->NavigateTab_tab, 0) is Some)
        &&& (t[0] is Net ==> net_target(s, t[0]->Net_conn) is Some)
        &&& user_tabs_open(rules, urls, fetch, step(rules, urls, fetch, s, t[0]).0, t.drop_first())
    }
}

// ---------------------------------------------------------------------
// Outputs addressed to a domain.
// ---------------------------------------------------------------------

/// Output `o` of the step from `s` to `s1` is addressed to a renderer of
/// domain `d`: one of the renderers of `s` or `s1` with that id (a `Kill`
/// names a renderer of `s`, a `Spawn` one of `s1`) is in `d`. A renderer's
/// lock never changes while its id lives, so the domain of an id is the same
/// in `s` and `s1`. `Connect`, `Send` and `Close` are addressed to the network shell, not to a
/// renderer.
pub open spec fn addressed_to(rules: Seq<clazel_psl::spec::Rule>, d: crate::domain::Domain, s: State, s1: State, o: Output) -> bool {
    !(o is Connect || o is Send || o is Close) && exists|r: Renderer|
        (s.renderers.contains(r) || s1.renderers.contains(r)) && r.id == crate::domain::output_id(o) && crate::domain::domain_of_renderer(rules, r) == d
}

/// The outputs of one step that are addressed to `d`.
pub open spec fn outputs_for(rules: Seq<clazel_psl::spec::Rule>, d: crate::domain::Domain, s: State, s1: State, out: Seq<Output>) -> Seq<Output> {
    out.filter(|o: Output| addressed_to(rules, d, s, s1, o))
}

/// The outputs addressed to `d` over the run of `t` from `s`, in order.
pub open spec fn run_outputs_for(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s: State, t: Seq<Event>) -> Seq<Output>
    decreases t.len(),
{
    if t.len() == 0 {
        seq![]
    } else {
        let (s1, out) = step(rules, urls, fetch, s, t[0]);
        outputs_for(rules, d, s, s1, out) + run_outputs_for(rules, urls, fetch, d, s1, t.drop_first())
    }
}

// ---------------------------------------------------------------------
// The relation between the run of the trace (`s1`) and of its purge (`s2`).
// ---------------------------------------------------------------------

/// The outputs addressed to renderers (a reply, a `Spawn`, a `Kill`), as
/// opposed to those addressed to the network shell.
pub open spec fn renderer_bound(o: Output) -> bool {
    o is ToRenderer || o is Spawn || o is Kill
}

/// The renderer-bound outputs of `out`, in order. Two related runs' outputs
/// agree on these (the network-bound ones differ in the order of `Close`s and
/// the octets of `Send`s, which no renderer sees).
pub open spec fn renderer_outs(out: Seq<Output>) -> Seq<Output> {
    out.filter(|o: Output| renderer_bound(o))
}

/// What `s1` and `s2` agree on of the connections (item 3.7): the counters,
/// every connection of `s1` is in `s2`, and every connection of `s2` whose tab
/// is open in `s1` is in `s1`. (`s2` may still hold the connections of tabs
/// that closed in the run of `t`.)
pub open spec fn rel_conn(s1: State, s2: State) -> bool {
    &&& s1.next_conn == s2.next_conn
    &&& forall|i: int| 0 <= i < s1.conns.len() ==> s2.conns.contains(#[trigger] s1.conns[i])
    &&& forall|i: int| 0 <= i < s2.conns.len() && find_by_tab(s1.renderers, (#[trigger] s2.conns[i]).tab, 0) is Some ==> s1.conns.contains(s2.conns[i])
}

/// What `s1` and `s2` agree on for observer `d`: the renderers of `d`, its
/// unexpired cookies, its storage maps, the counters and the time; and, to
/// keep them in step, that every renderer of `s1` is also in `s2` (`s2` may
/// still hold renderers that exited in the run of `t`: those of another
/// domain whose frames were dropped by the purge). Item 3.7: the same holds of
/// connections (every connection of `s1` is in `s2`; `s2` may still hold those
/// of tabs that closed in the run of `t`, and no others), so the two runs
/// open the same connections for the tabs they share, and the `Net` events
/// they are given step the same fetches.
pub open spec fn rel(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State) -> bool {
    &&& crate::invariant::kernel_wf(rules, urls, s1)
    &&& crate::invariant::kernel_wf(rules, urls, s2)
    &&& forall|i: int| 0 <= i < s1.renderers.len() ==> s2.renderers.contains(#[trigger] s1.renderers[i])
    &&& forall|i: int| 0 <= i < s2.renderers.len() && crate::domain::domain_of_renderer(rules, #[trigger] s2.renderers[i]) == d ==> s1.renderers.contains(s2.renderers[i])
    &&& s1.next_id == s2.next_id
    &&& rel_conn(s1, s2)
    &&& s1.now == s2.now
    &&& (d is Root ==> crate::domain::cookies_of_domain(rules, clazel_cookie::storage::spec::evict_expired(s1.jar, s1.now), d) == crate::domain::cookies_of_domain(
        rules,
        clazel_cookie::storage::spec::evict_expired(s2.jar, s2.now),
        d,
    ))
    &&& forall|o: clazel_origin::spec::Origin| o is Tuple && crate::domain::domain_of_lock(rules, o) == d ==> storage_of(s1, o) == storage_of(s2, o)
}

// ---------------------------------------------------------------------
// The unwinding lemmas' statements.
// ---------------------------------------------------------------------

/// An event that stays in the purge for `d` as it is (`ipurge_event` is
/// `Some(e)`) and that the run of the purge can take: a `NavigateTab` or a
/// `Net` names an open connection.
pub open spec fn kept_event(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, e: Event) -> bool {
    &&& crate::domain::ipurge_event(rules, urls, s1, d, e) == Some(e)
    &&& (e is NavigateTab ==> find_by_tab(s1.renderers, e->NavigateTab_tab, 0) is Some)
    &&& (e is Net ==> net_target(s1, e->Net_conn) is Some)
}

/// `lemma_output_consistency`: from related states, a kept event gives the
/// same outputs to `d` in both runs.
pub open spec fn output_consistency_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, e: Event) -> bool {
    let (s1b, out1) = step(rules, urls, fetch, s1, e);
    let (s2b, out2) = step(rules, urls, fetch, s2, e);
    outputs_for(rules, d, s1, s1b, out1) == outputs_for(rules, d, s2, s2b, out2)
}

/// `lemma_step_consistency`: from related states, a kept event leaves them
/// related.
pub open spec fn step_consistency_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, e: Event) -> bool {
    rel(rules, urls, d, step(rules, urls, fetch, s1, e).0, step(rules, urls, fetch, s2, e).0)
}

/// An event of a renderer of another domain that has no declassified part:
/// anything but a `Navigate` whose URL decodes and resolves (a `Navigate`
/// that does not is answered with an error to the sender and changes nothing,
/// like a message that is not a `Navigate`).
pub open spec fn other_domain_local(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, e: Event) -> bool {
    &&& e is FromRenderer
    &&& crate::domain::event_domain(rules, s1, e) matches Some(d2) && d2 != d
    &&& crate::domain::declassified(urls, s1, e) is None
}

/// `lemma_local_respect` (the plan's "not a `Navigate`", widened to "no
/// declassified part"): such an event leaves the state related to the
/// unchanged other one, and sends nothing to `d`.
pub open spec fn local_respect_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, e: Event) -> bool {
    let (s1b, out1) = step(rules, urls, fetch, s1, e);
    &&& rel(rules, urls, d, s1b, s2)
    &&& outputs_for(rules, d, s1, s1b, out1) == Seq::<Output>::empty()
}

/// An event of a renderer of another domain, that is a `Navigate` that
/// resolves: it has a declassified part.
pub open spec fn other_domain_navigate(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, e: Event) -> bool {
    &&& e is FromRenderer
    &&& crate::domain::event_domain(rules, s1, e) matches Some(d2) && d2 != d
    &&& crate::domain::declassified(urls, s1, e) is Some
}

/// `lemma_navigate_declassify`: such an event changes the state, and sends
/// to `d`, exactly as its declassified `NavigateTab` does in the other run.
pub open spec fn navigate_declassify_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, e: Event) -> bool {
    let dn = crate::domain::declassified(urls, s1, e)->Some_0;
    let (s1b, out1) = step(rules, urls, fetch, s1, e);
    let (s2b, out2) = step(rules, urls, fetch, s2, dn);
    &&& rel(rules, urls, d, s1b, s2b)
    &&& outputs_for(rules, d, s1, s1b, out1) == outputs_for(rules, d, s2, s2b, out2)
}

/// `theorem_cookie_noninterference` (from any reachable state; `s` the
/// initial one gives the plan's `purge`).
pub open spec fn cookie_noninterference_statement(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, d: crate::domain::Domain, t: Seq<Event>) -> bool {
    run_outputs_for(rules, urls, fetch, d, s, t) == run_outputs_for(rules, urls, fetch, d, s, crate::domain::ipurge(rules, urls, fetch, s, d, t))
}

} // verus!
