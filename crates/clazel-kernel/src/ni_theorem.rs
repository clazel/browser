//! `lemma_navigate_declassify`, the four unwinding lemmas for kept events,
//! the induction over traces, and **`theorem_cookie_noninterference`**
//! (item 2.11).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// **`lemma_navigate_declassify`.**
pub proof fn lemma_navigate_declassify(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, e: Event)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::noninterference::other_domain_navigate(rules, urls, d, s1, e),
    ensures
        crate::noninterference::navigate_declassify_statement(rules, urls, fetch, d, s1, s2, e),
{
    let id = e->FromRenderer_id;
    let bytes = e->FromRenderer_bytes;
    assert(e == (Event::FromRenderer { id, bytes }));
    let d2 = crate::domain::event_domain(rules, s1, e)->Some_0;
    crate::unwinding_b::lemma_b_sender(rules, urls, d, s1, s2, id, bytes, d2);
    let i1 = find_by_id(s1.renderers, id, 0)->Some_0;
    let r = s1.renderers[i1];
    let dn = crate::domain::declassified(urls, s1, e)->Some_0;
    let (s1b, o1) = step(rules, urls, fetch, s1, e);
    let (s2b, o2) = step(rules, urls, fetch, s2, dn);
    // The declassified event is a NavigateTab of the sender's tab.
    if let Some(clazel_ipc::message::spec::Message::Navigate { url }) = decode_renderer_frame(bytes) {
        let relative = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url)->Some_0;
        let resolved = (urls.resolve)(r.url, relative)->Some_0;
        assert(dn == (Event::NavigateTab { tab: r.tab, url: resolved }));
        crate::unwind_base::lemma_found_contained(s1, r.tab);
        assert(s1.renderers.contains(r));
        crate::unwind_base::lemma_find_contained(urls, s1, r);
        if lock_of_url(urls, resolved, s1.next_id) is Some {
            crate::domain::lemma_declassified_is_navigate_tab(rules, urls, fetch, s1, e, dn);
            crate::unwinding::lemma_begin_consistency(rules, urls, fetch, d, s1, s2, r.tab, resolved);
            crate::unwind_base::lemma_outputs_for_same(rules, urls, d, s1, s2, s1b, s2b, o1);
        } else {
            // The kernel answers the sender with an error; the NavigateTab is ignored.
            assert(s1b == s1);
            assert(s2b == s2);
            assert(o2 == Seq::<Output>::empty());
            lemma_local_error_outputs(rules, urls, fetch, d, s1, s2, id, bytes, d2);
            assert(o1 == step(rules, urls, fetch, s1, e).1);
            reveal(Seq::filter);
            assert(crate::noninterference::outputs_for(rules, d, s2, s2b, o2) == Seq::<Output>::empty());
        }
    }
}

/// A `Navigate` answered with an error: nothing is addressed to `d`.
pub proof fn lemma_local_error_outputs(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns, fetch: FetchFns,
    d: crate::domain::Domain,
    s1: State,
    s2: State,
    id: nat,
    bytes: Seq<u8>,
    d2: crate::domain::Domain,
)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::domain::event_domain(rules, s1, Event::FromRenderer { id, bytes }) == Some(d2),
        d2 != d,
        decode_renderer_frame(bytes) matches Some(clazel_ipc::message::spec::Message::Navigate { url }) && clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(
            url,
        ) matches Some(relative) && (urls.resolve)(s1.renderers[find_by_id(s1.renderers, id, 0)->Some_0].url, relative) matches Some(resolved) && lock_of_url(
            urls,
            resolved,
            s1.next_id,
        ) is None,
    ensures
        crate::noninterference::outputs_for(rules, d, s1, s1, step(rules, urls, fetch, s1, Event::FromRenderer { id, bytes }).1) == Seq::<Output>::empty(),
{
    crate::unwind_base::lemma_found_contained(s1, id);
    let i1 = find_by_id(s1.renderers, id, 0)->Some_0;
    let r = s1.renderers[i1];
    let out = step(rules, urls, fetch, s1, Event::FromRenderer { id, bytes }).1;
    assert forall|k: int| 0 <= k < out.len() implies !crate::noninterference::addressed_to(rules, d, s1, s1, #[trigger] out[k]) by {
        if crate::noninterference::addressed_to(rules, d, s1, s1, out[k]) {
            let q = choose|q: Renderer| (s1.renderers.contains(q) || s1.renderers.contains(q)) && q.id == crate::domain::output_id(out[k]) && crate::domain::domain_of_renderer(rules, q) == d;
            assert(crate::domain::output_id(out[k]) == id);
            assert(s1.renderers.contains(r));
            crate::unwind_base::lemma_same_id_same_renderer(urls, s1.renderers, s1.next_id, q, r);
        }
    }
    crate::unwind_base::lemma_filter_none(out, |o: Output| crate::noninterference::addressed_to(rules, d, s1, s1, o));
}

// ---------------------------------------------------------------------
// Kept events.
// ---------------------------------------------------------------------

/// A kept event gives the same outputs in both runs, and related states.
pub proof fn lemma_kept_step(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, e: Event)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::noninterference::kept_event(rules, urls, d, s1, e),
    ensures
        step(rules, urls, fetch, s1, e).1 == step(rules, urls, fetch, s2, e).1,
        crate::noninterference::rel(rules, urls, d, step(rules, urls, fetch, s1, e).0, step(rules, urls, fetch, s2, e).0),
{
    match e {
        Event::FromRenderer { id, bytes } => {
            let d2 = crate::domain::event_domain(rules, s1, e)->Some_0;
            assert(crate::domain::event_domain(rules, s1, e) is Some);
            if d2 != d {
                assert(crate::domain::declassified(urls, s1, e) == Some(e));
                assert(crate::domain::declassified(urls, s1, e) matches Some(x) ==> x is NavigateTab);
                assert(false);
            }
            crate::unwinding_d::lemma_d_event(rules, urls, fetch, d, s1, s2, id, bytes);
        },
        Event::OpenTab { url, script } => {
            crate::unwinding::lemma_open_tab_consistency(rules, urls, fetch, d, s1, s2, url, script);
        },
        Event::NavigateTab { tab, url } => {
            crate::unwinding::lemma_begin_consistency(rules, urls, fetch, d, s1, s2, tab, url);
        },
        Event::Net { conn, input } => {
            crate::unwinding::lemma_net_consistency(rules, urls, fetch, d, s1, s2, conn, input);
        },
        Event::RendererExited { id } => {
            crate::unwinding::lemma_exited_consistency(rules, urls, fetch, d, s1, s2, id);
        },
        Event::Tick { time } => {
            crate::unwinding::lemma_tick_consistency(rules, urls, fetch, d, s1, s2, time);
        },
    }
}

/// **`lemma_output_consistency`.**
pub proof fn lemma_output_consistency(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, e: Event)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::noninterference::kept_event(rules, urls, d, s1, e),
    ensures
        crate::noninterference::output_consistency_statement(rules, urls, fetch, d, s1, s2, e),
{
    lemma_kept_step(rules, urls, fetch, d, s1, s2, e);
    let (s1b, o1) = step(rules, urls, fetch, s1, e);
    let (s2b, o2) = step(rules, urls, fetch, s2, e);
    crate::unwind_base::lemma_outputs_for_same(rules, urls, d, s1, s2, s1b, s2b, o1);
}

/// **`lemma_step_consistency`.**
pub proof fn lemma_step_consistency(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, e: Event)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::noninterference::kept_event(rules, urls, d, s1, e),
    ensures
        crate::noninterference::step_consistency_statement(rules, urls, fetch, d, s1, s2, e),
{
    lemma_kept_step(rules, urls, fetch, d, s1, s2, e);
}

// ---------------------------------------------------------------------
// The induction over traces.
// ---------------------------------------------------------------------

/// A run of `[pe] + rest`.
pub proof fn lemma_run_outputs_cons(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s: State, pe: Event, rest: Seq<Event>)
    ensures
        crate::noninterference::run_outputs_for(rules, urls, fetch, d, s, seq![pe] + rest) == crate::noninterference::outputs_for(rules, d, s, step(rules, urls, fetch, s, pe).0, step(rules, urls, fetch, s, pe).1)
            + crate::noninterference::run_outputs_for(rules, urls, fetch, d, step(rules, urls, fetch, s, pe).0, rest),
{
    let t = seq![pe] + rest;
    assert(t[0] == pe);
    assert(t.drop_first() =~= rest);
}

/// The trace theorem: related states, run on a trace and on its purge,
/// send the same outputs to `d`.
pub proof fn lemma_trace_noninterference(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, t: Seq<Event>)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::noninterference::user_tabs_open(rules, urls, fetch, s1, t),
    ensures
        crate::noninterference::run_outputs_for(rules, urls, fetch, d, s1, t) == crate::noninterference::run_outputs_for(rules, urls, fetch, d, s2, crate::domain::ipurge(rules, urls, fetch, s1, d, t)),
    decreases t.len(),
{
    if t.len() > 0 {
        let e = t[0];
        let rest = t.drop_first();
        let (s1b, o1) = step(rules, urls, fetch, s1, e);
        assert(crate::noninterference::user_tabs_open(rules, urls, fetch, s1b, rest));
        let pe_opt = crate::domain::ipurge_event(rules, urls, s1, d, e);
        let kept: Seq<Event> = match pe_opt {
            Some(pe) => seq![pe],
            None => seq![],
        };
        assert(crate::domain::ipurge(rules, urls, fetch, s1, d, t) == kept + crate::domain::ipurge(rules, urls, fetch, s1b, d, rest));
        reveal(Seq::filter);
        match pe_opt {
            None => {
                // A frame of a renderer that is not open, or of another domain without a
                // declassified part: the purged run does nothing.
                assert(e is FromRenderer);
                match crate::domain::event_domain(rules, s1, e) {
                    None => {
                        let id = e->FromRenderer_id;
                        crate::invariant::lemma_find_by_id(s1.renderers, id, 0);
                        assert(find_by_id(s1.renderers, id, 0) is None);
                        assert(s1b == s1 && o1 == Seq::<Output>::empty());
                        assert(crate::noninterference::outputs_for(rules, d, s1, s1b, o1) == Seq::<Output>::empty());
                        lemma_trace_noninterference(rules, urls, fetch, d, s1b, s2, rest);
                        assert(kept + crate::domain::ipurge(rules, urls, fetch, s1b, d, rest) == crate::domain::ipurge(rules, urls, fetch, s1b, d, rest));
                    },
                    Some(d2) => {
                        assert(d2 != d);
                        assert(crate::domain::declassified(urls, s1, e) is None);
                        crate::unwinding_b::lemma_local_respect(rules, urls, fetch, d, s1, s2, e);
                        lemma_trace_noninterference(rules, urls, fetch, d, s1b, s2, rest);
                        assert(kept + crate::domain::ipurge(rules, urls, fetch, s1b, d, rest) =~= crate::domain::ipurge(rules, urls, fetch, s1b, d, rest));
                    },
                }
            },
            Some(pe) => {
                if pe == e {
                    assert(crate::noninterference::kept_event(rules, urls, d, s1, e));
                    lemma_kept_step(rules, urls, fetch, d, s1, s2, e);
                    let (s2b, o2) = step(rules, urls, fetch, s2, e);
                    crate::unwind_base::lemma_outputs_for_same(rules, urls, d, s1, s2, s1b, s2b, o1);
                    lemma_trace_noninterference(rules, urls, fetch, d, s1b, s2b, rest);
                    lemma_run_outputs_cons(rules, urls, fetch, d, s2, e, crate::domain::ipurge(rules, urls, fetch, s1b, d, rest));
                } else {
                    // The declassified NavigateTab of a renderer of another domain.
                    assert(e is FromRenderer);
                    let d2 = crate::domain::event_domain(rules, s1, e)->Some_0;
                    assert(d2 != d);
                    assert(crate::domain::declassified(urls, s1, e) == Some(pe));
                    assert(crate::noninterference::other_domain_navigate(rules, urls, d, s1, e));
                    lemma_navigate_declassify(rules, urls, fetch, d, s1, s2, e);
                    let (s2b, o2) = step(rules, urls, fetch, s2, pe);
                    lemma_trace_noninterference(rules, urls, fetch, d, s1b, s2b, rest);
                    lemma_run_outputs_cons(rules, urls, fetch, d, s2, pe, crate::domain::ipurge(rules, urls, fetch, s1b, d, rest));
                }
            },
        }
    }
}

// ---------------------------------------------------------------------
// The theorem.
// ---------------------------------------------------------------------

/// **`theorem_cookie_noninterference`**, from any reachable state.
pub proof fn theorem_cookie_noninterference_from(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, d: crate::domain::Domain, t: Seq<Event>)
    requires
        reachable(rules, urls, fetch, s),
        crate::noninterference::user_tabs_open(rules, urls, fetch, s, t),
    ensures
        crate::noninterference::cookie_noninterference_statement(rules, urls, fetch, s, d, t),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    assert(crate::noninterference::rel(rules, urls, d, s, s));
    lemma_trace_noninterference(rules, urls, fetch, d, s, s, t);
}

/// **`theorem_cookie_noninterference`**, the plan's form: from the initial
/// state, with `purge(t, D)`. The outputs addressed to the renderers of `d`
/// are the same from `t` and from its purge. The only hypothesis is that the
/// user navigates only tabs that are open.
pub proof fn theorem_cookie_noninterference(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, t: Seq<Event>)
    requires
        crate::noninterference::user_tabs_open(rules, urls, fetch, init_state(), t),
    ensures
        crate::noninterference::run_outputs_for(rules, urls, fetch, d, init_state(), t) == crate::noninterference::run_outputs_for(rules, urls, fetch, d, init_state(), crate::domain::purge(rules, urls, fetch, d, t)),
{
    let t0 = Seq::<Event>::empty();
    assert(run_state(rules, urls, fetch, init_state(), t0) == init_state());
    assert(reachable(rules, urls, fetch, init_state()));
    theorem_cookie_noninterference_from(rules, urls, fetch, init_state(), d, t);
}

/// The renderer id an output names, renamed by `f`.
pub open spec fn rename_output(f: spec_fn(nat) -> nat, o: Output) -> Output {
    match o {
        Output::ToRenderer { id, bytes } => Output::ToRenderer { id: f(id), bytes },
        Output::Spawn { id, policy } => Output::Spawn { id: f(id), policy },
        Output::Kill { id } => Output::Kill { id: f(id) },
        Output::Connect { conn, host, port, tls } => Output::Connect { conn, host, port, tls },
        Output::Send { conn, bytes } => Output::Send { conn, bytes },
        Output::Close { conn } => Output::Close { conn },
    }
}

/// `f` is a bijection on renderer ids: it has an inverse `g`.
pub open spec fn is_bijection(f: spec_fn(nat) -> nat) -> bool {
    exists|g: spec_fn(nat) -> nat| #[trigger] is_inverse(f, g)
}

/// `g` is the inverse of `f`.
pub open spec fn is_inverse(f: spec_fn(nat) -> nat, g: spec_fn(nat) -> nat) -> bool {
    (forall|x: nat| #[trigger] g(f(x)) == x) && (forall|y: nat| #[trigger] f(g(y)) == y)
}

/// **`theorem_cookie_noninterference`, up to a bijection on renderer ids**,
/// as the plan states it: the outputs to `d` of `t` are those of its purge
/// with the ids renamed by a bijection. (The proof shows the identity does:
/// a declassified `NavigateTab` takes the same id from the counter as the
/// `Navigate` it replaces.)
pub proof fn theorem_cookie_noninterference_up_to_ids(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, t: Seq<Event>)
    requires
        crate::noninterference::user_tabs_open(rules, urls, fetch, init_state(), t),
    ensures
        exists|f: spec_fn(nat) -> nat|
            is_bijection(f) && crate::noninterference::run_outputs_for(rules, urls, fetch, d, init_state(), t) =~= crate::noninterference::run_outputs_for(rules, urls, fetch, d, init_state(), crate::domain::purge(rules, urls, fetch, d, t)).map_values(
                |o: Output| rename_output(f, o),
            ),
{
    theorem_cookie_noninterference(rules, urls, fetch, d, t);
    let f = |x: nat| x;
    let outs = crate::noninterference::run_outputs_for(rules, urls, fetch, d, init_state(), crate::domain::purge(rules, urls, fetch, d, t));
    assert(is_bijection(f)) by {
        let g = |x: nat| x;
        assert(is_inverse(f, g));
    }
    assert forall|k: int| 0 <= k < outs.len() implies outs.map_values(|o: Output| rename_output(f, o))[k] == outs[k] by {
        match outs[k] {
            Output::ToRenderer { id, bytes } => {},
            Output::Spawn { id, policy } => {},
            Output::Kill { id } => {},
            Output::Connect { conn, host, port, tls } => {},
            Output::Send { conn, bytes } => {},
            Output::Close { conn } => {},
        }
    }
    assert(outs.map_values(|o: Output| rename_output(f, o)) =~= outs);
}

} // verus!
