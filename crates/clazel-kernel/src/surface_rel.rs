//! Item 2.11's noninterference over item 5.18's events: the unwinding lemmas
//! for a GPU process's frame (`FromGpu`), the host's `Resize` and the user's
//! `Input`, and the facts about the titles of a domain they need.
//!
//! `rel` (`noninterference.rs`) holds the two runs to the same viewports
//! (only `Resize` sets them, and every purge keeps it) and to the same
//! titles of the observer's locks ([`crate::domain::titles_of_domain`]). A
//! title entry carries its renderer's lock, and an entry is read only by a
//! renderer with that lock ([`title_of`]), so the titles of another domain,
//! which the purge's runs do not share, never reach the observer.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Filters.
// ---------------------------------------------------------------------

/// Filtering a sequence with an element added at the end.
pub proof fn lemma_filter_push<A>(s: Seq<A>, x: A, p: spec_fn(A) -> bool)
    ensures
        s.push(x).filter(p) == (if p(x) {
            s.filter(p).push(x)
        } else {
            s.filter(p)
        }),
{
    reveal(Seq::filter);
    assert(s.push(x).drop_last() =~= s);
    assert(s.push(x).last() == x);
}

/// Two filters commute.
pub proof fn lemma_filter_commute<A>(s: Seq<A>, p: spec_fn(A) -> bool, q: spec_fn(A) -> bool)
    ensures
        s.filter(p).filter(q) == s.filter(q).filter(p),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let t = s.drop_last();
        let x = s.last();
        assert(s == t.push(x));
        lemma_filter_commute(t, p, q);
        lemma_filter_push(t, x, p);
        lemma_filter_push(t, x, q);
        if p(x) {
            lemma_filter_push(t.filter(p), x, q);
        }
        if q(x) {
            lemma_filter_push(t.filter(q), x, p);
        }
    }
}

/// A filter that keeps every element changes nothing.
pub proof fn lemma_filter_all<A>(s: Seq<A>, p: spec_fn(A) -> bool)
    requires
        forall|i: int| 0 <= i < s.len() ==> p(#[trigger] s[i]),
    ensures
        s.filter(p) == s,
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let t = s.drop_last();
        assert forall|i: int| 0 <= i < t.len() implies p(#[trigger] t[i]) by {
            assert(t[i] == s[i]);
        }
        lemma_filter_all(t, p);
        assert(p(s[s.len() - 1]));
        assert(t.push(s.last()) =~= s);
    }
}

// ---------------------------------------------------------------------
// The titles of a domain.
// ---------------------------------------------------------------------

/// Forgetting a title commutes with taking a domain's titles.
pub proof fn lemma_titles_forget_commute(rules: Seq<clazel_psl::spec::Rule>, ts: Seq<Titled>, id: nat, lock: clazel_origin::spec::Origin, d: crate::domain::Domain)
    ensures
        crate::domain::titles_of_domain(rules, forget_title(ts, id, lock), d) == forget_title(crate::domain::titles_of_domain(rules, ts, d), id, lock),
{
    lemma_filter_commute(
        ts,
        |x: Titled| !(x.id == id && x.lock == lock),
        |x: Titled| crate::domain::domain_of_lock(rules, x.lock) == d,
    );
}

/// Forgetting a title under a lock of another domain does not change the
/// domain's titles.
pub proof fn lemma_titles_forget_other(rules: Seq<clazel_psl::spec::Rule>, ts: Seq<Titled>, id: nat, lock: clazel_origin::spec::Origin, d: crate::domain::Domain)
    requires
        crate::domain::domain_of_lock(rules, lock) != d,
    ensures
        crate::domain::titles_of_domain(rules, forget_title(ts, id, lock), d) == crate::domain::titles_of_domain(rules, ts, d),
{
    lemma_titles_forget_commute(rules, ts, id, lock, d);
    let td = crate::domain::titles_of_domain(rules, ts, d);
    let keep = |x: Titled| !(x.id == id && x.lock == lock);
    let ind = |x: Titled| crate::domain::domain_of_lock(rules, x.lock) == d;
    assert forall|i: int| 0 <= i < td.len() implies keep(#[trigger] td[i]) by {
        ts.lemma_filter_pred(ind, i);
    }
    lemma_filter_all(td, keep);
}

/// Setting a title under a lock of another domain does not change the
/// domain's titles.
pub proof fn lemma_titles_set_other(rules: Seq<clazel_psl::spec::Rule>, ts: Seq<Titled>, id: nat, lock: clazel_origin::spec::Origin, title: Seq<u8>, d: crate::domain::Domain)
    requires
        crate::domain::domain_of_lock(rules, lock) != d,
    ensures
        crate::domain::titles_of_domain(rules, set_title(ts, id, lock, title), d) == crate::domain::titles_of_domain(rules, ts, d),
{
    lemma_titles_forget_other(rules, ts, id, lock, d);
    lemma_filter_push(forget_title(ts, id, lock), Titled { id, lock, title }, |x: Titled| crate::domain::domain_of_lock(rules, x.lock) == d);
}

/// Forgetting the same title in two runs whose domain's titles agree keeps
/// them agreeing.
pub proof fn lemma_titles_forget_same(
    rules: Seq<clazel_psl::spec::Rule>,
    ts1: Seq<Titled>,
    ts2: Seq<Titled>,
    id: nat,
    lock: clazel_origin::spec::Origin,
    d: crate::domain::Domain,
)
    requires
        crate::domain::titles_of_domain(rules, ts1, d) == crate::domain::titles_of_domain(rules, ts2, d),
    ensures
        crate::domain::titles_of_domain(rules, forget_title(ts1, id, lock), d) == crate::domain::titles_of_domain(rules, forget_title(ts2, id, lock), d),
{
    lemma_titles_forget_commute(rules, ts1, id, lock, d);
    lemma_titles_forget_commute(rules, ts2, id, lock, d);
}

/// Setting the same title in two runs whose domain's titles agree keeps them
/// agreeing.
pub proof fn lemma_titles_set_same(
    rules: Seq<clazel_psl::spec::Rule>,
    ts1: Seq<Titled>,
    ts2: Seq<Titled>,
    id: nat,
    lock: clazel_origin::spec::Origin,
    title: Seq<u8>,
    d: crate::domain::Domain,
)
    requires
        crate::domain::titles_of_domain(rules, ts1, d) == crate::domain::titles_of_domain(rules, ts2, d),
    ensures
        crate::domain::titles_of_domain(rules, set_title(ts1, id, lock, title), d) == crate::domain::titles_of_domain(rules, set_title(ts2, id, lock, title), d),
{
    lemma_titles_forget_same(rules, ts1, ts2, id, lock, d);
    let ind = |x: Titled| crate::domain::domain_of_lock(rules, x.lock) == d;
    lemma_filter_push(forget_title(ts1, id, lock), Titled { id, lock, title }, ind);
    lemma_filter_push(forget_title(ts2, id, lock), Titled { id, lock, title }, ind);
}

/// The title of a renderer of domain `d` is read from `d`'s titles alone.
pub proof fn lemma_title_of_domain(rules: Seq<clazel_psl::spec::Rule>, ts: Seq<Titled>, r: Renderer, d: crate::domain::Domain)
    requires
        crate::domain::domain_of_renderer(rules, r) == d,
    ensures
        title_of(ts, r) == title_of(crate::domain::titles_of_domain(rules, ts, d), r),
    decreases ts.len(),
{
    let ind = |x: Titled| crate::domain::domain_of_lock(rules, x.lock) == d;
    if ts.len() > 0 {
        let x = ts[0];
        let rest = ts.drop_first();
        assert(ts =~= seq![x] + rest);
        rest.lemma_filter_prepend(x, ind);
        lemma_title_of_domain(rules, rest, r, d);
        let fr = rest.filter(ind);
        if ind(x) {
            assert(ts.filter(ind) == seq![x] + fr);
            assert((seq![x] + fr)[0] == x);
            assert((seq![x] + fr).drop_first() =~= fr);
        } else {
            assert(ts.filter(ind) =~= fr);
            assert(!(x.id == r.id && x.lock == r.lock));
        }
    } else {
        reveal(Seq::filter);
    }
}

/// Related states give a renderer of `d` the same title.
pub proof fn lemma_title_of_rel(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, r: Renderer)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::domain::domain_of_renderer(rules, r) == d,
    ensures
        title_of(s1.titles, r) == title_of(s2.titles, r),
{
    lemma_title_of_domain(rules, s1.titles, r, d);
    lemma_title_of_domain(rules, s2.titles, r, d);
}

// ---------------------------------------------------------------------
// `Resize` and `Input`: the user's, kept for every observer.
// ---------------------------------------------------------------------

/// The outputs of a `Resize` or an `Input` of `tab`: for its renderer, if it
/// has one.
pub open spec fn user_outputs_for_tab(s: State, tab: nat, out: Seq<Output>) -> bool {
    match find_by_tab(s.renderers, tab, 0) {
        None => out == Seq::<Output>::empty(),
        Some(i) => forall|k: int| 0 <= k < out.len() ==> crate::domain::output_id(#[trigger] out[k]) == s.renderers[i].id && (out[k] is ToRenderer || out[k] is ToGpu),
    }
}

/// From related states, a step whose outputs are all for the renderer of
/// `tab` (if any) and whose state keeps the table gives `d` the same
/// outputs in both runs, provided both runs give the same outputs when the
/// first run has the tab.
pub proof fn lemma_user_outputs(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    d: crate::domain::Domain,
    s1: State,
    s2: State,
    s1b: State,
    s2b: State,
    tab: nat,
    o1: Seq<Output>,
    o2: Seq<Output>,
)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::noninterference::rel(rules, urls, d, s1b, s2b),
        s1b.renderers == s1.renderers,
        s2b.renderers == s2.renderers,
        user_outputs_for_tab(s1, tab, o1),
        user_outputs_for_tab(s2, tab, o2),
        find_by_tab(s1.renderers, tab, 0) is Some ==> o1 == o2,
    ensures
        crate::noninterference::outputs_for(rules, d, s1, s1b, o1) == crate::noninterference::outputs_for(rules, d, s2, s2b, o2),
{
    if find_by_tab(s1.renderers, tab, 0) is Some {
        crate::net_rel::lemma_renderer_outs_concat(o1, Seq::<Output>::empty());
        crate::unwind_base::lemma_outputs_for_same_rb(rules, urls, d, s1, s2, s1b, s2b, o1, o2);
    } else {
        crate::unwind_base::lemma_filter_none(o1, |o: Output| crate::noninterference::addressed_to(rules, d, s1, s1b, o));
        if let Some(i2) = find_by_tab(s2.renderers, tab, 0) {
            crate::unwind_base::lemma_found_contained(s2, tab);
            let r2 = s2.renderers[i2];
            // `r2` is not in `d`: a renderer of `d` in the second run is in the
            // first, where the tab has none.
            assert(crate::domain::domain_of_renderer(rules, r2) != d) by {
                if crate::domain::domain_of_renderer(rules, r2) == d {
                    assert(s1.renderers.contains(r2));
                    crate::unwind_base::lemma_find_contained(urls, s1, r2);
                }
            }
            assert forall|k: int| 0 <= k < o2.len() implies !crate::noninterference::addressed_to(rules, d, s2, s2b, #[trigger] o2[k]) by {
                if crate::noninterference::addressed_to(rules, d, s2, s2b, o2[k]) {
                    let q = choose|q: Renderer|
                        (s2.renderers.contains(q) || s2b.renderers.contains(q)) && (if o2[k] is Show || o2[k] is Paint || o2[k] is GpuStopped {
                            q.tab == crate::domain::output_id(o2[k])
                        } else {
                            q.id == crate::domain::output_id(o2[k])
                        }) && crate::domain::domain_of_renderer(rules, q) == d;
                    assert(s2.renderers.contains(r2));
                    crate::unwind_base::lemma_same_id_same_renderer(urls, s2.renderers, s2.next_id, q, r2);
                }
            }
            crate::unwind_base::lemma_filter_none(o2, |o: Output| crate::noninterference::addressed_to(rules, d, s2, s2b, o));
        } else {
            crate::unwind_base::lemma_filter_none(o2, |o: Output| crate::noninterference::addressed_to(rules, d, s2, s2b, o));
        }
    }
}

/// `Resize` from related states: related states, and the same outputs to
/// `d`.
pub proof fn lemma_resize_consistency(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    d: crate::domain::Domain,
    s1: State,
    s2: State,
    tab: nat,
    v: Viewport,
)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
    ensures
        crate::noninterference::rel(rules, urls, d, resize(s1, tab, v).0, resize(s2, tab, v).0),
        crate::noninterference::outputs_for(rules, d, s1, resize(s1, tab, v).0, resize(s1, tab, v).1) == crate::noninterference::outputs_for(
            rules,
            d,
            s2,
            resize(s2, tab, v).0,
            resize(s2, tab, v).1,
        ),
{
    let e = Event::Resize { tab, width: v.width, height: v.height, scale: v.scale };
    assert(step(rules, urls, fetch, s1, e) == resize(s1, tab, v));
    assert(step(rules, urls, fetch, s2, e) == resize(s2, tab, v));
    crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s1, e);
    crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s2, e);
    let (s1b, o1) = resize(s1, tab, v);
    let (s2b, o2) = resize(s2, tab, v);
    assert forall|x: Renderer| s1b.renderers.contains(x) implies s2b.renderers.contains(x) by {
        let k = choose|k: int| 0 <= k < s1.renderers.len() && s1.renderers[k] == x;
    }
    crate::net_rel::lemma_rel_conn_tabs(s1, s2, s1b, s2b);
    crate::unwinding::lemma_rel_from_sets(rules, urls, d, s1b, s2b);
    if find_by_tab(s1.renderers, tab, 0) is Some {
        crate::net_rel::lemma_same_renderer_by_tab(rules, urls, d, s1, s2, tab);
    }
    lemma_user_outputs(rules, urls, d, s1, s2, s1b, s2b, tab, o1, o2);
}

/// `Input` from related states: the states are unchanged, and `d` gets the
/// same outputs.
pub proof fn lemma_input_consistency(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    d: crate::domain::Domain,
    s1: State,
    s2: State,
    tab: nat,
    input: UserInput,
)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
    ensures
        crate::noninterference::rel(rules, urls, d, user_input(s1, tab, input).0, user_input(s2, tab, input).0),
        crate::noninterference::outputs_for(rules, d, s1, user_input(s1, tab, input).0, user_input(s1, tab, input).1)
            == crate::noninterference::outputs_for(rules, d, s2, user_input(s2, tab, input).0, user_input(s2, tab, input).1),
{
    let (s1b, o1) = user_input(s1, tab, input);
    let (s2b, o2) = user_input(s2, tab, input);
    if find_by_tab(s1.renderers, tab, 0) is Some {
        crate::net_rel::lemma_same_renderer_by_tab(rules, urls, d, s1, s2, tab);
    }
    lemma_user_outputs(rules, urls, d, s1, s2, s1b, s2b, tab, o1, o2);
}

/// A kept `Resize` or `Input`: related states and the same outputs to `d`.
pub proof fn lemma_user_event_consistency(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, e: Event)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        e is Resize || e is Input,
    ensures
        crate::noninterference::step_consistency_statement(rules, urls, fetch, d, s1, s2, e),
        crate::noninterference::output_consistency_statement(rules, urls, fetch, d, s1, s2, e),
{
    match e {
        Event::Resize { tab, width, height, scale } => {
            lemma_resize_consistency(rules, urls, fetch, d, s1, s2, tab, Viewport { width, height, scale });
        },
        Event::Input { tab, input } => {
            lemma_input_consistency(rules, urls, fetch, d, s1, s2, tab, input);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------
// `FromGpu`.
// ---------------------------------------------------------------------

/// A GPU process's frame that kills its renderer: the step is
/// [`kill_renderer`].
pub open spec fn gpu_kills(r: Renderer, bytes: Seq<u8>) -> bool {
    match decode_gpu_frame(bytes) {
        None => true,
        Some(clazel_ipc::message::spec::Message::FrameReady { buffer, .. }) => !r.committed || buffer >= ring_size(),
        Some(_) => false,
    }
}

/// What a GPU process's frame does to the state: it kills its renderer, or
/// changes nothing but (a `GpuReady`, item 5.17c) its renderer's GPU record.
pub proof fn lemma_from_gpu_shape(s: State, id: nat, bytes: Seq<u8>)
    ensures
        match find_by_id(s.renderers, id, 0) {
            None => from_gpu(s, id, bytes) == (s, Seq::<Output>::empty()),
            Some(i) => if gpu_kills(s.renderers[i], bytes) {
                from_gpu(s, id, bytes) == kill_renderer(s, i, id)
            } else {
                from_gpu(s, id, bytes).0 == (if decode_gpu_frame(bytes) matches Some(clazel_ipc::message::spec::Message::GpuReady { .. }) {
                    gpu_ready(s, s.renderers[i], decode_gpu_frame(bytes)->Some_0->GpuReady_software)
                } else {
                    s
                }) && (decode_gpu_frame(bytes) matches Some(clazel_ipc::message::spec::Message::GpuReady { .. }) ==> from_gpu(s, id, bytes).1.len() == 0)
                && from_gpu(s, id, bytes).1.len() <= 1 && (from_gpu(s, id, bytes).1.len() == 1 ==> gpu_of(s, s.renderers[i]).running && from_gpu(s, id, bytes).1[0]
                    == Output::Paint {
                    tab: s.renderers[i].tab,
                    url: s.renderers[i].url,
                    title: title_of(s.titles, s.renderers[i]),
                    buffer: decode_gpu_frame(bytes)->Some_0->FrameReady_buffer,
                    width: decode_gpu_frame(bytes)->Some_0->FrameReady_width,
                    height: decode_gpu_frame(bytes)->Some_0->FrameReady_height,
                } && decode_gpu_frame(bytes)->Some_0 is FrameReady && s.renderers[i].committed && decode_gpu_frame(bytes)->Some_0->FrameReady_buffer < ring_size() && fits(
                    viewport_of(s, s.renderers[i].tab),
                    decode_gpu_frame(bytes)->Some_0->FrameReady_width,
                    decode_gpu_frame(bytes)->Some_0->FrameReady_height,
                ))
            },
        },
{
}

/// The pair of renderer `s1.renderers[i1]`, of `d`, killed in both runs.
#[verifier::spinoff_prover]
pub proof fn lemma_kill_both(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, i1: int, i2: int, id: nat)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        0 <= i1 < s1.renderers.len(),
        0 <= i2 < s2.renderers.len(),
        s1.renderers[i1] == s2.renderers[i2],
        s1.renderers[i1].id == id,
        crate::domain::domain_of_renderer(rules, s1.renderers[i1]) == d,
        crate::invariant::kernel_wf(rules, urls, kill_renderer(s1, i1, id).0),
        crate::invariant::kernel_wf(rules, urls, kill_renderer(s2, i2, id).0),
    ensures
        crate::noninterference::renderer_outs(kill_renderer(s1, i1, id).1) == crate::noninterference::renderer_outs(kill_renderer(s2, i2, id).1),
        crate::noninterference::rel(rules, urls, d, kill_renderer(s1, i1, id).0, kill_renderer(s2, i2, id).0),
{
    let r = s1.renderers[i1];
    let (s1b, o1) = kill_renderer(s1, i1, id);
    let (s2b, o2) = kill_renderer(s2, i2, id);
    assert(s1b.renderers == s1.renderers.remove(i1));
    assert(s2b.renderers == s2.renderers.remove(i2));
    assert forall|x: Renderer| s1b.renderers.contains(x) implies s2b.renderers.contains(x) by {
        crate::unwind_base::lemma_remove_contains(urls, s1.renderers, s1.next_id, i1, x);
        crate::unwind_base::lemma_remove_contains(urls, s2.renderers, s2.next_id, i2, x);
        let k = choose|k: int| 0 <= k < s1.renderers.len() && s1.renderers[k] == x;
    }
    assert forall|x: Renderer| s2b.renderers.contains(x) && crate::domain::domain_of_renderer(rules, x) == d implies s1b.renderers.contains(x) by {
        crate::unwind_base::lemma_remove_contains(urls, s1.renderers, s1.next_id, i1, x);
        crate::unwind_base::lemma_remove_contains(urls, s2.renderers, s2.next_id, i2, x);
    }
    crate::net_rel::lemma_renderer_outs_kill(id, s1.conns, r.tab);
    crate::net_rel::lemma_renderer_outs_kill(id, s2.conns, r.tab);
    crate::net_rel::lemma_rel_conn_exit_both(rules, urls, s1, s2, i1, i2);
    lemma_titles_forget_same(rules, s1.titles, s2.titles, r.id, r.lock, d);
    crate::net_rel::lemma_rel_conn_ext(
        State { conns: without_tab(s1.conns, s1.renderers[i1].tab), renderers: s1.renderers.remove(i1), ..s1 },
        State { conns: without_tab(s2.conns, s2.renderers[i2].tab), renderers: s2.renderers.remove(i2), ..s2 },
        s1b,
        s2b,
    );
    crate::unwinding::lemma_rel_from_sets(rules, urls, d, s1b, s2b);
}

/// A frame of the GPU process of a renderer of `d`: related states and the
/// same renderer-bound outputs in both runs.
#[verifier::spinoff_prover]
pub proof fn lemma_d_gpu_event(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, id: nat, bytes: Seq<u8>)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::domain::event_domain(rules, s1, Event::FromGpu { id, bytes }) == Some(d),
    ensures
        crate::noninterference::renderer_outs(step(rules, urls, fetch, s1, Event::FromGpu { id, bytes }).1) == crate::noninterference::renderer_outs(step(rules, urls, fetch, s2, Event::FromGpu { id, bytes }).1),
        crate::noninterference::rel(rules, urls, d, step(rules, urls, fetch, s1, Event::FromGpu { id, bytes }).0, step(rules, urls, fetch, s2, Event::FromGpu { id, bytes }).0),
{
    let e = Event::FromGpu { id, bytes };
    assert(crate::domain::event_domain(rules, s1, Event::FromRenderer { id, bytes }) == Some(d));
    crate::unwinding_d::lemma_d_sender(rules, urls, d, s1, s2, id, bytes);
    let i1 = find_by_id(s1.renderers, id, 0)->Some_0;
    let i2 = find_by_id(s2.renderers, id, 0)->Some_0;
    let r = s1.renderers[i1];
    lemma_from_gpu_shape(s1, id, bytes);
    lemma_from_gpu_shape(s2, id, bytes);
    if gpu_kills(r, bytes) {
        crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s1, e);
        crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s2, e);
        assert(step(rules, urls, fetch, s1, e) == kill_renderer(s1, i1, id));
        assert(step(rules, urls, fetch, s2, e) == kill_renderer(s2, i2, id));
        lemma_kill_both(rules, urls, d, s1, s2, i1, i2, id);
    } else {
        lemma_title_of_rel(rules, urls, d, s1, s2, r);
        crate::gpu_rel::lemma_gpu_of_rel(rules, urls, d, s1, s2, r);
        assert(s2.renderers[i2] == r);
        assert(step(rules, urls, fetch, s1, e).1 == step(rules, urls, fetch, s2, e).1);
        if decode_gpu_frame(bytes) matches Some(clazel_ipc::message::spec::Message::GpuReady { .. }) {
            // Item 5.17c: the same record set in both runs.
            let software = decode_gpu_frame(bytes)->Some_0->GpuReady_software;
            crate::gpu_theorems::lemma_gpu_of_key(s1, r);
            let g = gpu_of(s1, r);
            crate::gpu_rel::lemma_gpu_recs_set_same(rules, s1.gpu.recs, s2.gpu.recs, GpuRec { running: true, software: g.software || software, ..g }, d);
            crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s1, e);
            crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s2, e);
        }
    }
}

/// The outputs of a frame of the GPU process of renderer `r`, of another
/// domain than `d`, name `r` only, by id or by tab: none is addressed to `d`.
#[verifier::spinoff_prover]
pub proof fn lemma_gpu_outputs_not_d(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, i1: int, id: nat, bytes: Seq<u8>)
    requires
        crate::invariant::renderers_wf(urls, s1.renderers, s1.next_id),
        find_by_id(s1.renderers, id, 0) == Some(i1),
        0 <= i1 < s1.renderers.len(),
        s1.renderers[i1].id == id,
        crate::domain::domain_of_renderer(rules, s1.renderers[i1]) != d,
    ensures
        crate::noninterference::outputs_for(rules, d, s1, from_gpu(s1, id, bytes).0, from_gpu(s1, id, bytes).1) == Seq::<Output>::empty(),
{
    let r = s1.renderers[i1];
    lemma_from_gpu_shape(s1, id, bytes);
    let (s1b, out1) = from_gpu(s1, id, bytes);
    assert(s1.renderers.contains(r));
    if gpu_kills(r, bytes) {
        crate::net_theorems::lemma_closes_of_tab(s1.conns, r.tab);
    }
    assert forall|k: int| 0 <= k < out1.len() implies !crate::noninterference::addressed_to(rules, d, s1, s1b, #[trigger] out1[k]) by {
        if crate::noninterference::addressed_to(rules, d, s1, s1b, out1[k]) {
            let q = choose|q: Renderer|
                (s1.renderers.contains(q) || s1b.renderers.contains(q)) && (if out1[k] is Show || out1[k] is Paint || out1[k] is GpuStopped {
                    q.tab == crate::domain::output_id(out1[k])
                } else {
                    q.id == crate::domain::output_id(out1[k])
                }) && crate::domain::domain_of_renderer(rules, q) == d;
            if gpu_kills(r, bytes) {
                crate::unwind_base::lemma_remove_contains(urls, s1.renderers, s1.next_id, i1, q);
                assert(s1.renderers.contains(q));
                if k > 0 {
                    assert(out1[k] == closes_of_tab(s1.conns, r.tab)[k - 1]);
                }
                crate::unwind_base::lemma_same_id_same_renderer(urls, s1.renderers, s1.next_id, q, r);
            } else {
                assert(s1.renderers.contains(q));
                crate::unwind_base::lemma_same_tab_same_renderer(urls, s1.renderers, s1.next_id, q, r);
            }
        }
    }
    crate::unwind_base::lemma_filter_none(out1, |o: Output| crate::noninterference::addressed_to(rules, d, s1, s1b, o));
}

/// The pair of renderer `s1.renderers[i1]`, of another domain than `d`,
/// killed in the first run only: the states stay related.
#[verifier::spinoff_prover]
pub proof fn lemma_kill_first(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, i1: int, id: nat)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        0 <= i1 < s1.renderers.len(),
        s1.renderers[i1].id == id,
        crate::domain::domain_of_renderer(rules, s1.renderers[i1]) != d,
        crate::invariant::kernel_wf(rules, urls, kill_renderer(s1, i1, id).0),
    ensures
        crate::noninterference::rel(rules, urls, d, kill_renderer(s1, i1, id).0, s2),
{
    let r = s1.renderers[i1];
    let s1b = kill_renderer(s1, i1, id).0;
    assert(s1b.renderers == s1.renderers.remove(i1));
    assert forall|x: Renderer| s1b.renderers.contains(x) implies s2.renderers.contains(x) by {
        crate::unwind_base::lemma_remove_contains(urls, s1.renderers, s1.next_id, i1, x);
        let k = choose|k: int| 0 <= k < s1.renderers.len() && s1.renderers[k] == x;
    }
    assert forall|x: Renderer| s2.renderers.contains(x) && crate::domain::domain_of_renderer(rules, x) == d implies s1b.renderers.contains(x) by {
        crate::unwind_base::lemma_remove_contains(urls, s1.renderers, s1.next_id, i1, x);
        assert(s1.renderers.contains(x));
        assert(s1.renderers.contains(r));
        if x.id == r.id {
            crate::unwind_base::lemma_same_id_same_renderer(urls, s1.renderers, s1.next_id, x, r);
        }
    }
    assert(s1b.jar == s1.jar && s1b.storage == s1.storage && s1b.now == s1.now && s1b.next_id == s1.next_id);
    crate::net_rel::lemma_rel_conn_exit_first(rules, urls, s1, s2, i1);
    lemma_titles_forget_other(rules, s1.titles, r.id, r.lock, d);
    crate::net_rel::lemma_rel_conn_ext(State { conns: without_tab(s1.conns, s1.renderers[i1].tab), renderers: s1.renderers.remove(i1), ..s1 }, s2, s1b, s2);
    crate::unwinding::lemma_rel_from_sets(rules, urls, d, s1b, s2);
}

/// A frame of the GPU process of a renderer of another domain: nothing is
/// sent to `d`, and the state stays related to the other run's.
#[verifier::spinoff_prover]
pub proof fn lemma_local_respect_gpu(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, e: Event)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        e is FromGpu,
        crate::domain::event_domain(rules, s1, e) matches Some(d2) && d2 != d,
    ensures
        crate::noninterference::local_respect_statement(rules, urls, fetch, d, s1, s2, e),
{
    let id = e->FromGpu_id;
    let bytes = e->FromGpu_bytes;
    assert(e == (Event::FromGpu { id, bytes }));
    let d2 = crate::domain::event_domain(rules, s1, e)->Some_0;
    assert(crate::domain::event_domain(rules, s1, Event::FromRenderer { id, bytes }) == Some(d2));
    crate::unwinding_b::lemma_b_sender(rules, urls, d, s1, s2, id, bytes, d2);
    let i1 = find_by_id(s1.renderers, id, 0)->Some_0;
    let r = s1.renderers[i1];
    lemma_from_gpu_shape(s1, id, bytes);
    assert(step(rules, urls, fetch, s1, e) == from_gpu(s1, id, bytes));
    lemma_gpu_outputs_not_d(rules, urls, d, s1, i1, id, bytes);
    if gpu_kills(r, bytes) {
        crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s1, e);
        assert(from_gpu(s1, id, bytes) == kill_renderer(s1, i1, id));
        lemma_kill_first(rules, urls, d, s1, s2, i1, id);
    } else if decode_gpu_frame(bytes) matches Some(clazel_ipc::message::spec::Message::GpuReady { .. }) {
        // Item 5.17c: its renderer's record only, under a lock of `d2`.
        let software = decode_gpu_frame(bytes)->Some_0->GpuReady_software;
        crate::gpu_theorems::lemma_gpu_of_key(s1, r);
        let g = gpu_of(s1, r);
        crate::gpu_rel::lemma_gpu_recs_set_other(rules, s1.gpu.recs, GpuRec { running: true, software: g.software || software, ..g }, d);
        crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s1, e);
    }
}

} // verus!
