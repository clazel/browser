//! Item 2.11's noninterference over item 5.17c's events: the GPU records of
//! a domain (as 5.18's titles), the consistency of `GpuExited`,
//! `GpuSoftware` and `GpuSiteExit` between related runs, and
//! `lemma_gpu_declassify` (another domain's `GpuExited` does to the observer
//! exactly what its declassified part does).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The GPU records of a domain.
// ---------------------------------------------------------------------

/// Setting the record of a lock of another domain does not change the
/// domain's records.
pub proof fn lemma_gpu_recs_set_other(rules: Seq<clazel_psl::spec::Rule>, gs: Seq<GpuRec>, g: GpuRec, d: crate::domain::Domain)
    requires
        crate::domain::domain_of_lock(rules, g.lock) != d,
    ensures
        crate::domain::gpu_recs_of_domain(rules, set_gpu_rec(gs, g), d) == crate::domain::gpu_recs_of_domain(rules, gs, d),
{
    let keep = |x: GpuRec| !(x.id == g.id && x.lock == g.lock);
    let ind = |x: GpuRec| crate::domain::domain_of_lock(rules, x.lock) == d;
    crate::surface_rel::lemma_filter_commute(gs, keep, ind);
    let gd = gs.filter(ind);
    assert forall|i: int| 0 <= i < gd.len() implies keep(#[trigger] gd[i]) by {
        gs.lemma_filter_pred(ind, i);
    }
    crate::surface_rel::lemma_filter_all(gd, keep);
    crate::surface_rel::lemma_filter_push(gs.filter(keep), g, ind);
}

/// Setting the same record in two runs whose domain's records agree keeps
/// them agreeing.
pub proof fn lemma_gpu_recs_set_same(rules: Seq<clazel_psl::spec::Rule>, gs1: Seq<GpuRec>, gs2: Seq<GpuRec>, g: GpuRec, d: crate::domain::Domain)
    requires
        crate::domain::gpu_recs_of_domain(rules, gs1, d) == crate::domain::gpu_recs_of_domain(rules, gs2, d),
    ensures
        crate::domain::gpu_recs_of_domain(rules, set_gpu_rec(gs1, g), d) == crate::domain::gpu_recs_of_domain(rules, set_gpu_rec(gs2, g), d),
{
    let keep = |x: GpuRec| !(x.id == g.id && x.lock == g.lock);
    let ind = |x: GpuRec| crate::domain::domain_of_lock(rules, x.lock) == d;
    crate::surface_rel::lemma_filter_commute(gs1, keep, ind);
    crate::surface_rel::lemma_filter_commute(gs2, keep, ind);
    crate::surface_rel::lemma_filter_push(gs1.filter(keep), g, ind);
    crate::surface_rel::lemma_filter_push(gs2.filter(keep), g, ind);
}

/// The record of a renderer of domain `d` is read from `d`'s records alone.
pub proof fn lemma_gpu_rec_of_domain(rules: Seq<clazel_psl::spec::Rule>, gs: Seq<GpuRec>, r: Renderer, d: crate::domain::Domain)
    requires
        crate::domain::domain_of_renderer(rules, r) == d,
    ensures
        gpu_rec_of(gs, r.id, r.lock) == gpu_rec_of(crate::domain::gpu_recs_of_domain(rules, gs, d), r.id, r.lock),
    decreases gs.len(),
{
    let ind = |x: GpuRec| crate::domain::domain_of_lock(rules, x.lock) == d;
    if gs.len() > 0 {
        let x = gs[0];
        let rest = gs.drop_first();
        assert(gs =~= seq![x] + rest);
        rest.lemma_filter_prepend(x, ind);
        lemma_gpu_rec_of_domain(rules, rest, r, d);
        let fr = rest.filter(ind);
        if ind(x) {
            assert(gs.filter(ind) == seq![x] + fr);
            assert((seq![x] + fr)[0] == x);
            assert((seq![x] + fr).drop_first() =~= fr);
        } else {
            assert(gs.filter(ind) =~= fr);
            assert(!(x.id == r.id && x.lock == r.lock));
        }
    } else {
        reveal(Seq::filter);
    }
}

/// Related states give a renderer of `d` the same GPU record.
pub proof fn lemma_gpu_of_rel(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, r: Renderer)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::domain::domain_of_renderer(rules, r) == d,
    ensures
        gpu_of(s1, r) == gpu_of(s2, r),
{
    lemma_gpu_rec_of_domain(rules, s1.gpu.recs, r, d);
    lemma_gpu_rec_of_domain(rules, s2.gpu.recs, r, d);
}

// ---------------------------------------------------------------------
// The events.
// ---------------------------------------------------------------------

/// A step that changes only the crash policy's state, setting the shared
/// part equally in both runs and the records of `d` equally, keeps the runs
/// related.
pub proof fn lemma_rel_gpu_only(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, s1b: State, s2b: State)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        s1b == (State { gpu: s1b.gpu, ..s1 }),
        s2b == (State { gpu: s2b.gpu, ..s2 }),
        crate::invariant::kernel_wf(rules, urls, s1b),
        crate::invariant::kernel_wf(rules, urls, s2b),
        s1b.gpu.demoted == s2b.gpu.demoted,
        s1b.gpu.sites == s2b.gpu.sites,
        crate::domain::gpu_recs_of_domain(rules, s1b.gpu.recs, d) == crate::domain::gpu_recs_of_domain(rules, s2b.gpu.recs, d),
    ensures
        crate::noninterference::rel(rules, urls, d, s1b, s2b),
{
}

/// A step that changes only the crash policy's state, leaving its shared
/// part and the records of `d` as they were, keeps the run related to the
/// unchanged other one.
pub proof fn lemma_rel_gpu_local(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, s1b: State)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        s1b == (State { gpu: s1b.gpu, ..s1 }),
        crate::invariant::kernel_wf(rules, urls, s1b),
        s1b.gpu.demoted == s1.gpu.demoted,
        s1b.gpu.sites == s1.gpu.sites,
        crate::domain::gpu_recs_of_domain(rules, s1b.gpu.recs, d) == crate::domain::gpu_recs_of_domain(rules, s1.gpu.recs, d),
    ensures
        crate::noninterference::rel(rules, urls, d, s1b, s2),
{
}

/// `GpuSoftware` and `GpuSiteExit`, kept for every observer: the same
/// shared state after in both runs, no record changed, and no output to a
/// renderer or tab.
pub proof fn lemma_shared_event_consistency(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, e: Event)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        e is GpuSoftware || e is GpuSiteExit,
    ensures
        crate::noninterference::renderer_outs(step(rules, urls, fetch, s1, e).1) == Seq::<Output>::empty(),
        crate::noninterference::renderer_outs(step(rules, urls, fetch, s2, e).1) == Seq::<Output>::empty(),
        crate::noninterference::outputs_for(rules, d, s1, step(rules, urls, fetch, s1, e).0, step(rules, urls, fetch, s1, e).1) == Seq::<Output>::empty(),
        crate::noninterference::outputs_for(rules, d, s2, step(rules, urls, fetch, s2, e).0, step(rules, urls, fetch, s2, e).1) == Seq::<Output>::empty(),
        crate::noninterference::rel(rules, urls, d, step(rules, urls, fetch, s1, e).0, step(rules, urls, fetch, s2, e).0),
{
    reveal(Seq::filter);
    crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s1, e);
    crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s2, e);
    let (s1b, o1) = step(rules, urls, fetch, s1, e);
    let (s2b, o2) = step(rules, urls, fetch, s2, e);
    if e is GpuSoftware {
        assert(o1 == demote_all(s1).1 && o2 == demote_all(s2).1);
    } else {
        let site = crate::domain::domain_of_lock(rules, e->GpuSiteExit_lock);
        assert(o1 == gpu_site_exit(s1, site).1 && o2 == gpu_site_exit(s2, site).1);
        let t1 = State { gpu: GpuState { sites: note_site(s1.gpu.sites, site, s1.now), ..s1.gpu }, ..s1 };
        let t2 = State { gpu: GpuState { sites: note_site(s2.gpu.sites, site, s2.now), ..s2.gpu }, ..s2 };
        assert(demote_all(t1).1.len() <= 1 && demote_all(t2).1.len() <= 1);
    }
    crate::gpu_theorems::lemma_channel_gpu_events(rules, urls, fetch, s1, e);
    crate::gpu_theorems::lemma_channel_gpu_events(rules, urls, fetch, s2, e);
    lemma_filter_none(o1, |o: Output| crate::noninterference::renderer_bound(o));
    lemma_filter_none(o2, |o: Output| crate::noninterference::renderer_bound(o));
    lemma_filter_none(o1, |o: Output| crate::noninterference::addressed_to(rules, d, s1, s1b, o));
    lemma_filter_none(o2, |o: Output| crate::noninterference::addressed_to(rules, d, s2, s2b, o));
    lemma_rel_gpu_only(rules, urls, d, s1, s2, s1b, s2b);
}

/// The record a `GpuExited` of the live renderer `r` sets, or `None` if it
/// sets none (a stopped tab).
pub open spec fn exit_new_rec(rules: Seq<clazel_psl::spec::Rule>, s: State, r: Renderer) -> Option<GpuRec> {
    let g = gpu_of(s, r);
    if !g.running {
        if g.stopped {
            None
        } else if g.software {
            Some(GpuRec { running: false, stopped: true, ..g })
        } else {
            Some(GpuRec { software: true, running: false, stopped: false, exits: seq![], ..g })
        }
    } else if g.software {
        if third_exit(g, s.now) {
            Some(GpuRec { running: false, stopped: true, ..g })
        } else {
            Some(GpuRec { software: true, running: false, stopped: false, exits: noted_exits(g, s.now), ..g })
        }
    } else if third_exit(g, s.now) || gpu_site_exit(s, crate::domain::domain_of_renderer(rules, r)).0.gpu.demoted {
        Some(GpuRec { software: true, running: false, stopped: false, exits: seq![], ..g })
    } else {
        Some(GpuRec { software: false, running: false, stopped: false, exits: noted_exits(g, s.now), ..g })
    }
}

/// [`gpu_exit_of`] sets exactly [`exit_new_rec`], of `r`'s key.
pub proof fn lemma_exit_recs(rules: Seq<clazel_psl::spec::Rule>, s: State, r: Renderer)
    ensures
        gpu_exit_of(rules, s, r).0.gpu.recs == match exit_new_rec(rules, s, r) {
            None => s.gpu.recs,
            Some(n) => set_gpu_rec(s.gpu.recs, n),
        },
        exit_new_rec(rules, s, r) matches Some(n) ==> n.lock == r.lock && n.id == r.id,
{
    crate::gpu_theorems::lemma_gpu_of_key(s, r);
}

/// [`gpu_exit_of`] from two states that agree on what it reads: the same
/// outputs, the same shared state after, and the same record for `r`.
pub proof fn lemma_exit_of_same(rules: Seq<clazel_psl::spec::Rule>, s1: State, s2: State, r: Renderer)
    requires
        gpu_of(s1, r) == gpu_of(s2, r),
        s1.gpu.demoted == s2.gpu.demoted,
        s1.gpu.sites == s2.gpu.sites,
        s1.now == s2.now,
        s1.viewports == s2.viewports,
    ensures
        gpu_exit_of(rules, s1, r).1 == gpu_exit_of(rules, s2, r).1,
        gpu_exit_of(rules, s1, r).0.gpu.demoted == gpu_exit_of(rules, s2, r).0.gpu.demoted,
        gpu_exit_of(rules, s1, r).0.gpu.sites == gpu_exit_of(rules, s2, r).0.gpu.sites,
        exit_new_rec(rules, s1, r) == exit_new_rec(rules, s2, r),
{
    let g = gpu_of(s1, r);
    let site = crate::domain::domain_of_renderer(rules, r);
    assert(gpu_site_exit(s1, site).1 == gpu_site_exit(s2, site).1);
    assert(gpu_site_exit(s1, site).0.gpu.demoted == gpu_site_exit(s2, site).0.gpu.demoted);
    assert(gpu_site_exit(s1, site).0.viewports == s1.viewports);
    assert(gpu_site_exit(s2, site).0.viewports == s2.viewports);
    assert(demote_all(s1).1 == demote_all(s2).1);
    assert(demote_all(s1).0.viewports == s1.viewports && demote_all(s2).0.viewports == s2.viewports);
}

/// A `GpuExited` of a renderer of `d`, kept in both runs: the same outputs,
/// related states.
#[verifier::spinoff_prover]
pub proof fn lemma_d_gpu_exited(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, id: nat)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::domain::event_domain(rules, s1, Event::GpuExited { id }) == Some(d),
    ensures
        step(rules, urls, fetch, s1, Event::GpuExited { id }).1 == step(rules, urls, fetch, s2, Event::GpuExited { id }).1,
        crate::noninterference::rel(rules, urls, d, step(rules, urls, fetch, s1, Event::GpuExited { id }).0, step(rules, urls, fetch, s2, Event::GpuExited { id }).0),
{
    let e = Event::GpuExited { id };
    let bytes = Seq::<u8>::empty();
    assert(crate::domain::event_domain(rules, s1, Event::FromRenderer { id, bytes }) == Some(d));
    crate::unwinding_d::lemma_d_sender(rules, urls, d, s1, s2, id, bytes);
    let i1 = find_by_id(s1.renderers, id, 0)->Some_0;
    let i2 = find_by_id(s2.renderers, id, 0)->Some_0;
    let r = s1.renderers[i1];
    assert(s2.renderers[i2] == r);
    lemma_gpu_of_rel(rules, urls, d, s1, s2, r);
    crate::gpu_theorems::lemma_gpu_exited_frame(rules, s1, i1);
    crate::gpu_theorems::lemma_gpu_exited_frame(rules, s2, i2);
    lemma_exit_recs(rules, s1, r);
    lemma_exit_recs(rules, s2, r);
    crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s1, e);
    crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s2, e);
    assert(gpu_exited(rules, s1, id) == gpu_exit_of(rules, s1, r));
    assert(gpu_exited(rules, s2, id) == gpu_exit_of(rules, s2, r));
    lemma_exit_of_same(rules, s1, s2, r);
    let (s1b, o1) = gpu_exited(rules, s1, id);
    let (s2b, o2) = gpu_exited(rules, s2, id);
    assert(o1 == o2);
    assert(s1b.gpu.demoted == s2b.gpu.demoted && s1b.gpu.sites == s2b.gpu.sites);
    if let Some(n) = exit_new_rec(rules, s1, r) {
        lemma_gpu_recs_set_same(rules, s1.gpu.recs, s2.gpu.recs, n, d);
    }
    lemma_rel_gpu_only(rules, urls, d, s1, s2, s1b, s2b);
}

/// No output of a `GpuExited` of renderer `r`, of another domain than `d`,
/// is addressed to `d`: each names `r` by id or by tab, or is the host's.
pub proof fn lemma_exit_outputs_not_d(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, i1: int)
    requires
        crate::invariant::kernel_wf(rules, urls, s1),
        0 <= i1 < s1.renderers.len(),
        find_by_id(s1.renderers, s1.renderers[i1].id, 0) == Some(i1),
        crate::domain::domain_of_renderer(rules, s1.renderers[i1]) != d,
    ensures
        ({
            let (s1b, o1) = gpu_exited(rules, s1, s1.renderers[i1].id);
            crate::noninterference::outputs_for(rules, d, s1, s1b, o1) == Seq::<Output>::empty()
        }),
{
    let r = s1.renderers[i1];
    let id = r.id;
    crate::gpu_theorems::theorem_gpu_exit_contained(rules, urls, fetch, s1, id);
    crate::gpu_theorems::lemma_gpu_exited_frame(rules, s1, i1);
    let (s1b, o1) = gpu_exited(rules, s1, id);
    assert(step(rules, urls, fetch, s1, Event::GpuExited { id }) == gpu_exited(rules, s1, id));
    assert(s1b.renderers == s1.renderers);
    assert(s1.renderers.contains(r));
    reveal(Seq::filter);
    assert forall|k: int| 0 <= k < o1.len() implies !crate::noninterference::addressed_to(rules, d, s1, s1b, #[trigger] o1[k]) by {
        if crate::noninterference::addressed_to(rules, d, s1, s1b, o1[k]) {
            let q = choose|q: Renderer|
                (s1.renderers.contains(q) || s1b.renderers.contains(q)) && (if o1[k] is Show || o1[k] is Paint || o1[k] is GpuStopped {
                    q.tab == crate::domain::output_id(o1[k])
                } else {
                    q.id == crate::domain::output_id(o1[k])
                }) && crate::domain::domain_of_renderer(rules, q) == d;
            if o1[k] is GpuStopped {
                let j = choose|j: int| 0 <= j < s1.renderers.len() && s1.renderers[j].id == id && s1.renderers[j].tab == o1[k]->GpuStopped_tab && s1.renderers[j].url == o1[k]->GpuStopped_url;
                assert(s1.renderers.contains(s1.renderers[j]));
                crate::unwind_base::lemma_same_id_same_renderer(urls, s1.renderers, s1.next_id, s1.renderers[j], r);
                crate::unwind_base::lemma_same_tab_same_renderer(urls, s1.renderers, s1.next_id, q, r);
            } else {
                crate::unwind_base::lemma_same_id_same_renderer(urls, s1.renderers, s1.next_id, q, r);
            }
        }
    }
    lemma_filter_none(o1, |o: Output| crate::noninterference::addressed_to(rules, d, s1, s1b, o));
}

/// A filter that keeps nothing is empty.
pub proof fn lemma_filter_none<A>(s: Seq<A>, p: spec_fn(A) -> bool)
    requires
        forall|k: int| 0 <= k < s.len() ==> !p(#[trigger] s[k]),
    ensures
        s.filter(p) == Seq::<A>::empty(),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let init = s.drop_last();
        assert forall|k: int| 0 <= k < init.len() implies !p(#[trigger] init[k]) by {
            assert(init[k] == s[k]);
        }
        lemma_filter_none(init, p);
        assert(!p(s[s.len() - 1]));
    }
    assert(s.filter(p) =~= Seq::<A>::empty());
}

/// `lemma_local_respect` for another domain's `GpuExited` with no
/// declassified part (in software, or stopped): its renderer's record only.
#[verifier::spinoff_prover]
pub proof fn lemma_local_respect_gpu_exit(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, e: Event)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::noninterference::other_domain_local(rules, urls, d, s1, e),
        e is GpuExited,
    ensures
        crate::noninterference::local_respect_statement(rules, urls, fetch, d, s1, s2, e),
{
    let id = e->GpuExited_id;
    let bytes = Seq::<u8>::empty();
    let d2 = crate::domain::event_domain(rules, s1, e)->Some_0;
    assert(crate::domain::event_domain(rules, s1, Event::FromRenderer { id, bytes }) == Some(d2));
    crate::unwinding_b::lemma_b_sender(rules, urls, d, s1, s2, id, bytes, d2);
    let i1 = find_by_id(s1.renderers, id, 0)->Some_0;
    let r = s1.renderers[i1];
    crate::gpu_theorems::lemma_gpu_of_key(s1, r);
    crate::gpu_theorems::lemma_gpu_exited_frame(rules, s1, i1);
    lemma_exit_recs(rules, s1, r);
    lemma_exit_outputs_not_d(rules, urls, fetch, d, s1, i1);
    assert(gpu_exited(rules, s1, id) == gpu_exit_of(rules, s1, r));
    crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s1, e);
    let s1b = gpu_exited(rules, s1, id).0;
    if let Some(n) = exit_new_rec(rules, s1, r) {
        lemma_gpu_recs_set_other(rules, s1.gpu.recs, n, d);
    }
    lemma_rel_gpu_local(rules, urls, d, s1, s2, s1b);
}

/// **`lemma_gpu_declassify`** (item 5.17c).
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
pub proof fn lemma_gpu_declassify(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, e: Event)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::noninterference::other_domain_gpu(rules, urls, d, s1, e),
    ensures
        crate::noninterference::gpu_declassify_statement(rules, urls, fetch, d, s1, s2, e),
{
    let id = e->GpuExited_id;
    let bytes = Seq::<u8>::empty();
    let d2 = crate::domain::event_domain(rules, s1, e)->Some_0;
    assert(crate::domain::event_domain(rules, s1, Event::FromRenderer { id, bytes }) == Some(d2));
    crate::unwinding_b::lemma_b_sender(rules, urls, d, s1, s2, id, bytes, d2);
    let i1 = find_by_id(s1.renderers, id, 0)->Some_0;
    let r = s1.renderers[i1];
    let dn = crate::domain::declassified(urls, s1, e)->Some_0;
    crate::gpu_theorems::lemma_gpu_of_key(s1, r);
    crate::gpu_theorems::lemma_gpu_exited_frame(rules, s1, i1);
    lemma_exit_recs(rules, s1, r);
    lemma_exit_outputs_not_d(rules, urls, fetch, d, s1, i1);
    assert(gpu_exited(rules, s1, id) == gpu_exit_of(rules, s1, r));
    crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s1, e);
    crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s2, dn);
    lemma_shared_event_consistency(rules, urls, fetch, d, s1, s2, dn);
    let (s1b, o1) = step(rules, urls, fetch, s1, e);
    let (s2b, o2) = step(rules, urls, fetch, s2, dn);
    assert(s2b == State { gpu: s2b.gpu, ..s2 });
    assert(s1b.gpu.demoted == s2b.gpu.demoted && s1b.gpu.sites == s2b.gpu.sites);
    if let Some(n) = exit_new_rec(rules, s1, r) {
        lemma_gpu_recs_set_other(rules, s1.gpu.recs, n, d);
    }
    lemma_rel_gpu_only(rules, urls, d, s1, s2, s1b, s2b);
}

} // verus!
