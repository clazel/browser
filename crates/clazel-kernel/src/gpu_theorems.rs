//! Phase 5 item 5.17c's theorems, stated in `statements.rs`: a GPU process's
//! exit changes no other tab's state or output (`theorem_gpu_exit_contained`);
//! a tab's GPU process is restarted in one mode at most twice within five
//! minutes after exits in that mode (`theorem_gpu_restart_bounded`); every
//! tab goes to software only through the host, a refusal before any page
//! reached the process, or hardware exits from three sites within five
//! minutes (`theorem_site_cannot_demote_others`, with
//! `theorem_gpu_sites_wf_kept`); and a frame from an exited GPU process is
//! never painted (`theorem_paint_after_restart`, 5.18's paint theorems
//! restated over restarts). None assumes anything of the GPU process or the
//! page.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The record table.
// ---------------------------------------------------------------------

/// A record found for `(id, lock)` has that id and lock.
pub proof fn lemma_gpu_rec_of_key(gs: Seq<GpuRec>, id: nat, lock: clazel_origin::spec::Origin)
    ensures
        gpu_rec_of(gs, id, lock) matches Some(g) ==> g.id == id && g.lock == lock,
    decreases gs.len(),
{
    if gs.len() > 0 && !(gs[0].id == id && gs[0].lock == lock) {
        lemma_gpu_rec_of_key(gs.drop_first(), id, lock);
    }
}

/// [`gpu_rec_of`] of a table with one more record at the end.
pub proof fn lemma_gpu_rec_of_push(gs: Seq<GpuRec>, g: GpuRec, id: nat, lock: clazel_origin::spec::Origin)
    ensures
        gpu_rec_of(gs.push(g), id, lock) == match gpu_rec_of(gs, id, lock) {
            Some(x) => Some(x),
            None => if g.id == id && g.lock == lock { Some(g) } else { None },
        },
    decreases gs.len(),
{
    if gs.len() > 0 {
        assert(gs.push(g)[0] == gs[0]);
        assert(gs.push(g).drop_first() =~= gs.drop_first().push(g));
        lemma_gpu_rec_of_push(gs.drop_first(), g, id, lock);
        assert(gpu_rec_of(gs.push(g), id, lock) == (if gs[0].id == id && gs[0].lock == lock { Some(gs[0]) } else { gpu_rec_of(gs.drop_first().push(g), id, lock) }));
        assert(gpu_rec_of(gs, id, lock) == (if gs[0].id == id && gs[0].lock == lock { Some(gs[0]) } else { gpu_rec_of(gs.drop_first(), id, lock) }));
    } else {
        assert(gs.push(g)[0] == g);
        assert(gs.push(g).drop_first() =~= Seq::<GpuRec>::empty());
        assert(gpu_rec_of(Seq::<GpuRec>::empty(), id, lock) is None);
        assert(gpu_rec_of(gs, id, lock) is None);
        assert(gpu_rec_of(gs.push(g), id, lock) == (if g.id == id && g.lock == lock { Some(g) } else { gpu_rec_of(Seq::<GpuRec>::empty(), id, lock) }));
    }
}

/// Removing the records of another key changes no record of `(id, lock)`.
pub proof fn lemma_gpu_rec_of_filter(gs: Seq<GpuRec>, kid: nat, klock: clazel_origin::spec::Origin, id: nat, lock: clazel_origin::spec::Origin)
    ensures
        gpu_rec_of(gs.filter(|x: GpuRec| !(x.id == kid && x.lock == klock)), id, lock) == (if kid == id && klock == lock {
            None
        } else {
            gpu_rec_of(gs, id, lock)
        }),
    decreases gs.len(),
{
    let p = |x: GpuRec| !(x.id == kid && x.lock == klock);
    reveal(Seq::filter);
    if gs.len() > 0 {
        let a = gs.drop_last();
        let x = gs.last();
        assert(gs =~= a.push(x));
        lemma_gpu_rec_of_filter(a, kid, klock, id, lock);
        lemma_gpu_rec_of_push(a, x, id, lock);
        if p(x) {
            assert(gs.filter(p) =~= a.filter(p).push(x));
            lemma_gpu_rec_of_push(a.filter(p), x, id, lock);
        } else {
            assert(gs.filter(p) =~= a.filter(p));
        }
    } else {
        assert(gs.filter(p) =~= Seq::<GpuRec>::empty());
    }
}

/// [`set_gpu_rec`] sets the record of `g`'s key to `g` and no other.
pub proof fn lemma_set_gpu_rec(gs: Seq<GpuRec>, g: GpuRec, id: nat, lock: clazel_origin::spec::Origin)
    ensures
        gpu_rec_of(set_gpu_rec(gs, g), id, lock) == (if g.id == id && g.lock == lock { Some(g) } else { gpu_rec_of(gs, id, lock) }),
{
    let f = gs.filter(|x: GpuRec| !(x.id == g.id && x.lock == g.lock));
    lemma_gpu_rec_of_filter(gs, g.id, g.lock, id, lock);
    lemma_gpu_rec_of_push(f, g, id, lock);
}

/// After [`with_gpu_rec`] of a record of renderer `r`'s key, `r`'s record is it.
pub proof fn lemma_gpu_of_with(s: State, g: GpuRec, r: Renderer)
    ensures
        g.id == r.id && g.lock == r.lock ==> gpu_of(with_gpu_rec(s, g), r) == g,
        !(g.id == r.id && g.lock == r.lock) ==> gpu_rec_of(with_gpu_rec(s, g).gpu.recs, r.id, r.lock) == gpu_rec_of(s.gpu.recs, r.id, r.lock),
{
    lemma_set_gpu_rec(s.gpu.recs, g, r.id, r.lock);
}

/// [`gpu_of`] has the renderer's key.
pub proof fn lemma_gpu_of_key(s: State, r: Renderer)
    ensures
        gpu_of(s, r).id == r.id,
        gpu_of(s, r).lock == r.lock,
{
    lemma_gpu_rec_of_key(s.gpu.recs, r.id, r.lock);
}

// ---------------------------------------------------------------------
// The shape of a `GpuExited` step.
// ---------------------------------------------------------------------

/// The restart's outputs: a `Spawn` of `r`'s GPU process in that mode first,
/// then at most the two viewport frames, to `r`.
pub proof fn lemma_restart_outputs(s: State, r: Renderer, software: bool)
    ensures
        ({
            let o = gpu_restart_outputs(s, r, software);
            &&& o.len() >= 1
            &&& o[0] == Output::Spawn { id: r.id, policy: gpu_policy(software) }
            &&& forall|k: int| 1 <= k < o.len() ==> (#[trigger] o[k] is ToRenderer && o[k]->ToRenderer_id == r.id) || (o[k] is ToGpu && o[k]->ToGpu_id == r.id)
        }),
{
}

/// What a `GpuExited` of a live renderer does, branch by branch: the state
/// after is `s` with only the crash policy's state changed, the records of
/// every other key unchanged, and the outputs those of `all` (at most
/// `GpuAllSoftware`) and of the branch.
pub proof fn lemma_gpu_exited_frame(rules: Seq<clazel_psl::spec::Rule>, s: State, i: int)
    requires
        0 <= i < s.renderers.len(),
        find_by_id(s.renderers, s.renderers[i].id, 0) == Some(i),
    ensures
        ({
            let r = s.renderers[i];
            let (s1, out) = gpu_exited(rules, s, r.id);
            &&& s1 == State { gpu: s1.gpu, ..s }
            &&& forall|x: nat, lock: clazel_origin::spec::Origin| x != r.id ==> gpu_rec_of(s1.gpu.recs, x, lock) == gpu_rec_of(s.gpu.recs, x, lock)
        }),
{
    let r = s.renderers[i];
    let g = gpu_of(s, r);
    lemma_gpu_of_key(s, r);
    let (s1, out) = gpu_exited(rules, s, r.id);
    assert forall|x: nat, lock: clazel_origin::spec::Origin| x != r.id implies gpu_rec_of(s1.gpu.recs, x, lock) == gpu_rec_of(s.gpu.recs, x, lock) by {
        let gx = GpuRec { software: true, running: false, stopped: false, exits: seq![], ..g };
        lemma_set_gpu_rec(s.gpu.recs, GpuRec { running: false, stopped: true, ..g }, x, lock);
        lemma_set_gpu_rec(s.gpu.recs, gx, x, lock);
        lemma_set_gpu_rec(s.gpu.recs, GpuRec { software: true, running: false, stopped: false, exits: noted_exits(g, s.now), ..g }, x, lock);
        lemma_set_gpu_rec(s.gpu.recs, GpuRec { software: false, running: false, stopped: false, exits: noted_exits(g, s.now), ..g }, x, lock);
    }
}

// ---------------------------------------------------------------------
// The theorems.
// ---------------------------------------------------------------------

/// `theorem_gpu_exit_contained`.
pub proof fn theorem_gpu_exit_contained(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat)
    ensures
        crate::statements::gpu_exit_contained_statement(rules, urls, fetch, s, id),
{
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
    if let Some(i) = find_by_id(s.renderers, id, 0) {
        let r = s.renderers[i];
        lemma_gpu_exited_frame(rules, s, i);
        lemma_gpu_of_key(s, r);
        let g = gpu_of(s, r);
        let (s1, out) = gpu_exited(rules, s, id);
        lemma_restart_outputs(s, r, true);
        lemma_restart_outputs(s, r, false);
        let site = crate::domain::domain_of_renderer(rules, r);
        let s_all = demote_all(s).0;
        let s_site = gpu_site_exit(s, site).0;
        lemma_restart_outputs(s_all, r, true);
        lemma_restart_outputs(s_site, r, true);
        lemma_restart_outputs(s_site, r, false);
        assert(s_all.viewports == s.viewports && s_site.viewports == s.viewports);
        assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
            Output::Spawn { id: x, policy: p } => x == id && p != Policy::Renderer,
            Output::ToRenderer { id: x, .. } => x == id,
            Output::ToGpu { id: x, .. } => x == id,
            Output::GpuStopped { tab, url } => exists|j: int| 0 <= j < s.renderers.len() && s.renderers[j].id == id && s.renderers[j].tab == tab && s.renderers[j].url == url,
            Output::GpuAllSoftware => true,
            _ => false,
        } by {
            assert(gpu_policy(true) != Policy::Renderer && gpu_policy(false) != Policy::Renderer);
            if !g.running {
                if !g.stopped && !g.software {
                    let all = demote_all(s).1;
                    if k >= all.len() {
                        assert(out[k] == gpu_restart_outputs(s_all, r, true)[k - all.len()]);
                    }
                }
            } else if !g.software {
                let all = gpu_site_exit(s, site).1;
                assert(all.len() == 0 || all == seq![Output::GpuAllSoftware]);
                if k >= all.len() {
                    if third_exit(g, s.now) || s_site.gpu.demoted {
                        assert(out[k] == gpu_restart_outputs(s_site, r, true)[k - all.len()]);
                    } else {
                        assert(out[k] == gpu_restart_outputs(s_site, r, false)[k - all.len()]);
                    }
                }
            }
        }
    }
}

/// `theorem_gpu_restart_bounded`.
pub proof fn theorem_gpu_restart_bounded(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat)
    ensures
        crate::statements::gpu_restart_bounded_statement(rules, urls, fetch, s, id),
{
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
    if let Some(i) = find_by_id(s.renderers, id, 0) {
        let r = s.renderers[i];
        lemma_gpu_of_key(s, r);
        let g = gpu_of(s, r);
        let (s1, out) = gpu_exited(rules, s, id);
        let site = crate::domain::domain_of_renderer(rules, r);
        let s_all = demote_all(s).0;
        let s_site = gpu_site_exit(s, site).0;
        lemma_restart_outputs(s, r, true);
        lemma_restart_outputs(s_all, r, true);
        lemma_restart_outputs(s_site, r, true);
        lemma_restart_outputs(s_site, r, false);
        assert(gpu_policy(true) != gpu_policy(false));
        // Every output is a `Spawn` only at the restart's first position.
        let sw_pol = Output::Spawn { id, policy: gpu_policy(g.software) };
        let other_pol = Output::Spawn { id, policy: gpu_policy(!g.software) };
        if !g.running {
            if !g.stopped && !g.software {
                let all = demote_all(s).1;
                let rest = gpu_restart_outputs(s_all, r, true);
                assert(out =~= all + rest);
                lemma_gpu_of_with(s_all, GpuRec { software: true, running: false, stopped: false, exits: seq![], ..g }, r);
                if out.contains(sw_pol) {
                    let k = choose|k: int| 0 <= k < out.len() && out[k] == sw_pol;
                    if k >= all.len() {
                        assert(rest[k - all.len()] == sw_pol);
                    }
                }
            } else if g.stopped {
            } else {
                lemma_gpu_of_with(s, GpuRec { running: false, stopped: true, ..g }, r);
            }
        } else if g.software {
            if third_exit(g, s.now) {
                lemma_gpu_of_with(s, GpuRec { running: false, stopped: true, ..g }, r);
            } else {
                let n = GpuRec { software: true, running: false, stopped: false, exits: noted_exits(g, s.now), ..g };
                lemma_gpu_of_with(s, n, r);
                let rest = gpu_restart_outputs(s, r, true);
                if out.contains(other_pol) {
                    let k = choose|k: int| 0 <= k < out.len() && out[k] == other_pol;
                    assert(rest[k] == other_pol);
                }
                if g.exits.len() >= 1 {
                    assert(noted_exits(g, s.now) =~= seq![s.now] + g.exits.take(1));
                } else {
                    assert(noted_exits(g, s.now) =~= seq![s.now] + g.exits.take(0));
                }
            }
        } else {
            let all = gpu_site_exit(s, site).1;
            assert(all.len() == 0 || all == seq![Output::GpuAllSoftware]);
            if third_exit(g, s.now) || s_site.gpu.demoted {
                let n = GpuRec { software: true, running: false, stopped: false, exits: seq![], ..g };
                lemma_gpu_of_with(s_site, n, r);
                let rest = gpu_restart_outputs(s_site, r, true);
                assert(out =~= all + rest);
                if out.contains(sw_pol) {
                    let k = choose|k: int| 0 <= k < out.len() && out[k] == sw_pol;
                    if k >= all.len() {
                        assert(rest[k - all.len()] == sw_pol);
                    }
                }
            } else {
                let n = GpuRec { software: false, running: false, stopped: false, exits: noted_exits(g, s.now), ..g };
                lemma_gpu_of_with(s_site, n, r);
                let rest = gpu_restart_outputs(s_site, r, false);
                assert(out =~= all + rest);
                if out.contains(other_pol) {
                    let k = choose|k: int| 0 <= k < out.len() && out[k] == other_pol;
                    if k >= all.len() {
                        assert(rest[k - all.len()] == other_pol);
                    }
                }
                if g.exits.len() >= 1 {
                    assert(noted_exits(g, s.now) =~= seq![s.now] + g.exits.take(1));
                } else {
                    assert(noted_exits(g, s.now) =~= seq![s.now] + g.exits.take(0));
                }
            }
        }
    }
}

/// `site_demotes` gives two other sites within 300 seconds.
proof fn lemma_site_demotes_two(sites: Seq<SiteExit>, site: crate::domain::Domain, now: int)
    requires
        site_demotes(sites, site, now),
    ensures
        crate::statements::two_other_sites(sites, site, now),
{
    let p = |x: SiteExit| x.site != site && within(x.time, now);
    let f = sites.filter(p);
    assert(f.len() >= 2);
    // The filter's elements are elements of `sites`, in order: take the
    // first two and find them.
    lemma_filter_two(sites, p);
}

/// A filter with two elements has two elements of the sequence satisfying
/// the predicate, at increasing indices.
proof fn lemma_filter_two(s: Seq<SiteExit>, p: spec_fn(SiteExit) -> bool)
    requires
        s.filter(p).len() >= 2,
    ensures
        exists|a: int, b: int| 0 <= a < b < s.len() && p(s[a]) && p(s[b]),
    decreases s.len(),
{
    reveal(Seq::filter);
    let init = s.drop_last();
    let x = s.last();
    assert(s =~= init.push(x));
    if p(x) {
        assert(s.filter(p) =~= init.filter(p).push(x));
        if init.filter(p).len() >= 2 {
            lemma_filter_two(init, p);
            let (a, b) = choose|a: int, b: int| 0 <= a < b < init.len() && p(init[a]) && p(init[b]);
            assert(s[a] == init[a] && s[b] == init[b]);
        } else {
            lemma_filter_one(init, p);
            let a = choose|a: int| 0 <= a < init.len() && p(init[a]);
            assert(s[a] == init[a]);
            assert(s[s.len() - 1] == x);
        }
    } else {
        assert(s.filter(p) =~= init.filter(p));
        lemma_filter_two(init, p);
        let (a, b) = choose|a: int, b: int| 0 <= a < b < init.len() && p(init[a]) && p(init[b]);
        assert(s[a] == init[a] && s[b] == init[b]);
    }
}

/// A non-empty filter has an element of the sequence satisfying the
/// predicate.
proof fn lemma_filter_one(s: Seq<SiteExit>, p: spec_fn(SiteExit) -> bool)
    requires
        s.filter(p).len() >= 1,
    ensures
        exists|a: int| 0 <= a < s.len() && p(s[a]),
    decreases s.len(),
{
    reveal(Seq::filter);
    let init = s.drop_last();
    let x = s.last();
    assert(s =~= init.push(x));
    if p(x) {
        assert(s[s.len() - 1] == x);
    } else {
        assert(s.filter(p) =~= init.filter(p));
        lemma_filter_one(init, p);
        let a = choose|a: int| 0 <= a < init.len() && p(init[a]);
        assert(s[a] == init[a]);
    }
}

/// `theorem_site_cannot_demote_others`.
pub proof fn theorem_site_cannot_demote_others(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    ensures
        crate::statements::site_cannot_demote_others_statement(rules, urls, fetch, s, e),
{
    let s1 = step(rules, urls, fetch, s, e).0;
    if !s.gpu.demoted && s1.gpu.demoted {
        match e {
            Event::GpuSiteExit { lock } => {
                lemma_site_demotes_two(s.gpu.sites, crate::domain::domain_of_lock(rules, lock), s.now);
            },
            Event::GpuExited { id } => {
                if let Some(i) = find_by_id(s.renderers, id, 0) {
                    let r = s.renderers[i];
                    let g = gpu_of(s, r);
                    if g.running && !g.software {
                        lemma_site_demotes_two(s.gpu.sites, crate::domain::domain_of_renderer(rules, r), s.now);
                    }
                }
            },
            Event::GpuSoftware => {},
            _ => {
                lemma_step_keeps_gpu(rules, urls, fetch, s, e);
            },
        }
    }
}

/// [`crate::statements::gpu_sites_wf`] of a sequence that is the first two of
/// a distinct site and other sites.
proof fn lemma_note_site_wf(sites: Seq<SiteExit>, site: crate::domain::Domain, now: int)
    requires
        crate::statements::gpu_sites_wf(sites),
    ensures
        crate::statements::gpu_sites_wf(note_site(sites, site, now)),
{
    let p = |x: SiteExit| x.site != site;
    let rest = sites.filter(p);
    reveal(Seq::filter);
    rest.filter_lemma(p);
    // `rest` is a subsequence of distinct sites: at most two, distinct.
    lemma_filter_distinct(sites, p);
    let n = note_site(sites, site, now);
    assert forall|a: int, b: int| 0 <= a < b < n.len() implies n[a].site != n[b].site by {
        if a == 0 {
            assert(n[b] == rest[b - 1]);
            assert(p(rest[b - 1]));
        } else {
            assert(n[a] == rest[a - 1] && n[b] == rest[b - 1]);
        }
    }
}

/// A filter of distinct sites is distinct and no longer.
proof fn lemma_filter_distinct(sites: Seq<SiteExit>, p: spec_fn(SiteExit) -> bool)
    requires
        crate::statements::gpu_sites_wf(sites),
    ensures
        sites.filter(p).len() <= sites.len(),
        forall|a: int, b: int| 0 <= a < b < sites.filter(p).len() ==> sites.filter(p)[a].site != sites.filter(p)[b].site,
    decreases sites.len(),
{
    reveal(Seq::filter);
    if sites.len() > 0 {
        let init = sites.drop_last();
        let x = sites.last();
        assert(sites =~= init.push(x));
        lemma_filter_distinct(init, p);
        init.filter_lemma(p);
        if p(x) {
            let f = init.filter(p);
            assert(sites.filter(p) =~= f.push(x));
            lemma_filter_from(init, p);
            assert forall|a: int| 0 <= a < f.len() implies f[a].site != x.site by {
                let j = choose|j: int| 0 <= j < init.len() && init[j] == f[a];
                assert(sites[j] == init[j] && sites[sites.len() - 1] == x);
            }
        } else {
            assert(sites.filter(p) =~= init.filter(p));
        }
    }
}

/// Every element of a filter is an element of the sequence.
proof fn lemma_filter_from(s: Seq<SiteExit>, p: spec_fn(SiteExit) -> bool)
    ensures
        forall|a: int| 0 <= a < s.filter(p).len() ==> exists|j: int| 0 <= j < s.len() && s[j] == #[trigger] s.filter(p)[a],
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let init = s.drop_last();
        let x = s.last();
        assert(s =~= init.push(x));
        lemma_filter_from(init, p);
        let f = init.filter(p);
        if p(x) {
            assert(s.filter(p) =~= f.push(x));
            assert forall|a: int| 0 <= a < s.filter(p).len() implies exists|j: int| 0 <= j < s.len() && s[j] == #[trigger] s.filter(p)[a] by {
                if a < f.len() {
                    let j = choose|j: int| 0 <= j < init.len() && init[j] == f[a];
                    assert(s[j] == init[j]);
                } else {
                    assert(s[s.len() - 1] == x);
                }
            }
        } else {
            assert(s.filter(p) =~= f);
            assert forall|a: int| 0 <= a < s.filter(p).len() implies exists|j: int| 0 <= j < s.len() && s[j] == #[trigger] s.filter(p)[a] by {
                let j = choose|j: int| 0 <= j < init.len() && init[j] == f[a];
                assert(s[j] == init[j]);
            }
        }
    } else {
        assert(s.filter(p) =~= Seq::<SiteExit>::empty());
    }
}

/// `theorem_gpu_sites_wf_kept`.
pub proof fn theorem_gpu_sites_wf_kept(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    ensures
        crate::statements::gpu_sites_wf_kept_statement(rules, urls, fetch, s, e),
{
    if crate::statements::gpu_sites_wf(s.gpu.sites) {
        match e {
            Event::GpuSiteExit { lock } => {
                lemma_note_site_wf(s.gpu.sites, crate::domain::domain_of_lock(rules, lock), s.now);
            },
            Event::GpuExited { id } => {
                if let Some(i) = find_by_id(s.renderers, id, 0) {
                    lemma_note_site_wf(s.gpu.sites, crate::domain::domain_of_renderer(rules, s.renderers[i]), s.now);
                }
            },
            Event::GpuSoftware => {},
            _ => {
                lemma_step_keeps_gpu(rules, urls, fetch, s, e);
            },
        }
    }
}

/// Every event but the three of item 5.17c and `FromGpu` leaves the crash
/// policy's state as it is; `FromGpu` changes only its records.
pub proof fn lemma_step_keeps_gpu(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    ensures
        !(e is GpuExited || e is GpuSoftware || e is GpuSiteExit || e is FromGpu) ==> step(rules, urls, fetch, s, e).0.gpu == s.gpu,
        e is FromGpu ==> step(rules, urls, fetch, s, e).0.gpu.demoted == s.gpu.demoted && step(rules, urls, fetch, s, e).0.gpu.sites == s.gpu.sites,
{
    crate::unwind_base::lemma_step_gpu_frame(rules, urls, fetch, s, e);
}

/// `theorem_channel_only_own_tab` for item 5.17c's events; and
/// `GpuSoftware` and `GpuSiteExit` give at most the host's `GpuAllSoftware`.
pub proof fn lemma_channel_gpu_events(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        e is GpuExited || e is GpuSoftware || e is GpuSiteExit,
    ensures
        crate::statements::channel_only_own_tab_statement(rules, urls, fetch, s, e),
        !(e is GpuExited) ==> forall|k: int| 0 <= k < step(rules, urls, fetch, s, e).1.len() ==> (#[trigger] step(rules, urls, fetch, s, e).1[k]) == Output::GpuAllSoftware,
{
    let out = step(rules, urls, fetch, s, e).1;
    match e {
        Event::GpuExited { id } => {
            theorem_gpu_exit_contained(rules, urls, fetch, s, id);
            crate::invariant::lemma_find_by_id(s.renderers, id, 0);
            assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                Output::Spawn { id: x, policy: p } => (x == s.next_id && out.contains(Output::Spawn { id: x, policy: Policy::Gpu }) && out.contains(
                    Output::Spawn { id: x, policy: Policy::Renderer },
                )) || (crate::statements::gpu_restarted(s, e, x) && p != Policy::Renderer),
                Output::ToGpu { id: x, .. } => (x == s.next_id && out.contains(Output::Spawn { id: x, policy: Policy::Gpu })) || (e matches Event::Resize {
                    tab,
                    ..
                } && find_by_tab(s.renderers, tab, 0) matches Some(i) && s.renderers[i].id == x) || crate::statements::gpu_restarted(s, e, x),
                _ => true,
            } by {
                if out.len() > 0 {
                    assert(find_by_id(s.renderers, id, 0) is Some);
                }
            }
        },
        Event::GpuSoftware => {},
        Event::GpuSiteExit { lock } => {
            let site = crate::domain::domain_of_lock(rules, lock);
            let t = State { gpu: GpuState { sites: note_site(s.gpu.sites, site, s.now), ..s.gpu }, ..s };
            assert(demote_all(t).1.len() <= 1);
        },
        _ => {},
    }
}

/// `theorem_paint_after_restart`.
pub proof fn theorem_paint_after_restart(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>)
    ensures
        crate::statements::paint_after_restart_statement(rules, urls, fetch, s, id, bytes),
{
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
    if let Some(i) = find_by_id(s.renderers, id, 0) {
        let r = s.renderers[i];
        lemma_gpu_of_key(s, r);
        let g = gpu_of(s, r);
        let site = crate::domain::domain_of_renderer(rules, r);
        if !g.running {
            if !g.stopped && !g.software {
                lemma_gpu_of_with(demote_all(s).0, GpuRec { software: true, running: false, stopped: false, exits: seq![], ..g }, r);
            } else if !g.stopped {
                lemma_gpu_of_with(s, GpuRec { running: false, stopped: true, ..g }, r);
            }
        } else if g.software {
            lemma_gpu_of_with(s, GpuRec { running: false, stopped: true, ..g }, r);
            lemma_gpu_of_with(s, GpuRec { software: true, running: false, stopped: false, exits: noted_exits(g, s.now), ..g }, r);
        } else {
            let s_site = gpu_site_exit(s, site).0;
            lemma_gpu_of_with(s_site, GpuRec { software: true, running: false, stopped: false, exits: seq![], ..g }, r);
            lemma_gpu_of_with(s_site, GpuRec { software: false, running: false, stopped: false, exits: noted_exits(g, s.now), ..g }, r);
        }
        crate::surface_rel::lemma_from_gpu_shape(s, id, bytes);
        if crate::surface_rel::gpu_kills(r, bytes) {
            crate::net_theorems::lemma_closes_of_tab(s.conns, r.tab);
        }
    }
}

} // verus!
