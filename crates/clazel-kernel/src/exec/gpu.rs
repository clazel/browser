//! The GPU crash policy (phase-5.md item 5.17c) over the exec records: each
//! function's `ensures` says it equals its spec on the views.

#[allow(unused_imports)]
use super::locks::*;
use super::records::*;
#[allow(unused_imports)]
use super::spec::*;
use super::step::*;
use super::surfaces::*;
use clazel_origin::exec::ParsedOrigin;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every field but the crash policy's is unchanged.
pub open spec fn only_gpu(before: StateRecord, after: StateRecord) -> bool {
    &&& after.renderers@ == before.renderers@
    &&& after.jar@ == before.jar@
    &&& after.storage@ == before.storage@
    &&& after.next_id == before.next_id
    &&& after.conns@ == before.conns@
    &&& after.next_conn == before.next_conn
    &&& after.now == before.now
    &&& after.viewports@ == before.viewports@
    &&& after.titles@ == before.titles@
    &&& after.subfetches@ == before.subfetches@
    &&& after.subcounts@ == before.subcounts@
}

/// [`within`].
pub fn within_exec(then: u64, now: u64) -> (r: bool)
    ensures
        r == within(then as int, now as int),
{
    if now >= then {
        now - then < 300
    } else {
        true
    }
}

/// A copy of a list of times.
fn copy_times(v: &[u64]) -> (out: Vec<u64>)
    ensures
        out@ == v@,
{
    vstd::slice::slice_to_vec(v)
}

/// A copy of a GPU record.
fn clone_rec(g: &GpuRecRecord) -> (out: GpuRecRecord)
    ensures
        out@ == g@,
{
    GpuRecRecord { id: g.id, lock: clone_origin(&g.lock), software: g.software, running: g.running, stopped: g.stopped, exits: copy_times(g.exits.as_slice()) }
}

/// [`gpu_rec_of`] reads past entries that are not the renderer's.
proof fn lemma_gpu_rec_of_skip(gs: Seq<GpuRec>, id: nat, lock: clazel_origin::spec::Origin, k: int)
    requires
        0 <= k < gs.len(),
        !(gs[k].id == id && gs[k].lock == lock),
    ensures
        gpu_rec_of(gs.skip(k), id, lock) == gpu_rec_of(gs.skip(k + 1), id, lock),
{
    assert(gs.skip(k)[0] == gs[k]);
    assert(gs.skip(k).drop_first() =~= gs.skip(k + 1));
}

/// [`gpu_rec_of`].
pub fn gpu_rec_of_exec(gs: &[GpuRecRecord], id: u64, lock: &ParsedOrigin) -> (r: Option<GpuRecRecord>)
    ensures
        match r {
            Some(g) => gpu_rec_of(gpu_recs_view(gs@), id as nat, lock@) == Some(g@),
            None => gpu_rec_of(gpu_recs_view(gs@), id as nat, lock@) is None,
        },
{
    let ghost gv = gpu_recs_view(gs@);
    let mut k: usize = 0;
    proof {
        assert(gv.skip(0) =~= gv);
    }
    while k < gs.len()
        invariant
            k <= gs.len(),
            gv == gpu_recs_view(gs@),
            gpu_rec_of(gv, id as nat, lock@) == gpu_rec_of(gv.skip(k as int), id as nat, lock@),
        decreases gs.len() - k,
    {
        if let Some(g) = gs.get(k) {
            proof {
                assert(gv[k as int] == g@);
                assert(gv.skip(k as int)[0] == g@);
            }
            if g.id == id && origin_eq_exec(&g.lock, lock) {
                return Some(clone_rec(g));
            }
            proof {
                lemma_gpu_rec_of_skip(gv, id as nat, lock@, k as int);
            }
        }
        // Never saturates: k < gs.len().
        k = k.saturating_add(1);
    }
    proof {
        assert(gv.skip(gs.len() as int) =~= Seq::<GpuRec>::empty());
    }
    None
}

/// [`set_gpu_rec`].
pub fn set_gpu_rec_exec(gs: &[GpuRecRecord], g: GpuRecRecord) -> (out: Vec<GpuRecRecord>)
    ensures
        gpu_recs_view(out@) == set_gpu_rec(gpu_recs_view(gs@), g@),
{
    let ghost gv = gpu_recs_view(gs@);
    let ghost gg = g@;
    let mut out: Vec<GpuRecRecord> = Vec::new();
    let mut k: usize = 0;
    proof {
        reveal(Seq::filter);
        assert(gv.take(0) =~= Seq::<GpuRec>::empty());
        assert(gpu_recs_view(out@) =~= Seq::<GpuRec>::empty());
    }
    while k < gs.len()
        invariant
            k <= gs.len(),
            gv == gpu_recs_view(gs@),
            gg == g@,
            gpu_recs_view(out@) == gv.take(k as int).filter(|x: GpuRec| !(x.id == gg.id && x.lock == gg.lock)),
        decreases gs.len() - k,
    {
        if let Some(x) = gs.get(k) {
            proof {
                reveal(Seq::filter);
                assert(gv.take(k as int + 1).drop_last() =~= gv.take(k as int));
                assert(gv.take(k as int + 1).last() == x@);
            }
            if !(x.id == g.id && origin_eq_exec(&x.lock, &g.lock)) {
                let ghost before = out@;
                let c = clone_rec(x);
                out.push(c);
                proof {
                    assert(gpu_recs_view(out@) =~= gpu_recs_view(before).push(x@));
                }
            }
        }
        // Never saturates: k < gs.len().
        k = k.saturating_add(1);
    }
    proof {
        assert(gv.take(gs.len() as int) =~= gv);
    }
    let ghost before = out@;
    out.push(g);
    proof {
        assert(gpu_recs_view(out@) =~= gpu_recs_view(before).push(gg));
    }
    out
}

/// What the crash policy reads of a renderer: its id, tab, URL and lock.
pub struct RendKey {
    /// The id.
    pub id: u64,
    /// The tab.
    pub tab: u64,
    /// The URL.
    pub url: Vec<u32>,
    /// The lock.
    pub lock: ParsedOrigin,
}

/// `k` holds `r`'s id, tab, URL and lock.
pub open spec fn key_of(k: RendKey, r: Renderer) -> bool {
    k.id as nat == r.id && k.tab as nat == r.tab && k.url@ == r.url && k.lock@ == r.lock
}

/// The key of renderer `i` of `s`.
pub fn key_at(s: &StateRecord, i: usize) -> (k: RendKey)
    requires
        i < s.renderers.len(),
    ensures
        key_of(k, s@.renderers[i as int]),
{
    let r = &s.renderers[i];
    proof {
        assert(s@.renderers[i as int] == r@);
    }
    RendKey { id: r.id, tab: r.tab, url: clazel_url::host::record::copy(r.url.as_slice()), lock: clone_origin(&r.lock) }
}

/// [`gpu_of`] for the renderer `r` of `s`, whose key is `k`.
pub fn gpu_of_exec(s: &StateRecord, k: &RendKey, Ghost(r): Ghost<Renderer>) -> (out: GpuRecRecord)
    requires
        key_of(*k, r),
    ensures
        out@ == gpu_of(s@, r),
{
    match gpu_rec_of_exec(s.gpu.recs.as_slice(), k.id, &k.lock) {
        Some(g) => g,
        None => {
            let g = GpuRecRecord { id: k.id, lock: clone_origin(&k.lock), software: s.gpu.demoted, running: false, stopped: false, exits: Vec::new() };
            proof {
                assert(g@.exits =~= Seq::<int>::empty());
            }
            g
        },
    }
}

/// [`with_gpu_rec`].
pub fn with_gpu_rec_exec(s: StateRecord, g: GpuRecRecord) -> (out: StateRecord)
    ensures
        out@ == with_gpu_rec(s@, g@),
        only_gpu(s, out),
        out.gpu.demoted == s.gpu.demoted,
        out.gpu.sites@ == s.gpu.sites@,
{
    let recs = set_gpu_rec_exec(s.gpu.recs.as_slice(), g);
    let mut s = s;
    s.gpu.recs = recs;
    s
}

/// [`gpu_ready`] for the renderer `r` of `s`.
pub fn gpu_ready_exec(s: StateRecord, k: &RendKey, Ghost(r): Ghost<Renderer>, software: bool) -> (out: StateRecord)
    requires
        key_of(*k, r),
    ensures
        out@ == gpu_ready(s@, r, software),
        only_gpu(s, out),
{
    let g = gpu_of_exec(&s, k, Ghost(r));
    if g.running || g.stopped {
        s
    } else {
        let sw = g.software || software;
        let n = GpuRecRecord { running: true, software: sw, ..g };
        with_gpu_rec_exec(s, n)
    }
}

/// [`third_exit`].
pub fn third_exit_exec(g: &GpuRecRecord, now: u64) -> (r: bool)
    ensures
        r == third_exit(g@, now as int),
{
    if g.exits.len() >= 2 {
        match g.exits.get(1) {
            Some(t) => within_exec(*t, now),
            None => false,
        }
    } else {
        false
    }
}

/// [`noted_exits`].
pub fn noted_exits_exec(g: &GpuRecRecord, now: u64) -> (out: Vec<u64>)
    ensures
        out@.map_values(|t: u64| t as int) == noted_exits(g@, now as int),
{
    let mut out: Vec<u64> = Vec::new();
    out.push(now);
    if g.exits.len() > 1 {
        if let Some(t) = g.exits.get(0) {
            out.push(*t);
        }
        proof {
            assert(out@.map_values(|t: u64| t as int) =~= seq![now as int] + g@.exits.take(1));
        }
    } else {
        if let Some(t) = g.exits.get(0) {
            out.push(*t);
        }
        proof {
            assert(out@.map_values(|t: u64| t as int) =~= seq![now as int] + g@.exits);
        }
    }
    out
}

/// A copy of a domain.
fn clone_domain(d: &DomainRecord) -> (out: DomainRecord)
    ensures
        out@ == d@,
{
    match d {
        DomainRecord::Root(h) => DomainRecord::Root(
            clazel_cookie::matching::exec::CanonicalHostName { name: vstd::slice::slice_to_vec(h.name.as_slice()), is_ip_address: h.is_ip_address },
        ),
        DomainRecord::Opaque(id) => DomainRecord::Opaque(*id),
    }
}

/// Whether two domains are equal.
pub fn domain_eq_exec(a: &DomainRecord, b: &DomainRecord) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    match (a, b) {
        (DomainRecord::Opaque(x), DomainRecord::Opaque(y)) => *x == *y,
        (DomainRecord::Root(x), DomainRecord::Root(y)) => super::subfetch::bytes_eq(x.name.as_slice(), y.name.as_slice()) && x.is_ip_address == y.is_ip_address,
        _ => false,
    }
}

/// A copy of a site entry.
fn clone_site(x: &SiteExitRecord) -> (out: SiteExitRecord)
    ensures
        out@ == x@,
{
    SiteExitRecord { site: clone_domain(&x.site), time: x.time }
}

/// [`site_demotes`].
pub fn site_demotes_exec(sites: &[SiteExitRecord], site: &DomainRecord, now: u64) -> (r: bool)
    ensures
        r == site_demotes(sites_view(sites@), site@, now as int),
{
    let ghost sv = sites_view(sites@);
    let ghost p = |x: SiteExit| x.site != site@ && within(x.time, now as int);
    let mut count: usize = 0;
    let mut k: usize = 0;
    proof {
        reveal(Seq::filter);
        assert(sv.take(0) =~= Seq::<SiteExit>::empty());
    }
    while k < sites.len()
        invariant
            k <= sites.len(),
            sv == sites_view(sites@),
            p == (|x: SiteExit| x.site != site@ && within(x.time, now as int)),
            count as int == sv.take(k as int).filter(p).len(),
            count <= k,
        decreases sites.len() - k,
    {
        if let Some(x) = sites.get(k) {
            proof {
                reveal(Seq::filter);
                assert(sv.take(k as int + 1).drop_last() =~= sv.take(k as int));
                assert(sv.take(k as int + 1).last() == x@);
            }
            if !domain_eq_exec(&x.site, site) && within_exec(x.time, now) {
                count = count + 1;
            }
        }
        // Never saturates: k < sites.len().
        k = k.saturating_add(1);
    }
    proof {
        assert(sv.take(sites.len() as int) =~= sv);
        assert(other_sites(sv, site@, now as int) == sv.filter(p));
    }
    count >= 2
}

/// [`note_site`].
pub fn note_site_exec(sites: &[SiteExitRecord], site: DomainRecord, now: u64) -> (out: Vec<SiteExitRecord>)
    ensures
        sites_view(out@) == note_site(sites_view(sites@), site@, now as int),
{
    let ghost sv = sites_view(sites@);
    let ghost sd = site@;
    let mut rest: Vec<SiteExitRecord> = Vec::new();
    let mut k: usize = 0;
    proof {
        reveal(Seq::filter);
        assert(sv.take(0) =~= Seq::<SiteExit>::empty());
        assert(sites_view(rest@) =~= Seq::<SiteExit>::empty());
    }
    while k < sites.len()
        invariant
            k <= sites.len(),
            sv == sites_view(sites@),
            sd == site@,
            sites_view(rest@) == sv.take(k as int).filter(|x: SiteExit| x.site != sd),
        decreases sites.len() - k,
    {
        if let Some(x) = sites.get(k) {
            proof {
                reveal(Seq::filter);
                assert(sv.take(k as int + 1).drop_last() =~= sv.take(k as int));
                assert(sv.take(k as int + 1).last() == x@);
            }
            if !domain_eq_exec(&x.site, &site) {
                let ghost before = rest@;
                rest.push(clone_site(x));
                proof {
                    assert(sites_view(rest@) =~= sites_view(before).push(x@));
                }
            }
        }
        // Never saturates: k < sites.len().
        k = k.saturating_add(1);
    }
    proof {
        assert(sv.take(sites.len() as int) =~= sv);
    }
    let ghost rv = sites_view(rest@);
    let mut out: Vec<SiteExitRecord> = Vec::new();
    out.push(SiteExitRecord { site, time: now });
    if rest.len() > 1 {
        if let Some(x) = rest.get(0) {
            out.push(clone_site(x));
        }
        proof {
            assert(sites_view(out@) =~= seq![SiteExit { site: sd, time: now as int }] + rv.take(1));
        }
    } else {
        if let Some(x) = rest.get(0) {
            out.push(clone_site(x));
        }
        proof {
            assert(sites_view(out@) =~= seq![SiteExit { site: sd, time: now as int }] + rv);
        }
    }
    out
}

/// [`demote_all`].
pub fn demote_all_exec(s: StateRecord) -> (out: (StateRecord, Vec<OutputRecord>))
    ensures
        result_view(out) == demote_all(s@),
        only_gpu(s, out.0),
{
    if s.gpu.demoted {
        (s, no_outputs())
    } else {
        let mut s = s;
        s.gpu.demoted = true;
        (s, one_output(OutputRecord::GpuAllSoftware))
    }
}

/// [`gpu_site_exit`].
pub fn gpu_site_exit_exec(s: StateRecord, site: DomainRecord) -> (out: (StateRecord, Vec<OutputRecord>))
    ensures
        result_view(out) == gpu_site_exit(s@, site@),
        only_gpu(s, out.0),
{
    let flips = !s.gpu.demoted && site_demotes_exec(s.gpu.sites.as_slice(), &site, s.now);
    let sites = note_site_exec(s.gpu.sites.as_slice(), site, s.now);
    let mut s1 = s;
    s1.gpu.sites = sites;
    if flips {
        demote_all_exec(s1)
    } else {
        (s1, no_outputs())
    }
}

/// [`gpu_restart_outputs`] for the renderer `r` of `s`.
pub fn gpu_restart_outputs_exec(s: &StateRecord, k: &RendKey, Ghost(r): Ghost<Renderer>, software: bool) -> (out: Vec<OutputRecord>)
    requires
        key_of(*k, r),
    ensures
        outputs_view(out@) == gpu_restart_outputs(s@, r, software),
{
    let spawn = if software {
        OutputRecord::SpawnGpuSoftware { id: k.id }
    } else {
        OutputRecord::SpawnGpu { id: k.id }
    };
    match find_viewport_exec(s.viewports.as_slice(), k.tab) {
        None => {
            let ghost g = spawn@;
            let v = one_output(spawn);
            proof {
                assert(outputs_view(v@) =~= seq![g] + Seq::<Output>::empty());
            }
            v
        },
        Some(j) => {
            let (w, h, sc) = match s.viewports.get(j) {
                Some(v) => (v.width, v.height, v.scale),
                None => (0, 0, 1),
            };
            let a = OutputRecord::ToRenderer { id: k.id, bytes: viewport_frame_exec(w, h, sc) };
            let b = OutputRecord::ToGpu { id: k.id, bytes: gpu_viewport_frame_exec(w, h, sc) };
            let ghost (g0, g1, g2) = (spawn@, a@, b@);
            let v = vec![spawn, a, b];
            proof {
                assert(outputs_view(v@) =~= seq![g0] + seq![g1, g2]);
            }
            v
        },
    }
}

/// [`gpu_restart`] for the renderer `r` of `s`.
fn gpu_restart_exec(s: StateRecord, k: &RendKey, Ghost(r): Ghost<Renderer>, g: GpuRecRecord, software: bool, exits: Vec<u64>) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        key_of(*k, r),
    ensures
        result_view(out) == gpu_restart(s@, r, g@, software, exits@.map_values(|t: u64| t as int)),
        only_gpu(s, out.0),
{
    let outs = gpu_restart_outputs_exec(&s, k, Ghost(r), software);
    let n = GpuRecRecord { software, running: false, stopped: false, exits, ..g };
    (with_gpu_rec_exec(s, n), outs)
}

/// [`gpu_stop`] for the renderer `r` of `s`.
fn gpu_stop_exec(s: StateRecord, k: &RendKey, Ghost(r): Ghost<Renderer>, g: GpuRecRecord) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        key_of(*k, r),
    ensures
        result_view(out) == gpu_stop(s@, r, g@),
        only_gpu(s, out.0),
{
    let n = GpuRecRecord { running: false, stopped: true, ..g };
    let o = OutputRecord::GpuStopped { tab: k.tab, url: clazel_url::host::record::copy(k.url.as_slice()) };
    (with_gpu_rec_exec(s, n), one_output(o))
}

/// `GpuExited(id)` ([`gpu_exited`]).
pub fn gpu_exited_exec(s: StateRecord, id: u64) -> (out: (StateRecord, Vec<OutputRecord>))
    ensures
        result_view(out) == gpu_exited(crate::contract::psl(), s@, id as nat),
        only_gpu(s, out.0),
{
    match find_by_id_exec(s.renderers.as_slice(), id) {
        None => (s, no_outputs()),
        Some(i) => {
            let k = key_at(&s, i);
            let ghost r = s@.renderers[i as int];
            let g = gpu_of_exec(&s, &k, Ghost(r));
            if !g.running {
                if g.stopped {
                    (s, no_outputs())
                } else if g.software {
                    gpu_stop_exec(s, &k, Ghost(r), g)
                } else {
                    let (s1, all) = demote_all_exec(s);
                    let (s2, out) = gpu_restart_exec(s1, &k, Ghost(r), g, true, Vec::new());
                    proof {
                        assert(Seq::<u64>::empty().map_values(|t: u64| t as int) =~= Seq::<int>::empty());
                    }
                    (s2, append_outputs(all, out))
                }
            } else if g.software {
                if third_exit_exec(&g, s.now) {
                    gpu_stop_exec(s, &k, Ghost(r), g)
                } else {
                    let exits = noted_exits_exec(&g, s.now);
                    gpu_restart_exec(s, &k, Ghost(r), g, true, exits)
                }
            } else {
                let now = s.now;
                let third = third_exit_exec(&g, now);
                let exits = noted_exits_exec(&g, now);
                let (s1, all) = gpu_site_exit_exec(s, domain_of_lock_exec(&k.lock));
                let (s2, out) = if third || s1.gpu.demoted {
                    proof {
                        assert(Seq::<u64>::empty().map_values(|t: u64| t as int) =~= Seq::<int>::empty());
                    }
                    gpu_restart_exec(s1, &k, Ghost(r), g, true, Vec::new())
                } else {
                    gpu_restart_exec(s1, &k, Ghost(r), g, false, exits)
                };
                (s2, append_outputs(all, out))
            }
        },
    }
}

/// `GpuSoftware` ([`gpu_software`]).
pub fn gpu_software_exec(s: StateRecord) -> (out: (StateRecord, Vec<OutputRecord>))
    ensures
        result_view(out) == gpu_software(s@),
        only_gpu(s, out.0),
{
    demote_all_exec(s)
}

/// `GpuSiteExit(lock)` ([`gpu_site_exit`] for the lock's domain).
pub fn gpu_site_exit_lock_exec(s: StateRecord, lock: &ParsedOrigin) -> (out: (StateRecord, Vec<OutputRecord>))
    ensures
        result_view(out) == gpu_site_exit(s@, crate::domain::domain_of_lock(crate::contract::psl(), lock@)),
        only_gpu(s, out.0),
{
    gpu_site_exit_exec(s, domain_of_lock_exec(lock))
}

} // verus!
