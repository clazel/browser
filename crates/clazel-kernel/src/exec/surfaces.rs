//! The exec twins of item 5.18's functions in [`crate::spec`]: the tabs'
//! viewports, the renderers' titles, `Resize`, `Input` and a GPU process's
//! frames. Each `ensures` says the function equals its spec on the views.

use super::fetch::*;
use super::frames::*;
use super::locks::*;
use super::records::*;
#[allow(unused_imports)]
use super::spec::*;
use super::step::*;
use clazel_ipc::message::codec::Msg;
use clazel_url::host::record::copy;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Viewports.
// ---------------------------------------------------------------------

/// Skipping viewports of other tabs does not change [`find_viewport`].
proof fn lemma_find_viewport_skip(vs: Seq<TabViewport>, tab: nat, i: nat, k: nat)
    requires
        i <= k <= vs.len(),
        forall|j: int| i <= j < k ==> (#[trigger] vs[j]).tab != tab,
    ensures
        find_viewport(vs, tab, i) == find_viewport(vs, tab, k),
    decreases k - i,
{
    if i < k {
        lemma_find_viewport_skip(vs, tab, i + 1, k);
    }
}

/// [`find_viewport`] from the start, as the index of the entry.
pub fn find_viewport_exec(vs: &[TabViewportRecord], tab: u64) -> (r: Option<usize>)
    ensures
        match r {
            Some(k) => k < vs.len() && find_viewport(viewports_view(vs@), tab as nat, 0) == Some(viewports_view(vs@)[k as int].viewport),
            None => find_viewport(viewports_view(vs@), tab as nat, 0) is None,
        },
{
    let ghost vv = viewports_view(vs@);
    let mut i: usize = 0;
    while i < vs.len()
        invariant
            i <= vs.len(),
            vv == viewports_view(vs@),
            forall|j: int| 0 <= j < i ==> (#[trigger] vv[j]).tab != tab as nat,
        decreases vs.len() - i,
    {
        if let Some(v) = vs.get(i) {
            proof {
                assert(vv[i as int] == vs@[i as int]@);
            }
            if v.tab == tab {
                proof {
                    lemma_find_viewport_skip(vv, tab as nat, 0, i as nat);
                }
                return Some(i);
            }
        }
        // Never saturates: i < vs.len().
        i = i.saturating_add(1);
    }
    proof {
        lemma_find_viewport_skip(vv, tab as nat, 0, vs.len() as nat);
    }
    None
}

/// [`viewport_of`]: the viewport of `tab`, or [`no_viewport`].
pub fn viewport_of_exec(vs: &[TabViewportRecord], tab: u64) -> (r: (u64, u64, u64))
    ensures
        (Viewport { width: r.0, height: r.1, scale: r.2 }) == match find_viewport(viewports_view(vs@), tab as nat, 0) {
            Some(v) => v,
            None => no_viewport(),
        },
{
    match find_viewport_exec(vs, tab) {
        Some(k) => match vs.get(k) {
            Some(v) => (v.width, v.height, v.scale),
            None => (0, 0, 1),
        },
        None => (0, 0, 1),
    }
}

/// [`set_viewport`]: the viewport of `tab` is `(width, height, scale)`.
pub fn set_viewport_exec(vs: &[TabViewportRecord], tab: u64, width: u64, height: u64, scale: u64) -> (out: Vec<TabViewportRecord>)
    ensures
        viewports_view(out@) == set_viewport(viewports_view(vs@), tab as nat, Viewport { width, height, scale }),
{
    let ghost vv = viewports_view(vs@);
    let mut out: Vec<TabViewportRecord> = Vec::new();
    let mut k: usize = 0;
    proof {
        reveal(Seq::filter);
        assert(vv.take(0) =~= Seq::<TabViewport>::empty());
        assert(viewports_view(out@) =~= Seq::<TabViewport>::empty());
    }
    while k < vs.len()
        invariant
            k <= vs.len(),
            vv == viewports_view(vs@),
            viewports_view(out@) == vv.take(k as int).filter(|x: TabViewport| x.tab != tab as nat),
        decreases vs.len() - k,
    {
        if let Some(v) = vs.get(k) {
            proof {
                reveal(Seq::filter);
                assert(vv.take(k as int + 1).drop_last() =~= vv.take(k as int));
                assert(vv.take(k as int + 1).last() == v@);
            }
            if v.tab != tab {
                let ghost before = out@;
                out.push(TabViewportRecord { tab: v.tab, width: v.width, height: v.height, scale: v.scale });
                proof {
                    assert(viewports_view(out@) =~= viewports_view(before).push(v@));
                }
            }
        }
        // Never saturates: k < vs.len().
        k = k.saturating_add(1);
    }
    proof {
        assert(vv.take(vs.len() as int) =~= vv);
    }
    let ghost before = out@;
    out.push(TabViewportRecord { tab, width, height, scale });
    proof {
        assert(viewports_view(out@) =~= viewports_view(before).push(TabViewport { tab: tab as nat, viewport: Viewport { width, height, scale } }));
    }
    out
}

// ---------------------------------------------------------------------
// Titles.
// ---------------------------------------------------------------------

/// [`title_of`] reads past entries that are not the renderer's.
proof fn lemma_title_of_skip(ts: Seq<Titled>, r: Renderer, k: int)
    requires
        0 <= k < ts.len(),
        !(ts[k].id == r.id && ts[k].lock == r.lock),
    ensures
        title_of(ts.skip(k), r) == title_of(ts.skip(k + 1), r),
{
    assert(ts.skip(k)[0] == ts[k]);
    assert(ts.skip(k).drop_first() =~= ts.skip(k + 1));
}

/// [`title_of`]: the title of renderer `r`.
pub fn title_of_exec(ts: &[TitledRecord], r: &RendererRecord) -> (out: Vec<u8>)
    ensures
        out@ == title_of(titles_view(ts@), r@),
{
    let ghost tv = titles_view(ts@);
    let mut k: usize = 0;
    proof {
        assert(tv.skip(0) =~= tv);
    }
    while k < ts.len()
        invariant
            k <= ts.len(),
            tv == titles_view(ts@),
            title_of(tv, r@) == title_of(tv.skip(k as int), r@),
        decreases ts.len() - k,
    {
        if let Some(t) = ts.get(k) {
            proof {
                assert(tv[k as int] == t@);
                assert(tv.skip(k as int)[0] == t@);
            }
            if t.id == r.id && origin_eq_exec(&t.lock, &r.lock) {
                return vstd::slice::slice_to_vec(t.title.as_slice());
            }
            proof {
                lemma_title_of_skip(tv, r@, k as int);
            }
        }
        // Never saturates: k < ts.len().
        k = k.saturating_add(1);
    }
    proof {
        assert(tv.skip(ts.len() as int) =~= Seq::<Titled>::empty());
    }
    Vec::new()
}

/// A copy of a title entry.
fn clone_titled(t: &TitledRecord) -> (out: TitledRecord)
    ensures
        out@ == t@,
{
    TitledRecord { id: t.id, lock: clone_origin(&t.lock), title: vstd::slice::slice_to_vec(t.title.as_slice()) }
}

/// [`forget_title`]: the entries that are not renderer `id`'s with `lock`.
pub fn forget_title_exec(ts: &[TitledRecord], id: u64, lock: &clazel_origin::exec::ParsedOrigin) -> (out: Vec<TitledRecord>)
    ensures
        titles_view(out@) == forget_title(titles_view(ts@), id as nat, lock@),
{
    let ghost tv = titles_view(ts@);
    let mut out: Vec<TitledRecord> = Vec::new();
    let mut k: usize = 0;
    proof {
        reveal(Seq::filter);
        assert(tv.take(0) =~= Seq::<Titled>::empty());
        assert(titles_view(out@) =~= Seq::<Titled>::empty());
    }
    while k < ts.len()
        invariant
            k <= ts.len(),
            tv == titles_view(ts@),
            titles_view(out@) == tv.take(k as int).filter(|x: Titled| !(x.id == id as nat && x.lock == lock@)),
        decreases ts.len() - k,
    {
        if let Some(t) = ts.get(k) {
            proof {
                reveal(Seq::filter);
                assert(tv.take(k as int + 1).drop_last() =~= tv.take(k as int));
                assert(tv.take(k as int + 1).last() == t@);
            }
            if !(t.id == id && origin_eq_exec(&t.lock, lock)) {
                let ghost before = out@;
                let c = clone_titled(t);
                out.push(c);
                proof {
                    assert(titles_view(out@) =~= titles_view(before).push(t@));
                }
            }
        }
        // Never saturates: k < ts.len().
        k = k.saturating_add(1);
    }
    proof {
        assert(tv.take(ts.len() as int) =~= tv);
    }
    out
}

/// [`set_title`]: renderer `id`'s title, under `lock`, is `title`.
pub fn set_title_exec(ts: &[TitledRecord], id: u64, lock: &clazel_origin::exec::ParsedOrigin, title: Vec<u8>) -> (out: Vec<TitledRecord>)
    ensures
        titles_view(out@) == set_title(titles_view(ts@), id as nat, lock@, title@),
{
    let mut out = forget_title_exec(ts, id, lock);
    let ghost before = out@;
    let entry = TitledRecord { id, lock: clone_origin(lock), title };
    let ghost ev = entry@;
    out.push(entry);
    proof {
        assert(titles_view(out@) =~= titles_view(before).push(ev));
    }
    out
}

// ---------------------------------------------------------------------
// Outputs.
// ---------------------------------------------------------------------

/// Four outputs.
fn four_outputs(a: OutputRecord, b: OutputRecord, c: OutputRecord, d: OutputRecord) -> (v: Vec<OutputRecord>)
    ensures
        outputs_view(v@) == seq![a@, b@, c@, d@],
{
    let ghost (ga, gb, gc, gd) = (a@, b@, c@, d@);
    let v = vec![a, b, c, d];
    assert(outputs_view(v@) =~= seq![ga, gb, gc, gd]);
    v
}

/// Six outputs.
fn six_outputs(a: OutputRecord, b: OutputRecord, c: OutputRecord, d: OutputRecord, e: OutputRecord, f: OutputRecord) -> (v: Vec<OutputRecord>)
    ensures
        outputs_view(v@) == seq![a@, b@, c@, d@, e@, f@],
{
    let ghost (ga, gb, gc, gd, ge, gf) = (a@, b@, c@, d@, e@, f@);
    let v = vec![a, b, c, d, e, f];
    assert(outputs_view(v@) =~= seq![ga, gb, gc, gd, ge, gf]);
    v
}

/// The two outputs of a pair.
fn pair_outputs(a: OutputRecord, b: OutputRecord) -> (v: Vec<OutputRecord>)
    ensures
        outputs_view(v@) == seq![a@, b@],
{
    let ghost (ga, gb) = (a@, b@);
    let v = vec![a, b];
    assert(outputs_view(v@) =~= seq![ga, gb]);
    v
}

/// [`viewport_frame`].
pub fn viewport_frame_exec(width: u64, height: u64, scale: u64) -> (r: Vec<u8>)
    ensures
        r@ == viewport_frame(Viewport { width, height, scale }),
{
    reply_frame_exec(&Msg::Viewport { width, height, scale })
}

/// [`gpu_viewport_frame`].
pub fn gpu_viewport_frame_exec(width: u64, height: u64, scale: u64) -> (r: Vec<u8>)
    ensures
        r@ == gpu_viewport_frame(Viewport { width, height, scale }),
{
    reply_frame_exec(&Msg::GpuViewport { width, height, scale })
}

/// [`replace_outputs`]: the outputs of a cross-origin navigation that
/// replaces renderer `old` with `id`, for the tab whose viewports are `vs`.
pub fn replace_outputs_exec(old: u64, id: u64, vs: &[TabViewportRecord], tab: u64, commit: Vec<u8>) -> (out: Vec<OutputRecord>)
    ensures
        outputs_view(out@) == replace_outputs(old as nat, id as nat, find_viewport(viewports_view(vs@), tab as nat, 0), commit@),
{
    match find_viewport_exec(vs, tab) {
        None => four_outputs(
            OutputRecord::Kill { id: old },
            OutputRecord::SpawnGpu { id },
            OutputRecord::Spawn { id },
            OutputRecord::ToRenderer { id, bytes: commit },
        ),
        Some(k) => {
            let (w, h, sc) = match vs.get(k) {
                Some(v) => (v.width, v.height, v.scale),
                None => (0, 0, 1),
            };
            six_outputs(
                OutputRecord::Kill { id: old },
                OutputRecord::SpawnGpu { id },
                OutputRecord::Spawn { id },
                OutputRecord::ToRenderer { id, bytes: viewport_frame_exec(w, h, sc) },
                OutputRecord::ToGpu { id, bytes: gpu_viewport_frame_exec(w, h, sc) },
                OutputRecord::ToRenderer { id, bytes: commit },
            )
        },
    }
}

// ---------------------------------------------------------------------
// Events.
// ---------------------------------------------------------------------

/// `Resize(tab, width, height, scale)` ([`resize`]).
pub fn resize_exec(s: StateRecord, tab: u64, width: u64, height: u64, scale: u64) -> (out: (StateRecord, Vec<OutputRecord>))
    ensures
        result_view(out) == resize(s@, tab as nat, Viewport { width, height, scale }),
        out.0.renderers@ == s.renderers@,
        out.0.conns@ == s.conns@,
        out.0.titles@ == s.titles@,
        keeps_storage_jar_now(s, out.0),
        out.0.next_id == s.next_id,
        out.0.next_conn == s.next_conn,
{
    let found = find_by_tab_exec(s.renderers.as_slice(), tab);
    let vs = set_viewport_exec(s.viewports.as_slice(), tab, width, height, scale);
    let mut s = s;
    s.viewports = vs;
    match found {
        None => (s, no_outputs()),
        Some(i) => {
            let id = match s.renderers.get(i) {
                Some(r) => r.id,
                None => 0,
            };
            let outs = pair_outputs(
                OutputRecord::ToRenderer { id, bytes: viewport_frame_exec(width, height, scale) },
                OutputRecord::ToGpu { id, bytes: gpu_viewport_frame_exec(width, height, scale) },
            );
            (s, outs)
        },
    }
}

/// `Input(tab, input)` ([`user_input`]).
/// The input is `(kind, x, y, negative, delta, key)`.
pub fn user_input_exec(s: StateRecord, tab: u64, input: (u64, u64, u64, bool, u64, u64)) -> (out: (StateRecord, Vec<OutputRecord>))
    ensures
        result_view(out) == user_input(
            s@,
            tab as nat,
            UserInput { kind: input.0, x: input.1, y: input.2, negative: input.3, delta: input.4, key: input.5 },
        ),
        out.0 == s,
{
    match find_by_tab_exec(s.renderers.as_slice(), tab) {
        None => (s, no_outputs()),
        Some(i) => {
            let id = match s.renderers.get(i) {
                Some(r) => r.id,
                None => 0,
            };
            let (kind, x, y, negative, delta, key) = input;
            let bytes = reply_frame_exec(&Msg::Input { kind, x, y, negative, delta, key });
            (s, one_output(OutputRecord::ToRenderer { id, bytes }))
        },
    }
}

/// [`decode_gpu_frame`]: the message in a GPU process's frame, if it may
/// send it.
pub fn decode_gpu_frame_exec(bytes: &[u8]) -> (r: Option<Msg>)
    ensures
        crate::contract::decode_gpu_frame_ensures(bytes@, clazel_ipc::message::codec::option_msg(r)),
{
    let m = clazel_ipc::message::codec::decode_framed(bytes)?;
    if clazel_ipc::message::codec::is_from_gpu(&m) {
        Some(m)
    } else {
        None
    }
}

/// `FromGpu(id, bytes)` ([`from_gpu`]).
pub fn from_gpu_exec<F: FetchFnsExec>(s: StateRecord, id: u64, bytes: &[u8]) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        renderers_ok::<F>(s.renderers@),
        super::subfetch::subfetches_ok::<F>(s.subfetches@),
    ensures
        result_view(out) == from_gpu(s@, id as nat, bytes@),
        keeps_storage_jar_now(s, out.0),
        out.0.next_id == s.next_id,
        out.0.next_conn == s.next_conn,
        renderers_ok::<F>(out.0.renderers@),
        super::subfetch::subfetches_ok::<F>(out.0.subfetches@),
{
    match find_by_id_exec(s.renderers.as_slice(), id) {
        None => (s, no_outputs()),
        Some(i) => match decode_gpu_frame_exec(bytes) {
            None => kill_renderer_exec::<F>(s, i, id),
            Some(Msg::FrameReady { buffer, width, height }) => {
                let (committed, tab) = match s.renderers.get(i) {
                    Some(r) => (r.committed, r.tab),
                    None => (false, 0),
                };
                if !committed || buffer >= 3 {
                    kill_renderer_exec::<F>(s, i, id)
                } else {
                    let (vw, vh, _vs) = viewport_of_exec(s.viewports.as_slice(), tab);
                    if width <= vw && height <= vh {
                        let (url, title) = match s.renderers.get(i) {
                            Some(r) => (copy(r.url.as_slice()), title_of_exec(s.titles.as_slice(), r)),
                            None => (Vec::new(), Vec::new()),
                        };
                        let outs = one_output(OutputRecord::Paint { tab, url, title, buffer, width, height });
                        (s, outs)
                    } else {
                        (s, no_outputs())
                    }
                }
            },
            Some(_) => (s, no_outputs()),
        },
    }
}

} // verus!
