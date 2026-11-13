//! The exec twins of item 5.19's functions in [`crate::spec`]: style sheet
//! fetches. Each `ensures` says the function equals its spec on the views.

use super::fetch::*;
use super::frames::*;
use super::locks::*;
use super::records::*;
#[allow(unused_imports)]
use super::spec::*;
use super::step::*;
use super::urls::UrlFnsExec;
use clazel_cookie::matching::exec::CanonicalHostName;
use clazel_fetch::transducer::contract::UrlFnsExec as TransducerUrls;
use clazel_fetch::transducer::types::{ActionBuf, InputBuf};
use clazel_ipc::message::codec::Msg;
use clazel_origin::exec::ParsedOrigin;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What the exec state keeps of each sub-fetch beyond its view: its
/// transducer state keeps the parser invariant, its redirects are within
/// the budget, and its connections plus the transducer's remaining
/// `Connect`s stay within 21, so its `hop` never overflows.
pub open spec fn subfetches_ok<F: FetchFnsExec>(fs: Seq<SubFetchRecord>) -> bool {
    forall|i: int|
        0 <= i < fs.len() ==> F::nav_ok(&(#[trigger] fs[i]).fetch) && fs[i].fetch@.redirects <= 20 && fs[i].hop as int
            + clazel_fetch::transducer::theorems::connect_budget(fs[i].fetch@) <= 21
}

// ---------------------------------------------------------------------
// Counts.
// ---------------------------------------------------------------------

/// [`subcount_of`] reads past entries that are not the renderer's.
proof fn lemma_subcount_skip(cs: Seq<SubCount>, id: nat, lock: clazel_origin::spec::Origin, k: int)
    requires
        0 <= k < cs.len(),
        !(cs[k].renderer == id && cs[k].lock == lock),
    ensures
        subcount_of(cs.skip(k), id, lock) == subcount_of(cs.skip(k + 1), id, lock),
{
    assert(cs.skip(k)[0] == cs[k]);
    assert(cs.skip(k).drop_first() =~= cs.skip(k + 1));
}

/// [`subcount_of`].
pub fn subcount_of_exec(cs: &[SubCountRecord], id: u64, lock: &ParsedOrigin) -> (r: (u64, u64))
    ensures
        (r.0 as nat, r.1 as nat) == subcount_of(subcounts_view(cs@), id as nat, lock@),
{
    let ghost cv = subcounts_view(cs@);
    let mut k: usize = 0;
    proof {
        assert(cv.skip(0) =~= cv);
    }
    while k < cs.len()
        invariant
            k <= cs.len(),
            cv == subcounts_view(cs@),
            subcount_of(cv, id as nat, lock@) == subcount_of(cv.skip(k as int), id as nat, lock@),
        decreases cs.len() - k,
    {
        if let Some(c) = cs.get(k) {
            proof {
                assert(cv[k as int] == c@);
                assert(cv.skip(k as int)[0] == c@);
            }
            if c.renderer == id && origin_eq_exec(&c.lock, lock) {
                return (c.serial, c.in_document);
            }
            proof {
                lemma_subcount_skip(cv, id as nat, lock@, k as int);
            }
        }
        k = k.saturating_add(1);
    }
    proof {
        assert(cv.skip(cs.len() as int) =~= Seq::<SubCount>::empty());
    }
    (0, 0)
}

/// A copy of a count.
fn clone_count(c: &SubCountRecord) -> (out: SubCountRecord)
    ensures
        out@ == c@,
{
    SubCountRecord { renderer: c.renderer, lock: clone_origin(&c.lock), serial: c.serial, in_document: c.in_document }
}

/// [`set_subcount`].
pub fn set_subcount_exec(cs: &[SubCountRecord], id: u64, lock: &ParsedOrigin, serial: u64, in_document: u64) -> (out: Vec<SubCountRecord>)
    ensures
        subcounts_view(out@) == set_subcount(subcounts_view(cs@), id as nat, lock@, serial as nat, in_document as nat),
{
    let ghost cv = subcounts_view(cs@);
    let mut out: Vec<SubCountRecord> = Vec::new();
    let mut k: usize = 0;
    proof {
        reveal(Seq::filter);
        assert(cv.take(0) =~= Seq::<SubCount>::empty());
        assert(subcounts_view(out@) =~= Seq::<SubCount>::empty());
    }
    while k < cs.len()
        invariant
            k <= cs.len(),
            cv == subcounts_view(cs@),
            subcounts_view(out@) == cv.take(k as int).filter(|c: SubCount| !(c.renderer == id as nat && c.lock == lock@)),
        decreases cs.len() - k,
    {
        if let Some(c) = cs.get(k) {
            proof {
                reveal(Seq::filter);
                assert(cv.take(k as int + 1).drop_last() =~= cv.take(k as int));
                assert(cv.take(k as int + 1).last() == c@);
            }
            if !(c.renderer == id && origin_eq_exec(&c.lock, lock)) {
                let ghost before = out@;
                out.push(clone_count(c));
                proof {
                    assert(subcounts_view(out@) =~= subcounts_view(before).push(c@));
                }
            }
        }
        k = k.saturating_add(1);
    }
    proof {
        assert(cv.take(cs.len() as int) =~= cv);
    }
    let ghost before = out@;
    let entry = SubCountRecord { renderer: id, lock: clone_origin(lock), serial, in_document };
    let ghost ev = entry@;
    out.push(entry);
    proof {
        assert(subcounts_view(out@) =~= subcounts_view(before).push(ev));
    }
    out
}

/// One count after a commit of renderer `id` locked to `lock`.
pub open spec fn reset_count(c: SubCount, id: nat, lock: clazel_origin::spec::Origin) -> SubCount {
    if c.renderer == id && c.lock == lock {
        SubCount { in_document: 0, ..c }
    } else {
        c
    }
}

/// One sub-fetch after a commit of renderer `id` locked to `lock`.
pub open spec fn end_one(f: SubFetch, id: nat, lock: clazel_origin::spec::Origin) -> SubFetch {
    if f.renderer == id && f.lock == lock {
        SubFetch { ended: true, ..f }
    } else {
        f
    }
}

/// [`new_document_counts`].
pub fn new_document_counts_exec(cs: &[SubCountRecord], id: u64, lock: &ParsedOrigin) -> (out: Vec<SubCountRecord>)
    ensures
        subcounts_view(out@) == new_document_counts(subcounts_view(cs@), id as nat, lock@),
{
    let ghost cv = subcounts_view(cs@);
    let mut out: Vec<SubCountRecord> = Vec::new();
    let mut k: usize = 0;
    while k < cs.len()
        invariant
            k <= cs.len(),
            cv == subcounts_view(cs@),
            subcounts_view(out@).len() == k,
            forall|j: int| 0 <= j < k ==> subcounts_view(out@)[j] == reset_count(cv[j], id as nat, lock@),
        decreases cs.len() - k,
    {
        if let Some(c) = cs.get(k) {
            proof {
                assert(cv[k as int] == c@);
            }
            let mut d = clone_count(c);
            if c.renderer == id && origin_eq_exec(&c.lock, lock) {
                d.in_document = 0;
            }
            let ghost before = out@;
            let ghost dv = d@;
            assert(dv == reset_count(cv[k as int], id as nat, lock@));
            out.push(d);
            proof {
                assert(subcounts_view(out@) =~= subcounts_view(before).push(dv));
                assert forall|j: int| 0 <= j < k + 1 implies subcounts_view(out@)[j] == reset_count(cv[j], id as nat, lock@) by {
                    if j < k {
                        assert(subcounts_view(out@)[j] == subcounts_view(before)[j]);
                    }
                }
            }
        }
        k = k.saturating_add(1);
    }
    proof {
        assert(subcounts_view(out@) =~= new_document_counts(cv, id as nat, lock@));
    }
    out
}

// ---------------------------------------------------------------------
// The table of sub-fetches.
// ---------------------------------------------------------------------

/// [`end_subfetches`]: consumes the table.
pub fn end_subfetches_exec<F: FetchFnsExec>(fs: Vec<SubFetchRecord>, id: u64, lock: &ParsedOrigin) -> (out: Vec<SubFetchRecord>)
    requires
        subfetches_ok::<F>(fs@),
    ensures
        subfetches_view(out@) == end_subfetches(subfetches_view(fs@), id as nat, lock@),
        subfetches_ok::<F>(out@),
{
    let ghost fv = subfetches_view(fs@);
    let ghost orig = fs@;
    let mut fs = fs;
    let mut out: Vec<SubFetchRecord> = Vec::new();
    let mut k: usize = 0;
    let n = fs.len();
    let _ = n;
    while fs.len() > 0
        invariant
            k + fs.len() == n,
            n == orig.len(),
            fv == subfetches_view(orig),
            fs@ == orig.skip(k as int),
            subfetches_view(out@).len() == k,
            forall|j: int| 0 <= j < k ==> subfetches_view(out@)[j] == end_one(fv[j], id as nat, lock@),
            subfetches_ok::<F>(orig),
            subfetches_ok::<F>(out@),
        decreases fs.len(),
    {
        let ghost before = out@;
        let f = fs.remove(0);
        proof {
            assert(f == orig[k as int]);
            assert(fv[k as int] == f@);
            assert(fs@ =~= orig.skip(k as int + 1));
        }
        let mut f = f;
        if f.renderer == id && origin_eq_exec(&f.lock, lock) {
            f.ended = true;
        }
        let ghost fv2 = f@;
        out.push(f);
        proof {
            assert(subfetches_view(out@) =~= subfetches_view(before).push(fv2));
            assert(fv2 == end_one(fv[k as int], id as nat, lock@));
            assert forall|j: int| 0 <= j < k + 1 implies subfetches_view(out@)[j] == end_one(fv[j], id as nat, lock@) by {
                if j < k {
                    assert(subfetches_view(out@)[j] == subfetches_view(before)[j]);
                }
            }
            assert forall|j: int| 0 <= j < out@.len() implies F::nav_ok(&(#[trigger] out@[j]).fetch) && out@[j].fetch@.redirects <= 20 && out@[j].hop as int
                + clazel_fetch::transducer::theorems::connect_budget(out@[j].fetch@) <= 21 by {
                if j < before.len() {
                    assert(out@[j] == before[j]);
                } else {
                    assert(out@[j].fetch == orig[k as int].fetch);
                }
            }
        }
        k = k.saturating_add(1);
    }
    proof {
        assert(subfetches_view(out@) =~= end_subfetches(fv, id as nat, lock@));
    }
    out
}

/// [`live_subfetches`] reads past one entry.
proof fn lemma_live_skip(fs: Seq<SubFetch>, id: nat, lock: clazel_origin::spec::Origin, k: int)
    requires
        0 <= k < fs.len(),
    ensures
        live_subfetches(fs.skip(k), id, lock) == (if fs[k].renderer == id && fs[k].lock == lock && !fs[k].ended { 1nat } else { 0nat })
            + live_subfetches(fs.skip(k + 1), id, lock),
{
    assert(fs.skip(k)[0] == fs[k]);
    assert(fs.skip(k).drop_first() =~= fs.skip(k + 1));
}

/// [`live_subfetches`], up to `cap` (enough to compare it with a limit).
pub fn live_subfetches_exec(fs: &[SubFetchRecord], id: u64, lock: &ParsedOrigin) -> (r: u64)
    ensures
        r as nat == live_subfetches(subfetches_view(fs@), id as nat, lock@),
{
    let ghost fv = subfetches_view(fs@);
    let mut k: usize = fs.len();
    let mut count: u64 = 0;
    proof {
        assert(fv.skip(fs.len() as int) =~= Seq::<SubFetch>::empty());
    }
    while k > 0
        invariant
            k <= fs.len(),
            fv == subfetches_view(fs@),
            count as nat == live_subfetches(fv.skip(k as int), id as nat, lock@),
            count as nat <= fs.len() - k,
        decreases k,
    {
        k = k - 1;
        proof {
            lemma_live_skip(fv, id as nat, lock@, k as int);
        }
        if let Some(f) = fs.get(k) {
            proof {
                assert(fv[k as int] == f@);
            }
            if f.renderer == id && origin_eq_exec(&f.lock, lock) && !f.ended {
                count = count + 1;
            }
        }
    }
    proof {
        assert(fv.skip(0) =~= fv);
    }
    count
}

/// The first entry of a key, at index `k`: what [`subfetch_of`] finds, and
/// what [`replace_subfetch`] and [`drop_subfetch`] change.
pub proof fn lemma_first_key(fs: Seq<SubFetch>, id: nat, lock: clazel_origin::spec::Origin, serial: nat, k: int, f: SubFetch)
    requires
        0 <= k < fs.len(),
        subfetch_is(fs[k], id, lock, serial),
        forall|j: int| 0 <= j < k ==> !subfetch_is(#[trigger] fs[j], id, lock, serial),
        f.renderer == id && f.lock == lock && f.serial == serial,
    ensures
        subfetch_of(fs, id, lock, serial) == Some(fs[k]),
        replace_subfetch(fs, f) == fs.update(k, f),
        drop_subfetch(fs, f) == fs.remove(k),
    decreases k,
{
    if k > 0 {
        let t = fs.drop_first();
        assert forall|j: int| 0 <= j < k - 1 implies !subfetch_is(#[trigger] t[j], id, lock, serial) by {
            assert(t[j] == fs[j + 1]);
        }
        lemma_first_key(t, id, lock, serial, k - 1, f);
        assert(fs.update(k, f) =~= seq![fs[0]] + t.update(k - 1, f));
        assert(fs.remove(k) =~= seq![fs[0]] + t.remove(k - 1));
    } else {
        assert(fs.update(0, f) =~= seq![f] + fs.drop_first());
        assert(fs.remove(0) =~= fs.drop_first());
    }
}

/// No entry of a key: [`subfetch_of`] finds none.
pub proof fn lemma_no_key(fs: Seq<SubFetch>, id: nat, lock: clazel_origin::spec::Origin, serial: nat)
    requires
        forall|j: int| 0 <= j < fs.len() ==> !subfetch_is(#[trigger] fs[j], id, lock, serial),
    ensures
        subfetch_of(fs, id, lock, serial) is None,
    decreases fs.len(),
{
    if fs.len() > 0 {
        let t = fs.drop_first();
        assert forall|j: int| 0 <= j < t.len() implies !subfetch_is(#[trigger] t[j], id, lock, serial) by {
            assert(t[j] == fs[j + 1]);
        }
        lemma_no_key(t, id, lock, serial);
    }
}

/// The index of the first entry of a key.
pub fn find_key_exec(fs: &[SubFetchRecord], id: u64, lock: &ParsedOrigin, serial: u64) -> (r: Option<usize>)
    ensures
        match r {
            Some(k) => k < fs.len() && subfetch_is(subfetches_view(fs@)[k as int], id as nat, lock@, serial as nat) && forall|j: int|
                0 <= j < k ==> !subfetch_is(#[trigger] subfetches_view(fs@)[j], id as nat, lock@, serial as nat),
            None => forall|j: int| 0 <= j < fs.len() ==> !subfetch_is(#[trigger] subfetches_view(fs@)[j], id as nat, lock@, serial as nat),
        },
{
    let ghost fv = subfetches_view(fs@);
    let mut i: usize = 0;
    while i < fs.len()
        invariant
            i <= fs.len(),
            fv == subfetches_view(fs@),
            forall|j: int| 0 <= j < i ==> !subfetch_is(#[trigger] fv[j], id as nat, lock@, serial as nat),
        decreases fs.len() - i,
    {
        if let Some(f) = fs.get(i) {
            proof {
                assert(fv[i as int] == f@);
            }
            if f.renderer == id && f.serial == serial && origin_eq_exec(&f.lock, lock) {
                return Some(i);
            }
        }
        i = i.saturating_add(1);
    }
    None
}

// ---------------------------------------------------------------------
// Credentials.
// ---------------------------------------------------------------------

/// Whether two optional canonical hosts are equal.
fn opt_canon_eq(a: &Option<CanonicalHostName>, b: &Option<CanonicalHostName>) -> (r: bool)
    ensures
        r == (clazel_cookie::matching::exec::option_view(*a) == clazel_cookie::matching::exec::option_view(*b)),
{
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => {
            let r = x.is_ip_address == y.is_ip_address && bytes_eq(x.name.as_slice(), y.name.as_slice());
            proof {
                if x.is_ip_address == y.is_ip_address && x.name@ == y.name@ {
                    assert(x@ == y@);
                }
            }
            r
        },
        _ => false,
    }
}

/// Whether two byte strings are equal.
fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    assert(a@ =~= b@);
    true
}

/// [`credentialed`].
pub fn credentialed_exec<F: FetchFnsExec>(fetch: &F, lock: &ParsedOrigin, url: &clazel_url::url::record::ParsedUrl) -> (r: bool)
    ensures
        r == credentialed(fetch.fetch(), lock@, url@),
{
    let u = fetch.url_fns();
    let o = u.origin(url);
    if !origin_eq_exec(&o, lock) {
        return false;
    }
    let ru = u.request_url(url);
    let lh = lock_host_exec(lock);
    lh.is_some() && opt_canon_eq(&ru.host, &lh)
}

// ---------------------------------------------------------------------
// Frames.
// ---------------------------------------------------------------------

/// One more step of [`style_body_frames`].
proof fn lemma_style_body_frames_step(request: u64, b: Seq<u8>, pos: nat)
    requires
        pos < b.len(),
    ensures
        style_body_frames(request, b.skip(pos as int)) == if b.len() - pos <= clazel_ipc::message::spec::max_style_chunk() {
            reply_frame(clazel_ipc::message::spec::Message::StyleBody { request, bytes: b.skip(pos as int) })
        } else {
            reply_frame(
                clazel_ipc::message::spec::Message::StyleBody {
                    request,
                    bytes: b.subrange(pos as int, (pos + clazel_ipc::message::spec::max_style_chunk()) as int),
                },
            ) + style_body_frames(request, b.skip((pos + clazel_ipc::message::spec::max_style_chunk()) as int))
        },
{
    let r = b.skip(pos as int);
    let c = clazel_ipc::message::spec::max_style_chunk();
    assert(r.len() == b.len() - pos);
    if r.len() > c {
        assert(r.take(c as int) =~= b.subrange(pos as int, (pos + c) as int));
        assert(r.skip(c as int) =~= b.skip((pos + c) as int));
    }
}

/// [`style_frames`] of a sheet with this content type and body.
pub fn style_frames_exec(request: u64, content_type: &[u8], body: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == style_frames(request, Document { content_type: content_type@, kind: kind_document(), body: body@ }),
{
    let mut out = reply_frame_exec(&Msg::StyleResponse { request, content_type: vstd::slice::slice_to_vec(content_type) });
    let ghost head = out@;
    let ghost c = clazel_ipc::message::spec::max_style_chunk();
    proof {
        clazel_ipc::message::codec::lemma_max_style_chunk();
        assert(body@.skip(0) =~= body@);
    }
    let chunk = clazel_ipc::message::codec::MAX_STYLE_CHUNK;
    let mut pos: usize = 0;
    while pos < body.len()
        invariant
            pos <= body.len(),
            c == clazel_ipc::message::spec::max_style_chunk(),
            chunk as nat == c,
            head + style_body_frames(request, body@) == out@ + style_body_frames(request, body@.skip(pos as int)),
        decreases body.len() - pos,
    {
        proof {
            lemma_style_body_frames_step(request, body@, pos as nat);
        }
        let rest = body.len().saturating_sub(pos);
        if rest <= chunk {
            let piece = reply_frame_exec(&Msg::StyleBody { request, bytes: vstd::slice::slice_to_vec(vstd::slice::slice_subrange(body, pos, body.len())) });
            proof {
                assert(body@.subrange(pos as int, body.len() as int) =~= body@.skip(pos as int));
                assert(body@.skip(body.len() as int) =~= Seq::<u8>::empty());
                assert(style_body_frames(request, Seq::<u8>::empty()) == Seq::<u8>::empty());
            }
            let ghost before = out@;
            out.extend_from_slice(piece.as_slice());
            assert(out@ =~= before + piece@);
            pos = body.len();
            assert(out@ + style_body_frames(request, body@.skip(pos as int)) =~= out@);
        } else {
            let end = pos.saturating_add(chunk);
            let piece = reply_frame_exec(&Msg::StyleBody { request, bytes: vstd::slice::slice_to_vec(vstd::slice::slice_subrange(body, pos, end)) });
            let ghost before = out@;
            out.extend_from_slice(piece.as_slice());
            assert(out@ =~= before + piece@);
            pos = end;
        }
    }
    let ghost before = out@;
    let tail = reply_frame_exec(&Msg::StyleEnd { request });
    out.extend_from_slice(tail.as_slice());
    proof {
        assert(body@.skip(body.len() as int) =~= Seq::<u8>::empty());
        assert(out@ =~= before + tail@);
        assert(out@ =~= head + style_body_frames(request, body@) + tail@);
    }
    out
}

/// [`style_failed_frame`].
pub fn style_failed_frame_exec(request: u64) -> (r: Vec<u8>)
    ensures
        r@ == style_failed_frame(request),
{
    reply_frame_exec(&Msg::StyleFailed { request })
}

// ---------------------------------------------------------------------
// Actions.
// ---------------------------------------------------------------------

/// The connection [`sub_actions`] ends on is the one it started from plus
/// its `Connect`s, at most.
pub proof fn lemma_sub_actions_hop(id: nat, serial: nat, request: u64, hop: nat, actions: Seq<NetAction>)
    ensures
        hop <= sub_actions(id, serial, request, hop, actions).0 <= hop + clazel_fetch::transducer::contract::count_connects(actions),
    decreases actions.len(),
{
    if actions.len() > 0 {
        lemma_count_head(actions);
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { .. } => lemma_sub_actions_hop(id, serial, request, hop + 1, actions.drop_first()),
            clazel_fetch::transducer::spec::Action::Send(_) | clazel_fetch::transducer::spec::Action::Close => lemma_sub_actions_hop(
                id,
                serial,
                request,
                hop,
                actions.drop_first(),
            ),
            _ => {},
        }
    }
}

/// [`sub_actions`].
pub fn sub_actions_exec(id: u64, serial: u64, request: u64, hop: u64, actions: Vec<ActionBuf>) -> (out: (u64, Vec<OutputRecord>, Option<Vec<u8>>))
    requires
        hop as nat + clazel_fetch::transducer::contract::count_connects(clazel_fetch::transducer::types::actions_view(actions@)) <= 0xFFFF_FFFF_FFFF_FFFFnat,
    ensures
        ({
            let (h, o, e) = sub_actions(id as nat, serial as nat, request, hop as nat, clazel_fetch::transducer::types::actions_view(actions@));
            &&& out.0 as nat == h
            &&& outputs_view(out.1@) == o
            &&& match out.2 {
                Some(v) => e == Some(v@),
                None => e is None,
            }
        }),
    decreases actions.len(),
{
    let ghost av = clazel_fetch::transducer::types::actions_view(actions@);
    if actions.is_empty() {
        proof {
            assert(av =~= Seq::<NetAction>::empty());
        }
        return (hop, no_outputs(), None);
    }
    let mut actions = actions;
    let act = actions.remove(0);
    proof {
        assert(clazel_fetch::transducer::types::actions_view(actions@) =~= av.drop_first());
        lemma_count_head(av);
        assert(av[0] == act@);
    }
    match act {
        ActionBuf::Connect { host, port, tls } => {
            let h1 = hop + 1;
            let (h, out, end) = sub_actions_exec(id, serial, request, h1, actions);
            let first = one_output(OutputRecord::SubConnect { renderer: id, serial, hop: h1, host, port: port as u64, tls });
            (h, append_outputs(first, out), end)
        },
        ActionBuf::Send(bytes) => {
            let (h, out, end) = sub_actions_exec(id, serial, request, hop, actions);
            let first = one_output(OutputRecord::SubSend { renderer: id, serial, hop, bytes });
            (h, append_outputs(first, out), end)
        },
        ActionBuf::Close => {
            let (h, out, end) = sub_actions_exec(id, serial, request, hop, actions);
            let first = one_output(OutputRecord::SubClose { renderer: id, serial, hop });
            (h, append_outputs(first, out), end)
        },
        ActionBuf::Done { url: _, response } => {
            let content_type = content_type_exec(response.fields.as_slice());
            let frames = style_frames_exec(request, content_type.as_slice(), response.body.as_slice());
            (hop, no_outputs(), Some(frames))
        },
        ActionBuf::Fail(_) => (hop, no_outputs(), Some(style_failed_frame_exec(request))),
    }
}

// ---------------------------------------------------------------------
// Events.
// ---------------------------------------------------------------------

/// The facts the sub-fetch functions keep of the parts of the state they do
/// not touch.
pub open spec fn keeps_rest(before: StateRecord, after: StateRecord) -> bool {
    &&& after.renderers@ == before.renderers@
    &&& after.storage@ == before.storage@
    &&& after.now == before.now
    &&& after.next_id == before.next_id
    &&& after.next_conn == before.next_conn
}

/// `FetchStyle { request, url }` of renderer `r` ([`fetch_style`]).
pub fn fetch_style_exec<U: UrlFnsExec, F: FetchFnsExec>(urls: &U, fetch: &F, s: StateRecord, r: &RendererRecord, request: u64, url: &[u8]) -> (out: (
    StateRecord,
    Vec<OutputRecord>,
))
    requires
        subfetches_ok::<F>(s.subfetches@),
    ensures
        result_view(out) == fetch_style(crate::contract::psl(), urls.urls(), fetch.fetch(), s@, r@, request, url@),
        subfetches_ok::<F>(out.0.subfetches@),
        keeps_rest(s, out.0),
        out.0.jar@ == s.jar@,
{
    let ghost sv = s@;
    let (serial, in_document) = subcount_of_exec(s.subcounts.as_slice(), r.id, &r.lock);
    let live = live_subfetches_exec(s.subfetches.as_slice(), r.id, &r.lock);
    if live >= 8 || in_document >= 64 || serial == 0xFFFF_FFFF_FFFF_FFFFu64 {
        let outs = reply_exec(r, &Msg::StyleFailed { request });
        return (s, outs);
    }
    let relative = match clazel_encoding::utf8::decode::decode_without_bom_or_fail(url) {
        Some(v) => v,
        None => {
            let outs = reply_exec(r, &Msg::StyleFailed { request });
            return (s, outs);
        },
    };
    let resolved = match urls.resolve(r.url.as_slice(), relative.as_slice()) {
        Some(v) => v,
        None => {
            let outs = reply_exec(r, &Msg::StyleFailed { request });
            return (s, outs);
        },
    };
    let parsed = match fetch.parse(resolved.as_slice()) {
        Some(p) => p,
        None => {
            let outs = reply_exec(r, &Msg::StyleFailed { request });
            return (s, outs);
        },
    };
    let (fs, actions) = clazel_fetch::transducer::step::start(&parsed);
    let ghost av = clazel_fetch::transducer::types::actions_view(actions@);
    proof {
        F::nav_ok_idle(&fs);
        reveal_with_fuel(clazel_fetch::transducer::contract::count_connects, 2);
    }
    let (hop, out, end) = sub_actions_exec(r.id, serial, request, 0, actions);
    proof {
        lemma_sub_actions_hop(r.id as nat, serial as nat, request, 0, av);
    }
    let counts = set_subcount_exec(s.subcounts.as_slice(), r.id, &r.lock, serial + 1, in_document + 1);
    let mut s = s;
    s.subcounts = counts;
    let ghost f = SubFetch {
        renderer: r.id as nat,
        lock: r.lock@,
        serial: serial as nat,
        request,
        tab: r.tab as nat,
        fetch: fs@,
        hop: 0,
        started: sv.now as int,
        partition: crate::domain::domain_of_renderer(crate::contract::psl(), r@),
        ended: false,
    };
    match end {
        None => {
            let ghost before = s.subfetches@;
            let rec = SubFetchRecord {
                renderer: r.id,
                lock: clone_origin(&r.lock),
                serial,
                request,
                tab: r.tab,
                fetch: fs,
                hop,
                started: s.now,
                partition: domain_of_lock_exec(&r.lock),
                ended: false,
            };
            let ghost rv = rec@;
            s.subfetches.push(rec);
            proof {
                assert(subfetches_view(s.subfetches@) =~= subfetches_view(before).push(rv));
                assert forall|i: int| 0 <= i < s.subfetches@.len() implies F::nav_ok(&(#[trigger] s.subfetches@[i]).fetch) && s.subfetches@[i].fetch@.redirects <= 20
                    && s.subfetches@[i].hop as int + clazel_fetch::transducer::theorems::connect_budget(s.subfetches@[i].fetch@) <= 21 by {
                    if i < before.len() {
                        assert(s.subfetches@[i] == before[i]);
                    }
                }
            }
            (s, out)
        },
        Some(frames) => {
            let last = one_output(OutputRecord::ToRenderer { id: r.id, bytes: frames });
            (s, append_outputs(out, last))
        },
    }
}

/// [`subfetch_live`] of an entry, for a state whose renderers are `rs`.
pub fn subfetch_live_exec(rs: &[RendererRecord], f: &SubFetchRecord, Ghost(st): Ghost<State>) -> (r: bool)
    requires
        st.renderers == renderers_view(rs@),
    ensures
        r == subfetch_live(st, f@),
{
    if f.ended {
        return false;
    }
    match find_by_id_exec(rs, f.renderer) {
        None => false,
        Some(i) => match rs.get(i) {
            Some(x) => origin_eq_exec(&x.lock, &f.lock) && x.committed,
            None => false,
        },
    }
}

/// Replacing an entry of the table replaces it in the view.
proof fn lemma_subfetches_replace(v: Seq<SubFetchRecord>, i: int, r: SubFetchRecord)
    requires
        0 <= i < v.len(),
    ensures
        subfetches_view(v.remove(i).insert(i, r)) =~= subfetches_view(v).update(i, r@),
        subfetches_view(v.remove(i)) =~= subfetches_view(v).remove(i),
{
    assert(v.remove(i).insert(i, r).len() == v.len());
    assert forall|j: int| 0 <= j < v.len() implies subfetches_view(v.remove(i).insert(i, r))[j] == subfetches_view(v).update(i, r@)[j] by {
        if j < i {
            assert(v.remove(i).insert(i, r)[j] == v[j]);
        } else if j > i {
            assert(v.remove(i).insert(i, r)[j] == v.remove(i)[j - 1]);
            assert(v.remove(i)[j - 1] == v[j]);
        }
    }
}

/// `SubNet { renderer, serial, hop, input }` ([`sub_net`]).
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn sub_net_exec<F: FetchFnsExec>(fetch: &F, s: StateRecord, renderer: u64, serial: u64, hop: u64, input: &InputBuf) -> (out: (
    StateRecord,
    Vec<OutputRecord>,
))
    requires
        subfetches_ok::<F>(s.subfetches@),
        clazel_cookie::set_cookie::contract::now_in_range(s.now as int),
        clazel_cookie::storage::contract::jar_in_range(s@.jar),
    ensures
        result_view(out) == sub_net(crate::contract::psl(), fetch.fetch(), s@, renderer as nat, serial as nat, hop as nat, input@),
        subfetches_ok::<F>(out.0.subfetches@),
        keeps_rest(s, out.0),
{
    let ghost sv = s@;
    let ri = match find_by_id_exec(s.renderers.as_slice(), renderer) {
        None => return (s, no_outputs()),
        Some(ri) => ri,
    };
    let rlock = match s.renderers.get(ri) {
        Some(x) => clone_origin(&x.lock),
        None => ParsedOrigin::Opaque(0),
    };
    let k = match find_key_exec(s.subfetches.as_slice(), renderer, &rlock, serial) {
        None => {
            proof {
                lemma_no_key(subfetches_view(s.subfetches@), renderer as nat, rlock@, serial as nat);
            }
            return (s, no_outputs());
        },
        Some(k) => k,
    };
    proof {
        let fv0 = subfetches_view(s.subfetches@);
        lemma_first_key(fv0, renderer as nat, rlock@, serial as nat, k as int, fv0[k as int]);
    }
    let (live, fhop) = match s.subfetches.get(k) {
        Some(f) => (subfetch_live_exec(s.renderers.as_slice(), f, Ghost(sv)), f.hop),
        None => (false, 0),
    };
    proof {
        assert(subfetches_view(s.subfetches@)[k as int] == s.subfetches@[k as int]@);
    }
    if !live || hop == 0 || fhop != hop {
        return (s, no_outputs());
    }
    let mut s = s;
    let ghost old_table = s.subfetches@;
    let f = s.subfetches.remove(k);
    let ghost fv = f@;
    let cred = credentialed_exec(fetch, &f.lock, &f.fetch.url);
    let h = fetch.http_fns();
    proof {
        clazel_cookie::storage::exec::lemma_jar_view_in_range(s.jar@);
        assert(old_table[k as int] == f);
        assert(F::nav_ok(&f.fetch));
    }
    let empty: Vec<clazel_cookie::storage::exec::CookieRecord> = Vec::new();
    proof {
        assert(clazel_cookie::storage::exec::jar_view(empty@) =~= Seq::<clazel_cookie::storage::spec::Cookie>::empty());
    }
    let (fs, actions, ops) = if cred {
        clazel_fetch::transducer::step::step(h, fetch.url_fns(), f.fetch, input, s.jar.as_slice(), s.now)
    } else {
        clazel_fetch::transducer::step::step(h, fetch.url_fns(), f.fetch, input, empty.as_slice(), s.now)
    };
    proof {
        clazel_fetch::transducer::theorems::lemma_step_budget(fetch.fetch().http, fetch.fetch().urls, fv.fetch, input@, subfetch_jar(fetch.fetch(), sv, fv), sv.now);
    }
    if cred {
        proof {
            let ov = clazel_fetch::transducer::types::ops_view(ops@);
            assert forall|j: int| 0 <= j < ov.len() implies clazel_cookie::set_cookie::contract::now_in_range(clazel_fetch::transducer::contract::op_now(#[trigger] ov[j])) by {
                assert(clazel_fetch::transducer::contract::op_now(ov[j]) == s.now as int);
            }
        }
        let mut jar = Vec::new();
        std::mem::swap(&mut jar, &mut s.jar);
        s.jar = apply_net_ops_exec(jar, ops.as_slice());
    }
    let ghost av = clazel_fetch::transducer::types::actions_view(actions@);
    proof {
        lemma_sub_actions_hop(renderer as nat, serial as nat, f.request, hop as nat, av);
    }
    let (h2, out, end) = sub_actions_exec(renderer, serial, f.request, hop, actions);
    match end {
        None => {
            let rec = SubFetchRecord {
                renderer: f.renderer,
                lock: f.lock,
                serial: f.serial,
                request: f.request,
                tab: f.tab,
                fetch: fs,
                hop: h2,
                started: f.started,
                partition: f.partition,
                ended: f.ended,
            };
            let ghost rv = rec@;
            s.subfetches.insert(k, rec);
            proof {
                lemma_subfetches_replace(old_table, k as int, rec);
                lemma_first_key(subfetches_view(old_table), renderer as nat, rlock@, serial as nat, k as int, rv);
                assert(old_table.remove(k as int).insert(k as int, rec) == s.subfetches@);
                assert forall|i: int| 0 <= i < s.subfetches@.len() implies F::nav_ok(&(#[trigger] s.subfetches@[i]).fetch) && s.subfetches@[i].fetch@.redirects <= 20
                    && s.subfetches@[i].hop as int + clazel_fetch::transducer::theorems::connect_budget(s.subfetches@[i].fetch@) <= 21 by {
                    if i < k {
                        assert(s.subfetches@[i] == old_table[i]);
                    } else if i > k {
                        assert(s.subfetches@[i] == old_table[i]);
                    }
                }
            }
            (s, out)
        },
        Some(frames) => {
            proof {
                lemma_subfetches_replace(old_table, k as int, f);
                lemma_first_key(subfetches_view(old_table), renderer as nat, rlock@, serial as nat, k as int, SubFetch { fetch: fs@, hop: h2 as nat, ..fv });
                assert forall|i: int| 0 <= i < s.subfetches@.len() implies F::nav_ok(&(#[trigger] s.subfetches@[i]).fetch) && s.subfetches@[i].fetch@.redirects <= 20
                    && s.subfetches@[i].hop as int + clazel_fetch::transducer::theorems::connect_budget(s.subfetches@[i].fetch@) <= 21 by {
                    if i < k {
                        assert(s.subfetches@[i] == old_table[i]);
                    } else {
                        assert(s.subfetches@[i] == old_table[i + 1]);
                    }
                }
            }
            let last = one_output(OutputRecord::ToRenderer { id: renderer, bytes: frames });
            (s, append_outputs(out, last))
        },
    }
}

/// [`sweep`] reads one entry.
proof fn lemma_sweep_skip(st: State, fs: Seq<SubFetch>, k: int)
    requires
        0 <= k < fs.len(),
    ensures
        fs.skip(k).len() > 0,
        fs.skip(k)[0] == fs[k],
        fs.skip(k).drop_first() =~= fs.skip(k + 1),
{
}

/// [`sweep`] of the table, for the state `st` it is read in.
pub fn sweep_exec<F: FetchFnsExec>(rs: &[RendererRecord], now: u64, fs: Vec<SubFetchRecord>, Ghost(st): Ghost<State>) -> (out: (Vec<SubFetchRecord>, Vec<OutputRecord>))
    requires
        st.renderers == renderers_view(rs@),
        st.now == now as int,
        subfetches_ok::<F>(fs@),
    ensures
        (subfetches_view(out.0@), outputs_view(out.1@)) == sweep(st, subfetches_view(fs@)),
        subfetches_ok::<F>(out.0@),
{
    let ghost fv = subfetches_view(fs@);
    let ghost orig = fs@;
    let mut fs = fs;
    let mut kept: Vec<SubFetchRecord> = Vec::new();
    let mut outs: Vec<OutputRecord> = Vec::new();
    proof {
        assert(fv.skip(fv.len() as int) =~= Seq::<SubFetch>::empty());
        assert(subfetches_view(kept@) =~= Seq::<SubFetch>::empty());
        assert(outputs_view(outs@) =~= Seq::<Output>::empty());
        assert(fs@ =~= orig.take(orig.len() as int));
    }
    while fs.len() > 0
        invariant
            fv == subfetches_view(orig),
            fs@ == orig.take(fs@.len() as int),
            fs@.len() <= orig.len(),
            (subfetches_view(kept@), outputs_view(outs@)) == sweep(st, fv.skip(fs@.len() as int)),
            st.renderers == renderers_view(rs@),
            st.now == now as int,
            subfetches_ok::<F>(orig),
            subfetches_ok::<F>(kept@),
        decreases fs.len(),
    {
        let ghost k = (fs@.len() - 1) as int;
        let f = match fs.pop() {
            Some(f) => f,
            None => {
                proof {
                    assert(false);
                }
                return (kept, outs);
            },
        };
        proof {
            assert(f == orig[k]);
            assert(fs@ =~= orig.take(k));
            lemma_sweep_skip(st, fv, k);
            assert(fv[k] == f@);
        }
        let live = subfetch_live_exec(rs, &f, Ghost(st));
        let close = if f.hop > 0 {
            one_output(OutputRecord::SubClose { renderer: f.renderer, serial: f.serial, hop: f.hop })
        } else {
            no_outputs()
        };
        let late = match f.started.checked_add(60) {
            Some(t) => now >= t,
            None => false,
        };
        if !live {
            outs = append_outputs(close, outs);
        } else if late {
            let failed = one_output(OutputRecord::ToRenderer { id: f.renderer, bytes: style_failed_frame_exec(f.request) });
            outs = append_outputs(append_outputs(close, failed), outs);
        } else {
            let ghost before = kept@;
            let ghost fr = f;
            kept.insert(0, f);
            proof {
                assert(subfetches_view(kept@) =~= seq![fr@] + subfetches_view(before));
                assert forall|i: int| 0 <= i < kept@.len() implies F::nav_ok(&(#[trigger] kept@[i]).fetch) && kept@[i].fetch@.redirects <= 20 && kept@[i].hop as int
                    + clazel_fetch::transducer::theorems::connect_budget(kept@[i].fetch@) <= 21 by {
                    if i > 0 {
                        assert(kept@[i] == before[i - 1]);
                    } else {
                        assert(kept@[0] == orig[k]);
                    }
                }
            }
        }
    }
    proof {
        assert(fv.skip(0) =~= fv);
    }
    (kept, outs)
}

/// `Tick(time)` ([`tick_all`]).
pub fn tick_all_exec<F: FetchFnsExec>(s: StateRecord, time: u64) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        clazel_cookie::set_cookie::contract::now_in_range(s.now as int),
        clazel_cookie::set_cookie::contract::now_in_range(time as int),
        subfetches_ok::<F>(s.subfetches@),
    ensures
        result_view(out) == tick_all(s@, time as int),
        subfetches_ok::<F>(out.0.subfetches@),
        out.0.storage@ == s.storage@,
        out.0.renderers@ == s.renderers@,
        out.0.next_id == s.next_id,
        out.0.next_conn == s.next_conn,
        clazel_cookie::set_cookie::contract::now_in_range(out.0.now as int),
{
    let (s1, _none) = tick_exec(s, time);
    let ghost s1v = s1@;
    let mut s1 = s1;
    let mut fs = Vec::new();
        std::mem::swap(&mut fs, &mut s1.subfetches);
    let (kept, outs) = sweep_exec::<F>(s1.renderers.as_slice(), s1.now, fs, Ghost(s1v));
    s1.subfetches = kept;
    (s1, outs)
}

} // verus!
