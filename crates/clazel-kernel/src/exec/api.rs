//! The exec twins of item 7.16's `fetch()` and XHR functions in
//! [`crate::spec`] ([`crate::spec::fetch_api`] and the answer it is given).
//! Each `ensures` says the function equals its spec on the views.

use super::fetch::*;
use super::frames::*;
use super::locks::*;
use super::records::*;
#[allow(unused_imports)]
use super::spec::*;
use super::step::*;
use super::subfetch::*;
use super::urls::UrlFnsExec;
use clazel_fetch::transducer::contract::UrlFnsExec as TransducerUrls;
use clazel_fetch::transducer::types::ActionBuf;
use clazel_http::field::types::FieldLineBuf;
use clazel_ipc::message::codec::Msg;
use clazel_origin::exec::ParsedOrigin;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Frames.
// ---------------------------------------------------------------------

/// [`fetch_failed_frame`].
pub fn fetch_failed_frame_exec(request: u64) -> (r: Vec<u8>)
    ensures
        r@ == fetch_failed_frame(request),
{
    reply_frame_exec(&Msg::FetchFailed { request })
}

/// [`failed_frame_of`] of a sub-fetch that is a `Fetch` (`api`) or not.
pub fn failed_frame_of_exec(api: bool, script: bool, request: u64) -> (r: Vec<u8>)
    ensures
        r@ == (if api {
            fetch_failed_frame(request)
        } else {
            sub_failed_frame(script, request)
        }),
{
    if api {
        fetch_failed_frame_exec(request)
    } else {
        sub_failed_frame_exec(script, request)
    }
}

/// [`fetch_opaque_frames`].
pub fn fetch_opaque_frames_exec(request: u64) -> (r: Vec<u8>)
    ensures
        r@ == fetch_opaque_frames(request),
{
    let empty: Vec<u8> = Vec::new();
    assert(empty@ =~= Seq::<u8>::empty());
    let mut out = reply_frame_exec(&Msg::FetchResponse { request, status: 0, content_type: empty });
    let tail = reply_frame_exec(&Msg::FetchEnd { request });
    let ghost before = out@;
    out.extend_from_slice(tail.as_slice());
    assert(out@ =~= before + tail@);
    out
}

/// One more step of [`fetch_body_frames`].
proof fn lemma_fetch_body_frames_step(request: u64, b: Seq<u8>, pos: nat)
    requires
        pos < b.len(),
    ensures
        fetch_body_frames(request, b.skip(pos as int)) == if b.len() - pos <= clazel_ipc::message::spec::max_fetch_chunk() {
            reply_frame(clazel_ipc::message::spec::Message::FetchBody { request, bytes: b.skip(pos as int) })
        } else {
            reply_frame(
                clazel_ipc::message::spec::Message::FetchBody {
                    request,
                    bytes: b.subrange(pos as int, (pos + clazel_ipc::message::spec::max_fetch_chunk()) as int),
                },
            ) + fetch_body_frames(request, b.skip((pos + clazel_ipc::message::spec::max_fetch_chunk()) as int))
        },
{
    let r = b.skip(pos as int);
    let c = clazel_ipc::message::spec::max_fetch_chunk();
    assert(r.len() == b.len() - pos);
    if r.len() > c {
        assert(r.take(c as int) =~= b.subrange(pos as int, (pos + c) as int));
        assert(r.skip(c as int) =~= b.skip((pos + c) as int));
    }
}

/// [`fetch_frames`] of `response`.
pub fn fetch_frames_exec(request: u64, response: &clazel_http::message::types::ResponseBuf) -> (r: Vec<u8>)
    ensures
        r@ == fetch_frames(request, response@),
{
    let content_type = content_type_exec(response.fields.as_slice());
    let body = response.body.as_slice();
    let mut out = reply_frame_exec(&Msg::FetchResponse { request, status: response.status_line.status as u64, content_type });
    let ghost head = out@;
    let ghost c = clazel_ipc::message::spec::max_fetch_chunk();
    proof {
        clazel_ipc::message::codec::lemma_max_fetch_chunk();
        assert(body@.skip(0) =~= body@);
    }
    let chunk = clazel_ipc::message::codec::MAX_FETCH_CHUNK;
    let mut pos: usize = 0;
    while pos < body.len()
        invariant
            pos <= body.len(),
            c == clazel_ipc::message::spec::max_fetch_chunk(),
            chunk as nat == c,
            head + fetch_body_frames(request, body@) == out@ + fetch_body_frames(request, body@.skip(pos as int)),
        decreases body.len() - pos,
    {
        proof {
            lemma_fetch_body_frames_step(request, body@, pos as nat);
        }
        let rest = body.len().saturating_sub(pos);
        if rest <= chunk {
            let piece = reply_frame_exec(&Msg::FetchBody { request, bytes: vstd::slice::slice_to_vec(vstd::slice::slice_subrange(body, pos, body.len())) });
            proof {
                assert(body@.subrange(pos as int, body.len() as int) =~= body@.skip(pos as int));
                assert(body@.skip(body.len() as int) =~= Seq::<u8>::empty());
                assert(fetch_body_frames(request, Seq::<u8>::empty()) == Seq::<u8>::empty());
            }
            let ghost before = out@;
            out.extend_from_slice(piece.as_slice());
            assert(out@ =~= before + piece@);
            pos = body.len();
            assert(out@ + fetch_body_frames(request, body@.skip(pos as int)) =~= out@);
        } else {
            let end = pos.saturating_add(chunk);
            let piece = reply_frame_exec(&Msg::FetchBody { request, bytes: vstd::slice::slice_to_vec(vstd::slice::slice_subrange(body, pos, end)) });
            let ghost before = out@;
            out.extend_from_slice(piece.as_slice());
            assert(out@ =~= before + piece@);
            pos = end;
        }
    }
    let ghost before = out@;
    let tail = reply_frame_exec(&Msg::FetchEnd { request });
    out.extend_from_slice(tail.as_slice());
    proof {
        assert(body@.skip(body.len() as int) =~= Seq::<u8>::empty());
        assert(out@ =~= before + tail@);
        assert(out@ =~= head + fetch_body_frames(request, body@) + tail@);
    }
    out
}

// ---------------------------------------------------------------------
// The CORS check and the answer.
// ---------------------------------------------------------------------

/// `s`, each code point narrowed to an octet.
fn narrow_exec(s: &[u32]) -> (out: Vec<u8>)
    ensures
        out@ == s@.map_values(|c: u32| c as u8),
{
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ =~= s@.take(i as int).map_values(|c: u32| c as u8),
        decreases s.len() - i,
    {
        if let Some(c) = s.get(i) {
            out.push(*c as u8);
            assert(s@.take(i as int + 1) =~= s@.take(i as int).push(*c));
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(s@.take(s.len() as int) =~= s@);
    out
}

/// [`request_origin`].
pub fn request_origin_exec(lock: &ParsedOrigin, tainted: bool) -> (r: Vec<u8>)
    ensures
        r@ == request_origin(lock@, tainted),
{
    if tainted {
        let v = vec![0x6Eu8, 0x75, 0x6C, 0x6C];
        assert(v@ =~= lit_null_origin());
        v
    } else {
        let s = clazel_origin::exec::serialization_of_origin_exec(lock);
        narrow_exec(s.as_slice())
    }
}

/// [`cors_check`].
pub fn cors_check_exec(fields: &[FieldLineBuf], origin: &[u8]) -> (r: bool)
    ensures
        r == cors_check(
            clazel_http::message::spec::Response {
                status_line: arbitrary_status_line(),
                fields: clazel_http::field::types::lines_view(fields@),
                body: Seq::<u8>::empty(),
            },
            origin@,
        ),
{
    let name: [u8; 27] = [
        0x61, 0x63, 0x63, 0x65, 0x73, 0x73, 0x2D, 0x63, 0x6F, 0x6E, 0x74, 0x72, 0x6F, 0x6C, 0x2D, 0x61, 0x6C, 0x6C, 0x6F, 0x77, 0x2D, 0x6F, 0x72, 0x69, 0x67,
        0x69, 0x6E,
    ];
    assert(name@ =~= lit_acao());
    match clazel_http::field::section::combined_field_value(fields, &name) {
        None => false,
        Some(v) => {
            let star: [u8; 1] = [0x2A];
            assert(star@ =~= lit_star());
            bytes_eq(v.as_slice(), &star) || bytes_eq(v.as_slice(), origin)
        },
    }
}

/// A status line for [`cors_check_exec`]'s statement (the check reads only
/// the fields).
pub open spec fn arbitrary_status_line() -> clazel_http::message::spec::StatusLine {
    clazel_http::message::spec::StatusLine { major: 1, minor: 1, status: 200, reason: Seq::<u8>::empty() }
}

/// [`cors_check`] reads only the response's fields.
pub proof fn lemma_cors_check_fields(a: clazel_http::message::spec::Response, b: clazel_http::message::spec::Response, origin: Seq<u8>)
    requires
        a.fields == b.fields,
    ensures
        cors_check(a, origin) == cors_check(b, origin),
{
}

/// [`api_readable`].
pub fn api_readable_exec<F: FetchFnsExec>(
    fetch: &F,
    lock: &ParsedOrigin,
    mode: u64,
    tainted: bool,
    url: &clazel_url::url::record::ParsedUrl,
    response: &clazel_http::message::types::ResponseBuf,
) -> (r: bool)
    ensures
        r == api_readable(fetch.fetch(), lock@, mode, tainted, url@, response@),
{
    let u = fetch.url_fns();
    let o = u.origin(url);
    if origin_eq_exec(&o, lock) && !tainted {
        return true;
    }
    if mode != 1 {
        return false;
    }
    let origin = request_origin_exec(lock, tainted);
    let ok = cors_check_exec(response.fields.as_slice(), origin.as_slice());
    proof {
        lemma_cors_check_fields(
            response@,
            clazel_http::message::spec::Response {
                status_line: arbitrary_status_line(),
                fields: clazel_http::field::types::lines_view(response.fields@),
                body: Seq::<u8>::empty(),
            },
            origin@,
        );
    }
    ok
}

/// [`end_action`] reads past actions that do not end the fetch.
proof fn lemma_end_action_skip(actions: Seq<NetAction>, k: int)
    requires
        0 <= k < actions.len(),
        !(actions[k] is Done || actions[k] is Fail),
    ensures
        end_action(actions.skip(k)) == end_action(actions.skip(k + 1)),
{
    assert(actions.skip(k)[0] == actions[k]);
    assert(actions.skip(k).drop_first() =~= actions.skip(k + 1));
}

/// [`api_end`].
pub fn api_end_exec<F: FetchFnsExec>(fetch: &F, lock: &ParsedOrigin, request: u64, mode: u64, tainted: bool, actions: &[ActionBuf]) -> (r: Vec<u8>)
    ensures
        r@ == api_end(fetch.fetch(), lock@, request, mode, tainted, clazel_fetch::transducer::types::actions_view(actions@)),
{
    let ghost av = clazel_fetch::transducer::types::actions_view(actions@);
    let mut k: usize = 0;
    proof {
        assert(av.skip(0) =~= av);
    }
    while k < actions.len()
        invariant
            k <= actions.len(),
            av == clazel_fetch::transducer::types::actions_view(actions@),
            end_action(av) == end_action(av.skip(k as int)),
        decreases actions.len() - k,
    {
        if let Some(a) = actions.get(k) {
            proof {
                assert(av[k as int] == a@);
                assert(av.skip(k as int)[0] == a@);
            }
            match a {
                ActionBuf::Done { url, response } => {
                    proof {
                        assert(end_action(av.skip(k as int)) == Some(a@));
                    }
                    if api_readable_exec(fetch, lock, mode, tainted, url, response) {
                        return fetch_frames_exec(request, response);
                    } else if mode == 2 {
                        return fetch_opaque_frames_exec(request);
                    } else {
                        return fetch_failed_frame_exec(request);
                    }
                },
                ActionBuf::Fail(_) => {
                    proof {
                        assert(end_action(av.skip(k as int)) == Some(a@));
                    }
                    return fetch_failed_frame_exec(request);
                },
                _ => {
                    proof {
                        lemma_end_action_skip(av, k as int);
                    }
                },
            }
        }
        // Never saturates: k < actions.len().
        k = k.saturating_add(1);
    }
    proof {
        assert(av.skip(actions.len() as int) =~= Seq::<NetAction>::empty());
    }
    fetch_failed_frame_exec(request)
}

// ---------------------------------------------------------------------
// The request.
// ---------------------------------------------------------------------

/// [`header_pairs`].
pub fn header_pairs_exec(ts: &[Vec<u8>]) -> (r: Option<Vec<FieldLineBuf>>)
    ensures
        match r {
            Some(v) => header_pairs(clazel_ipc::message::codec::strings_view(ts@)) == Some(clazel_http::field::types::lines_view(v@)),
            None => header_pairs(clazel_ipc::message::codec::strings_view(ts@)) is None,
        },
{
    let ghost tv = clazel_ipc::message::codec::strings_view(ts@);
    if ts.len() % 2 == 1 {
        proof {
            lemma_header_pairs_odd(tv);
        }
        return None;
    }
    let mut out: Vec<FieldLineBuf> = Vec::new();
    let mut k: usize = 0;
    proof {
        lemma_header_pairs_even(tv);
        assert(tv.skip(0) =~= tv);
        assert(clazel_http::field::types::lines_view(out@) =~= Seq::<clazel_http::field::spec::FieldLine>::empty());
        assert(Seq::<clazel_http::field::spec::FieldLine>::empty() + header_pairs(tv)->Some_0 =~= header_pairs(tv)->Some_0);
    }
    while k.saturating_add(1) < ts.len()
        invariant
            k <= ts.len(),
            k % 2 == 0,
            ts.len() % 2 == 0,
            tv == clazel_ipc::message::codec::strings_view(ts@),
            header_pairs(tv) == Some(clazel_http::field::types::lines_view(out@) + header_pairs(tv.skip(k as int))->Some_0),
            header_pairs(tv.skip(k as int)) is Some,
        decreases ts.len() - k,
    {
        let name = match ts.get(k) {
            Some(n) => vstd::slice::slice_to_vec(n.as_slice()),
            None => Vec::new(),
        };
        let value = match ts.get(k.saturating_add(1)) {
            Some(v) => vstd::slice::slice_to_vec(v.as_slice()),
            None => Vec::new(),
        };
        proof {
            let rest = tv.skip(k as int);
            assert(rest.subrange(2, rest.len() as int) =~= tv.skip(k as int + 2));
            assert(rest[0] == name@ && rest[1] == value@);
        }
        let ghost before = out@;
        out.push(FieldLineBuf { name, value });
        proof {
            let pair = clazel_http::field::spec::FieldLine { name: tv[k as int], value: tv[k as int + 1] };
            assert(clazel_http::field::types::lines_view(out@) =~= clazel_http::field::types::lines_view(before).push(pair));
            let rest = tv.skip(k as int);
            assert(rest[0] == tv[k as int] && rest[1] == tv[k as int + 1]);
            assert(header_pairs(rest) == Some(seq![pair] + header_pairs(tv.skip(k as int + 2))->Some_0));
            assert(clazel_http::field::types::lines_view(out@) + header_pairs(tv.skip(k as int + 2))->Some_0 =~= clazel_http::field::types::lines_view(before)
                + header_pairs(rest)->Some_0);
        }
        k = k.saturating_add(2);
    }
    proof {
        assert(k == ts.len());
        assert(tv.skip(k as int) =~= Seq::<Seq<u8>>::empty());
        assert(clazel_http::field::types::lines_view(out@) + Seq::<clazel_http::field::spec::FieldLine>::empty() =~= clazel_http::field::types::lines_view(out@));
    }
    Some(out)
}

/// An odd number of texts has no pairs.
proof fn lemma_header_pairs_odd(ts: Seq<Seq<u8>>)
    requires
        ts.len() % 2 == 1,
    ensures
        header_pairs(ts) is None,
    decreases ts.len(),
{
    if ts.len() > 1 {
        lemma_header_pairs_odd(ts.subrange(2, ts.len() as int));
    }
}

/// An even number of texts has pairs.
proof fn lemma_header_pairs_even(ts: Seq<Seq<u8>>)
    requires
        ts.len() % 2 == 0,
    ensures
        header_pairs(ts) is Some,
    decreases ts.len(),
{
    if ts.len() > 0 {
        lemma_header_pairs_even(ts.subrange(2, ts.len() as int));
    }
}

/// [`clazel_fetch::request::spec::filter_author_headers`].
pub fn filter_author_headers_exec(lines: Vec<FieldLineBuf>) -> (r: Vec<FieldLineBuf>)
    ensures
        clazel_http::field::types::lines_view(r@) == clazel_fetch::request::spec::filter_author_headers(clazel_http::field::types::lines_view(lines@)),
{
    let ghost lv = clazel_http::field::types::lines_view(lines@);
    let mut out: Vec<FieldLineBuf> = Vec::new();
    let mut k: usize = 0;
    proof {
        reveal(Seq::filter);
        assert(lv.take(0) =~= Seq::<clazel_http::field::spec::FieldLine>::empty());
        assert(clazel_http::field::types::lines_view(out@) =~= Seq::<clazel_http::field::spec::FieldLine>::empty());
    }
    while k < lines.len()
        invariant
            k <= lines.len(),
            lv == clazel_http::field::types::lines_view(lines@),
            clazel_http::field::types::lines_view(out@) == lv.take(k as int).filter(
                |h: clazel_http::field::spec::FieldLine| !clazel_fetch::request::spec::author_header_dropped(h.name),
            ),
        decreases lines.len() - k,
    {
        if let Some(h) = lines.get(k) {
            proof {
                reveal(Seq::filter);
                assert(lv.take(k as int + 1).drop_last() =~= lv.take(k as int));
                assert(lv.take(k as int + 1).last() == h@);
            }
            if !clazel_fetch::request::build::author_header_dropped_exec(h.name.as_slice()) {
                let ghost before = out@;
                out.push(FieldLineBuf { name: vstd::slice::slice_to_vec(h.name.as_slice()), value: vstd::slice::slice_to_vec(h.value.as_slice()) });
                proof {
                    assert(clazel_http::field::types::lines_view(out@) =~= clazel_http::field::types::lines_view(before).push(h@));
                }
            }
        }
        // Never saturates: k < lines.len().
        k = k.saturating_add(1);
    }
    proof {
        assert(lv.take(lines.len() as int) =~= lv);
    }
    out
}

/// [`api_request`].
pub fn api_request_exec(r: &RendererRecord, method: &[u8], content_type: Vec<u8>, body: Vec<u8>, mode: u64, headers: &[Vec<u8>]) -> (out: Option<
    clazel_fetch::request::build::ReqBuf,
>)
    ensures
        match out {
            Some(q) => api_request(r@, method@, content_type@, body@, mode, clazel_ipc::message::codec::strings_view(headers@)) == Some(q@),
            None => api_request(r@, method@, content_type@, body@, mode, clazel_ipc::message::codec::strings_view(headers@)) is None,
        },
{
    let req = submit_request_exec(r, method, content_type, body);
    let lines = header_pairs_exec(headers);
    match (req, lines) {
        (Some(q), Some(ls)) => {
            if mode > 2 {
                return None;
            }
            let mut q = q;
            q.headers = filter_author_headers_exec(ls);
            q.cors = mode == 1;
            Some(q)
        },
        _ => None,
    }
}

/// [`content_type_safelisted`].
pub fn content_type_safelisted_exec(v: &[u8]) -> (r: bool)
    ensures
        r == content_type_safelisted(v@),
{
    if v.is_empty() {
        return true;
    }
    if v.len() > 128 {
        return false;
    }
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            forall|j: int| 0 <= j < i ==> !cors_unsafe_byte(#[trigger] v@[j]),
        decreases v.len() - i,
    {
        if let Some(b) = v.get(i) {
            let b = *b;
            if (b < 0x20 && b != 0x09) || b == 0x22 || b == 0x28 || b == 0x29 || b == 0x3A || b == 0x3C || b == 0x3E || b == 0x3F || b == 0x40 || b == 0x5B
                || b == 0x5C || b == 0x5D || b == 0x7B || b == 0x7D || b == 0x7F {
                proof {
                    assert(cors_unsafe_byte(v@[i as int]));
                }
                return false;
            }
        }
        // Never saturates: i < v.len().
        i = i.saturating_add(1);
    }
    let l = clazel_fetch::request::build::byte_lowercase_exec(v);
    let e0: [u8; 33] = [
        0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x77, 0x77, 0x77, 0x2D, 0x66, 0x6F, 0x72, 0x6D, 0x2D, 0x75, 0x72,
        0x6C, 0x65, 0x6E, 0x63, 0x6F, 0x64, 0x65, 0x64,
    ];
    let e1: [u8; 19] = [0x6D, 0x75, 0x6C, 0x74, 0x69, 0x70, 0x61, 0x72, 0x74, 0x2F, 0x66, 0x6F, 0x72, 0x6D, 0x2D, 0x64, 0x61, 0x74, 0x61];
    let e2: [u8; 10] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x70, 0x6C, 0x61, 0x69, 0x6E];
    proof {
        assert(safelisted_essences()[0] =~= e0@);
        assert(safelisted_essences()[1] =~= e1@);
        assert(safelisted_essences()[2] =~= e2@);
    }
    let r0 = has_essence_exec(l.as_slice(), &e0);
    let r1 = has_essence_exec(l.as_slice(), &e1);
    let r2 = has_essence_exec(l.as_slice(), &e2);
    proof {
        if r0 {
            assert(has_essence(v@, safelisted_essences()[0]));
        }
        if r1 {
            assert(has_essence(v@, safelisted_essences()[1]));
        }
        if r2 {
            assert(has_essence(v@, safelisted_essences()[2]));
        }
        if !(r0 || r1 || r2) {
            assert forall|k: int| 0 <= k < safelisted_essences().len() implies !has_essence(v@, #[trigger] safelisted_essences()[k]) by {
                if k == 0 {
                } else if k == 1 {
                } else {
                }
            }
        }
    }
    r0 || r1 || r2
}

/// [`has_essence`] of a value already byte-lowercased (`l`).
fn has_essence_exec(l: &[u8], e: &[u8]) -> (r: bool)
    requires
        e@.len() > 0,
    ensures
        forall|v: Seq<u8>| clazel_fetch::request::spec::byte_lowercase(v) == l@ ==> r == has_essence(v, e@),
{
    let mut with_semi = vstd::slice::slice_to_vec(e);
    with_semi.push(0x3B);
    assert(with_semi@ =~= e@ + seq![0x3Bu8]);
    bytes_eq(l, e) || clazel_fetch::request::build::starts_with_exec(l, with_semi.as_slice())
}

/// [`needs_no_preflight`].
pub fn needs_no_preflight_exec(req: &clazel_fetch::request::build::ReqBuf) -> (r: bool)
    ensures
        r == needs_no_preflight(req@),
{
    if !req.headers.is_empty() {
        return false;
    }
    match &req.body {
        Some(p) => content_type_safelisted_exec(p.content_type.as_slice()),
        None => true,
    }
}

// ---------------------------------------------------------------------
// The event.
// ---------------------------------------------------------------------

/// `Fetch { request, method, url, content_type, body, mode, headers }` of
/// renderer `r` ([`fetch_api`]).
pub fn fetch_api_exec<U: UrlFnsExec, F: FetchFnsExec>(urls: &U, fetch: &F, s: StateRecord, r: &RendererRecord, m: Msg) -> (out: (StateRecord, Vec<OutputRecord>))
    requires
        subfetches_ok::<F>(s.subfetches@),
        m@ is Fetch,
    ensures
        result_view(out) == fetch_api(
            crate::contract::psl(),
            urls.urls(),
            fetch.fetch(),
            s@,
            r@,
            m@->Fetch_request,
            m@->Fetch_method,
            m@->Fetch_url,
            m@->Fetch_content_type,
            m@->Fetch_body,
            m@->Fetch_mode,
            m@->Fetch_headers,
        ),
        subfetches_ok::<F>(out.0.subfetches@),
        keeps_rest(s, out.0),
        out.0.jar@ == s.jar@,
{
    let (request, method, url, content_type, body, mode, headers) = match m {
        Msg::Fetch { request, method, url, content_type, body, mode, headers } => (request, method, url, content_type, body, mode, headers),
        _ => {
            proof {
                assert(false);
            }
            return (s, no_outputs());
        },
    };
    let method = method.as_slice();
    let url = url.as_slice();
    let headers = headers.as_slice();
    let ghost sv = s@;
    let (serial, in_document) = subcount_of_exec(s.subcounts.as_slice(), r.id, &r.lock);
    let live = live_subfetches_exec(s.subfetches.as_slice(), r.id, &r.lock);
    if live >= 8 || in_document >= 64 || serial == 0xFFFF_FFFF_FFFF_FFFFu64 {
        let outs = one_output(OutputRecord::ToRenderer { id: r.id, bytes: fetch_failed_frame_exec(request) });
        return (s, outs);
    }
    let req = match api_request_exec(r, method, content_type, body, mode, headers) {
        Some(q) => q,
        None => {
            let outs = one_output(OutputRecord::ToRenderer { id: r.id, bytes: fetch_failed_frame_exec(request) });
            return (s, outs);
        },
    };
    let relative = match clazel_encoding::utf8::decode::decode_without_bom_or_fail(url) {
        Some(v) => v,
        None => {
            let outs = one_output(OutputRecord::ToRenderer { id: r.id, bytes: fetch_failed_frame_exec(request) });
            return (s, outs);
        },
    };
    let resolved = match urls.resolve(r.url.as_slice(), relative.as_slice()) {
        Some(v) => v,
        None => {
            let outs = one_output(OutputRecord::ToRenderer { id: r.id, bytes: fetch_failed_frame_exec(request) });
            return (s, outs);
        },
    };
    let parsed = match fetch.parse(resolved.as_slice()) {
        Some(p) => p,
        None => {
            let outs = one_output(OutputRecord::ToRenderer { id: r.id, bytes: fetch_failed_frame_exec(request) });
            return (s, outs);
        },
    };
    let o = fetch.url_fns().origin(&parsed);
    if !origin_eq_exec(&o, &r.lock) && (mode == 0 || !needs_no_preflight_exec(&req)) {
        let outs = one_output(OutputRecord::ToRenderer { id: r.id, bytes: fetch_failed_frame_exec(request) });
        return (s, outs);
    }
    let ghost rq = req@;
    let (fs, actions) = clazel_fetch::transducer::step::start_req(&parsed, req);
    let ghost av = clazel_fetch::transducer::types::actions_view(actions@);
    proof {
        F::nav_ok_idle(&fs);
        reveal_with_fuel(clazel_fetch::transducer::contract::count_connects, 2);
    }
    let tainted = fs.req.origin_tainted;
    let api_frames = api_end_exec(fetch, &r.lock, request, mode, tainted, actions.as_slice());
    let (hop, out, end) = sub_actions_exec(r.id, serial, request, false, 0, actions);
    proof {
        lemma_sub_actions_hop(r.id as nat, serial as nat, request, false, 0, av);
    }
    let end = if end.is_some() {
        Some(api_frames)
    } else {
        None
    };
    let counts = set_subcount_exec(s.subcounts.as_slice(), r.id, &r.lock, serial.saturating_add(1), in_document.saturating_add(1));
    let mut s = s;
    s.subcounts = counts;
    match end {
        None => {
            let ghost before = s.subfetches@;
            let rec = SubFetchRecord {
                renderer: r.id,
                lock: clone_origin(&r.lock),
                serial,
                request,
                script: false,
                tab: r.tab,
                fetch: fs,
                hop,
                started: s.now,
                partition: domain_of_lock_exec(&r.lock),
                ended: false,
                api: Some(mode),
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

} // verus!
