//! The executable transducer, proven to meet [`super::contract`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::contract::{HttpFnsExec, UrlFnsExec};
use super::types::{ActionBuf, InputBuf, JarOpBuf, LocationBuf, PhaseBuf, SettledBuf, StateBuf};
use crate::request::build::{connect_to, is_interim, request_bytes, request_bytes_cookie};
use clazel_cookie::storage::exec::{
    CookieRecord, HttpRequestRecord, RequestContextRecord, clone_cookie,
    retrieve_a_cookie_string_exec, store_a_set_cookie_string_exec,
};
use clazel_http::field::section::field_values_named;
use clazel_http::field::string::copy;
use clazel_http::message::body::ResponseParser;
use clazel_http::message::types::{ParseBuf, ResponseBuf};
use clazel_origin::exec::{ParsedOrigin, same_site_exec};
use clazel_url::url::record::{ParsedUrl, clone_opt_str, clone_url, eq_str};

verus! {

/// `begin`: ask for the connection for `url`, or fail.
fn begin_exec(url: ParsedUrl, redirects: u8, tainted: bool) -> (out: (StateBuf, Vec<ActionBuf>))
    ensures
        (out.0@, super::types::actions_view(out.1@)) == begin(url@, redirects as nat, tainted),
        !(out.0.phase is Reading),
{
    match (connect_to(&url), request_bytes(&url)) {
        (Some((host, port)), Some(_)) => {
            let a = vec![ActionBuf::Connect { host, port, tls: false }];
            assert(super::types::actions_view(a@) =~= begin(url@, redirects as nat, tainted).1);
            (StateBuf { url, redirects, phase: PhaseBuf::Connecting, tainted }, a)
        },
        _ => {
            let a = vec![ActionBuf::Fail(Reason::NotFetched)];
            assert(super::types::actions_view(a@) =~= begin(url@, redirects as nat, tainted).1);
            (StateBuf { url, redirects, phase: PhaseBuf::Finished, tainted }, a)
        },
    }
}

/// `start`: the first state and actions of a fetch of `url`.
pub fn start(url: &ParsedUrl) -> (out: (StateBuf, Vec<ActionBuf>))
    ensures
        super::contract::start_ensures(url@, out.0@, super::types::actions_view(out.1@)),
        super::contract::step_requires(out.0@),
        !(out.0.phase is Reading),
{
    begin_exec(clone_url(url), 0, false)
}

/// `close_if(open)` followed by `rest`.
fn after_close(open: bool, rest: Vec<ActionBuf>) -> (out: Vec<ActionBuf>)
    ensures
        super::types::actions_view(out@) == close_if(open) + super::types::actions_view(rest@),
{
    let mut a: Vec<ActionBuf> = Vec::new();
    if open {
        a.push(ActionBuf::Close);
    }
    let ghost first = a@;
    let ghost tail = rest@;
    let mut rest = rest;
    a.append(&mut rest);
    assert(super::types::actions_view(first) =~= close_if(open));
    assert(super::types::actions_view(a@) =~= close_if(open) + super::types::actions_view(tail));
    a
}

/// `fail` for a state `s`, given as `base`, which is [`finished`] of it,
/// with the jar operations `ops` before.
fn fail_exec(base: StateBuf, reason: Reason, open: bool, ops: Vec<JarOpBuf>, Ghost(s): Ghost<State>) -> (out: (StateBuf, Vec<ActionBuf>, Vec<JarOpBuf>))
    requires
        base@ == finished(s),
    ensures
        (out.0@, super::types::actions_view(out.1@), super::types::ops_view(out.2@)) == with_ops(fail(s, reason, open), super::types::ops_view(ops@)),
        out.0@.redirects == s.redirects,
        !(out.0.phase is Reading),
{
    let last = vec![ActionBuf::Fail(reason)];
    assert(super::types::actions_view(last@) =~= seq![Action::Fail(reason)]);
    assert(super::types::ops_view(ops@) + Seq::<JarOp>::empty() =~= super::types::ops_view(ops@));
    (base, after_close(open, last), ops)
}

/// `is_redirect_status` (Fetch §2.2.3).
fn is_redirect_status_exec(status: u16) -> (r: bool)
    ensures
        r == is_redirect_status(status as nat),
{
    status == 301 || status == 302 || status == 303 || status == 307 || status == 308
}

/// `location_url` (Fetch §2.2.6).
fn location_url_exec<U: UrlFnsExec>(u: &U, response: &ResponseBuf, request_url: &ParsedUrl) -> (out: LocationBuf)
    ensures
        out@ == location_url(u.urls(), response@, request_url@),
{
    // 1.
    if !is_redirect_status_exec(response.status_line.status) {
        return LocationBuf::Null;
    }
    // 2.
    let values = field_values_named(response.fields.as_slice(), &[0x4C, 0x6F, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E]);
    proof {
        assert(seq![0x4Cu8, 0x6F, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E] =~= lit_location());
    }
    if values.is_empty() {
        return LocationBuf::Null;
    }
    if values.len() > 1 {
        return LocationBuf::Failure;
    }
    match values.first() {
        None => LocationBuf::Failure,
        Some(value) => {
            // 3.
            match u.location(request_url, value.as_slice()) {
                None => LocationBuf::Failure,
                Some(location) => {
                    // 4.
                    let mut location = location;
                    let ghost before = location@;
                    if location.fragment.is_none() {
                        location.fragment = clone_opt_str(&request_url.fragment);
                    }
                    assert(location@ == with_fragment(before, request_url@.fragment));
                    // 5.
                    LocationBuf::Url(location)
                },
            }
        },
    }
}

/// `request_context` (RFC 6265bis §5.2) for a state whose URL is `url`.
fn request_context_exec<U: UrlFnsExec>(u: &U, url: &ParsedUrl, tainted: bool, Ghost(s): Ghost<State>) -> (r: RequestContextRecord)
    requires
        s.url == url@,
        s.tainted == tainted,
    ensures
        r@ == request_context(u.urls(), s),
{
    let url_origin = u.origin(url);
    let site_for_cookies = if tainted {
        Some(ParsedOrigin::Opaque(0))
    } else {
        None
    };
    RequestContextRecord::Http(HttpRequestRecord {
        url_origin,
        site_for_cookies,
        is_reload_navigation: false,
        reloaded_document_was_same_site: false,
        navigates_top_level_traversable: true,
        method_is_safe: true,
        target_is_active_or_top_level: true,
    })
}

/// `retrieval_op` for a state whose URL is `url`.
fn retrieval_op_exec<U: UrlFnsExec>(u: &U, url: &ParsedUrl, tainted: bool, now: u64, Ghost(s): Ghost<State>) -> (r: JarOpBuf)
    requires
        s.url == url@,
        s.tainted == tainted,
    ensures
        r@ == retrieval_op(u.urls(), s, now as int),
{
    JarOpBuf::Retrieved { url: u.request_url(url), ctx: request_context_exec(u, url, tainted, Ghost(s)), now }
}

/// `response_ops` (Fetch §3.1.2 step 6) of `lines`, the response's
/// `Set-Cookie` values, for a state whose URL is `url`.
fn response_ops_exec<U: UrlFnsExec>(u: &U, url: &ParsedUrl, tainted: bool, lines: &[Vec<u8>], now: u64, Ghost(s): Ghost<State>) -> (out: Vec<JarOpBuf>)
    requires
        s.url == url@,
        s.tainted == tainted,
    ensures
        super::types::ops_view(out@) == stored_ops(clazel_http::field::types::strings_view(lines@), (u.urls().request_url)(s.url), request_context(u.urls(), s), now as int),
{
    let ghost ls = clazel_http::field::types::strings_view(lines@);
    let ghost ru = (u.urls().request_url)(s.url);
    let ghost rc = request_context(u.urls(), s);
    let mut out: Vec<JarOpBuf> = Vec::new();
    let mut i: usize = 0;
    assert(ls.skip(0) =~= ls);
    assert(super::types::ops_view(out@) =~= Seq::<JarOp>::empty());
    while i < lines.len()
        invariant
            i <= lines.len(),
            ls == clazel_http::field::types::strings_view(lines@),
            ru == (u.urls().request_url)(s.url),
            rc == request_context(u.urls(), s),
            s.url == url@,
            s.tainted == tainted,
            super::types::ops_view(out@) + stored_ops(ls.skip(i as int), ru, rc, now as int) == stored_ops(ls, ru, rc, now as int),
        decreases lines.len() - i,
    {
        if let Some(value) = lines.get(i) {
            let line = copy(value.as_slice());
            proof {
                assert(ls.skip(i as int).drop_first() =~= ls.skip(i as int + 1));
                assert(ls.skip(i as int)[0] == ls[i as int]);
                assert(ls[i as int] == lines@[i as int]@);
            }
            let op = JarOpBuf::Stored { line, url: u.request_url(url), ctx: request_context_exec(u, url, tainted, Ghost(s)), now };
            let ghost before = out@;
            out.push(op);
            proof {
                assert(super::types::ops_view(out@) =~= super::types::ops_view(before).push(op@));
                assert(stored_ops(ls.skip(i as int), ru, rc, now as int) =~= seq![op@] + stored_ops(ls.skip(i as int + 1), ru, rc, now as int));
                assert(super::types::ops_view(before).push(op@) + stored_ops(ls.skip(i as int + 1), ru, rc, now as int)
                    =~= super::types::ops_view(before) + stored_ops(ls.skip(i as int), ru, rc, now as int));
            }
        }
        // Never saturates: i < lines.len().
        i = i.saturating_add(1);
    }
    assert(ls.skip(lines.len() as int) =~= Seq::<Seq<u8>>::empty());
    assert(super::types::ops_view(out@) + Seq::<JarOp>::empty() =~= super::types::ops_view(out@));
    out
}

/// `on_final` (Fetch §4.5) for a state `s0`, given as `base`, which is
/// [`finished`] of it.
fn on_final_exec<U: UrlFnsExec>(u: &U, base: StateBuf, response: ResponseBuf, open: bool, now: u64, Ghost(s0): Ghost<State>) -> (out: (StateBuf, Vec<ActionBuf>, Vec<JarOpBuf>))
    requires
        base@ == finished(s0),
        s0.redirects <= max_redirects(),
    ensures
        (out.0@, super::types::actions_view(out.1@), super::types::ops_view(out.2@)) == on_final(u.urls(), s0, response@, open, now as int),
        out.0@.redirects <= max_redirects(),
        !(out.0.phase is Reading),
{
    let url = base.url;
    let redirects = base.redirects;
    let tainted = base.tainted;
    // Fetch §4.7 step 17: the operations storing the response's `Set-Cookie` lines.
    let lines = field_values_named(response.fields.as_slice(), &[0x53, 0x65, 0x74, 0x2D, 0x43, 0x6F, 0x6F, 0x6B, 0x69, 0x65]);
    proof {
        assert(seq![0x53u8, 0x65, 0x74, 0x2D, 0x43, 0x6F, 0x6F, 0x6B, 0x69, 0x65] =~= lit_set_cookie());
    }
    let ops = response_ops_exec(u, &url, tainted, lines.as_slice(), now, Ghost(s0));
    let ghost s = s0;
    // 3.
    match location_url_exec(u, &response, &url) {
        // 4.
        LocationBuf::Null => {
            let ghost r = response@;
            let last = vec![ActionBuf::Done { url: Box::new(clone_url(&url)), response: Box::new(response) }];
            assert(super::types::actions_view(last@) =~= seq![Action::Done { url: s.url, response: r }]);
            let st = StateBuf { url, redirects, phase: PhaseBuf::Finished, tainted };
            assert(st@ == finished(s));
            let acts = after_close(open, last);
            assert(super::types::actions_view(acts@) == close_if(open) + seq![Action::Done { url: s.url, response: r }]);
            (st, acts, ops)
        },
        // 5.
        LocationBuf::Failure => fail_exec(StateBuf { url, redirects, phase: PhaseBuf::Finished, tainted }, Reason::RedirectLocation, open, ops, Ghost(s)),
        LocationBuf::Url(location) => {
            proof {
                assert(seq![0x68u32, 0x74, 0x74, 0x70] =~= clazel_url::url::spec::http_str());
                assert(seq![0x68u32, 0x74, 0x74, 0x70, 0x73] =~= clazel_url::url::spec::https_str());
            }
            let http_s = eq_str(location.scheme.as_slice(), &[0x68, 0x74, 0x74, 0x70])
                || eq_str(location.scheme.as_slice(), &[0x68, 0x74, 0x74, 0x70, 0x73]);
            if !http_s {
                // 6.
                fail_exec(StateBuf { url, redirects, phase: PhaseBuf::Finished, tainted }, Reason::RedirectScheme, open, ops, Ghost(s))
            } else if redirects >= 20 {
                // 7.
                fail_exec(StateBuf { url, redirects, phase: PhaseBuf::Finished, tainted }, Reason::RedirectLimit, open, ops, Ghost(s))
            } else {
                // 8., 18., 22. and the redirect-taint.
                let from = u.origin(&url);
                let to = u.origin(&location);
                let crossed = !same_site_exec(&from, &to);
                proof {
                    u.rules_are_psl();
                }
                // Never saturates: redirects < 20.
                let next = begin_exec(location, redirects.saturating_add(1), tainted || crossed);
                (next.0, after_close(open, next.1), ops)
            }
        },
    }
}

/// `settle` of all that `p` received, given `first`, the parser's answer
/// for it: skip complete interim responses at the start, each time
/// reading what follows into a new parser.
fn settle_exec<H: HttpFnsExec>(h: &H, p: ResponseParser, first: ParseBuf) -> (out: SettledBuf)
    requires
        h.parser_ok(&p),
        first@ == (h.http().parse)(p.received()),
    ensures
        out@ == settle(h.http(), p.received()),
        match out {
            SettledBuf::Wait(q) => h.parser_ok(&q),
            _ => true,
        },
{
    let ghost all = p.received();
    let mut cur = p;
    let mut answer = first;
    loop
        invariant
            all == p.received(),
            h.parser_ok(&cur),
            answer@ == (h.http().parse)(cur.received()),
            settle(h.http(), cur.received()) == settle(h.http(), all),
        decreases cur.received().len(),
    {
        match answer {
            ParseBuf::Incomplete => {
                return SettledBuf::Wait(cur);
            },
            ParseBuf::Invalid => {
                return SettledBuf::Bad(Reason::Invalid);
            },
            ParseBuf::Unsupported => {
                return SettledBuf::Bad(Reason::Unsupported);
            },
            ParseBuf::Done { response, rest } => {
                if is_interim(response.status_line.status) {
                    if rest.len() < cur.received_bytes().len() {
                        let mut next = h.new_parser();
                        answer = h.feed(&mut next, rest.as_slice());
                        assert(next.received() =~= rest@);
                        cur = next;
                    } else {
                        return SettledBuf::Bad(Reason::Invalid);
                    }
                } else {
                    return SettledBuf::Final(response);
                }
            },
        }
    }
}

/// `settle_at_close` of all that `p` received.
fn settle_at_close_exec<H: HttpFnsExec>(h: &H, p: ResponseParser) -> (out: SettledBuf)
    requires
        h.parser_ok(&p),
    ensures
        out@ == settle_at_close(h.http(), p.received()),
{
    match h.parse_at_close(p) {
        ParseBuf::Done { response, rest: _ } => if is_interim(response.status_line.status) {
            SettledBuf::Bad(Reason::Incomplete)
        } else {
            SettledBuf::Final(response)
        },
        ParseBuf::Invalid => SettledBuf::Bad(Reason::Invalid),
        ParseBuf::Unsupported => SettledBuf::Bad(Reason::Unsupported),
        ParseBuf::Incomplete => SettledBuf::Bad(Reason::Incomplete),
    }
}

/// `step` while reading the response into `parser`; `base` is the state
/// [`finished`], which every branch but the waiting one returns. The jar is
/// not read in this phase, so the result is `step`'s for every jar.
fn step_reading<H: HttpFnsExec, U: UrlFnsExec>(h: &H, u: &U, base: StateBuf, parser: ResponseParser, input: &InputBuf, now: u64, Ghost(s): Ghost<State>) -> (out: (StateBuf, Vec<ActionBuf>, Vec<JarOpBuf>))
    requires
        base@ == finished(s),
        s.redirects <= max_redirects(),
        s.phase == (Phase::Reading { received: parser.received() }),
        h.parser_ok(&parser),
    ensures
        forall|jar: Seq<Cookie>| #[trigger] super::contract::step_ensures(h.http(), u.urls(), s, input@, jar, now as int, out.0@, super::types::actions_view(out.1@), super::types::ops_view(out.2@)),
        out.0@.redirects <= max_redirects(),
        super::contract::state_ok(h, &out.0),
{
    let none: Vec<JarOpBuf> = Vec::new();
    assert(super::types::ops_view(none@) =~= Seq::<JarOp>::empty());
    match input {
        InputBuf::Connected => fail_exec(base, Reason::Shell, true, none, Ghost(s)),
        InputBuf::Bytes(bytes) => {
            let mut parser = parser;
            let first = h.feed(&mut parser, bytes.as_slice());
            match settle_exec(h, parser, first) {
                SettledBuf::Wait(rest) => {
                    let a: Vec<ActionBuf> = Vec::new();
                    assert(super::types::actions_view(a@) =~= Seq::<Action>::empty());
                    let url = base.url;
                    let redirects = base.redirects;
                    let tainted = base.tainted;
                    (StateBuf { url, redirects, phase: PhaseBuf::Reading { parser: rest }, tainted }, a, none)
                },
                SettledBuf::Final(response) => on_final_exec(u, base, response, true, now, Ghost(s)),
                SettledBuf::Bad(reason) => fail_exec(base, reason, true, none, Ghost(s)),
            }
        },
        InputBuf::Closed => match settle_at_close_exec(h, parser) {
            SettledBuf::Final(response) => on_final_exec(u, base, response, false, now, Ghost(s)),
            SettledBuf::Bad(reason) => fail_exec(base, reason, false, none, Ghost(s)),
            SettledBuf::Wait(_) => fail_exec(base, Reason::Incomplete, false, none, Ghost(s)),
        },
        InputBuf::Error => fail_exec(base, Reason::Network, true, none, Ghost(s)),
    }
}

/// A copy of `jar`.
fn copy_jar(jar: &[CookieRecord]) -> (out: Vec<CookieRecord>)
    ensures
        clazel_cookie::storage::exec::jar_view(out@) == clazel_cookie::storage::exec::jar_view(jar@),
{
    let mut out: Vec<CookieRecord> = Vec::new();
    let mut i: usize = 0;
    while i < jar.len()
        invariant
            i <= jar.len(),
            clazel_cookie::storage::exec::jar_view(out@) == clazel_cookie::storage::exec::jar_view(jar@).take(i as int),
        decreases jar.len() - i,
    {
        if let Some(cookie) = jar.get(i) {
            let ghost before = out@;
            out.push(clone_cookie(cookie));
            assert(clazel_cookie::storage::exec::jar_view(out@) =~= clazel_cookie::storage::exec::jar_view(before).push(jar@[i as int]@));
            assert(clazel_cookie::storage::exec::jar_view(jar@).take(i as int + 1) =~= clazel_cookie::storage::exec::jar_view(jar@).take(i as int).push(jar@[i as int]@));
        }
        // Never saturates: i < jar.len().
        i = i.saturating_add(1);
    }
    assert(clazel_cookie::storage::exec::jar_view(jar@).take(jar.len() as int) =~= clazel_cookie::storage::exec::jar_view(jar@));
    out
}

/// `step`: the next state, actions and jar operations after `input`, given
/// the jar `jar` at time `now`.
pub fn step<H: HttpFnsExec, U: UrlFnsExec>(h: &H, u: &U, s: StateBuf, input: &InputBuf, jar: &[CookieRecord], now: u64) -> (out: (
    StateBuf,
    Vec<ActionBuf>,
    Vec<JarOpBuf>,
))
    requires
        super::contract::step_requires(s@),
        super::contract::state_ok(h, &s),
        super::contract::jar_requires(clazel_cookie::storage::exec::jar_view(jar@), now as int),
    ensures
        super::contract::step_ensures(
            h.http(),
            u.urls(),
            s@,
            input@,
            clazel_cookie::storage::exec::jar_view(jar@),
            now as int,
            out.0@,
            super::types::actions_view(out.1@),
            super::types::ops_view(out.2@),
        ),
        super::contract::step_requires(out.0@),
        super::contract::state_ok(h, &out.0),
        super::contract::ops_at(super::types::ops_view(out.2@), now as int),
{
    let ghost sv = s@;
    let ghost jv = clazel_cookie::storage::exec::jar_view(jar@);
    let url = s.url;
    let redirects = s.redirects;
    let phase = s.phase;
    let tainted = s.tainted;
    let none: Vec<JarOpBuf> = Vec::new();
    assert(super::types::ops_view(none@) =~= Seq::<JarOp>::empty());
    let out = match phase {
        PhaseBuf::Finished => {
            let a: Vec<ActionBuf> = Vec::new();
            assert(super::types::actions_view(a@) =~= Seq::<Action>::empty());
            (StateBuf { url, redirects, phase: PhaseBuf::Finished, tainted }, a, none)
        },
        PhaseBuf::Connecting => match input {
            InputBuf::Connected => {
                proof {
                    u.rules_are_psl();
                }
                let op = retrieval_op_exec(u, &url, tainted, now, Ghost(sv));
                let ops = vec![op];
                assert(super::types::ops_view(ops@) =~= seq![retrieval_op(u.urls(), sv, now as int)]);
                match request_bytes(&url) {
                    Some(plain) => {
                        // The cookie-string, from a copy of the jar (the
                        // retrieval's step 5 is the operation, applied by the
                        // caller).
                        let url_rec = u.request_url(&url);
                        let ctx = request_context_exec(u, &url, tainted, Ghost(sv));
                        let mut copy = copy_jar(jar);
                        let cookie = retrieve_a_cookie_string_exec(&mut copy, &url_rec, &ctx, now);
                        let bytes = match request_bytes_cookie(&url, cookie.as_slice()) {
                            Some(b) => b,
                            None => plain,
                        };
                        let a = vec![ActionBuf::Send(bytes)];
                        assert(super::types::actions_view(a@) =~= super::spec::step(h.http(), u.urls(), sv, input@, jv, now as int).1);
                        (StateBuf { url, redirects, phase: PhaseBuf::Reading { parser: h.new_parser() }, tainted }, a, ops)
                    },
                    None => fail_exec(StateBuf { url, redirects, phase: PhaseBuf::Finished, tainted }, Reason::NotFetched, true, ops, Ghost(sv)),
                }
            },
            InputBuf::Bytes(_) => fail_exec(StateBuf { url, redirects, phase: PhaseBuf::Finished, tainted }, Reason::Shell, true, none, Ghost(sv)),
            InputBuf::Closed => fail_exec(StateBuf { url, redirects, phase: PhaseBuf::Finished, tainted }, Reason::Network, false, none, Ghost(sv)),
            InputBuf::Error => fail_exec(StateBuf { url, redirects, phase: PhaseBuf::Finished, tainted }, Reason::Network, false, none, Ghost(sv)),
        },
        PhaseBuf::Reading { parser } => step_reading(
            h,
            u,
            StateBuf { url, redirects, phase: PhaseBuf::Finished, tainted },
            parser,
            input,
            now,
            Ghost(sv),
        ),
    };
    proof {
        // In the reading phase, `step_reading`'s ensures for this jar.
        assert(super::contract::step_ensures(h.http(), u.urls(), sv, input@, jv, now as int, out.0@, super::types::actions_view(out.1@), super::types::ops_view(out.2@)));
        super::theorems::theorem_ops_name_request(h.http(), u.urls(), sv, input@, jv, now as int);
        let ops = super::types::ops_view(out.2@);
        assert forall|k: int| 0 <= k < ops.len() implies super::contract::op_now(#[trigger] ops[k]) == now as int by {
            match ops[k] {
                JarOp::Retrieved { .. } => {},
                JarOp::Stored { .. } => {},
            }
        }
    }
    out
}

/// `apply_ops`, executable: the jar after each of `ops`, in order (RFC 6265bis
/// §5.8.3 step 5 for a `Retrieved`, §5.7 for a `Stored`).
pub fn apply_ops_exec(jar: Vec<CookieRecord>, ops: &[JarOpBuf]) -> (out: Vec<CookieRecord>)
    requires
        super::contract::apply_ops_requires(clazel_cookie::storage::exec::jar_view(jar@), super::types::ops_view(ops@)),
    ensures
        super::contract::apply_ops_ensures(clazel_cookie::storage::exec::jar_view(jar@), super::types::ops_view(ops@), clazel_cookie::storage::exec::jar_view(out@)),
        clazel_cookie::storage::contract::jar_in_range(clazel_cookie::storage::exec::jar_view(out@)),
{
    let ghost rules = clazel_psl::table::psl_rules();
    let ghost ov = super::types::ops_view(ops@);
    let ghost jar0 = clazel_cookie::storage::exec::jar_view(jar@);
    let mut cur = jar;
    let mut i: usize = 0;
    assert(ov.skip(0) =~= ov);
    while i < ops.len()
        invariant
            i <= ops.len(),
            ov == super::types::ops_view(ops@),
            rules == clazel_psl::table::psl_rules(),
            forall|k: int| 0 <= k < ov.len() ==> clazel_cookie::set_cookie::contract::now_in_range(super::contract::op_now(#[trigger] ov[k])),
            clazel_cookie::storage::contract::jar_in_range(clazel_cookie::storage::exec::jar_view(cur@)),
            apply_ops(rules, clazel_cookie::storage::exec::jar_view(cur@), ov.skip(i as int)) == apply_ops(rules, jar0, ov),
        decreases ops.len() - i,
    {
        let ghost before = clazel_cookie::storage::exec::jar_view(cur@);
        proof {
            assert(ov[i as int] == ops@[i as int]@);
            assert(ov.skip(i as int).drop_first() =~= ov.skip(i as int + 1));
            assert(ov.skip(i as int)[0] == ov[i as int]);
            assert(clazel_cookie::set_cookie::contract::now_in_range(super::contract::op_now(ov[i as int])));
        }
        if let Some(op) = ops.get(i) {
            match op {
                JarOpBuf::Retrieved { url, ctx, now } => {
                    let _ = retrieve_a_cookie_string_exec(&mut cur, url, ctx, *now);
                },
                JarOpBuf::Stored { line, url, ctx, now } => {
                    cur = store_a_set_cookie_string_exec(cur.as_slice(), line.as_slice(), url, ctx, *now);
                },
            }
            proof {
                clazel_cookie::storage::exec::lemma_jar_view_in_range(cur@);
                assert(clazel_cookie::storage::exec::jar_view(cur@) == apply_op(rules, before, ov[i as int]));
            }
        }
        // Never saturates: i < ops.len().
        i = i.saturating_add(1);
    }
    assert(ov.skip(ops.len() as int) =~= Seq::<JarOp>::empty());
    cur
}

} // verus!
