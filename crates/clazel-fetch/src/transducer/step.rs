//! The executable transducer, proven to meet [`super::contract`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::contract::{HttpFnsExec, UrlFnsExec};
use super::types::{ActionBuf, InputBuf, LocationBuf, PhaseBuf, SettledBuf, StateBuf};
use crate::request::build::{connect_to, is_interim, request_bytes, request_bytes_cookie};
use clazel_cookie::storage::exec::{
    CookieRecord, HttpRequestRecord, RequestContextRecord, RequestUrlRecord,
    retrieve_a_cookie_string_exec, store_a_set_cookie_string_exec,
};
use clazel_origin::exec::{ParsedOrigin, same_site_exec};
use clazel_http::field::section::field_values_named;
use clazel_http::message::body::ResponseParser;
use clazel_http::message::types::{ParseBuf, ResponseBuf};
use clazel_url::url::record::{ParsedUrl, clone_opt_str, clone_url, eq_str};

verus! {

/// `begin`: ask for the connection for `url`, or fail.
fn begin_exec(url: ParsedUrl, redirects: u8, jar: Vec<CookieRecord>, now: u64, tainted: bool) -> (out: (StateBuf, Vec<ActionBuf>))
    ensures
        (out.0@, super::types::actions_view(out.1@)) == begin(url@, redirects as nat, clazel_cookie::storage::exec::jar_view(jar@), now as int, tainted),
        !(out.0.phase is Reading),
{
    match (connect_to(&url), request_bytes(&url)) {
        (Some((host, port)), Some(_)) => {
            let a = vec![ActionBuf::Connect { host, port, tls: false }];
            assert(super::types::actions_view(a@) =~= begin(url@, redirects as nat, clazel_cookie::storage::exec::jar_view(jar@), now as int, tainted).1);
            (StateBuf { url, redirects, phase: PhaseBuf::Connecting, jar, now, tainted }, a)
        },
        _ => {
            let a = vec![ActionBuf::Fail(Reason::NotFetched)];
            assert(super::types::actions_view(a@) =~= begin(url@, redirects as nat, clazel_cookie::storage::exec::jar_view(jar@), now as int, tainted).1);
            (StateBuf { url, redirects, phase: PhaseBuf::Finished, jar, now, tainted }, a)
        },
    }
}

/// `start`: the first state and actions of a fetch of `url` with the jar
/// `jar` at time `now`.
pub fn start(url: &ParsedUrl, jar: Vec<CookieRecord>, now: u64) -> (out: (StateBuf, Vec<ActionBuf>))
    requires
        super::contract::start_requires(now as int),
    ensures
        super::contract::start_ensures(url@, clazel_cookie::storage::exec::jar_view(jar@), now as int, out.0@, super::types::actions_view(out.1@)),
        super::contract::step_requires(out.0@),
        !(out.0.phase is Reading),
{
    proof {
        clazel_cookie::storage::exec::lemma_jar_view_in_range(jar@);
    }
    begin_exec(clone_url(url), 0, jar, now, false)
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

/// `fail` for a state `s`, given as `base`, which is [`finished`] of it.
fn fail_exec(base: StateBuf, reason: Reason, open: bool, Ghost(s): Ghost<State>) -> (out: (StateBuf, Vec<ActionBuf>))
    requires
        base@ == finished(s),
    ensures
        (out.0@, super::types::actions_view(out.1@)) == fail(s, reason, open),
        out.0@.redirects == s.redirects,
        !(out.0.phase is Reading),
{
    let last = vec![ActionBuf::Fail(reason)];
    assert(super::types::actions_view(last@) =~= seq![Action::Fail(reason)]);
    (base, after_close(open, last))
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

/// `store_lines`: each of `lines` stored in order (Fetch §3.1.2 step 6).
fn store_all_exec(jar: Vec<CookieRecord>, lines: &[Vec<u8>], url: &RequestUrlRecord, ctx: &RequestContextRecord, now: u64) -> (out: Vec<CookieRecord>)
    requires
        clazel_cookie::set_cookie::contract::now_in_range(now as int),
    ensures
        clazel_cookie::storage::exec::jar_view(out@) == store_lines(clazel_psl::table::psl_rules(), clazel_cookie::storage::exec::jar_view(jar@), clazel_http::field::types::strings_view(lines@), url@, ctx@, now as int),
{
    let ghost rules = clazel_psl::table::psl_rules();
    let ghost ls = clazel_http::field::types::strings_view(lines@);
    let ghost jar0 = clazel_cookie::storage::exec::jar_view(jar@);
    let mut cur = jar;
    let mut i: usize = 0;
    assert(ls.skip(0) =~= ls);
    while i < lines.len()
        invariant
            i <= lines.len(),
            ls == clazel_http::field::types::strings_view(lines@),
            rules == clazel_psl::table::psl_rules(),
            clazel_cookie::set_cookie::contract::now_in_range(now as int),
            store_lines(rules, clazel_cookie::storage::exec::jar_view(cur@), ls.skip(i as int), url@, ctx@, now as int) == store_lines(rules, jar0, ls, url@, ctx@, now as int),
        decreases lines.len() - i,
    {
        if let Some(line) = lines.get(i) {
            proof {
                clazel_cookie::storage::exec::lemma_jar_view_in_range(cur@);
                assert(ls[i as int] == line@);
                assert(ls.skip(i as int).drop_first() =~= ls.skip(i as int + 1));
            }
            cur = store_a_set_cookie_string_exec(cur.as_slice(), line.as_slice(), url, ctx, now);
        }
        // Never saturates: i < lines.len().
        i = i.saturating_add(1);
    }
    assert(ls.skip(lines.len() as int) =~= Seq::<Seq<u8>>::empty());
    cur
}

/// `on_final` (Fetch §4.5) for a state `s0`, given as `base`, which is
/// [`finished`] of it.
fn on_final_exec<U: UrlFnsExec>(u: &U, base: StateBuf, response: ResponseBuf, open: bool, Ghost(s0): Ghost<State>) -> (out: (StateBuf, Vec<ActionBuf>))
    requires
        base@ == finished(s0),
        s0.redirects <= max_redirects(),
        clazel_cookie::set_cookie::contract::now_in_range(s0.now),
    ensures
        (out.0@, super::types::actions_view(out.1@)) == on_final(u.urls(), s0, response@, open),
        out.0@.redirects <= max_redirects(),
        !(out.0.phase is Reading),
{
    let url = base.url;
    let redirects = base.redirects;
    let jar = base.jar;
    let now = base.now;
    let tainted = base.tainted;
    proof {
        u.rules_are_psl();
    }
    // Fetch §4.7 step 17: store the response's `Set-Cookie` lines.
    let url_rec = u.request_url(&url);
    let ctx = request_context_exec(u, &url, tainted, Ghost(s0));
    let lines = field_values_named(response.fields.as_slice(), &[0x53, 0x65, 0x74, 0x2D, 0x43, 0x6F, 0x6F, 0x6B, 0x69, 0x65]);
    proof {
        assert(seq![0x53u8, 0x65, 0x74, 0x2D, 0x43, 0x6F, 0x6F, 0x6B, 0x69, 0x65] =~= lit_set_cookie());
    }
    let jar = store_all_exec(jar, lines.as_slice(), &url_rec, &ctx, now);
    let ghost s = State { jar: clazel_cookie::storage::exec::jar_view(jar@), ..s0 };
    proof {
        assert(clazel_cookie::storage::exec::jar_view(jar@) == store_response(u.urls(), s0, response@));
    }
    // 3.
    match location_url_exec(u, &response, &url) {
        // 4.
        LocationBuf::Null => {
            let last = vec![ActionBuf::Done { url: Box::new(clone_url(&url)), response: Box::new(response) }];
            assert(super::types::actions_view(last@) =~= seq![Action::Done { url: s.url, response: response@ }]);
            (StateBuf { url, redirects, phase: PhaseBuf::Finished, jar, now, tainted }, after_close(open, last))
        },
        // 5.
        LocationBuf::Failure => fail_exec(StateBuf { url, redirects, phase: PhaseBuf::Finished, jar, now, tainted }, Reason::RedirectLocation, open, Ghost(s)),
        LocationBuf::Url(location) => {
            proof {
                assert(seq![0x68u32, 0x74, 0x74, 0x70] =~= clazel_url::url::spec::http_str());
                assert(seq![0x68u32, 0x74, 0x74, 0x70, 0x73] =~= clazel_url::url::spec::https_str());
            }
            let http_s = eq_str(location.scheme.as_slice(), &[0x68, 0x74, 0x74, 0x70])
                || eq_str(location.scheme.as_slice(), &[0x68, 0x74, 0x74, 0x70, 0x73]);
            if !http_s {
                // 6.
                fail_exec(StateBuf { url, redirects, phase: PhaseBuf::Finished, jar, now, tainted }, Reason::RedirectScheme, open, Ghost(s))
            } else if redirects >= 20 {
                // 7.
                fail_exec(StateBuf { url, redirects, phase: PhaseBuf::Finished, jar, now, tainted }, Reason::RedirectLimit, open, Ghost(s))
            } else {
                // 8., 18., 22. and the redirect-taint.
                let from = u.origin(&url);
                let to = u.origin(&location);
                let crossed = !same_site_exec(&from, &to);
                // Never saturates: redirects < 20.
                let next = begin_exec(location, redirects.saturating_add(1), jar, now, tainted || crossed);
                (next.0, after_close(open, next.1))
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
/// [`finished`], which every branch but the waiting one returns.
fn step_reading<H: HttpFnsExec, U: UrlFnsExec>(h: &H, u: &U, base: StateBuf, parser: ResponseParser, input: &InputBuf, Ghost(s): Ghost<State>) -> (out: (StateBuf, Vec<ActionBuf>))
    requires
        base@ == finished(s),
        s.redirects <= max_redirects(),
        clazel_cookie::set_cookie::contract::now_in_range(s.now),
        s.phase == (Phase::Reading { received: parser.received() }),
        h.parser_ok(&parser),
    ensures
        super::contract::step_ensures(h.http(), u.urls(), s, input@, out.0@, super::types::actions_view(out.1@)),
        out.0@.redirects <= max_redirects(),
        super::contract::state_ok(h, &out.0),
{
    match input {
        InputBuf::Connected => fail_exec(base, Reason::Shell, true, Ghost(s)),
        InputBuf::Bytes(bytes) => {
            let mut parser = parser;
            let first = h.feed(&mut parser, bytes.as_slice());
            match settle_exec(h, parser, first) {
                SettledBuf::Wait(rest) => {
                    let a: Vec<ActionBuf> = Vec::new();
                    assert(super::types::actions_view(a@) =~= Seq::<Action>::empty());
                    let url = base.url;
    let redirects = base.redirects;
    let jar = base.jar;
    let now = base.now;
    let tainted = base.tainted;
                    (StateBuf { url, redirects, phase: PhaseBuf::Reading { parser: rest }, jar, now, tainted }, a)
                },
                SettledBuf::Final(response) => on_final_exec(u, base, response, true, Ghost(s)),
                SettledBuf::Bad(reason) => fail_exec(base, reason, true, Ghost(s)),
            }
        },
        InputBuf::Closed => match settle_at_close_exec(h, parser) {
            SettledBuf::Final(response) => on_final_exec(u, base, response, false, Ghost(s)),
            SettledBuf::Bad(reason) => fail_exec(base, reason, false, Ghost(s)),
            SettledBuf::Wait(_) => fail_exec(base, Reason::Incomplete, false, Ghost(s)),
        },
        InputBuf::Error => fail_exec(base, Reason::Network, true, Ghost(s)),
    }
}

/// `step`: the next state and actions after `input`.
pub fn step<H: HttpFnsExec, U: UrlFnsExec>(h: &H, u: &U, s: StateBuf, input: &InputBuf) -> (out: (StateBuf, Vec<ActionBuf>))
    requires
        super::contract::step_requires(s@),
        super::contract::state_ok(h, &s),
    ensures
        super::contract::step_ensures(h.http(), u.urls(), s@, input@, out.0@, super::types::actions_view(out.1@)),
        super::contract::step_requires(out.0@),
        super::contract::state_ok(h, &out.0),
{
    let ghost sv = s@;
    let url = s.url;
    let redirects = s.redirects;
    let phase = s.phase;
    let jar = s.jar;
    let now = s.now;
    let tainted = s.tainted;
    let out = match phase {
        PhaseBuf::Finished => {
            let a: Vec<ActionBuf> = Vec::new();
            assert(super::types::actions_view(a@) =~= Seq::<Action>::empty());
            (StateBuf { url, redirects, phase: PhaseBuf::Finished, jar, now, tainted }, a)
        },
        PhaseBuf::Connecting => match input {
            InputBuf::Connected => {
                proof {
                    clazel_cookie::storage::exec::lemma_jar_view_in_range(jar@);
                    u.rules_are_psl();
                }
                let url_rec = u.request_url(&url);
                let ctx = request_context_exec(u, &url, tainted, Ghost(sv));
                let mut jar = jar;
                let cookie = retrieve_a_cookie_string_exec(&mut jar, &url_rec, &ctx, now);
                match request_bytes_cookie(&url, cookie.as_slice()) {
                    Some(bytes) => {
                        let a = vec![ActionBuf::Send(bytes)];
                        assert(super::types::actions_view(a@) =~= super::spec::step(h.http(), u.urls(), sv, input@).1);
                        (StateBuf { url, redirects, phase: PhaseBuf::Reading { parser: h.new_parser() }, jar, now, tainted }, a)
                    },
                    None => fail_exec(
                        StateBuf { url, redirects, phase: PhaseBuf::Finished, jar, now, tainted },
                        Reason::NotFetched,
                        true,
                        Ghost(State { jar: jar_after_cookie_string(u.urls(), sv), ..sv }),
                    ),
                }
            },
            InputBuf::Bytes(_) => fail_exec(StateBuf { url, redirects, phase: PhaseBuf::Finished, jar, now, tainted }, Reason::Shell, true, Ghost(sv)),
            InputBuf::Closed => fail_exec(StateBuf { url, redirects, phase: PhaseBuf::Finished, jar, now, tainted }, Reason::Network, false, Ghost(sv)),
            InputBuf::Error => fail_exec(StateBuf { url, redirects, phase: PhaseBuf::Finished, jar, now, tainted }, Reason::Network, false, Ghost(sv)),
        },
        PhaseBuf::Reading { parser } => step_reading(h, u, StateBuf { url, redirects, phase: PhaseBuf::Finished, jar, now, tainted }, parser, input, Ghost(sv)),
    };
    proof {
        super::theorems::theorem_jar_frame(h.http(), u.urls(), sv, input@);
        clazel_cookie::storage::exec::lemma_jar_view_in_range(out.0.jar@);
    }
    out
}

} // verus!
