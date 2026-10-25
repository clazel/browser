//! The executable transducer, proven to meet [`super::contract`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::contract::{HttpFnsExec, UrlFnsExec};
use super::types::{ActionBuf, InputBuf, LocationBuf, PhaseBuf, SettledBuf, StateBuf};
use crate::request::build::{connect_to, is_interim, request_bytes};
use clazel_http::field::section::field_values_named;
use clazel_http::message::body::ResponseParser;
use clazel_http::message::types::{ParseBuf, ResponseBuf};
use clazel_url::url::record::{ParsedUrl, clone_opt_str, clone_url, eq_str};

verus! {

/// `begin`: ask for the connection for `url`, or fail.
fn begin_exec(url: ParsedUrl, redirects: u8) -> (out: (StateBuf, Vec<ActionBuf>))
    ensures
        (out.0@, super::types::actions_view(out.1@)) == begin(url@, redirects as nat),
        !(out.0.phase is Reading),
{
    match (connect_to(&url), request_bytes(&url)) {
        (Some((host, port)), Some(_)) => {
            let a = vec![ActionBuf::Connect { host, port, tls: false }];
            assert(super::types::actions_view(a@) =~= begin(url@, redirects as nat).1);
            (StateBuf { url, redirects, phase: PhaseBuf::Connecting }, a)
        },
        _ => {
            let a = vec![ActionBuf::Fail(Reason::NotFetched)];
            assert(super::types::actions_view(a@) =~= begin(url@, redirects as nat).1);
            (StateBuf { url, redirects, phase: PhaseBuf::Finished }, a)
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
    begin_exec(clone_url(url), 0)
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

/// `fail` for a state whose URL is `url`.
fn fail_exec(url: ParsedUrl, redirects: u8, reason: Reason, open: bool, Ghost(s): Ghost<State>) -> (out: (StateBuf, Vec<ActionBuf>))
    requires
        s.url == url@,
        s.redirects == redirects as nat,
    ensures
        (out.0@, super::types::actions_view(out.1@)) == fail(s, reason, open),
        out.0@.redirects == s.redirects,
        !(out.0.phase is Reading),
{
    let last = vec![ActionBuf::Fail(reason)];
    assert(super::types::actions_view(last@) =~= seq![Action::Fail(reason)]);
    (StateBuf { url, redirects, phase: PhaseBuf::Finished }, after_close(open, last))
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

/// `on_final` (Fetch §4.5) for a state whose URL is `url`.
fn on_final_exec<U: UrlFnsExec>(u: &U, url: ParsedUrl, redirects: u8, response: ResponseBuf, open: bool, Ghost(s): Ghost<State>) -> (out: (StateBuf, Vec<ActionBuf>))
    requires
        s.url == url@,
        s.redirects == redirects as nat,
        s.redirects <= max_redirects(),
    ensures
        (out.0@, super::types::actions_view(out.1@)) == on_final(u.urls(), s, response@, open),
        out.0@.redirects <= max_redirects(),
        !(out.0.phase is Reading),
{
    // 3.
    match location_url_exec(u, &response, &url) {
        // 4.
        LocationBuf::Null => {
            let last = vec![ActionBuf::Done { url: Box::new(clone_url(&url)), response: Box::new(response) }];
            assert(super::types::actions_view(last@) =~= seq![Action::Done { url: s.url, response: response@ }]);
            (StateBuf { url, redirects, phase: PhaseBuf::Finished }, after_close(open, last))
        },
        // 5.
        LocationBuf::Failure => fail_exec(url, redirects, Reason::RedirectLocation, open, Ghost(s)),
        LocationBuf::Url(location) => {
            proof {
                assert(seq![0x68u32, 0x74, 0x74, 0x70] =~= clazel_url::url::spec::http_str());
                assert(seq![0x68u32, 0x74, 0x74, 0x70, 0x73] =~= clazel_url::url::spec::https_str());
            }
            let http_s = eq_str(location.scheme.as_slice(), &[0x68, 0x74, 0x74, 0x70])
                || eq_str(location.scheme.as_slice(), &[0x68, 0x74, 0x74, 0x70, 0x73]);
            if !http_s {
                // 6.
                fail_exec(url, redirects, Reason::RedirectScheme, open, Ghost(s))
            } else if redirects >= 20 {
                // 7.
                fail_exec(url, redirects, Reason::RedirectLimit, open, Ghost(s))
            } else {
                // 8., 18., 22.
                // Never saturates: redirects < 20.
                let next = begin_exec(location, redirects.saturating_add(1));
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

/// `step` while reading the response into `parser`.
fn step_reading<H: HttpFnsExec, U: UrlFnsExec>(h: &H, u: &U, url: ParsedUrl, redirects: u8, parser: ResponseParser, input: &InputBuf, Ghost(s): Ghost<State>) -> (out: (StateBuf, Vec<ActionBuf>))
    requires
        s.url == url@,
        s.redirects == redirects as nat,
        s.redirects <= max_redirects(),
        s.phase == (Phase::Reading { received: parser.received() }),
        h.parser_ok(&parser),
    ensures
        super::contract::step_ensures(h.http(), u.urls(), s, input@, out.0@, super::types::actions_view(out.1@)),
        out.0@.redirects <= max_redirects(),
        super::contract::state_ok(h, &out.0),
{
    match input {
        InputBuf::Connected => fail_exec(url, redirects, Reason::Shell, true, Ghost(s)),
        InputBuf::Bytes(bytes) => {
            let mut parser = parser;
            let first = h.feed(&mut parser, bytes.as_slice());
            match settle_exec(h, parser, first) {
                SettledBuf::Wait(rest) => {
                    let a: Vec<ActionBuf> = Vec::new();
                    assert(super::types::actions_view(a@) =~= Seq::<Action>::empty());
                    (StateBuf { url, redirects, phase: PhaseBuf::Reading { parser: rest } }, a)
                },
                SettledBuf::Final(response) => on_final_exec(u, url, redirects, response, true, Ghost(s)),
                SettledBuf::Bad(reason) => fail_exec(url, redirects, reason, true, Ghost(s)),
            }
        },
        InputBuf::Closed => match settle_at_close_exec(h, parser) {
            SettledBuf::Final(response) => on_final_exec(u, url, redirects, response, false, Ghost(s)),
            SettledBuf::Bad(reason) => fail_exec(url, redirects, reason, false, Ghost(s)),
            SettledBuf::Wait(_) => fail_exec(url, redirects, Reason::Incomplete, false, Ghost(s)),
        },
        InputBuf::Error => fail_exec(url, redirects, Reason::Network, true, Ghost(s)),
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
    match phase {
        PhaseBuf::Finished => {
            let a: Vec<ActionBuf> = Vec::new();
            assert(super::types::actions_view(a@) =~= Seq::<Action>::empty());
            (StateBuf { url, redirects, phase: PhaseBuf::Finished }, a)
        },
        PhaseBuf::Connecting => match input {
            InputBuf::Connected => match request_bytes(&url) {
                Some(bytes) => {
                    let a = vec![ActionBuf::Send(bytes)];
                    assert(super::types::actions_view(a@) =~= super::spec::step(h.http(), u.urls(), sv, input@).1);
                    (StateBuf { url, redirects, phase: PhaseBuf::Reading { parser: h.new_parser() } }, a)
                },
                None => fail_exec(url, redirects, Reason::NotFetched, true, Ghost(sv)),
            },
            InputBuf::Bytes(_) => fail_exec(url, redirects, Reason::Shell, true, Ghost(sv)),
            InputBuf::Closed => fail_exec(url, redirects, Reason::Network, false, Ghost(sv)),
            InputBuf::Error => fail_exec(url, redirects, Reason::Network, false, Ghost(sv)),
        },
        PhaseBuf::Reading { parser } => step_reading(h, u, url, redirects, parser, input, Ghost(sv)),
    }
}

} // verus!
