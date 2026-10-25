//! The executable transducer, proven to meet [`super::contract`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::contract::HttpFnsExec;
use super::types::{ActionBuf, InputBuf, PhaseBuf, SettledBuf, StateBuf};
use crate::request::build::{connect_to, is_interim, request_bytes};
use clazel_http::field::string::append;
use clazel_http::message::types::{ParseBuf, ResponseBuf};
use clazel_url::url::record::{ParsedUrl, clone_url};

verus! {

/// `begin`: ask for the connection for `url`, or fail.
fn begin_exec(url: ParsedUrl) -> (out: (StateBuf, Vec<ActionBuf>))
    ensures
        (out.0@, super::types::actions_view(out.1@)) == begin(url@),
{
    match (connect_to(&url), request_bytes(&url)) {
        (Some((host, port)), Some(_)) => {
            let a = vec![ActionBuf::Connect { host, port, tls: false }];
            assert(super::types::actions_view(a@) =~= begin(url@).1);
            (StateBuf { url, phase: PhaseBuf::Connecting }, a)
        },
        _ => {
            let a = vec![ActionBuf::Fail(Reason::NotFetched)];
            assert(super::types::actions_view(a@) =~= begin(url@).1);
            (StateBuf { url, phase: PhaseBuf::Finished }, a)
        },
    }
}

/// `start`: the first state and actions of a fetch of `url`.
pub fn start(url: &ParsedUrl) -> (out: (StateBuf, Vec<ActionBuf>))
    ensures
        super::contract::start_ensures(url@, out.0@, super::types::actions_view(out.1@)),
{
    begin_exec(clone_url(url))
}

/// `close_if(open)` followed by `last`.
fn closing(open: bool, last: ActionBuf) -> (out: Vec<ActionBuf>)
    ensures
        super::types::actions_view(out@) == close_if(open) + seq![last@],
{
    let mut a: Vec<ActionBuf> = Vec::new();
    if open {
        a.push(ActionBuf::Close);
    }
    a.push(last);
    assert(super::types::actions_view(a@) =~= close_if(open) + seq![last@]);
    a
}

/// `fail` for a state whose URL is `url`.
fn fail_exec(url: ParsedUrl, reason: Reason, open: bool, Ghost(s): Ghost<State>) -> (out: (StateBuf, Vec<ActionBuf>))
    requires
        s.url == url@,
    ensures
        (out.0@, super::types::actions_view(out.1@)) == fail(s, reason, open),
{
    (StateBuf { url, phase: PhaseBuf::Finished }, closing(open, ActionBuf::Fail(reason)))
}

/// `on_final` for a state whose URL is `url`.
fn on_final_exec(url: ParsedUrl, response: ResponseBuf, open: bool, Ghost(s): Ghost<State>) -> (out: (StateBuf, Vec<ActionBuf>))
    requires
        s.url == url@,
    ensures
        (out.0@, super::types::actions_view(out.1@)) == on_final(s, response@, open),
{
    let done = ActionBuf::Done { url: Box::new(clone_url(&url)), response: Box::new(response) };
    (StateBuf { url, phase: PhaseBuf::Finished }, closing(open, done))
}

/// `settle`: skip complete interim responses at the start of `received`.
fn settle_exec<H: HttpFnsExec>(h: &H, received: Vec<u8>) -> (out: SettledBuf)
    ensures
        out@ == settle(h.http(), received@),
{
    let mut cur = received;
    loop
        invariant
            settle(h.http(), cur@) == settle(h.http(), received@),
        decreases cur@.len(),
    {
        match h.parse(cur.as_slice()) {
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
                    if rest.len() < cur.len() {
                        cur = rest;
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

/// `settle_at_close`.
fn settle_at_close_exec<H: HttpFnsExec>(h: &H, received: &[u8]) -> (out: SettledBuf)
    ensures
        out@ == settle_at_close(h.http(), received@),
{
    match h.parse_at_close(received) {
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

/// `step`: the next state and actions after `input`.
pub fn step<H: HttpFnsExec>(h: &H, s: StateBuf, input: &InputBuf) -> (out: (StateBuf, Vec<ActionBuf>))
    ensures
        super::contract::step_ensures(h.http(), s@, input@, out.0@, super::types::actions_view(out.1@)),
{
    let ghost sv = s@;
    let url = s.url;
    let phase = s.phase;
    match phase {
        PhaseBuf::Finished => {
            let a: Vec<ActionBuf> = Vec::new();
            assert(super::types::actions_view(a@) =~= Seq::<Action>::empty());
            (StateBuf { url, phase: PhaseBuf::Finished }, a)
        },
        PhaseBuf::Connecting => match input {
            InputBuf::Connected => match request_bytes(&url) {
                Some(bytes) => {
                    let a = vec![ActionBuf::Send(bytes)];
                    assert(super::types::actions_view(a@) =~= super::spec::step(h.http(), sv, input@).1);
                    (StateBuf { url, phase: PhaseBuf::Reading { received: Vec::new() } }, a)
                },
                None => fail_exec(url, Reason::NotFetched, true, Ghost(sv)),
            },
            InputBuf::Bytes(_) => fail_exec(url, Reason::Shell, true, Ghost(sv)),
            InputBuf::Closed => fail_exec(url, Reason::Network, false, Ghost(sv)),
            InputBuf::Error => fail_exec(url, Reason::Network, false, Ghost(sv)),
        },
        PhaseBuf::Reading { received } => match input {
            InputBuf::Connected => fail_exec(url, Reason::Shell, true, Ghost(sv)),
            InputBuf::Bytes(bytes) => {
                let mut all = received;
                append(&mut all, bytes.as_slice());
                match settle_exec(h, all) {
                    SettledBuf::Wait(rest) => {
                        let a: Vec<ActionBuf> = Vec::new();
                        assert(super::types::actions_view(a@) =~= Seq::<Action>::empty());
                        (StateBuf { url, phase: PhaseBuf::Reading { received: rest } }, a)
                    },
                    SettledBuf::Final(response) => on_final_exec(url, response, true, Ghost(sv)),
                    SettledBuf::Bad(reason) => fail_exec(url, reason, true, Ghost(sv)),
                }
            },
            InputBuf::Closed => match settle_at_close_exec(h, received.as_slice()) {
                SettledBuf::Final(response) => on_final_exec(url, response, false, Ghost(sv)),
                SettledBuf::Bad(reason) => fail_exec(url, reason, false, Ghost(sv)),
                SettledBuf::Wait(_) => fail_exec(url, Reason::Incomplete, false, Ghost(sv)),
            },
            InputBuf::Error => fail_exec(url, Reason::Network, true, Ghost(sv)),
        },
    }
}

} // verus!
