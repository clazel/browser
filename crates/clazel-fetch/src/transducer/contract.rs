//! Contracts the executable transducer must be proven to meet, and the
//! theorems about the spec, stated as predicates (proven in `theorems.rs`
//! for every [`HttpFns`]).
//!
//! The exec functions (in `step.rs`) take the HTTP functions as a value of
//! a type implementing [`HttpFnsExec`], whose methods are each proven equal
//! to the spec function of the same name, so the proofs hold for any
//! implementation; `real.rs` gives the one the shell runs.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use clazel_http::message::types::ParseBuf;

verus! {

/// The HTTP functions, executable: each method's result is the spec
/// function's of [`HttpFnsExec::http`].
pub trait HttpFnsExec {
    /// The spec the methods implement.
    spec fn http(&self) -> HttpFns;

    /// [`HttpFns::parse`] of all of `received`.
    fn parse(&self, received: &[u8]) -> (r: ParseBuf)
        ensures
            r@ == (self.http().parse)(received@),
    ;

    /// [`HttpFns::parse_at_close`] of all of `received`.
    fn parse_at_close(&self, received: &[u8]) -> (r: ParseBuf)
        ensures
            r@ == (self.http().parse_at_close)(received@),
    ;
}

/// Contract for `start(&ParsedUrl) -> (StateBuf, Vec<ActionBuf>)`.
pub open spec fn start_ensures(url: Url, state: State, actions: Seq<Action>) -> bool {
    (state, actions) == start(url)
}

/// Contract for `step<H: HttpFnsExec>(&H, StateBuf, &InputBuf) ->
/// (StateBuf, Vec<ActionBuf>)`, with `http` the `H`'s spec.
pub open spec fn step_ensures(http: HttpFns, s: State, input: Input, state: State, actions: Seq<Action>) -> bool {
    (state, actions) == step(http, s, input)
}

// ===========================================================================
// Theorems about the spec (statements; the proofs are in `theorems.rs`).
// ===========================================================================

/// How many `Send` actions `actions` has.
pub open spec fn count_sends(actions: Seq<Action>) -> nat
    decreases actions.len()
{
    if actions.len() == 0 {
        0
    } else {
        count_sends(actions.drop_last()) + if actions.last() is Send { 1nat } else { 0nat }
    }
}

/// How many `Connect` actions `actions` has.
pub open spec fn count_connects(actions: Seq<Action>) -> nat
    decreases actions.len()
{
    if actions.len() == 0 {
        0
    } else {
        count_connects(actions.drop_last()) + if actions.last() is Connect { 1nat } else { 0nat }
    }
}

/// The most requests one fetch makes.
pub open spec fn max_requests() -> nat {
    1
}

/// Every action of a fetch of `url` given the inputs `inputs`.
pub open spec fn trace(http: HttpFns, url: Url, inputs: Seq<Input>) -> Seq<Action> {
    start(url).1 + run(http, start(url).0, inputs).1
}

/// Totality: whatever the shell reports, a fetch opens at most
/// [`max_requests`] connections and sends at most that many requests.
pub open spec fn requests_bounded(http: HttpFns, url: Url, inputs: Seq<Input>) -> bool {
    count_sends(trace(http, url, inputs)) <= max_requests()
        && count_connects(trace(http, url, inputs)) <= max_requests()
}

/// Every `Send` is the request for the current URL.
pub open spec fn sends_are_requests(http: HttpFns, s: State, input: Input) -> bool {
    forall|k: int| 0 <= k < step(http, s, input).1.len() ==> match #[trigger] step(http, s, input).1[k] {
        Action::Send(bytes) => crate::request::spec::request_bytes(s.url) == Some(bytes),
        _ => true,
    }
}

/// No action before the bytes decide: while reading, `Bytes` gives no
/// action exactly when the parser, on what remains after the interim
/// responses, has decided nothing (`Incomplete`).
pub open spec fn silent_until_decided(http: HttpFns, s: State, bytes: Seq<u8>) -> bool {
    match s.phase {
        Phase::Reading { received } => (step(http, s, Input::Bytes(bytes)).1.len() == 0) == (settle(http, received + bytes) is Wait)
            && match settle(http, received + bytes) {
                Settled::Wait(rest) => (http.parse)(rest) is Incomplete,
                _ => true,
            },
        _ => true,
    }
}

/// What the split theorem needs of the parser: a decision, once made, is
/// the same decision on more bytes, and a finished response consumes the
/// same octets. (`clazel_http::message::contract::monotone` states nearly
/// this, but leaves the octets after the response free to be longer than
/// `rest + more`; neither is proven on `main` yet.)
pub open spec fn prefix_stable(http: HttpFns) -> bool {
    forall|input: Seq<u8>, more: Seq<u8>| #![trigger (http.parse)(input), (http.parse)(input + more)] match (http.parse)(input) {
        clazel_http::message::spec::Parse::Done { response, rest } => (http.parse)(input + more)
            == (clazel_http::message::spec::Parse::Done { response: response, rest: rest + more }),
        clazel_http::message::spec::Parse::Invalid => (http.parse)(input + more) is Invalid,
        clazel_http::message::spec::Parse::Unsupported => (http.parse)(input + more) is Unsupported,
        clazel_http::message::spec::Parse::Incomplete => true,
    }
}

/// The split does not matter: for a parser that is [`prefix_stable`], the
/// octets `a` then `b` give what `a + b` gives at once. If `a` already
/// decides, `a + b` decides the same (same state, same actions); if not,
/// `b` afterwards leads to the same state and actions as `a + b`. So no
/// action depends on how the bytes were cut, and none is taken on fewer
/// bytes than the decision needs.
pub open spec fn split_invariant(http: HttpFns, s: State, a: Seq<u8>, b: Seq<u8>) -> bool {
    match s.phase {
        Phase::Reading { received: _ } => {
            let first = step(http, s, Input::Bytes(a));
            let whole = step(http, s, Input::Bytes(a + b));
            if first.1.len() == 0 {
                step(http, first.0, Input::Bytes(b)) == whole
            } else {
                first == whole
            }
        },
        _ => true,
    }
}

} // verus!
