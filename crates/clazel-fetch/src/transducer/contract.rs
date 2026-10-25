//! Contracts the executable transducer must be proven to meet, and the
//! theorems about the spec, stated as predicates (proven in `theorems.rs`
//! for every [`HttpFns`]).
//!
//! The exec functions (in `step.rs`) take the HTTP and URL functions as
//! values of types implementing [`HttpFnsExec`] and [`UrlFnsExec`], whose
//! methods are each proven equal to the spec function of the same name, so
//! the proofs hold for any implementation; `real.rs` gives the one the
//! shell runs. The exec state's invariant beyond its view is
//! [`state_ok`]: `start` gives it and `step` requires and keeps it.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use clazel_http::message::body::ResponseParser;
use clazel_http::message::types::ParseBuf;
use clazel_url::url::record::ParsedUrl;

verus! {

/// The HTTP functions, executable: each answer is the spec function's of
/// [`HttpFnsExec::http`]. The octets of a connection go into a
/// [`ResponseParser`] as they arrive, each given once, so a fetch is
/// linear in the response's size; [`HttpFnsExec::parser_ok`] is the
/// invariant such a parser keeps.
pub trait HttpFnsExec {
    /// The spec the methods implement.
    spec fn http(&self) -> HttpFns;

    /// What a parser of these functions keeps between octets.
    spec fn parser_ok(&self, p: &ResponseParser) -> bool;

    /// A parser that has received nothing.
    fn new_parser(&self) -> (p: ResponseParser)
        ensures
            self.parser_ok(&p),
            p.received() == Seq::<u8>::empty(),
    ;

    /// `bytes` appended to what `p` received, and [`HttpFns::parse`] of
    /// all of it.
    fn feed(&self, p: &mut ResponseParser, bytes: &[u8]) -> (r: ParseBuf)
        requires
            self.parser_ok(old(p)),
        ensures
            self.parser_ok(final(p)),
            final(p).received() == old(p).received() + bytes@,
            r@ == (self.http().parse)(final(p).received()),
    ;

    /// [`HttpFns::parse_at_close`] of all that `p` received.
    fn parse_at_close(&self, p: ResponseParser) -> (r: ParseBuf)
        requires
            self.parser_ok(&p),
        ensures
            r@ == (self.http().parse_at_close)(p.received()),
    ;
}

/// The executable state's invariant for `h`: a parser being read into
/// keeps [`HttpFnsExec::parser_ok`]. A state that is not reading (as every
/// one [`start`] gives) has it for every `h`.
pub open spec fn state_ok<H: HttpFnsExec>(h: &H, s: &super::types::StateBuf) -> bool {
    match s.phase {
        super::types::PhaseBuf::Reading { parser } => h.parser_ok(&parser),
        _ => true,
    }
}

/// The URL functions, executable.
pub trait UrlFnsExec {
    /// The spec the method implements.
    spec fn urls(&self) -> UrlFns;

    /// [`UrlFns::location`]: `value` parsed with `base` as its base URL.
    fn location(&self, base: &ParsedUrl, value: &[u8]) -> (r: Option<ParsedUrl>)
        ensures
            clazel_url::url::record::opt_url_view(r) == (self.urls().location)(base@, value@),
    ;
}

/// Contract for `start(&ParsedUrl) -> (StateBuf, Vec<ActionBuf>)`.
pub open spec fn start_ensures(url: Url, state: State, actions: Seq<Action>) -> bool {
    (state, actions) == start(url)
}

/// Precondition of `step`: the redirect count is at most
/// [`max_redirects`], as in every state [`start`] and `step` give
/// ([`redirects_bounded`]); `step` ensures it of its result. (The exec
/// count is a `u8`.)
pub open spec fn step_requires(s: State) -> bool {
    s.redirects <= max_redirects()
}

/// Contract for `step<H: HttpFnsExec, U: UrlFnsExec>(&H, &U, StateBuf,
/// &InputBuf) -> (StateBuf, Vec<ActionBuf>)`, with `http` and `urls` their
/// specs.
pub open spec fn step_ensures(http: HttpFns, urls: UrlFns, s: State, input: Input, state: State, actions: Seq<Action>) -> bool {
    (state, actions) == step(http, urls, s, input)
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

/// The most requests one fetch makes: the first and 20 redirects (Fetch
/// §4.5 step 7). Written out, not computed from [`max_redirects`], so a
/// change to the limit shows here.
pub open spec fn max_requests() -> nat {
    21
}

/// Every action of a fetch of `url` given the inputs `inputs`.
pub open spec fn trace(http: HttpFns, urls: UrlFns, url: Url, inputs: Seq<Input>) -> Seq<Action> {
    start(url).1 + run(http, urls, start(url).0, inputs).1
}

/// Totality: whatever the shell reports, a fetch opens at most
/// [`max_requests`] connections and sends at most that many requests.
pub open spec fn requests_bounded(http: HttpFns, urls: UrlFns, url: Url, inputs: Seq<Input>) -> bool {
    count_sends(trace(http, urls, url, inputs)) <= max_requests()
        && count_connects(trace(http, urls, url, inputs)) <= max_requests()
}

/// The redirect count never passes 20 (Fetch §4.5 step 7), whatever the
/// input.
pub open spec fn redirects_bounded(http: HttpFns, urls: UrlFns, s: State, input: Input) -> bool {
    s.redirects <= 20 ==> step(http, urls, s, input).0.redirects <= 20
}

/// The current URL changes only by a redirect: to an HTTP(S) URL (Fetch
/// §4.5 step 6), with the redirect count one more (step 8).
pub open spec fn url_changes_only_by_redirect(http: HttpFns, urls: UrlFns, s: State, input: Input) -> bool {
    let next = step(http, urls, s, input).0;
    next.url == s.url && next.redirects == s.redirects
        || next.redirects == s.redirects + 1 && is_http_s_scheme(next.url.scheme)
}

/// Every `Send` is the request for the current URL.
pub open spec fn sends_are_requests(http: HttpFns, urls: UrlFns, s: State, input: Input) -> bool {
    forall|k: int| 0 <= k < step(http, urls, s, input).1.len() ==> match #[trigger] step(http, urls, s, input).1[k] {
        Action::Send(bytes) => crate::request::spec::request_bytes(s.url) == Some(bytes),
        _ => true,
    }
}

/// No action before the bytes decide: while reading, `Bytes` gives no
/// action exactly when the parser, on what remains after the interim
/// responses, has decided nothing (`Incomplete`).
pub open spec fn silent_until_decided(http: HttpFns, urls: UrlFns, s: State, bytes: Seq<u8>) -> bool {
    match s.phase {
        Phase::Reading { received } => (step(http, urls, s, Input::Bytes(bytes)).1.len() == 0) == (settle(http, received + bytes) is Wait)
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
/// `rest + more`; `clazel_http::message::lemmas::lemma_parse_response_append`
/// is exactly this, for `parse_response`.)
pub open spec fn prefix_stable(http: HttpFns) -> bool {
    forall|input: Seq<u8>, more: Seq<u8>| #![trigger (http.parse)(input), (http.parse)(input + more)] match (http.parse)(input) {
        clazel_http::message::spec::Parse::Done { response, rest } => (http.parse)(input + more)
            == (clazel_http::message::spec::Parse::Done { response: response, rest: rest + more }),
        clazel_http::message::spec::Parse::Invalid => (http.parse)(input + more) is Invalid,
        clazel_http::message::spec::Parse::Unsupported => (http.parse)(input + more) is Unsupported,
        clazel_http::message::spec::Parse::Incomplete => true,
    }
}

/// The shipped parser is [`prefix_stable`] (proven in `real.rs` from
/// `clazel_http::message::lemmas::lemma_parse_response_append`), so the
/// split theorem holds of the client the shell runs.
pub open spec fn real_prefix_stable() -> bool {
    prefix_stable(super::real::real_http())
}

/// The split does not matter: for a parser that is [`prefix_stable`], the
/// octets `a` then `b` give what `a + b` gives at once. If `a` already
/// decides, `a + b` decides the same (same state, same actions); if not,
/// `b` afterwards leads to the same state and actions as `a + b`. So no
/// action depends on how the bytes were cut, and none is taken on fewer
/// bytes than the decision needs.
pub open spec fn split_invariant(http: HttpFns, urls: UrlFns, s: State, a: Seq<u8>, b: Seq<u8>) -> bool {
    match s.phase {
        Phase::Reading { received: _ } => {
            let first = step(http, urls, s, Input::Bytes(a));
            let whole = step(http, urls, s, Input::Bytes(a + b));
            if first.1.len() == 0 {
                step(http, urls, first.0, Input::Bytes(b)) == whole
            } else {
                first == whole
            }
        },
        _ => true,
    }
}

} // verus!
