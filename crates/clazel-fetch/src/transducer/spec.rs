//! Executable-style specification of the client state machine (phase-3.md
//! item 3.6): a pure transducer from a URL and the events of the
//! connections it asks for to the actions the network shell carries out.
//! Nothing here runs.
//!
//! Sources (pinned; an RFC never changes after publication):
//! - RFC 9112 "HTTP/1.1", June 2022: §6.3 message body length (step 8:
//!   a body delimited by the connection closing), §9.6 tear-down;
//! - RFC 9110 "HTTP Semantics", June 2022: §15.2 informational (1xx)
//!   responses, §15.4 redirection (3xx), §10.2.2 `Location`;
//! - the Fetch Standard, Living Standard last updated 19 October 2026,
//!   commit `59afe349913d56898c947576216f1c2579308be7`: §2.2.3 "redirect
//!   status", §2.2.6 a response's "location URL", §4.5 "HTTP-redirect
//!   fetch" (steps 3 to 8, 18 and 22), §2.1 "HTTP(S) scheme";
//! - the request itself and [`crate::request::spec::is_interim`] are [`crate::request::spec`]'s.
//!
//! The protocol between the transducer and the shell: [`start`] gives the
//! first actions; the shell carries out each action in order and reports
//! what happened as an [`Input`], which [`step`] maps to the next state and
//! actions. `Connect` opens a connection (the shell reports `Connected`
//! or `Error`), `Send` writes bytes to it, `Close` closes it, and every
//! byte read from it arrives as `Bytes`, in order, until the server closes
//! it (`Closed`) or it fails (`Error`). `Done` and `Fail` end the fetch;
//! after them every input is ignored.
//!
//! Modelling choices (each a choice of ours or a deviation in form, never
//! in meaning):
//! - **The HTTP functions are parameters** ([`HttpFns`]): the response
//!   parser over everything received on the connection, while it is open
//!   and once the server has closed it. So no proof here unfolds the parser;
//!   `real` joins them to `clazel_http::message::spec::parse_response` and
//!   `parse_response_at_close` (the request is always GET, never HEAD).
//! - **One request per connection** (the request carries
//!   `Connection: close`), so a connection's bytes are one response, after
//!   any interim ones, and anything after the final response is dropped
//!   (RFC 9112 §6.3: "A client MUST NOT process, cache, or forward such
//!   extra data as a separate response").
//! - **The received bytes are kept whole** (`Phase::Reading.received`)
//!   and re-parsed on every `Bytes`; interim responses are removed from the
//!   front as soon as they are complete. A real parser makes a decision
//!   only from bytes received, and the theorems state what the transducer
//!   adds to that (`contract.rs`).
//! - **Interim responses** (RFC 9110 §15.2: "A client MUST be able to parse
//!   one or more 1xx responses received prior to a final response") are
//!   skipped, and the next response read from the octets after them. The
//!   skipping recurses on the octets after the interim response, which a
//!   real parser leaves shorter than what it was given (a response is at
//!   least its status line); a parser that consumed nothing would loop, so
//!   that case is an invalid message instead. It is a guard for totality.
//! - **What the connection does at the end**: once a final response is
//!   decided while the connection is open, the transducer asks for `Close`
//!   (RFC 9112 §9.6: the client sent `close` and reads nothing more); if it
//!   was decided by the server closing, there is nothing to close. Every
//!   failure on an open connection also closes it.
//! - **Inputs out of order** (`Bytes` before `Connected`, a second
//!   `Connected`) are not something a correct shell sends; they end the
//!   fetch with [`Reason::Shell`] rather than being ignored.
//! - **The URL functions are parameters** ([`UrlFns`]): Fetch §2.2.6 step
//!   3, "parsing location with response's URL", is `UrlFns::location`
//!   given the request URL and the `Location` field value's octets. How
//!   the octets become the URL parser's input is the join's choice
//!   (`real`), since Fetch does not say.
//! - **Redirects** are Fetch §4.5 for a request that is a navigation GET
//!   with no body, redirect mode "follow", no CORS and no timing: of steps
//!   1 to 22, steps 9 to 17 and 19 to 21 do nothing for such a request (no
//!   body, the method stays GET for 301, 302 and 303, no CORS headers to
//!   remove, no timing info, no referrer) and are omitted, and steps 1
//!   and 2 only name things. The redirect count is [`State::redirects`];
//!   the URL list is not kept, only its last URL ([`State::url`], the
//!   "current URL"). Main fetch for the new request (step 22) comes down
//!   to [`begin`]: a new connection, a new request with `Connection:
//!   close`.
//! - **`Location` extraction** (Fetch §2.2.2 "extract header list
//!   values"): no `Location` line is null; more than one is failure (step
//!   2: "If the ABNF for name allows a single header and list contains more
//!   than one, then return failure", and RFC 9110 §10.2.2's `Location =
//!   URI-reference` is a single value); one line's value is given to the
//!   URL parser without first checking it against the `URI-reference`
//!   grammar: the URL parser decides it (as browsers do), so a value it
//!   rejects is the failure of step 4.2.
//! - **Only `http:`.** TLS is not built yet: `Connect.tls` is always false,
//!   and a URL that [`crate::request::spec::request_bytes`] refuses (any
//!   other scheme, userinfo, a non-ASCII host) ends the fetch with
//!   [`Reason::NotFetched`] before anything is sent.
//! - **No cookies yet.** The state has no jar. 3.6's jar becomes a field of
//!   [`State`], passed to [`start`] and returned with `Done`/`Fail`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The URL record this crate fetches.
pub type Url = clazel_url::url::spec::Url;

/// A parsed response.
pub type Response = clazel_http::message::spec::Response;

/// The result of the response parser.
pub type Parse = clazel_http::message::spec::Parse;

// ===========================================================================
// The parameters.
// ===========================================================================

/// What the transducer needs of the URL parser.
pub struct UrlFns {
    /// Fetch §2.2.6 location URL, step 3: the result of parsing the
    /// `Location` value (octets) with the request's URL as the base URL;
    /// `None` is failure.
    pub location: spec_fn(Url, Seq<u8>) -> Option<Url>,
}

/// What the transducer needs of the HTTP response parser.
pub struct HttpFns {
    /// The response at the start of everything received so far on a
    /// connection that is still open (`parse_response`).
    pub parse: spec_fn(Seq<u8>) -> Parse,
    /// The response in everything received on a connection the server has
    /// closed (`parse_response_at_close`: RFC 9112 §6.3 steps 6 and 8).
    pub parse_at_close: spec_fn(Seq<u8>) -> Parse,
}

// ===========================================================================
// States, inputs and actions.
// ===========================================================================

/// Why a fetch failed.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Reason {
    /// A URL this client does not fetch ([`crate::request::spec::request_bytes`]
    /// is `None` or there is nowhere to connect).
    NotFetched,
    /// The connection failed or closed before anything was decided.
    Network,
    /// The bytes received are not a valid response (or past a limit).
    Invalid,
    /// A transfer coding this client cannot decode.
    Unsupported,
    /// The connection closed before a final response was complete.
    Incomplete,
    /// An input the protocol does not allow in this phase.
    Shell,
    /// Fetch §4.5 step 5: the location URL is failure (the `Location`
    /// value does not parse, or there is more than one).
    RedirectLocation,
    /// Fetch §4.5 step 6: the location URL's scheme is not an HTTP(S)
    /// scheme.
    RedirectScheme,
    /// Fetch §4.5 step 7: a redirect after [`max_redirects`] of them.
    RedirectLimit,
}

/// Where the current request is.
pub enum Phase {
    /// `Connect` was asked for; waiting for `Connected`.
    Connecting,
    /// The request was sent; `received` is what has arrived since, after
    /// any complete interim responses.
    Reading {
        /// the octets received and not yet consumed
        received: Seq<u8>,
    },
    /// `Done` or `Fail` was given; nothing more happens.
    Finished,
}

/// The transducer's state.
pub struct State {
    /// The URL of the current request (Fetch: "request's current URL").
    pub url: Url,
    /// Fetch: "request's redirect count".
    pub redirects: nat,
    /// Where it is.
    pub phase: Phase,
}

/// What the shell reports.
pub enum Input {
    /// The connection asked for is open.
    Connected,
    /// Octets read from the connection, in order.
    Bytes(Seq<u8>),
    /// The server closed the connection (end of stream).
    Closed,
    /// The connection could not be opened, or failed.
    Error,
}

/// What the shell is asked to do.
pub enum Action {
    /// Open a connection to `host` (the host serializer's output, for the
    /// resolver) at `port`, with TLS when `tls` (never, yet).
    Connect {
        /// the host
        host: Seq<u8>,
        /// the port
        port: nat,
        /// whether to speak TLS on it
        tls: bool,
    },
    /// Write these octets to the connection.
    Send(Seq<u8>),
    /// Close the connection.
    Close,
    /// The fetch is over: the final response, for the URL it is the
    /// response to.
    Done {
        /// the URL of the request it answers
        url: Url,
        /// the response
        response: Response,
    },
    /// The fetch failed.
    Fail(Reason),
}

// ===========================================================================
// Starting a request.
// ===========================================================================

/// The state that has ended, keeping the URL.
pub open spec fn finished(s: State) -> State {
    State { url: s.url, redirects: s.redirects, phase: Phase::Finished }
}

/// Begin the request for `url`, after `redirects` redirects: ask for its
/// connection, or fail if it is a URL this client does not fetch.
pub open spec fn begin(url: Url, redirects: nat) -> (State, Seq<Action>) {
    match (crate::request::spec::connect_to(url), crate::request::spec::request_bytes(url)) {
        (Some((host, port)), Some(_)) => (
            State { url: url, redirects: redirects, phase: Phase::Connecting },
            seq![Action::Connect { host: host, port: port, tls: false }],
        ),
        _ => (State { url: url, redirects: redirects, phase: Phase::Finished }, seq![Action::Fail(Reason::NotFetched)]),
    }
}

/// The first state and actions of a fetch of `url`.
pub open spec fn start(url: Url) -> (State, Seq<Action>) {
    begin(url, 0)
}

// ===========================================================================
// Reading the response.
// ===========================================================================

/// The response read from the received octets so far.
pub enum Settled {
    /// Nothing decided: wait for more, with these octets still unconsumed.
    Wait(Seq<u8>),
    /// The final response.
    Final(Response),
    /// The fetch fails.
    Bad(Reason),
}

/// The final response at the start of `received` on an open connection,
/// skipping complete interim responses (RFC 9110 §15.2).
pub open spec fn settle(http: HttpFns, received: Seq<u8>) -> Settled
    decreases received.len()
{
    match (http.parse)(received) {
        clazel_http::message::spec::Parse::Incomplete => Settled::Wait(received),
        clazel_http::message::spec::Parse::Invalid => Settled::Bad(Reason::Invalid),
        clazel_http::message::spec::Parse::Unsupported => Settled::Bad(Reason::Unsupported),
        clazel_http::message::spec::Parse::Done { response, rest } => if crate::request::spec::is_interim(response.status_line.status) {
            // §15.2: the interim response is skipped and the next one read
            // from the octets after it (the guard: see the modelling
            // choices).
            if rest.len() < received.len() {
                settle(http, rest)
            } else {
                Settled::Bad(Reason::Invalid)
            }
        } else {
            Settled::Final(response)
        },
    }
}

/// The final response in `received` once the server has closed the
/// connection: RFC 9112 §6.3 step 8 ends a close-delimited body here, and
/// any other unfinished message is an error (step 6), as the parser
/// decides. An interim response is not a final one: the final response
/// never came.
pub open spec fn settle_at_close(http: HttpFns, received: Seq<u8>) -> Settled {
    match (http.parse_at_close)(received) {
        clazel_http::message::spec::Parse::Done { response, rest } => if crate::request::spec::is_interim(response.status_line.status) {
            Settled::Bad(Reason::Incomplete)
        } else {
            Settled::Final(response)
        },
        clazel_http::message::spec::Parse::Invalid => Settled::Bad(Reason::Invalid),
        clazel_http::message::spec::Parse::Unsupported => Settled::Bad(Reason::Unsupported),
        clazel_http::message::spec::Parse::Incomplete => Settled::Bad(Reason::Incomplete),
    }
}

/// `Close`, when the connection is still open.
pub open spec fn close_if(open: bool) -> Seq<Action> {
    if open {
        seq![Action::Close]
    } else {
        seq![]
    }
}

// ===========================================================================
// Redirects.
// ===========================================================================

/// Fetch §4.5 step 7: the most redirects a fetch follows.
pub open spec fn max_redirects() -> nat {
    20
}

/// Fetch §2.2.3: "A redirect status is a status that is 301, 302, 303,
/// 307, or 308." (RFC 9110 §15.4.2 to §15.4.4, §15.4.8, §15.4.9.)
pub open spec fn is_redirect_status(status: nat) -> bool {
    status == 301 || status == 302 || status == 303 || status == 307 || status == 308
}

/// Fetch §2.1: "An HTTP(S) scheme is "http" or "https"."
pub open spec fn is_http_s_scheme(scheme: Seq<u32>) -> bool {
    scheme == clazel_url::url::spec::http_str() || scheme == clazel_url::url::spec::https_str()
}

/// "Location" (RFC 9110 §10.2.2; field names are case-insensitive).
pub open spec fn lit_location() -> Seq<u8> {
    seq![0x4Cu8, 0x6F, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E]
}

/// What Fetch §2.2.6 location URL returns.
pub enum LocationUrl {
    /// null: not a redirect
    Null,
    /// failure
    Failure,
    /// a URL
    Url(Url),
}

/// `url` with `fragment` as its fragment if it has none (Fetch §2.2.6
/// location URL, step 4).
pub open spec fn with_fragment(url: Url, fragment: Option<Seq<u32>>) -> Url {
    if url.fragment is None {
        clazel_url::url::spec::Url {
            scheme: url.scheme,
            username: url.username,
            password: url.password,
            host: url.host,
            port: url.port,
            path: url.path,
            query: url.query,
            fragment: fragment,
        }
    } else {
        url
    }
}

/// Fetch §2.2.6: "The location URL of a response response, given null or
/// an ASCII string requestFragment", for the response to a request for
/// `request_url` (which is "response's URL").
pub open spec fn location_url(urls: UrlFns, response: Response, request_url: Url) -> LocationUrl {
    // 1. "If response's status is not a redirect status, then return null."
    if !is_redirect_status(response.status_line.status) {
        LocationUrl::Null
    } else {
        // 2. "Let location be the result of extracting header list values
        // given `Location` and response's header list." (See the modelling
        // choices: none is null, more than one is failure.)
        let values = clazel_http::field::spec::field_values_named(response.fields, lit_location());
        if values.len() == 0 {
            LocationUrl::Null
        } else if values.len() > 1 {
            LocationUrl::Failure
        } else {
            // 3. "If location is a header value, then set location to the
            // result of parsing location with response's URL."
            match (urls.location)(request_url, values[0]) {
                None => LocationUrl::Failure,
                // 4. "If location is a URL whose fragment is null, then set
                // location's fragment to requestFragment."
                // 5. "Return location."
                Some(location) => LocationUrl::Url(with_fragment(location, request_url.fragment)),
            }
        }
    }
}

/// What a final response for the current request leads to (Fetch §4.5
/// HTTP-redirect fetch); `open` says whether the connection is still
/// open.
pub open spec fn on_final(urls: UrlFns, s: State, response: Response, open: bool) -> (State, Seq<Action>) {
    // 3. "Let locationURL be internalResponse's location URL given
    // request's current URL's fragment."
    match location_url(urls, response, s.url) {
        // 4. "If locationURL is null, then return response."
        LocationUrl::Null => (finished(s), close_if(open) + seq![Action::Done { url: s.url, response: response }]),
        // 5. "If locationURL is failure, then return a network error."
        LocationUrl::Failure => fail(s, Reason::RedirectLocation, open),
        LocationUrl::Url(location) => if !is_http_s_scheme(location.scheme) {
            // 6. "If locationURL's scheme is not an HTTP(S) scheme, then
            // return a network error."
            fail(s, Reason::RedirectScheme, open)
        } else if s.redirects == max_redirects() {
            // 7. "If request's redirect count is 20, then return a network
            // error."
            fail(s, Reason::RedirectLimit, open)
        } else {
            // 8. "Increase request's redirect count by 1."
            // 18. "Append locationURL to request's URL list." (It becomes
            // the current URL.)
            // 22. "Return the result of running main fetch given
            // fetchParams and recursive": a new request, on a new
            // connection.
            let next = begin(location, s.redirects + 1);
            (next.0, close_if(open) + next.1)
        },
    }
}

/// The fetch fails for `reason`; `open` says whether the connection is
/// still open.
pub open spec fn fail(s: State, reason: Reason, open: bool) -> (State, Seq<Action>) {
    (finished(s), close_if(open) + seq![Action::Fail(reason)])
}

// ===========================================================================
// The step function.
// ===========================================================================

/// The next state and actions after `input` in state `s`.
pub open spec fn step(http: HttpFns, urls: UrlFns, s: State, input: Input) -> (State, Seq<Action>) {
    match s.phase {
        Phase::Finished => (s, seq![]),
        Phase::Connecting => match input {
            // The connection is open: send the request.
            Input::Connected => match crate::request::spec::request_bytes(s.url) {
                Some(bytes) => (State { url: s.url, redirects: s.redirects, phase: Phase::Reading { received: seq![] } }, seq![Action::Send(bytes)]),
                None => fail(s, Reason::NotFetched, true),
            },
            Input::Bytes(_) => fail(s, Reason::Shell, true),
            Input::Closed => fail(s, Reason::Network, false),
            Input::Error => fail(s, Reason::Network, false),
        },
        Phase::Reading { received } => match input {
            Input::Connected => fail(s, Reason::Shell, true),
            Input::Bytes(bytes) => match settle(http, received + bytes) {
                Settled::Wait(rest) => (State { url: s.url, redirects: s.redirects, phase: Phase::Reading { received: rest } }, seq![]),
                Settled::Final(response) => on_final(urls, s, response, true),
                Settled::Bad(reason) => fail(s, reason, true),
            },
            Input::Closed => match settle_at_close(http, received) {
                Settled::Final(response) => on_final(urls, s, response, false),
                Settled::Bad(reason) => fail(s, reason, false),
                // settle_at_close never waits.
                Settled::Wait(_) => fail(s, Reason::Incomplete, false),
            },
            Input::Error => fail(s, Reason::Network, true),
        },
    }
}

/// The state and every action after the inputs `inputs`, in order, from
/// state `s`.
pub open spec fn run(http: HttpFns, urls: UrlFns, s: State, inputs: Seq<Input>) -> (State, Seq<Action>)
    decreases inputs.len()
{
    if inputs.len() == 0 {
        (s, seq![])
    } else {
        let first = step(http, urls, s, inputs[0]);
        let after = run(http, urls, first.0, inputs.drop_first());
        (after.0, first.1 + after.1)
    }
}

} // verus!
