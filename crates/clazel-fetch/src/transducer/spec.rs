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
//!   fetch" (steps 3 to 8, 18 and 22), §2.1 "HTTP(S) scheme", §3.1.1
//!   "append a request `Cookie` header", §3.1.2 "parse and store response
//!   `Set-Cookie` headers", §4.6 "HTTP-network-or-cache fetch" (steps 8.3
//!   and 8.21.1: `includeCredentials`, the `Cookie` header) and §4.7
//!   "HTTP-network fetch" (step 17: storing the response's cookies);
//! - draft-ietf-httpbis-rfc6265bis-22 (as in `clazel_cookie::storage::spec`):
//!   §5.2 same-site requests, §5.3, §5.7 storage, §5.8 retrieval, all as
//!   `clazel_cookie` states them;
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
//! - **The jar is not part of [`State`]** (phase-3.md 3.7: the kernel
//!   owns one jar for every tab, and two fetches in flight must not each
//!   hold a copy of it). [`step`] is given the jar as it is at that moment
//!   and the time `now` (seconds since 1601, `clazel_cookie`'s clock), reads
//!   the jar only to build the `Cookie` field, and returns, besides the next
//!   state and the actions, the **jar operations** it performed, in order
//!   ([`JarOp`]): §5.8.3 step 5's update when the request is built
//!   (`Retrieved`) and §5.7 storage of each `Set-Cookie` line of a final
//!   response (`Stored`). The caller applies them ([`apply_ops`], defined by
//!   `clazel_cookie`'s spec functions) to its jar. The next state, the
//!   operations and every action other than the `Send`'s bytes do not
//!   depend on the jar (`theorem_jar_only_in_sends`), so a caller that
//!   applies them to a jar other fetches also change still runs this
//!   transducer.
//! - **The cookie parameters** are in [`UrlFns`]: the Public Suffix List
//!   `rules` the cookie functions take, the URL as they read it
//!   ([`request_url`]) and the URL Standard's "origin" of a URL, from which
//!   the request's origin and the same-site status of a redirect are
//!   computed. The shipped join gives `psl_rules()` and
//!   `url_origin` (`real`); the proofs hold for every one.
//! - **Cookies are included** (Fetch §4.6 step 8.3: `includeCredentials` is
//!   true when "request's credentials mode is "include"", which is a
//!   navigation request's) and the user agent is not configured to block
//!   them. The `Cookie` field is added when the connection is open and the
//!   request is sent ([`step`], `Connected`), as Fetch adds it in HTTP-
//!   network-or-cache fetch, after any redirect: from the jar as it is
//!   then. If the cookie-string is one no field value can carry (the
//!   request with it is not valid), the request is sent without a `Cookie`
//!   field (a choice of ours: Fetch appends the header without checking it;
//!   a cookie stored by §5.6's parser never has such a value, which is not
//!   proven here). Either way the request is sent, so whether it is sent does
//!   not depend on the jar. The `Set-Cookie` field lines are stored in [`on_final`], before
//!   the redirect is decided (Fetch §4.7 step 17 is before the redirect
//!   fetch gets the response), from the point of view of the request's
//!   current URL, **one field line at a time** (§3.1.2 step 6: "each
//!   occurrence is processed independently"). Only a final response
//!   reaches [`on_final`]: [`settle`] skips every 1xx response, which is
//!   RFC 6265bis §5.3's "ignore the Set-Cookie fields of 100-level
//!   responses". A failure that ends the fetch after a final response
//!   (a bad `Location`, the limit) still keeps the cookies it set: its
//!   `Stored` operations come with the `Fail`.
//! - **The request context** (RFC 6265bis §5.2, `RequestContext::Http`) is a
//!   user's top-level navigation with no client: GET (a "safe" method),
//!   navigating a top-level traversable, not a reload, `site for cookies`
//!   "none" (so "same-site": §5.2 says "or if the request has no client")
//!   and the current URL's origin from [`UrlFns::origin`]. Fetch §3.1.3
//!   "determine the same-site mode" adds the **redirect-taint**: "if request's
//!   redirect-taint is "cross-site"", the mode is "unset-or-less"; we model
//!   the taint as [`State::tainted`], set (and never cleared) when a redirect
//!   leads to a URL whose origin is not same-site with the current URL's
//!   (the pinned Fetch text computes "redirect-taint" outside the steps we
//!   transcribed, so this is our reading of its name), and a tainted
//!   request's "site for cookies" is an opaque origin, which no URL is
//!   same-site with, so §5.2 makes it "cross-site": SameSite=Strict cookies
//!   are not sent, Lax and Default ones are (a safe method, a top-level
//!   target). *Fetch §3.1.3 step 3, as we read it, returns "lax-or-less"
//!   for every GET request whose destination is "document" before the
//!   taint is looked at; that would withhold Strict cookies from
//!   a same-site navigation and does not agree with RFC 6265bis §5.2, so we
//!   follow §5.2 (we are not sure we read step 3 as intended, so it is not
//!   an entry of `docs/ERRATA.md`).* The draft's §5.2 has no rule about
//!   redirect chains of its own.
//! - **Secure.** A connection is "secure" ([`clazel_cookie::storage::spec::url_is_secure`])
//!   when the URL's scheme is `https`; `Connect.tls` is false exactly when
//!   the scheme is `http`, which is the only scheme fetched yet, so no
//!   `Secure` cookie is ever sent. Both change together when TLS arrives.
//! - **The cookie-string's request URL** is [`request_url`]: the URL's
//!   scheme, canonicalized host and path (an empty path is `/`, as
//!   [`crate::request::spec::origin_form`] sends it).

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

/// The cookie model's types (`clazel_cookie::storage::spec`).
pub type Cookie = clazel_cookie::storage::spec::Cookie;

/// The URL a cookie function reads.
pub type RequestUrl = clazel_cookie::storage::spec::RequestUrl;

/// The request context a cookie function reads.
pub type RequestContext = clazel_cookie::storage::spec::RequestContext;

/// What the transducer needs of the URL parser and the URL-side
/// functions of the cookie model.
pub struct UrlFns {
    /// URL §4.7 "origin" of a URL.
    pub origin: spec_fn(Url) -> clazel_origin::spec::Origin,
    /// The URL as the cookie functions read it: [`request_url`] in the
    /// shipped join.
    pub request_url: spec_fn(Url) -> RequestUrl,
    /// The Public Suffix List the cookie functions take.
    pub rules: Seq<clazel_psl::spec::Rule>,
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
    /// Fetch's "redirect-taint" is "cross-site": some redirect crossed
    /// sites (see the modelling choices).
    pub tainted: bool,
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

/// What a step did to the cookie jar it was given (see the modelling
/// choices): the caller applies these, in order ([`apply_ops`]).
pub enum JarOp {
    /// RFC 6265bis §5.8.3 retrieval for this request URL and context at
    /// `now`: step 5 ("Update the last-access-time of each cookie in the
    /// cookie-list") and the eviction of expired cookies.
    Retrieved {
        /// the request URL, as the cookie functions read it
        url: RequestUrl,
        /// the request context
        ctx: RequestContext,
        /// the time
        now: int,
    },
    /// RFC 6265bis §5.7 storage of one `Set-Cookie` field value as HTTP
    /// (Fetch §3.1.2 step 6.2), for this request URL and context at `now`.
    Stored {
        /// the field value
        line: Seq<u8>,
        /// the request URL, as the cookie functions read it
        url: RequestUrl,
        /// the request context
        ctx: RequestContext,
        /// the time
        now: int,
    },
}

/// The jar after `op`: `clazel_cookie`'s `jar_after_retrieval` or
/// `store_a_set_cookie_string`.
pub open spec fn apply_op(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<Cookie>, op: JarOp) -> Seq<Cookie> {
    match op {
        JarOp::Retrieved { url, ctx, now } => clazel_cookie::storage::spec::jar_after_retrieval(rules, jar, url, ctx, now),
        JarOp::Stored { line, url, ctx, now } => clazel_cookie::storage::spec::store_a_set_cookie_string(rules, jar, line, url, ctx, now),
    }
}

/// The jar after each of `ops`, in order.
pub open spec fn apply_ops(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<Cookie>, ops: Seq<JarOp>) -> Seq<Cookie>
    decreases ops.len()
{
    if ops.len() == 0 {
        jar
    } else {
        apply_ops(rules, apply_op(rules, jar, ops[0]), ops.drop_first())
    }
}

// ===========================================================================
// Starting a request.
// ===========================================================================

/// The state that has ended, keeping the URL.
pub open spec fn finished(s: State) -> State {
    State { phase: Phase::Finished, ..s }
}

/// The scheme as the cookie functions read it: `url_is_secure` asks whether
/// it is `https` (or `wss`), so a connection is "secure" exactly when TLS
/// is used (see the modelling choices, "Secure").
pub open spec fn cookie_scheme(url: Url) -> Seq<u8> {
    clazel_cookie::matching::spec::narrow(url.scheme)
}

/// RFC 6265bis §5.7 and §5.8's view of the URL: its scheme, canonicalized
/// host and path (see the modelling choices). The transducer reads it
/// through [`UrlFns::request_url`], which `real` sets to this.
pub open spec fn request_url(url: Url) -> RequestUrl {
    let p = clazel_url::url::spec::url_path_serializer(url.path);
    RequestUrl {
        scheme: cookie_scheme(url),
        host: clazel_cookie::matching::spec::canonicalize_a_host_name(url.host),
        path: clazel_cookie::matching::spec::narrow(if p.len() == 0 { seq![0x2Fu32] } else { p }),
    }
}

/// RFC 6265bis §5.2's context of the current request of `s` (see the
/// modelling choices): a top-level navigation, GET, with no client, its
/// "site for cookies" an opaque origin once a redirect has crossed sites.
pub open spec fn request_context(urls: UrlFns, s: State) -> RequestContext {
    RequestContext::Http(clazel_cookie::storage::spec::HttpRequest {
        url_origin: (urls.origin)(s.url),
        site_for_cookies: if s.tainted { Some(clazel_origin::spec::Origin::Opaque(0)) } else { None },
        is_reload_navigation: false,
        reloaded_document_was_same_site: false,
        navigates_top_level_traversable: true,
        method_is_safe: true,
        target_is_active_or_top_level: true,
    })
}

/// "Set-Cookie".
pub open spec fn lit_set_cookie() -> Seq<u8> {
    seq![0x53u8, 0x65, 0x74, 0x2D, 0x43, 0x6F, 0x6F, 0x6B, 0x69, 0x65]
}

/// Fetch §3.1.2 step 6: the value of each `Set-Cookie` field line of the
/// response, in order, one per field line (Fetch §2.2.2's extraction would
/// combine them with commas, which §3.1.2 says not to do).
pub open spec fn set_cookie_values(response: Response) -> Seq<Seq<u8>> {
    clazel_http::field::spec::field_values_named(response.fields, lit_set_cookie())
}

/// Fetch §3.1.2 step 6: one `Stored` operation for each of `lines`, in
/// order, each "parse and store" by RFC 6265bis §5.7 as HTTP (the string
/// parsed by §5.6), for the request URL `url` and context `ctx` at `now`.
pub open spec fn stored_ops(lines: Seq<Seq<u8>>, url: RequestUrl, ctx: RequestContext, now: int) -> Seq<JarOp>
    decreases lines.len()
{
    if lines.len() == 0 {
        seq![]
    } else {
        seq![JarOp::Stored { line: lines[0], url: url, ctx: ctx, now: now }] + stored_ops(lines.drop_first(), url, ctx, now)
    }
}

/// The operations storing the cookies of `response`, the response to the
/// current request of `s`.
pub open spec fn response_ops(urls: UrlFns, s: State, response: Response, now: int) -> Seq<JarOp> {
    stored_ops(set_cookie_values(response), (urls.request_url)(s.url), request_context(urls, s), now)
}

/// The retrieval for the current request of `s` (§5.8.3 step 5, and the
/// eviction of expired cookies).
pub open spec fn retrieval_op(urls: UrlFns, s: State, now: int) -> JarOp {
    JarOp::Retrieved { url: (urls.request_url)(s.url), ctx: request_context(urls, s), now: now }
}

/// The cookie-string of the request `s` sends, from `jar` at `now` (Fetch
/// §3.1.1 steps 5 to 7; RFC 6265bis §5.8.3).
pub open spec fn cookie_string(urls: UrlFns, s: State, jar: Seq<Cookie>, now: int) -> Seq<u8> {
    clazel_cookie::storage::spec::retrieve_cookie_string(urls.rules, jar, (urls.request_url)(s.url), request_context(urls, s), now)
}

/// The bytes sent for `url` with the cookie-string `cookie`, given `plain`,
/// the request without a `Cookie` field: the request with it, or `plain`
/// if no field value can carry it (see the modelling choices).
pub open spec fn wire_bytes(url: Url, cookie: Seq<u8>, plain: Seq<u8>) -> Seq<u8> {
    match crate::request::spec::request_bytes_cookie(url, cookie) {
        Some(bytes) => bytes,
        None => plain,
    }
}

/// Begin the request for `url`, after `redirects` redirects, with
/// redirect-taint `tainted`: ask for its connection, or fail if it is a URL
/// this client does not fetch.
pub open spec fn begin(url: Url, redirects: nat, tainted: bool) -> (State, Seq<Action>) {
    match (crate::request::spec::connect_to(url), crate::request::spec::request_bytes(url)) {
        (Some((host, port)), Some(_)) => (
            State { url: url, redirects: redirects, phase: Phase::Connecting, tainted: tainted },
            seq![Action::Connect { host: host, port: port, tls: false }],
        ),
        _ => (
            State { url: url, redirects: redirects, phase: Phase::Finished, tainted: tainted },
            seq![Action::Fail(Reason::NotFetched)],
        ),
    }
}

/// The first state and actions of a fetch of `url`. (No jar: nothing is
/// sent before the connection is open.)
pub open spec fn start(url: Url) -> (State, Seq<Action>) {
    begin(url, 0, false)
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
/// open. The cookies are stored at `now`.
pub open spec fn on_final(urls: UrlFns, s: State, response: Response, open: bool, now: int) -> (State, Seq<Action>, Seq<JarOp>) {
    // Fetch §4.7 step 17 (§3.1.2): "If includeCredentials is true, then the
    // user agent should parse and store response's `Set-Cookie` headers",
    // before the redirect fetch sees the response.
    let ops = response_ops(urls, s, response, now);
    // 3. "Let locationURL be internalResponse's location URL given
    // request's current URL's fragment."
    match location_url(urls, response, s.url) {
        // 4. "If locationURL is null, then return response."
        LocationUrl::Null => (finished(s), close_if(open) + seq![Action::Done { url: s.url, response: response }], ops),
        // 5. "If locationURL is failure, then return a network error."
        LocationUrl::Failure => with_ops(fail(s, Reason::RedirectLocation, open), ops),
        LocationUrl::Url(location) => if !is_http_s_scheme(location.scheme) {
            // 6. "If locationURL's scheme is not an HTTP(S) scheme, then
            // return a network error."
            with_ops(fail(s, Reason::RedirectScheme, open), ops)
        } else if s.redirects == max_redirects() {
            // 7. "If request's redirect count is 20, then return a network
            // error."
            with_ops(fail(s, Reason::RedirectLimit, open), ops)
        } else {
            // 8. "Increase request's redirect count by 1."
            // 18. "Append locationURL to request's URL list." (It becomes
            // the current URL.)
            // 22. "Return the result of running main fetch given
            // fetchParams and recursive": a new request, on a new
            // connection.
            // The redirect-taint (see the modelling choices).
            let tainted = s.tainted || !clazel_origin::spec::same_site(urls.rules, (urls.origin)(s.url), (urls.origin)(location));
            let next = begin(location, s.redirects + 1, tainted);
            (next.0, close_if(open) + next.1, ops)
        },
    }
}

/// The fetch fails for `reason`; `open` says whether the connection is
/// still open. No jar operation.
pub open spec fn fail(s: State, reason: Reason, open: bool) -> (State, Seq<Action>, Seq<JarOp>) {
    (finished(s), close_if(open) + seq![Action::Fail(reason)], seq![])
}

/// `r` with the jar operations `ops` before its own.
pub open spec fn with_ops(r: (State, Seq<Action>, Seq<JarOp>), ops: Seq<JarOp>) -> (State, Seq<Action>, Seq<JarOp>) {
    (r.0, r.1, ops + r.2)
}

// ===========================================================================
// The step function.
// ===========================================================================

/// The next state, actions and jar operations after `input` in state `s`,
/// given the cookie jar `jar` at time `now` (read only to build the
/// `Cookie` field).
pub open spec fn step(http: HttpFns, urls: UrlFns, s: State, input: Input, jar: Seq<Cookie>, now: int) -> (State, Seq<Action>, Seq<JarOp>) {
    match s.phase {
        Phase::Finished => (s, seq![], seq![]),
        Phase::Connecting => match input {
            // The connection is open: send the request, with the `Cookie`
            // field of Fetch §3.1.1 from the jar (RFC 6265bis §5.8.3), and
            // the retrieval's step 5 as an operation.
            Input::Connected => match crate::request::spec::request_bytes(s.url) {
                Some(plain) => {
                    let bytes = wire_bytes(s.url, cookie_string(urls, s, jar, now), plain);
                    (
                        State { phase: Phase::Reading { received: seq![] }, ..s },
                        seq![Action::Send(bytes)],
                        seq![retrieval_op(urls, s, now)],
                    )
                },
                None => with_ops(fail(s, Reason::NotFetched, true), seq![retrieval_op(urls, s, now)]),
            },
            Input::Bytes(_) => fail(s, Reason::Shell, true),
            Input::Closed => fail(s, Reason::Network, false),
            Input::Error => fail(s, Reason::Network, false),
        },
        Phase::Reading { received } => match input {
            Input::Connected => fail(s, Reason::Shell, true),
            Input::Bytes(bytes) => match settle(http, received + bytes) {
                Settled::Wait(rest) => (State { phase: Phase::Reading { received: rest }, ..s }, seq![], seq![]),
                Settled::Final(response) => on_final(urls, s, response, true, now),
                Settled::Bad(reason) => fail(s, reason, true),
            },
            Input::Closed => match settle_at_close(http, received) {
                Settled::Final(response) => on_final(urls, s, response, false, now),
                Settled::Bad(reason) => fail(s, reason, false),
                // settle_at_close never waits.
                Settled::Wait(_) => fail(s, Reason::Incomplete, false),
            },
            Input::Error => fail(s, Reason::Network, true),
        },
    }
}

/// What the shell reports at one step, and the jar and time the step is
/// given.
pub struct Given {
    /// the input
    pub input: Input,
    /// the cookie jar at that step
    pub jar: Seq<Cookie>,
    /// the time at that step
    pub now: int,
}

/// The state, every action and every jar operation after the steps
/// `given`, in order, from state `s`.
pub open spec fn run(http: HttpFns, urls: UrlFns, s: State, given: Seq<Given>) -> (State, Seq<Action>, Seq<JarOp>)
    decreases given.len()
{
    if given.len() == 0 {
        (s, seq![], seq![])
    } else {
        let first = step(http, urls, s, given[0].input, given[0].jar, given[0].now);
        let after = run(http, urls, first.0, given.drop_first());
        (after.0, first.1 + after.1, first.2 + after.2)
    }
}

} // verus!
