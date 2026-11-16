//! Executable-style specification of the request a client sends for a
//! URL, and of which responses are interim. Nothing here runs.
//!
//! Sources (pinned; an RFC never changes after publication):
//! - RFC 9112 "HTTP/1.1", June 2022, §3.2.1 origin form;
//! - RFC 9110 "HTTP Semantics", June 2022, §4.2.1 the `http` URI scheme,
//!   §4.2.2 the `https` URI scheme, §4.2.4 deprecated userinfo, §7.2 `Host`, §7.6.1 `Connection`, §12.5.1
//!   `Accept`, §10.1.5 `User-Agent`, §15.2 informational responses;
//! - the URL Standard (as transcribed in `clazel_url`): the URL record,
//!   the URL path serializer, the host serializer and "serialize an
//!   integer".
//!
//! Modelling choices (each a choice of ours or a deviation in form, never
//! in meaning):
//! - Only `http:` and `https:` URLs are fetched (Fetch §2.1's "HTTP(S)
//!   scheme"), only with GET, and one request per connection, so every
//!   request carries `Connection: close` (§7.6.1) and the response may be
//!   close-delimited. The request is the same for both schemes (§4.2.2's
//!   `https-URI` has `http`'s authority, path and query, and "The
//!   hierarchical path component and optional query component identify the
//!   target resource within that origin server's namespace"); they differ
//!   in the default port ([`default_port`]) and in the connection, which
//!   speaks TLS for `https` ([`uses_tls`]): §4.2.2, "A client MUST ensure
//!   that its HTTP requests for an "https" resource are secured, prior to
//!   being communicated". Securing the connection (TLS 1.3 and the
//!   certificate checks) is the shell's.
//! - The fields sent, in this order: `Host` (§7.2: "A user agent MUST
//!   generate a Host header field in a request"), `Connection: close`,
//!   `Accept: */*` (§12.5.1) and `User-Agent: clazel` (§10.1.5). No
//!   `Accept-Encoding`, so a conforming server sends identity content.
//! - **The `Cookie` field** (Fetch §3.1.1 "append a request `Cookie` header",
//!   steps 6 to 8: "If no cookies were returned, stop" and otherwise
//!   append `Cookie` with the serialized cookies) is the last field, and is
//!   present only when the cookie-string is not empty
//!   ([`request_for_cookie`]). The cookie-string itself is not computed
//!   here: the transducer passes RFC 6265bis §5.8.3's. Everything else
//!   about the request is [`request_for`]'s, so the jar reaches the wire
//!   through this one field value (`theorem_wire_cookies`).
//! - A URL with a username or password is refused (§4.2.4: "A recipient
//!   SHOULD parse for userinfo and treat its presence as an error"); a
//!   sender would otherwise have to decide what to do with it.
//! - The fragment is never sent: the origin form (§3.2.1) has none.
//! - URL strings are code points; what is sent must be ASCII. A URL the
//!   URL parser produced for `http:` serializes to ASCII (its path and
//!   query are percent-encoded and its host is a domain after IDNA or an
//!   IP address), but the spec does not rely on that: a non-ASCII code
//!   point makes the request `None`. The serializer then refuses any
//!   octet that is not allowed where it would go.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every code point of `s` is ASCII.
pub open spec fn all_ascii(s: Seq<u32>) -> bool
    decreases s.len()
{
    s.len() == 0 || (s[0] < 0x80 && all_ascii(s.drop_first()))
}

/// `s` as octets, when every code point is ASCII.
pub open spec fn ascii_octets(s: Seq<u32>) -> Option<Seq<u8>> {
    if all_ascii(s) {
        Some(s.map_values(|c: u32| c as u8))
    } else {
        None
    }
}

/// RFC 9112 §3.2.1: `origin-form = absolute-path [ "?" query ]`: "the
/// absolute path and query components of the target URI. If the target
/// URI's path component is empty, the client MUST send "/" as the path".
/// The path is the URL path serializer's; the query is the URL's.
pub open spec fn origin_form(url: clazel_url::url::spec::Url) -> Seq<u32> {
    let p = clazel_url::url::spec::url_path_serializer(url.path);
    let path = if p.len() == 0 { seq![0x2Fu32] } else { p };
    match url.query {
        Some(q) => path + seq![0x3Fu32] + q,
        None => path,
    }
}

/// RFC 9110 §7.2: `Host = uri-host [ ":" port ]`: the URL's host,
/// serialized, and its port when it has one (the URL parser drops the
/// scheme's default port, as §4.2.1 lets a sender do: "If the port is
/// equal to the default port for a scheme, the normal form is to omit the
/// port subcomponent").
pub open spec fn host_value(url: clazel_url::url::spec::Url) -> Option<Seq<u32>> {
    match url.host {
        Some(host) => {
            let h = clazel_url::host::spec::host_serializer(host);
            Some(match url.port {
                Some(port) => h + seq![0x3Au32] + clazel_url::host::spec::serialize_integer(port),
                None => h,
            })
        },
        None => None,
    }
}

/// "Host".
pub open spec fn lit_host() -> Seq<u8> {
    seq![0x48u8, 0x6F, 0x73, 0x74]
}

/// "Connection".
pub open spec fn lit_connection() -> Seq<u8> {
    seq![0x43u8, 0x6F, 0x6E, 0x6E, 0x65, 0x63, 0x74, 0x69, 0x6F, 0x6E]
}

/// "close".
pub open spec fn lit_close() -> Seq<u8> {
    seq![0x63u8, 0x6C, 0x6F, 0x73, 0x65]
}

/// "Accept".
pub open spec fn lit_accept() -> Seq<u8> {
    seq![0x41u8, 0x63, 0x63, 0x65, 0x70, 0x74]
}

/// "*/*".
pub open spec fn lit_any_type() -> Seq<u8> {
    seq![0x2Au8, 0x2F, 0x2A]
}

/// "User-Agent".
pub open spec fn lit_user_agent() -> Seq<u8> {
    seq![0x55u8, 0x73, 0x65, 0x72, 0x2D, 0x41, 0x67, 0x65, 0x6E, 0x74]
}

/// "clazel".
pub open spec fn lit_product() -> Seq<u8> {
    seq![0x63u8, 0x6C, 0x61, 0x7A, 0x65, 0x6C]
}

/// "GET".
pub open spec fn lit_get() -> Seq<u8> {
    seq![0x47u8, 0x45, 0x54]
}

/// The schemes this client fetches: `http` (RFC 9110 §4.2.1) and `https`
/// (§4.2.2), Fetch §2.1's "HTTP(S) scheme".
pub open spec fn is_fetched_scheme(scheme: Seq<u32>) -> bool {
    scheme == clazel_url::url::spec::http_str() || scheme == clazel_url::url::spec::https_str()
}

/// The request for `url`, or `None` if this client does not fetch it.
pub open spec fn request_for(url: clazel_url::url::spec::Url) -> Option<clazel_http::message::spec::Request> {
    if !is_fetched_scheme(url.scheme) || url.username.len() > 0 || url.password.len() > 0 {
        None
    } else {
        match (ascii_octets(origin_form(url)), host_value(url)) {
            (Some(target), Some(h)) => match ascii_octets(h) {
                Some(host) => Some(clazel_http::message::spec::Request {
                    method: lit_get(),
                    target: target,
                    fields: seq![
                        clazel_http::field::spec::FieldLine { name: lit_host(), value: host },
                        clazel_http::field::spec::FieldLine { name: lit_connection(), value: lit_close() },
                        clazel_http::field::spec::FieldLine { name: lit_accept(), value: lit_any_type() },
                        clazel_http::field::spec::FieldLine { name: lit_user_agent(), value: lit_product() },
                    ],
                }),
                None => None,
            },
            _ => None,
        }
    }
}

/// "Cookie" (RFC 6265bis §5.8.3 via Fetch §3.1.1).
pub open spec fn lit_cookie() -> Seq<u8> {
    seq![0x43u8, 0x6F, 0x6F, 0x6B, 0x69, 0x65]
}

/// The field lines Fetch §3.1.1 steps 6 to 8 add for the cookie-string
/// `cookie`: none if it is empty ("If no cookies were returned, stop."),
/// else one `Cookie` field line holding it.
pub open spec fn cookie_field_lines(cookie: Seq<u8>) -> Seq<clazel_http::field::spec::FieldLine> {
    if cookie.len() == 0 {
        seq![]
    } else {
        seq![clazel_http::field::spec::FieldLine { name: lit_cookie(), value: cookie }]
    }
}

/// The request for `url` carrying the cookie-string `cookie`: [`request_for`]
/// with the field lines of [`cookie_field_lines`] appended.
pub open spec fn request_for_cookie(url: clazel_url::url::spec::Url, cookie: Seq<u8>) -> Option<clazel_http::message::spec::Request> {
    match request_for(url) {
        Some(r) => Some(clazel_http::message::spec::Request { method: r.method, target: r.target, fields: r.fields + cookie_field_lines(cookie) }),
        None => None,
    }
}

/// The bytes sent for `url` carrying the cookie-string `cookie`: the
/// request, serialized, when it is valid (RFC 9112 §2.1, §3). A cookie
/// value no field value can carry makes the request `None`.
pub open spec fn request_bytes_cookie(url: clazel_url::url::spec::Url, cookie: Seq<u8>) -> Option<Seq<u8>> {
    match request_for_cookie(url, cookie) {
        Some(r) => if clazel_http::message::spec::is_valid_request(r) {
            Some(clazel_http::message::spec::serialize_request(r))
        } else {
            None
        },
        None => None,
    }
}

/// The bytes sent for `url`: the request, serialized, when it is valid
/// (RFC 9112 §2.1, §3).
pub open spec fn request_bytes(url: clazel_url::url::spec::Url) -> Option<Seq<u8>> {
    match request_for(url) {
        Some(r) => if clazel_http::message::spec::is_valid_request(r) {
            Some(clazel_http::message::spec::serialize_request(r))
        } else {
            None
        },
        None => None,
    }
}

/// Whether the connection for `url` speaks TLS: exactly when its scheme is
/// `https` (RFC 9110 §4.2.2: "A client MUST ensure that its HTTP requests
/// for an "https" resource are secured, prior to being communicated"; an
/// `http` request is sent in the clear, §4.2.1).
pub open spec fn uses_tls(url: clazel_url::url::spec::Url) -> bool {
    url.scheme == clazel_url::url::spec::https_str()
}

/// The scheme's default port: 443 for `https` (RFC 9110 §4.2.2: "If the
/// port subcomponent is empty or not given, TCP port 443 (the reserved
/// port for HTTP over TLS) is the default"), else 80 (§4.2.1: "TCP port 80
/// ... is the default"). For a
/// scheme this client does not fetch, [`request_bytes`] is `None`, so the
/// value is never used.
pub open spec fn default_port(url: clazel_url::url::spec::Url) -> nat {
    if uses_tls(url) {
        443
    } else {
        80
    }
}

/// Where to connect for `url`: the host as the resolver takes it (the
/// host serializer's output) and the port, the URL's or the scheme's
/// default ([`default_port`]).
pub open spec fn connect_to(url: clazel_url::url::spec::Url) -> Option<(Seq<u8>, nat)> {
    match url.host {
        Some(host) => match ascii_octets(clazel_url::host::spec::host_serializer(host)) {
            Some(h) => Some((h, match url.port {
                Some(p) => p,
                None => default_port(url),
            })),
            None => None,
        },
        None => None,
    }
}

/// RFC 9110 §15.2: "A client MUST be able to parse one or more 1xx
/// responses received prior to a final response". An interim response is
/// skipped and the next response read from the octets after it. 101
/// (Switching Protocols) is not interim for us: we never send `Upgrade`,
/// so it is a final response we do not support.
pub open spec fn is_interim(status: nat) -> bool {
    100 <= status && status <= 199 && status != 101
}


// ===========================================================================
// Item 6.16: a request with a method and a body.
// ===========================================================================
//
// Sources (6.16; Fetch at the commit `transducer::spec` pins; the step
// numbers below are those of the text as read from that commit, marked †
// in phase-6.md until a person checks them):
// - Fetch §4.6 "HTTP-network-or-cache fetch": steps 6 to 9, "Let
//   contentLengthHeaderValue be null. If httpRequest's body is null and
//   httpRequest's method is `POST` or `PUT`, then set
//   contentLengthHeaderValue to `0`. If contentLength is non-null, then set
//   contentLengthHeaderValue, serialized and isomorphic encoded. If
//   contentLengthHeaderValue is non-null, then append (`Content-Length`,
//   contentLengthHeaderValue) to httpRequest's header list."; step 13,
//   "Append a request `Origin` header for httpRequest"; step 22.1, the
//   `Cookie` header;
// - Fetch "append a request `Origin` header": "1. Assert: request's origin
//   is not "client". 2. Let serializedOrigin be the result of byte-
//   serializing a request origin with request. 3. If request's response
//   tainting is "cors" or request's mode is "websocket" or "webtransport",
//   then append (`Origin`, serializedOrigin) to request's header list. 4.
//   Otherwise, if request's method is neither `GET` nor `HEAD`, then: 1. If
//   request's mode is not "cors", then switch on request's referrer
//   policy: "no-referrer": set serializedOrigin to `null`.
//   "no-referrer-when-downgrade", "strict-origin" or
//   "strict-origin-when-cross-origin": if request's origin is a tuple
//   origin, its scheme is "https", and request's current URL's scheme is
//   not "https", then set serializedOrigin to `null`. "same-origin": ...
//   2. Append (`Origin`, serializedOrigin) to request's header list.";
// - Fetch "serializing a request origin" step 2: "If request's redirect-
//   taint is not "same-origin", then return "null"."; step 3: "Return
//   request's origin, serialized.";
// - RFC 9110 §9.2.1 safe methods ("GET, HEAD, OPTIONS, and TRACE"); §8.6
//   `Content-Length`; §8.3 `Content-Type`; RFC 9112 §6.2 (a request's body
//   length is its `Content-Length`).
//
// Modelling choices of this part (6.16):
// - A **request** here is a method, a body (null, or a content type and
//   the octets), and the origin of the document that made it (the
//   "initiator": Fetch's "request's origin", also what RFC 6265bis §5.2
//   reads as the site for cookies of a request with a client; `None` is a
//   navigation with no client, which is every request before 6.16).
//   [`Req`] is the part of Fetch's request that is not the URL.
// - Only `GET` and `POST` are fetched ([`is_navigation_method`]): a form
//   submission is one of them (HTML "submit as entity body" and "mutate
//   action URL"). `HEAD` never arises, so the `HEAD` of Fetch's rewriting
//   rule is kept in the rule and never reached. A `GET` has no body (Fetch:
//   a request with method `GET` and a body is a TypeError at construction):
//   [`req_ok`].
// - The body is a byte sequence with a content type, both from the caller
//   (the kernel gets them from the renderer's `Submit`, bounded there).
//   Fetch's body "source" is always bytes, so Fetch's step 11 of HTTP-
//   redirect fetch ("If internalResponse's status is not 303, request's
//   body is non-null, and request's body's source is null, then return a
//   network error") never fires.
// - The header list is the fixed fields of [`request_for`], then, in this
//   order, `Content-Type` (the body's), `Content-Length` (steps 6 to 9),
//   `Origin` (step 13), then `Cookie` last (step 22.1). Fetch's
//   "request-body-header names" are deleted when the body is removed
//   (HTTP-redirect fetch 12.2); here those fields are *derived* from the
//   body, so a request without a body has none of them: the same thing.
// - `Origin` follows the algorithm above with the default referrer policy
//   ("strict-origin-when-cross-origin"; the initiator's own policy is not
//   carried until a phase that has referrers) and mode navigate: no
//   `Origin` on `GET`; on any other method the byte-serialized request
//   origin, `null` if the origin is opaque, if there is no initiator, if
//   the request's redirect-taint is not "same-origin" ([`Req::origin_tainted`],
//   which the transducer sets when a redirect leaves the origin of the URL
//   before it) or if the initiator is an `https` origin and the current
//   URL's scheme is not `https`.
// - A body is sent on the wire after the empty line, exactly
//   `Content-Length` octets (RFC 9112 §6.2). Octets are never altered.

/// "POST".
pub open spec fn lit_post() -> Seq<u8> {
    seq![0x50u8, 0x4F, 0x53, 0x54]
}

/// "HEAD".
pub open spec fn lit_head() -> Seq<u8> {
    seq![0x48u8, 0x45, 0x41, 0x44]
}

/// "OPTIONS".
pub open spec fn lit_options() -> Seq<u8> {
    seq![0x4Fu8, 0x50, 0x54, 0x49, 0x4F, 0x4E, 0x53]
}

/// "TRACE".
pub open spec fn lit_trace() -> Seq<u8> {
    seq![0x54u8, 0x52, 0x41, 0x43, 0x45]
}

/// "Content-Type".
pub open spec fn lit_content_type() -> Seq<u8> {
    seq![0x43u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x54, 0x79, 0x70, 0x65]
}

/// "Content-Length".
pub open spec fn lit_content_length() -> Seq<u8> {
    seq![0x43u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68]
}

/// "Origin".
pub open spec fn lit_origin() -> Seq<u8> {
    seq![0x4Fu8, 0x72, 0x69, 0x67, 0x69, 0x6E]
}

/// "null" (a serialized opaque origin).
pub open spec fn lit_null() -> Seq<u8> {
    seq![0x6Eu8, 0x75, 0x6C, 0x6C]
}

/// A request body: its `Content-Type` field value and its octets.
pub struct Payload {
    /// the `Content-Type` field value
    pub content_type: Seq<u8>,
    /// the octets
    pub bytes: Seq<u8>,
}

/// The part of Fetch's request that is not its URL (see the modelling
/// choices of this part).
pub struct Req {
    /// the method
    pub method: Seq<u8>,
    /// the body, or null
    pub body: Option<Payload>,
    /// the origin of the document that made the request (Fetch's
    /// "request's origin"), or none: a navigation with no client
    pub initiator: Option<clazel_origin::spec::Origin>,
    /// Fetch's redirect-taint is not "same-origin": some redirect led to a
    /// URL whose origin is not that of the URL before it
    pub origin_tainted: bool,
}

/// The request every fetch before 6.16 is: `GET`, no body, no client.
pub open spec fn get_req() -> Req {
    Req { method: lit_get(), body: None, initiator: None, origin_tainted: false }
}

/// A navigation with `GET`, no body and no client (the class before 6.16;
/// `origin_tainted` is not looked at: no `Origin` is sent on `GET`).
pub open spec fn is_plain_get(req: Req) -> bool {
    req.method == lit_get() && req.body is None && req.initiator is None
}

/// The methods a navigation uses here: `GET` and `POST`.
pub open spec fn is_navigation_method(m: Seq<u8>) -> bool {
    m == lit_get() || m == lit_post()
}

/// RFC 9110 §9.2.1: "the request methods GET, HEAD, OPTIONS, and TRACE
/// are defined to be safe".
pub open spec fn is_safe_method(m: Seq<u8>) -> bool {
    m == lit_get() || m == lit_head() || m == lit_options() || m == lit_trace()
}

/// The most octets a request body may have (16 MiB, the bound `clazel-ipc`'s
/// `Submit` carries): a request with a longer body is not built.
pub open spec fn max_request_body() -> nat {
    0x100_0000
}

/// A request this client builds: a navigation method, no body on `GET`, and
/// a body of at most [`max_request_body`] octets.
pub open spec fn req_ok(req: Req) -> bool {
    is_navigation_method(req.method) && (req.method == lit_get() ==> req.body is None)
        && (match req.body {
        Some(p) => p.bytes.len() <= max_request_body(),
        None => true,
    })
}

/// The decimal digits of `n`, as octets (Fetch: "serialized and isomorphic
/// encoded"; URL's "serialize an integer").
pub open spec fn decimal_octets(n: nat) -> Seq<u8> {
    clazel_url::host::spec::serialize_integer(n).map_values(|c: u32| c as u8)
}

/// The octets of the body, none if it is null.
pub open spec fn body_bytes(req: Req) -> Seq<u8> {
    match req.body {
        Some(p) => p.bytes,
        None => Seq::<u8>::empty(),
    }
}

/// Fetch §4.6 steps 6 to 9 (and the `Content-Type` the body's extraction
/// set): the field lines the body adds. A body adds `Content-Type` and
/// `Content-Length`; a `POST` without a body adds `Content-Length: 0`;
/// anything else adds none.
pub open spec fn body_field_lines(req: Req) -> Seq<clazel_http::field::spec::FieldLine> {
    match req.body {
        Some(p) => seq![
            clazel_http::field::spec::FieldLine { name: lit_content_type(), value: p.content_type },
            clazel_http::field::spec::FieldLine { name: lit_content_length(), value: decimal_octets(p.bytes.len()) },
        ],
        None => if req.method == lit_post() {
            seq![clazel_http::field::spec::FieldLine { name: lit_content_length(), value: decimal_octets(0) }]
        } else {
            seq![]
        },
    }
}

/// "append a request `Origin` header" step 4.1 and "serializing a request
/// origin" (see the modelling choices): the value `Origin` would have for a
/// request for `url`, or `None` if it is not ASCII.
pub open spec fn origin_value(url: clazel_url::url::spec::Url, req: Req) -> Option<Seq<u8>> {
    match req.initiator {
        None => Some(lit_null()),
        Some(o) => if req.origin_tainted {
            Some(lit_null())
        } else {
            match o {
                clazel_origin::spec::Origin::Tuple { scheme, .. } => if scheme == clazel_url::url::spec::https_str() && url.scheme != clazel_url::url::spec::https_str() {
                    Some(lit_null())
                } else {
                    ascii_octets(clazel_origin::spec::serialization_of_origin(o))
                },
                clazel_origin::spec::Origin::Opaque(_) => Some(lit_null()),
            }
        },
    }
}

/// "append a request `Origin` header" for a request for `url`: none for
/// `GET` or `HEAD` (step 4), else one `Origin` field line (step 4.2), or
/// `None` if the value is not ASCII.
pub open spec fn origin_field_lines(url: clazel_url::url::spec::Url, req: Req) -> Option<Seq<clazel_http::field::spec::FieldLine>> {
    if req.method == lit_get() || req.method == lit_head() {
        Some(seq![])
    } else {
        match origin_value(url, req) {
            Some(v) => Some(seq![clazel_http::field::spec::FieldLine { name: lit_origin(), value: v }]),
            None => None,
        }
    }
}

/// The request for `url` with the method, body and `Origin` of `req`:
/// [`request_for`]'s fields, then [`body_field_lines`] and
/// [`origin_field_lines`]; `None` if this client does not fetch it.
pub open spec fn request_for_req(url: clazel_url::url::spec::Url, req: Req) -> Option<clazel_http::message::spec::Request> {
    match (request_for(url), origin_field_lines(url, req)) {
        (Some(r), Some(of)) => if req_ok(req) {
            Some(clazel_http::message::spec::Request { method: req.method, target: r.target, fields: r.fields + body_field_lines(req) + of })
        } else {
            None
        },
        _ => None,
    }
}

/// [`request_for_req`] carrying the cookie-string `cookie` (Fetch §4.6
/// step 22.1: the last field).
pub open spec fn request_for_req_cookie(url: clazel_url::url::spec::Url, req: Req, cookie: Seq<u8>) -> Option<clazel_http::message::spec::Request> {
    match request_for_req(url, req) {
        Some(r) => Some(clazel_http::message::spec::Request { method: r.method, target: r.target, fields: r.fields + cookie_field_lines(cookie) }),
        None => None,
    }
}

/// The bytes sent: the serialized head (RFC 9112 §2.1, §3) when it is
/// valid, then the body's octets (§6.2).
pub open spec fn request_bytes_req_cookie(url: clazel_url::url::spec::Url, req: Req, cookie: Seq<u8>) -> Option<Seq<u8>> {
    match request_for_req_cookie(url, req, cookie) {
        Some(r) => if clazel_http::message::spec::is_valid_request(r) {
            Some(clazel_http::message::spec::serialize_request(r) + body_bytes(req))
        } else {
            None
        },
        None => None,
    }
}

/// The bytes sent with no cookies: [`request_bytes_req_cookie`] with the
/// empty cookie-string.
pub open spec fn request_bytes_req(url: clazel_url::url::spec::Url, req: Req) -> Option<Seq<u8>> {
    request_bytes_req_cookie(url, req, Seq::<u8>::empty())
}

/// HTTP-redirect fetch step 12: "If one of the following is true:
/// internalResponse's status is 301 or 302 and request's method is `POST`;
/// internalResponse's status is 303 and request's method is not `GET` or
/// `HEAD`; then: 12.1 Set request's method to `GET` and request's body to
/// null. 12.2 For each headerName of request-body-header name, delete
/// headerName from request's header list." (RFC 9110 §15.4.2, §15.4.3,
/// §15.4.4: 301 and 302 may change `POST` to `GET`, 303 does; §15.4.8 and
/// §15.4.9: 307 and 308 "MUST NOT change the request method".) The deleted
/// header names are derived from the body (see the modelling choices). The
/// redirect-taint is updated by the caller.
pub open spec fn rewrite_for_redirect(status: nat, req: Req) -> Req {
    if (status == 301 || status == 302) && req.method == lit_post() || status == 303 && req.method != lit_get() && req.method != lit_head() {
        Req { method: lit_get(), body: None, ..req }
    } else {
        req
    }
}

/// The cookie request context's "safe method" bit for `req` (RFC 6265bis
/// §5.2's "method is safe", RFC 9110 §9.2.1).
pub open spec fn method_is_safe(req: Req) -> bool {
    is_safe_method(req.method)
}

} // verus!
