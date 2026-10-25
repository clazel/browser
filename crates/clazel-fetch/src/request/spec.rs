//! Executable-style specification of the request a client sends for a
//! URL, and of which responses are interim. Nothing here runs.
//!
//! Sources (pinned; an RFC never changes after publication):
//! - RFC 9112 "HTTP/1.1", June 2022, §3.2.1 origin form;
//! - RFC 9110 "HTTP Semantics", June 2022, §4.2.1 the `http` URI scheme,
//!   §4.2.4 deprecated userinfo, §7.2 `Host`, §7.6.1 `Connection`, §12.5.1
//!   `Accept`, §10.1.5 `User-Agent`, §15.2 informational responses;
//! - the URL Standard (as transcribed in `clazel_url`): the URL record,
//!   the URL path serializer, the host serializer and "serialize an
//!   integer".
//!
//! Modelling choices (each a choice of ours or a deviation in form, never
//! in meaning):
//! - Only `http:` URLs are fetched (TLS is not built yet), only with GET,
//!   and one request per connection, so every request carries
//!   `Connection: close` (§7.6.1) and the response may be close-delimited.
//! - The fields sent, in this order: `Host` (§7.2: "A user agent MUST
//!   generate a Host header field in a request"), `Connection: close`,
//!   `Accept: */*` (§12.5.1) and `User-Agent: clazel` (§10.1.5). No
//!   `Accept-Encoding`, so a conforming server sends identity content.
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

/// The request for `url`, or `None` if this client does not fetch it.
pub open spec fn request_for(url: clazel_url::url::spec::Url) -> Option<clazel_http::message::spec::Request> {
    if url.scheme != clazel_url::url::spec::http_str() || url.username.len() > 0 || url.password.len() > 0 {
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

/// Where to connect for `url`: the host as the resolver takes it (the
/// host serializer's output) and the port, the URL's or the scheme's
/// default (RFC 9110 §4.2.1: "If the port subcomponent is empty or not
/// given, TCP port 80 ... is the default").
pub open spec fn connect_to(url: clazel_url::url::spec::Url) -> Option<(Seq<u8>, nat)> {
    match url.host {
        Some(host) => match ascii_octets(clazel_url::host::spec::host_serializer(host)) {
            Some(h) => Some((h, match url.port {
                Some(p) => p,
                None => 80,
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

} // verus!
