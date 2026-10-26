//! The transducer's parameters joined to the real functions (phase-3.md
//! item 3.6, last part, as item 2.13 joined the kernel's `UrlFns`):
//! [`real_http`] is `clazel-http`'s response parser for a GET request, and
//! [`real_urls`] parses a `Location` value with `clazel-url`'s basic URL
//! parser. [`RealHttp`] and [`RealUrls`] implement the exec traits, each
//! method proven equal to them, and [`step_real`] is the `step` the
//! network shell runs.
//!
//! Every theorem of `theorems.rs` holds for every `HttpFns` and `UrlFns`,
//! so it holds of these without change. `theorem_split_invariant` needs
//! its parser to be `prefix_stable`: [`theorem_real_prefix_stable`] proves
//! that of [`real_http`] from `clazel-http`'s
//! `lemma_parse_response_append`, and [`theorem_real_split_invariant`] is
//! the split theorem for the shipped client.
//!
//! [`RealHttp`] keeps one `clazel-http` `ResponseParser` per connection in
//! the reading state and feeds it each octet once (`HttpFnsExec::feed`),
//! so a fetch is linear in the response's size; the parser's invariant is
//! its `wf`, for a request that is not `HEAD`.
//!
//! # Modelling choices
//!
//! - **The request is a GET**, so `request_is_head` is false.
//! - **The `Location` value's octets are UTF-8 decoded** (Encoding §6
//!   "UTF-8 decode without BOM", errors replaced by U+FFFD) before the URL
//!   parser. Fetch passes the header value to the URL parser without
//!   saying how octets become code points; UTF-8 is what browsers do with
//!   a non-ASCII `Location`, and it makes the input a scalar value string,
//!   as the URL parser requires (`lemma_hooks_scalar`). On ASCII it is the
//!   identity, so it decides nothing for a value RFC 9110 §10.2.2 allows.
//! - **"Parsing" is the basic URL parser** (URL §4.4) with the request's
//!   URL as base: the URL Standard's API-level "URL parser" adds only the
//!   blob URL entry, which no HTTP(S) URL has.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::contract::{HttpFnsExec, UrlFnsExec};
use super::types::{ActionBuf, InputBuf, JarOpBuf, StateBuf};
use clazel_cookie::matching::exec::canonicalize_a_host_name;
use clazel_cookie::storage::exec::CookieRecord;
use clazel_cookie::storage::exec::{RequestUrlRecord, narrow_exec};
use clazel_encoding::utf8::decode::decode_without_bom;
use clazel_http::message::body::ResponseParser;
use clazel_http::message::types::ParseBuf;
use clazel_origin::exec::{ParsedOrigin, url_origin_exec};
use clazel_url::url::parse::basic_url_parser;
use clazel_url::url::record::ParsedUrl;
use clazel_url::url::serialize::url_path_serializer;

verus! {

/// The HTTP functions of the shipped client: the response parser, for a
/// request that is not `HEAD`.
pub open spec fn real_http() -> HttpFns {
    HttpFns {
        parse: |received: Seq<u8>| clazel_http::message::spec::parse_response(received, false),
        parse_at_close: |received: Seq<u8>| clazel_http::message::spec::parse_response_at_close(received, false),
    }
}

/// Fetch §2.2.6 step 3 with the real parser: `value`, UTF-8 decoded,
/// parsed with `base` as the base URL.
pub open spec fn real_location(base: Url, value: Seq<u8>) -> Option<Url> {
    clazel_url::url::spec::basic_url_parser(
        clazel_encoding::utf8::spec::utf8_decode_without_bom(value),
        Some(base),
        clazel_url::url::contract::url_domain_parser(),
    )
}

/// The URL functions of the shipped client.
pub open spec fn real_urls() -> UrlFns {
    UrlFns {
        location: |base: Url, value: Seq<u8>| real_location(base, value),
        // URL §4.7 "origin" with the real domain parser; the opaque origin
        // id of a URL with none is 0 (no HTTP(S) URL has one).
        origin: |url: Url| clazel_origin::spec::url_origin(url, clazel_url::url::contract::url_domain_parser(), 0),
        request_url: |url: Url| request_url(url),
        rules: clazel_psl::table::psl_rules(),
    }
}

/// The shipped parser is prefix-stable
/// (`super::contract::real_prefix_stable`): `clazel-http`'s append lemma
/// for `parse_response` is the statement, for a request that is not `HEAD`.
pub proof fn theorem_real_prefix_stable()
    ensures
        super::contract::real_prefix_stable(),
{
    assert forall|input: Seq<u8>, more: Seq<u8>| #![trigger (real_http().parse)(input), (real_http().parse)(input + more)] match (real_http().parse)(input) {
        clazel_http::message::spec::Parse::Done { response, rest } => (real_http().parse)(input + more)
            == (clazel_http::message::spec::Parse::Done { response: response, rest: rest + more }),
        clazel_http::message::spec::Parse::Invalid => (real_http().parse)(input + more) is Invalid,
        clazel_http::message::spec::Parse::Unsupported => (real_http().parse)(input + more) is Unsupported,
        clazel_http::message::spec::Parse::Incomplete => true,
    } by {
        clazel_http::message::lemmas::lemma_parse_response_append(input, more, false);
    }
}

/// The split does not matter for the shipped client
/// (`super::contract::split_invariant` with [`real_http`] and
/// [`real_urls`]), for every state and split.
pub proof fn theorem_real_split_invariant(s: State, a: Seq<u8>, b: Seq<u8>, jar: Seq<Cookie>, now: int)
    ensures
        super::contract::split_invariant(real_http(), real_urls(), s, a, b, jar, now),
{
    theorem_real_prefix_stable();
    super::theorems::theorem_split_invariant(real_http(), real_urls(), s, a, b, jar, now);
}

/// `request_url` (RFC 6265bis §5.7, §5.8's view of the URL).
pub fn request_url_exec(url: &ParsedUrl) -> (r: RequestUrlRecord)
    ensures
        r@ == request_url(url@),
{
    let scheme = narrow_exec(url.scheme.as_slice());
    let host = canonicalize_a_host_name(&url.host);
    let mut p = url_path_serializer(&url.path);
    if p.is_empty() {
        p.push(0x2F);
        assert(p@ =~= seq![0x2Fu32]);
    }
    let path = narrow_exec(p.as_slice());
    RequestUrlRecord { scheme, host, path }
}

/// [`real_http`], executable.
pub struct RealHttp;

impl HttpFnsExec for RealHttp {
    open spec fn http(&self) -> HttpFns {
        real_http()
    }

    /// `clazel-http`'s invariant, for a request that is not `HEAD`.
    open spec fn parser_ok(&self, p: &ResponseParser) -> bool {
        p.wf() && !p.head()
    }

    fn new_parser(&self) -> (p: ResponseParser) {
        ResponseParser::new(false)
    }

    fn feed(&self, p: &mut ResponseParser, bytes: &[u8]) -> (r: ParseBuf) {
        p.feed(bytes)
    }

    fn parse_at_close(&self, p: ResponseParser) -> (r: ParseBuf) {
        p.close()
    }
}

/// [`real_urls`], executable.
pub struct RealUrls;

impl UrlFnsExec for RealUrls {
    open spec fn urls(&self) -> UrlFns {
        real_urls()
    }

    proof fn rules_are_psl(&self) {
    }

    fn request_url(&self, url: &ParsedUrl) -> (r: RequestUrlRecord) {
        request_url_exec(url)
    }

    fn origin(&self, url: &ParsedUrl) -> (r: ParsedOrigin) {
        url_origin_exec(url, 0)
    }

    fn location(&self, base: &ParsedUrl, value: &[u8]) -> (r: Option<ParsedUrl>) {
        let input = decode_without_bom(value);
        proof {
            clazel_encoding::utf8::lemmas::lemma_hooks_scalar(value@);
        }
        basic_url_parser(input.as_slice(), Some(base))
    }
}

/// The transducer's `step` with the real functions: what the network
/// shell and the kernel call. The caller applies the jar operations it
/// returns to its jar (`super::step::apply_ops_exec`).
pub fn step_real(s: StateBuf, input: &InputBuf, jar: &[CookieRecord], now: u64) -> (out: (StateBuf, Vec<ActionBuf>, Vec<JarOpBuf>))
    requires
        super::contract::step_requires(s@),
        super::contract::state_ok(&RealHttp, &s),
        super::contract::jar_requires(clazel_cookie::storage::exec::jar_view(jar@), now as int),
    ensures
        super::contract::step_ensures(
            real_http(),
            real_urls(),
            s@,
            input@,
            clazel_cookie::storage::exec::jar_view(jar@),
            now as int,
            out.0@,
            super::types::actions_view(out.1@),
            super::types::ops_view(out.2@),
        ),
        super::contract::step_requires(out.0@),
        super::contract::state_ok(&RealHttp, &out.0),
        super::contract::ops_at(super::types::ops_view(out.2@), now as int),
{
    super::step::step(&RealHttp, &RealUrls, s, input, jar, now)
}

} // verus!
