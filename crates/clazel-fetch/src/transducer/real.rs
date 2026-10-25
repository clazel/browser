//! The transducer's parameters joined to the real functions (phase-3.md
//! item 3.6, last part, as item 2.13 joined the kernel's `UrlFns`):
//! [`real_http`] is `clazel-http`'s response parser for a GET request, and
//! [`real_urls`] parses a `Location` value with `clazel-url`'s basic URL
//! parser. [`RealHttp`] and [`RealUrls`] implement the exec traits, each
//! method proven equal to them, and [`step_real`] is the `step` the
//! network shell runs.
//!
//! Every theorem of `theorems.rs` holds for every `HttpFns` and `UrlFns`,
//! so it holds of these without change, except
//! `theorem_split_invariant`, whose hypothesis `prefix_stable` is **not
//! proven** of [`real_http`] (it needs the monotonicity of
//! `clazel_http::message::spec::parse_response`, stated in
//! `clazel_http::message::contract` but not proven, and slightly stronger:
//! see `prefix_stable`).
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
use super::types::{ActionBuf, InputBuf, StateBuf};
use clazel_encoding::utf8::decode::decode_without_bom;
use clazel_http::message::body::{parse_response_at_close_exec, parse_response_exec};
use clazel_http::message::types::ParseBuf;
use clazel_url::url::parse::basic_url_parser;
use clazel_url::url::record::ParsedUrl;

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
    UrlFns { location: |base: Url, value: Seq<u8>| real_location(base, value) }
}

/// [`real_http`], executable.
pub struct RealHttp;

impl HttpFnsExec for RealHttp {
    open spec fn http(&self) -> HttpFns {
        real_http()
    }

    fn parse(&self, received: &[u8]) -> (r: ParseBuf) {
        parse_response_exec(received, false)
    }

    fn parse_at_close(&self, received: &[u8]) -> (r: ParseBuf) {
        parse_response_at_close_exec(received, false)
    }
}

/// [`real_urls`], executable.
pub struct RealUrls;

impl UrlFnsExec for RealUrls {
    open spec fn urls(&self) -> UrlFns {
        real_urls()
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
/// shell calls.
pub fn step_real(s: StateBuf, input: &InputBuf) -> (out: (StateBuf, Vec<ActionBuf>))
    requires
        super::contract::step_requires(s@),
    ensures
        super::contract::step_ensures(real_http(), real_urls(), s@, input@, out.0@, super::types::actions_view(out.1@)),
        super::contract::step_requires(out.0@),
{
    super::step::step(&RealHttp, &RealUrls, s, input)
}

} // verus!
