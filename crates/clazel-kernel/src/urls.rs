//! The kernel's URL functions instantiated with the real URL parser (phase-2.md
//! item 2.13): [`real_urls`] is a [`UrlFns`] built from `clazel-url`'s basic
//! URL parser (URL §4.4), its URL serializer (§4.5) and path serializer, and
//! `clazel-origin`'s URL origin (§4.7), with `clazel-idna`'s domain parser
//! (through `clazel_url::url::contract::url_domain_parser`, as `host_parser_full`
//! joined it in item 1.9).
//!
//! Every theorem of items 2.10 to 2.12 is proven for **every** [`UrlFns`], so it
//! holds of this one without change. This file only says which one the
//! shipped kernel runs.
//!
//! Where it lives: in `clazel-kernel`, which already depends on `clazel-url`,
//! `clazel-origin`, `clazel-cookie` (for `narrow`) and `clazel-encoding`. The
//! parser, serializers and origin know nothing of the kernel, and the kernel
//! proof (`spec`, `invariant`, `theorems`, ...) never imports this module, so
//! the dependency runs one way: kernel proof, then the trait [`UrlFns`] /
//! `UrlFnsExec`, with this module and `exec::real_urls` as the one instantiation.
//! A new crate would add nothing but a `Cargo.lock` row.
//!
//! # Modelling choices
//!
//! - **Parse failure.** `origin_of` of a string that does not parse is `None`
//!   (so the kernel refuses the URL: an `OpenTab`/`NavigateTab` is ignored and
//!   a renderer's `Navigate` gets `error_bad_url`). `path_of` of such a string
//!   is the empty path (the kernel only reads `path_of` of a URL it committed,
//!   which parsed). `resolve(base, input)` is `None` if `base` does not parse
//!   (with no base), or `input` does not parse against it; the base is parsed
//!   first, as `new URL(input, base)` does.
//! - **The parser takes a scalar value string** (URL §4.4: "The basic URL
//!   parser takes a scalar value string input"), but the kernel's functions
//!   are total on `Seq<u32>`. A string with a code point that is not a scalar
//!   value (a surrogate or above U+10FFFF) is treated as a string that does
//!   not parse: every function fails on it as on a parse failure. The text
//!   a renderer or the user sends is decoded from UTF-8 (item 2.3), so it
//!   is always scalar; the guard makes the functions total.
//! - **`resolve` returns scalar value strings** ([`urls_resolve_scalar`]
//!   of the kernel's contract). The serialization of a parsed URL always is
//!   (every non-ASCII code point of the input is percent-encoded, or
//!   punycoded in a domain), but that is a property of the whole parser that
//!   is **not proven** here: the result is guarded, and a serialization with a
//!   code point that is not a scalar value would count as a parse failure.
//!   The guard never fires on the WPT `urltestdata.json` rows or on fuzzed
//!   inputs (`tests/conformance_urls.rs`). So `urls_resolve_scalar` holds of
//!   [`real_urls`] by construction ([`lemma_real_urls_resolve_scalar`]), not by
//!   an argument about the parser.
//! - **Opaque origins.** `origin_of` passes the new opaque origin's id `0`
//!   to `url_origin`: the kernel replaces any opaque id it is given with the
//!   renderer's own (`lock_of_origin`), so the number is never read.
//! - **`path_of` is the octets of the path serialization** (URL §4.5 URL path
//!   serializing), `narrow` of it, which is exact on ASCII. That a parsed URL's
//!   path serialization is ASCII (the path percent-encode set covers every
//!   non-ASCII code point) is, like the above, a property of the parser that
//!   is not proven here; `tests/conformance_urls.rs` checks it on the WPT rows.
//! - **The pieces are split from the guards** (`*_scalar`) so that Verus's
//!   `compute_only` can evaluate them on concrete strings: `all_scalar_values`
//!   is a quantifier. The kill certificates of `mutations.json` use them.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The URL §3.3 domain parser the real instantiation runs: `clazel-idna`'s.
pub open spec fn real_domain_parser() -> clazel_url::host::spec::DomainParser {
    clazel_url::url::contract::url_domain_parser()
}

/// The id passed to `url_origin` as "a new opaque origin"; the kernel ignores
/// it ([`lock_of_origin`]).
pub open spec fn fresh_opaque_id() -> nat {
    0
}

/// URL §4.4 "basic URL parser" on a scalar value string `input`, with no base
/// (null) and no url or state override: what parsing an absolute URL string
/// means. `None` is failure.
pub open spec fn parse_absolute(dp: clazel_url::host::spec::DomainParser, input: Seq<u32>) -> Option<clazel_url::url::spec::Url> {
    clazel_url::url::spec::basic_url_parser(input, None, dp)
}

/// `origin_of` on a scalar value string: URL §4.7 "origin" of the parsed URL,
/// or `None` if it does not parse.
pub open spec fn origin_of_scalar(dp: clazel_url::host::spec::DomainParser, input: Seq<u32>) -> Option<clazel_origin::spec::Origin> {
    match parse_absolute(dp, input) {
        Some(url) => Some(clazel_origin::spec::url_origin(url, dp, fresh_opaque_id())),
        None => None,
    }
}

/// `path_of` on a scalar value string: the octets of URL §4.5 "URL path
/// serializing" the parsed URL's path, or the empty path if it does not parse.
pub open spec fn path_of_scalar(dp: clazel_url::host::spec::DomainParser, input: Seq<u32>) -> Seq<u8> {
    match parse_absolute(dp, input) {
        Some(url) => clazel_cookie::matching::spec::narrow(clazel_url::url::spec::url_path_serializer(url.path)),
        None => seq![],
    }
}

/// `resolve` on scalar value strings: parse `base` (no base), parse `input`
/// with `base` as its base URL, and URL §4.5 serialize the result (with
/// exclude fragment false); `None` if either fails.
pub open spec fn resolve_scalar(dp: clazel_url::host::spec::DomainParser, base: Seq<u32>, input: Seq<u32>) -> Option<Seq<u32>> {
    match parse_absolute(dp, base) {
        Some(b) => match clazel_url::url::spec::basic_url_parser(input, Some(b), dp) {
            Some(url) => Some(clazel_url::url::spec::url_serializer(url, false)),
            None => None,
        },
        None => None,
    }
}

/// The kernel's URL functions with the domain parser `dp`: the three
/// functions above, guarded to the strings the parser accepts as input and
/// (for `resolve`) to a scalar value result (see the modelling choices).
pub open spec fn urls_with(dp: clazel_url::host::spec::DomainParser) -> UrlFns {
    UrlFns {
        origin_of: |url: Seq<u32>| if clazel_encoding::utf8::spec::all_scalar_values(url) {
            origin_of_scalar(dp, url)
        } else {
            None
        },
        path_of: |url: Seq<u32>| if clazel_encoding::utf8::spec::all_scalar_values(url) {
            path_of_scalar(dp, url)
        } else {
            seq![]
        },
        resolve: |base: Seq<u32>, input: Seq<u32>| if clazel_encoding::utf8::spec::all_scalar_values(base)
            && clazel_encoding::utf8::spec::all_scalar_values(input) {
            match resolve_scalar(dp, base, input) {
                Some(href) => if clazel_encoding::utf8::spec::all_scalar_values(href) {
                    Some(href)
                } else {
                    None
                },
                None => None,
            }
        } else {
            None
        },
    }
}

/// The URL functions of the shipped kernel: [`urls_with`] the real domain
/// parser.
pub open spec fn real_urls() -> UrlFns {
    urls_with(real_domain_parser())
}

/// The fetch's parser of a navigation URL (item 3.7): the basic URL parser
/// with no base on a scalar value string, as [`parse_absolute`]; a string
/// with a code point that is not a scalar value does not parse (see the
/// modelling choices).
pub open spec fn real_parse(input: Seq<u32>) -> Option<clazel_url::url::spec::Url> {
    if clazel_encoding::utf8::spec::all_scalar_values(input) {
        parse_absolute(real_domain_parser(), input)
    } else {
        None
    }
}

/// The transducer's parameters of the shipped kernel (item 3.7): the real
/// response parser and URL functions of `clazel-fetch`, and [`real_parse`].
pub open spec fn real_fetch() -> FetchFns {
    FetchFns {
        http: clazel_fetch::transducer::real::real_http(),
        urls: clazel_fetch::transducer::real::real_urls(),
        parse: |input: Seq<u32>| real_parse(input),
    }
}

/// `resolve` returns scalar value strings, whatever the domain parser: the
/// condition [`crate::contract::urls_resolve_scalar`] that
/// `step_requires` puts on the URL functions. By construction of
/// [`urls_with`] (its result is guarded), not by an argument about the
/// parser; see the modelling choices.
pub proof fn lemma_urls_with_resolve_scalar(dp: clazel_url::host::spec::DomainParser)
    ensures
        crate::contract::urls_resolve_scalar(urls_with(dp)),
{
    let urls = urls_with(dp);
    assert forall|base: Seq<u32>, input: Seq<u32>| match #[trigger] (urls.resolve)(base, input) {
        Some(u) => clazel_encoding::utf8::spec::all_scalar_values(u),
        None => true,
    } by {
        let _ = (urls.resolve)(base, input);
    }
}

/// [`crate::contract::urls_resolve_scalar`] of the real URL functions: what
/// the exec `step_real` needs of them.
pub proof fn lemma_real_urls_resolve_scalar()
    ensures
        crate::contract::urls_resolve_scalar(real_urls()),
{
    lemma_urls_with_resolve_scalar(real_domain_parser());
}


} // verus!
