//! The real URL functions, executable (phase-2.md item 2.13): [`RealUrls`]
//! implements [`UrlFnsExec`] with `urls()` equal to
//! [`crate::urls::real_urls`], each method proven against it using the proven
//! exec parser (`clazel_url::url::parse::basic_url_parser`), the serializers
//! and `clazel_origin::exec::url_origin_exec`.
//!
//! [`step_real`] is the kernel's `step` with them: the function the host
//! shell (item 2.15) calls.

use clazel_origin::exec::{ParsedOrigin, url_origin_exec};
use clazel_url::url::parse::basic_url_parser;
use clazel_url::url::serialize::url_path_serializer;

use super::records::{EventRecord, StateRecord};
use super::step::step_exec;
use super::fetch::FetchFnsExec;
use super::urls::UrlFnsExec;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Whether `s` is a scalar value string.
pub fn all_scalar_values_exec(s: &[u32]) -> (r: bool)
    ensures
        r == clazel_encoding::utf8::spec::all_scalar_values(s@),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            forall|k: int| 0 <= k < i ==> clazel_encoding::utf8::spec::is_scalar_value(s@[k]),
        decreases s.len() - i,
    {
        match s.get(i) {
            Some(c) if *c > 0x10FFFF || (0xD800 <= *c && *c <= 0xDFFF) => {
                proof {
                    assert(!clazel_encoding::utf8::spec::is_scalar_value(s@[i as int]));
                }
                return false;
            },
            _ => {},
        }
        i = i.saturating_add(1);
    }
    true
}

/// `clazel_cookie::matching::spec::narrow`: the low octet of each code point.
fn narrow_exec(s: &[u32]) -> (r: Vec<u8>)
    ensures
        r@ == clazel_cookie::matching::spec::narrow(s@),
{
    let mut r: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            r@.len() == i,
            forall|k: int| 0 <= k < i ==> r@[k] == s@[k] as u8,
        decreases s.len() - i,
    {
        match s.get(i) {
            Some(c) => {
                r.push(*c as u8);
            },
            None => {
                return Vec::new();
            },
        }
        i = i.saturating_add(1);
    }
    proof {
        assert(r@ =~= clazel_cookie::matching::spec::narrow(s@));
    }
    r
}

/// The kernel's URL functions with the real parser: [`crate::urls::real_urls`].
pub struct RealUrls;

impl UrlFnsExec for RealUrls {
    open spec fn urls(&self) -> crate::spec::UrlFns {
        crate::urls::real_urls()
    }

    fn origin_of(&self, url: &[u32]) -> (r: Option<ParsedOrigin>) {
        if !all_scalar_values_exec(url) {
            return None;
        }
        match basic_url_parser(url, None) {
            None => None,
            Some(parsed) => {
                let origin = url_origin_exec(&parsed, 0);
                Some(origin)
            },
        }
    }

    fn path_of(&self, url: &[u32]) -> (r: Vec<u8>) {
        if !all_scalar_values_exec(url) {
            return Vec::new();
        }
        match basic_url_parser(url, None) {
            Some(parsed) => {
                let path = url_path_serializer(&parsed.path);
                narrow_exec(path.as_slice())
            },
            None => Vec::new(),
        }
    }

    fn resolve(&self, base: &[u32], input: &[u32]) -> (r: Option<Vec<u32>>) {
        if !all_scalar_values_exec(base) || !all_scalar_values_exec(input) {
            return None;
        }
        match basic_url_parser(base, None) {
            None => None,
            Some(b) => match basic_url_parser(input, Some(&b)) {
                None => None,
                Some(parsed) => {
                    let href = parsed.serialize(false);
                    if all_scalar_values_exec(href.as_slice()) {
                        Some(href)
                    } else {
                        None
                    }
                },
            },
        }
    }
}

/// The transducer's parameters of the shipped kernel ([`crate::urls::real_fetch`]):
/// `clazel-fetch`'s real response parser and URL functions, and the basic
/// URL parser on a navigation URL.
pub struct RealFetch {
    /// `clazel-fetch`'s response parser.
    pub http: clazel_fetch::transducer::real::RealHttp,
    /// `clazel-fetch`'s URL functions.
    pub urls: clazel_fetch::transducer::real::RealUrls,
}

impl FetchFnsExec for RealFetch {
    type H = clazel_fetch::transducer::real::RealHttp;
    type U = clazel_fetch::transducer::real::RealUrls;

    open spec fn fetch(&self) -> crate::spec::FetchFns {
        crate::urls::real_fetch()
    }

    open spec fn nav_ok(s: &clazel_fetch::transducer::types::StateBuf) -> bool {
        clazel_fetch::transducer::contract::state_ok(&clazel_fetch::transducer::real::RealHttp, s)
    }

    proof fn nav_ok_idle(s: &clazel_fetch::transducer::types::StateBuf) {
    }

    fn http_fns(&self) -> (r: &clazel_fetch::transducer::real::RealHttp) {
        &self.http
    }

    fn url_fns(&self) -> (r: &clazel_fetch::transducer::real::RealUrls) {
        &self.urls
    }

    fn parse(&self, url: &[u32]) -> (r: Option<clazel_url::url::record::ParsedUrl>) {
        if !all_scalar_values_exec(url) {
            return None;
        }
        basic_url_parser(url, None)
    }
}

/// The kernel's `step` with the real URL functions ([`RealUrls`]) and the
/// real transducer ([`RealFetch`]): the function the host shell calls. It
/// meets [`crate::contract::step_ensures`] for [`crate::urls::real_urls`] and
/// [`crate::urls::real_fetch`] under [`crate::contract::step_requires`],
/// whose URL condition `urls_resolve_scalar` is
/// [`crate::urls::lemma_real_urls_resolve_scalar`]'s.
pub fn step_real(s: StateRecord, e: &EventRecord) -> (out: (StateRecord, Vec<super::records::OutputRecord>))
    requires
        crate::contract::step_requires(crate::urls::real_urls(), crate::urls::real_fetch(), s@, e@),
        s.exec_wf::<RealFetch>(),
    ensures
        crate::contract::step_ensures(crate::urls::real_urls(), crate::urls::real_fetch(), s@, e@, super::step::result_view(out)),
        out.0.exec_wf::<RealFetch>(),
        clazel_cookie::storage::contract::jar_in_range(out.0@.jar),
        clazel_cookie::set_cookie::contract::now_in_range(out.0@.now),
        out.0@.next_id <= s@.next_id + 1,
        out.0@.next_conn <= s@.next_conn + 21,
{
    let fetch = RealFetch { http: clazel_fetch::transducer::real::RealHttp, urls: clazel_fetch::transducer::real::RealUrls };
    step_exec(&RealUrls, &fetch, s, e)
}

} // verus!
