//! The exec counterpart of [`crate::spec::FetchFns`] (item 3.7): a trait whose
//! methods are proven equal to the spec's, so the kernel's proof holds for any
//! implementation and never unfolds the HTTP client or the URL parser. The
//! shipped kernel runs with `real_urls::RealFetch`, joined to `clazel-fetch`'s
//! `RealHttp` and `RealUrls`.
//!
//! The kernel steps the transducer of `clazel-fetch` itself, so the trait
//! hands out that crate's exec parameters (`H` and `U`) and adds the one
//! function the transducer does not have: the parser of a navigation URL.

#[allow(unused_imports)]
use super::spec::*;
use clazel_fetch::transducer::contract::{HttpFnsExec, UrlFnsExec};
use clazel_url::url::record::ParsedUrl;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The transducer's parameters of the kernel, executable: each is proven
/// equal to the spec of [`FetchFnsExec::fetch`].
pub trait FetchFnsExec {
    /// The response parser.
    type H: HttpFnsExec;
    /// The URL-side functions.
    type U: UrlFnsExec;

    /// The spec the methods implement.
    spec fn fetch(&self) -> FetchFns;

    /// What a navigation's transducer state keeps between steps: the
    /// parser invariant of [`FetchFnsExec::http_fns`]
    /// (`clazel_fetch::transducer::contract::state_ok`), stated without an
    /// instance so that the kernel's state invariant is a spec.
    spec fn nav_ok(s: &clazel_fetch::transducer::types::StateBuf) -> bool;

    /// A state that is not reading keeps it, whatever the parser (as every
    /// state `start` gives).
    proof fn nav_ok_idle(s: &clazel_fetch::transducer::types::StateBuf)
        requires
            !(s.phase is Reading),
        ensures
            Self::nav_ok(s),
    ;

    /// The HTTP functions: [`FetchFns::http`].
    fn http_fns(&self) -> (r: &Self::H)
        ensures
            r.http() == self.fetch().http,
            forall|s: &clazel_fetch::transducer::types::StateBuf| #[trigger] clazel_fetch::transducer::contract::state_ok(r, s) == Self::nav_ok(s),
    ;

    /// The URL functions of the transducer: [`FetchFns::urls`].
    fn url_fns(&self) -> (r: &Self::U)
        ensures
            r.urls() == self.fetch().urls,
    ;

    /// [`FetchFns::parse`].
    fn parse(&self, url: &[u32]) -> (r: Option<ParsedUrl>)
        ensures
            clazel_url::url::record::opt_url_view(r) == (self.fetch().parse)(url@),
    ;
}

} // verus!
