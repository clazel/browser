//! The exec counterpart of [`crate::spec::UrlFns`]: a trait whose methods are
//! each proven equal to the spec function of the same name, so the kernel's
//! proof holds for any implementation and never unfolds the URL parser.
//! Item 2.13 implements it with the real parser (`real_urls::RealUrls`).

use clazel_origin::exec::ParsedOrigin;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The view of an optional exec origin.
pub open spec fn origin_opt_view(o: Option<ParsedOrigin>) -> Option<clazel_origin::spec::Origin> {
    match o {
        Some(o) => Some(o@),
        None => None,
    }
}

/// The view of an optional string of code points.
pub open spec fn code_points_opt_view(o: Option<Vec<u32>>) -> Option<Seq<u32>> {
    match o {
        Some(v) => Some(v@),
        None => None,
    }
}

/// The URL functions of the kernel: four exec functions whose results are
/// those of the spec functions of [`UrlFnsExec::urls`].
pub trait UrlFnsExec {
    /// The spec the methods implement.
    spec fn urls(&self) -> crate::spec::UrlFns;

    /// [`crate::spec::UrlFns::origin_of`].
    fn origin_of(&self, url: &[u32]) -> (r: Option<ParsedOrigin>)
        ensures
            origin_opt_view(r) == (self.urls().origin_of)(url@),
    ;

    /// [`crate::spec::UrlFns::is_javascript`] (item 7.16).
    fn is_javascript(&self, url: &[u32]) -> (r: bool)
        ensures
            r == (self.urls().is_javascript)(url@),
    ;

    /// [`crate::spec::UrlFns::path_of`].
    fn path_of(&self, url: &[u32]) -> (r: Vec<u8>)
        ensures
            r@ == (self.urls().path_of)(url@),
    ;

    /// [`crate::spec::UrlFns::resolve`].
    fn resolve(&self, base: &[u32], input: &[u32]) -> (r: Option<Vec<u32>>)
        ensures
            code_points_opt_view(r) == (self.urls().resolve)(base@, input@),
    ;
}

} // verus!
