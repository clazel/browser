//! The fetch functions of the shipped kernel (phase-3.md item 3.7), until
//! item 3.6's transducer is joined to them.
//!
//! The kernel takes the fetch as a parameter ([`FetchFns`], as it takes
//! [`UrlFns`]): `run(url, net)` is the fetch of `url` given the octets the
//! network shell delivered. [`stub_fetch`] is the stand-in the host shell
//! uses while it has no network (and the tests use): the response is the
//! octets themselves, as the body of a document at the URL asked for, with
//! no redirect and no cookie. Every theorem of the kernel holds for every
//! `FetchFns`, so the stand-in is not trusted with anything; the join of the
//! real client replaces it (`exec::fetch::FetchFnsExec`) and changes no
//! theorem, only the instantiation.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The stand-in fetch: `Done` with the URL asked for and the octets as the
/// body, and no `Set-Cookie` line.
pub open spec fn stub_fetch() -> FetchFns {
    FetchFns { run: |url: Seq<u32>, net: Seq<u8>| FetchRun { result: FetchResult::Done { url, body: net }, stores: Seq::<HttpStore>::empty() } }
}

} // verus!
