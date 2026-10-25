//! The exec counterpart of [`crate::spec::FetchFns`] (item 3.7): a trait whose
//! method is proven equal to the spec's `run`, so the kernel's proof holds
//! for any implementation and never unfolds the HTTP client. [`StubFetch`] is
//! the stand-in ([`crate::fetch::stub_fetch`]) the shipped kernel runs with
//! until item 3.6's transducer is joined.
//!
//! The records are the exec forms of what a fetch gives: a result, and the
//! `Set-Cookie` lines of its responses with the request each answers (the
//! exec request URL and context of `clazel-cookie`, the same the kernel's
//! cookie calls use).

#[allow(unused_imports)]
use super::spec::*;
use clazel_cookie::storage::exec::{RequestContextRecord, RequestUrlRecord};
use clazel_url::host::record::copy;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What the network shell reports, viewed as [`NetOutcome`].
pub struct NetOutcomeRecord {
    /// The URL the fetch was started for.
    pub url: Vec<u32>,
    /// What the network delivered.
    pub net: Vec<u8>,
}

impl View for NetOutcomeRecord {
    type V = NetOutcome;

    open spec fn view(&self) -> NetOutcome {
        NetOutcome { url: self.url@, net: self.net@ }
    }
}

/// How a fetch ended, viewed as [`FetchResult`].
pub enum FetchResultRecord {
    /// The response: the final URL and the body.
    Done {
        /// The final URL.
        url: Vec<u32>,
        /// The body.
        body: Vec<u8>,
    },
    /// The fetch failed.
    Failed,
}

impl View for FetchResultRecord {
    type V = FetchResult;

    open spec fn view(&self) -> FetchResult {
        match self {
            FetchResultRecord::Done { url, body } => FetchResult::Done { url: url@, body: body@ },
            FetchResultRecord::Failed => FetchResult::Failed,
        }
    }
}

/// One `Set-Cookie` line of a response and the request it answers, viewed as
/// [`HttpStore`].
pub struct HttpStoreRecord {
    /// The `Set-Cookie` field value.
    pub line: Vec<u8>,
    /// The request's URL (scheme, canonical host and path).
    pub url: RequestUrlRecord,
    /// The request's context.
    pub ctx: RequestContextRecord,
}

impl View for HttpStoreRecord {
    type V = HttpStore;

    open spec fn view(&self) -> HttpStore {
        HttpStore { line: self.line@, url: self.url@, ctx: self.ctx@ }
    }
}

/// The view of a list of stores.
pub open spec fn stores_view(v: Seq<HttpStoreRecord>) -> Seq<HttpStore> {
    v.map_values(|s: HttpStoreRecord| s@)
}

/// What running a fetch gives, viewed as [`FetchRun`].
pub struct FetchRunRecord {
    /// How it ended.
    pub result: FetchResultRecord,
    /// The `Set-Cookie` lines of the responses of the chain.
    pub stores: Vec<HttpStoreRecord>,
}

impl View for FetchRunRecord {
    type V = FetchRun;

    open spec fn view(&self) -> FetchRun {
        FetchRun { result: self.result@, stores: stores_view(self.stores@) }
    }
}

/// The fetch of the kernel: an exec function whose result is that of the
/// spec function of [`FetchFnsExec::fetch`].
pub trait FetchFnsExec {
    /// The spec the method implements.
    spec fn fetch(&self) -> FetchFns;

    /// [`FetchFns::run`].
    fn run(&self, url: &[u32], net: &[u8]) -> (r: FetchRunRecord)
        ensures
            r@ == (self.fetch().run)(url@, net@),
    ;
}

/// The stand-in fetch: the octets are the body of a document at the URL
/// asked for ([`crate::fetch::stub_fetch`]).
pub struct StubFetch;

impl FetchFnsExec for StubFetch {
    open spec fn fetch(&self) -> FetchFns {
        crate::fetch::stub_fetch()
    }

    fn run(&self, url: &[u32], net: &[u8]) -> (r: FetchRunRecord) {
        let body = vstd::slice::slice_to_vec(net);
        let stores: Vec<HttpStoreRecord> = Vec::new();
        let r = FetchRunRecord { result: FetchResultRecord::Done { url: copy(url), body }, stores };
        proof {
            assert(stores_view(r.stores@) =~= Seq::<HttpStore>::empty());
        }
        r
    }
}

} // verus!
