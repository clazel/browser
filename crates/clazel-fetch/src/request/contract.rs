//! Contracts the executable request functions must be proven to meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `request_bytes(&ParsedUrl) -> Option<Vec<u8>>`.
pub open spec fn request_bytes_ensures(url: clazel_url::url::spec::Url, output: Option<Seq<u8>>) -> bool {
    output == request_bytes(url)
}

/// Contract for `request_bytes_cookie(&ParsedUrl, &[u8]) -> Option<Vec<u8>>`.
pub open spec fn request_bytes_cookie_ensures(url: clazel_url::url::spec::Url, cookie: Seq<u8>, output: Option<Seq<u8>>) -> bool {
    output == request_bytes_cookie(url, cookie)
}

/// Contract for `connect_to(&ParsedUrl) -> Option<(Vec<u8>, u16)>`.
pub open spec fn connect_to_ensures(url: clazel_url::url::spec::Url, output: Option<(Seq<u8>, nat)>) -> bool {
    output == connect_to(url)
}

/// Contract for `is_interim(u16) -> bool`.
pub open spec fn is_interim_ensures(status: nat, output: bool) -> bool {
    output == is_interim(status)
}

} // verus!
