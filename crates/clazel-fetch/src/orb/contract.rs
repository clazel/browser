//! Contracts the executable ORB functions must be proven to meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `opaque_response_safelist_check(&ResponseBuf) -> Verdict`:
/// the verdict of [`opaque_response_safelist_check`] on the response's view.
pub open spec fn safelist_check_ensures(response: clazel_http::message::spec::Response, output: Verdict) -> bool {
    output == opaque_response_safelist_check(response)
}

/// Contract for `extract_a_mime_type(&[FieldLineBuf]) -> Option<MimeType>`.
pub open spec fn extract_ensures(fields: Seq<clazel_http::field::spec::FieldLine>, output: Option<clazel_mime::mime_type::spec::MimeTypeRecord>) -> bool {
    output == extract_a_mime_type(fields)
}

/// Contract for `determine_nosniff(&[FieldLineBuf]) -> bool`.
pub open spec fn nosniff_ensures(fields: Seq<clazel_http::field::spec::FieldLine>, output: bool) -> bool {
    output == determine_nosniff(fields)
}

} // verus!
