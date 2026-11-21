//! Contracts the executable ORB functions must be proven to meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `extract_mime_type_exec(&[FieldLineBuf]) -> Option<MimeType>`.
pub open spec fn extract_mime_type_ensures(fields: Seq<clazel_http::field::spec::FieldLine>, output: Option<clazel_mime::mime_type::spec::MimeTypeRecord>) -> bool {
    output == extract_mime_type(fields)
}

/// Contract for `determine_nosniff_exec(&[FieldLineBuf]) -> bool`.
pub open spec fn determine_nosniff_ensures(fields: Seq<clazel_http::field::spec::FieldLine>, output: bool) -> bool {
    output == determine_nosniff(fields)
}

/// Contract for `safelist_check_exec(&ResponseBuf) -> bool`, which is the
/// check with [`kernel_model`].
pub open spec fn safelist_check_ensures(response: clazel_http::message::spec::Response, output: bool) -> bool {
    output == opaque_response_safelist_check(kernel_model(), response.status_line.status, response.fields, response.body)
}

/// Contract for `orb_allows_exec(bool, &ResponseBuf) -> bool`:
/// [`orb_allows_given`].
pub open spec fn orb_allows_ensures(applies: bool, response: clazel_http::message::spec::Response, output: bool) -> bool {
    output == orb_allows_given(applies, response)
}

} // verus!
