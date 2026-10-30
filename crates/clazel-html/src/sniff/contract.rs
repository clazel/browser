//! Contracts the executable sniffing functions must be proven to meet, in
//! terms of [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `sniff(&[u8], Option<Encoding>) -> (Encoding, Confidence)`:
/// equals the encoding sniffing algorithm.
pub open spec fn sniff_ensures(
    bytes: Seq<u8>,
    transport: Option<clazel_encoding::labels::spec::Encoding>,
    output: (clazel_encoding::labels::spec::Encoding, Confidence),
) -> bool {
    output == sniff(bytes, transport)
}

/// Contract for `prescan(&[u8]) -> Option<Encoding>`: equals "prescan a byte
/// stream to determine its encoding" of those bytes (the caller cuts them to
/// the end condition).
pub open spec fn prescan_ensures(b: Seq<u8>, output: Option<clazel_encoding::labels::spec::Encoding>) -> bool {
    output == prescan(b)
}

/// Contract for `transport_encoding(&MimeType) -> Option<Encoding>`: "get an
/// encoding" of its `charset` parameter.
pub open spec fn transport_encoding_ensures(
    mime_type: clazel_mime::mime_type::spec::MimeTypeRecord,
    output: Option<clazel_encoding::labels::spec::Encoding>,
) -> bool {
    output == transport_encoding(mime_type.parameters)
}

/// Contract for `change_the_encoding(Encoding, Encoding) -> Option<Encoding>`.
pub open spec fn change_the_encoding_ensures(
    current: clazel_encoding::labels::spec::Encoding,
    new: clazel_encoding::labels::spec::Encoding,
    output: Option<clazel_encoding::labels::spec::Encoding>,
) -> bool {
    output == change_the_encoding(current, new)
}

} // verus!
