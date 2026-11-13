//! Contracts the executable code must be proven to meet. Each exec function's `ensures`
//! clause is one of these predicates, so reading these and [`super::spec`] is enough to
//! know what the implementation guarantees.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `fallback_encoding`: the spec's "determine the fallback encoding".
pub open spec fn fallback_encoding_ensures(
    stylesheet: Seq<u8>,
    protocol_label: Option<Seq<u32>>,
    environment_encoding: Option<clazel_encoding::labels::spec::Encoding>,
    output: clazel_encoding::labels::spec::Encoding,
) -> bool {
    output == determine_the_fallback_encoding(stylesheet, protocol_label, environment_encoding)
}

/// Contract for `decode_stylesheet`: the spec's "decode", `None` when `clazel-encoding`
/// has no decoder for the encoding the bytes need.
pub open spec fn decode_stylesheet_ensures(
    stylesheet: Seq<u8>,
    protocol_label: Option<Seq<u32>>,
    environment_encoding: Option<clazel_encoding::labels::spec::Encoding>,
    output: Option<Seq<u32>>,
) -> bool {
    output == decode_bytes(stylesheet, protocol_label, environment_encoding)
}

} // verus!
