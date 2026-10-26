//! Contracts for the RFC 5280 Certificate envelope reader.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `parse_certificate`: success exactly matches the envelope
/// spec, including complete input consumption and exact original TBS TLV.
pub open spec fn parse_certificate_ensures(
    input: Seq<u8>, output: Option<CertificateEnvelope>,
) -> bool {
    output == parse_certificate(input)
}

} // verus!
