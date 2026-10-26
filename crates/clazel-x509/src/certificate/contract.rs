//! Contracts for the RFC 5280 Certificate envelope reader.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// View conversion for the executable AlgorithmIdentifier parser result.
pub open spec fn view_algorithm_result(
    result: Option<(super::exec::AlgorithmIdentifier<'_>, usize)>,
) -> Option<(AlgorithmIdentifier, nat)> {
    match result {
        Some((algorithm, next)) => Some((algorithm@, next as nat)),
        None => None,
    }
}

/// Contract for RFC 5280 §4.1.1.2 AlgorithmIdentifier.
pub open spec fn parse_algorithm_identifier_ensures(
    input: Seq<u8>, pos: nat, end: nat, output: Option<(AlgorithmIdentifier, nat)>,
) -> bool {
    output == parse_algorithm_identifier(input, pos, end)
}

/// View conversion for the executable Certificate parser result.
pub open spec fn view_certificate_result(
    result: Option<super::exec::CertificateEnvelope<'_>>,
) -> Option<CertificateEnvelope> {
    match result {
        Some(certificate) => Some(certificate@),
        None => None,
    }
}

/// Contract for `parse_certificate`: success exactly matches the envelope
/// spec, including complete input consumption and exact original TBS TLV.
pub open spec fn parse_certificate_ensures(
    input: Seq<u8>, output: Option<CertificateEnvelope>,
) -> bool {
    output == parse_certificate(input)
}

} // verus!
