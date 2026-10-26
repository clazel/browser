//! Contracts for signature AlgorithmIdentifier classification and pairing.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for supported/unsupported signature AlgorithmIdentifier classification.
pub open spec fn classify_ensures(
    input: crate::certificate::spec::AlgorithmIdentifier,
    output: Option<AlgorithmClass>,
) -> bool {
    output == classify(input)
}

/// Contract for RFC 5280's matching TBS/outer signature algorithm fields.
pub open spec fn prepare_signature_ensures(
    tbs_algorithm: crate::certificate::spec::AlgorithmIdentifier,
    outer_algorithm: crate::certificate::spec::AlgorithmIdentifier,
    tbs_der: Seq<u8>,
    signature_bits: Seq<u8>,
    signature_unused_bits: u8,
    output: Option<PreparedSignature>,
) -> bool {
    output == prepare_signature(
        tbs_algorithm,
        outer_algorithm,
        tbs_der,
        signature_bits,
        signature_unused_bits,
    )
}

} // verus!
