//! Host theorems for signature AlgorithmIdentifier profile mutations.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// RFC 4055 §5 requires implementations to accept SHA-256 RSA parameters
/// encoded as NULL as well as absent.
pub proof fn lemma_sha256_null_parameters_are_accepted()
    ensures classify(crate::certificate::spec::AlgorithmIdentifier {
        oid: seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 11nat],
        parameters_der: Some(seq![0x05u8, 0x00u8]),
    }) == Some(AlgorithmClass::Supported(RsaPkcs1v15Hash::Sha256))
{
    assert(classify(crate::certificate::spec::AlgorithmIdentifier {
        oid: seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 11nat],
        parameters_der: Some(seq![0x05u8, 0x00u8]),
    }) == Some(AlgorithmClass::Supported(RsaPkcs1v15Hash::Sha256))) by (compute_only);
}

/// RFC 5280 §4.1.1.2 requires the TBS and outer signature profiles to agree.
pub proof fn lemma_rsa_sha256_and_sha384_do_not_match()
    ensures prepare_signature(
        crate::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 11nat],
            parameters_der: None,
        },
        crate::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 12nat],
            parameters_der: None,
        },
        seq![0x30u8, 0x00], seq![0x01u8], 0,
    ) == None
{
    assert(prepare_signature(
        crate::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 11nat],
            parameters_der: None,
        },
        crate::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 12nat],
            parameters_der: None,
        },
        seq![0x30u8, 0x00], seq![0x01u8], 0,
    ) == None) by (compute_only);
}

/// Supported RSA signature BIT STRING values are octet aligned.
pub proof fn lemma_supported_signature_requires_zero_unused_bits()
    ensures prepare_signature(
        crate::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 11nat],
            parameters_der: None,
        },
        crate::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 11nat],
            parameters_der: None,
        },
        seq![0x30u8, 0x00], seq![0xA0u8], 1,
    ) == None
{
    assert(prepare_signature(
        crate::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 11nat],
            parameters_der: None,
        },
        crate::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 11nat],
            parameters_der: None,
        },
        seq![0x30u8, 0x00], seq![0xA0u8], 1,
    ) == None) by (compute_only);
}

/// Unsupported algorithms are paired only when their identifiers match.
pub proof fn lemma_unsupported_identifiers_must_match()
    ensures prepare_signature(
        crate::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 2nat, 3nat], parameters_der: None,
        },
        crate::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 2nat, 4nat], parameters_der: None,
        },
        seq![0x30u8, 0x00], seq![0xA0u8], 0,
    ) == None
{
    assert(prepare_signature(
        crate::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 2nat, 3nat], parameters_der: None,
        },
        crate::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 2nat, 4nat], parameters_der: None,
        },
        seq![0x30u8, 0x00], seq![0xA0u8], 0,
    ) == None) by (compute_only);
}

} // verus!
