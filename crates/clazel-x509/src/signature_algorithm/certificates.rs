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

/// An AlgorithmIdentifier with the given OID arcs and optional parameters TLV.
pub open spec fn ex_alg(
    oid: Seq<nat>, parameters_der: Option<Seq<u8>>,
) -> crate::certificate::spec::AlgorithmIdentifier {
    crate::certificate::spec::AlgorithmIdentifier { oid, parameters_der }
}

/// RFC 5758 §3.2: ecdsa-with-SHA256, 1.2.840.10045.4.3.2, with its
/// parameters omitted, is the SHA-256 ECDSA profile.
pub proof fn lemma_ecdsa_sha256_class()
    ensures classify(ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat], None))
        == Some(AlgorithmClass::Ecdsa(EcdsaHash::Sha256))
{
    assert(classify(ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat], None))
        == Some(AlgorithmClass::Ecdsa(EcdsaHash::Sha256))) by (compute_only);
}

/// RFC 5758 §3.2: ecdsa-with-SHA384, 1.2.840.10045.4.3.3, with its
/// parameters omitted, is the SHA-384 ECDSA profile.
pub proof fn lemma_ecdsa_sha384_class()
    ensures classify(ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 3nat], None))
        == Some(AlgorithmClass::Ecdsa(EcdsaHash::Sha384))
{
    assert(classify(ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 3nat], None))
        == Some(AlgorithmClass::Ecdsa(EcdsaHash::Sha384))) by (compute_only);
}

/// RFC 5758 §3.2: "the encoding MUST omit the parameters field", so NULL
/// parameters (which RSA accepts) and any other parameters are malformed.
pub proof fn lemma_ecdsa_rejects_any_parameters()
    ensures
        classify(ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat],
            Some(seq![0x05u8, 0x00u8]))) is None,
        classify(ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 3nat],
            Some(seq![0x05u8, 0x00u8]))) is None,
        classify(ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat],
            Some(seq![0x04u8, 0x00u8]))) is None,
{
    assert(classify(ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat],
        Some(seq![0x05u8, 0x00u8]))) is None) by (compute_only);
    assert(classify(ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 3nat],
        Some(seq![0x05u8, 0x00u8]))) is None) by (compute_only);
    assert(classify(ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat],
        Some(seq![0x04u8, 0x00u8]))) is None) by (compute_only);
}

/// The other ECDSA signature identifiers are refused (Unsupported): RFC 5758
/// §3.1 ecdsa-with-SHA224 (4.3.1) and §3.2 ecdsa-with-SHA512 (4.3.4), and
/// RFC 3279 §2.2.3 ecdsa-with-SHA1 (1.2.840.10045.4.1).
pub proof fn lemma_other_ecdsa_hashes_are_unsupported()
    ensures
        classify(ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 1nat], None))
            == Some(AlgorithmClass::Unsupported),
        classify(ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 4nat], None))
            == Some(AlgorithmClass::Unsupported),
        classify(ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 1nat], None))
            == Some(AlgorithmClass::Unsupported),
{
    assert(classify(ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 1nat], None))
        == Some(AlgorithmClass::Unsupported)) by (compute_only);
    assert(classify(ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 4nat], None))
        == Some(AlgorithmClass::Unsupported)) by (compute_only);
    assert(classify(ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 1nat], None))
        == Some(AlgorithmClass::Unsupported)) by (compute_only);
}

/// RFC 5280 §4.1.1.2: ECDSA SHA-256 and SHA-384 identifiers do not match.
pub proof fn lemma_ecdsa_sha256_and_sha384_do_not_match()
    ensures prepare_signature(
        ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat], None),
        ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 3nat], None),
        seq![0x30u8, 0x00], seq![0x01u8], 0,
    ) == None::<PreparedSignature>
{
    assert(prepare_signature(
        ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat], None),
        ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 3nat], None),
        seq![0x30u8, 0x00], seq![0x01u8], 0,
    ) == None::<PreparedSignature>) by (compute_only);
}

/// RFC 5280 §4.1.1.2: an RSA identifier and an ECDSA identifier do not match,
/// even with the same hash.
pub proof fn lemma_rsa_and_ecdsa_do_not_match()
    ensures prepare_signature(
        ex_alg(seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 11nat], None),
        ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat], None),
        seq![0x30u8, 0x00], seq![0x01u8], 0,
    ) == None::<PreparedSignature>
{
    assert(prepare_signature(
        ex_alg(seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 11nat], None),
        ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat], None),
        seq![0x30u8, 0x00], seq![0x01u8], 0,
    ) == None::<PreparedSignature>) by (compute_only);
}

/// Matching ECDSA identifiers and an octet-aligned signature are prepared;
/// the prepared class is the ECDSA profile.
pub proof fn lemma_ecdsa_sha256_pairs_with_itself()
    ensures
        prepare_signature(
            ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat], None),
            ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat], None),
            seq![0x30u8, 0x00], seq![0x01u8], 0,
        ) is Some,
        prepare_signature(
            ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat], None),
            ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat], None),
            seq![0x30u8, 0x00], seq![0x01u8], 0,
        ).unwrap().class == AlgorithmClass::Ecdsa(EcdsaHash::Sha256),
{
    assert(prepare_signature(
        ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat], None),
        ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat], None),
        seq![0x30u8, 0x00], seq![0x01u8], 0,
    ) is Some) by (compute_only);
    assert(prepare_signature(
        ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat], None),
        ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat], None),
        seq![0x30u8, 0x00], seq![0x01u8], 0,
    ).unwrap().class == AlgorithmClass::Ecdsa(EcdsaHash::Sha256)) by (compute_only);
}

/// RFC 5280 §4.1.1.2: an ECDSA signature BIT STRING must be octet aligned.
pub proof fn lemma_ecdsa_requires_zero_unused_bits()
    ensures prepare_signature(
        ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 3nat], None),
        ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 3nat], None),
        seq![0x30u8, 0x00], seq![0xA0u8], 1,
    ) == None::<PreparedSignature>
{
    assert(prepare_signature(
        ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 3nat], None),
        ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 3nat], None),
        seq![0x30u8, 0x00], seq![0xA0u8], 1,
    ) == None::<PreparedSignature>) by (compute_only);
}


} // verus!
