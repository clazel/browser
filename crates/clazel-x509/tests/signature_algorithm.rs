//! Signature algorithm profile and certificate-pair fixtures.

use clazel_x509::certificate::exec::AlgorithmIdentifier;
use clazel_x509::signature_algorithm::exec::{
    AlgorithmClass, EcdsaHash, RsaPkcs1v15Hash, classify, prepare_signature_input,
};

const NULL_PARAMETERS: &[u8] = &[0x05, 0x00];
const OTHER_PARAMETERS: &[u8] = &[0x04, 0x00];

fn rsa_sha2(last_arc: u64, parameters_der: Option<&'static [u8]>) -> AlgorithmIdentifier<'static> {
    AlgorithmIdentifier {
        oid: vec![1, 2, 840, 113549, 1, 1, last_arc],
        parameters_der,
    }
}

/// 1.2.840.10045.4.3.<last_arc> (RFC 5758 §3.2: ecdsa-with-SHA2 = 4.3).
fn ecdsa_sha2(
    last_arc: u64,
    parameters_der: Option<&'static [u8]>,
) -> AlgorithmIdentifier<'static> {
    AlgorithmIdentifier {
        oid: vec![1, 2, 840, 10045, 4, 3, last_arc],
        parameters_der,
    }
}

fn unknown(oid: Vec<u64>, parameters_der: Option<&'static [u8]>) -> AlgorithmIdentifier<'static> {
    AlgorithmIdentifier {
        oid,
        parameters_der,
    }
}

#[test]
fn classifies_rsa_sha2_oids_and_accepts_absent_or_null_parameters() {
    let cases = [
        (11, AlgorithmClass::Supported(RsaPkcs1v15Hash::Sha256)),
        (12, AlgorithmClass::Supported(RsaPkcs1v15Hash::Sha384)),
        (13, AlgorithmClass::Supported(RsaPkcs1v15Hash::Sha512)),
    ];
    for (last_arc, expected) in cases {
        let absent = rsa_sha2(last_arc, None);
        let present = rsa_sha2(last_arc, Some(NULL_PARAMETERS));
        assert!(matches!(
            classify(&absent),
            Some(AlgorithmClass::Supported(_))
        ));
        assert!(matches!(
            classify(&present),
            Some(AlgorithmClass::Supported(_))
        ));

        let prepared = prepare_signature_input(&absent, &present, &[0x30, 0x00], 0, &[0xA5, 0x5A]);
        assert!(prepared.is_some());
        let Some(prepared) = prepared else { return };
        assert!(matches!(
            (&prepared.class, expected),
            (
                AlgorithmClass::Supported(RsaPkcs1v15Hash::Sha256),
                AlgorithmClass::Supported(RsaPkcs1v15Hash::Sha256)
            ) | (
                AlgorithmClass::Supported(RsaPkcs1v15Hash::Sha384),
                AlgorithmClass::Supported(RsaPkcs1v15Hash::Sha384)
            ) | (
                AlgorithmClass::Supported(RsaPkcs1v15Hash::Sha512),
                AlgorithmClass::Supported(RsaPkcs1v15Hash::Sha512)
            )
        ));
        assert_eq!(prepared.tbs_der, &[0x30, 0x00]);
        assert_eq!(prepared.signature_bits, &[0xA5, 0x5A]);
        assert_eq!(prepared.tbs_algorithm.parameters_der, None);
        assert_eq!(
            prepared.outer_algorithm.parameters_der,
            Some(NULL_PARAMETERS)
        );
    }
}

#[test]
fn rejects_known_oid_with_wrong_parameters_or_non_aligned_signature() {
    let valid = rsa_sha2(11, Some(NULL_PARAMETERS));
    let wrong_parameters = rsa_sha2(11, Some(OTHER_PARAMETERS));
    assert!(classify(&wrong_parameters).is_none());
    assert!(
        prepare_signature_input(&valid, &wrong_parameters, &[0x30, 0x00], 0, &[0x11]).is_none()
    );
    assert!(prepare_signature_input(&valid, &valid, &[0x30, 0x00], 1, &[0x11]).is_none());
}

#[test]
fn rejects_different_supported_profiles_and_unsupported_identifiers() {
    let sha256 = rsa_sha2(11, None);
    let sha384 = rsa_sha2(12, None);
    assert!(prepare_signature_input(&sha256, &sha384, &[0x30, 0x00], 0, &[0x01]).is_none());

    let first = unknown(vec![1, 2, 3], None);
    let second = unknown(vec![1, 2, 4], None);
    assert!(matches!(
        classify(&first),
        Some(AlgorithmClass::Unsupported)
    ));
    assert!(prepare_signature_input(&first, &second, &[0x30, 0x00], 0, &[0x01]).is_none());
}

#[test]
fn preserves_unsupported_algorithm_and_generic_bit_string_metadata() {
    let pss = unknown(vec![1, 2, 840, 113549, 1, 1, 10], Some(OTHER_PARAMETERS));
    let matching_pss = unknown(vec![1, 2, 840, 113549, 1, 1, 10], Some(OTHER_PARAMETERS));
    let prepared = prepare_signature_input(&pss, &matching_pss, &[0x30, 0x00], 3, &[0xA0, 0xB8]);
    assert!(prepared.is_some());
    let Some(prepared) = prepared else { return };
    assert!(matches!(prepared.class, AlgorithmClass::Unsupported));
    assert_eq!(prepared.tbs_algorithm.oid, pss.oid);
    assert_eq!(
        prepared.outer_algorithm.parameters_der,
        Some(OTHER_PARAMETERS)
    );
    assert_eq!(prepared.signature_unused_bits, 3);
    assert_eq!(prepared.signature_bits, &[0xA0, 0xB8]);
}

#[test]
fn classifies_ecdsa_sha256_and_sha384_with_absent_parameters() {
    // RFC 5758 §3.2: ecdsa-with-SHA256 is 4.3.2 and ecdsa-with-SHA384 is 4.3.3.
    assert!(matches!(
        classify(&ecdsa_sha2(2, None)),
        Some(AlgorithmClass::Ecdsa(EcdsaHash::Sha256))
    ));
    assert!(matches!(
        classify(&ecdsa_sha2(3, None)),
        Some(AlgorithmClass::Ecdsa(EcdsaHash::Sha384))
    ));
}

#[test]
fn ecdsa_parameters_must_be_absent() {
    // RFC 5758 §3.2: "the encoding MUST omit the parameters field"; NULL,
    // which the RSA identifiers accept, is malformed here.
    for last_arc in [2, 3] {
        assert!(classify(&ecdsa_sha2(last_arc, Some(NULL_PARAMETERS))).is_none());
        assert!(classify(&ecdsa_sha2(last_arc, Some(OTHER_PARAMETERS))).is_none());
    }
    let valid = ecdsa_sha2(2, None);
    let with_null = ecdsa_sha2(2, Some(NULL_PARAMETERS));
    assert!(prepare_signature_input(&valid, &with_null, &[0x30, 0x00], 0, &[0x01]).is_none());
}

#[test]
fn other_ecdsa_hashes_are_refused_as_unsupported() {
    // 4.3.1 ecdsa-with-SHA224, 4.3.4 ecdsa-with-SHA512 (RFC 5758) and
    // 1.2.840.10045.4.1 ecdsa-with-SHA1 (RFC 3279 §2.2.3).
    for last_arc in [1, 4] {
        assert!(matches!(
            classify(&ecdsa_sha2(last_arc, None)),
            Some(AlgorithmClass::Unsupported)
        ));
    }
    let sha1 = unknown(vec![1, 2, 840, 10045, 4, 1], None);
    assert!(matches!(classify(&sha1), Some(AlgorithmClass::Unsupported)));
}

#[test]
fn ecdsa_pairs_agree_on_hash_and_are_octet_aligned() {
    let sha256 = ecdsa_sha2(2, None);
    let sha384 = ecdsa_sha2(3, None);
    let rsa = rsa_sha2(11, None);
    let prepared = prepare_signature_input(&sha256, &sha256, &[0x30, 0x00], 0, &[0x01]);
    assert!(matches!(
        prepared.map(|p| p.class),
        Some(AlgorithmClass::Ecdsa(EcdsaHash::Sha256))
    ));
    assert!(prepare_signature_input(&sha256, &sha384, &[0x30, 0x00], 0, &[0x01]).is_none());
    assert!(prepare_signature_input(&sha384, &sha384, &[0x30, 0x00], 1, &[0xA0]).is_none());
    // The same hash under RSA and ECDSA are different algorithms.
    assert!(prepare_signature_input(&rsa, &sha256, &[0x30, 0x00], 0, &[0x01]).is_none());
    assert!(prepare_signature_input(&sha256, &rsa, &[0x30, 0x00], 0, &[0x01]).is_none());
}
