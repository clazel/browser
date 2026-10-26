//! Independent byte fixtures for the Certificate envelope parser.

use clazel_x509::certificate::exec::parse_certificate;

const CERT_WITHOUT_PARAMETERS: [u8; 16] = [
    0x30, 0x0E, // Certificate SEQUENCE, 14 content octets
    0x30, 0x02, 0x05, 0x00, // opaque TBSCertificate SEQUENCE TLV
    0x30, 0x04, 0x06, 0x02, 0x2A, 0x03, // AlgorithmIdentifier { OID 1.2.3 }
    0x03, 0x02, 0x03, 0xA8, // signature BIT STRING, 3 unused zero bits
];

#[test]
fn preserves_full_tbs_tlv_and_der_signature_bits() {
    assert!(parse_certificate(&CERT_WITHOUT_PARAMETERS).is_some());
    let Some(parsed) = parse_certificate(&CERT_WITHOUT_PARAMETERS) else {
        return;
    };
    assert_eq!(parsed.tbs_certificate_der, &[0x30, 0x02, 0x05, 0x00]);
    assert_eq!(parsed.signature_algorithm.oid, vec![1, 2, 3]);
    assert_eq!(parsed.signature_algorithm.parameters_der, None);
    assert_eq!(parsed.signature_unused_bits, 3);
    assert_eq!(parsed.signature_bits, &[0xA8]);
}

#[test]
fn preserves_optional_algorithm_parameters_as_full_der() {
    let cert = [
        0x30, 0x10, 0x30, 0x02, 0x05, 0x00, 0x30, 0x06, 0x06, 0x02, 0x2A, 0x03, 0x05, 0x00, 0x03,
        0x02, 0x00, 0xAB,
    ];
    assert!(parse_certificate(&cert).is_some());
    let Some(parsed) = parse_certificate(&cert) else {
        return;
    };
    assert_eq!(
        parsed.signature_algorithm.parameters_der,
        Some(&[0x05, 0x00][..])
    );
    assert_eq!(parsed.signature_unused_bits, 0);
    assert_eq!(parsed.signature_bits, &[0xAB]);
}

#[test]
fn rejects_wrong_tags_truncation_and_length_overrun() {
    let mut wrong_outer = CERT_WITHOUT_PARAMETERS;
    wrong_outer[0] = 0x31;
    assert!(parse_certificate(&wrong_outer).is_none());

    let mut wrong_tbs = CERT_WITHOUT_PARAMETERS;
    wrong_tbs[2] = 0x05;
    assert!(parse_certificate(&wrong_tbs).is_none());

    let mut wrong_algorithm = CERT_WITHOUT_PARAMETERS;
    wrong_algorithm[6] = 0x05;
    assert!(parse_certificate(&wrong_algorithm).is_none());

    assert!(parse_certificate(&CERT_WITHOUT_PARAMETERS[..15]).is_none());
    let mut overrun = CERT_WITHOUT_PARAMETERS;
    overrun[1] = 0x20;
    assert!(parse_certificate(&overrun).is_none());
}

#[test]
fn rejects_bad_oid_parameter_arity_bit_string_and_trailing_fields() {
    let bad_oid = [
        0x30, 0x0C, 0x30, 0x02, 0x05, 0x00, 0x30, 0x02, 0x06, 0x00, 0x03, 0x02, 0x00, 0xAB,
    ];
    assert!(parse_certificate(&bad_oid).is_none());

    let two_parameters = [
        0x30, 0x12, 0x30, 0x02, 0x05, 0x00, 0x30, 0x08, 0x06, 0x02, 0x2A, 0x03, 0x05, 0x00, 0x05,
        0x00, 0x03, 0x02, 0x00, 0xAB,
    ];
    assert!(parse_certificate(&two_parameters).is_none());

    let truncated_parameter = [
        0x30, 0x10, 0x30, 0x02, 0x05, 0x00, 0x30, 0x06, 0x06, 0x02, 0x2A, 0x03, 0x05, 0x01, 0x03,
        0x02, 0x00, 0xAB,
    ];
    assert!(parse_certificate(&truncated_parameter).is_none());

    let no_unused_count = [
        0x30, 0x0C, 0x30, 0x02, 0x05, 0x00, 0x30, 0x04, 0x06, 0x02, 0x2A, 0x03, 0x03, 0x00,
    ];
    assert!(parse_certificate(&no_unused_count).is_none());

    let nonzero_padding = [
        0x30, 0x0E, 0x30, 0x02, 0x05, 0x00, 0x30, 0x04, 0x06, 0x02, 0x2A, 0x03, 0x03, 0x02, 0x03,
        0xA9,
    ];
    assert!(parse_certificate(&nonzero_padding).is_none());

    let extra_outer_child = [
        0x30, 0x10, 0x30, 0x02, 0x05, 0x00, 0x30, 0x04, 0x06, 0x02, 0x2A, 0x03, 0x03, 0x02, 0x00,
        0xAB, 0x05, 0x00,
    ];
    assert!(parse_certificate(&extra_outer_child).is_none());

    let mut trailing = CERT_WITHOUT_PARAMETERS.to_vec();
    trailing.extend_from_slice(&[0x05, 0x00]);
    assert!(parse_certificate(&trailing).is_none());
}
