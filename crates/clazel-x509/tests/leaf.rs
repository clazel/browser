//! Compositional, explicitly partial server-leaf checks.

use clazel_x509::{
    leaf::exec::{LeafPolicy, PartialValidationState, check_leaf_certificate},
    matcher::ReferenceIdentity,
    time::exec::CertificateTime,
};

const SERVER_AUTH_OID: &[u8] = &[0x06, 0x08, 0x2b, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x01];
const ANY_EKU_OID: &[u8] = &[0x06, 0x04, 0x55, 0x1d, 0x25, 0x00];
const CLIENT_AUTH_OID: &[u8] = &[0x06, 0x08, 0x2b, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x02];

fn tlv(tag: u8, contents: &[u8]) -> Vec<u8> {
    let Ok(length) = u8::try_from(contents.len()) else {
        return Vec::new();
    };
    let mut result = if length < 128 {
        vec![tag, length]
    } else {
        vec![tag, 0x81, length]
    };
    result.extend_from_slice(contents);
    result
}

fn extension(oid: &[u8], critical: bool, value: &[u8]) -> Vec<u8> {
    let mut contents = oid.to_vec();
    if critical {
        contents.extend_from_slice(&[0x01, 0x01, 0xff]);
    }
    contents.extend_from_slice(&tlv(0x04, value));
    tlv(0x30, &contents)
}

fn san_dns(name: &[u8]) -> Vec<u8> {
    let general_names = tlv(0x82, name);
    tlv(0x30, &general_names)
}

fn san_ip(address: &[u8]) -> Vec<u8> {
    let general_names = tlv(0x87, address);
    tlv(0x30, &general_names)
}

fn certificate(extensions: &[u8], not_before: &[u8; 13], not_after: &[u8; 13]) -> Vec<u8> {
    let mut tbs_contents = vec![0xa0, 0x03, 0x02, 0x01, 0x02]; // explicit v3
    tbs_contents.extend_from_slice(&[
        0x02, 0x01, 0x01, // serial number
        0x30, 0x04, 0x06, 0x02, 0x2a, 0x03, // opaque signature AlgorithmIdentifier
        0x30, 0x02, 0x31, 0x00, // opaque issuer Name
        0x30, 0x1e, 0x17, 0x0d,
    ]);
    tbs_contents.extend_from_slice(not_before);
    tbs_contents.extend_from_slice(&[0x17, 0x0d]);
    tbs_contents.extend_from_slice(not_after);
    tbs_contents.extend_from_slice(&[0x30, 0x00, 0x30, 0x00]); // subject, SPKI
    tbs_contents.extend_from_slice(&tlv(0xa3, extensions));
    let tbs = tlv(0x30, &tbs_contents);

    let mut certificate_contents = tbs;
    certificate_contents.extend_from_slice(&[0x30, 0x04, 0x06, 0x02, 0x2a, 0x03]);
    certificate_contents.extend_from_slice(&[0x03, 0x01, 0x00]); // empty signature bits
    tlv(0x30, &certificate_contents)
}

fn extensions(children: &[Vec<u8>]) -> Vec<u8> {
    let contents: Vec<u8> = children
        .iter()
        .flat_map(|child| child.iter().copied())
        .collect();
    tlv(0x30, &contents)
}

fn time(year: u8, month: u8, day: u8) -> CertificateTime {
    CertificateTime {
        year: 2000 + u16::from(year),
        month,
        day,
        hour: 0,
        minute: 0,
        second: 0,
    }
}

fn base_extensions(san: Vec<u8>) -> Vec<Vec<u8>> {
    vec![extension(&[0x06, 0x03, 0x55, 0x1d, 0x11], false, &san)]
}

fn check<'a>(
    cert: &[u8],
    reference: ReferenceIdentity<'a>,
    now: &CertificateTime,
    policy: LeafPolicy,
) -> Option<clazel_x509::leaf::exec::PartialLeafChecks<'a>> {
    check_leaf_certificate(cert, reference, now, policy)
}

#[test]
fn dns_san_validity_and_absent_usages_produce_only_partial_evidence() {
    let extensions = extensions(&base_extensions(san_dns(b"www.example.test")));
    let cert = certificate(&extensions, b"260101000000Z", b"270101000000Z");
    let result = check(
        &cert,
        ReferenceIdentity::Dns(b"www.example.test"),
        &time(26, 1, 1),
        LeafPolicy {
            allow_any_extended_key_usage: false,
        },
    );
    assert!(result.is_some());
    let Some(result) = result else { return };
    assert!(result.identity_matched);
    assert!(result.valid_at_captured_time);
    assert!(!result.key_usage_present);
    assert!(!result.extended_key_usage_present);
    assert!(!result.basic_constraints_present);
    assert_eq!(result.state, PartialValidationState::NeedsPathValidation);
}

#[test]
fn ip_san_is_binary_exact_and_cross_type_never_matches() {
    let extensions = extensions(&base_extensions(san_ip(&[192, 0, 2, 7])));
    let cert = certificate(&extensions, b"260101000000Z", b"270101000000Z");
    assert!(
        check(
            &cert,
            ReferenceIdentity::Ip(&[192, 0, 2, 7]),
            &time(26, 6, 1),
            LeafPolicy {
                allow_any_extended_key_usage: false,
            }
        )
        .is_some()
    );
    assert!(
        check(
            &cert,
            ReferenceIdentity::Ip(&[192, 0, 2, 8]),
            &time(26, 6, 1),
            LeafPolicy {
                allow_any_extended_key_usage: false,
            }
        )
        .is_none()
    );
    assert!(
        check(
            &cert,
            ReferenceIdentity::Dns(b"192.0.2.7"),
            &time(26, 6, 1),
            LeafPolicy {
                allow_any_extended_key_usage: false,
            }
        )
        .is_none()
    );
}

#[test]
fn validity_endpoints_are_inclusive_and_outside_or_reversed_intervals_fail() {
    let extensions = extensions(&base_extensions(san_dns(b"www.example.test")));
    let cert = certificate(&extensions, b"260101000000Z", b"270101000000Z");
    let policy = LeafPolicy {
        allow_any_extended_key_usage: false,
    };
    assert!(
        check(
            &cert,
            ReferenceIdentity::Dns(b"www.example.test"),
            &time(26, 1, 1),
            policy
        )
        .is_some()
    );
    assert!(
        check(
            &cert,
            ReferenceIdentity::Dns(b"www.example.test"),
            &time(27, 1, 1),
            policy
        )
        .is_some()
    );
    assert!(
        check(
            &cert,
            ReferenceIdentity::Dns(b"www.example.test"),
            &time(25, 12, 31),
            policy
        )
        .is_none()
    );
    assert!(
        check(
            &cert,
            ReferenceIdentity::Dns(b"www.example.test"),
            &time(27, 1, 2),
            policy
        )
        .is_none()
    );
    let reversed = certificate(&extensions, b"270101000000Z", b"260101000000Z");
    assert!(
        check(
            &reversed,
            ReferenceIdentity::Dns(b"www.example.test"),
            &time(26, 6, 1),
            policy
        )
        .is_none()
    );
}

#[test]
fn key_usage_eku_and_basic_constraints_apply_leaf_policy() {
    let san = extension(
        &[0x06, 0x03, 0x55, 0x1d, 0x11],
        false,
        &san_dns(b"www.example.test"),
    );
    let eku = extension(
        &[0x06, 0x03, 0x55, 0x1d, 0x25],
        false,
        &tlv(0x30, SERVER_AUTH_OID),
    );
    let digital_signature = extension(
        &[0x06, 0x03, 0x55, 0x1d, 0x0f],
        false,
        &[0x03, 0x02, 0x07, 0x80],
    );
    let bc_end_entity = extension(&[0x06, 0x03, 0x55, 0x1d, 0x13], false, &[0x30, 0x00]);
    let policy = LeafPolicy {
        allow_any_extended_key_usage: false,
    };
    let now = time(26, 6, 1);

    let good_exts = extensions(&[
        san.clone(),
        eku.clone(),
        digital_signature.clone(),
        bc_end_entity,
    ]);
    let good = certificate(&good_exts, b"260101000000Z", b"270101000000Z");
    let result = check(
        &good,
        ReferenceIdentity::Dns(b"www.example.test"),
        &now,
        policy,
    );
    assert!(result.is_some());
    let Some(result) = result else { return };
    assert!(result.server_auth_purpose_allowed);
    assert!(result.digital_signature_allowed);
    assert!(result.leaf_role_allowed);
    assert!(
        result.key_usage_present
            && result.extended_key_usage_present
            && result.basic_constraints_present
    );

    let no_sign = extension(
        &[0x06, 0x03, 0x55, 0x1d, 0x0f],
        false,
        &[0x03, 0x02, 0x05, 0x20],
    );
    let exts = extensions(&[san.clone(), no_sign]);
    assert!(
        check(
            &certificate(&exts, b"260101000000Z", b"270101000000Z"),
            ReferenceIdentity::Dns(b"www.example.test"),
            &now,
            policy
        )
        .is_none()
    );

    let client_eku = extension(
        &[0x06, 0x03, 0x55, 0x1d, 0x25],
        false,
        &tlv(0x30, CLIENT_AUTH_OID),
    );
    let exts = extensions(&[san.clone(), client_eku]);
    assert!(
        check(
            &certificate(&exts, b"260101000000Z", b"270101000000Z"),
            ReferenceIdentity::Dns(b"www.example.test"),
            &now,
            policy
        )
        .is_none()
    );

    let any_eku = extension(
        &[0x06, 0x03, 0x55, 0x1d, 0x25],
        false,
        &tlv(0x30, ANY_EKU_OID),
    );
    let exts = extensions(&[san.clone(), any_eku.clone()]);
    assert!(
        check(
            &certificate(&exts, b"260101000000Z", b"270101000000Z"),
            ReferenceIdentity::Dns(b"www.example.test"),
            &now,
            policy
        )
        .is_none()
    );
    assert!(
        check(
            &certificate(&exts, b"260101000000Z", b"270101000000Z"),
            ReferenceIdentity::Dns(b"www.example.test"),
            &now,
            LeafPolicy {
                allow_any_extended_key_usage: true,
            }
        )
        .is_some()
    );

    let ca = extension(
        &[0x06, 0x03, 0x55, 0x1d, 0x13],
        false,
        &[0x30, 0x03, 0x01, 0x01, 0xff],
    );
    let exts = extensions(&[san, ca]);
    assert!(
        check(
            &certificate(&exts, b"260101000000Z", b"270101000000Z"),
            ReferenceIdentity::Dns(b"www.example.test"),
            &now,
            policy
        )
        .is_none()
    );
}

#[test]
fn unknown_critical_extensions_and_missing_san_fail_closed() {
    let san = extension(
        &[0x06, 0x03, 0x55, 0x1d, 0x11],
        false,
        &san_dns(b"www.example.test"),
    );
    let unknown = extension(&[0x06, 0x02, 0x2a, 0x03], true, &[0x05, 0x00]);
    let critical = extensions(&[san.clone(), unknown]);
    let policy = LeafPolicy {
        allow_any_extended_key_usage: false,
    };
    let now = time(26, 6, 1);
    assert!(
        check(
            &certificate(&critical, b"260101000000Z", b"270101000000Z"),
            ReferenceIdentity::Dns(b"www.example.test"),
            &now,
            policy
        )
        .is_none()
    );

    let noncritical = extension(&[0x06, 0x02, 0x2a, 0x03], false, &[0x05, 0x00]);
    let exts = extensions(&[san, noncritical]);
    assert!(
        check(
            &certificate(&exts, b"260101000000Z", b"270101000000Z"),
            ReferenceIdentity::Dns(b"www.example.test"),
            &now,
            policy
        )
        .is_some()
    );

    let exts = extensions(&[]);
    assert!(
        check(
            &certificate(&exts, b"260101000000Z", b"270101000000Z"),
            ReferenceIdentity::Dns(b"www.example.test"),
            &now,
            policy
        )
        .is_none()
    );
}
