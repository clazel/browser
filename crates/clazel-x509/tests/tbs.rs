//! Independent hostile fixtures for RFC 5280 §4.1.2 TBS framing.

use clazel_x509::tbs::exec::parse_tbs_certificate;

fn minimal_tbs(include_v3: bool) -> Vec<u8> {
    let mut contents = Vec::new();
    if include_v3 {
        contents.extend_from_slice(&[0xA0, 0x03, 0x02, 0x01, 0x02]);
    }
    contents.extend_from_slice(&[
        0x02, 0x01, 0x01, // serialNumber = 1
        0x30, 0x04, 0x06, 0x02, 0x2A, 0x03, // AlgorithmIdentifier
        0x30, 0x02, 0x31, 0x00, // issuer Name
        0x30, 0x1E, // Validity
        0x17, 0x0D, b'2', b'6', b'0', b'1', b'0', b'1', b'0', b'0', b'0', b'0', b'0', b'0', b'Z',
        0x17, 0x0D, b'2', b'7', b'0', b'1', b'0', b'1', b'0', b'0', b'0', b'0', b'0', b'0', b'Z',
        0x30, 0x00, // empty subject Name
        0x30, 0x00, // opaque SPKI
    ]);
    let mut encoded = vec![0x30, contents.len() as u8];
    encoded.extend_from_slice(&contents);
    encoded
}

fn replace_byte(bytes: &mut [u8], index: usize, value: u8) -> bool {
    match bytes.get_mut(index) {
        Some(byte) => {
            *byte = value;
            true
        }
        None => false,
    }
}

#[test]
fn retains_complete_signed_tbs_tlv_and_decodes_required_fields() {
    let input = minimal_tbs(true);
    let parsed = parse_tbs_certificate(&input);
    assert!(parsed.is_some());
    let Some(parsed) = parsed else {
        return;
    };
    assert_eq!(parsed.version, 2);
    assert_eq!(parsed.serial_number_der, &[0x02, 0x01, 0x01]);
    assert_eq!(parsed.issuer_der, &[0x30, 0x02, 0x31, 0x00]);
    assert_eq!(parsed.subject_der, &[0x30, 0x00]);
    assert_eq!(parsed.subject_public_key_info_der, &[0x30, 0x00]);
    assert_eq!(parsed.tbs_certificate_der, input.as_slice());
    assert_eq!(parsed.not_before.year, 2026);
    assert_eq!(parsed.not_after.year, 2027);
}

#[test]
fn rejects_explicit_default_v1_and_trailing_data() {
    let mut explicit_default = minimal_tbs(true);
    assert!(replace_byte(&mut explicit_default, 6, 0));
    assert!(parse_tbs_certificate(&explicit_default).is_none());

    let mut trailing = minimal_tbs(false);
    trailing.push(0x05);
    trailing.push(0x00);
    assert!(parse_tbs_certificate(&trailing).is_none());
}

#[test]
fn rejects_v1_unique_id_and_non_v3_extensions() {
    let v1 = minimal_tbs(false);
    let mut contents = v1.get(2..).unwrap_or_default().to_vec();
    contents.extend_from_slice(&[0x81, 0x02, 0x00, 0x80]);
    let mut v1_uid = vec![0x30, contents.len() as u8];
    v1_uid.extend_from_slice(&contents);
    assert!(parse_tbs_certificate(&v1_uid).is_none());

    let v3 = minimal_tbs(true);
    let mut contents = v3.get(2..).unwrap_or_default().to_vec();
    assert!(replace_byte(&mut contents, 4, 1)); // v2; extensions require v3.
    contents.extend_from_slice(&[0xA3, 0x02, 0x30, 0x00]);
    let mut v2_extensions = vec![0x30, contents.len() as u8];
    v2_extensions.extend_from_slice(&contents);
    assert!(parse_tbs_certificate(&v2_extensions).is_none());
}
