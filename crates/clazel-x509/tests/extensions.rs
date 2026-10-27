//! Adversarial checks for the X.509 Extensions and subjectAltName decoders.

use clazel_x509::extensions::exec::{GeneralName, parse_extensions, parse_subject_alt_name};

fn extension(critical: bool, value: &[u8]) -> Vec<u8> {
    let Ok(value_len) = u8::try_from(value.len()) else {
        return Vec::new();
    };
    let mut content = vec![0x06, 0x03, 0x55, 0x1d, 0x11]; // id-ce-subjectAltName
    if critical {
        content.extend_from_slice(&[0x01, 0x01, 0xff]);
    }
    content.push(0x04);
    content.push(value_len);
    content.extend_from_slice(value);
    let Ok(content_len) = u8::try_from(content.len()) else {
        return Vec::new();
    };
    let mut out = vec![0x30, content_len];
    out.extend_from_slice(&content);
    out
}

fn extensions(children: &[u8]) -> Vec<u8> {
    let Ok(children_len) = u8::try_from(children.len()) else {
        return Vec::new();
    };
    let mut out = vec![0x30, children_len];
    out.extend_from_slice(children);
    out
}

#[test]
fn extension_container_preserves_unknown_payload_and_default_false() {
    let child = extension(false, &[0x05, 0x00]);
    let encoded = extensions(&child);
    let parsed = parse_extensions(&encoded);
    assert!(parsed.is_some());
    let Some(parsed) = parsed else {
        return;
    };
    assert_eq!(parsed.len(), 1);
    let Some(record) = parsed.first() else {
        return;
    };
    assert!(!record.critical);
    assert_eq!(record.oid, vec![2, 5, 29, 17]);
    assert_eq!(record.value, &[0x05, 0x00]);
}

#[test]
fn extension_container_exposes_critical_true() {
    let child = extension(true, &[0x05, 0x00]);
    let encoded = extensions(&child);
    let parsed = parse_extensions(&encoded);
    assert!(parsed.is_some());
    let Some(parsed) = parsed else {
        return;
    };
    assert_eq!(parsed.len(), 1);
    let Some(record) = parsed.first() else {
        return;
    };
    assert!(record.critical);
}

#[test]
fn extension_container_rejects_duplicate_oids() {
    let child = extension(false, &[0x05, 0x00]);
    let mut duplicate = child.clone();
    duplicate.extend_from_slice(&child);
    assert!(parse_extensions(&extensions(&duplicate)).is_none());
}

#[test]
fn extension_container_rejects_explicit_default_false() {
    let content = [
        0x06, 0x03, 0x55, 0x1d, 0x11, 0x01, 0x01, 0x00, 0x04, 0x02, 0x05, 0x00,
    ];
    let mut input = vec![0x30, 12];
    input.extend_from_slice(&content);
    assert!(parse_extensions(&input).is_none());
}

#[test]
fn extension_container_rejects_empty_and_trailing_data() {
    assert!(parse_extensions(&[0x30, 0x00]).is_none());
    assert!(parse_extensions(&[0x30, 0x00, 0x05, 0x00]).is_none());
    assert!(parse_extensions(&[0x30, 0x02, 0x05, 0x00]).is_none());
}

#[test]
fn san_extracts_dns_and_ipv4_and_preserves_other_names() {
    let encoded = vec![
        0x30, 0x15, 0x82, 0x0b, b'w', b'w', b'w', b'.', b'e', b'x', b'a', b'm', b'p', b'l', b'e',
        0x87, 0x04, 192, 0, 2, 1, 0xa0, 0x00,
    ];
    let san = parse_subject_alt_name(&encoded);
    assert!(san.is_some());
    let Some(san) = san else {
        return;
    };
    assert_eq!(san.names.len(), 3);
    match san.names.first() {
        Some(GeneralName::DnsName(bytes)) => assert_eq!(*bytes, b"www.example"),
        _ => assert_eq!(san.names.len(), 4),
    }
    match san.names.get(1) {
        Some(GeneralName::IpAddress(bytes)) => assert_eq!(*bytes, &[192, 0, 2, 1]),
        _ => assert_eq!(san.names.len(), 4),
    }
    match san.names.get(2) {
        Some(GeneralName::Other(0, bytes)) => assert_eq!(*bytes, &[0xa0, 0x00]),
        _ => assert_eq!(san.names.len(), 4),
    }
}

#[test]
fn san_rejects_empty_names_bad_dns_and_wrong_ip_width() {
    assert!(parse_subject_alt_name(&[0x30, 0x00]).is_none());
    assert!(parse_subject_alt_name(&[0x30, 0x02, 0x82, 0x00]).is_none());
    assert!(parse_subject_alt_name(&[0x30, 0x03, 0x82, 0x01, 0xff]).is_none());
    assert!(parse_subject_alt_name(&[0x30, 0x03, 0x87, 0x01, 0x01]).is_none());
    assert!(parse_subject_alt_name(&[0x30, 0x04, 0x87, 0x02, 0x01, 0x00]).is_none());
}

#[test]
fn san_rejects_invalid_tag_forms_and_trailing_bytes() {
    assert!(parse_subject_alt_name(&[0x30, 0x03, 0xa2, 0x01, b'a']).is_none());
    assert!(parse_subject_alt_name(&[0x30, 0x03, 0x89, 0x01, b'a']).is_none());
    assert!(parse_subject_alt_name(&[0x30, 0x00, 0x05, 0x00]).is_none());
}
