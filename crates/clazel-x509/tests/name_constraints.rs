//! Adversarial RFC 5280 NameConstraints syntax and extraction tests.

use clazel_x509::name_constraints::exec::{
    GeneralNameConstraint, general_name_constraint_supported, parse_name_constraints,
};

fn tlv(tag: u8, value: &[u8]) -> Vec<u8> {
    let Ok(length) = u8::try_from(value.len()) else {
        return Vec::new();
    };
    let mut encoded = vec![tag, length];
    encoded.extend_from_slice(value);
    encoded
}

fn subtree(base: &[u8], suffix: &[u8]) -> Vec<u8> {
    let mut contents = base.to_vec();
    contents.extend_from_slice(suffix);
    tlv(0x30, &contents)
}

fn name_constraints(fields: &[u8]) -> Vec<u8> {
    tlv(0x30, fields)
}

#[test]
fn extracts_dns_subtrees_and_implicit_default_minimum() {
    let base = tlv(0x82, b"example.test");
    let subtree = subtree(&base, &[]);
    let permitted = tlv(0xa0, &subtree);
    let encoded = name_constraints(&permitted);
    let parsed = parse_name_constraints(&encoded);
    assert!(parsed.is_some());
    let Some(parsed) = parsed else { return };
    assert!(parsed.excluded_subtrees.is_none());
    let Some(items) = parsed.permitted_subtrees else {
        return;
    };
    assert_eq!(items.len(), 1);
    match items.first().map(|item| item.base) {
        Some(GeneralNameConstraint::DnsName(bytes)) => assert_eq!(bytes, b"example.test"),
        _ => assert_eq!(items.len(), 2),
    }
}

#[test]
fn extracts_ipv4_and_ipv6_address_mask_pairs() {
    let ipv4 = [192, 0, 2, 0, 255, 255, 255, 0];
    let base4 = tlv(0x87, &ipv4);
    let subtree4 = subtree(&base4, &[]);
    let excluded = tlv(0xa1, &subtree4);
    let encoded4 = name_constraints(&excluded);
    let parsed4 = parse_name_constraints(&encoded4);
    assert!(parsed4.is_some());
    let Some(parsed4) = parsed4 else { return };
    let Some(items4) = parsed4.excluded_subtrees else {
        return;
    };
    match items4.first().map(|item| item.base) {
        Some(GeneralNameConstraint::IpAddress { address, mask }) => {
            assert_eq!(address, &[192, 0, 2, 0]);
            assert_eq!(mask, &[255, 255, 255, 0]);
        }
        _ => assert_eq!(items4.len(), 2),
    }

    let mut ipv6 = vec![0u8; 32];
    if let Some(first) = ipv6.first_mut() {
        *first = 0x20;
    }
    if let Some(second) = ipv6.get_mut(1) {
        *second = 0x01;
    }
    for byte in ipv6.iter_mut().skip(16) {
        *byte = 0xff;
    }
    let base6 = tlv(0x87, &ipv6);
    let subtree6 = subtree(&base6, &[]);
    let permitted6 = tlv(0xa0, &subtree6);
    let encoded6 = name_constraints(&permitted6);
    let parsed6 = parse_name_constraints(&encoded6);
    assert!(parsed6.is_some());
    let Some(parsed6) = parsed6 else { return };
    let Some(items6) = parsed6.permitted_subtrees else {
        return;
    };
    match items6.first().map(|item| item.base) {
        Some(GeneralNameConstraint::IpAddress { address, mask }) => {
            assert_eq!(address.len(), 16);
            assert_eq!(address.first().copied(), Some(0x20));
            assert_eq!(mask, &[0xff; 16]);
        }
        _ => assert_eq!(items6.len(), 2),
    }
}

#[test]
fn permits_ordered_fields_and_preserves_unsupported_general_name() {
    let unsupported_base = [0xa4, 0x00]; // directoryName choice, preserved whole.
    let unsupported_subtree = subtree(&unsupported_base, &[]);
    let permitted = tlv(0xa0, &unsupported_subtree);
    let excluded_base = tlv(0x82, b"blocked.test");
    let excluded_subtree = subtree(&excluded_base, &[]);
    let excluded = tlv(0xa1, &excluded_subtree);
    let mut fields = permitted;
    fields.extend_from_slice(&excluded);
    let encoded = name_constraints(&fields);
    let parsed = parse_name_constraints(&encoded);
    assert!(parsed.is_some());
    let Some(parsed) = parsed else { return };
    let Some(items) = parsed.permitted_subtrees else {
        return;
    };
    match items.first().map(|item| item.base) {
        Some(base @ GeneralNameConstraint::Unsupported { tag: 4, der }) => {
            assert_eq!(der, &unsupported_base);
            assert!(!general_name_constraint_supported(base));
        }
        _ => assert_eq!(items.len(), 2),
    }
    assert!(parsed.excluded_subtrees.is_some());
}

#[test]
fn rejects_bad_ip_widths_and_general_name_tag_forms() {
    let bad_ip = tlv(0x87, &[192, 0, 2, 1, 255, 255, 255]);
    let bad_subtree = subtree(&bad_ip, &[]);
    assert!(parse_name_constraints(&name_constraints(&tlv(0xa0, &bad_subtree))).is_none());

    let constructed_dns = tlv(0xa2, b"a.test");
    let malformed_subtree = subtree(&constructed_dns, &[]);
    assert!(parse_name_constraints(&name_constraints(&tlv(0xa0, &malformed_subtree))).is_none());

    let unknown_tag = [0x89, 0x00];
    let malformed_subtree = subtree(&unknown_tag, &[]);
    assert!(parse_name_constraints(&name_constraints(&tlv(0xa0, &malformed_subtree))).is_none());
}

#[test]
fn rejects_empty_subtrees_explicit_default_minimum_and_maximum() {
    assert!(parse_name_constraints(&[0x30, 0x02, 0xa0, 0x00]).is_none());

    let base = tlv(0x82, b"a.test");
    let minimum_zero = subtree(&base, &[0x80, 0x01, 0x00]);
    assert!(parse_name_constraints(&name_constraints(&tlv(0xa0, &minimum_zero))).is_none());

    let maximum_one = subtree(&base, &[0x81, 0x01, 0x01]);
    assert!(parse_name_constraints(&name_constraints(&tlv(0xa0, &maximum_one))).is_none());
}

#[test]
fn rejects_field_reordering_trailing_bytes_and_bad_outer_consumption() {
    let base = tlv(0x82, b"a.test");
    let sub = subtree(&base, &[]);
    let excluded = tlv(0xa1, &sub);
    let permitted = tlv(0xa0, &sub);
    let mut reversed = excluded;
    reversed.extend_from_slice(&permitted);
    assert!(parse_name_constraints(&name_constraints(&reversed)).is_none());

    let only_permitted = tlv(0xa0, &sub);
    let mut trailing = name_constraints(&only_permitted);
    trailing.extend_from_slice(&[0x05, 0x00]);
    assert!(parse_name_constraints(&trailing).is_none());

    assert!(parse_name_constraints(&[0x30, 0x00]).is_some());
}
