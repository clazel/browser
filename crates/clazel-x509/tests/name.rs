//! Independent DER Name and RDN structural decoder fixtures.

use clazel_x509::name::exec::parse_name;

const NAME_CN_A: [u8; 14] = [
    0x30, 0x0c, 0x31, 0x0a, 0x30, 0x08, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0c, 0x01, 0x61,
];

#[test]
fn parses_and_preserves_name_rdn_and_attribute_encodings() {
    let parsed = parse_name(&NAME_CN_A);
    assert!(parsed.is_some());
    if let Some(name) = parsed {
        assert_eq!(name.der, NAME_CN_A);
        assert_eq!(name.rdns.len(), 1);
        if let Some(rdn) = name.rdns.first() {
            assert_eq!(
                rdn.der,
                [
                    0x31, 0x0a, 0x30, 0x08, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0c, 0x01, 0x61
                ]
            );
            assert_eq!(rdn.attributes.len(), 1);
            if let Some(attribute) = rdn.attributes.first() {
                assert_eq!(
                    attribute.der,
                    [0x30, 0x08, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0c, 0x01, 0x61]
                );
                assert_eq!(attribute.oid, vec![2, 5, 4, 3]);
                assert_eq!(attribute.value_der, &[0x0c, 0x01, 0x61]);
                assert_eq!(
                    attribute.value_tag.class,
                    clazel_der::spec::Class::Universal
                );
                assert!(!attribute.value_tag.constructed);
                assert_eq!(attribute.value_tag.number, 12);
            }
        }
    }
}

#[test]
fn accepts_empty_name_sequence_but_rejects_empty_rdn() {
    assert!(parse_name(&[0x30, 0x00]).is_some());
    assert!(parse_name(&[0x30, 0x02, 0x31, 0x00]).is_none());
}

#[test]
fn accepts_der_ordered_multi_attribute_rdn() {
    // CN precedes OU by the complete AttributeTypeAndValue encodings.
    let ordered = [
        0x30, 0x16, 0x31, 0x14, 0x30, 0x08, 0x06, 0x03, 0x55, 0x04, 0x03, 0x13, 0x01, 0x61, 0x30,
        0x08, 0x06, 0x03, 0x55, 0x04, 0x0b, 0x16, 0x01, 0x62,
    ];
    let parsed = parse_name(&ordered);
    assert!(parsed.is_some());
    if let Some(name) = parsed
        && let Some(rdn) = name.rdns.first()
    {
        assert_eq!(rdn.attributes.len(), 2);
    }
}

#[test]
fn rejects_noncanonical_order_and_malformed_name_shapes() {
    let reversed = [
        0x30, 0x16, 0x31, 0x14, 0x30, 0x08, 0x06, 0x03, 0x55, 0x04, 0x0b, 0x16, 0x01, 0x62, 0x30,
        0x08, 0x06, 0x03, 0x55, 0x04, 0x03, 0x13, 0x01, 0x61,
    ];
    assert!(parse_name(&reversed).is_none());
    assert!(parse_name(&[0x31, 0x00]).is_none());
    assert!(parse_name(&[0x30, 0x01, 0x00]).is_none());
    assert!(
        parse_name(&[
            0x30, 0x0c, 0x31, 0x0a, 0x30, 0x08, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0c, 0x01, 0x61,
            0x00
        ])
        .is_none()
    );
    assert!(
        NAME_CN_A
            .get(..NAME_CN_A.len().saturating_sub(1))
            .is_some_and(|truncated| parse_name(truncated).is_none())
    );
}

#[test]
fn rejects_attribute_missing_oid_or_value_and_extra_children() {
    let no_oid = [0x30, 0x04, 0x31, 0x02, 0x30, 0x00];
    let no_value = [
        0x30, 0x09, 0x31, 0x07, 0x30, 0x05, 0x06, 0x03, 0x55, 0x04, 0x03,
    ];
    let extra_value = [
        0x30, 0x0f, 0x31, 0x0d, 0x30, 0x0b, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0c, 0x01, 0x61, 0x05,
        0x00,
    ];
    assert!(parse_name(&no_oid).is_none());
    assert!(parse_name(&no_value).is_none());
    assert!(parse_name(&extra_value).is_none());
}
