//! RFC 5280 §4.2.1.11 PolicyConstraints known answers, written out by hand
//! from the ASN.1: `80` is `[0] requireExplicitPolicy` and `81` is
//! `[1] inhibitPolicyMapping`, primitive and implicit over an INTEGER.

use clazel_x509::policy_constraints::exec::parse_policy_constraints;

/// (requireExplicitPolicy, inhibitPolicyMapping) magnitudes.
type Fields = (Option<Vec<u8>>, Option<Vec<u8>>);

/// The decoded fields, or `None`.
fn decode(der: &[u8]) -> Option<Fields> {
    let parsed = parse_policy_constraints(der)?;
    Some((
        parsed.require_explicit_policy.map(<[u8]>::to_vec),
        parsed.inhibit_policy_mapping.map(<[u8]>::to_vec),
    ))
}

#[test]
fn decodes_both_fields_and_each_alone() {
    assert_eq!(
        decode(&[0x30, 0x06, 0x80, 0x01, 0x02, 0x81, 0x01, 0x03]),
        Some((Some(vec![2]), Some(vec![3])))
    );
    assert_eq!(
        decode(&[0x30, 0x03, 0x80, 0x01, 0x00]),
        Some((Some(vec![0]), None))
    );
    assert_eq!(
        decode(&[0x30, 0x03, 0x81, 0x01, 0x05]),
        Some((None, Some(vec![5])))
    );
}

#[test]
fn an_empty_sequence_is_refused() {
    // "Conforming CAs MUST NOT issue" one (RFC 5280 §4.2.1.11).
    assert_eq!(decode(&[0x30, 0x00]), None);
}

#[test]
fn negative_and_non_minimal_values_are_refused() {
    assert_eq!(decode(&[0x30, 0x03, 0x80, 0x01, 0x80]), None);
    assert_eq!(decode(&[0x30, 0x03, 0x81, 0x01, 0xFF]), None);
    // A redundant 0x00, and a redundant 0xFF.
    assert_eq!(decode(&[0x30, 0x04, 0x80, 0x02, 0x00, 0x05]), None);
    assert_eq!(decode(&[0x30, 0x04, 0x80, 0x02, 0xFF, 0x80]), None);
    // Empty contents.
    assert_eq!(decode(&[0x30, 0x02, 0x80, 0x00]), None);
}

#[test]
fn the_sign_pad_is_not_part_of_the_magnitude() {
    assert_eq!(
        decode(&[0x30, 0x04, 0x80, 0x02, 0x00, 0x80]),
        Some((Some(vec![0x80]), None))
    );
}

#[test]
fn values_below_2_pow_32_are_accepted_and_larger_are_refused() {
    assert_eq!(
        decode(&[0x30, 0x07, 0x80, 0x05, 0x00, 0xFF, 0xFF, 0xFF, 0xFF]),
        Some((Some(vec![0xFF, 0xFF, 0xFF, 0xFF]), None))
    );
    assert_eq!(
        decode(&[0x30, 0x07, 0x80, 0x05, 0x01, 0x00, 0x00, 0x00, 0x00]),
        None
    );
    assert_eq!(
        decode(&[
            0x30, 0x0A, 0x81, 0x08, 0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF
        ]),
        None
    );
}

#[test]
fn wrong_tags_order_and_trailing_bytes_are_refused() {
    // A universal INTEGER, a constructed [0], and [2].
    assert_eq!(decode(&[0x30, 0x03, 0x02, 0x01, 0x00]), None);
    assert_eq!(decode(&[0x30, 0x05, 0xA0, 0x03, 0x02, 0x01, 0x00]), None);
    assert_eq!(decode(&[0x30, 0x03, 0x82, 0x01, 0x00]), None);
    // [1] before [0], and a repeated field.
    assert_eq!(
        decode(&[0x30, 0x06, 0x81, 0x01, 0x03, 0x80, 0x01, 0x02]),
        None
    );
    assert_eq!(
        decode(&[0x30, 0x06, 0x80, 0x01, 0x01, 0x80, 0x01, 0x02]),
        None
    );
    // Bytes inside and after the SEQUENCE.
    assert_eq!(decode(&[0x30, 0x05, 0x80, 0x01, 0x00, 0x05, 0x00]), None);
    assert_eq!(decode(&[0x30, 0x03, 0x80, 0x01, 0x00, 0x05, 0x00]), None);
    // Not a SEQUENCE, and truncated.
    assert_eq!(decode(&[0x31, 0x03, 0x80, 0x01, 0x00]), None);
    assert_eq!(decode(&[0x30, 0x03, 0x80, 0x01]), None);
}
