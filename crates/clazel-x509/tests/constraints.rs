//! Adversarial checks for RFC 5280 constraints extension decoders.

use clazel_x509::constraints::exec::{
    KeyUsageBit, basic_constraints_compatible, eku_allows_server_auth, key_usage_has,
    parse_basic_constraints, parse_extended_key_usage, parse_key_usage,
};

#[test]
fn basic_constraints_defaults_and_accepts_zero_path_length_for_ca() {
    let defaulted = parse_basic_constraints(&[0x30, 0x00]);
    assert!(defaulted.is_some());
    let Some(defaulted) = defaulted else { return };
    assert!(!defaulted.ca);
    assert!(defaulted.path_len_constraint.is_none());

    let ca_with_zero_path =
        parse_basic_constraints(&[0x30, 0x06, 0x01, 0x01, 0xff, 0x02, 0x01, 0x00]);
    assert!(ca_with_zero_path.is_some());
    let Some(ca_with_zero_path) = ca_with_zero_path else {
        return;
    };
    assert!(ca_with_zero_path.ca);
    assert_eq!(ca_with_zero_path.path_len_constraint, Some(&[0x00][..]));
}

#[test]
fn basic_constraints_rejects_non_der_default_negative_or_extra_fields() {
    assert!(parse_basic_constraints(&[0x30, 0x03, 0x01, 0x01, 0x00]).is_none());
    assert!(parse_basic_constraints(&[0x30, 0x06, 0x01, 0x01, 0x00, 0x02, 0x01, 0x00]).is_none());
    assert!(parse_basic_constraints(&[0x30, 0x06, 0x01, 0x01, 0xff, 0x02, 0x01, 0xff]).is_none());
    assert!(parse_basic_constraints(&[0x30, 0x05, 0x01, 0x01, 0xff, 0x02, 0x00]).is_none());
    assert!(parse_basic_constraints(&[0x30, 0x03, 0x01, 0x01, 0x01]).is_none());
    assert!(parse_basic_constraints(&[0x30, 0x00, 0x05, 0x00]).is_none());
}

#[test]
fn basic_constraints_preserves_large_nonnegative_path_length_magnitude() {
    let input = [
        0x30, 0x0e, 0x01, 0x01, 0xff, 0x02, 0x09, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
        0x09,
    ];
    let parsed = parse_basic_constraints(&input);
    assert!(parsed.is_some());
    let Some(parsed) = parsed else { return };
    assert_eq!(parsed.path_len_constraint, Some(&input[7..16]));
}

#[test]
fn key_usage_decodes_named_bits_and_rejects_invalid_named_bit_forms() {
    let digital_signature = parse_key_usage(&[0x03, 0x02, 0x07, 0x80]);
    assert!(digital_signature.is_some());
    let Some(digital_signature) = digital_signature else {
        return;
    };
    assert!(key_usage_has(
        digital_signature,
        KeyUsageBit::DigitalSignature
    ));
    assert!(!key_usage_has(digital_signature, KeyUsageBit::KeyCertSign));

    let bit_eight = parse_key_usage(&[0x03, 0x03, 0x07, 0x00, 0x80]);
    assert!(bit_eight.is_some());
    let Some(bit_eight) = bit_eight else { return };
    assert!(key_usage_has(bit_eight, KeyUsageBit::DecipherOnly));

    assert!(parse_key_usage(&[0x03, 0x01, 0x00]).is_none());
    assert!(parse_key_usage(&[0x03, 0x03, 0x06, 0x00, 0x80]).is_none());
    assert!(parse_key_usage(&[0x03, 0x03, 0x07, 0x80, 0x00]).is_none());
    assert!(parse_key_usage(&[0x03, 0x02, 0x00, 0x00]).is_none());
    assert!(parse_key_usage(&[0x03, 0x02, 0x08, 0x80]).is_none());
    assert!(parse_key_usage(&[0x03, 0x02, 0x07, 0x00, 0x05, 0x00]).is_none());
}

#[test]
fn basic_constraints_and_key_usage_cross_conditions_are_explicit() {
    let ca = parse_basic_constraints(&[0x30, 0x03, 0x01, 0x01, 0xff]);
    let key_cert_sign = parse_key_usage(&[0x03, 0x02, 0x02, 0x04]);
    assert!(basic_constraints_compatible(ca, key_cert_sign));
    assert!(!basic_constraints_compatible(None, key_cert_sign));

    let path_len = parse_basic_constraints(&[0x30, 0x06, 0x01, 0x01, 0xff, 0x02, 0x01, 0x00]);
    assert!(!basic_constraints_compatible(path_len, None));
    assert!(basic_constraints_compatible(path_len, key_cert_sign));
    let end_entity = parse_basic_constraints(&[0x30, 0x00]);
    assert!(basic_constraints_compatible(end_entity, None));
}

#[test]
fn extended_key_usage_is_nonempty_unique_and_has_explicit_any_policy() {
    let server_auth = [
        0x30, 0x0a, 0x06, 0x08, 0x2b, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x01,
    ];
    let parsed = parse_extended_key_usage(&server_auth);
    assert!(parsed.is_some());
    let Some(parsed) = parsed else { return };
    assert!(eku_allows_server_auth(parsed, false));

    let any_eku = [0x30, 0x06, 0x06, 0x04, 0x55, 0x1d, 0x25, 0x00];
    let parsed_any = parse_extended_key_usage(&any_eku);
    assert!(parsed_any.is_some());
    let Some(parsed_any) = parsed_any else { return };
    assert!(!eku_allows_server_auth(parsed_any, false));
    let parsed_any = parse_extended_key_usage(&any_eku);
    assert!(parsed_any.is_some());
    let Some(parsed_any) = parsed_any else { return };
    assert!(eku_allows_server_auth(parsed_any, true));

    assert!(parse_extended_key_usage(&[0x30, 0x00]).is_none());
    assert!(
        parse_extended_key_usage(&[
            0x30, 0x0c, 0x06, 0x04, 0x55, 0x1d, 0x25, 0x00, 0x06, 0x04, 0x55, 0x1d, 0x25, 0x00
        ])
        .is_none()
    );
    assert!(
        parse_extended_key_usage(&[0x30, 0x06, 0x06, 0x04, 0x55, 0x1d, 0x25, 0x00, 0x05, 0x00])
            .is_none()
    );
}
