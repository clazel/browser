//! Independent RSA and unsupported-algorithm fixtures for RFC 5280 §4.1.2.7.

use clazel_x509::spki::exec::{PublicKey, parse_subject_public_key_info};

fn rsa_spki(modulus: &[u8], exponent: &[u8], unused_bits: u8, parameters: &[u8]) -> Vec<u8> {
    let mut rsa = vec![0x30, 0x00];
    let mut rsa_contents = Vec::new();
    rsa_contents.extend_from_slice(modulus);
    rsa_contents.extend_from_slice(exponent);
    if let Some(length) = rsa.get_mut(1) {
        *length = u8::try_from(rsa_contents.len()).unwrap_or(0);
    }
    rsa.extend_from_slice(&rsa_contents);

    let mut bits = vec![unused_bits];
    bits.extend_from_slice(&rsa);
    let mut bit_string = vec![0x03, u8::try_from(bits.len()).unwrap_or(0)];
    bit_string.extend_from_slice(&bits);

    let mut algorithm_contents = vec![
        0x06, 0x09, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x01, 0x01,
    ];
    algorithm_contents.extend_from_slice(parameters);
    let mut algorithm = vec![0x30, u8::try_from(algorithm_contents.len()).unwrap_or(0)];
    algorithm.extend_from_slice(&algorithm_contents);

    let mut contents = algorithm;
    contents.extend_from_slice(&bit_string);
    let mut spki = vec![0x30, u8::try_from(contents.len()).unwrap_or(0)];
    spki.extend_from_slice(&contents);
    spki
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
fn decodes_rsa_and_retains_signed_der_and_positive_magnitudes() {
    let input = rsa_spki(
        &[0x02, 0x02, 0x00, 0x80],
        &[0x02, 0x01, 0x03],
        0,
        &[0x05, 0x00],
    );
    let parsed = parse_subject_public_key_info(&input);
    assert!(parsed.is_some());
    let Some(parsed) = parsed else {
        return;
    };
    assert_eq!(parsed.spki_der, input.as_slice());
    assert_eq!(parsed.subject_public_key_unused_bits, 0);
    assert_eq!(parsed.subject_public_key_bits.last(), Some(&0x03));
    assert!(matches!(&parsed.public_key, PublicKey::Rsa(_)));
    match parsed.public_key {
        PublicKey::Rsa(key) => {
            assert_eq!(key.encoded_der, parsed.subject_public_key_bits);
            assert_eq!(key.modulus_der, &[0x02, 0x02, 0x00, 0x80]);
            assert_eq!(key.modulus_octets, &[0x80]);
            assert_eq!(key.public_exponent_der, &[0x02, 0x01, 0x03]);
            assert_eq!(key.public_exponent_octets, &[0x03]);
        }
        PublicKey::Unsupported => (),
    }
}

#[test]
fn unknown_algorithm_is_explicit_and_retains_key_bits() {
    let input = [
        0x30, 0x0B, 0x30, 0x04, 0x06, 0x02, 0x2A, 0x03, 0x03, 0x03, 0x03, 0xF0, 0xA0,
    ];
    let parsed = parse_subject_public_key_info(&input);
    assert!(parsed.is_some());
    let Some(parsed) = parsed else {
        return;
    };
    assert!(matches!(parsed.public_key, PublicKey::Unsupported));
    assert_eq!(parsed.algorithm.oid, vec![1, 2, 3]);
    assert_eq!(parsed.subject_public_key_unused_bits, 3);
    assert_eq!(parsed.subject_public_key_bits, &[0xF0, 0xA0]);
    assert_eq!(parsed.spki_der, input.as_slice());
}

#[test]
fn rejects_bad_rsa_parameters_nonzero_unused_bits_and_zero_integers() {
    let no_parameters = rsa_spki(&[0x02, 0x01, 0x01], &[0x02, 0x01, 0x03], 0, &[]);
    assert!(parse_subject_public_key_info(&no_parameters).is_none());

    let nonzero_unused = rsa_spki(&[0x02, 0x01, 0x02], &[0x02, 0x01, 0x02], 1, &[0x05, 0x00]);
    assert!(parse_subject_public_key_info(&nonzero_unused).is_none());

    let zero_modulus = rsa_spki(&[0x02, 0x01, 0x00], &[0x02, 0x01, 0x03], 0, &[0x05, 0x00]);
    assert!(parse_subject_public_key_info(&zero_modulus).is_none());

    let zero_exponent = rsa_spki(&[0x02, 0x01, 0x03], &[0x02, 0x01, 0x00], 0, &[0x05, 0x00]);
    assert!(parse_subject_public_key_info(&zero_exponent).is_none());
}

#[test]
fn rejects_extra_fields_trailing_data_and_wrong_outer_tags() {
    let mut input = rsa_spki(&[0x02, 0x01, 0x03], &[0x02, 0x01, 0x03], 0, &[0x05, 0x00]);
    let _ = replace_byte(&mut input, 0, 0x31);
    assert!(parse_subject_public_key_info(&input).is_none());

    let mut trailing = rsa_spki(&[0x02, 0x01, 0x03], &[0x02, 0x01, 0x03], 0, &[0x05, 0x00]);
    trailing.push(0x00);
    assert!(parse_subject_public_key_info(&trailing).is_none());

    let extra_field = rsa_spki(
        &[0x02, 0x01, 0x03],
        &[0x02, 0x01, 0x03, 0x02, 0x01, 0x01],
        0,
        &[0x05, 0x00],
    );
    assert!(parse_subject_public_key_info(&extra_field).is_none());
}
