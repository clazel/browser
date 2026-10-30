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
        PublicKey::EcP256(_) | PublicKey::EcP384(_) | PublicKey::Unsupported => (),
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

/// Independent known answers: keys generated with `openssl ecparam` (LibreSSL
/// 3.3.6) and written with `openssl ec -pubout`; the expected points are
/// the `pub:` octets that `openssl ec -text` prints, not read from our
/// decoder.
mod ec {
    use super::{PublicKey, parse_subject_public_key_info};

    /// prime256v1, 91 octets (RFC 5480 §2.1.1).
    const P256_SPKI: &str = "3059301306072a8648ce3d020106082a8648ce3d0301070342000462221489361cbf692338cb1c55f7703e3499180eadc7687d662033568a267f672a38d6ba139d54852df13bc50aea510ad435d0b01923ed0bde0656b2c8d484ff";
    /// secp384r1, 120 octets.
    const P384_SPKI: &str = "3076301006072a8648ce3d020106052b810400220362000455caf3f821d1ec7fa2309dba54e7b0c0e32ad8f9a178807f3a45131c3d9225597d48585ab736d086fe12843d191b1621cf5036722ccbbd034bfe9b92dabef25b6e26def9345c9e8f3f67e22fbfd3b91c21b9002c2d450f68b886c7c2bfd6c768";

    pub fn unhex(text: &str) -> Vec<u8> {
        text.as_bytes()
            .chunks(2)
            .map(|pair| {
                let digits: String = pair.iter().map(|&b| char::from(b)).collect();
                u8::from_str_radix(&digits, 16).unwrap_or(0)
            })
            .collect()
    }

    /// Replace the first occurrence of `from` in `der` by `to` (same length).
    fn patched(der: &[u8], from: &[u8], to: &[u8]) -> Vec<u8> {
        let mut out = der.to_vec();
        if let Some(at) = der.windows(from.len()).position(|w| w == from) {
            for (offset, byte) in to.iter().enumerate() {
                if let Some(slot) = out.get_mut(at.saturating_add(offset)) {
                    *slot = *byte;
                }
            }
        }
        out
    }

    #[test]
    fn p256_key_is_classified_with_x_and_y() {
        let der = unhex(P256_SPKI);
        let parsed = parse_subject_public_key_info(&der);
        assert!(parsed.is_some());
        let Some(parsed) = parsed else { return };
        assert!(matches!(parsed.public_key, PublicKey::EcP256(_)));
        let PublicKey::EcP256(xy) = parsed.public_key else {
            return;
        };
        // `openssl ec -text` prints 04 || X || Y; EcP256 holds X || Y.
        assert_eq!(xy.len(), 64);
        assert_eq!(xy.first(), Some(&0x62));
        assert_eq!(xy.last(), Some(&0xff));
        assert_eq!(xy, parsed.subject_public_key_bits.get(1..).unwrap_or(&[]));
        assert_eq!(parsed.subject_public_key_bits.first(), Some(&0x04));
    }

    #[test]
    fn p384_key_is_classified_with_the_whole_ecpoint() {
        let der = unhex(P384_SPKI);
        let parsed = parse_subject_public_key_info(&der);
        assert!(parsed.is_some());
        let Some(parsed) = parsed else { return };
        assert!(matches!(parsed.public_key, PublicKey::EcP384(_)));
        let PublicKey::EcP384(point) = parsed.public_key else {
            return;
        };
        // The 97-octet ECPoint, 0x04 included (clazel-p384 decodes it).
        assert_eq!(point.len(), 97);
        assert_eq!(point.first(), Some(&0x04));
        assert_eq!(point.get(1), Some(&0x55));
        assert_eq!(point.last(), Some(&0x68));
        assert_eq!(point, parsed.subject_public_key_bits);
    }

    #[test]
    fn unclassified_ec_keys_still_parse_as_unsupported() {
        let p256 = unhex(P256_SPKI);
        // The compressed prefix 0x02 on a 65-octet point.
        let compressed_prefix = patched(&p256, &[0x00, 0x04, 0x62], &[0x00, 0x02, 0x62]);
        // secp256r1's curve OID 1.2.840.10045.3.1.7 -> 1.2.840.10045.3.1.1
        // (prime192v1), a named curve that is not classified.
        let other_curve = patched(
            &p256,
            &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07],
            &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x01],
        );
        // The P-384 key's curve 1.3.132.0.34 -> secp521r1's 1.3.132.0.35.
        let p384 = unhex(P384_SPKI);
        let p521 = patched(
            &p384,
            &[0x2b, 0x81, 0x04, 0x00, 0x22],
            &[0x2b, 0x81, 0x04, 0x00, 0x23],
        );
        // id-ecPublicKey 1.2.840.10045.2.1 -> a near miss, ...2.2.
        let wrong_oid = patched(
            &p256,
            &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01],
            &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x02],
        );
        for der in [compressed_prefix, other_curve, p521, wrong_oid] {
            let parsed = parse_subject_public_key_info(&der);
            assert!(parsed.is_some());
            let Some(parsed) = parsed else { return };
            assert!(matches!(parsed.public_key, PublicKey::Unsupported));
        }
    }

    #[test]
    fn unused_bits_wrong_length_and_missing_parameters_are_unsupported() {
        let p256 = unhex(P256_SPKI);
        // BIT STRING unused-bits octet 0 -> 1.
        let unused = patched(&p256, &[0x03, 0x42, 0x00, 0x04], &[0x03, 0x42, 0x01, 0x04]);
        // A 66-octet point: BIT STRING length 0x42 -> 0x43 with an extra
        // octet, and the outer lengths grown to match.
        let mut long = p256.clone();
        long.push(0x00);
        long = patched(&long, &[0x30, 0x59], &[0x30, 0x5a]);
        long = patched(&long, &[0x03, 0x42], &[0x03, 0x43]);
        // Parameters absent: AlgorithmIdentifier is just id-ecPublicKey.
        let mut absent = vec![0x30, 0x4f, 0x30, 0x09, 0x06, 0x07];
        absent.extend_from_slice(&[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01]);
        absent.extend_from_slice(&[0x03, 0x42]);
        absent.extend_from_slice(p256.get(p256.len().saturating_sub(66)..).unwrap_or(&[]));
        // DER also wants the unused low bit of the last octet (0xff) clear,
        // so the SPKI itself is refused; a key is never classified from it.
        assert!(parse_subject_public_key_info(&unused).is_none());
        for der in [long, absent] {
            let parsed = parse_subject_public_key_info(&der);
            assert!(parsed.is_some());
            let Some(parsed) = parsed else { return };
            assert!(matches!(parsed.public_key, PublicKey::Unsupported));
        }
    }
}
