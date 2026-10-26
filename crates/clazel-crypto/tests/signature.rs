//! CertificateVerify signature checks (`clazel_crypto::signature::verify`)
//! with the standards' own vectors where they exist: RFC 8032 §7.1 TEST 1
//! and TEST 2 (Ed25519) and RFC 6979 A.2.5 (ECDSA P-256, SHA-256, message
//! "sample"). RSA-PSS has no deterministic vector; its fixtures are in
//! tests/fixtures/rsa-pss (see SOURCE.md there). Every refusal the spec's
//! modelling choices list is exercised.

use clazel_crypto::signature::verify;

const ECDSA_P256_SHA256: u16 = 0x0403;
const RSA_PSS_RSAE_SHA256: u16 = 0x0804;
const RSA_PSS_RSAE_SHA384: u16 = 0x0805;
const RSA_PSS_RSAE_SHA512: u16 = 0x0806;
const ED25519: u16 = 0x0807;
const RSA_PSS_PSS_SHA256: u16 = 0x0809;

type TestResult = Result<(), String>;

fn hex(text: &str) -> Result<Vec<u8>, String> {
    let digits: Vec<u8> = text.bytes().filter(|b| !b.is_ascii_whitespace()).collect();
    digits
        .chunks(2)
        .map(|pair| {
            let pair = std::str::from_utf8(pair).map_err(|e| e.to_string())?;
            u8::from_str_radix(pair, 16).map_err(|e| format!("{pair}: {e}"))
        })
        .collect()
}

/// A DER TLV with a short-form length (every value here is under 128 octets).
fn tlv(tag: u8, value: &[u8]) -> Result<Vec<u8>, String> {
    let len = u8::try_from(value.len()).map_err(|e| e.to_string())?;
    if len >= 0x80 {
        return Err("long-form length not needed here".into());
    }
    Ok([&[tag, len][..], value].concat())
}

/// A non-negative DER INTEGER with magnitude `m` (a sign octet if needed).
fn der_uint(m: &[u8]) -> Result<Vec<u8>, String> {
    let needs_pad = m.first().is_some_and(|b| *b >= 0x80);
    let value = if needs_pad {
        [&[0u8][..], m].concat()
    } else {
        m.to_vec()
    };
    tlv(0x02, &value)
}

fn ecdsa_sig(r: &[u8], s: &[u8]) -> Result<Vec<u8>, String> {
    tlv(0x30, &[der_uint(r)?, der_uint(s)?].concat())
}

fn p256_spki(point: &[u8]) -> Result<Vec<u8>, String> {
    let algorithm = tlv(
        0x30,
        &[
            tlv(0x06, &hex("2a8648ce3d0201")?)?,
            tlv(0x06, &hex("2a8648ce3d030107")?)?,
        ]
        .concat(),
    )?;
    let key = tlv(0x03, &[&[0u8][..], point].concat())?;
    tlv(0x30, &[algorithm, key].concat())
}

fn ed25519_spki(key: &[u8], with_null_parameters: bool) -> Result<Vec<u8>, String> {
    let mut algorithm = tlv(0x06, &hex("2b6570")?)?;
    if with_null_parameters {
        algorithm.extend_from_slice(&[0x05, 0x00]);
    }
    let algorithm = tlv(0x30, &algorithm)?;
    let key = tlv(0x03, &[&[0u8][..], key].concat())?;
    tlv(0x30, &[algorithm, key].concat())
}

struct P256 {
    spki: Vec<u8>,
    point: Vec<u8>,
    r: Vec<u8>,
    s: Vec<u8>,
}

/// RFC 6979 A.2.5: the key pair and the SHA-256 signature of "sample".
fn rfc_6979() -> Result<P256, String> {
    let x = hex("60FED4BA255A9D31C961EB74C6356D68C049B8923B61FA6CE669622E60F29FB6")?;
    let y = hex("7903FE1008B8BC99A41AE9E95628BC64F2F1B20C2D7E9F5177A3C294D4462299")?;
    let point = [&[0x04u8][..], &x, &y].concat();
    Ok(P256 {
        spki: p256_spki(&point)?,
        point,
        r: hex("EFD48B2AACB6A8FD1140DD9CD45E81D69D2C877B56AAF991C34D0EA84EAF3716")?,
        s: hex("F7CB1C942D657C41D436C7A1B6E29F65F3E900DBB9AFF4064DC4AB2F843ACDA8")?,
    })
}

#[test]
#[cfg_attr(miri, ignore = "full P-256 verifications are slow under Miri")]
fn ecdsa_p256_sha256_rfc_6979_a_2_5() -> TestResult {
    let v = rfc_6979()?;
    let sig = ecdsa_sig(&v.r, &v.s)?;
    assert!(verify(&v.spki, ECDSA_P256_SHA256, b"sample", &sig));
    // Another message, another scheme number, a swapped r and s.
    assert!(!verify(&v.spki, ECDSA_P256_SHA256, b"samplf", &sig));
    assert!(!verify(&v.spki, RSA_PSS_RSAE_SHA256, b"sample", &sig));
    assert!(!verify(
        &v.spki,
        ECDSA_P256_SHA256,
        b"sample",
        &ecdsa_sig(&v.s, &v.r)?
    ));
    Ok(())
}

#[test]
fn ecdsa_refuses_malformed_signatures() -> TestResult {
    let v = rfc_6979()?;
    let sig = ecdsa_sig(&v.r, &v.s)?;
    // Trailing octets after the Ecdsa-Sig-Value.
    let mut trailing = sig.clone();
    trailing.push(0);
    assert!(!verify(&v.spki, ECDSA_P256_SHA256, b"sample", &trailing));
    // r with 33 magnitude octets (a leading 0x01 makes it too large).
    let long_r = [&[0x01u8][..], &v.r].concat();
    assert!(!verify(
        &v.spki,
        ECDSA_P256_SHA256,
        b"sample",
        &ecdsa_sig(&long_r, &v.s)?
    ));
    // A negative r: the magnitude without its sign octet.
    let negative = tlv(0x30, &[tlv(0x02, &v.r)?, der_uint(&v.s)?].concat())?;
    assert!(!verify(&v.spki, ECDSA_P256_SHA256, b"sample", &negative));
    // r = 0 (libcrux checks 1 <= r < n).
    assert!(!verify(
        &v.spki,
        ECDSA_P256_SHA256,
        b"sample",
        &ecdsa_sig(&[0], &v.s)?
    ));
    // Raw r || s instead of DER.
    let raw = [v.r.clone(), v.s.clone()].concat();
    assert!(!verify(&v.spki, ECDSA_P256_SHA256, b"sample", &raw));
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "P-256 point checks are slow under Miri")]
fn ecdsa_refuses_other_key_encodings() -> TestResult {
    let v = rfc_6979()?;
    let sig = ecdsa_sig(&v.r, &v.s)?;
    // The compressed form of the same point (RFC 5480 §2.2 makes it optional).
    let y_last = v.point.last().ok_or("empty point")?;
    let prefix = if y_last % 2 == 0 { 0x02u8 } else { 0x03u8 };
    let x = v.point.get(1..33).ok_or("short point")?;
    let compressed = p256_spki(&[&[prefix][..], x].concat())?;
    assert!(!verify(&compressed, ECDSA_P256_SHA256, b"sample", &sig));
    // A point not on the curve (Y + 1).
    let mut off_curve = v.point.clone();
    let last = off_curve.last_mut().ok_or("empty point")?;
    *last ^= 1;
    assert!(!verify(
        &p256_spki(&off_curve)?,
        ECDSA_P256_SHA256,
        b"sample",
        &sig
    ));
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "full Ed25519 verifications are slow under Miri")]
fn ed25519_rfc_8032_tests_1_and_2() -> TestResult {
    let key1 = hex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")?;
    let sig1 = hex(
        "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155
         5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
    )?;
    let key2 = hex("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c")?;
    let sig2 = hex(
        "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da
         085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
    )?;
    assert!(verify(&ed25519_spki(&key1, false)?, ED25519, b"", &sig1));
    assert!(verify(
        &ed25519_spki(&key2, false)?,
        ED25519,
        &[0x72],
        &sig2
    ));
    // The other test's key, message or signature.
    assert!(!verify(
        &ed25519_spki(&key1, false)?,
        ED25519,
        &[0x72],
        &sig2
    ));
    assert!(!verify(
        &ed25519_spki(&key2, false)?,
        ED25519,
        &[0x73],
        &sig2
    ));
    let mut tampered = sig1.clone();
    let first = tampered.first_mut().ok_or("empty signature")?;
    *first ^= 1;
    assert!(!verify(
        &ed25519_spki(&key1, false)?,
        ED25519,
        b"",
        &tampered
    ));
    // RFC 8410 §3: parameters must be absent.
    assert!(!verify(&ed25519_spki(&key1, true)?, ED25519, b"", &sig1));
    // A signature of the wrong length, and the wrong scheme.
    assert!(!verify(
        &ed25519_spki(&key1, false)?,
        ED25519,
        b"",
        sig1.get(..63).ok_or("short")?
    ));
    assert!(!verify(
        &ed25519_spki(&key1, false)?,
        ECDSA_P256_SHA256,
        b"",
        &sig1
    ));
    Ok(())
}

fn fixture(name: &str) -> Result<Vec<u8>, String> {
    let path = format!(
        "{}/tests/fixtures/rsa-pss/{name}",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::read(&path).map_err(|e| format!("{path}: {e}"))
}

#[test]
#[cfg_attr(miri, ignore = "reads fixtures; RSA-2048 is slow under Miri")]
fn rsa_pss_rsae_sha256_384_512() -> TestResult {
    let key = fixture("k2048.spki.der")?;
    let message = fixture("msg.bin")?;
    let sig256 = fixture("k2048.sha256.sig")?;
    let sig384 = fixture("k2048.sha384.sig")?;
    let sig512 = fixture("k2048.sha512.sig")?;
    assert!(verify(&key, RSA_PSS_RSAE_SHA256, &message, &sig256));
    assert!(verify(&key, RSA_PSS_RSAE_SHA384, &message, &sig384));
    assert!(verify(&key, RSA_PSS_RSAE_SHA512, &message, &sig512));
    // Each signature under another hash's scheme.
    assert!(!verify(&key, RSA_PSS_RSAE_SHA384, &message, &sig256));
    assert!(!verify(&key, RSA_PSS_RSAE_SHA256, &message, &sig512));
    // Another message, a flipped bit, a truncated signature.
    assert!(!verify(
        &key,
        RSA_PSS_RSAE_SHA256,
        b"another message",
        &sig256
    ));
    let mut tampered = sig256.clone();
    let last = tampered.last_mut().ok_or("empty signature")?;
    *last ^= 1;
    assert!(!verify(&key, RSA_PSS_RSAE_SHA256, &message, &tampered));
    assert!(!verify(
        &key,
        RSA_PSS_RSAE_SHA256,
        &message,
        sig256.get(1..).ok_or("short")?
    ));
    // rsa_pss_pss_* is not offered and never verified.
    assert!(!verify(&key, RSA_PSS_PSS_SHA256, &message, &sig256));
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "reads fixtures from disk")]
fn rsa_refuses_keys_outside_the_profile() -> TestResult {
    let message = fixture("msg.bin")?;
    // e = 3: refused, never verified with another exponent.
    assert!(!verify(
        &fixture("ke3.spki.der")?,
        RSA_PSS_RSAE_SHA256,
        &message,
        &fixture("ke3.sha256.sig")?
    ));
    // A 2047-bit modulus.
    assert!(!verify(
        &fixture("k2047.spki.der")?,
        RSA_PSS_RSAE_SHA256,
        &message,
        &fixture("k2047.sha256.sig")?
    ));
    Ok(())
}

#[test]
fn garbage_keys_and_unknown_schemes_are_refused() -> TestResult {
    let v = rfc_6979()?;
    let sig = ecdsa_sig(&v.r, &v.s)?;
    assert!(!verify(&[], ECDSA_P256_SHA256, b"sample", &sig));
    assert!(!verify(
        v.spki.get(1..).ok_or("short spki")?,
        ECDSA_P256_SHA256,
        b"sample",
        &sig
    ));
    for scheme in [0x0000u16, 0x0401, 0x0503, 0x0808, 0x0809, 0xffff] {
        assert!(
            !verify(&v.spki, scheme, b"sample", &sig),
            "scheme {scheme:#06x}"
        );
    }
    Ok(())
}
