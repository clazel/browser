//! Certificate-chain links (`clazel_crypto::chain::exec`, proven equal to
//! `chain::spec::link`): known answers for each accepted class and each
//! refusal of the spec's modelling choices.
//!
//! - Our own certificates, in tests/fixtures/chain (see SOURCE.md there),
//!   each checked with `openssl verify` when generated, so every signature
//!   here is valid: a refusal is the profile's, never a bad signature.
//! - Mozilla's 118 server roots (`clazel_x509::roots::ROOTS`), each one's
//!   self-signature under its own key: real signatures from real CAs.

use clazel_crypto::chain::exec::{CertificateLinks, link};
use clazel_x509::certificate::exec::AlgorithmIdentifier;
use clazel_x509::path::contract::LinkVerifier;
use clazel_x509::path::parsed::exec::{PathCert, parse_path_cert};
use clazel_x509::spki::exec::{PublicKey, parse_subject_public_key_info};

type TestResult = Result<(), String>;

macro_rules! fixture {
    ($name:literal) => {
        include_bytes!(concat!("fixtures/chain/", $name)).as_slice()
    };
}

fn cert(der: &[u8]) -> Result<PathCert<'_>, String> {
    parse_path_cert(der).ok_or_else(|| "certificate does not parse".to_owned())
}

/// The link from `issuer`'s key to `child`, as `path::exec` asks it.
fn link_of(issuer: &PathCert<'_>, child: &PathCert<'_>) -> bool {
    CertificateLinks.verify(
        issuer.tbs.subject_public_key_info_der,
        &child.tbs.signature,
        child.envelope.tbs_certificate_der,
        child.envelope.signature_bits,
    )
}

/// A self-signed certificate's own link.
fn self_link(der: &[u8]) -> Result<bool, String> {
    let c = cert(der)?;
    Ok(link_of(&c, &c))
}

/// `der` with one bit of its TBSCertificate flipped (in the validity's last
/// digit, so it still parses).
fn flip_tbs(der: &[u8]) -> Result<Vec<u8>, String> {
    let c = cert(der)?;
    let tbs = c.envelope.tbs_certificate_der;
    let start = der
        .windows(tbs.len())
        .position(|w| w == tbs)
        .ok_or("no TBS")?;
    // The serial number's last octet: always inside the TBS, never a length.
    let serial = c.tbs.serial_number_der;
    let at = tbs
        .windows(serial.len())
        .position(|w| w == serial)
        .and_then(|p| p.checked_add(serial.len()))
        .and_then(|p| p.checked_sub(1))
        .and_then(|p| p.checked_add(start))
        .ok_or("no serial")?;
    let mut out = der.to_vec();
    let byte = out.get_mut(at).ok_or("index")?;
    *byte ^= 0x01;
    Ok(out)
}

fn oid(arcs: &[u64]) -> AlgorithmIdentifier<'static> {
    AlgorithmIdentifier {
        oid: arcs.to_vec(),
        parameters_der: None,
    }
}

const NULL: &[u8] = &[0x05, 0x00];

// ---------------------------------------------------------------------------
// Accepted classes
// ---------------------------------------------------------------------------

#[test]
#[cfg_attr(miri, ignore = "full RSA verifications are slow under Miri")]
fn rsa_pkcs1_v1_5_links_verify() -> TestResult {
    for der in [
        fixture!("rsa2048-sha256.der"),
        fixture!("rsa2048-sha384.der"),
        fixture!("rsa2048-sha512.der"),
        // e = 3, the smallest odd exponent clazel-pkcs1 accepts.
        fixture!("rsae3-sha256.der"),
        // e = 2^33 - 1, the largest BoringSSL accepts.
        fixture!("rsae2p33m1-sha256.der"),
        // 2052 bits: not a multiple of 8, accepted as Chrome, Firefox and
        // webpki accept it (CA/B BR §6.1.5 asks for a multiple of 8).
        fixture!("rsa2052-sha256.der"),
    ] {
        assert!(self_link(der)?);
        assert!(!self_link(&flip_tbs(der)?)?);
    }
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "full P-256 verifications are slow under Miri")]
fn ecdsa_p256_links_verify() -> TestResult {
    for der in [fixture!("p256-sha256.der"), fixture!("p256-sha384.der")] {
        assert!(self_link(der)?);
        assert!(!self_link(&flip_tbs(der)?)?);
    }
    Ok(())
}

// One link of each accepted key type, so the libcrux code a certificate
// link reaches (SHA-2 for RSA, which clazel-pkcs1 then checks, and the
// P-256 ECDSA verifier) can be interpreted by Miri. Under Miri only the
// valid signature is checked: the tampered check costs a second full
// verification, and runs natively. The P-256 link runs under Miri (about
// 214 s of Miri time, 80 s of wall time); the RSA-2048 link took 2,320 s of
// Miri time (18 minutes of wall time), too long for one test, and is
// ignored there. Miri still interprets libcrux's SHA-256, directly and
// through HMAC and HKDF, in `known_answers.rs`. The tests around
// them cover the other hashes and shapes natively and are ignored under
// Miri for time.

#[test]
#[cfg_attr(
    miri,
    ignore = "one RSA-2048 verification takes about 2,300 s of Miri time"
)]
fn one_rsa_2048_link_verifies_also_under_miri() -> TestResult {
    let der = fixture!("rsa2048-sha256.der");
    assert!(self_link(der)?);
    if !cfg!(miri) {
        assert!(!self_link(&flip_tbs(der)?)?);
    }
    Ok(())
}

#[test]
fn one_p256_link_verifies_also_under_miri() -> TestResult {
    let der = fixture!("p256-sha256.der");
    assert!(self_link(der)?);
    if !cfg!(miri) {
        assert!(!self_link(&flip_tbs(der)?)?);
    }
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "full RSA and P-256 verifications are slow under Miri")]
fn links_across_key_types_verify_under_the_issuer_key() -> TestResult {
    let rsa_root = cert(fixture!("rsa2048-sha256.der"))?;
    let p256_root = cert(fixture!("p256-sha256.der"))?;
    // A P-256 key, signed sha384WithRSAEncryption by the RSA root.
    let child_of_rsa = cert(fixture!("child-of-rsa2048-sha384.der"))?;
    // An RSA key, signed ecdsa-with-SHA384 by the P-256 root.
    let child_of_p256 = cert(fixture!("child-of-p256-sha384.der"))?;
    assert!(link_of(&rsa_root, &child_of_rsa));
    assert!(link_of(&p256_root, &child_of_p256));
    // Under the wrong issuer, or under its own key, neither verifies.
    assert!(!link_of(&p256_root, &child_of_rsa));
    assert!(!link_of(&rsa_root, &child_of_p256));
    assert!(!link_of(&child_of_rsa, &child_of_rsa));
    assert!(!link_of(&child_of_p256, &child_of_p256));
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "full RSA verifications are slow under Miri")]
fn rsa_parameters_null_or_absent_are_one_algorithm() -> TestResult {
    // RFC 4055 §5: NULL, and absent, sha256WithRSAEncryption parameters.
    let c = cert(fixture!("rsa2048-sha256.der"))?;
    let key = c.tbs.subject_public_key_info_der;
    let (tbs, sig) = (c.envelope.tbs_certificate_der, c.envelope.signature_bits);
    let arcs = [1, 2, 840, 113_549, 1, 1, 11];
    let mut with_null = oid(&arcs);
    with_null.parameters_der = Some(NULL);
    assert!(link(key, &with_null, tbs, sig));
    assert!(link(key, &oid(&arcs), tbs, sig));
    // Any other parameters are malformed.
    let mut with_int = oid(&arcs);
    with_int.parameters_der = Some(&[0x02, 0x01, 0x00]);
    assert!(!link(key, &with_int, tbs, sig));
    Ok(())
}

// ---------------------------------------------------------------------------
// Refusals (each signature is valid)
// ---------------------------------------------------------------------------

#[test]
fn refused_algorithms() -> TestResult {
    // sha1WithRSAEncryption, RSASSA-PSS, ecdsa-with-SHA512: Unsupported.
    assert!(!self_link(fixture!("rsa2048-sha1.der"))?);
    assert!(!self_link(fixture!("rsa2048-pss.der"))?);
    assert!(!self_link(fixture!("p256-sha512.der"))?);
    // Ed25519 and Ed448 (RFC 8410 §3), MD5 with RSA, DSA with SHA-256.
    let c = cert(fixture!("rsa2048-sha256.der"))?;
    let (key, tbs, sig) = (
        c.tbs.subject_public_key_info_der,
        c.envelope.tbs_certificate_der,
        c.envelope.signature_bits,
    );
    for arcs in [
        &[1, 3, 101, 112][..],
        &[1, 3, 101, 113][..],
        &[1, 2, 840, 113_549, 1, 1, 4][..],
        &[2, 16, 840, 1, 101, 3, 4, 3, 2][..],
    ] {
        assert!(!link(key, &oid(arcs), tbs, sig));
    }
    Ok(())
}

#[test]
fn refused_ecdsa_with_parameters() -> TestResult {
    // RFC 5758 §3.2: the parameters MUST be omitted; NULL is refused.
    let c = cert(fixture!("p256-sha256.der"))?;
    let mut alg = oid(&[1, 2, 840, 10_045, 4, 3, 2]);
    alg.parameters_der = Some(NULL);
    assert!(!link(
        c.tbs.subject_public_key_info_der,
        &alg,
        c.envelope.tbs_certificate_der,
        c.envelope.signature_bits
    ));
    Ok(())
}

#[test]
fn refused_p384_issuer_key_until_p17() -> TestResult {
    let c = cert(fixture!("p384-sha384.der"))?;
    let spki = parse_subject_public_key_info(c.tbs.subject_public_key_info_der).ok_or("spki")?;
    assert!(matches!(spki.public_key, PublicKey::EcP384(_)));
    assert!(!link_of(&c, &c));
    // Under either hash.
    let alg = oid(&[1, 2, 840, 10_045, 4, 3, 2]);
    assert!(!link(
        c.tbs.subject_public_key_info_der,
        &alg,
        c.envelope.tbs_certificate_der,
        c.envelope.signature_bits
    ));
    Ok(())
}

#[test]
fn refused_rsa_keys() -> TestResult {
    // 1024 bits: below Firefox's MIN_RSA_BITS (and clazel-pkcs1's domain).
    assert!(!self_link(fixture!("rsa1024-sha256.der"))?);
    // e = 2^33 + 1: odd, but above BoringSSL's 33 bits.
    assert!(!self_link(fixture!("rsae2p33p1-sha256.der"))?);
    Ok(())
}

#[test]
fn refused_key_and_algorithm_mismatch() -> TestResult {
    let rsa = cert(fixture!("rsa2048-sha256.der"))?;
    let p256 = cert(fixture!("p256-sha256.der"))?;
    // An RSA signature under an EC key, an ECDSA signature under an RSA key.
    assert!(!link_of(&p256, &rsa));
    assert!(!link_of(&rsa, &p256));
    Ok(())
}

#[test]
fn refused_compressed_point() -> TestResult {
    // The P-256 root's own key, compressed (0x02/0x03 || X): the signature
    // is valid, the key form is refused (mozilla::pkix).
    let c = cert(fixture!("p256-sha256.der"))?;
    let compressed = fixture!("p256-compressed.spki.der");
    let spki = parse_subject_public_key_info(compressed).ok_or("spki")?;
    assert!(matches!(spki.public_key, PublicKey::Unsupported));
    assert!(!link(
        compressed,
        &c.tbs.signature,
        c.envelope.tbs_certificate_der,
        c.envelope.signature_bits
    ));
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "a full P-256 verification is slow under Miri")]
fn refused_malformed_inputs() -> TestResult {
    let c = cert(fixture!("p256-sha256.der"))?;
    let (key, alg, tbs, sig) = (
        c.tbs.subject_public_key_info_der,
        &c.tbs.signature,
        c.envelope.tbs_certificate_der,
        c.envelope.signature_bits,
    );
    assert!(link(key, alg, tbs, sig));
    // A key that does not parse, a truncated or extended signature.
    assert!(!link(&[], alg, tbs, sig));
    assert!(!link(key.get(1..).ok_or("key")?, alg, tbs, sig));
    assert!(!link(
        key,
        alg,
        tbs,
        sig.get(..sig.len().saturating_sub(1)).ok_or("sig")?
    ));
    assert!(!link(key, alg, tbs, &[sig, &[0][..]].concat()));
    Ok(())
}

// ---------------------------------------------------------------------------
// Mozilla's roots, self-signed
// ---------------------------------------------------------------------------

#[test]
#[cfg_attr(miri, ignore = "118 full verifications are slow under Miri")]
fn every_mozilla_root_self_signature() -> TestResult {
    // (accepted, refused P-384 key, refused other)
    let (mut ok, mut p384, mut other) = (Vec::new(), Vec::new(), Vec::new());
    for root in &clazel_x509::roots::ROOTS {
        let c = cert(root.der).map_err(|e| format!("{}: {e}", root.label))?;
        let spki = parse_subject_public_key_info(c.tbs.subject_public_key_info_der)
            .ok_or_else(|| format!("{}: spki", root.label))?;
        if link_of(&c, &c) {
            ok.push(root.label);
        } else if matches!(spki.public_key, PublicKey::EcP384(_)) {
            p384.push(root.label);
        } else {
            other.push(root.label);
        }
    }
    println!(
        "Mozilla roots: {} self-signatures verify, {} refused (P-384 key), {} refused otherwise: {other:?}",
        ok.len(),
        p384.len(),
        other.len()
    );
    // Every root signed with SHA-2 under an RSA or P-256 key verifies; the
    // P-384 roots are refused until P17. The rest, refused (R) as their
    // algorithm is (a root's own signature is never checked in a path, but
    // chains through the P-521 root's key are refused):
    assert_eq!((ok.len(), p384.len()), (79, 35));
    assert_eq!(
        other,
        [
            // sha1WithRSAEncryption self-signatures.
            "Certum Trusted Network CA",
            "TWCA Root Certification Authority",
            "ACCVRAIZ1",
            // A P-521 key, ecdsa-with-SHA512.
            "e-Szigno TLS Root CA 2023",
        ]
    );
    Ok(())
}
