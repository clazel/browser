//! Known-answer tests for every provider, from the standards' own vectors:
//! FIPS 180-2 Appendix B.1 (SHA-256 "abc"), RFC 4231 §4.2 and §4.3
//! (HMAC-SHA256), RFC 5869 A.1 and A.3 (HKDF-SHA256), RFC 8439 §2.8.2
//! (ChaCha20-Poly1305) and RFC 7748 §6.1 (X25519). Each is called through
//! the `clazel-tls` trait it implements, as the TLS code calls it.

use clazel_crypto::provider::{ChaCha20Poly1305Factory, Sha256Suite, X25519};
use clazel_tls::hello::key_exchange::KeyExchange;
use clazel_tls::record::Aead;
use clazel_tls::schedule::crypto::Crypto;
use clazel_tls::traffic::provider::Factory;

type TestResult = Result<(), String>;

fn hex(text: &str) -> Result<Vec<u8>, String> {
    let digits: Vec<u8> = text
        .bytes()
        .filter(|b| !b.is_ascii_whitespace() && *b != b':')
        .collect();
    digits
        .chunks(2)
        .map(|pair| {
            let pair = std::str::from_utf8(pair).map_err(|e| e.to_string())?;
            u8::from_str_radix(pair, 16).map_err(|e| format!("{pair}: {e}"))
        })
        .collect()
}

#[test]
fn sha256_fips_180_2_abc() -> TestResult {
    let expected = hex("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")?;
    assert_eq!(Sha256Suite.hash(b"abc"), expected);
    Ok(())
}

#[test]
fn hmac_sha256_rfc_4231() -> TestResult {
    // §4.2 Test Case 1.
    let key = hex("0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b")?;
    let tag = hex("b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7")?;
    assert_eq!(Sha256Suite.hmac(&key, b"Hi There"), tag);
    // §4.3 Test Case 2: a key shorter than the output.
    let tag = hex("5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843")?;
    assert_eq!(
        Sha256Suite.hmac(b"Jefe", b"what do ya want for nothing?"),
        tag
    );
    Ok(())
}

#[test]
fn hkdf_sha256_rfc_5869_a1() -> TestResult {
    let ikm = hex("0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b")?;
    let salt = hex("000102030405060708090a0b0c")?;
    let info = hex("f0f1f2f3f4f5f6f7f8f9")?;
    let prk = hex("077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5")?;
    let okm = hex(
        "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865",
    )?;
    assert_eq!(Sha256Suite.extract(&salt, &ikm), prk);
    assert_eq!(Sha256Suite.expand(&prk, &info, 42), okm);
    // HKDF-Expand's T(1) is a prefix of every longer output (RFC 5869 §2.3),
    // so the 12-octet IV length TLS uses is a prefix of the vector.
    assert_eq!(
        Sha256Suite.expand(&prk, &info, 12),
        okm.get(..12).ok_or("short okm")?
    );
    Ok(())
}

#[test]
fn hkdf_sha256_rfc_5869_a3_empty_salt_and_info() -> TestResult {
    let ikm = hex("0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b")?;
    let prk = hex("19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04")?;
    let okm = hex(
        "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8",
    )?;
    assert_eq!(Sha256Suite.extract(&[], &ikm), prk);
    assert_eq!(Sha256Suite.expand(&prk, &[], 42), okm);
    Ok(())
}

const RFC_8439_PLAINTEXT: &[u8] = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";

/// RFC 8439 §2.8.2's key, nonce, additional data and sealed output.
struct Vector {
    key: Vec<u8>,
    nonce: Vec<u8>,
    aad: Vec<u8>,
    sealed: Vec<u8>,
}

fn rfc_8439_vector() -> Result<Vector, String> {
    let key = hex("808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f")?;
    // §2.8.2: the 32-bit fixed-common part followed by the 8-octet IV.
    let nonce = hex("07000000 4041424344454647")?;
    let aad = hex("50515253c0c1c2c3c4c5c6c7")?;
    let sealed = hex(
        "d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d6
         3dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b36
         92ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc
         3ff4def08e4b7a9de576d26586cec64b6116
         1ae10b594f09e26a7e902ecbd0600691",
    )?;
    Ok(Vector {
        key,
        nonce,
        aad,
        sealed,
    })
}

#[test]
fn chacha20poly1305_rfc_8439_seal_and_open() -> TestResult {
    let Vector {
        key,
        nonce,
        aad,
        sealed,
    } = rfc_8439_vector()?;
    let cipher = ChaCha20Poly1305Factory.make(&key);
    assert_eq!((cipher.tag_len(), cipher.nonce_len()), (16, 12));
    assert_eq!(cipher.seal(&nonce, &aad, RFC_8439_PLAINTEXT), sealed);
    assert_eq!(
        cipher.open(&nonce, &aad, &sealed).as_deref(),
        Some(RFC_8439_PLAINTEXT)
    );
    Ok(())
}

#[test]
fn chacha20poly1305_refuses_tampering() -> TestResult {
    let Vector {
        key,
        nonce,
        aad,
        sealed,
    } = rfc_8439_vector()?;
    let cipher = ChaCha20Poly1305Factory.make(&key);
    // A flipped bit in the ciphertext, in the tag, or in the additional data.
    for position in [0, sealed.len().saturating_sub(1)] {
        let mut tampered = sealed.clone();
        let byte = tampered.get_mut(position).ok_or("position")?;
        *byte ^= 1;
        assert_eq!(cipher.open(&nonce, &aad, &tampered), None);
    }
    let mut other_aad = aad.clone();
    other_aad.push(0);
    assert_eq!(cipher.open(&nonce, &other_aad, &sealed), None);
    // Shorter than a tag.
    assert_eq!(
        cipher.open(&nonce, &aad, sealed.get(..15).ok_or("short")?),
        None
    );
    Ok(())
}

#[test]
fn x25519_rfc_7748_6_1() -> TestResult {
    let alice = hex("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a")?;
    let alice_public = hex("8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a")?;
    let bob = hex("5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb")?;
    let bob_public = hex("de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f")?;
    let shared = hex("4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742")?;
    assert_eq!(X25519.public_key(&alice), alice_public);
    assert_eq!(X25519.public_key(&bob), bob_public);
    assert_eq!(
        X25519.shared_secret(&alice, &bob_public),
        Some(shared.clone())
    );
    assert_eq!(X25519.shared_secret(&bob, &alice_public), Some(shared));
    Ok(())
}

#[test]
fn x25519_refuses_an_all_zero_shared_secret() -> TestResult {
    // u = 0 is a small-order point: every scalar maps it to zero (RFC 7748
    // §6.1), which RFC 8446 §7.4.2 requires the client to refuse.
    let alice = hex("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a")?;
    assert_eq!(X25519.shared_secret(&alice, &[0u8; 32]), None);
    Ok(())
}
