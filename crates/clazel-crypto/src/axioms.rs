//! The trust boundary: every call into libcrux, each one axiom.
//!
//! Each wrapper is `external_body`. Verus takes its `ensures` on trust, and
//! the body is a direct call to one libcrux function with no logic beyond
//! length conversion. The `ensures` states only what libcrux documents: the
//! output is the uninterpreted function of [`crate::spec`] applied to these
//! exact inputs, with the documented output length. That libcrux computes
//! the standard's function is HACL*'s proof, recorded in the TCB
//! (docs/VERIFICATION.md), and is never assumed here.
//!
//! The libcrux functions refuse inputs longer than `u32::MAX` octets, and
//! some panic close to that bound: `libcrux-hkdf`'s expand computes its
//! buffer length with a wrapping `u32` sum, so an `info` within 33 octets of
//! `u32::MAX` makes it slice out of range. HACL*'s preconditions also stop
//! short of `u32::MAX` (for HMAC, data plus the 64-octet block). Every
//! wrapper therefore checks each variable-length input against
//! [`MAX_INPUT`] first and calls [`std::process::abort`] instead, so it
//! never returns a value no axiom covers and never unwinds. Callers in this
//! browser never come near that size: a TLS record is at most 2^14 + 256
//! octets, and handshake messages are bounded by the reassembler.
//!
//! These axioms are counted in the README table. A session other than the
//! one that wrote them reviews every change to this file
//! (docs/phases/phase-3.md 3.5f).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The longest input any wrapper passes to libcrux: 2^32 - 256 octets,
/// below every HACL* precondition (the tightest is HKDF-Expand's inner
/// HMAC over 32 + info + 1 octets plus its 64-octet block).
pub const MAX_INPUT: usize = 0xffff_ff00;

/// SHA-256 of `message`.
// AXIOM: libcrux-sha2 0.0.9 `sha256(&[u8]) -> [u8; 32]` returns SHA-256 of
// its input (verified-hacl); it panics above u32::MAX, so we abort above MAX_INPUT.
#[verifier::external_body]
pub fn sha256(message: &[u8]) -> (out: Vec<u8>)
    ensures out@ == crate::spec::sha256(message@), out.len() == 32,
{
    if message.len() > MAX_INPUT {
        std::process::abort();
    }
    libcrux_sha2::sha256(message).to_vec()
}

/// HMAC-SHA256(key, message).
// AXIOM: libcrux-hmac 0.0.9 `hmac_sha2_256(&mut [u8; 32], key, data)` writes
// HMAC-SHA256(key, data) (verified-hacl); we abort above MAX_INPUT first.
#[verifier::external_body]
pub fn hmac_sha256(key: &[u8], message: &[u8]) -> (out: Vec<u8>)
    ensures out@ == crate::spec::hmac_sha256(key@, message@), out.len() == 32,
{
    if key.len() > MAX_INPUT || message.len() > MAX_INPUT {
        std::process::abort();
    }
    let mut tag = [0u8; 32];
    libcrux_hmac::hmac_sha2_256(&mut tag, key, message);
    tag.to_vec()
}

/// HKDF-Extract(salt, IKM) with SHA-256.
// AXIOM: libcrux-hkdf 0.0.9 `sha2_256::extract(prk, salt, ikm)` writes the
// 32-octet HKDF-Extract PRK; errs only above u32::MAX; we abort above MAX_INPUT.
#[verifier::external_body]
pub fn hkdf_extract(salt: &[u8], ikm: &[u8]) -> (out: Vec<u8>)
    ensures out@ == crate::spec::hkdf_extract(salt@, ikm@), out.len() == 32,
{
    if salt.len() > MAX_INPUT || ikm.len() > MAX_INPUT {
        std::process::abort();
    }
    let mut prk = [0u8; 32];
    match libcrux_hkdf::sha2_256::extract(&mut prk, salt, ikm) {
        Ok(()) => prk.to_vec(),
        Err(_) => std::process::abort(),
    }
}

/// HKDF-Expand(PRK, info, length) with SHA-256.
// AXIOM: libcrux-hkdf 0.0.9 `sha2_256::expand(okm, prk, info)` fills okm with
// HKDF-Expand(prk[..32], info, okm.len()); panics near u32::MAX info: abort above MAX_INPUT.
#[verifier::external_body]
pub fn hkdf_expand(prk: &[u8], info: &[u8], length: u16) -> (out: Vec<u8>)
    requires prk.len() == 32, length <= 8160,
    ensures out@ == crate::spec::hkdf_expand(prk@, info@, length as nat), out.len() == length,
{
    // libcrux uses only prk's first 32 octets; `requires` makes that all of it.
    if info.len() > MAX_INPUT {
        std::process::abort();
    }
    let mut okm = vec![0u8; usize::from(length)];
    match libcrux_hkdf::sha2_256::expand(&mut okm, prk, info) {
        Ok(()) => okm,
        Err(_) => std::process::abort(),
    }
}

/// ChaCha20-Poly1305 encryption: ciphertext then the 16-octet tag.
// AXIOM: libcrux-chacha20poly1305 0.0.10 `encrypt(key, ptxt, ctxt, aad, nonce)`
// writes ciphertext then 16-octet tag into ctxt; errs only above u32::MAX (we: MAX_INPUT).
#[verifier::external_body]
pub fn chacha20poly1305_seal(key: &[u8], nonce: &[u8], ad: &[u8], plaintext: &[u8])
    -> (out: Vec<u8>)
    requires key.len() == 32, nonce.len() == 12,
    ensures out@ == crate::spec::chacha20poly1305_seal(key@, nonce@, ad@, plaintext@),
{
    let (Ok(key), Ok(nonce)) = (<&[u8; 32]>::try_from(key), <&[u8; 12]>::try_from(nonce)) else {
        std::process::abort();
    };
    if ad.len() > MAX_INPUT || plaintext.len() > MAX_INPUT {
        std::process::abort();
    }
    let Some(length) = plaintext.len().checked_add(libcrux_chacha20poly1305::TAG_LEN) else {
        std::process::abort();
    };
    let mut out = vec![0u8; length];
    match libcrux_chacha20poly1305::encrypt(key, plaintext, &mut out, ad, nonce) {
        Ok(_) => out,
        Err(_) => std::process::abort(),
    }
}

/// ChaCha20-Poly1305 decryption, or none when the tag does not verify.
// AXIOM: libcrux-chacha20poly1305 0.0.10 `decrypt(key, ptxt, ctxt, aad, nonce)`
// returns the plaintext iff the tag verifies, else Err (also for ctxt < 16 octets).
#[verifier::external_body]
pub fn chacha20poly1305_open(key: &[u8], nonce: &[u8], ad: &[u8], ciphertext: &[u8])
    -> (out: Option<Vec<u8>>)
    requires key.len() == 32, nonce.len() == 12,
    ensures match out {
        Some(p) => crate::spec::chacha20poly1305_open(key@, nonce@, ad@, ciphertext@) == Some(p@),
        None => crate::spec::chacha20poly1305_open(key@, nonce@, ad@, ciphertext@) is None,
    },
{
    let (Ok(key), Ok(nonce)) = (<&[u8; 32]>::try_from(key), <&[u8; 12]>::try_from(nonce)) else {
        std::process::abort();
    };
    if ad.len() > MAX_INPUT || ciphertext.len() > MAX_INPUT {
        std::process::abort();
    }
    let mut plaintext = vec![0u8; ciphertext.len().saturating_sub(libcrux_chacha20poly1305::TAG_LEN)];
    match libcrux_chacha20poly1305::decrypt(key, &mut plaintext, ciphertext, ad, nonce) {
        Ok(_) => Some(plaintext),
        Err(_) => None,
    }
}

/// The sealed output is exactly 16 octets longer than the plaintext.
// AXIOM: libcrux-chacha20poly1305 0.0.10 appends exactly TAG_LEN = 16 octets
// (RFC 8439 §2.8); `encrypt`'s output split is (ptxt.len(), 16).
#[verifier::external_body]
pub proof fn axiom_chacha20poly1305_seal_len(key: Seq<u8>, nonce: Seq<u8>, ad: Seq<u8>,
    plaintext: Seq<u8>)
    ensures crate::spec::chacha20poly1305_seal(key, nonce, ad, plaintext).len() == plaintext.len() + 16,
{
}

/// X25519(private_key, 9).
// AXIOM: libcrux-curve25519 0.0.9 `secret_to_public(pk, sk)` writes
// X25519(sk, 9) (verified-hacl); both are 32-octet arrays.
#[verifier::external_body]
pub fn x25519_public(private_key: &[u8]) -> (out: Vec<u8>)
    requires private_key.len() == 32,
    ensures out@ == crate::spec::x25519_public(private_key@), out.len() == 32,
{
    let Ok(private_key) = <&[u8; 32]>::try_from(private_key) else {
        std::process::abort();
    };
    let mut public = [0u8; 32];
    libcrux_curve25519::secret_to_public(&mut public, private_key);
    public.to_vec()
}

/// X25519(private_key, peer_key), or none for an all-zero result.
// AXIOM: libcrux-curve25519 0.0.9 `ecdh(out, pk, sk)` writes X25519(sk, pk)
// and returns Err exactly when HACL reports failure (an all-zero result).
#[verifier::external_body]
pub fn x25519_shared(private_key: &[u8], peer_key: &[u8]) -> (out: Option<Vec<u8>>)
    requires private_key.len() == 32, peer_key.len() == 32,
    ensures match out {
        Some(s) => s.len() == 32 && crate::spec::x25519_shared(private_key@, peer_key@) == Some(s@),
        None => crate::spec::x25519_shared(private_key@, peer_key@) is None,
    },
{
    let (Ok(private_key), Ok(peer_key)) =
        (<&[u8; 32]>::try_from(private_key), <&[u8; 32]>::try_from(peer_key)) else {
        std::process::abort();
    };
    let mut shared = [0u8; 32];
    match libcrux_curve25519::ecdh(&mut shared, peer_key, private_key) {
        Ok(()) => Some(shared.to_vec()),
        Err(_) => None,
    }
}

/// ECDSA P-256/SHA-256 verification of `message` with raw r, s and X || Y.
// AXIOM: libcrux-ecdsa 0.0.9 `p256::verify(Sha256, payload, &Signature::from_raw(r, s),
// &PublicKey(x||y))` is Ok iff HACL's ecdsa_verif_p256_sha2 is true (valid point, 1<=r,s<n, sig ok).
#[verifier::external_body]
pub fn ecdsa_p256_sha256_verify(message: &[u8], r: &[u8], s: &[u8], point: &[u8]) -> (out: bool)
    requires r.len() == 32, s.len() == 32, point.len() == 64,
    ensures out == crate::signature::spec::ecdsa_p256_sha256_verify(message@, r@, s@, point@),
{
    if message.len() > MAX_INPUT {
        std::process::abort();
    }
    let (Ok(r), Ok(s), Ok(point)) =
        (<[u8; 32]>::try_from(r), <[u8; 32]>::try_from(s), <[u8; 64]>::try_from(point)) else {
        std::process::abort();
    };
    let signature = libcrux_ecdsa::p256::Signature::from_raw(r, s);
    let public_key = libcrux_ecdsa::p256::PublicKey(point);
    libcrux_ecdsa::p256::verify(libcrux_ecdsa::DigestAlgorithm::Sha256, message, &signature,
        &public_key).is_ok()
}

/// RSASSA-PSS verification with e = 65537, MGF1 over `hash`, and `salt_len`.
// AXIOM: libcrux-rsa 0.0.9 `verify(alg, &VarLenPublicKey(n), msg, salt_len, sig)` (e fixed to 65537)
// is Ok iff HACL's rsapss_pkey_verify is true; its other errors are excluded by `requires`.
#[verifier::external_body]
pub fn rsa_pss_verify(hash: crate::signature::spec::Hash, modulus: &[u8], message: &[u8],
    salt_len: u32, signature: &[u8]) -> (out: bool)
    requires
        crate::signature::spec::modulus_ok(modulus@),
        signature.len() == modulus.len(),
        salt_len == crate::signature::spec::hash_len(hash),
    ensures out == crate::signature::spec::rsa_pss_verify(hash, modulus@, message@,
        salt_len as nat, signature@),
{
    if message.len() > MAX_INPUT {
        std::process::abort();
    }
    let alg = match hash {
        crate::signature::spec::Hash::Sha256 => libcrux_rsa::DigestAlgorithm::Sha2_256,
        crate::signature::spec::Hash::Sha384 => libcrux_rsa::DigestAlgorithm::Sha2_384,
        crate::signature::spec::Hash::Sha512 => libcrux_rsa::DigestAlgorithm::Sha2_512,
    };
    let Ok(key) = libcrux_rsa::VarLenPublicKey::try_from(modulus) else {
        std::process::abort();
    };
    match libcrux_rsa::verify(alg, &key, message, salt_len, signature) {
        Ok(()) => true,
        Err(libcrux_rsa::Error::VerificationFailed) => false,
        Err(_) => std::process::abort(),
    }
}

/// Ed25519 verification of `message` under a 32-octet key.
// AXIOM: libcrux-ed25519 0.0.10 `verify(payload, &[u8; 32], &[u8; 64])` is Ok iff HACL's
// ed25519 verify is true (verified-hacl); it errs otherwise only above u32::MAX octets.
#[verifier::external_body]
pub fn ed25519_verify(message: &[u8], key: &[u8], signature: &[u8]) -> (out: bool)
    requires key.len() == 32, signature.len() == 64,
    ensures out == crate::signature::spec::ed25519_verify(message@, key@, signature@),
{
    if message.len() > MAX_INPUT {
        std::process::abort();
    }
    let (Ok(key), Ok(signature)) =
        (<&[u8; 32]>::try_from(key), <&[u8; 64]>::try_from(signature)) else {
        std::process::abort();
    };
    libcrux_ed25519::verify(message, key, signature).is_ok()
}

} // verus!
