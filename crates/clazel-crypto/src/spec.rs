//! The functions libcrux computes, as uninterpreted specification functions.
//!
//! Each is named for the algorithm and the standard it implements, and has
//! no body: what a call returns is fixed only by the axiom in
//! [`crate::axioms`] that wraps the libcrux function, which states the
//! documented input and output types and nothing else (phase-3.md 3.5f).
//! That the libcrux code computes the standard's function is HACL*'s proof
//! and is in the TCB (docs/VERIFICATION.md); it is not restated here.
//!
//! - SHA-256: FIPS 180-4 §6.2, <https://doi.org/10.6028/NIST.FIPS.180-4>.
//! - SHA-384 and SHA-512: FIPS 180-4 §6.5 and §6.4 (certificate links,
//!   `chain`).
//! - HMAC-SHA256: RFC 2104 §2, <https://www.rfc-editor.org/rfc/rfc2104#section-2>.
//! - HKDF-SHA256: RFC 5869 §2.2 (Extract) and §2.3 (Expand),
//!   <https://www.rfc-editor.org/rfc/rfc5869#section-2>.
//! - ChaCha20-Poly1305: RFC 8439 §2.8,
//!   <https://www.rfc-editor.org/rfc/rfc8439#section-2.8>.
//! - X25519: RFC 7748 §5 and §6.1,
//!   <https://www.rfc-editor.org/rfc/rfc7748#section-5>.
//!
//! Modelling choices:
//! - Each function is total over byte sequences. Inputs longer than
//!   [`crate::axioms::MAX_INPUT`] (2^32 - 256) octets, which includes
//!   everything libcrux refuses or panics on, are never returned from: the
//!   wrapper aborts the process instead, so no axiom states a value there.
//! - X25519 returns no shared secret when libcrux reports failure, which it
//!   does for an all-zero result (RFC 7748 §6.1, RFC 8446 §7.4.2).
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// SHA-256 of `message` (FIPS 180-4 §6.2).
pub uninterp spec fn sha256(message: Seq<u8>) -> Seq<u8>;

/// SHA-384 of `message` (FIPS 180-4 §6.5).
pub uninterp spec fn sha384(message: Seq<u8>) -> Seq<u8>;

/// SHA-512 of `message` (FIPS 180-4 §6.4).
pub uninterp spec fn sha512(message: Seq<u8>) -> Seq<u8>;

/// HMAC-SHA256(key, message) (RFC 2104 §2 with SHA-256, B = 64, L = 32).
pub uninterp spec fn hmac_sha256(key: Seq<u8>, message: Seq<u8>) -> Seq<u8>;

/// HKDF-Extract(salt, IKM) with SHA-256 (RFC 5869 §2.2).
pub uninterp spec fn hkdf_extract(salt: Seq<u8>, ikm: Seq<u8>) -> Seq<u8>;

/// HKDF-Expand(PRK, info, L) with SHA-256 (RFC 5869 §2.3).
pub uninterp spec fn hkdf_expand(prk: Seq<u8>, info: Seq<u8>, length: nat) -> Seq<u8>;

/// AEAD_CHACHA20_POLY1305 encryption: ciphertext followed by the 16-octet
/// tag (RFC 8439 §2.8).
pub uninterp spec fn chacha20poly1305_seal(key: Seq<u8>, nonce: Seq<u8>, ad: Seq<u8>,
    plaintext: Seq<u8>) -> Seq<u8>;

/// AEAD_CHACHA20_POLY1305 decryption: the plaintext, or none when the tag
/// does not verify (RFC 8439 §2.8).
pub uninterp spec fn chacha20poly1305_open(key: Seq<u8>, nonce: Seq<u8>, ad: Seq<u8>,
    ciphertext: Seq<u8>) -> Option<Seq<u8>>;

/// X25519(k, 9): the public key of private scalar `k` (RFC 7748 §6.1).
pub uninterp spec fn x25519_public(private_key: Seq<u8>) -> Seq<u8>;

/// X25519(k, u): the shared secret, or none when libcrux refuses it (an
/// all-zero result, RFC 7748 §6.1).
pub uninterp spec fn x25519_shared(private_key: Seq<u8>, peer_key: Seq<u8>) -> Option<Seq<u8>>;

} // verus!
