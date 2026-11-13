//! The abstract parameters of the transcription, and the numbers of the one
//! cipher suite it models, `TLS_CHACHA20_POLY1305_SHA256` (RFC 8446 Appendix
//! B.4, {0x13,0x03}).
//!
//! Modelling choices:
//! - Every cryptographic operation is a field of [`Primitives`], an
//!   uninterpreted `spec_fn`. Nothing is assumed of them: no output length, no
//!   collision resistance, no inverse. A statement about a result holds for
//!   every choice of them.
//! - Hash.length is 32 (SHA-256, [SHS]). The AEAD is AEAD_CHACHA20_POLY1305
//!   (RFC 8439), whose key is 32 bytes, whose N_MIN is 12, and whose expansion
//!   is its 16-byte tag. These four numbers are the only facts about the suite
//!   the RFC's text needs, and they are constants rather than fields because
//!   the suite is fixed. RFC 8446 itself gives none of them: they are SHA-256's
//!   and RFC 8439's.
//! - Key exchange is one function, X25519 of RFC 7748, `x25519(scalar, u)`,
//!   used for both directions as §7.4.2 describes.
//! - The certificate chain is validated by one function of the whole
//!   `certificate_list` that either gives the end-entity certificate's
//!   public key or names the alert ([`ChainResult`]), because X.509 path
//!   validation, OCSP and SCT checking are out of scope. Its rejection is
//!   §4.4.2.2's "appropriate certificate-related alert".
//! - A signature check is `verify_signature(scheme, key, content, signature)`.
//!   §4.4.3's "MUST also be compatible with the key" is a separate field,
//!   since it has its own failure; an instantiation with one combined check
//!   sets `key_compatible` to always true and loses nothing but the alert.

#[allow(unused_imports)]
use vstd::prelude::*;

use super::authentication::CertificateEntry;

verus! {

/// §4.4.2.2, §4.4.2.4: the outcome of validating a server's certificate chain.
pub enum ChainResult {
    /// The chain is acceptable; this is the end-entity certificate's key.
    Accepted(Seq<u8>),
    /// The chain is not; this is the AlertDescription code to send.
    Rejected(nat),
}

/// §5.2's AEAD-Encrypt, as a type: (key, nonce, additional_data, plaintext).
pub type AeadEncrypt = spec_fn(Seq<u8>, Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>;

/// §5.2's AEAD-Decrypt, as a type: (key, nonce, additional_data, AEADEncrypted).
pub type AeadDecrypt = spec_fn(Seq<u8>, Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>;

/// §4.4.3's verification, as a type: (scheme, public key, content, signature).
pub type VerifySignature = spec_fn(nat, Seq<u8>, Seq<u8>, Seq<u8>) -> bool;

/// The abstract operations, each named for the RFC's use of it.
pub struct Primitives {
    /// §4.4.1, §7.1: "Hash", the cipher suite's hash function.
    pub hash: spec_fn(Seq<u8>) -> Seq<u8>,
    /// §7.1: HKDF-Extract(salt, IKM) of RFC 5869.
    pub hkdf_extract: spec_fn(Seq<u8>, Seq<u8>) -> Seq<u8>,
    /// §7.1: HKDF-Expand(PRK, info, L) of RFC 5869.
    pub hkdf_expand: spec_fn(Seq<u8>, Seq<u8>, nat) -> Seq<u8>,
    /// §4.4.4: HMAC(key, message) of RFC 2104 with the hash above.
    pub hmac: spec_fn(Seq<u8>, Seq<u8>) -> Seq<u8>,
    /// §5.2: AEAD-Encrypt(write_key, nonce, additional_data, plaintext).
    pub aead_encrypt: AeadEncrypt,
    /// §5.2: AEAD-Decrypt(peer_write_key, nonce, additional_data,
    /// AEADEncrypted): "either the plaintext or an error".
    pub aead_decrypt: AeadDecrypt,
    /// §7.4.2: the ECDH scalar multiplication function of X25519.
    pub x25519: spec_fn(Seq<u8>, Seq<u8>) -> Seq<u8>,
    /// §4.4.3: whether a signature verifies, (scheme, public key, content
    /// covered, signature).
    pub verify_signature: VerifySignature,
    /// §4.4.3: whether a signature algorithm "is compatible with the key in
    /// the sender's end-entity certificate".
    pub key_compatible: spec_fn(nat, Seq<u8>) -> bool,
    /// §4.4.2.4: certificate validation of the `certificate_list`.
    pub validate_certificate_chain: spec_fn(Seq<CertificateEntry>) -> ChainResult,
}

/// §7.1: "Hash.length is its output length in bytes", for SHA-256.
pub open spec fn hash_length() -> nat {
    32
}

/// §7.3: key_length for AEAD_CHACHA20_POLY1305 (RFC 8439 §2.8).
pub open spec fn key_length() -> nat {
    32
}

/// §5.3: "iv_length ... is set to the larger of 8 bytes and N_MIN for the AEAD
/// algorithm"; N_MIN is 12 for AEAD_CHACHA20_POLY1305.
pub open spec fn iv_length() -> nat {
    12
}

/// §5.2: "any expansion added by the AEAD algorithm"; the 16-byte Poly1305 tag.
pub open spec fn aead_expansion() -> nat {
    16
}

/// §7.1: "0" in the key schedule diagram, "a string of Hash.length bytes set to
/// zero".
pub open spec fn zero_value() -> Seq<u8> {
    seq![0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
         0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
}

/// RFC 7748 §4.1: the standard public basepoint of §7.4.2, u = 9.
pub open spec fn x25519_basepoint() -> Seq<u8> {
    seq![9u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
         0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
}

} // verus!
