//! The adapters: `clazel-tls`'s provider traits, implemented by the
//! wrappers of [`crate::axioms`]. Verus checks each method against the
//! trait's contract; nothing here is trusted.
use crate::axioms;
use clazel_tls::hello::key_exchange::KeyExchange;
use clazel_tls::record::Aead;
use clazel_tls::schedule::crypto::Crypto;
use clazel_tls::traffic::provider::{Factory, KeyedAead};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// SHA-256, HKDF-SHA256 and HMAC-SHA256 for the key schedule (RFC 8446
/// §4.4.1 and §7.1), from libcrux.
pub struct Sha256Suite;

impl Crypto for Sha256Suite {
    open spec fn functions(&self) -> clazel_tls::schedule::spec::Crypto {
        clazel_tls::schedule::spec::Crypto {
            hash: |m: Seq<u8>| crate::spec::sha256(m),
            extract: |salt: Seq<u8>, ikm: Seq<u8>| crate::spec::hkdf_extract(salt, ikm),
            expand: |prk: Seq<u8>, info: Seq<u8>, length: nat| crate::spec::hkdf_expand(prk, info, length),
            hmac: |key: Seq<u8>, message: Seq<u8>| crate::spec::hmac_sha256(key, message),
        }
    }

    fn hash(&self, messages: &[u8]) -> (out: Vec<u8>) {
        axioms::sha256(messages)
    }

    fn extract(&self, salt: &[u8], ikm: &[u8]) -> (out: Vec<u8>) {
        axioms::hkdf_extract(salt, ikm)
    }

    fn expand(&self, secret: &[u8], info: &[u8], length: u16) -> (out: Vec<u8>) {
        axioms::hkdf_expand(secret, info, length)
    }

    fn hmac(&self, key: &[u8], message: &[u8]) -> (out: Vec<u8>) {
        axioms::hmac_sha256(key, message)
    }
}

/// Makes ChaCha20-Poly1305 record ciphers (RFC 8446 §5.2 and §7.3, RFC 8439
/// §2.8), from libcrux.
pub struct ChaCha20Poly1305Factory;

/// One ChaCha20-Poly1305 key, installed once and never exported.
pub struct ChaCha20Poly1305 {
    key: Vec<u8>,
}

impl ChaCha20Poly1305 {
    /// The installed key is 32 octets.
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.key@.len() == 32
    }
}

impl Aead for ChaCha20Poly1305 {
    closed spec fn seal_spec(&self, nonce: Seq<u8>, ad: Seq<u8>, plaintext: Seq<u8>) -> Seq<u8> {
        crate::spec::chacha20poly1305_seal(self.key@, nonce, ad, plaintext)
    }

    closed spec fn open_spec(&self, nonce: Seq<u8>, ad: Seq<u8>, ciphertext: Seq<u8>) -> Option<Seq<u8>> {
        crate::spec::chacha20poly1305_open(self.key@, nonce, ad, ciphertext)
    }

    closed spec fn tag_len_spec(&self) -> nat {
        16
    }

    closed spec fn nonce_len_spec(&self) -> nat {
        12
    }

    fn tag_len(&self) -> (n: usize) {
        16
    }

    fn nonce_len(&self) -> (n: usize) {
        12
    }

    fn seal(&self, nonce: &[u8], ad: &[u8], plaintext: &[u8]) -> (ciphertext: Vec<u8>) {
        proof { use_type_invariant(self); }
        axioms::chacha20poly1305_seal(self.key.as_slice(), nonce, ad, plaintext)
    }

    fn open(&self, nonce: &[u8], ad: &[u8], ciphertext: &[u8]) -> (plaintext: Option<Vec<u8>>) {
        proof { use_type_invariant(self); }
        axioms::chacha20poly1305_open(self.key.as_slice(), nonce, ad, ciphertext)
    }

    proof fn lemma_seal_len(&self, nonce: Seq<u8>, ad: Seq<u8>, plaintext: Seq<u8>) {
        axioms::axiom_chacha20poly1305_seal_len(self.key@, nonce, ad, plaintext);
    }
}

impl KeyedAead for ChaCha20Poly1305 {
    closed spec fn key_spec(&self) -> Seq<u8> {
        self.key@
    }
}

impl Factory for ChaCha20Poly1305Factory {
    type Cipher = ChaCha20Poly1305;

    open spec fn functions(&self) -> clazel_tls::traffic::spec::Cipher {
        clazel_tls::traffic::spec::Cipher {
            seal: |key: Seq<u8>, nonce: Seq<u8>, ad: Seq<u8>, plaintext: Seq<u8>|
                crate::spec::chacha20poly1305_seal(key, nonce, ad, plaintext),
            open: |key: Seq<u8>, nonce: Seq<u8>, ad: Seq<u8>, ciphertext: Seq<u8>|
                crate::spec::chacha20poly1305_open(key, nonce, ad, ciphertext),
        }
    }

    fn make(&self, key: &[u8]) -> (out: Self::Cipher) {
        let mut installed = Vec::new();
        installed.extend_from_slice(key);
        let out = ChaCha20Poly1305 { key: installed };
        proof {
            assert(out.key@ =~= key@);
            assert(out.tag_len_spec() == 16);
            assert(out.nonce_len_spec() == 12);
            assert forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>|
                #[trigger] out.seal_spec(n, ad, p) == (self.functions().seal)(key@, n, ad, p) by {}
            assert forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>|
                #[trigger] out.open_spec(n, ad, ct) == (self.functions().open)(key@, n, ad, ct) by {}
        }
        out
    }
}

/// X25519 for the `key_share` exchange (RFC 8446 §4.2.8.2 and §7.4.2, RFC
/// 7748 §6.1), from libcrux.
pub struct X25519;

impl KeyExchange for X25519 {
    open spec fn functions(&self) -> clazel_tls::hello::join_spec::KeyExchange {
        clazel_tls::hello::join_spec::KeyExchange {
            public_key: |private_key: Seq<u8>| crate::spec::x25519_public(private_key),
            shared_secret: |private_key: Seq<u8>, peer_key: Seq<u8>|
                crate::spec::x25519_shared(private_key, peer_key),
        }
    }

    fn public_key(&self, private_key: &[u8]) -> (out: Vec<u8>) {
        axioms::x25519_public(private_key)
    }

    fn shared_secret(&self, private_key: &[u8], peer_key: &[u8]) -> (out: Option<Vec<u8>>) {
        axioms::x25519_shared(private_key, peer_key)
    }
}

} // verus!
