//! Abstract cryptographic interface for RFC 8446 §7.1 and §4.4.4.
//! No implementation or axiom is introduced here. A provider must prove
//! these contracts; joining libcrux is phase-3.md item 3.5f.
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
/// SHA-256, HKDF-SHA256 and HMAC-SHA256 as parameters to the schedule.
pub trait Crypto {
    /// The functions used by the specification.
    spec fn functions(&self) -> super::spec::Crypto;

    /// RFC 8446 §4.4.1 Transcript-Hash (SHA-256).
    fn hash(&self, messages: &[u8]) -> (out: Vec<u8>)
        ensures out@ == (self.functions().hash)(messages@), out.len() == 32;

    /// RFC 5869 §2.2 HKDF-Extract, Salt first, IKM second.
    fn extract(&self, salt: &[u8], ikm: &[u8]) -> (out: Vec<u8>)
        ensures out@ == (self.functions().extract)(salt@, ikm@), out.len() == 32;

    /// RFC 5869 §2.3 HKDF-Expand, at most 255 * Hash.length octets.
    fn expand(&self, secret: &[u8], info: &[u8], length: u16) -> (out: Vec<u8>)
        requires secret.len() == 32, length <= 8160,
        ensures out@ == (self.functions().expand)(secret@, info@, length as nat),
            out.len() == length;

    /// RFC 8446 §4.4.4 HMAC(finished_key, transcript_hash).
    fn hmac(&self, key: &[u8], message: &[u8]) -> (out: Vec<u8>)
        requires key.len() == 32,
        ensures out@ == (self.functions().hmac)(key@, message@), out.len() == 32;
}
} // verus!
