//! X25519 provider interface; no production implementation is supplied here.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// RFC 8446 §4.2.8.2/§7.4.2: key-pair derivation and agreement on explicit inputs.
pub trait KeyExchange {
    /// Pure functions implemented by this provider.
    spec fn functions(&self) -> super::join_spec::KeyExchange;
    /// Derive the public input corresponding to this exact 32-byte scalar.
    fn public_key(&self, private_key: &[u8]) -> (out: Vec<u8>)
        requires private_key.len() == 32,
        ensures out.len() == 32, out@ == (self.functions().public_key)(private_key@);
    /// Derive a shared secret or reject the peer input. The controller separately
    /// performs RFC 8446 §7.4.2's required all-zero shared-secret check.
    fn shared_secret(&self, private_key: &[u8], peer_key: &[u8]) -> (out: Option<Vec<u8>>)
        requires private_key.len() == 32, peer_key.len() == 32,
        ensures match out {
            None => (self.functions().shared_secret)(private_key@, peer_key@) is None,
            Some(shared) => shared.len() == 32 && (self.functions().shared_secret)(private_key@, peer_key@) == Some(shared@),
        };
}
} // verus!
