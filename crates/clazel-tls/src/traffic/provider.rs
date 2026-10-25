//! Bind a derived traffic key to the existing verified AEAD record interface.
use crate::record::Aead;
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Fixed-profile AEAD construction; no production provider is supplied here.
pub trait Factory {
    /// Owned cipher object, keeping its installed key immutable.
    type Cipher: Aead;
    /// Key-explicit encryption/authentication functions implemented by this factory.
    spec fn functions(&self) -> super::spec::Cipher;
    /// RFC 8446 §7.3: install exactly the derived 32-byte traffic key.
    fn make(&self, key: &[u8]) -> (out: Self::Cipher)
        requires key.len() == 32,
        ensures out.tag_len_spec() == 16, out.nonce_len_spec() == 12,
            forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] out.seal_spec(n, ad, p) == (self.functions().seal)(key@, n, ad, p),
            forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] out.open_spec(n, ad, ct) == (self.functions().open)(key@, n, ad, ct);
}
} // verus!
