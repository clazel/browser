//! The contract the executable `verify` must be proven to meet. There is no
//! executable code yet; these predicates are what its `requires` and
//! `ensures` clauses will be, so reviewing them and [`super::spec`] is
//! enough to know what the implementation will guarantee (the same shape as
//! `clazel-pkcs1`'s `contract.rs`).
//!
//! ```text
//! pub fn verify(digest: &[u8], r: &[u8; 48], s: &[u8; 48], point: &[u8]) -> (ok: bool)
//!     requires verify_requires(digest@),
//!     ensures  verify_ensures(digest@, r@, s@, point@, ok)
//! ```

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What the caller owes `verify`: a digest of 0 to 64 octets (so SHA-256,
/// SHA-384 and SHA-512 are all accepted; modelling choice 1 of the spec).
/// `r` and `s` are `[u8; 48]` arrays, so their length is in the type, and
/// `point` may be any octet string: decoding is inside the verifier.
pub open spec fn verify_requires(digest: Seq<u8>) -> bool {
    digest.len() <= 64
}

/// `verify(digest, r, s, point)`: ECDSA verification over P-384 (FIPS 186-5
/// §6.4.2). `r` and `s` are the big-endian octets of the signature integers,
/// and `point` is the 97-octet ECPoint `04 || X || Y` of the public key (any
/// other string is rejected by the spec's decoding).
pub open spec fn verify_ensures(
    digest: Seq<u8>,
    r: Seq<u8>,
    s: Seq<u8>,
    point: Seq<u8>,
    ok: bool,
) -> bool {
    ok == ecdsa_verify(p384(), digest, os2ip(r), os2ip(s), point)
}

} // verus!
