//! Contracts the executable RFC 8017 functions must be proven to meet.
//! Each exec function's `ensures` clause is exactly one of these
//! predicates, so reviewing these and [`super::spec`] is enough to know what
//! the implementation guarantees. The arithmetic's contracts are in
//! [`super::bignum::contract`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The RFC's operations.
// ---------------------------------------------------------------------

/// `encode_message(digest, em_len, hash)`: EMSA-PKCS1-v1_5-ENCODE.
pub open spec fn encode_ensures(digest: Seq<u8>, em_len: nat, h: HashId, out: Option<Seq<u8>>) -> bool {
    out == emsa_pkcs1_v1_5_encode(digest, em_len, h)
}

/// `verify(n, e, digest, hash, signature)`: RSASSA-PKCS1-V1_5-VERIFY with
/// the modulus given as an octet string `n` (leading zero octets allowed).
pub open spec fn verify_ensures(
    n: Seq<u8>,
    e: u64,
    digest: Seq<u8>,
    h: HashId,
    signature: Seq<u8>,
    result: bool,
) -> bool {
    result == rsassa_pkcs1_v1_5_verify(os2ip(n), e as nat, digest, h, signature)
}

} // verus!
