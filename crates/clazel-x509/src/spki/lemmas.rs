//! Facts about the SubjectPublicKeyInfo spec, proven for use by other crates.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What `parse_subject_public_key_info` classifies a key as: an RSA key for
/// rsaEncryption, and otherwise exactly what `classify_ec_public_key` says
/// of the key's own AlgorithmIdentifier and BIT STRING.
pub proof fn lemma_parse_classifies_key(input: Seq<u8>, spki: SubjectPublicKeyInfo)
    requires parse_subject_public_key_info(input) == Some(spki),
    ensures
        is_rsa_encryption(spki.algorithm.oid) ==> spki.public_key is Rsa,
        !is_rsa_encryption(spki.algorithm.oid) ==> spki.public_key == classify_ec_public_key(
            spki.algorithm, spki.subject_public_key_unused_bits, spki.subject_public_key_bits),
{
}

/// The lengths `classify_ec_public_key` guarantees: an `EcP256` point is the
/// 64 octets X || Y and an `EcP384` point the 97-octet ECPoint.
pub open spec fn ec_lengths_ok(spki: SubjectPublicKeyInfo) -> bool {
    match spki.public_key {
        PublicKey::EcP256(point) => point.len() == 64,
        PublicKey::EcP384(point) => point.len() == 97,
        _ => true,
    }
}

/// Every key the decoder accepts has the lengths of `ec_lengths_ok`.
pub proof fn lemma_parse_ec_lengths(input: Seq<u8>, spki: SubjectPublicKeyInfo)
    requires parse_subject_public_key_info(input) == Some(spki),
    ensures ec_lengths_ok(spki),
{
    lemma_parse_classifies_key(input, spki);
}

} // verus!
