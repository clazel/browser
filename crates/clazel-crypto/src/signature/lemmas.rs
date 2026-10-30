//! `p256_point` after the key classification moved into `clazel_x509::spki`
//! is the same function as before, on every key `verify` can see.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// For every key the SPKI decoder accepts, the `EcP256` class gives the
/// point that the earlier, direct definition (RFC 5480 §2.1.1, §2.2 read
/// off the key's fields) gives. So CertificateVerify's meaning is unchanged.
pub proof fn lemma_p256_point_unchanged(
    key: Seq<u8>, spki: clazel_x509::spki::spec::SubjectPublicKeyInfo,
)
    requires clazel_x509::spki::spec::parse_subject_public_key_info(key) == Some(spki),
    ensures p256_point(spki) == p256_point_direct(spki),
{
    // Only the classification is needed, not the decoder's definition.
    hide(clazel_x509::spki::spec::parse_subject_public_key_info);
    clazel_x509::spki::lemmas::lemma_parse_classifies_key(key, spki);
    let alg = spki.algorithm;
    let rsa = seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 1nat];
    assert(rsa.len() == 7);
    assert(is_ec_public_key(alg.oid) == clazel_x509::spki::spec::is_id_ec_public_key(alg.oid));
    assert(secp256r1_parameter() == clazel_x509::spki::spec::secp256r1_parameter());
    assert(secp256r1_parameter().len() == 10);
    assert(clazel_x509::spki::spec::secp384r1_parameter().len() == 7);
    if clazel_x509::spki::spec::is_rsa_encryption(alg.oid) {
        assert(alg.oid.len() == 7);
        assert(!is_ec_public_key(alg.oid));
    }
}

} // verus!
