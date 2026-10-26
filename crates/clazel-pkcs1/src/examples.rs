//! Known answers, evaluated: small cases of the RFC's functions with
//! results worked out by hand or written out from the RFC's text, proven by
//! evaluating the spec (`by (compute_only)`). They are facts about the
//! spec itself, evidence that the transcription computes what the RFC
//! defines, and the theorems the mutation certificates in `mutations.json`
//! contradict.
//!
//! The verification examples use `e = 1` with the signature equal to the
//! encoded message (`s^1 mod n = s`), so no private key is needed, and the
//! smallest modulus with the right octet length (`256^(k-1)`). The steps of
//! §8.2.2 are exercised through `rsassa_pkcs1_v1_5_verify_steps`, which has
//! no size restriction; the 2048-bit restriction is `modulus_in_range`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `n` zero octets.
pub open spec fn ex_zeros(n: nat) -> Seq<u8> {
    Seq::new(n, |i: int| 0u8)
}

/// `n` octets of 0xff.
pub open spec fn ex_ones(n: nat) -> Seq<u8> {
    Seq::new(n, |i: int| 0xffu8)
}

/// The smallest modulus of `k` octets.
pub open spec fn ex_n(k: nat) -> nat {
    pow256((k - 1) as nat)
}

/// The encoded message for the all-zero 32-octet digest and `Sha256`,
/// the shortest the RFC allows (`emLen = tLen + 11 = 62`: eight octets of
/// padding), written out from §9.2 step 5.
pub open spec fn ex_em_sha256() -> Seq<u8> {
    seq![0x00u8, 0x01u8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0x00u8, 0x30u8, 0x31u8, 0x30u8, 0x0du8, 0x06u8, 0x09u8, 0x60u8, 0x86u8, 0x48u8, 0x01u8, 0x65u8, 0x03u8, 0x04u8, 0x02u8, 0x01u8, 0x05u8, 0x00u8, 0x04u8, 0x20u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8]
}

/// The encoded message for the all-zero 48-octet digest and `Sha384`,
/// the shortest the RFC allows (`emLen = tLen + 11 = 78`: eight octets of
/// padding), written out from §9.2 step 5.
pub open spec fn ex_em_sha384() -> Seq<u8> {
    seq![0x00u8, 0x01u8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0x00u8, 0x30u8, 0x41u8, 0x30u8, 0x0du8, 0x06u8, 0x09u8, 0x60u8, 0x86u8, 0x48u8, 0x01u8, 0x65u8, 0x03u8, 0x04u8, 0x02u8, 0x02u8, 0x05u8, 0x00u8, 0x04u8, 0x30u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8]
}

/// The encoded message for the all-zero 64-octet digest and `Sha512`,
/// the shortest the RFC allows (`emLen = tLen + 11 = 94`: eight octets of
/// padding), written out from §9.2 step 5.
pub open spec fn ex_em_sha512() -> Seq<u8> {
    seq![0x00u8, 0x01u8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0x00u8, 0x30u8, 0x51u8, 0x30u8, 0x0du8, 0x06u8, 0x09u8, 0x60u8, 0x86u8, 0x48u8, 0x01u8, 0x65u8, 0x03u8, 0x04u8, 0x02u8, 0x03u8, 0x05u8, 0x00u8, 0x04u8, 0x40u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8]
}


/// OS2IP and I2OSP (§4.1, §4.2): `1 * 256 + 2 = 258`, the first octet the
/// most significant; 256 does not fit one octet.
pub proof fn lemma_os2ip_i2osp_examples()
    ensures
        os2ip(seq![1u8, 2u8]) == 258nat,
        os2ip(seq![0x12u8, 0x34u8, 0x56u8]) == 0x123456nat,
        os2ip(Seq::<u8>::empty()) == 0nat,
        i2osp(258nat, 2nat) == Some(seq![1u8, 2u8]),
        i2osp(0x123456nat, 4nat) == Some(seq![0u8, 0x12u8, 0x34u8, 0x56u8]),
        i2osp(255nat, 1nat) == Some(seq![255u8]),
        i2osp(256nat, 1nat) is None,
        i2osp(0nat, 0nat) == Some(Seq::<u8>::empty()),
        i2osp(1nat, 0nat) is None,
{
    reveal(vstd::arithmetic::power::pow);
    assert(os2ip(seq![1u8, 2u8]) == 258nat) by (compute_only);
    assert(os2ip(seq![0x12u8, 0x34u8, 0x56u8]) == 0x123456nat) by (compute_only);
    assert(os2ip(Seq::<u8>::empty()) == 0nat) by (compute_only);
    assert(i2osp(258nat, 2nat) == Some(seq![1u8, 2u8])) by (compute_only);
    assert(i2osp(0x123456nat, 4nat) == Some(seq![0u8, 0x12u8, 0x34u8, 0x56u8])) by (compute_only);
    assert(i2osp(255nat, 1nat) == Some(seq![255u8])) by (compute_only);
    assert(i2osp(256nat, 1nat) is None) by (compute_only);
    assert(i2osp(0nat, 0nat) == Some(Seq::<u8>::empty())) by (compute_only);
    assert(i2osp(1nat, 0nat) is None) by (compute_only);
}

/// `octet_len`, the RFC's `k`.
pub proof fn lemma_octet_len_examples()
    ensures
        octet_len(0nat) == 0nat,
        octet_len(255nat) == 1nat,
        octet_len(256nat) == 2nat,
        octet_len(65535nat) == 2nat,
        octet_len(65536nat) == 3nat,
{
    assert(octet_len(0nat) == 0nat) by (compute_only);
    assert(octet_len(255nat) == 1nat) by (compute_only);
    assert(octet_len(256nat) == 2nat) by (compute_only);
    assert(octet_len(65535nat) == 2nat) by (compute_only);
    assert(octet_len(65536nat) == 3nat) by (compute_only);
}

/// RSAVP1 (§5.2.2): `2^3 = 8 (mod 33)`, and a representative must be below
/// `n`; `4^13 = 445 (mod 497)`, the textbook modular exponentiation.
pub proof fn lemma_rsavp1_examples()
    ensures
        rsavp1(33nat, 3nat, 2nat) == Some(8nat),
        rsavp1(33nat, 3nat, 32nat) == Some(32nat),
        rsavp1(33nat, 3nat, 33nat) is None,
        rsavp1(33nat, 3nat, 34nat) is None,
        modpow(4nat, 13nat, 497nat) == 445nat,
        modpow(7nat, 0nat, 10nat) == 1nat,
{
    reveal(vstd::arithmetic::power::pow);
    assert(rsavp1(33nat, 3nat, 2nat) == Some(8nat)) by (compute_only);
    assert(rsavp1(33nat, 3nat, 32nat) == Some(32nat)) by (compute_only);
    assert(rsavp1(33nat, 3nat, 33nat) is None) by (compute_only);
    assert(rsavp1(33nat, 3nat, 34nat) is None) by (compute_only);
    assert(modpow(4nat, 13nat, 497nat) == 445nat) by (compute_only);
    assert(modpow(7nat, 0nat, 10nat) == 1nat) by (compute_only);
}

/// §9.2 Note 1: the `DigestInfo` prefixes, octet by octet where they
/// identify the hash, and `hLen`.
pub proof fn lemma_digest_info_examples()
    ensures
        hash_len(HashId::Sha256) == 32nat,
        hash_len(HashId::Sha384) == 48nat,
        hash_len(HashId::Sha512) == 64nat,
        digest_info_prefix(HashId::Sha256).len() == 19nat,
        digest_info_prefix(HashId::Sha384).len() == 19nat,
        digest_info_prefix(HashId::Sha512).len() == 19nat,
        digest_info_prefix(HashId::Sha256)[1] == 0x31u8,
        digest_info_prefix(HashId::Sha384)[1] == 0x41u8,
        digest_info_prefix(HashId::Sha512)[1] == 0x51u8,
        digest_info_prefix(HashId::Sha256)[14] == 1u8,
        digest_info_prefix(HashId::Sha384)[14] == 2u8,
        digest_info_prefix(HashId::Sha512)[14] == 3u8,
        digest_info_prefix(HashId::Sha256)[18] == 0x20u8,
        digest_info_prefix(HashId::Sha384)[18] == 0x30u8,
        digest_info_prefix(HashId::Sha512)[18] == 0x40u8,
        digest_info_prefix(HashId::Sha256)[0] == 0x30u8,
        digest_info_prefix(HashId::Sha256)[6] == 0x60u8,
        digest_info_prefix(HashId::Sha256)[7] == 0x86u8,
        digest_info_prefix(HashId::Sha256)[16] == 0x00u8,
{
    assert(hash_len(HashId::Sha256) == 32nat) by (compute_only);
    assert(hash_len(HashId::Sha384) == 48nat) by (compute_only);
    assert(hash_len(HashId::Sha512) == 64nat) by (compute_only);
    assert(digest_info_prefix(HashId::Sha256).len() == 19nat) by (compute_only);
    assert(digest_info_prefix(HashId::Sha384).len() == 19nat) by (compute_only);
    assert(digest_info_prefix(HashId::Sha512).len() == 19nat) by (compute_only);
    assert(digest_info_prefix(HashId::Sha256)[1] == 0x31u8) by (compute_only);
    assert(digest_info_prefix(HashId::Sha384)[1] == 0x41u8) by (compute_only);
    assert(digest_info_prefix(HashId::Sha512)[1] == 0x51u8) by (compute_only);
    assert(digest_info_prefix(HashId::Sha256)[14] == 1u8) by (compute_only);
    assert(digest_info_prefix(HashId::Sha384)[14] == 2u8) by (compute_only);
    assert(digest_info_prefix(HashId::Sha512)[14] == 3u8) by (compute_only);
    assert(digest_info_prefix(HashId::Sha256)[18] == 0x20u8) by (compute_only);
    assert(digest_info_prefix(HashId::Sha384)[18] == 0x30u8) by (compute_only);
    assert(digest_info_prefix(HashId::Sha512)[18] == 0x40u8) by (compute_only);
    assert(digest_info_prefix(HashId::Sha256)[0] == 0x30u8) by (compute_only);
    assert(digest_info_prefix(HashId::Sha256)[6] == 0x60u8) by (compute_only);
    assert(digest_info_prefix(HashId::Sha256)[7] == 0x86u8) by (compute_only);
    assert(digest_info_prefix(HashId::Sha256)[16] == 0x00u8) by (compute_only);
}

/// EMSA-PKCS1-v1_5-ENCODE (§9.2): the shortest encoding for each hash is
/// exactly the written-out block; one octet less is "intended encoded
/// message length too short"; a digest of the wrong length is refused; with
/// more room the padding grows.
pub proof fn lemma_encode_examples()
    ensures
        emsa_pkcs1_v1_5_encode(ex_zeros(32), 62nat, HashId::Sha256) == Some(ex_em_sha256()),
        emsa_pkcs1_v1_5_encode(ex_zeros(48), 78nat, HashId::Sha384) == Some(ex_em_sha384()),
        emsa_pkcs1_v1_5_encode(ex_zeros(64), 94nat, HashId::Sha512) == Some(ex_em_sha512()),
        emsa_pkcs1_v1_5_encode(ex_zeros(32), 61nat, HashId::Sha256) is None,
        emsa_pkcs1_v1_5_encode(ex_zeros(48), 77nat, HashId::Sha384) is None,
        emsa_pkcs1_v1_5_encode(ex_zeros(64), 93nat, HashId::Sha512) is None,
        emsa_pkcs1_v1_5_encode(ex_zeros(31), 62nat, HashId::Sha256) is None,
        emsa_pkcs1_v1_5_encode(ex_zeros(32), 62nat, HashId::Sha384) is None,
        emsa_pkcs1_v1_5_encode(ex_zeros(32), 63nat, HashId::Sha256) == Some(
            seq![0x00u8, 0x01u8, 0xffu8] + ex_em_sha256().skip(2),
        ),
{
    reveal(vstd::arithmetic::power::pow);
    assert(emsa_pkcs1_v1_5_encode(ex_zeros(32), 62nat, HashId::Sha256) == Some(ex_em_sha256()))
        by (compute_only);
    assert(emsa_pkcs1_v1_5_encode(ex_zeros(48), 78nat, HashId::Sha384) == Some(ex_em_sha384()))
        by (compute_only);
    assert(emsa_pkcs1_v1_5_encode(ex_zeros(64), 94nat, HashId::Sha512) == Some(ex_em_sha512()))
        by (compute_only);
    assert(emsa_pkcs1_v1_5_encode(ex_zeros(32), 61nat, HashId::Sha256) is None) by (compute_only);
    assert(emsa_pkcs1_v1_5_encode(ex_zeros(48), 77nat, HashId::Sha384) is None) by (compute_only);
    assert(emsa_pkcs1_v1_5_encode(ex_zeros(64), 93nat, HashId::Sha512) is None) by (compute_only);
    assert(emsa_pkcs1_v1_5_encode(ex_zeros(31), 62nat, HashId::Sha256) is None) by (compute_only);
    assert(emsa_pkcs1_v1_5_encode(ex_zeros(32), 62nat, HashId::Sha384) is None) by (compute_only);
    assert(emsa_pkcs1_v1_5_encode(ex_zeros(32), 63nat, HashId::Sha256) == Some(
        seq![0x00u8, 0x01u8, 0xffu8] + ex_em_sha256().skip(2),
    )) by (compute_only);
}

/// The steps of RSASSA-PKCS1-V1_5-VERIFY (§8.2.2) on small keys with `e =
/// 1` and the signature equal to the encoded message: the genuine block
/// verifies; a signature of the wrong length (step 1), one at least `n`
/// (step 2.(c)), a block with a bad padding octet, a wrong digest or a
/// wrong hash (step 3), or any other block (step 4) does not.
pub proof fn lemma_verify_steps_examples()
    ensures
        rsassa_pkcs1_v1_5_verify_steps(ex_n(62nat), 1nat, ex_zeros(32), HashId::Sha256, ex_em_sha256()),
        rsassa_pkcs1_v1_5_verify_steps(ex_n(78nat), 1nat, ex_zeros(48), HashId::Sha384, ex_em_sha384()),
        rsassa_pkcs1_v1_5_verify_steps(ex_n(94nat), 1nat, ex_zeros(64), HashId::Sha512, ex_em_sha512()),
        !rsassa_pkcs1_v1_5_verify_steps(
            ex_n(62nat),
            1nat,
            ex_zeros(32),
            HashId::Sha256,
            ex_em_sha256().skip(1),
        ),
        !rsassa_pkcs1_v1_5_verify_steps(
            ex_n(62nat),
            1nat,
            ex_zeros(32),
            HashId::Sha256,
            seq![0u8] + ex_em_sha256(),
        ),
        !rsassa_pkcs1_v1_5_verify_steps(ex_n(62nat), 1nat, ex_zeros(32), HashId::Sha256, ex_ones(62nat)),
        !rsassa_pkcs1_v1_5_verify_steps(
            ex_n(62nat),
            1nat,
            ex_zeros(32),
            HashId::Sha256,
            seq![1u8] + ex_zeros(61nat),
        ),
        !rsassa_pkcs1_v1_5_verify_steps(ex_n(62nat), 1nat, ex_ones(32), HashId::Sha256, ex_em_sha256()),
        !rsassa_pkcs1_v1_5_verify_steps(ex_n(62nat), 1nat, ex_zeros(32), HashId::Sha384, ex_em_sha256()),
        !rsassa_pkcs1_v1_5_verify_steps(
            ex_n(62nat),
            1nat,
            ex_zeros(32),
            HashId::Sha256,
            ex_em_sha256().update(5, 0xfeu8),
        ),
        !rsassa_pkcs1_v1_5_verify_steps(
            ex_n(62nat),
            1nat,
            ex_zeros(32),
            HashId::Sha256,
            ex_em_sha256().update(1, 2u8),
        ),
        !rsassa_pkcs1_v1_5_verify_steps(
            ex_n(62nat),
            1nat,
            ex_zeros(32),
            HashId::Sha256,
            ex_em_sha256().update(61, 1u8),
        ),
        !rsassa_pkcs1_v1_5_verify_steps(
            ex_n(62nat),
            1nat,
            ex_zeros(32),
            HashId::Sha256,
            ex_em_sha256().update(10, 1u8),
        ),
{
    reveal(vstd::arithmetic::power::pow);
    assert(rsassa_pkcs1_v1_5_verify_steps(ex_n(62nat), 1nat, ex_zeros(32), HashId::Sha256, ex_em_sha256()))
        by (compute_only);
    assert(rsassa_pkcs1_v1_5_verify_steps(ex_n(78nat), 1nat, ex_zeros(48), HashId::Sha384, ex_em_sha384()))
        by (compute_only);
    assert(rsassa_pkcs1_v1_5_verify_steps(ex_n(94nat), 1nat, ex_zeros(64), HashId::Sha512, ex_em_sha512()))
        by (compute_only);
    assert(!rsassa_pkcs1_v1_5_verify_steps(
        ex_n(62nat),
        1nat,
        ex_zeros(32),
        HashId::Sha256,
        ex_em_sha256().skip(1),
    )) by (compute_only);
    assert(!rsassa_pkcs1_v1_5_verify_steps(
        ex_n(62nat),
        1nat,
        ex_zeros(32),
        HashId::Sha256,
        seq![0u8] + ex_em_sha256(),
    )) by (compute_only);
    assert(!rsassa_pkcs1_v1_5_verify_steps(ex_n(62nat), 1nat, ex_zeros(32), HashId::Sha256, ex_ones(62nat)))
        by (compute_only);
    assert(!rsassa_pkcs1_v1_5_verify_steps(
        ex_n(62nat),
        1nat,
        ex_zeros(32),
        HashId::Sha256,
        seq![1u8] + ex_zeros(61nat),
    )) by (compute_only);
    assert(!rsassa_pkcs1_v1_5_verify_steps(ex_n(62nat), 1nat, ex_ones(32), HashId::Sha256, ex_em_sha256()))
        by (compute_only);
    assert(!rsassa_pkcs1_v1_5_verify_steps(ex_n(62nat), 1nat, ex_zeros(32), HashId::Sha384, ex_em_sha256()))
        by (compute_only);
    assert(!rsassa_pkcs1_v1_5_verify_steps(
        ex_n(62nat),
        1nat,
        ex_zeros(32),
        HashId::Sha256,
        ex_em_sha256().update(5, 0xfeu8),
    )) by (compute_only);
    assert(!rsassa_pkcs1_v1_5_verify_steps(
        ex_n(62nat),
        1nat,
        ex_zeros(32),
        HashId::Sha256,
        ex_em_sha256().update(1, 2u8),
    )) by (compute_only);
    assert(!rsassa_pkcs1_v1_5_verify_steps(
        ex_n(62nat),
        1nat,
        ex_zeros(32),
        HashId::Sha256,
        ex_em_sha256().update(61, 1u8),
    )) by (compute_only);
    assert(!rsassa_pkcs1_v1_5_verify_steps(
        ex_n(62nat),
        1nat,
        ex_zeros(32),
        HashId::Sha256,
        ex_em_sha256().update(10, 1u8),
    )) by (compute_only);
}

/// The domain restrictions: 2048 to 8192 bit moduli, `3 <= e <= 2^64 - 1`.
pub proof fn lemma_range_examples()
    ensures
        modulus_in_range(two_to(2047)),
        !modulus_in_range((two_to(2047) - 1) as nat),
        modulus_in_range((two_to(8192) - 1) as nat),
        !modulus_in_range(two_to(8192)),
        exponent_in_range(3nat),
        !exponent_in_range(2nat),
        !exponent_in_range(0nat),
        exponent_in_range(0xFFFF_FFFF_FFFF_FFFFnat),
        !exponent_in_range(0x1_0000_0000_0000_0000nat),
{
    reveal(vstd::arithmetic::power::pow);
    assert(modulus_in_range(two_to(2047))) by (compute_only);
    assert(!modulus_in_range((two_to(2047) - 1) as nat)) by (compute_only);
    assert(modulus_in_range((two_to(8192) - 1) as nat)) by (compute_only);
    assert(!modulus_in_range(two_to(8192))) by (compute_only);
    assert(exponent_in_range(3nat)) by (compute_only);
    assert(!exponent_in_range(2nat)) by (compute_only);
    assert(!exponent_in_range(0nat)) by (compute_only);
    assert(exponent_in_range(0xFFFF_FFFF_FFFF_FFFFnat)) by (compute_only);
    assert(!exponent_in_range(0x1_0000_0000_0000_0000nat)) by (compute_only);
}

/// The limb value (`bignum/spec.rs`): little-endian, radix 2^64.
pub proof fn lemma_value_examples()
    ensures
        crate::bignum::spec::value(seq![1u64, 2u64]) == 1 + 2 * 0x1_0000_0000_0000_0000nat,
        crate::bignum::spec::value(seq![0u64, 1u64]) == 0x1_0000_0000_0000_0000nat,
        crate::bignum::spec::value(seq![5u64, 0u64, 0u64]) == 5nat,
        crate::bignum::spec::value(seq![0u64, 0u64, 7u64]) == 7 * 0x1_0000_0000_0000_0000nat
            * 0x1_0000_0000_0000_0000nat,
        crate::bignum::spec::value(Seq::<u64>::empty()) == 0nat,
        crate::bignum::spec::limb_pow(3nat) == 0x1_0000_0000_0000_0000nat
            * 0x1_0000_0000_0000_0000nat * 0x1_0000_0000_0000_0000nat,
{
    assert(crate::bignum::spec::value(seq![1u64, 2u64]) == 1 + 2 * 0x1_0000_0000_0000_0000nat)
        by (compute_only);
    assert(crate::bignum::spec::value(seq![0u64, 1u64]) == 0x1_0000_0000_0000_0000nat)
        by (compute_only);
    assert(crate::bignum::spec::value(seq![5u64, 0u64, 0u64]) == 5nat) by (compute_only);
    assert(crate::bignum::spec::value(seq![0u64, 0u64, 7u64]) == 7 * 0x1_0000_0000_0000_0000nat
        * 0x1_0000_0000_0000_0000nat) by (compute_only);
    assert(crate::bignum::spec::value(Seq::<u64>::empty()) == 0nat) by (compute_only);
    assert(crate::bignum::spec::limb_pow(3nat) == 0x1_0000_0000_0000_0000nat
        * 0x1_0000_0000_0000_0000nat * 0x1_0000_0000_0000_0000nat) by (compute_only);
}

/// The powers the spec uses: `256^m` and `2^m`.
pub proof fn lemma_power_examples()
    ensures
        pow256(0nat) == 1nat,
        pow256(1nat) == 256nat,
        pow256(2nat) == 65536nat,
        pow256(3nat) == 16777216nat,
        two_to(0nat) == 1nat,
        two_to(3nat) == 8nat,
        two_to(4nat) == 16nat,
        two_to(11nat) == 2048nat,
        two_to(64nat) == 0x1_0000_0000_0000_0000nat,
{
    assert(pow256(0nat) == 1nat) by (compute_only);
    assert(pow256(1nat) == 256nat) by (compute_only);
    assert(pow256(2nat) == 65536nat) by (compute_only);
    assert(pow256(3nat) == 16777216nat) by (compute_only);
    assert(two_to(0nat) == 1nat) by (compute_only);
    assert(two_to(3nat) == 8nat) by (compute_only);
    assert(two_to(4nat) == 16nat) by (compute_only);
    assert(two_to(11nat) == 2048nat) by (compute_only);
    assert(two_to(64nat) == 0x1_0000_0000_0000_0000nat) by (compute_only);
}

/// The domain restrictions apply to the whole verification: with `e = 1`
/// and a signature that equals the encoded message, the steps accept a
/// 2048-bit modulus, and the verification does not, because `e < 3`.
pub proof fn lemma_domain_example()
    ensures
        rsassa_pkcs1_v1_5_verify_steps(
            two_to(2047nat),
            1nat,
            ex_zeros(32),
            HashId::Sha256,
            emsa_pkcs1_v1_5_encode(ex_zeros(32), 256nat, HashId::Sha256).unwrap(),
        ),
        !rsassa_pkcs1_v1_5_verify(
            two_to(2047nat),
            1nat,
            ex_zeros(32),
            HashId::Sha256,
            emsa_pkcs1_v1_5_encode(ex_zeros(32), 256nat, HashId::Sha256).unwrap(),
        ),
{
    reveal(vstd::arithmetic::power::pow);
    assert(rsassa_pkcs1_v1_5_verify_steps(
        two_to(2047nat),
        1nat,
        ex_zeros(32),
        HashId::Sha256,
        emsa_pkcs1_v1_5_encode(ex_zeros(32), 256nat, HashId::Sha256).unwrap(),
    )) by (compute_only);
    assert(!rsassa_pkcs1_v1_5_verify(
        two_to(2047nat),
        1nat,
        ex_zeros(32),
        HashId::Sha256,
        emsa_pkcs1_v1_5_encode(ex_zeros(32), 256nat, HashId::Sha256).unwrap(),
    )) by (compute_only);
}

} // verus!
