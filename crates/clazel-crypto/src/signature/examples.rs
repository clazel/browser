//! Known answers, evaluated: small cases of the signature check's parsing
//! and profile functions, with results written out from the RFCs or worked
//! out independently of [`super::spec`], proven by evaluating the spec
//! (`by (compute_only)`). They are facts about the spec itself and the
//! theorems the mutation certificates in `mutations.json` contradict.
//!
//! The three verifications are uninterpreted, so nothing here evaluates
//! one; the guards around them are covered by the exec proof and
//! tests/signature.rs (their mutations are `killed-incidentally`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A SubjectPublicKeyInfo with the given algorithm and key bits. The fields
/// the signature check does not read are left empty.
pub open spec fn ex_spki(oid: Seq<nat>, parameters_der: Option<Seq<u8>>, unused_bits: u8,
    bits: Seq<u8>) -> clazel_x509::spki::spec::SubjectPublicKeyInfo {
    clazel_x509::spki::spec::SubjectPublicKeyInfo {
        algorithm: clazel_x509::certificate::spec::AlgorithmIdentifier { oid, parameters_der },
        public_key: clazel_x509::spki::spec::PublicKey::Unsupported,
        subject_public_key_unused_bits: unused_bits,
        subject_public_key_bits: bits,
        subject_public_key_tlv: Seq::empty(),
        spki_der: Seq::empty(),
    }
}

/// An X || Y whose octets are 1, 2, ..., 64, so a shifted copy differs.
pub open spec fn ex_point() -> Seq<u8> {
    Seq::new(64, |i: int| (i + 1) as u8)
}

/// A secp256r1 key in uncompressed form, 0x04 || X || Y (RFC 5480 §2.2).
pub open spec fn ex_p256_spki(first: u8, point: Seq<u8>) -> clazel_x509::spki::spec::SubjectPublicKeyInfo {
    ex_spki(seq![1nat, 2nat, 840nat, 10045nat, 2nat, 1nat],
        Some(seq![0x06u8, 0x08u8, 0x2au8, 0x86u8, 0x48u8, 0xceu8, 0x3du8, 0x03u8, 0x01u8, 0x07u8]),
        0, seq![first] + point)
}

/// RFC 5480 §2.1.1 and RFC 8410 §3: the key algorithm identifiers.
pub proof fn lemma_oid_examples()
    ensures
        is_ec_public_key(seq![1nat, 2nat, 840nat, 10045nat, 2nat, 1nat]),
        // ecdsa-with-SHA256 (RFC 5758 §3.2) is a signature, not a key, OID.
        !is_ec_public_key(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat]),
        is_ed25519(seq![1nat, 3nat, 101nat, 112nat]),
        // id-Ed448 (RFC 8410 §3).
        !is_ed25519(seq![1nat, 3nat, 101nat, 113nat]),
{
    assert(is_ec_public_key(seq![1nat, 2nat, 840nat, 10045nat, 2nat, 1nat])) by (compute_only);
    assert(!is_ec_public_key(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat])) by (compute_only);
    assert(is_ed25519(seq![1nat, 3nat, 101nat, 112nat])) by (compute_only);
    assert(!is_ed25519(seq![1nat, 3nat, 101nat, 113nat])) by (compute_only);
}

/// RFC 5480 §2.1.1.1: the namedCurve parameter decodes, with our DER
/// decoder, to secp256r1's OBJECT IDENTIFIER 1.2.840.10045.3.1.7.
pub proof fn lemma_secp256r1_parameter_example()
    ensures
        clazel_der::spec::read_oid(secp256r1_parameter(), 0, 10)
            == Some((seq![1nat, 2nat, 840nat, 10045nat, 3nat, 1nat, 7nat], 10nat)),
{
    assert(clazel_der::spec::read_oid(secp256r1_parameter(), 0, 10)
        == Some((seq![1nat, 2nat, 840nat, 10045nat, 3nat, 1nat, 7nat], 10nat))) by (compute_only);
}

/// Left-padding to 32 octets keeps the value: zeros go in front.
pub proof fn lemma_pad32_example()
    ensures
        pad32(seq![0x01u8]).len() == 32,
        pad32(seq![0x01u8])[0] == 0u8,
        pad32(seq![0x01u8])[31] == 0x01u8,
{
    assert(pad32(seq![0x01u8]).len() == 32) by (compute_only);
    assert(pad32(seq![0x01u8])[0] == 0u8) by (compute_only);
    assert(pad32(seq![0x01u8])[31] == 0x01u8) by (compute_only);
}

/// RFC 5480 §2.2: only 0x04 || X || Y, 65 octets, with no unused bits.
pub proof fn lemma_p256_point_examples()
    ensures
        p256_point(ex_p256_spki(0x04u8, ex_point())) == Some(ex_point()),
        // The compressed form, 0x02 || X.
        p256_point(ex_p256_spki(0x02u8, ex_point().subrange(0, 32))) is None,
        // A point one octet short.
        p256_point(ex_p256_spki(0x04u8, ex_point().subrange(0, 63))) is None,
{
    assert(p256_point(ex_p256_spki(0x04u8, ex_point())) == Some(ex_point())) by (compute_only);
    assert(p256_point(ex_p256_spki(0x02u8, ex_point().subrange(0, 32))) is None) by (compute_only);
    assert(p256_point(ex_p256_spki(0x04u8, ex_point().subrange(0, 63))) is None) by (compute_only);
}

/// Ecdsa-Sig-Value { r 1, s 2 } (RFC 3279 §2.2.3).
pub open spec fn ex_sig_1_2() -> Seq<u8> {
    seq![0x30u8, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02]
}

/// `n` octets of 0xff.
pub open spec fn ex_ones(n: nat) -> Seq<u8> {
    Seq::new(n, |i: int| 0xffu8)
}

/// Ecdsa-Sig-Value { r 2^256 - 1, s 2^256 - 1 }: 32 magnitude octets each,
/// after the 0x00 that keeps them positive.
pub open spec fn ex_sig_max() -> Seq<u8> {
    seq![0x30u8, 0x46, 0x02, 0x21, 0x00] + ex_ones(32) + seq![0x02u8, 0x21, 0x00] + ex_ones(32)
}

/// RFC 3279 §2.2.3 and the modelling choices: one SEQUENCE of two
/// non-negative INTEGERs of at most 32 magnitude octets, nothing after it.
pub proof fn lemma_ecdsa_sig_value_examples()
    ensures
        ecdsa_sig_value(ex_sig_1_2()) == Some((pad32(seq![0x01u8]), pad32(seq![0x02u8]))),
        ecdsa_sig_value(ex_sig_max()) == Some((ex_ones(32), ex_ones(32))),
        // r = -128.
        ecdsa_sig_value(seq![0x30u8, 0x06, 0x02, 0x01, 0x80, 0x02, 0x01, 0x02]) is None,
        // A third INTEGER.
        ecdsa_sig_value(seq![0x30u8, 0x09, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02, 0x02, 0x01, 0x03]) is None,
        // An octet after the SEQUENCE.
        ecdsa_sig_value(seq![0x30u8, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02, 0x00]) is None,
{
    assert(ecdsa_sig_value(ex_sig_1_2()) == Some((pad32(seq![0x01u8]), pad32(seq![0x02u8]))))
        by (compute_only);
    assert(ecdsa_sig_value(ex_sig_max()) == Some((ex_ones(32), ex_ones(32)))) by (compute_only);
    assert(ecdsa_sig_value(seq![0x30u8, 0x06, 0x02, 0x01, 0x80, 0x02, 0x01, 0x02]) is None)
        by (compute_only);
    assert(ecdsa_sig_value(seq![0x30u8, 0x09, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02, 0x02, 0x01, 0x03])
        is None) by (compute_only);
    assert(ecdsa_sig_value(seq![0x30u8, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02, 0x00]) is None)
        by (compute_only);
}

/// libcrux-rsa 0.0.9's moduli: 2048 to 8192 bits, the top bit set.
pub proof fn lemma_modulus_ok_examples()
    ensures
        modulus_ok(ex_ones(256)),
        modulus_ok(ex_ones(768)),
        modulus_ok(Seq::new(256, |i: int| if i == 0 { 0x80u8 } else { 0u8 })),
        // 2047 bits.
        !modulus_ok(Seq::new(256, |i: int| if i == 0 { 0x7fu8 } else { 0xffu8 })),
        // 2040 bits.
        !modulus_ok(ex_ones(255)),
{
    assert(modulus_ok(ex_ones(256))) by (compute_only);
    assert(modulus_ok(ex_ones(768))) by (compute_only);
    assert(modulus_ok(Seq::new(256, |i: int| if i == 0 { 0x80u8 } else { 0u8 }))) by (compute_only);
    assert(!modulus_ok(Seq::new(256, |i: int| if i == 0 { 0x7fu8 } else { 0xffu8 }))) by (compute_only);
    assert(!modulus_ok(ex_ones(255))) by (compute_only);
}

/// FIPS 180-4: the SHA-2 digest lengths, which RFC 8446 §4.2.3 makes the
/// PSS salt lengths.
pub proof fn lemma_hash_len_examples()
    ensures
        hash_len(Hash::Sha256) == 32,
        hash_len(Hash::Sha384) == 48,
        hash_len(Hash::Sha512) == 64,
{
}

/// 32 octets: `first`, then 30 of `middle`, then `last`.
pub open spec fn ex_key(first: u8, middle: u8, last: u8) -> Seq<u8> {
    Seq::new(32, |i: int| if i == 0 { first } else if i == 31 { last } else { middle })
}

/// The encodings of edwards25519's eight points of order dividing 8, and
/// p and p + 1, computed from RFC 8032 §5.1's curve equation separately
/// from the table in the spec (they match libsodium's blocklist).
pub open spec fn ex_order8_a(sign: u8) -> Seq<u8> {
    seq![0x26u8, 0xe8, 0x95, 0x8f, 0xc2, 0xb2, 0x27, 0xb0, 0x45, 0xc3, 0xf4, 0x89, 0xf2, 0xef,
        0x98, 0xf0, 0xd5, 0xdf, 0xac, 0x05, 0xd3, 0xc6, 0x33, 0x39, 0xb1, 0x38, 0x02, 0x88,
        0x6d, 0x53, 0xfc, 0x05 | sign]
}

/// The other order-8 pair (see [`ex_order8_a`]).
pub open spec fn ex_order8_b(sign: u8) -> Seq<u8> {
    seq![0xc7u8, 0x17, 0x6a, 0x70, 0x3d, 0x4d, 0xd8, 0x4f, 0xba, 0x3c, 0x0b, 0x76, 0x0d, 0x10,
        0x67, 0x0f, 0x2a, 0x20, 0x53, 0xfa, 0x2c, 0x39, 0xcc, 0xc6, 0x4e, 0xc7, 0xfd, 0x77,
        0x92, 0xac, 0x03, 0x7a | sign]
}

/// Each small-order encoding matches its table entry, with either x sign
/// bit, and the identity is small-order.
pub proof fn lemma_small_order_examples()
    ensures
        same_y(ex_key(0x00, 0x00, 0x00), small_order_y()[0]),
        same_y(ex_key(0x00, 0x00, 0x80), small_order_y()[0]),
        same_y(ex_key(0x01, 0x00, 0x00), small_order_y()[1]),
        same_y(ex_key(0x01, 0x00, 0x80), small_order_y()[1]),
        same_y(ex_key(0xec, 0xff, 0x7f), small_order_y()[2]),
        same_y(ex_order8_a(0x00), small_order_y()[3]),
        same_y(ex_order8_a(0x80), small_order_y()[3]),
        same_y(ex_order8_b(0x00), small_order_y()[4]),
        same_y(ex_order8_b(0x80), small_order_y()[4]),
        same_y(ex_key(0xed, 0xff, 0x7f), small_order_y()[5]),
        same_y(ex_key(0xee, 0xff, 0x7f), small_order_y()[6]),
        // The first octet counts: the identity is not y = 0.
        !same_y(ex_key(0x01, 0x00, 0x00), small_order_y()[0]),
        small_order_y().len() == 7,
        is_small_order(ex_key(0x01, 0x00, 0x00)),
{
    assert(same_y(ex_key(0x00, 0x00, 0x00), small_order_y()[0])) by (compute_only);
    assert(same_y(ex_key(0x00, 0x00, 0x80), small_order_y()[0])) by (compute_only);
    assert(same_y(ex_key(0x01, 0x00, 0x00), small_order_y()[1])) by (compute_only);
    assert(same_y(ex_key(0x01, 0x00, 0x80), small_order_y()[1])) by (compute_only);
    assert(same_y(ex_key(0xec, 0xff, 0x7f), small_order_y()[2])) by (compute_only);
    assert(same_y(ex_order8_a(0x00), small_order_y()[3])) by (compute_only);
    assert(same_y(ex_order8_a(0x80), small_order_y()[3])) by (compute_only);
    assert(same_y(ex_order8_b(0x00), small_order_y()[4])) by (compute_only);
    assert(same_y(ex_order8_b(0x80), small_order_y()[4])) by (compute_only);
    assert(same_y(ex_key(0xed, 0xff, 0x7f), small_order_y()[5])) by (compute_only);
    assert(same_y(ex_key(0xee, 0xff, 0x7f), small_order_y()[6])) by (compute_only);
    assert(!same_y(ex_key(0x01, 0x00, 0x00), small_order_y()[0])) by (compute_only);
    assert(small_order_y().len() == 7) by (compute_only);
}

} // verus!
