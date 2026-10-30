//! The executable CertificateVerify signature check, proven equal to
//! [`crate::signature::spec::verify`]. Parsing is ours (`clazel-x509`,
//! `clazel-der`); the three verifications are the axioms of
//! [`crate::axioms`].
use crate::axioms;
use crate::signature::spec::Hash;
use clazel_der::decode as der;
use clazel_x509::spki::exec::{PublicKey, SubjectPublicKeyInfo};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// id-Ed25519, 1.3.101.112 (RFC 8410 §3).
fn is_ed25519_oid(oid: &[u64]) -> (r: bool)
    ensures r == crate::signature::spec::is_ed25519(der::nats(oid@)),
{
    oid.len() == 4
        && oid.first() == Some(&1)
        && oid.get(1) == Some(&3)
        && oid.get(2) == Some(&101)
        && oid.get(3) == Some(&112)
}

/// `m` left-padded with zeros to 32 octets.
fn pad32(m: &[u8]) -> (out: Vec<u8>)
    requires m.len() <= 32,
    ensures out@ == crate::signature::spec::pad32(m@), out.len() == 32,
{
    // m.len() <= 32, so this is exact.
    let zeros = 32usize.saturating_sub(m.len());
    let mut out: Vec<u8> = Vec::new();
    let mut k: usize = 0;
    while k < zeros
        invariant k <= zeros, zeros == 32 - m.len(), out@ =~= Seq::new(k as nat, |i: int| 0u8),
        decreases zeros - k,
    {
        out.push(0);
        // k < zeros <= 32, so this is exact.
        k = k.saturating_add(1);
    }
    out.extend_from_slice(m);
    proof { assert(out@ =~= crate::signature::spec::pad32(m@)); }
    out
}

/// RFC 5480 §2.2: the X || Y of an uncompressed secp256r1 key, as
/// classified by `clazel_x509::spki`.
pub(crate) fn p256_point<'a>(spki: &SubjectPublicKeyInfo<'a>) -> (out: Option<&'a [u8]>)
    ensures
        match out {
            Some(p) => crate::signature::spec::p256_point(spki@) == Some(p@),
            None => crate::signature::spec::p256_point(spki@) is None,
        },
{
    match &spki.public_key {
        PublicKey::EcP256(point) => Some(*point),
        _ => None,
    }
}

/// RFC 3279 §2.2.3: r and s of one DER Ecdsa-Sig-Value, padded to 32.
pub(crate) fn ecdsa_sig_value(signature: &[u8]) -> (out: Option<(Vec<u8>, Vec<u8>)>)
    ensures
        match out {
            Some((r, s)) => crate::signature::spec::ecdsa_sig_value(signature@) == Some((r@, s@)),
            None => crate::signature::spec::ecdsa_sig_value(signature@) is None,
        },
{
    let (cs, ce) = der::expect_sequence(signature, 0, signature.len())?;
    if ce != signature.len() {
        return None;
    }
    let (r_negative, rs, re, after_r) = der::read_integer(signature, cs, ce)?;
    // read_integer gives rs <= re and ss <= se, so these are exact.
    if r_negative || re.saturating_sub(rs) > 32 {
        return None;
    }
    let (s_negative, ss, se, after_s) = der::read_integer(signature, after_r, ce)?;
    if s_negative || se.saturating_sub(ss) > 32 || after_s != ce {
        return None;
    }
    let r = pad32(vstd::slice::slice_subrange(signature, rs, re));
    let s = pad32(vstd::slice::slice_subrange(signature, ss, se));
    Some((r, s))
}

/// ecdsa_secp256r1_sha256 (0x0403).
pub(crate) fn ecdsa_p256_sha256(spki: &SubjectPublicKeyInfo, input: &[u8], signature: &[u8]) -> (out: bool)
    requires clazel_x509::spki::lemmas::ec_lengths_ok(spki@),
    ensures out == crate::signature::spec::ecdsa_p256_sha256(spki@, input@, signature@),
{
    match (p256_point(spki), ecdsa_sig_value(signature)) {
        (Some(point), Some((r, s))) =>
            axioms::ecdsa_p256_sha256_verify(input, r.as_slice(), s.as_slice(), point),
        _ => false,
    }
}

/// The modulus sizes libcrux-rsa accepts, with the top bit set.
fn modulus_ok(n: &[u8]) -> (r: bool)
    ensures r == crate::signature::spec::modulus_ok(n@),
{
    let len = n.len();
    (len == 256 || len == 384 || len == 512 || len == 768 || len == 1024)
        && match n.first() { Some(&b) => b >= 0x80, None => false }
}

/// rsa_pss_rsae_* (0x0804-0x0806).
fn rsa_pss_rsae(spki: &SubjectPublicKeyInfo, hash: Hash, input: &[u8], signature: &[u8]) -> (out: bool)
    ensures out == crate::signature::spec::rsa_pss_rsae(spki@, hash, input@, signature@),
{
    match &spki.public_key {
        PublicKey::Rsa(key) => {
            let e = key.public_exponent_octets;
            let n = key.modulus_octets;
            let e_ok = e.len() == 3 && e.first() == Some(&1) && e.get(1) == Some(&0)
                && e.get(2) == Some(&1);
            proof { assert(e_ok == (e@ =~= seq![0x01u8, 0x00u8, 0x01u8])); }
            if !e_ok || !modulus_ok(n) || signature.len() != n.len() {
                return false;
            }
            let salt_len: u32 = match hash {
                Hash::Sha256 => 32,
                Hash::Sha384 => 48,
                Hash::Sha512 => 64,
            };
            axioms::rsa_pss_verify(hash, n, input, salt_len, signature)
        },
        _ => false,
    }
}

/// Whether `key`, ignoring its x sign bit, has y-coordinate `y`.
fn same_y(key: &[u8], y: &[u8]) -> (r: bool)
    requires key.len() == 32, y.len() == 32,
    ensures r == crate::signature::spec::same_y(key@, y@),
{
    let mut i: usize = 0;
    while i < 31
        invariant i <= 31, key.len() == 32, y.len() == 32,
            forall|j: int| 0 <= j < i ==> key@[j] == y@[j],
        decreases 31 - i,
    {
        match (key.get(i), y.get(i)) {
            (Some(a), Some(b)) if *a == *b => {},
            _ => {
                proof { assert(key@.subrange(0, 31)[i as int] != y@.subrange(0, 31)[i as int]); }
                return false;
            },
        }
        // i < 31, so this is exact.
        i = i.saturating_add(1);
    }
    proof { assert(key@.subrange(0, 31) =~= y@.subrange(0, 31)); }
    match (key.get(31), y.get(31)) {
        (Some(a), Some(b)) => *a & 0x7f == *b,
        _ => false,
    }
}

/// Whether the 32-octet `key` encodes a point of small order.
fn is_small_order(key: &[u8]) -> (r: bool)
    requires key.len() == 32,
    ensures r == crate::signature::spec::is_small_order(key@),
{
    // 0: (sqrt(-1), 0) and (-sqrt(-1), 0), order 4
    let y0: [u8; 32] = [
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];
    // 1: the identity (0, 1), order 1
    let y1: [u8; 32] = [
                0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];
    // p - 1: (0, -1), order 2
    let y2: [u8; 32] = [
                0xec, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
    ];
    // two of the order-8 points
    let y3: [u8; 32] = [
                0x26, 0xe8, 0x95, 0x8f, 0xc2, 0xb2, 0x27, 0xb0,
                0x45, 0xc3, 0xf4, 0x89, 0xf2, 0xef, 0x98, 0xf0,
                0xd5, 0xdf, 0xac, 0x05, 0xd3, 0xc6, 0x33, 0x39,
                0xb1, 0x38, 0x02, 0x88, 0x6d, 0x53, 0xfc, 0x05,
    ];
    // the other two order-8 points
    let y4: [u8; 32] = [
                0xc7, 0x17, 0x6a, 0x70, 0x3d, 0x4d, 0xd8, 0x4f,
                0xba, 0x3c, 0x0b, 0x76, 0x0d, 0x10, 0x67, 0x0f,
                0x2a, 0x20, 0x53, 0xfa, 0x2c, 0x39, 0xcc, 0xc6,
                0x4e, 0xc7, 0xfd, 0x77, 0x92, 0xac, 0x03, 0x7a,
    ];
    // p: a non-canonical encoding of 0
    let y5: [u8; 32] = [
                0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
    ];
    // p + 1: a non-canonical encoding of 1
    let y6: [u8; 32] = [
                0xee, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
    ];
    let r = same_y(key, y0.as_slice()) || same_y(key, y1.as_slice())
        || same_y(key, y2.as_slice()) || same_y(key, y3.as_slice())
        || same_y(key, y4.as_slice()) || same_y(key, y5.as_slice())
        || same_y(key, y6.as_slice());
    proof {
        let ys = crate::signature::spec::small_order_y();
        assert(ys.len() == 7);
        assert(y0@ =~= ys[0]);
        assert(y1@ =~= ys[1]);
        assert(y2@ =~= ys[2]);
        assert(y3@ =~= ys[3]);
        assert(y4@ =~= ys[4]);
        assert(y5@ =~= ys[5]);
        assert(y6@ =~= ys[6]);
    }
    r
}

/// ed25519 (0x0807).
fn ed25519(spki: &SubjectPublicKeyInfo, input: &[u8], signature: &[u8]) -> (out: bool)
    ensures out == crate::signature::spec::ed25519(spki@, input@, signature@),
{
    let key = spki.subject_public_key_bits;
    if is_ed25519_oid(spki.algorithm.oid.as_slice())
        && spki.algorithm.parameters_der.is_none()
        && spki.subject_public_key_unused_bits == 0
        && key.len() == 32 && signature.len() == 64
        && !is_small_order(key) {
        axioms::ed25519_verify(input, key, signature)
    } else {
        false
    }
}

/// RFC 8446 §4.4.3: whether `signature` is a valid `scheme` signature of
/// `input` under the end-entity SubjectPublicKeyInfo `key`.
pub fn verify(key: &[u8], scheme: u16, input: &[u8], signature: &[u8]) -> (out: bool)
    ensures out == crate::signature::spec::verify(key@, scheme, input@, signature@),
{
    match clazel_x509::spki::exec::parse_subject_public_key_info(key) {
        None => false,
        Some(spki) => {
            proof { clazel_x509::spki::lemmas::lemma_parse_ec_lengths(key@, spki@); }
            if scheme == 0x0403 { ecdsa_p256_sha256(&spki, input, signature) }
            else if scheme == 0x0804 { rsa_pss_rsae(&spki, Hash::Sha256, input, signature) }
            else if scheme == 0x0805 { rsa_pss_rsae(&spki, Hash::Sha384, input, signature) }
            else if scheme == 0x0806 { rsa_pss_rsae(&spki, Hash::Sha512, input, signature) }
            else if scheme == 0x0807 { ed25519(&spki, input, signature) }
            else { false }
        },
    }
}

} // verus!
