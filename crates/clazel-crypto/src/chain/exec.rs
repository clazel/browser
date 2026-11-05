//! The executable link verifier, proven equal to [`crate::chain::spec::link`]:
//! the production `clazel_x509::path::contract::LinkVerifier`. Key parsing
//! and the signature algorithm's classification are `clazel-x509`'s, RSA
//! PKCS#1 v1.5 is `clazel-pkcs1`'s (both ours, proven), and the digests and
//! the ECDSA verifications are the axioms of [`crate::axioms`].
use crate::axioms;
use clazel_der::decode as der;
use clazel_pkcs1::spec::HashId;
use clazel_x509::certificate::exec::AlgorithmIdentifier;
use clazel_x509::signature_algorithm::exec::{AlgorithmClass, EcdsaHash, RsaPkcs1v15Hash};
use clazel_x509::spki::exec::{PublicKey, RsaPublicKey, SubjectPublicKeyInfo};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Taking a prefix never increases OS2IP (RFC 8017 §4.2).
proof fn lemma_os2ip_prefix_le(s: Seq<u8>, i: nat)
    requires i <= s.len(),
    ensures clazel_pkcs1::spec::os2ip(s.take(i as int)) <= clazel_pkcs1::spec::os2ip(s),
    decreases s.len(),
{
    if i == s.len() {
        assert(s.take(i as int) =~= s);
    } else {
        let d = s.drop_last();
        clazel_pkcs1::lemmas::lemma_os2ip_last(s);
        assert(s.take(i as int) =~= d.take(i as int));
        lemma_os2ip_prefix_le(d, i);
    }
}

/// The public exponent as a number when it is below 2^33 (RFC 8017 §4.2
/// OS2IP); `None` when it is at least 2^33, which `exponent_profile`
/// refuses.
fn exponent_value(octets: &[u8]) -> (out: Option<u64>)
    ensures
        match out {
            Some(e) => e as nat == clazel_pkcs1::spec::os2ip(octets@) && e < 0x2_0000_0000u64,
            None => clazel_pkcs1::spec::os2ip(octets@) >= 0x2_0000_0000nat,
        },
{
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    proof { assert(octets@.take(0) =~= Seq::<u8>::empty()); }
    while i < octets.len()
        invariant
            i <= octets.len(),
            acc as nat == clazel_pkcs1::spec::os2ip(octets@.take(i as int)),
            acc < 0x2_0000_0000u64,
        decreases octets.len() - i,
    {
        let b = match octets.get(i) { Some(b) => *b, None => 0 };
        proof {
            assert(b == octets@[i as int]);
            clazel_pkcs1::lemmas::lemma_os2ip_push(octets@.take(i as int), b);
            assert(octets@.take(i as int).push(b) =~= octets@.take(i as int + 1));
        }
        // acc < 2^33, so acc * 256 + b < 2^41: both are exact.
        acc = acc.saturating_mul(256).saturating_add(b as u64);
        // i < octets.len(), so this is exact.
        i = i.saturating_add(1);
        if acc >= 0x2_0000_0000u64 {
            proof { lemma_os2ip_prefix_le(octets@, i as nat); }
            return None;
        }
    }
    proof { assert(octets@.take(i as int) =~= octets@); }
    Some(acc)
}

/// RFC 4055 §5: the `DigestInfo` selector of each sha*WithRSAEncryption.
fn pkcs1_hash(hash: RsaPkcs1v15Hash) -> (out: HashId)
    ensures out == crate::chain::spec::pkcs1_hash(clazel_x509::signature_algorithm::exec::view_hash(hash)),
{
    match hash {
        RsaPkcs1v15Hash::Sha256 => HashId::Sha256,
        RsaPkcs1v15Hash::Sha384 => HashId::Sha384,
        RsaPkcs1v15Hash::Sha512 => HashId::Sha512,
    }
}

/// RFC 8017 §9.2 step 1: the digest of the signed octets (libcrux).
fn rsa_digest(hash: RsaPkcs1v15Hash, message: &[u8]) -> (out: Vec<u8>)
    ensures out@ == crate::chain::spec::rsa_digest(clazel_x509::signature_algorithm::exec::view_hash(hash), message@),
{
    match hash {
        RsaPkcs1v15Hash::Sha256 => axioms::sha256(message),
        RsaPkcs1v15Hash::Sha384 => axioms::sha384(message),
        RsaPkcs1v15Hash::Sha512 => axioms::sha512(message),
    }
}

/// RFC 8017 §8.2.2 under an rsaEncryption key, with the exponent profile.
fn rsa_pkcs1_link(key: &RsaPublicKey, hash: RsaPkcs1v15Hash, message: &[u8], signature: &[u8])
    -> (out: bool)
    ensures out == crate::chain::spec::rsa_pkcs1_link(key@,
        clazel_x509::signature_algorithm::exec::view_hash(hash), message@, signature@),
{
    let e = match exponent_value(key.public_exponent_octets) {
        Some(e) => e,
        None => return false,
    };
    if e % 2 != 1 {
        return false;
    }
    let digest = rsa_digest(hash, message);
    clazel_pkcs1::verify::verify(key.modulus_octets, e, digest.as_slice(), pkcs1_hash(hash), signature)
}

/// ecdsa-with-SHA384 under a secp256r1 key.
fn ecdsa_p256_sha384(spki: &SubjectPublicKeyInfo, message: &[u8], signature: &[u8]) -> (out: bool)
    requires clazel_x509::spki::lemmas::ec_lengths_ok(spki@),
    ensures out == crate::chain::spec::ecdsa_p256_sha384(spki@, message@, signature@),
{
    match (crate::signature::exec::p256_point(spki), crate::signature::exec::ecdsa_sig_value(signature)) {
        (Some(point), Some((r, s))) =>
            axioms::ecdsa_p256_sha384_verify(message, r.as_slice(), s.as_slice(), point),
        _ => false,
    }
}

/// The octet at `i` of `v`, or 0 past its end.
fn octet(v: &[u8], i: usize) -> (b: u8)
    ensures i < v.len() ==> b == v@[i as int],
{
    match v.get(i) {
        Some(b) => *b,
        None => 0,
    }
}

/// `m` left-padded with zeros to 48 octets ([`crate::chain::spec::pad48`]),
/// as the array `clazel_p384::verify::verify` takes.
fn pad48(m: &[u8]) -> (out: [u8; 48])
    requires m.len() <= 48,
    ensures out@ == crate::chain::spec::pad48(m@),
{
    // m.len() <= 48, so this is exact.
    let zeros = 48usize.saturating_sub(m.len());
    let mut v: Vec<u8> = Vec::new();
    let mut k: usize = 0;
    while k < zeros
        invariant k <= zeros, zeros == 48 - m.len(), v@ =~= Seq::new(k as nat, |i: int| 0u8),
        decreases zeros - k,
    {
        v.push(0);
        // k < zeros <= 48, so this is exact.
        k = k.saturating_add(1);
    }
    v.extend_from_slice(m);
    proof { assert(v@ =~= crate::chain::spec::pad48(m@)); }
    let vs = v.as_slice();
    let o = [
        octet(vs, 0), octet(vs, 1), octet(vs, 2), octet(vs, 3), octet(vs, 4), octet(vs, 5),
        octet(vs, 6), octet(vs, 7), octet(vs, 8), octet(vs, 9), octet(vs, 10), octet(vs, 11),
        octet(vs, 12), octet(vs, 13), octet(vs, 14), octet(vs, 15), octet(vs, 16), octet(vs, 17),
        octet(vs, 18), octet(vs, 19), octet(vs, 20), octet(vs, 21), octet(vs, 22), octet(vs, 23),
        octet(vs, 24), octet(vs, 25), octet(vs, 26), octet(vs, 27), octet(vs, 28), octet(vs, 29),
        octet(vs, 30), octet(vs, 31), octet(vs, 32), octet(vs, 33), octet(vs, 34), octet(vs, 35),
        octet(vs, 36), octet(vs, 37), octet(vs, 38), octet(vs, 39), octet(vs, 40), octet(vs, 41),
        octet(vs, 42), octet(vs, 43), octet(vs, 44), octet(vs, 45), octet(vs, 46), octet(vs, 47),
    ];
    proof { assert(o@ =~= v@); }
    o
}

/// RFC 3279 §2.2.3 for P-384: r and s of one DER Ecdsa-Sig-Value, padded
/// to 48 ([`crate::chain::spec::ecdsa_sig_value_p384`]).
fn ecdsa_sig_value_p384(signature: &[u8]) -> (out: Option<([u8; 48], [u8; 48])>)
    ensures
        match out {
            Some((r, s)) => crate::chain::spec::ecdsa_sig_value_p384(signature@) == Some((r@, s@)),
            None => crate::chain::spec::ecdsa_sig_value_p384(signature@) is None,
        },
{
    let (cs, ce) = der::expect_sequence(signature, 0, signature.len())?;
    if ce != signature.len() {
        return None;
    }
    let (r_negative, rs, re, after_r) = der::read_integer(signature, cs, ce)?;
    // read_integer gives rs <= re and ss <= se, so these are exact.
    if r_negative || re.saturating_sub(rs) > 48 {
        return None;
    }
    let (s_negative, ss, se, after_s) = der::read_integer(signature, after_r, ce)?;
    if s_negative || se.saturating_sub(ss) > 48 || after_s != ce {
        return None;
    }
    let r = pad48(vstd::slice::slice_subrange(signature, rs, re));
    let s = pad48(vstd::slice::slice_subrange(signature, ss, se));
    Some((r, s))
}

/// FIPS 186-5 §6.4.2 step 2: the digest of the signed octets (libcrux).
fn ecdsa_digest(hash: EcdsaHash, message: &[u8]) -> (out: Vec<u8>)
    ensures
        out@ == crate::chain::spec::ecdsa_digest(clazel_x509::signature_algorithm::exec::view_ecdsa_hash(hash), message@),
        out.len() <= 64,
{
    match hash {
        EcdsaHash::Sha256 => axioms::sha256(message),
        EcdsaHash::Sha384 => axioms::sha384(message),
    }
}

/// ecdsa-with-SHA256 or ecdsa-with-SHA384 under a secp384r1 key whose
/// ECPoint is `point` (design P17): FIPS 186-5 §6.4.2 by `clazel_p384`.
pub(crate) fn ecdsa_p384_link(point: &[u8], hash: EcdsaHash, message: &[u8], signature: &[u8]) -> (out: bool)
    ensures out == crate::chain::spec::ecdsa_p384_link(point@,
        clazel_x509::signature_algorithm::exec::view_ecdsa_hash(hash), message@, signature@),
{
    match ecdsa_sig_value_p384(signature) {
        Some((r, s)) => {
            let digest = ecdsa_digest(hash, message);
            clazel_p384::verify::verify(digest.as_slice(), &r, &s, point)
        },
        None => false,
    }
}

/// §6.1.3 (a)(1) for a parsed issuer key.
fn link_with_key(spki: &SubjectPublicKeyInfo, algorithm: &AlgorithmIdentifier, tbs_der: &[u8],
    signature: &[u8]) -> (out: bool)
    requires clazel_x509::spki::lemmas::ec_lengths_ok(spki@),
    ensures out == crate::chain::spec::link_with_key(spki@,
        clazel_x509::certificate::contract::view_algorithm_identifier(algorithm), tbs_der@, signature@),
{
    match clazel_x509::signature_algorithm::exec::classify(algorithm) {
        Some(AlgorithmClass::Supported(hash)) => match &spki.public_key {
            PublicKey::Rsa(key) => rsa_pkcs1_link(key, hash, tbs_der, signature),
            _ => false,
        },
        Some(AlgorithmClass::Ecdsa(hash)) if matches!(spki.public_key, PublicKey::EcP384(_)) =>
            match &spki.public_key {
                PublicKey::EcP384(point) => ecdsa_p384_link(point, hash, tbs_der, signature),
                _ => false,
            },
        Some(AlgorithmClass::Ecdsa(EcdsaHash::Sha256)) =>
            crate::signature::exec::ecdsa_p256_sha256(spki, tbs_der, signature),
        Some(AlgorithmClass::Ecdsa(EcdsaHash::Sha384)) => ecdsa_p256_sha384(spki, tbs_der, signature),
        Some(AlgorithmClass::Unsupported) => false,
        None => false,
    }
}

/// §6.1.3 (a)(1): whether `signature` over `tbs_der` verifies with
/// `algorithm` under the issuer's SubjectPublicKeyInfo DER `issuer_spki`.
pub fn link(issuer_spki: &[u8], algorithm: &AlgorithmIdentifier, tbs_der: &[u8], signature: &[u8])
    -> (out: bool)
    ensures out == crate::chain::spec::link(clazel_x509::path::spec::SignedData {
        issuer_spki: issuer_spki@,
        algorithm: clazel_x509::certificate::contract::view_algorithm_identifier(algorithm),
        tbs_der: tbs_der@,
        signature: signature@,
    }),
{
    match clazel_x509::spki::exec::parse_subject_public_key_info(issuer_spki) {
        None => false,
        Some(spki) => {
            proof { clazel_x509::spki::lemmas::lemma_parse_ec_lengths(issuer_spki@, spki@); }
            link_with_key(&spki, algorithm, tbs_der, signature)
        },
    }
}

/// The production link verifier (design §3.3): [`crate::chain::spec::production_link`].
pub struct CertificateLinks;

impl clazel_x509::path::contract::LinkVerifier for CertificateLinks {
    open spec fn link(&self) -> clazel_x509::path::spec::LinkFn {
        crate::chain::spec::production_link()
    }

    fn verify(&self, issuer_spki: &[u8], algorithm: &AlgorithmIdentifier<'_>, tbs_der: &[u8],
        signature: &[u8]) -> (out: bool)
    {
        link(issuer_spki, algorithm, tbs_der, signature)
    }
}

} // verus!
