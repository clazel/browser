//! RFC 5280 §6.1.3 (a)(1) for the production verifier: "The signature on
//! the certificate can be verified using working_public_key_algorithm, the
//! working_public_key, and the working_public_key_parameters." This is the
//! `LinkFn` that `clazel_x509::path` takes as a parameter (`path::spec`'s
//! `SignedData`, design §3.3), for the link profile of design §1.11.
//!
//! Sources, by step:
//! - RFC 5280 §4.1.1.2 (signatureAlgorithm), §4.1.1.3 (signatureValue, "the
//!   digital signature computed upon the ASN.1 DER encoded tbsCertificate")
//!   and §4.1.2.7 (subjectPublicKeyInfo),
//!   <https://www.rfc-editor.org/rfc/rfc5280#section-4.1.1.2>. The
//!   AlgorithmIdentifier is classified by
//!   `clazel_x509::signature_algorithm::spec::classify`, the key by
//!   `clazel_x509::spki::spec::parse_subject_public_key_info`.
//! - RFC 4055 §5 (sha256/384/512WithRSAEncryption, NULL or absent
//!   parameters) and RFC 3279 §2.3.1 (rsaEncryption keys),
//!   <https://www.rfc-editor.org/rfc/rfc4055#section-5>; RFC 8017 §8.2.2
//!   RSASSA-PKCS1-V1_5-VERIFY and §9.2 EMSA-PKCS1-v1_5,
//!   <https://www.rfc-editor.org/rfc/rfc8017#section-8.2.2>, as transcribed
//!   by `clazel_pkcs1::spec::rsassa_pkcs1_v1_5_verify`; FIPS 180-4 §6.2,
//!   §6.4, §6.5 for the digests (`crate::spec::sha256`, `sha384`, `sha512`).
//! - RFC 5758 §3.2 (ecdsa-with-SHA256 and ecdsa-with-SHA384, "the encoding
//!   MUST omit the parameters field"),
//!   <https://www.rfc-editor.org/rfc/rfc5758#section-3.2>; RFC 5480 §2.1.1
//!   and §2.2 (secp256r1 keys, the ECPoint); RFC 3279 §2.2.3
//!   (Ecdsa-Sig-Value); FIPS 186-5 §6.4.2 (verification, which libcrux
//!   performs: `crate::signature::spec::ecdsa_p256_sha256_verify` and
//!   `ecdsa_p256_sha384_verify`).
//! - Browser behaviour, for the refusals marked (R): Chromium
//!   `net/cert/cert_verify_proc.cc` (`IsWeakKey`: an RSA key below 1024 bits
//!   is weak) and BoringSSL `crypto/fipsmodule/rsa/rsa_impl.cc.inc`
//!   (`rsa_check_public_key`: e odd, at least 2 bits, `kMaxExponentBits =
//!   33`); Firefox `security/certverifier/CertVerifier.cpp` (`MIN_RSA_BITS =
//!   2048`; a chain to a built-in root with a smaller key is
//!   `ERROR_INADEQUATE_KEY_SIZE`); and webpki 0.103.16 over ring 0.17.14
//!   (`RSA_PKCS1_2048_8192_*`; `rsa/public_modulus.rs` compares the bit
//!   length rounded up to whole octets with 2048, and the exact bit length
//!   with 8192). All read 2026-10-29.
//!
//! Modelling choices. **(R)** marks a refusal RFC 5280 does not require,
//! **(=)** a change of form whose outcome is the RFC's. Every (R) follows
//! "do what Chrome and Firefox do", the stricter where they differ.
//! - **(=) The key is parsed here, whole.** `SignedData.issuer_spki` is the
//!   complete SubjectPublicKeyInfo DER (`path::spec`'s `working_public_key`,
//!   §6.1.2 (g) to (i) folded into one field). A key that does not parse
//!   verifies nothing. The algorithm of the key must be the one the
//!   signature algorithm names: an RSA signature under an EC key, or an
//!   ECDSA signature under an RSA key, is `false`.
//! - **(=) The signature algorithm is the TBS copy** (`path::spec`'s
//!   `signed_data`), which `prepare_signature` has checked equal to the
//!   outer one (§4.1.1.2) with no unused bits in the signature BIT STRING.
//!   It is classified again here, so this function is meaningful on its own.
//! - **RSA PKCS#1 v1.5** (sha256/384/512WithRSAEncryption): the digest of
//!   the exact `tbs_der` octets with the class's SHA-2 function (libcrux,
//!   `crate::axioms`), then `clazel_pkcs1`'s RSASSA-PKCS1-V1_5-VERIFY with
//!   the matching `DigestInfo` (RFC 8017 §9.2 Note 1). The modulus and
//!   exponent are the key's INTEGER magnitudes as numbers (RFC 8017 §4.2
//!   OS2IP).
//!   - **(R) The modulus has 2048 to 8192 bits**, `clazel_pkcs1`'s domain
//!     (`modulus_in_range`). The lower bound is Firefox's (`MIN_RSA_BITS`;
//!     Chrome's is 1024, so Firefox is the stricter; webpki's ring accepts
//!     2041 to 2047 bits, which round up to 256 octets). The upper bound is
//!     webpki's; Chrome and Firefox accept larger keys, which are refused
//!     here.
//!   - **Modulus sizes that are not a multiple of 8 bits are accepted**, as
//!     Chrome, Firefox and webpki accept them. CA/B Forum BR §6.1.5 requires
//!     a multiple of 8; limbo's `webpki::forbidden-rsa-*-not-divisible-by-8`
//!     cases (FAILURE) are therefore divergences.
//!   - **(R) The public exponent is odd and below 2^33** (`exponent_profile`),
//!     BoringSSL's `rsa_check_public_key`, which Chrome verifies with
//!     (ring's rule is the same). With `clazel_pkcs1`'s `exponent_in_range`
//!     (at least 3) that is e odd in 3 ..= 2^33 - 1.
//! - **ECDSA** (ecdsa-with-SHA256, ecdsa-with-SHA384, parameters absent by
//!   RFC 5758 §3.2): only an issuer key on secp256r1, classified by
//!   `clazel_x509::spki` as `EcP256` (namedCurve only, uncompressed point
//!   only) and read by `crate::signature::spec::p256_point`. The signature
//!   is one DER Ecdsa-Sig-Value read by `crate::signature::spec::ecdsa_sig_value`
//!   (the CertificateVerify decoder, shared). libcrux checks that the point
//!   is on the curve and that 1 <= r, s < n, and hashes `tbs_der` itself.
//!   - **(R) Compressed points are refused** (Firefox's mozilla::pkix
//!     accepts only the uncompressed form; RFC 5480 §2.2 makes the
//!     compressed form optional).
//!   - **(R) A secp384r1 issuer key (`EcP384`) is refused**, under either
//!     hash, until design P17 adds `clazel-p384` here; Chrome and Firefox
//!     accept it. Every chain through a P-384 CA (Let's Encrypt E5 to E9,
//!     35 of the 118 Mozilla roots) fails until then.
//!   - **(=) ecdsa-with-SHA384 under a P-256 key is accepted**, as RFC
//!     5758 §3.2 allows and both browsers do. It is listed because RFC 8446
//!     §4.2.3 does not allow the pair for CertificateVerify, so
//!     `crate::signature` has no scheme for it. FIPS 186-5 §6.4.2 uses the
//!     hash's leftmost 256 bits (libcrux reads the first 32 digest octets).
//! - **(R) Everything else is `false`**: RSASSA-PSS, Ed25519, Ed448, DSA,
//!   SHA-1 and MD5 with any key, ecdsa-with-SHA512, and every other curve
//!   (P-521, brainpool). `classify` calls those algorithms `Unsupported`,
//!   which `path::spec` refuses before asking `link`; this function refuses
//!   them too, so the refusal does not depend on the order.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// RSA PKCS#1 v1.5 (RFC 4055 §5, RFC 8017 §8.2.2)
// ---------------------------------------------------------------------------

/// RFC 4055 §5: the hash function of each sha*WithRSAEncryption, as the
/// `DigestInfo` selector of RFC 8017 §9.2 Note 1.
pub open spec fn pkcs1_hash(hash: clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash)
    -> clazel_pkcs1::spec::HashId
{
    match hash {
        clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha256 => clazel_pkcs1::spec::HashId::Sha256,
        clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha384 => clazel_pkcs1::spec::HashId::Sha384,
        clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha512 => clazel_pkcs1::spec::HashId::Sha512,
    }
}

/// RFC 8017 §9.2 step 1, "Apply the hash function to the message M": the
/// digest of the signed octets with the class's SHA-2 function (libcrux).
pub open spec fn rsa_digest(hash: clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash,
    message: Seq<u8>) -> Seq<u8>
{
    match hash {
        clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha256 => crate::spec::sha256(message),
        clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha384 => crate::spec::sha384(message),
        clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha512 => crate::spec::sha512(message),
    }
}

/// (R) BoringSSL `rsa_check_public_key` (Chrome): the public exponent is
/// odd and has at most 33 bits.
pub open spec fn exponent_profile(e: nat) -> bool {
    e % 2 == 1 && e < 0x2_0000_0000nat
}

/// RFC 8017 §8.2.2 RSASSA-PKCS1-V1_5-VERIFY ((n, e), M, S) with M the
/// signed octets `message`, under the rsaEncryption key `key`.
pub open spec fn rsa_pkcs1_link(key: clazel_x509::spki::spec::RsaPublicKey,
    hash: clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash, message: Seq<u8>,
    signature: Seq<u8>) -> bool
{
    // RFC 8017 §4.2 OS2IP of the key's INTEGER magnitudes (RFC 3279 §2.3.1).
    let n = clazel_pkcs1::spec::os2ip(key.modulus_octets);
    let e = clazel_pkcs1::spec::os2ip(key.public_exponent_octets);
    exponent_profile(e)
        && clazel_pkcs1::spec::rsassa_pkcs1_v1_5_verify(n, e, rsa_digest(hash, message),
            pkcs1_hash(hash), signature)
}

// ---------------------------------------------------------------------------
// ECDSA P-256 (RFC 5758 §3.2, RFC 5480 §2.1.1)
// ---------------------------------------------------------------------------

/// ecdsa-with-SHA384 under a secp256r1 key: the point, then r and s, then
/// libcrux's verification (FIPS 186-5 §6.4.2). The SHA-256 case is
/// `crate::signature::spec::ecdsa_p256_sha256`, shared with CertificateVerify.
pub open spec fn ecdsa_p256_sha384(spki: clazel_x509::spki::spec::SubjectPublicKeyInfo,
    message: Seq<u8>, signature: Seq<u8>) -> bool
{
    match (crate::signature::spec::p256_point(spki), crate::signature::spec::ecdsa_sig_value(signature)) {
        (Some(point), Some((r, s))) =>
            crate::signature::spec::ecdsa_p256_sha384_verify(message, r, s, point),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// §6.1.3 (a)(1)
// ---------------------------------------------------------------------------

/// §6.1.3 (a)(1) for an issuer key already parsed (`spki`): whether
/// `signature` over `tbs_der` verifies with `algorithm` under it.
pub open spec fn link_with_key(spki: clazel_x509::spki::spec::SubjectPublicKeyInfo,
    algorithm: clazel_x509::certificate::spec::AlgorithmIdentifier, tbs_der: Seq<u8>,
    signature: Seq<u8>) -> bool
{
    // §4.1.1.2: which algorithm signed the certificate.
    match clazel_x509::signature_algorithm::spec::classify(algorithm) {
        // RFC 4055 §5: RSASSA-PKCS1-v1_5 with SHA-2, under an rsaEncryption key.
        Some(clazel_x509::signature_algorithm::spec::AlgorithmClass::Supported(hash)) =>
            match spki.public_key {
                clazel_x509::spki::spec::PublicKey::Rsa(key) => rsa_pkcs1_link(key, hash, tbs_der, signature),
                _ => false,
            },
        // RFC 5758 §3.2: ecdsa-with-SHA256 under a secp256r1 key.
        Some(clazel_x509::signature_algorithm::spec::AlgorithmClass::Ecdsa(
            clazel_x509::signature_algorithm::spec::EcdsaHash::Sha256)) =>
            crate::signature::spec::ecdsa_p256_sha256(spki, tbs_der, signature),
        // RFC 5758 §3.2: ecdsa-with-SHA384 under a secp256r1 key.
        Some(clazel_x509::signature_algorithm::spec::AlgorithmClass::Ecdsa(
            clazel_x509::signature_algorithm::spec::EcdsaHash::Sha384)) =>
            ecdsa_p256_sha384(spki, tbs_der, signature),
        // (R) RSASSA-PSS, Ed25519, SHA-1, ... (header).
        Some(clazel_x509::signature_algorithm::spec::AlgorithmClass::Unsupported) => false,
        // A known OID with disallowed parameters.
        None => false,
    }
}

/// §6.1.3 (a)(1): whether the certificate's signature verifies under the
/// working public key (the issuer's complete SubjectPublicKeyInfo DER).
pub open spec fn link(d: clazel_x509::path::spec::SignedData) -> bool {
    match clazel_x509::spki::spec::parse_subject_public_key_info(d.issuer_spki) {
        None => false,
        Some(spki) => link_with_key(spki, d.algorithm, d.tbs_der, d.signature),
    }
}

/// The production `LinkFn` (design §3.3).
pub open spec fn production_link() -> clazel_x509::path::spec::LinkFn {
    |d: clazel_x509::path::spec::SignedData| link(d)
}

} // verus!
