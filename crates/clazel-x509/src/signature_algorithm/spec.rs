//! RFC 5280 certificate signature AlgorithmIdentifier profiles.
//! <https://www.rfc-editor.org/rfc/rfc5280.html#section-4.1.1.2>
//! <https://www.rfc-editor.org/rfc/rfc4055.html#section-5>
//! <https://www.rfc-editor.org/rfc/rfc8017.html#appendix-A.2.4>
//! <https://www.rfc-editor.org/rfc/rfc5758.html#section-3.2>
//!
//! Modelling choices and limits:
//! - Inputs are AlgorithmIdentifier values already decoded by the certificate
//!   envelope/TBSCertificate parsers; this module parses no DER itself.
//! - The supported profile set is SHA-256, SHA-384, and SHA-512 with
//!   RSASSA-PKCS1-v1_5, and ECDSA with SHA-256 and with SHA-384. Other OIDs
//!   (including RSASSA-PSS, ecdsa-with-SHA1 and ecdsa-with-SHA512) are
//!   explicitly Unsupported; PSS parameters and other algorithm-specific
//!   parameters are not interpreted here.
//! - RFC 5758 §3.2 says that for ecdsa-with-SHA256 and ecdsa-with-SHA384
//!   "the encoding MUST omit the parameters field". A known ECDSA OID with
//!   any parameters, NULL included, is therefore malformed (`classify` is
//!   `None`), as a known RSA OID with disallowed parameters is. Unlike RSA
//!   there is no "accept NULL" allowance, so absent is the only form.
//! - `Ecdsa(hash)` says only that the identifier is one of those two. Which
//!   curve the issuer key is on is the key's property (`spki`), not the
//!   signature identifier's, and is checked by the link verifier.
//! - RFC 4055 §5 requires NULL parameters for the three supported OIDs and
//!   also requires implementations to accept parameters absent. Both forms
//!   classify to the same profile. For matching those profiles, NULL and
//!   absent are treated as semantically equivalent. This is the profile-level
//!   interpretation of RFC 5280 §4.1.1.2's “same algorithm identifier”.
//! - For unsupported OIDs, this module cannot normalize algorithm-specific
//!   parameters, so the OID arcs and complete parameter TLV must match
//!   exactly. The original parsed identifiers remain in the output.
//! - A supported profile requires signatureValue's BIT STRING unused-bit
//!   count to be zero. Unsupported algorithms retain the count and bytes; no
//!   algorithm-specific validity is claimed for them.
//! - The parsed representation retains OID arcs and the complete optional
//!   parameter TLV. The existing certificate APIs do not retain the complete
//!   AlgorithmIdentifier SEQUENCE TLV.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// SHA-2 hash selection for supported RSASSA-PKCS1-v1_5 certificate signatures.
pub enum RsaPkcs1v15Hash {
    /// SHA-256.
    Sha256,
    /// SHA-384.
    Sha384,
    /// SHA-512.
    Sha512,
}

/// Hash selection for supported ECDSA certificate signatures (RFC 5758 §3.2).
pub enum EcdsaHash {
    /// ecdsa-with-SHA256.
    Sha256,
    /// ecdsa-with-SHA384.
    Sha384,
}

/// Result of checking one already-decoded signature AlgorithmIdentifier.
pub enum AlgorithmClass {
    /// One of the initially supported RSA PKCS #1 v1.5 profiles.
    Supported(RsaPkcs1v15Hash),
    /// ecdsa-with-SHA256 or ecdsa-with-SHA384, parameters absent.
    Ecdsa(EcdsaHash),
    /// Algorithm is outside this module's implemented profile.
    Unsupported,
}

/// Typed signature-verification inputs, without claiming the signature verifies.
pub struct PreparedSignature {
    /// Parsed TBSCertificate signature AlgorithmIdentifier, retained verbatim
    /// at the OID-arc and raw-parameter representation level.
    pub tbs_algorithm: crate::certificate::spec::AlgorithmIdentifier,
    /// Parsed outer Certificate signatureAlgorithm, retained likewise.
    pub outer_algorithm: crate::certificate::spec::AlgorithmIdentifier,
    /// Supported profile or explicit unsupported classification.
    pub class: AlgorithmClass,
    /// Exact DER encoding of the signed TBSCertificate.
    pub tbs_der: Seq<u8>,
    /// Signature BIT STRING data octets, excluding the unused-bit count octet.
    pub signature_bits: Seq<u8>,
    /// Number of unused low-order bits in the signature BIT STRING.
    pub signature_unused_bits: u8,
}

/// Whether parameters match the supported RSA PKCS #1 v1.5 profile.
pub open spec fn pkcs1_sha2_parameters(parameters: Option<Seq<u8>>) -> bool {
    parameters == None || parameters == Some(seq![0x05u8, 0x00u8])
}

/// RFC 4055 §5 OID for sha256WithRSAEncryption: { pkcs-1 11 }.
pub open spec fn is_sha256_with_rsa(oid: Seq<nat>) -> bool {
    oid =~= seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 11nat]
}

/// RFC 4055 §5 OID for sha384WithRSAEncryption: { pkcs-1 12 }.
pub open spec fn is_sha384_with_rsa(oid: Seq<nat>) -> bool {
    oid =~= seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 12nat]
}

/// RFC 4055 §5 OID for sha512WithRSAEncryption: { pkcs-1 13 }.
pub open spec fn is_sha512_with_rsa(oid: Seq<nat>) -> bool {
    oid =~= seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 13nat]
}

/// RFC 5758 §3.2: the parameters of an ECDSA signature AlgorithmIdentifier
/// "MUST" be omitted, so only an absent field is accepted.
pub open spec fn ecdsa_parameters(parameters: Option<Seq<u8>>) -> bool {
    parameters is None
}

/// RFC 5758 §3.2 OID for ecdsa-with-SHA256: { ecdsa-with-SHA2 2 }, i.e.
/// 1.2.840.10045.4.3.2.
pub open spec fn is_ecdsa_with_sha256(oid: Seq<nat>) -> bool {
    oid =~= seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat]
}

/// RFC 5758 §3.2 OID for ecdsa-with-SHA384: { ecdsa-with-SHA2 3 }, i.e.
/// 1.2.840.10045.4.3.3.
pub open spec fn is_ecdsa_with_sha384(oid: Seq<nat>) -> bool {
    oid =~= seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 3nat]
}

/// RFC 5280 §4.1.1.2, RFC 4055 §5 and RFC 5758 §3.2: classify supported RSA
/// SHA-2 and ECDSA SHA-256/384 signature IDs. Known OIDs with disallowed
/// parameters are malformed; unknown OIDs are explicit.
pub open spec fn classify(
    algorithm: crate::certificate::spec::AlgorithmIdentifier,
) -> Option<AlgorithmClass> {
    if is_sha256_with_rsa(algorithm.oid) {
        if pkcs1_sha2_parameters(algorithm.parameters_der) {
            Some(AlgorithmClass::Supported(RsaPkcs1v15Hash::Sha256))
        } else { None }
    } else if is_sha384_with_rsa(algorithm.oid) {
        if pkcs1_sha2_parameters(algorithm.parameters_der) {
            Some(AlgorithmClass::Supported(RsaPkcs1v15Hash::Sha384))
        } else { None }
    } else if is_sha512_with_rsa(algorithm.oid) {
        if pkcs1_sha2_parameters(algorithm.parameters_der) {
            Some(AlgorithmClass::Supported(RsaPkcs1v15Hash::Sha512))
        } else { None }
    } else if is_ecdsa_with_sha256(algorithm.oid) {
        if ecdsa_parameters(algorithm.parameters_der) {
            Some(AlgorithmClass::Ecdsa(EcdsaHash::Sha256))
        } else { None }
    } else if is_ecdsa_with_sha384(algorithm.oid) {
        if ecdsa_parameters(algorithm.parameters_der) {
            Some(AlgorithmClass::Ecdsa(EcdsaHash::Sha384))
        } else { None }
    } else {
        Some(AlgorithmClass::Unsupported)
    }
}

/// Whether two unsupported identifiers have the same parsed identifier value.
pub open spec fn unsupported_identifiers_equal(
    first: crate::certificate::spec::AlgorithmIdentifier,
    second: crate::certificate::spec::AlgorithmIdentifier,
) -> bool {
    first.oid =~= second.oid && first.parameters_der == second.parameters_der
}

/// RFC 5280 §4.1.1.2/.3: prepare signature inputs only when TBS and outer
/// AlgorithmIdentifiers match and supported (RSA or ECDSA) signatures are
/// octet-aligned.
pub open spec fn prepare_signature(
    tbs_algorithm: crate::certificate::spec::AlgorithmIdentifier,
    outer_algorithm: crate::certificate::spec::AlgorithmIdentifier,
    tbs_der: Seq<u8>,
    signature_bits: Seq<u8>,
    signature_unused_bits: u8,
) -> Option<PreparedSignature> {
    match (classify(tbs_algorithm), classify(outer_algorithm)) {
        (Some(AlgorithmClass::Supported(tbs_hash)), Some(AlgorithmClass::Supported(outer_hash)))
            if tbs_hash == outer_hash && signature_unused_bits == 0 =>
            Some(PreparedSignature {
                tbs_algorithm, outer_algorithm,
                class: AlgorithmClass::Supported(tbs_hash),
                tbs_der, signature_bits, signature_unused_bits,
            }),
        (Some(AlgorithmClass::Ecdsa(tbs_hash)), Some(AlgorithmClass::Ecdsa(outer_hash)))
            if tbs_hash == outer_hash && 0 == signature_unused_bits =>
            Some(PreparedSignature {
                tbs_algorithm, outer_algorithm,
                class: AlgorithmClass::Ecdsa(tbs_hash),
                tbs_der, signature_bits, signature_unused_bits,
            }),
        (Some(AlgorithmClass::Unsupported), Some(AlgorithmClass::Unsupported))
            if unsupported_identifiers_equal(tbs_algorithm, outer_algorithm) =>
            Some(PreparedSignature {
                tbs_algorithm, outer_algorithm,
                class: AlgorithmClass::Unsupported,
                tbs_der, signature_bits, signature_unused_bits,
            }),
        _ => None,
    }
}

} // verus!
