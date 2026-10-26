//! RFC 5280 §4.1.2.7 SubjectPublicKeyInfo and the initial RSA key profile.
//! <https://www.rfc-editor.org/rfc/rfc5280.html#section-4.1.2.7>
//! <https://www.rfc-editor.org/rfc/rfc3279.html#section-2.3.1>
//! <https://www.rfc-editor.org/rfc/rfc8017.html#appendix-A.1.1>
//!
//! Modelling choices and limits:
//! - The entire input is exactly one DER SubjectPublicKeyInfo SEQUENCE. Its
//!   AlgorithmIdentifier and subjectPublicKey BIT STRING TLVs, key bytes, and
//!   full outer SPKI TLV are retained exactly.
//! - rsaEncryption (1.2.840.113549.1.1.1) is the only initially supported
//!   profile. RFC 3279 §2.3.1 requires AlgorithmIdentifier parameters to be
//!   ASN.1 NULL; omission or another parameter encoding is rejected.
//! - RSA's BIT STRING must have zero unused bits. Its contents must be one
//!   complete DER RSAPublicKey SEQUENCE with exactly two canonical INTEGERs.
//!   Modulus and exponent must be positive and nonzero, as in RFC 8017 §3.1.
//! - This is syntax/profile decoding, not RSA key validation: primality,
//!   modulus structure, exponent range/GCD, minimum-strength policy, and
//!   signatures are not checked. Integer values remain borrowed octets; no
//!   big integers are allocated. No arbitrary key-size cap is imposed here.
//! - All other well-framed algorithm identifiers are returned explicitly as
//!   Unsupported with their BIT STRING unused-bit count and key bytes intact.
//!   Their algorithm-specific parameters and key syntax remain opaque.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Initial supported/unsupported SubjectPublicKeyInfo key classification.
pub enum PublicKey {
    /// RSA public key syntax from RFC 3279 §2.3.1.
    Rsa(RsaPublicKey),
    /// Algorithm OID is outside the implemented key profile.
    Unsupported,
}

/// Borrowed RSA public-key representation; integer values omit DER sign padding.
pub struct RsaPublicKey {
    /// Complete original RSAPublicKey SEQUENCE TLV.
    pub encoded_der: Seq<u8>,
    /// Complete DER INTEGER TLV encoding modulus n.
    pub modulus_der: Seq<u8>,
    /// Positive big-endian modulus octets, excluding any required DER sign pad.
    pub modulus_octets: Seq<u8>,
    /// Complete DER INTEGER TLV encoding public exponent e.
    pub public_exponent_der: Seq<u8>,
    /// Positive big-endian exponent octets, excluding any required DER sign pad.
    pub public_exponent_octets: Seq<u8>,
}

/// Parsed SubjectPublicKeyInfo with exact original encodings retained.
pub struct SubjectPublicKeyInfo {
    /// RFC 5280 AlgorithmIdentifier, including opaque optional parameters.
    pub algorithm: crate::certificate::spec::AlgorithmIdentifier,
    /// Supported RSA syntax, or explicit unsupported-algorithm classification.
    pub public_key: PublicKey,
    /// BIT STRING unused-bit count (zero for the supported RSA profile).
    pub subject_public_key_unused_bits: u8,
    /// BIT STRING data octets, excluding its initial unused-bit count.
    pub subject_public_key_bits: Seq<u8>,
    /// Complete DER BIT STRING TLV, including its unused-bit count.
    pub subject_public_key_tlv: Seq<u8>,
    /// Complete original SubjectPublicKeyInfo SEQUENCE TLV.
    pub spki_der: Seq<u8>,
}

/// Whether the OID arcs designate rsaEncryption.
pub open spec fn is_rsa_encryption(oid: Seq<nat>) -> bool {
    oid =~= seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 1nat]
}

/// A DER INTEGER magnitude is positive and nonzero iff at least one of its
/// canonical magnitude octets is nonzero.
pub open spec fn positive_integer_value(bytes: Seq<u8>, start: nat, end: nat) -> bool {
    start < end && exists|i: int| start as int <= i < end as int && bytes[i] != 0
}

/// RFC 5280 §4.1.2.7: parse an exact SubjectPublicKeyInfo SEQUENCE.
pub open spec fn parse_subject_public_key_info(input: Seq<u8>) -> Option<SubjectPublicKeyInfo> {
    match clazel_der::spec::expect_sequence(input, 0, input.len()) {
        None => None,
        Some((outer_start, outer_end)) => match clazel_der::spec::read_tlv(input, 0, input.len()) {
            Some(outer) if outer.cstart == outer_start && outer.cend == outer_end && outer.cend == input.len() =>
                match crate::certificate::spec::parse_algorithm_identifier(input, outer.cstart, outer.cend) {
                    None => None,
                    Some((algorithm, after_algorithm)) => match clazel_der::spec::read_bit_string(input, after_algorithm, outer.cend) {
                        Some((unused, bits_start, bits_end, after_bits)) if after_bits == outer.cend => {
                            let key_bits = input.subrange(bits_start as int, bits_end as int);
                            let bit_string_der = input.subrange(after_algorithm as int, after_bits as int);
                            if is_rsa_encryption(algorithm.oid) {
                                if algorithm.parameters_der != Some(seq![0x05u8, 0x00u8]) || unused != 0 { None }
                                else { match parse_rsa_public_key(key_bits) {
                                    Some(rsa) => Some(SubjectPublicKeyInfo {
                                        algorithm, public_key: PublicKey::Rsa(rsa),
                                        subject_public_key_unused_bits: unused,
                                        subject_public_key_bits: key_bits,
                                        subject_public_key_tlv: bit_string_der,
                                        spki_der: input,
                                    }),
                                    None => None,
                                }}
                            } else {
                                Some(SubjectPublicKeyInfo {
                                    algorithm, public_key: PublicKey::Unsupported,
                                    subject_public_key_unused_bits: unused,
                                    subject_public_key_bits: key_bits,
                                    subject_public_key_tlv: bit_string_der,
                                    spki_der: input,
                                })
                            }
                        },
                        _ => None,
                    },
                },
            _ => None,
        },
    }
}

/// RFC 3279 §2.3.1 and RFC 8017 Appendix A.1.1: parse the exact two-INTEGER
/// RSAPublicKey DER value carried inside the subjectPublicKey BIT STRING.
pub open spec fn parse_rsa_public_key(input: Seq<u8>) -> Option<RsaPublicKey> {
    match clazel_der::spec::expect_sequence(input, 0, input.len()) {
        None => None,
        Some((start, end)) => match clazel_der::spec::read_tlv(input, 0, input.len()) {
            Some(outer) if outer.cstart == start && outer.cend == end && end == input.len() =>
                match clazel_der::spec::read_integer(input, start, end) {
                    Some((false, modulus_start, modulus_end, after_modulus))
                        if positive_integer_value(input, modulus_start, modulus_end) =>
                        match clazel_der::spec::read_tlv(input, start, end) {
                            Some(modulus) => match clazel_der::spec::read_integer(input, after_modulus, end) {
                                Some((false, exponent_start, exponent_end, after_exponent))
                                    if after_exponent == end && positive_integer_value(input, exponent_start, exponent_end) =>
                                    match clazel_der::spec::read_tlv(input, after_modulus, end) {
                                        Some(exponent) if exponent.cend == end => Some(RsaPublicKey {
                                            encoded_der: input,
                                            modulus_der: input.subrange(start as int, modulus.cend as int),
                                            modulus_octets: input.subrange(modulus_start as int, modulus_end as int),
                                            public_exponent_der: input.subrange(after_modulus as int, exponent.cend as int),
                                            public_exponent_octets: input.subrange(exponent_start as int, exponent_end as int),
                                        }),
                                        _ => None,
                                    },
                                _ => None,
                            },
                            None => None,
                        },
                    _ => None,
                },
            _ => None,
        },
    }
}

} // verus!
