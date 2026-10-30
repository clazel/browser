//! RFC 5280 §4.1.2.7 SubjectPublicKeyInfo and the initial RSA key profile.
//! <https://www.rfc-editor.org/rfc/rfc5280.html#section-4.1.2.7>
//! <https://www.rfc-editor.org/rfc/rfc3279.html#section-2.3.1>
//! <https://www.rfc-editor.org/rfc/rfc8017.html#appendix-A.1.1>
//! <https://www.rfc-editor.org/rfc/rfc5480.html#section-2>
//!
//! Modelling choices and limits:
//! - The entire input is exactly one DER SubjectPublicKeyInfo SEQUENCE. Its
//!   AlgorithmIdentifier and subjectPublicKey BIT STRING TLVs, key bytes, and
//!   full outer SPKI TLV are retained exactly.
//! - rsaEncryption (1.2.840.113549.1.1.1) is the only supported RSA
//!   profile. RFC 3279 §2.3.1 requires AlgorithmIdentifier parameters to be
//!   ASN.1 NULL; omission or another parameter encoding is rejected.
//! - RSA's BIT STRING must have zero unused bits. Its contents must be one
//!   complete DER RSAPublicKey SEQUENCE with exactly two canonical INTEGERs.
//!   Modulus and exponent must be positive and nonzero, as in RFC 8017 §3.1.
//! - This is syntax/profile decoding, not RSA key validation: primality,
//!   modulus structure, exponent range/GCD, minimum-strength policy, and
//!   signatures are not checked. Integer values remain borrowed octets; no
//!   big integers are allocated. No arbitrary key-size cap is imposed here.
//! - EC keys (RFC 5480 §2.1.1): id-ecPublicKey (1.2.840.10045.2.1) whose
//!   parameters are exactly the DER OBJECT IDENTIFIER of namedCurve
//!   secp256r1 (1.2.840.10045.3.1.7) or secp384r1 (1.3.132.0.34) are
//!   classified by `classify_ec_public_key`. The parameters field is compared
//!   as the complete DER TLV, so explicit ECParameters, `implicitCurve`,
//!   absent parameters and every other named curve are not classified.
//! - The EC point is RFC 5480 §2.2's ECPoint, the BIT STRING's value, which
//!   must have no unused bits. Only the uncompressed form (leading octet
//!   0x04, SEC 1 §2.3.3) of exactly the curve's length is classified: 65
//!   octets for secp256r1, 97 for secp384r1. Compressed points (RFC 5480
//!   §2.2 makes them optional to support) and any other length are not.
//!   Whether the point is on the curve is not checked here.
//! - The two EC classes carry different values, on purpose. `EcP256` holds
//!   X || Y, the 64 octets after the 0x04 (the form libcrux takes).
//!   `EcP384` holds the complete 97-octet ECPoint, 0x04 included, so that
//!   `clazel-p384`'s point decoder, not this module, interprets it.
//! - An EC key that is not classified is not an error: like every other
//!   algorithm, the SPKI is returned as Unsupported with its unused-bit count
//!   and key bytes intact, so the set of inputs that parse is unchanged.
//!   RSA's classification is unchanged.
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
    /// id-ecPublicKey with namedCurve secp256r1 and an uncompressed point
    /// (RFC 5480 §2.1.1, §2.2): the 64 octets X || Y, without the 0x04.
    EcP256(Seq<u8>),
    /// id-ecPublicKey with namedCurve secp384r1 and an uncompressed point:
    /// the complete 97-octet ECPoint, 0x04 || X || Y.
    EcP384(Seq<u8>),
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

/// RFC 5480 §2.1.1: id-ecPublicKey, 1.2.840.10045.2.1.
pub open spec fn is_id_ec_public_key(oid: Seq<nat>) -> bool {
    oid =~= seq![1nat, 2nat, 840nat, 10045nat, 2nat, 1nat]
}

/// RFC 5480 §2.1.1.1: the DER of the namedCurve parameter secp256r1, OBJECT
/// IDENTIFIER 1.2.840.10045.3.1.7.
pub open spec fn secp256r1_parameter() -> Seq<u8> {
    seq![0x06u8, 0x08u8, 0x2au8, 0x86u8, 0x48u8, 0xceu8, 0x3du8, 0x03u8, 0x01u8, 0x07u8]
}

/// RFC 5480 §2.1.1.1: the DER of the namedCurve parameter secp384r1, OBJECT
/// IDENTIFIER 1.3.132.0.34.
pub open spec fn secp384r1_parameter() -> Seq<u8> {
    seq![0x06u8, 0x05u8, 0x2bu8, 0x81u8, 0x04u8, 0x00u8, 0x22u8]
}

/// RFC 5480 §2.1.1 and §2.2: classify a non-RSA key as an EC key on
/// secp256r1 or secp384r1 with an uncompressed point; anything else is
/// Unsupported.
pub open spec fn classify_ec_public_key(
    algorithm: crate::certificate::spec::AlgorithmIdentifier, unused: u8, bits: Seq<u8>,
) -> PublicKey {
    if is_id_ec_public_key(algorithm.oid) && unused == 0 && bits.len() > 0 && bits[0] == 0x04u8 {
        if algorithm.parameters_der == Some(secp256r1_parameter()) && bits.len() == 65 {
            PublicKey::EcP256(bits.subrange(1, 65))
        } else if algorithm.parameters_der == Some(secp384r1_parameter()) && bits.len() == 97 {
            PublicKey::EcP384(bits)
        } else {
            PublicKey::Unsupported
        }
    } else {
        PublicKey::Unsupported
    }
}

/// A DER INTEGER magnitude is positive and nonzero iff one octet in its
/// bounded magnitude range is nonzero. The recursion keeps concrete witness
/// evaluation quantifier-free.
pub open spec fn positive_integer_value(bytes: Seq<u8>, start: nat, end: nat) -> bool
    decreases end - start,
{
    if start >= end || end > bytes.len() {
        false
    } else {
        bytes[(end - 1) as int] != 0 || positive_integer_value(bytes, start, (end - 1) as nat)
    }
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
                                    algorithm,
                                    public_key: classify_ec_public_key(algorithm, unused, key_bits),
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
