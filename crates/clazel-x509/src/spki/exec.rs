//! Executable RFC 5280 §4.1.2.7 SubjectPublicKeyInfo decoder.

use crate::certificate::exec::AlgorithmIdentifier;
use clazel_der::decode as der;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// RFC 3279 rsaEncryption OID 1.2.840.113549.1.1.1.
fn is_rsa_oid(oid: &[u64]) -> (result: bool)
    ensures result == super::spec::is_rsa_encryption(der::nats(oid@))
{
    oid.len() == 7
        && oid.first() == Some(&1)
        && oid.get(1) == Some(&2)
        && oid.get(2) == Some(&840)
        && oid.get(3) == Some(&113549)
        && oid.get(4) == Some(&1)
        && oid.get(5) == Some(&1)
        && oid.get(6) == Some(&1)
}

/// RFC 5480 §2.1.1 id-ecPublicKey OID 1.2.840.10045.2.1.
fn is_id_ec_oid(oid: &[u64]) -> (result: bool)
    ensures result == super::spec::is_id_ec_public_key(der::nats(oid@))
{
    oid.len() == 6
        && oid.first() == Some(&1)
        && oid.get(1) == Some(&2)
        && oid.get(2) == Some(&840)
        && oid.get(3) == Some(&10045)
        && oid.get(4) == Some(&2)
        && oid.get(5) == Some(&1)
}

/// RFC 5480 §2.1.1.1: the namedCurve parameter secp256r1, 1.2.840.10045.3.1.7.
fn is_secp256r1_parameter(p: &[u8]) -> (result: bool)
    ensures result == (p@ =~= super::spec::secp256r1_parameter())
{
    p.len() == 10
        && p.first() == Some(&0x06)
        && p.get(1) == Some(&0x08)
        && p.get(2) == Some(&0x2a)
        && p.get(3) == Some(&0x86)
        && p.get(4) == Some(&0x48)
        && p.get(5) == Some(&0xce)
        && p.get(6) == Some(&0x3d)
        && p.get(7) == Some(&0x03)
        && p.get(8) == Some(&0x01)
        && p.get(9) == Some(&0x07)
}

/// RFC 5480 §2.1.1.1: the namedCurve parameter secp384r1, 1.3.132.0.34.
fn is_secp384r1_parameter(p: &[u8]) -> (result: bool)
    ensures result == (p@ =~= super::spec::secp384r1_parameter())
{
    p.len() == 7
        && p.first() == Some(&0x06)
        && p.get(1) == Some(&0x05)
        && p.get(2) == Some(&0x2b)
        && p.get(3) == Some(&0x81)
        && p.get(4) == Some(&0x04)
        && p.get(5) == Some(&0x00)
        && p.get(6) == Some(&0x22)
}

/// RFC 5480 §2.1.1 and §2.2: classify a non-RSA key as an uncompressed
/// secp256r1 or secp384r1 EC key, or Unsupported.
fn classify_ec_public_key<'a>(algorithm: &AlgorithmIdentifier<'a>, unused: u8, bits: &'a [u8])
    -> (result: PublicKey<'a>)
    ensures result@ == super::spec::classify_ec_public_key(
        crate::certificate::contract::view_algorithm_identifier(algorithm), unused, bits@)
{
    if !is_id_ec_oid(&algorithm.oid) || unused != 0 || bits.first() != Some(&0x04) {
        return PublicKey::Unsupported;
    }
    match algorithm.parameters_der {
        Some(p) => {
            if is_secp256r1_parameter(p) && bits.len() == 65 {
                PublicKey::EcP256(vstd::slice::slice_subrange(bits, 1, 65))
            } else if is_secp384r1_parameter(p) && bits.len() == 97 {
                PublicKey::EcP384(bits)
            } else {
                PublicKey::Unsupported
            }
        }
        None => PublicKey::Unsupported,
    }
}

/// Test whether the magnitude bytes contain any nonzero octet.
fn magnitude_nonzero(input: &[u8], start: usize, end: usize) -> (result: bool)
    requires start <= end, end <= input.len()
    ensures result == super::spec::positive_integer_value(input@, start as nat, end as nat)
{
    let mut i = start;
    let mut found = false;
    while i < end
        invariant
            start <= i <= end,
            end <= input.len(),
            found == super::spec::positive_integer_value(input@, start as nat, i as nat),
        decreases end - i
    {
        let byte = match input.get(i) { Some(&value) => value, None => return false };
        found = found || byte != 0;
        proof {
            reveal(super::spec::positive_integer_value);
            assert(input@[i as int] == byte);
        }
        i = i.saturating_add(1);
    }
    found
}

/// Check the one DER NULL parameter encoding required by RFC 3279 §2.3.1.
fn parameter_octet(input: &[u8], index: usize) -> (result: u8)
    ensures index < input.len() ==> result == input@[index as int]
{
    match input.get(index) {
        Some(&value) => value,
        None => 0,
    }
}

fn is_null_parameter(parameters: Option<&[u8]>) -> (result: bool)
    ensures result == match parameters {
        Some(bytes) => bytes@ =~= seq![0x05u8, 0x00u8],
        None => false,
    }
{
    match parameters {
        Some(bytes) => {
            let first = parameter_octet(bytes, 0);
            let second = parameter_octet(bytes, 1);
            let result = bytes.len() == 2 && first == 0x05 && second == 0x00;
            proof {
                assert(bytes@.len() == bytes.len());
                if result {
                    assert(first == bytes@[0]);
                    assert(second == bytes@[1]);
                    assert(bytes@[0] == 0x05);
                    assert(bytes@[1] == 0x00);
                    assert(bytes@ =~= seq![0x05u8, 0x00u8]);
                }
                if bytes@ =~= seq![0x05u8, 0x00u8] {
                    assert(bytes.len() == 2);
                    assert(first == 0x05);
                    assert(second == 0x00);
                }
            }
            result
        }
        None => false,
    }
}

/// Complete typed RSA public key components, preserving DER and magnitude bytes.
pub struct RsaPublicKey<'a> {
    /// Complete original RSAPublicKey SEQUENCE TLV.
    pub encoded_der: &'a [u8],
    /// Complete DER INTEGER TLV encoding modulus n.
    pub modulus_der: &'a [u8],
    /// Positive big-endian modulus octets, excluding DER sign padding.
    pub modulus_octets: &'a [u8],
    /// Complete DER INTEGER TLV encoding public exponent e.
    pub public_exponent_der: &'a [u8],
    /// Positive big-endian exponent octets, excluding DER sign padding.
    pub public_exponent_octets: &'a [u8],
}

impl View for RsaPublicKey<'_> {
    type V = super::spec::RsaPublicKey;
    open spec fn view(&self) -> Self::V {
        Self::V {
            encoded_der: self.encoded_der@,
            modulus_der: self.modulus_der@,
            modulus_octets: self.modulus_octets@,
            public_exponent_der: self.public_exponent_der@,
            public_exponent_octets: self.public_exponent_octets@,
        }
    }
}

/// Supported RSA or EC key, or explicit unsupported-algorithm marker.
pub enum PublicKey<'a> {
    /// rsaEncryption key syntax.
    Rsa(RsaPublicKey<'a>),
    /// secp256r1 uncompressed point: the 64 octets X || Y.
    EcP256(&'a [u8]),
    /// secp384r1 uncompressed point: the complete 97-octet ECPoint.
    EcP384(&'a [u8]),
    /// Algorithm outside this module's implemented profile.
    Unsupported,
}

impl View for PublicKey<'_> {
    type V = super::spec::PublicKey;
    open spec fn view(&self) -> Self::V {
        match self {
            PublicKey::Rsa(key) => super::spec::PublicKey::Rsa(key@),
            PublicKey::EcP256(point) => super::spec::PublicKey::EcP256(point@),
            PublicKey::EcP384(point) => super::spec::PublicKey::EcP384(point@),
            PublicKey::Unsupported => super::spec::PublicKey::Unsupported,
        }
    }
}

/// Parsed SPKI, with exact full container and key BIT STRING encodings retained.
pub struct SubjectPublicKeyInfo<'a> {
    /// RFC 5280 AlgorithmIdentifier.
    pub algorithm: AlgorithmIdentifier<'a>,
    /// Supported RSA key or explicit unsupported classification.
    pub public_key: PublicKey<'a>,
    /// BIT STRING unused-bit count; RSA requires zero.
    pub subject_public_key_unused_bits: u8,
    /// Key data octets excluding the initial unused-bit count.
    pub subject_public_key_bits: &'a [u8],
    /// Complete BIT STRING TLV.
    pub subject_public_key_tlv: &'a [u8],
    /// Complete original SubjectPublicKeyInfo SEQUENCE TLV.
    pub spki_der: &'a [u8],
}

impl View for SubjectPublicKeyInfo<'_> {
    type V = super::spec::SubjectPublicKeyInfo;
    open spec fn view(&self) -> Self::V {
        Self::V {
            algorithm: crate::certificate::contract::view_algorithm_identifier(&self.algorithm),
            public_key: self.public_key@,
            subject_public_key_unused_bits: self.subject_public_key_unused_bits,
            subject_public_key_bits: self.subject_public_key_bits@,
            subject_public_key_tlv: self.subject_public_key_tlv@,
            spki_der: self.spki_der@,
        }
    }
}

pub open spec fn view_rsa_result(result: Option<RsaPublicKey<'_>>) -> Option<super::spec::RsaPublicKey> {
    match result { Some(key) => Some(key@), None => None }
}

/// RFC 3279 §2.3.1 and RFC 8017 Appendix A.1.1: decode a canonical positive
/// modulus and exponent from one complete RSAPublicKey SEQUENCE.
pub fn parse_rsa_public_key(input: &[u8]) -> (result: Option<RsaPublicKey<'_>>)
    ensures view_rsa_result(result) == super::spec::parse_rsa_public_key(input@)
{
    let (contents_start, contents_end) = der::expect_sequence(input, 0, input.len())?;
    let outer = der::read_tlv(input, 0, input.len())?;
    if outer.cstart != contents_start || outer.cend != contents_end || outer.cend != input.len() { return None; }

    let modulus = der::read_tlv(input, contents_start, contents_end)?;
    let (modulus_negative, modulus_start, modulus_end, after_modulus) =
        der::read_integer(input, contents_start, contents_end)?;
    if modulus_negative || modulus.cend != after_modulus
        || !magnitude_nonzero(input, modulus_start, modulus_end) { return None; }
    let modulus_der = input.get(contents_start..modulus.cend)?;
    let modulus_octets = input.get(modulus_start..modulus_end)?;

    let exponent = der::read_tlv(input, after_modulus, contents_end)?;
    let (exponent_negative, exponent_start, exponent_end, after_exponent) =
        der::read_integer(input, after_modulus, contents_end)?;
    if exponent_negative || exponent.cend != after_exponent || after_exponent != contents_end
        || !magnitude_nonzero(input, exponent_start, exponent_end) { return None; }
    let public_exponent_der = input.get(after_modulus..exponent.cend)?;
    let public_exponent_octets = input.get(exponent_start..exponent_end)?;

    Some(RsaPublicKey {
        encoded_der: input,
        modulus_der,
        modulus_octets,
        public_exponent_der,
        public_exponent_octets,
    })
}

pub open spec fn view_spki_result(result: Option<SubjectPublicKeyInfo<'_>>) -> Option<super::spec::SubjectPublicKeyInfo> {
    match result { Some(value) => Some(value@), None => None }
}

/// RFC 5280 §4.1.2.7: parse one SPKI SEQUENCE with exactly an AlgorithmIdentifier
/// and BIT STRING. RSA uses the RFC 3279 §2.3.1 NULL-parameter profile; EC keys
/// are classified by RFC 5480 §2.1.1 and §2.2.
pub fn parse_subject_public_key_info(input: &[u8]) -> (result: Option<SubjectPublicKeyInfo<'_>>)
    ensures super::contract::parse_subject_public_key_info_ensures(input@, super::contract::view_result(result))
{
    hide(super::spec::parse_rsa_public_key);
    hide(crate::certificate::spec::parse_algorithm_identifier);
    hide(clazel_der::spec::read_tlv);
    hide(clazel_der::spec::read_bit_string);
    hide(clazel_der::spec::expect_sequence);
    proof {
        reveal(super::spec::parse_subject_public_key_info);
    }
    let (outer_start, outer_end) = der::expect_sequence(input, 0, input.len())?;
    let outer = der::read_tlv(input, 0, input.len())?;
    if outer.cstart != outer_start || outer.cend != outer_end || outer.cend != input.len() { return None; }

    let (algorithm, after_algorithm) =
        crate::certificate::exec::parse_algorithm_identifier(input, outer.cstart, outer.cend)?;
    let (unused_bits, bits_start, bits_end, after_bits) = der::read_bit_string(input, after_algorithm, outer.cend)?;
    proof {
        reveal(clazel_der::spec::read_bit_string);
        reveal(clazel_der::spec::read_tlv);
        assert(bits_start <= bits_end);
        assert(bits_end <= outer.cend);
    }
    if after_bits != outer.cend { return None; }
    let subject_public_key_bits = input.get(bits_start..bits_end)?;
    let subject_public_key_tlv = input.get(after_algorithm..after_bits)?;
    let spki_der = input.get(0..outer.cend)?;

    let public_key = if is_rsa_oid(&algorithm.oid) {
        let rsa_null_parameters = is_null_parameter(algorithm.parameters_der);
        proof {
            assert((crate::certificate::contract::view_algorithm_identifier(&algorithm).parameters_der
                == Some(seq![0x05u8, 0x00u8])) == rsa_null_parameters);
        }
        if !rsa_null_parameters || unused_bits != 0 { return None; }
        proof {
            assert(crate::certificate::contract::view_algorithm_identifier(&algorithm).parameters_der
                == Some(seq![0x05u8, 0x00u8]));
        }
        let rsa = parse_rsa_public_key(subject_public_key_bits)?;
        PublicKey::Rsa(rsa)
    } else {
        classify_ec_public_key(&algorithm, unused_bits, subject_public_key_bits)
    };
    let result = SubjectPublicKeyInfo {
        algorithm,
        public_key,
        subject_public_key_unused_bits: unused_bits,
        subject_public_key_bits,
        subject_public_key_tlv,
        spki_der,
    };
    proof {
        reveal(super::spec::parse_subject_public_key_info);
        reveal(crate::certificate::spec::parse_algorithm_identifier);
        assert(result.spki_der@ == input@);
    }
    Some(result)
}

} // verus!
