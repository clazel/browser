//! Executable RFC 5280 §4.1 envelope parser, proven to `spec`.

use super::spec as cert_spec;
use clazel_der::decode as der;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Parsed AlgorithmIdentifier with opaque borrowed parameter DER.
pub struct AlgorithmIdentifier<'a> {
    /// OBJECT IDENTIFIER arcs.
    pub oid: Vec<u64>,
    /// Optional complete DER TLV for algorithm-defined parameters.
    pub parameters_der: Option<&'a [u8]>,
}

impl View for AlgorithmIdentifier<'_> {
    type V = cert_spec::AlgorithmIdentifier;
    closed spec fn view(&self) -> Self::V {
        cert_spec::AlgorithmIdentifier {
            oid: der::nats(self.oid@),
            parameters_der: match self.parameters_der {
                Some(bytes) => Some(bytes@),
                None => None,
            },
        }
    }
}

/// Parsed Certificate envelope, not a validated certificate. The borrowed
/// TBS slice includes its full original TLV; its fields remain unvalidated.
pub struct CertificateEnvelope<'a> {
    /// Exact original TBSCertificate DER, including SEQUENCE tag and length.
    pub tbs_certificate_der: &'a [u8],
    /// Outer signature AlgorithmIdentifier.
    pub signature_algorithm: AlgorithmIdentifier<'a>,
    /// DER BIT STRING unused-bit count, retained as encoded.
    pub signature_unused_bits: u8,
    /// BIT STRING data octets, excluding the initial unused-bit count.
    pub signature_bits: &'a [u8],
}

impl View for CertificateEnvelope<'_> {
    type V = cert_spec::CertificateEnvelope;
    closed spec fn view(&self) -> Self::V {
        cert_spec::CertificateEnvelope {
            tbs_certificate_der: self.tbs_certificate_der@,
            signature_algorithm: self.signature_algorithm@,
            signature_unused_bits: self.signature_unused_bits,
            signature_bits: self.signature_bits@,
        }
    }
}

/// RFC 5280 §4.1.1.2 AlgorithmIdentifier: one OID and at most one optional
/// parameter TLV. The parameter remains opaque and is borrowed exactly.
pub fn parse_algorithm_identifier(input: &[u8], pos: usize, end: usize)
    -> (result: Option<(AlgorithmIdentifier<'_>, usize)>)
    requires end <= input.len()
    ensures super::contract::parse_algorithm_identifier_ensures(
        input@, pos as nat, end as nat, super::contract::view_algorithm_result(result))
{
    let (contents_start, contents_end) = der::expect_sequence(input, pos, end)?;
    let (oid, after_oid) = der::read_oid(input, contents_start, contents_end)?;
    let parameters_der = if after_oid == contents_end {
        None
    } else {
        let parameter = der::read_tlv(input, after_oid, contents_end)?;
        if parameter.cend != contents_end {
            return None;
        }
        let raw_parameter = input.get(after_oid..contents_end)?;
        Some(raw_parameter)
    };
    Some((AlgorithmIdentifier { oid, parameters_der }, contents_end))
}

/// RFC 5280 §4.1.1: parse precisely the Certificate's three outer fields.
/// TBS contents are deliberately opaque; their original tag, length and
/// contents are retained together as the signature input (§4.1.1.3).
pub fn parse_certificate(input: &[u8]) -> (result: Option<CertificateEnvelope<'_>>)
    ensures super::contract::parse_certificate_ensures(
        input@, super::contract::view_certificate_result(result))
{
    let (outer_start, outer_end) = der::expect_sequence(input, 0, input.len())?;
    let outer = der::read_tlv(input, 0, input.len())?;
    if outer.cstart != outer_start || outer.cend != outer_end || outer.cend != input.len() {
        return None;
    }
    let (tbs_start, tbs_end) = der::expect_sequence(input, outer.cstart, outer.cend)?;
    let tbs = der::read_tlv(input, outer.cstart, outer.cend)?;
    if tbs.cstart != tbs_start || tbs.cend != tbs_end {
        return None;
    }
    let tbs_certificate_der = input.get(outer.cstart..tbs.cend)?;
    let (signature_algorithm, after_algorithm) =
        parse_algorithm_identifier(input, tbs.cend, outer.cend)?;
    let (unused_bits, signature_start, signature_end, after_signature) =
        der::read_bit_string(input, after_algorithm, outer.cend)?;
    if after_signature != outer.cend {
        return None;
    }
    let signature_bits = input.get(signature_start..signature_end)?;
    Some(CertificateEnvelope {
        tbs_certificate_der,
        signature_algorithm,
        signature_unused_bits: unused_bits,
        signature_bits,
    })
}

} // verus!
