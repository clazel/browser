//! RFC 5280 §4.1.1.1 to §4.1.1.3 Certificate envelope specification.
//! <https://www.rfc-editor.org/rfc/rfc5280.html#section-4.1>
//!
//! Modelling choices and limits:
//! - The outer Certificate is exactly a DER SEQUENCE with exactly the three
//!   fields from §4.1: TBSCertificate SEQUENCE, AlgorithmIdentifier SEQUENCE,
//!   and signatureValue BIT STRING. The complete input must be consumed.
//! - TBSCertificate contents remain opaque. Its outer SEQUENCE TLV is retained
//!   byte-for-byte because §4.1.1.3 signs the DER encoding, not a re-encoding.
//!   No TBS fields are parsed or validated here.
//! - AlgorithmIdentifier parses one DER OBJECT IDENTIFIER and zero or one
//!   optional parameter value. The parameter's complete single TLV is kept
//!   opaque; this module does not interpret the algorithm-dependent ANY, nor
//!   recursively validate opaque constructed contents.
//! - The BIT STRING is checked by clazel-der's DER reader, including unused
//!   bits 0..=7 and zero padding bits. Its unused-bit count is preserved and
//!   is not forced to zero; a later supported-algorithm profile may require
//!   octet alignment.
//! - DER low-level readers reject unsupported tag/length encodings and
//!   overrun. This parser accepts the clazel-der reader's DER profile.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// AlgorithmIdentifier: OID arcs and the optional complete DER TLV of
/// algorithm-defined parameters (RFC 5280 §4.1.1.2).
pub struct AlgorithmIdentifier {
    /// OBJECT IDENTIFIER arcs.
    pub oid: Seq<nat>,
    /// Optional complete parameter TLV; retained without algorithm-specific
    /// interpretation.
    pub parameters_der: Option<Seq<u8>>,
}

/// The three required outer Certificate fields (RFC 5280 §4.1.1).
pub struct CertificateEnvelope {
    /// Exact DER TLV bytes of TBSCertificate, including tag and length.
    pub tbs_certificate_der: Seq<u8>,
    /// Parsed outer signature algorithm identifier.
    pub signature_algorithm: AlgorithmIdentifier,
    /// Number of unused low-order bits in the signature BIT STRING.
    pub signature_unused_bits: u8,
    /// Signature BIT STRING's data octets, excluding its initial unused-bit
    /// count octet.
    pub signature_bits: Seq<u8>,
}

/// RFC 5280 §4.1.1.2: AlgorithmIdentifier is a SEQUENCE containing the
/// algorithm OBJECT IDENTIFIER and an optional single parameters ANY value.
pub open spec fn parse_algorithm_identifier(
    input: Seq<u8>, pos: nat, end: nat,
) -> Option<(AlgorithmIdentifier, nat)> {
    match clazel_der::spec::expect_sequence(input, pos, end) {
        None => None,
        Some((contents_start, contents_end)) => match clazel_der::spec::read_oid(input, contents_start, contents_end) {
            None => None,
            Some((oid, after_oid)) => {
                if after_oid == contents_end {
                    Some((AlgorithmIdentifier { oid, parameters_der: None }, contents_end))
                } else {
                    match clazel_der::spec::read_tlv(input, after_oid, contents_end) {
                        Some(parameter) if parameter.cend == contents_end => {
                            Some((AlgorithmIdentifier {
                                oid,
                                parameters_der: Some(input.subrange(after_oid as int, contents_end as int)),
                            }, contents_end))
                        },
                        _ => None,
                    }
                }
            },
        },
    }
}

/// RFC 5280 §4.1 Certificate: parse the outer three fields and preserve the
/// exact TBSCertificate encoding used by §4.1.1.3's signature input.
pub open spec fn parse_certificate(input: Seq<u8>) -> Option<CertificateEnvelope> {
    match clazel_der::spec::expect_sequence(input, 0, input.len()) {
        Some((outer_start, outer_end)) => match clazel_der::spec::read_tlv(input, 0, input.len()) {
        Some(outer) if outer.cstart == outer_start && outer.cend == outer_end
            && outer.cend == input.len() =>
        {
            match clazel_der::spec::expect_sequence(input, outer.cstart, outer.cend) {
                Some((tbs_start, tbs_end)) => match clazel_der::spec::read_tlv(input, outer.cstart, outer.cend) {
                Some(tbs) if tbs.cstart == tbs_start && tbs.cend == tbs_end => {
                    match parse_algorithm_identifier(input, tbs.cend, outer.cend) {
                        Some((algorithm, after_algorithm)) =>
                        match clazel_der::spec::read_bit_string(input, after_algorithm, outer.cend) {
                            Some((unused, bits_start, bits_end, after_signature))
                                if after_signature == outer.cend =>
                            {
                                Some(CertificateEnvelope {
                                    tbs_certificate_der: input.subrange(outer.cstart as int, tbs.cend as int),
                                    signature_algorithm: algorithm,
                                    signature_unused_bits: unused,
                                    signature_bits: input.subrange(bits_start as int, bits_end as int),
                                })
                            },
                            _ => None,
                        },
                        None => None,
                    }
                },
                _ => None,
                },
                None => None,
            }
        },
        _ => None,
        },
        None => None,
    }
}

} // verus!
