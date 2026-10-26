//! RFC 5280 §4.1.2 TBSCertificate schema specification.
//! <https://www.rfc-editor.org/rfc/rfc5280.html#section-4.1.2>
//!
//! Modelling choices: input is exactly one DER SEQUENCE TLV. Name and
//! SubjectPublicKeyInfo are retained as complete opaque SEQUENCE TLVs. The
//! serial must be nonnegative and at most 20 content octets; zero is accepted
//! for graceful processing. Omitted version means v1; explicitly encoded
//! default v1 is rejected. Implicit unique IDs use DER BIT STRING contents.
//! Extensions are retained as both the [3] EXPLICIT TLV and inner SEQUENCE.
//! This parses framing only: Name/SPKI internals, signature checks, and path
//! validation are outside this module.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Structurally decoded fields from one TBSCertificate.
pub struct TbsCertificate {
    /// RFC version number: 0 (v1), 1 (v2), or 2 (v3).
    pub version: nat,
    /// Complete DER INTEGER TLV for serialNumber.
    pub serial_number_der: Seq<u8>,
    /// TBS signature AlgorithmIdentifier.
    pub signature: crate::certificate::spec::AlgorithmIdentifier,
    /// Complete opaque issuer Name SEQUENCE TLV.
    pub issuer_der: Seq<u8>,
    /// Decoded validity start.
    pub not_before: crate::time::spec::CertificateTime,
    /// Decoded validity end.
    pub not_after: crate::time::spec::CertificateTime,
    /// Complete opaque subject Name SEQUENCE TLV.
    pub subject_der: Seq<u8>,
    /// Complete opaque SubjectPublicKeyInfo SEQUENCE TLV.
    pub subject_public_key_info_der: Seq<u8>,
    /// Optional complete implicit [1] UniqueIdentifier TLV.
    pub issuer_unique_id_der: Option<Seq<u8>>,
    /// Optional complete implicit [2] UniqueIdentifier TLV.
    pub subject_unique_id_der: Option<Seq<u8>>,
    /// Optional complete [3] EXPLICIT Extensions wrapper TLV.
    pub extensions_der: Option<Seq<u8>>,
    /// Optional inner complete Extensions SEQUENCE TLV.
    pub extensions_sequence_der: Option<Seq<u8>>,
    /// Complete original signed TBSCertificate SEQUENCE TLV.
    pub tbs_certificate_der: Seq<u8>,
}

/// Prefix fields parsed in order before signature and issuer.
pub struct Prefix {
    /// RFC version number.
    pub version: nat,
    /// Complete serial INTEGER TLV.
    pub serial_der: Seq<u8>,
    /// Cursor after the serial INTEGER.
    pub pos: nat,
    /// Complete original TBS SEQUENCE TLV.
    pub tbs_der: Seq<u8>,
    /// End of TBSCertificate contents.
    pub end: nat,
}

/// Parse one complete DER UTCTime or GeneralizedTime.
pub open spec fn time_tlv(input: Seq<u8>, pos: nat, end: nat) -> Option<(crate::time::spec::CertificateTime, nat)> {
    match clazel_der::spec::read_tlv(input, pos, end) {
        Some(t) if t.tag == clazel_der::spec::universal_primitive(clazel_der::spec::UTC_TIME) =>
            match crate::time::spec::decode_time(crate::time::spec::TimeKind::Utc, input.subrange(t.cstart as int, t.cend as int)) {
                Some(time) => Some((time, t.cend)), None => None,
            },
        Some(t) if t.tag == clazel_der::spec::universal_primitive(clazel_der::spec::GENERALIZED_TIME) =>
            match crate::time::spec::decode_time(crate::time::spec::TimeKind::Generalized, input.subrange(t.cstart as int, t.cend as int)) {
                Some(time) => Some((time, t.cend)), None => None,
            },
        _ => None,
    }
}

/// RFC 5280 §4.1.2.2 serialNumber: a nonnegative INTEGER with at most 20
/// encoded contents octets; zero is allowed for graceful processing.
pub open spec fn parse_serial(input: Seq<u8>, pos: nat, end: nat) -> Option<(Seq<u8>, nat)> {
    match clazel_der::spec::read_tlv(input, pos, end) {
        None => None,
        Some(serial) => match clazel_der::spec::read_integer(input, pos, end) {
            Some((negative, _, contents_end, next)) if !negative && next == serial.cend
                && contents_end - serial.cstart <= 20
                => Some((input.subrange(pos as int, serial.cend as int), serial.cend)),
            _ => None,
        },
    }
}

/// RFC 5280 §4.1.2.1/.2: explicit non-default version followed by a
/// nonnegative, at-most-20-octet serial INTEGER.
pub open spec fn parse_prefix(input: Seq<u8>) -> Option<Prefix> {
    match clazel_der::spec::expect_sequence(input, 0, input.len()) {
        None => None,
        Some((start, end)) => match clazel_der::spec::read_tlv(input, 0, input.len()) {
            None => None,
            Some(outer) if outer.cstart != start || outer.cend != end || end != input.len() => None,
            Some(outer) => match parse_version(input, start, end) {
                None => None,
                Some((version, serial_pos)) => match parse_serial(input, serial_pos, end) {
                    Some((serial_der, after_serial)) => Some(Prefix { version, serial_der, pos: after_serial, tbs_der: input.subrange(0, outer.cend as int), end }),
                    None => None,
                },
            },
        },
    }
}

/// Optional [0] EXPLICIT Version DEFAULT v1, then the serial field cursor.
pub open spec fn parse_version(input: Seq<u8>, start: nat, end: nat) -> Option<(nat, nat)> {
    match clazel_der::spec::read_tlv(input, start, end) {
        None => None,
        Some(first) if first.tag == clazel_der::spec::context_specific(0, true) =>
            match clazel_der::spec::read_integer(input, first.cstart, first.cend) {
                Some((false, value_start, value_end, next)) if next == first.cend && value_end - value_start == 1 => {
                    let value = input[value_start as int] as nat;
                    if value == 1 || value == 2 { Some((value, first.cend)) } else { None }
                },
                _ => None,
            },
        Some(_) => Some((0, start)),
    }
}

/// Optional implicit UniqueIdentifier, preserving its full DER TLV.
pub open spec fn optional_unique(input: Seq<u8>, pos: nat, end: nat, number: u32, version: nat) -> Option<(Option<Seq<u8>>, nat)> {
    if pos == end { Some((None, pos)) }
    else { match clazel_der::spec::read_tlv(input, pos, end) {
        None => None,
        Some(t) if t.tag == clazel_der::spec::context_specific(number, false) => {
            let n = t.cend - t.cstart;
            if version == 0 || n == 0 || input[t.cstart as int] > 7
                || n == 1 && input[t.cstart as int] != 0
                || n > 1 && input[(t.cend - 1) as int] as nat % clazel_der::spec::pow2_unused(input[t.cstart as int]) != 0 { None }
            else { Some((Some(input.subrange(pos as int, t.cend as int)), t.cend)) }
        },
        Some(_) => Some((None, pos)),
    }}
}

/// Optional RFC 5280 [3] EXPLICIT Extensions, present only on v3.
pub open spec fn optional_extensions(input: Seq<u8>, pos: nat, end: nat, version: nat)
    -> Option<(Option<Seq<u8>>, Option<Seq<u8>>, nat)>
{
    if pos == end { Some((None, None, pos)) }
    else { match clazel_der::spec::read_tlv(input, pos, end) {
        None => None,
        Some(t) if t.tag == clazel_der::spec::context_specific(3, true) => {
            match clazel_der::spec::expect_sequence(input, t.cstart, t.cend) {
                Some((start, finish)) => match clazel_der::spec::read_tlv(input, t.cstart, t.cend) {
                    Some(inner) if version == 2 && inner.cstart == start && inner.cend == finish && inner.cend == t.cend
                        => Some((Some(input.subrange(pos as int, t.cend as int)), Some(input.subrange(t.cstart as int, t.cend as int)), t.cend)),
                    _ => None,
                },
                None => None,
            }
        },
        Some(_) => Some((None, None, pos)),
    }}
}

/// RFC 5280 §4.1.2 fields in schema order. Helpers isolate each bounded
/// section so refinement obligations remain local to each cursor transition.
pub open spec fn parse_tbs_certificate(input: Seq<u8>) -> Option<TbsCertificate> {
    match parse_prefix(input) {
        None => None,
        Some(prefix) => match parse_signature_issuer(input, prefix.pos, prefix.end) {
            None => None,
            Some((signature, issuer, pos)) => match parse_validity(input, pos, prefix.end) {
                None => None,
                Some((not_before, not_after, pos)) => match parse_subject_spki(input, pos, prefix.end) {
                    None => None,
                    Some((subject, spki, pos)) => match optional_unique(input, pos, prefix.end, 1, prefix.version) {
                        None => None,
                        Some((issuer_uid, pos)) => match optional_unique(input, pos, prefix.end, 2, prefix.version) {
                            None => None,
                            Some((subject_uid, pos)) => match optional_extensions(input, pos, prefix.end, prefix.version) {
                                Some((extensions, extension_sequence, after)) if after == prefix.end => Some(TbsCertificate {
                                    version: prefix.version, serial_number_der: prefix.serial_der, signature, issuer_der: issuer,
                                    not_before, not_after, subject_der: subject, subject_public_key_info_der: spki,
                                    issuer_unique_id_der: issuer_uid, subject_unique_id_der: subject_uid,
                                    extensions_der: extensions, extensions_sequence_der: extension_sequence,
                                    tbs_certificate_der: prefix.tbs_der,
                                }),
                                _ => None,
                            },
                        },
                    },
                },
            },
        },
    }
}

pub open spec fn parse_signature_issuer(input: Seq<u8>, pos: nat, end: nat)
    -> Option<(crate::certificate::spec::AlgorithmIdentifier, Seq<u8>, nat)>
{
    match crate::certificate::spec::parse_algorithm_identifier(input, pos, end) {
        None => None,
        Some((algorithm, after_algorithm)) => match clazel_der::spec::read_tlv(input, after_algorithm, end) {
            Some(issuer) if issuer.tag == clazel_der::spec::universal_constructed(clazel_der::spec::SEQUENCE) && issuer.cstart != issuer.cend
                => Some((algorithm, input.subrange(after_algorithm as int, issuer.cend as int), issuer.cend)),
            _ => None,
        },
    }
}

pub open spec fn parse_validity(input: Seq<u8>, pos: nat, end: nat)
    -> Option<(crate::time::spec::CertificateTime, crate::time::spec::CertificateTime, nat)>
{
    match clazel_der::spec::expect_sequence(input, pos, end) {
        None => None,
        Some((start, finish)) => match time_tlv(input, start, finish) {
            None => None,
            Some((before, after_before)) => match time_tlv(input, after_before, finish) {
                Some((after, after_after)) if after_after == finish && crate::time::spec::time_le(before, after)
                    => Some((before, after, finish)),
                _ => None,
            },
        },
    }
}

pub open spec fn parse_subject_spki(input: Seq<u8>, pos: nat, end: nat) -> Option<(Seq<u8>, Seq<u8>, nat)> {
    match clazel_der::spec::read_tlv(input, pos, end) {
        Some(subject) if subject.tag == clazel_der::spec::universal_constructed(clazel_der::spec::SEQUENCE) =>
            match clazel_der::spec::read_tlv(input, subject.cend, end) {
                Some(spki) if spki.tag == clazel_der::spec::universal_constructed(clazel_der::spec::SEQUENCE)
                    => Some((input.subrange(pos as int, subject.cend as int), input.subrange(subject.cend as int, spki.cend as int), spki.cend)),
                _ => None,
            },
        _ => None,
    }
}

} // verus!
