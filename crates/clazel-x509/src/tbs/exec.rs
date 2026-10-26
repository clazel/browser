//! RFC 5280 §4.1.2 TBSCertificate structural reader.

use crate::certificate::exec::AlgorithmIdentifier;
use clazel_der::decode as der;
use clazel_der::spec::{Class, Tag};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

fn is_context_tag(tag: Tag, number: u32, constructed: bool) -> (result: bool)
    ensures result == (tag == clazel_der::spec::context_specific(number, constructed))
{
    match tag.class {
        Class::ContextSpecific => tag.number == number && tag.constructed == constructed,
        _ => false,
    }
}

fn is_universal_tag(tag: Tag, number: u32, constructed: bool) -> (result: bool)
    ensures result == (tag == if constructed { clazel_der::spec::universal_constructed(number) } else { clazel_der::spec::universal_primitive(number) })
{
    match tag.class {
        Class::Universal => tag.number == number && tag.constructed == constructed,
        _ => false,
    }
}

/// Structurally decoded fields borrowed from one TBSCertificate.
pub struct TbsCertificate<'a> {
    /// RFC version number: 0 (v1), 1 (v2), or 2 (v3).
    pub version: u8,
    /// Complete DER INTEGER TLV for serialNumber.
    pub serial_number_der: &'a [u8],
    /// TBS signature AlgorithmIdentifier.
    pub signature: AlgorithmIdentifier<'a>,
    /// Complete opaque issuer Name SEQUENCE TLV.
    pub issuer_der: &'a [u8],
    /// Decoded validity start.
    pub not_before: crate::time::exec::CertificateTime,
    /// Decoded validity end.
    pub not_after: crate::time::exec::CertificateTime,
    /// Complete opaque subject Name SEQUENCE TLV.
    pub subject_der: &'a [u8],
    /// Complete opaque SubjectPublicKeyInfo SEQUENCE TLV.
    pub subject_public_key_info_der: &'a [u8],
    /// Optional complete implicit [1] UniqueIdentifier TLV.
    pub issuer_unique_id_der: Option<&'a [u8]>,
    /// Optional complete implicit [2] UniqueIdentifier TLV.
    pub subject_unique_id_der: Option<&'a [u8]>,
    /// Optional complete [3] EXPLICIT Extensions wrapper TLV.
    pub extensions_der: Option<&'a [u8]>,
    /// Optional inner complete Extensions SEQUENCE TLV.
    pub extensions_sequence_der: Option<&'a [u8]>,
    /// Complete original signed TBSCertificate SEQUENCE TLV.
    pub tbs_certificate_der: &'a [u8],
}

impl View for TbsCertificate<'_> {
    type V = super::spec::TbsCertificate;
    closed spec fn view(&self) -> Self::V {
        Self::V {
            version: self.version as nat,
            serial_number_der: self.serial_number_der@,
            signature: self.signature@,
            issuer_der: self.issuer_der@,
            not_before: self.not_before@,
            not_after: self.not_after@,
            subject_der: self.subject_der@,
            subject_public_key_info_der: self.subject_public_key_info_der@,
            issuer_unique_id_der: match self.issuer_unique_id_der { Some(x) => Some(x@), None => None },
            subject_unique_id_der: match self.subject_unique_id_der { Some(x) => Some(x@), None => None },
            extensions_der: match self.extensions_der { Some(x) => Some(x@), None => None },
            extensions_sequence_der: match self.extensions_sequence_der { Some(x) => Some(x@), None => None },
            tbs_certificate_der: self.tbs_certificate_der@,
        }
    }
}


/// Checked mandatory prefix and the cursor after serialNumber.
pub struct Prefix<'a> {
    /// RFC version number.
    pub version: u8,
    /// Complete serial INTEGER TLV.
    pub serial_der: &'a [u8],
    /// Cursor after serialNumber.
    pub pos: usize,
    /// Complete original TBS SEQUENCE TLV.
    pub tbs_der: &'a [u8],
    /// End of TBS contents.
    pub end: usize,
}

impl View for Prefix<'_> {
    type V = super::spec::Prefix;
    closed spec fn view(&self) -> Self::V {
        Self::V { version: self.version as nat, serial_der: self.serial_der@,
            pos: self.pos as nat, tbs_der: self.tbs_der@, end: self.end as nat }
    }
}

pub open spec fn view_prefix_result(result: Option<Prefix<'_>>) -> Option<super::spec::Prefix> {
    match result { Some(value) => Some(value@), None => None }
}

/// View conversion for the optional version parser.
pub open spec fn view_version_result(result: Option<(u8, usize)>) -> Option<(nat, nat)> {
    match result { Some((version, pos)) => Some((version as nat, pos as nat)), None => None }
}

/// RFC 5280 §4.1.2.1: omitted version defaults to v1; explicit v1 is DER's
/// forbidden encoding of DEFAULT and is rejected.
fn parse_version(input: &[u8], start: usize, end: usize) -> (result: Option<(u8, usize)>)
    requires end <= input.len(), start <= end
    ensures view_version_result(result) == super::spec::parse_version(input@, start as nat, end as nat)
{
    let first_result = der::read_tlv(input, start, end);
    proof {
        reveal(super::spec::parse_version);
        assert(der::view_tlv(first_result) == clazel_der::spec::read_tlv(input@, start as nat, end as nat));
    }
    let first = first_result?;
    if is_context_tag(first.tag, 0, true) {
        let integer_result = der::read_integer(input, first.cstart, first.cend);
        proof {
            reveal(clazel_der::spec::read_integer);
            assert(der::view_integer(integer_result) == clazel_der::spec::read_integer(input@, first.cstart as nat, first.cend as nat));
        }
        let (negative, value_start, value_end, next) = integer_result?;
        assert(value_start <= value_end);
        if negative || next != first.cend || value_end.checked_sub(value_start)? != 1 { return None; }
        let value = *input.get(value_start)?;
        if value == 0 || value > 2 { return None; }
        Some((value, first.cend))
    } else { Some((0, start)) }
}

/// View conversion for the serial reader result.
pub open spec fn view_serial_result(result: Option<(&[u8], usize)>) -> Option<(Seq<u8>, nat)> {
    match result { Some((serial, next)) => Some((serial@, next as nat)), None => None }
}

/// RFC 5280 §4.1.2.2: parse a nonnegative INTEGER and enforce the 20-octet
/// encoded-content size limit while retaining the exact TLV.
fn parse_serial(input: &[u8], pos: usize, end: usize) -> (result: Option<(&[u8], usize)>)
    requires pos <= end, end <= input.len()
    ensures view_serial_result(result) == super::spec::parse_serial(input@, pos as nat, end as nat)
{
    let serial = der::read_tlv(input, pos, end)?;
    let (negative, _, contents_end, next) = der::read_integer(input, pos, end)?;
    assert(serial.cstart <= contents_end);
    if negative || next != serial.cend || contents_end.checked_sub(serial.cstart)? > 20 { return None; }
    Some((input.get(pos..serial.cend)?, serial.cend))
}

/// RFC 5280 §4.1.2.1/.2: parse optional non-default version and serial number.
fn parse_prefix(input: &[u8]) -> (result: Option<Prefix<'_>>)
    ensures
        view_prefix_result(result) == super::spec::parse_prefix(input@),
        match result {
            Some(prefix) => prefix.pos <= prefix.end && prefix.end <= input.len() && prefix.version <= 2,
            None => true,
        }
{
    let (contents_start, contents_end) = der::expect_sequence(input, 0, input.len())?;
    let outer = der::read_tlv(input, 0, input.len())?;
    if outer.cstart != contents_start || outer.cend != contents_end || outer.cend != input.len() { return None; }
    let (version, serial_pos) = parse_version(input, contents_start, contents_end)?;
    let (serial_der, after_serial) = parse_serial(input, serial_pos, contents_end)?;
    Some(Prefix {
        version,
        serial_der,
        pos: after_serial,
        tbs_der: input.get(0..outer.cend)?,
        end: contents_end,
    })
}

pub open spec fn view_time_result(result: Option<(crate::time::exec::CertificateTime, usize)>)
    -> Option<(crate::time::spec::CertificateTime, nat)> {
    match result { Some((time, next)) => Some((time@, next as nat)), None => None }
}

/// Parse one validity time from its DER TLV. RFC 5280 §4.1.2.5.1/.2.
fn parse_time(input: &[u8], pos: usize, end: usize)
    -> (result: Option<(crate::time::exec::CertificateTime, usize)>)
    requires pos <= end, end <= input.len()
    ensures view_time_result(result) == super::spec::time_tlv(input@, pos as nat, end as nat)
{
    let tlv = der::read_tlv(input, pos, end)?;
    let utc_tag = is_universal_tag(tlv.tag, 23, false);
    let generalized_tag = is_universal_tag(tlv.tag, 24, false);
    let kind = if utc_tag {
        crate::time::exec::TimeKind::Utc
    } else if generalized_tag {
        crate::time::exec::TimeKind::Generalized
    } else {
        return None;
    };
    let contents = input.get(tlv.cstart..tlv.cend)?;
    proof {
        reveal(super::spec::time_tlv);
        assert(contents@ =~= input@.subrange(tlv.cstart as int, tlv.cend as int));
        assert(utc_tag == (tlv.tag == clazel_der::spec::universal_primitive(23)));
        assert(generalized_tag == (tlv.tag == clazel_der::spec::universal_primitive(24)));
        assert(kind@ == crate::time::exec::time_kind_view(kind));
        assert(crate::time::exec::time_kind_view(kind) == if utc_tag {
            crate::time::spec::TimeKind::Utc
        } else { crate::time::spec::TimeKind::Generalized });
    }
    Some((crate::time::exec::decode_time(contents, kind)?, tlv.cend))
}

/// Validate the contents of an implicitly tagged DER BIT STRING.
fn valid_implicit_bit_string(input: &[u8], start: usize, end: usize) -> (result: bool)
    requires start <= end, end <= input.len()
    ensures result == super::spec::valid_implicit_bit_string(input@.subrange(start as int, end as int))
{
    let len = end.saturating_sub(start);
    if len == 0 { return false; }
    let unused = match input.get(start) { Some(&n) => n, None => return false };
    if unused > 7 { return false; }
    if len == 1 { return unused == 0; }
    let last = match input.get(end.saturating_sub(1)) { Some(&n) => n, None => return false };
    let divisor: u16 = match unused {
        0 => 1, 1 => 2, 2 => 4, 3 => 8, 4 => 16, 5 => 32, 6 => 64, _ => 128,
    };
    (last as u16).is_multiple_of(divisor)
}

pub open spec fn view_signature_issuer_result(result: Option<(AlgorithmIdentifier<'_>, &[u8], usize)>)
    -> Option<(crate::certificate::spec::AlgorithmIdentifier, Seq<u8>, nat)> {
    match result { Some((alg, issuer, next)) => Some((alg@, issuer@, next as nat)), None => None }
}

/// RFC 5280 §4.1.2.3/.4: parse the TBS signature algorithm and bounded issuer Name.
fn parse_signature_issuer(input: &[u8], pos: usize, end: usize)
    -> (result: Option<(AlgorithmIdentifier<'_>, &[u8], usize)>)
    requires pos <= end, end <= input.len()
    ensures
        view_signature_issuer_result(result) == super::spec::parse_signature_issuer(input@, pos as nat, end as nat),
        match result { Some((_, _, next)) => next <= end, None => true }
{
    let (algorithm, after_algorithm) = crate::certificate::exec::parse_algorithm_identifier(input, pos, end)?;
    let issuer = der::read_tlv(input, after_algorithm, end)?;
    if !is_universal_tag(issuer.tag, 16, true) || issuer.cstart == issuer.cend { return None; }
    Some((algorithm, input.get(after_algorithm..issuer.cend)?, issuer.cend))
}

pub open spec fn view_validity_result(result: Option<(crate::time::exec::CertificateTime, crate::time::exec::CertificateTime, usize)>)
    -> Option<(crate::time::spec::CertificateTime, crate::time::spec::CertificateTime, nat)> {
    match result { Some((before, after, next)) => Some((before@, after@, next as nat)), None => None }
}

/// RFC 5280 §4.1.2.5: parse both ordered validity endpoints and consume the SEQUENCE.
fn parse_validity(input: &[u8], pos: usize, end: usize)
    -> (result: Option<(crate::time::exec::CertificateTime, crate::time::exec::CertificateTime, usize)>)
    requires pos <= end, end <= input.len()
    ensures
        view_validity_result(result) == super::spec::parse_validity(input@, pos as nat, end as nat),
        match result { Some((_, _, next)) => next <= end, None => true }
{
    let (start, finish) = der::expect_sequence(input, pos, end)?;
    let (before, after_before) = parse_time(input, start, finish)?;
    if after_before > finish { return None; }
    let (after, after_after) = parse_time(input, after_before, finish)?;
    if after_after != finish || !crate::time::exec::time_le(&before, &after) { return None; }
    Some((before, after, finish))
}

pub open spec fn view_subject_spki_result(result: Option<(&[u8], &[u8], usize)>) -> Option<(Seq<u8>, Seq<u8>, nat)> {
    match result { Some((subject, spki, next)) => Some((subject@, spki@, next as nat)), None => None }
}

/// RFC 5280 §4.1.2.6/.7: preserve the complete subject and SPKI SEQUENCE TLVs.
fn parse_subject_spki(input: &[u8], pos: usize, end: usize)
    -> (result: Option<(&[u8], &[u8], usize)>)
    requires pos <= end, end <= input.len()
    ensures
        view_subject_spki_result(result) == super::spec::parse_subject_spki(input@, pos as nat, end as nat),
        match result { Some((_, _, next)) => next <= end, None => true }
{
    let subject = der::read_tlv(input, pos, end)?;
    if !is_universal_tag(subject.tag, 16, true) { return None; }
    let spki = der::read_tlv(input, subject.cend, end)?;
    if !is_universal_tag(spki.tag, 16, true) { return None; }
    Some((input.get(pos..subject.cend)?, input.get(subject.cend..spki.cend)?, spki.cend))
}

/// Optional components after SubjectPublicKeyInfo.
pub struct OptionalTail<'a> {
    /// Original issuerUniqueID [1] TLV.
    pub issuer_uid: Option<&'a [u8]>,
    /// Original subjectUniqueID [2] TLV.
    pub subject_uid: Option<&'a [u8]>,
    /// Full [3] EXPLICIT Extensions TLV.
    pub extensions: Option<&'a [u8]>,
    /// Inner Extensions SEQUENCE TLV.
    pub extensions_sequence: Option<&'a [u8]>,
}

impl View for OptionalTail<'_> {
    type V = super::spec::OptionalTail;
    closed spec fn view(&self) -> Self::V {
        Self::V {
            issuer_unique_id_der: match self.issuer_uid { Some(bytes) => Some(bytes@), None => None },
            subject_unique_id_der: match self.subject_uid { Some(bytes) => Some(bytes@), None => None },
            extensions_der: match self.extensions { Some(bytes) => Some(bytes@), None => None },
            extensions_sequence_der: match self.extensions_sequence { Some(bytes) => Some(bytes@), None => None },
        }
    }
}

pub open spec fn view_optional_tail_result(result: Option<OptionalTail<'_>>) -> Option<super::spec::OptionalTail> {
    match result { Some(value) => Some(value@), None => None }
}

pub open spec fn view_optional_unique_result(result: Option<(Option<&[u8]>, usize)>)
    -> Option<(Option<Seq<u8>>, nat)> {
    match result { Some((raw, next)) => Some((match raw { Some(bytes) => Some(bytes@), None => None }, next as nat)), None => None }
}

/// RFC 5280 §4.1.2.8/.9: validate one optional implicit UniqueIdentifier.
fn parse_optional_unique(input: &[u8], pos: usize, end: usize, number: u32, version: u8)
    -> (result: Option<(Option<&[u8]>, usize)>)
    requires pos <= end, end <= input.len(), version <= 2
    ensures view_optional_unique_result(result) == super::spec::optional_unique(input@, pos as nat, end as nat, number, version as nat)
{
    if pos == end { return Some((None, pos)); }
    let optional = der::read_tlv(input, pos, end)?;
    if is_context_tag(optional.tag, number, false) {
        if version == 0 || !valid_implicit_bit_string(input, optional.cstart, optional.cend) { return None; }
        Some((Some(input.get(pos..optional.cend)?), optional.cend))
    } else { Some((None, pos)) }
}

/// Runtime result shape for an optional [3] Extensions wrapper.
pub type OptionalExtensionsResult<'a> = Option<(Option<&'a [u8]>, Option<&'a [u8]>, usize)>;

pub open spec fn view_optional_extensions_result(result: Option<(Option<&[u8]>, Option<&[u8]>, usize)>)
    -> Option<(Option<Seq<u8>>, Option<Seq<u8>>, nat)> {
    match result { Some((wrapper, sequence, next)) => Some((
        match wrapper { Some(bytes) => Some(bytes@), None => None },
        match sequence { Some(bytes) => Some(bytes@), None => None }, next as nat)), None => None }
}

/// RFC 5280 §4.1.2.9: parse one [3] EXPLICIT Extensions wrapper.
fn parse_optional_extensions(input: &[u8], pos: usize, end: usize, version: u8)
    -> (result: OptionalExtensionsResult<'_>)
    requires pos <= end, end <= input.len(), version <= 2
    ensures view_optional_extensions_result(result) == super::spec::optional_extensions(input@, pos as nat, end as nat, version as nat)
{
    if pos == end { return Some((None, None, pos)); }
    let optional = der::read_tlv(input, pos, end)?;
    if is_context_tag(optional.tag, 3, true) {
        if version != 2 { return None; }
        let (inner_start, inner_end) = der::expect_sequence(input, optional.cstart, optional.cend)?;
        let inner = der::read_tlv(input, optional.cstart, optional.cend)?;
        if inner.cstart != inner_start || inner.cend != inner_end || inner.cend != optional.cend { return None; }
        Some((Some(input.get(pos..optional.cend)?), Some(input.get(optional.cstart..inner.cend)?), optional.cend))
    } else { Some((None, None, pos)) }
}

/// RFC 5280 §4.1.2.8/.9: parse ordered optional IDs and [3] Extensions.
fn parse_optional_tail(input: &[u8], pos: usize, end: usize, version: u8)
    -> (result: Option<(OptionalTail<'_>, usize)>)
    requires pos <= end, end <= input.len(), version <= 2
    ensures match result {
        Some((tail, next)) => next == end && Some(tail@) == super::spec::parse_optional_tail(input@, pos as nat, end as nat, version as nat),
        None => super::spec::parse_optional_tail(input@, pos as nat, end as nat, version as nat) == None,
    }
{
    let (issuer_uid, after_issuer) = parse_optional_unique(input, pos, end, 1, version)?;
    let (subject_uid, after_subject) = parse_optional_unique(input, after_issuer, end, 2, version)?;
    let (extensions, extensions_sequence, after_extensions) = parse_optional_extensions(input, after_subject, end, version)?;
    if after_extensions != end { return None; }
    Some((OptionalTail { issuer_uid, subject_uid, extensions, extensions_sequence }, after_extensions))
}

/// RFC 5280 §4.1.2 TBSCertificate fields, in ASN.1 order. The complete
/// original TBS TLV and each opaque signed field are borrowed byte-for-byte.
pub fn parse_tbs_certificate(input: &[u8]) -> (result: Option<TbsCertificate<'_>>)
    ensures super::contract::parse_tbs_certificate_ensures(input@, super::contract::view_result(result))
{
    hide(super::spec::parse_prefix);
    hide(super::spec::parse_version);
    hide(super::spec::parse_serial);
    hide(super::spec::time_tlv);
    hide(super::spec::optional_unique);
    hide(super::spec::optional_extensions);
    hide(super::spec::valid_implicit_bit_string);
    hide(clazel_der::spec::read_tlv);
    hide(clazel_der::spec::read_integer);
    hide(clazel_der::spec::expect_sequence);
    let prefix = parse_prefix(input)?;
    let tbs_certificate_der = prefix.tbs_der;
    let mut pos = prefix.pos;
    let version = prefix.version;
    let contents_end = prefix.end;
    let serial_number_der = prefix.serial_der;

    let (signature, issuer_der, pos_after_issuer) = parse_signature_issuer(input, pos, contents_end)?;
    pos = pos_after_issuer;
    let (not_before, not_after, validity_end) = parse_validity(input, pos, contents_end)?;
    pos = validity_end;
    let (subject_der, subject_public_key_info_der, after_spki) = parse_subject_spki(input, pos, contents_end)?;
    pos = after_spki;

    let (optional_tail, final_cursor) = parse_optional_tail(input, pos, contents_end, version)?;
    if final_cursor != contents_end { return None; }
    Some(TbsCertificate {
        version, serial_number_der, signature, issuer_der, not_before, not_after,
        subject_der, subject_public_key_info_der,
        issuer_unique_id_der: optional_tail.issuer_uid,
        subject_unique_id_der: optional_tail.subject_uid,
        extensions_der: optional_tail.extensions,
        extensions_sequence_der: optional_tail.extensions_sequence,
        tbs_certificate_der,
    })
}

} // verus!
