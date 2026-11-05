//! Sanity examples for the independent transcription, evaluated by Verus on
//! small concrete inputs. Each proves one fact by running the spec: a value of
//! a clause's own example where it gives one, and a refusal for each kind of
//! encoding DER rules out. The certificates are built from parts below, so
//! that a refusal differs from an accepted input in the part that it tests.
//!
//! These check the transcription against the standards' examples. They do
//! not relate it to this crate's other transcription; no proof does yet.
//! Not read while writing this file: see the list in `independent/mod.rs`.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der::*;
#[cfg(verus_only)]
use super::extensions::*;
#[cfg(verus_only)]
use super::matching::*;
#[cfg(verus_only)]
use super::requirements::*;
#[cfg(verus_only)]
use super::structures::*;

verus! {

// ---------------------------------------------------------------------------
// Building blocks. Every part here is under 128 octets except where noted.
// ---------------------------------------------------------------------------

/// One encoding in the short form of length.
pub open spec fn tlv(tag: u8, contents: Seq<u8>) -> Seq<u8> {
    seq![tag, contents.len() as u8] + contents
}

/// One encoding with one long-form length octet, for 128 to 255 octets.
pub open spec fn tlv_long(tag: u8, contents: Seq<u8>) -> Seq<u8> {
    seq![tag, 0x81u8, contents.len() as u8] + contents
}

/// An encoding of any contents under 256 octets.
pub open spec fn tlv_any(tag: u8, contents: Seq<u8>) -> Seq<u8> {
    if contents.len() < 128 {
        tlv(tag, contents)
    } else {
        tlv_long(tag, contents)
    }
}

/// AlgorithmIdentifier with the object identifier 1.2.3.
pub open spec fn alg() -> Seq<u8> {
    tlv(0x30, tlv(0x06, seq![0x2Au8, 0x03u8]))
}

/// A Name of one RDN, CN=a.
pub open spec fn name_a() -> Seq<u8> {
    tlv(0x30, tlv(0x31, tlv(0x30, tlv(0x06, seq![0x55u8, 0x04u8, 0x03u8]) + tlv(0x13, seq![0x61u8]))))
}

/// The empty Name.
pub open spec fn name_empty() -> Seq<u8> {
    tlv(0x30, Seq::<u8>::empty())
}

/// Validity from 2025-01-01 to 2026-01-01.
pub open spec fn validity() -> Seq<u8> {
    tlv(0x30, tlv(0x17, seq![0x32u8, 0x35u8, 0x30u8, 0x31u8, 0x30u8, 0x31u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x5Au8]) + tlv(0x17, seq![0x32u8, 0x36u8, 0x30u8, 0x31u8, 0x30u8, 0x31u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x5Au8]))
}

/// SubjectPublicKeyInfo with one octet of key.
pub open spec fn spki() -> Seq<u8> {
    tlv(0x30, alg() + tlv(0x03, seq![0x00u8, 0x01u8]))
}

/// The signature: one octet.
pub open spec fn signature() -> Seq<u8> {
    tlv(0x03, seq![0x00u8, 0xABu8])
}

/// `version [0]` holding `v`.
pub open spec fn version_field(v: u8) -> Seq<u8> {
    tlv(0xA0, tlv(0x02, seq![v]))
}

/// A TBSCertificate from its optional head and tail, and a subject.
pub open spec fn tbs(head: Seq<u8>, subject: Seq<u8>, tail: Seq<u8>) -> Seq<u8> {
    tlv_any(
        0x30,
        head + tlv(0x02, seq![0x05u8]) + alg() + name_a() + validity() + subject + spki() + tail,
    )
}

/// A Certificate around a TBSCertificate.
pub open spec fn cert(to_be_signed: Seq<u8>) -> Seq<u8> {
    tlv_any(0x30, to_be_signed + alg() + signature())
}

/// `extensions [3]` around a list.
pub open spec fn exts(list: Seq<u8>) -> Seq<u8> {
    tlv_any(0xA3, tlv_any(0x30, list))
}

/// A v3 certificate with subject CN=a and these extensions.
pub open spec fn v3(list: Seq<u8>) -> Seq<u8> {
    cert(tbs(version_field(2), name_a(), exts(list)))
}

/// An extension from its last id-ce arc, optional critical field and value.
pub open spec fn ext(arc: u8, critical: Seq<u8>, value: Seq<u8>) -> Seq<u8> {
    tlv(0x30, tlv(0x06, seq![0x55u8, 0x1Du8, arc]) + critical + tlv(0x04, value))
}

/// `critical` encoded, TRUE.
pub open spec fn crit() -> Seq<u8> {
    tlv(0x01, seq![0xFFu8])
}

/// No `critical` field.
pub open spec fn plain() -> Seq<u8> {
    Seq::<u8>::empty()
}

/// subjectAltName with one dNSName.
pub open spec fn san(flag: Seq<u8>, dns: Seq<u8>) -> Seq<u8> {
    ext(17, flag, tlv(0x30, tlv(0x82, dns)))
}

/// A relying party that processes dNSName, directoryName and iPAddress.
pub open spec fn rp() -> RelyingParty {
    RelyingParty { recognized_name_forms: seq![2nat, 4nat, 7nat] }
}

/// `der` decodes and meets the prose's requirements.
pub open spec fn conforms(der: Seq<u8>) -> bool {
    match decode_certificate(der) {
        None => false,
        Some(c) => certificate_requirements(rp(), c),
    }
}

/// `der` decodes and matches `host` under `choices`.
pub open spec fn cert_matches(choices: MatchChoices, der: Seq<u8>, host: Seq<u8>) -> bool {
    match decode_certificate(der) {
        None => false,
        Some(c) => certificate_matches_host(choices, c, host),
    }
}

/// The wildcards a permissive client would take, for the MAY examples.
pub open spec fn permissive() -> MatchChoices {
    MatchChoices {
        wildcards: true,
        wildcard_beyond_left_most: true,
        wildcard_spans_labels: true,
        partial_label_wildcard: true,
        wildcard_in_a_label: true,
        cn_id: true,
        wildcard_may_be_empty: true,
        ignore_root_dot: true,
    }
}

/// Client answers with partial wildcards and nothing else.
pub open spec fn partial_only() -> MatchChoices {
    MatchChoices { partial_label_wildcard: true, ..cautious_choices() }
}

/// Client answers with the CN-ID fallback and nothing else.
pub open spec fn cn_fallback() -> MatchChoices {
    MatchChoices { cn_id: true, ..cautious_choices() }
}

// ---------------------------------------------------------------------------
// X.690
// ---------------------------------------------------------------------------

/// 8.1.3.5's example, L = 201 in the long form, and 10.1's refusals.
proof fn example_lengths() {
    assert(parse_length(seq![0x81u8, 0xC9u8], 0) == Some((201nat, 2nat))) by (compute_only);
    // Indefinite.
    assert(parse_length(seq![0x80u8], 0).is_none()) by (compute_only);
    // Long form where short would do.
    assert(parse_length(seq![0x81u8, 0x05u8, 0u8, 0u8, 0u8, 0u8, 0u8], 0).is_none())
        by (compute_only);
    // A leading zero octet.
    assert(parse_length(seq![0x82u8, 0x00u8, 0xC9u8], 0).is_none()) by (compute_only);
    // 8.1.3.5 c).
    assert(parse_length(seq![0xFFu8], 0).is_none()) by (compute_only);
}

/// 8.1.2: tag numbers.
proof fn example_identifiers() {
    assert(parse_identifier(seq![0x1Fu8, 0x1Fu8]) == Some(
        Identifier { class: 0, constructed: false, number: 31, size: 2 },
    )) by (compute_only);
    // 8.1.2.4.2 c).
    assert(parse_identifier(seq![0x1Fu8, 0x80u8, 0x1Fu8]).is_none()) by (compute_only);
    // The high form for a number that fits the low form.
    assert(parse_identifier(seq![0x1Fu8, 0x1Eu8]).is_none()) by (compute_only);
}

/// 8.2 and 11.1: "TRUE can be encoded as" `01 01 FF`; DER takes no other.
proof fn example_booleans() {
    assert(boolean_contents(seq![0xFFu8]) == Some(true)) by (compute_only);
    assert(boolean_contents(seq![0u8]) == Some(false)) by (compute_only);
    assert(boolean_contents(seq![0x01u8]).is_none()) by (compute_only);
}

/// 8.3: two's complement, smallest form.
proof fn example_integers() {
    assert(integer_contents(seq![0xFFu8]) == Some(-1int)) by (compute_only);
    assert(integer_contents(seq![0x00u8, 0x80u8]) == Some(128int)) by (compute_only);
    assert(integer_contents(seq![0x80u8]) == Some(-128int)) by (compute_only);
    assert(integer_contents(seq![0x00u8, 0x01u8]).is_none()) by (compute_only);
    assert(integer_contents(seq![0xFFu8, 0x80u8]).is_none()) by (compute_only);
    assert(integer_contents(Seq::<u8>::empty()).is_none()) by (compute_only);
}

/// 8.6: the example `03 07 04 0A 3B 5F 29 1C D0` of 8.6.4.2, and 11.2.
proof fn example_bit_strings() {
    assert(bit_string_contents(seq![0x04u8, 0x0Au8, 0x3Bu8, 0x5Fu8, 0x29u8, 0x1Cu8, 0xD0u8]).is_some())
        by (compute_only);
    // Unused bits set (11.2.1), too many unused bits (8.6.2.2), and an empty
    // string with unused bits (8.6.2.3).
    assert(bit_string_contents(seq![0x04u8, 0xD1u8]).is_none()) by (compute_only);
    assert(bit_string_contents(seq![0x08u8, 0x00u8]).is_none()) by (compute_only);
    assert(bit_string_contents(seq![0x01u8]).is_none()) by (compute_only);
    // digitalSignature and keyCertSign in a named bit list: bit 0 and 5.
    assert(bit_is_set(BitString { octets: seq![0x84u8], unused: 2 }, 0)) by (compute_only);
    assert(bit_is_set(BitString { octets: seq![0x84u8], unused: 2 }, 5)) by (compute_only);
    assert(!bit_is_set(BitString { octets: seq![0x84u8], unused: 2 }, 1)) by (compute_only);
    assert(no_trailing_zero_bits(BitString { octets: seq![0x84u8], unused: 2 })) by (compute_only);
    // 11.2.2: a trailing 0 bit left in.
    assert(!no_trailing_zero_bits(BitString { octets: seq![0x84u8], unused: 1 })) by (compute_only);
}

/// 8.19's example, {2 999 3}, with its contents `88 37 03`, and 8.19.2.
proof fn example_object_identifiers() {
    assert(object_identifier_contents(seq![0x88u8, 0x37u8, 0x03u8]) == Some(
        seq![2nat, 999nat, 3nat],
    )) by (compute_only);
    assert(object_identifier_contents(seq![0x55u8, 0x1Du8, 0x13u8]) == Some(id_ce_basic_constraints()))
        by (compute_only);
    // "the leading octet of the subidentifier shall not have the value 80".
    assert(object_identifier_contents(seq![0x2Au8, 0x80u8, 0x03u8]).is_none()) by (compute_only);
    // A subidentifier that never ends, and no subidentifiers.
    assert(object_identifier_contents(seq![0x2Au8, 0x83u8]).is_none()) by (compute_only);
    assert(object_identifier_contents(Seq::<u8>::empty()).is_none()) by (compute_only);
}

/// 11.6: the order, with the shorter encoding padded by zeros.
proof fn example_set_of_order() {
    assert(not_after(seq![0x01u8], seq![0x01u8, 0x00u8], 0)) by (compute_only);
    assert(not_after(seq![0x01u8, 0x00u8], seq![0x01u8], 0)) by (compute_only);
    assert(!not_after(seq![0x02u8], seq![0x01u8, 0xFFu8], 0)) by (compute_only);
}

/// 11.7 and 11.8's own valid and invalid representations.
proof fn example_times() {
    assert(generalized_time_contents(seq![0x31u8, 0x39u8, 0x39u8, 0x32u8, 0x30u8, 0x35u8, 0x32u8, 0x31u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x5Au8]).is_some()) by (compute_only);
    assert(generalized_time_contents(seq![0x31u8, 0x39u8, 0x39u8, 0x32u8, 0x30u8, 0x36u8, 0x32u8, 0x32u8, 0x31u8, 0x32u8, 0x33u8, 0x34u8, 0x32u8, 0x31u8, 0x5Au8]).is_some()) by (compute_only);
    assert(generalized_time_contents(seq![0x31u8, 0x39u8, 0x39u8, 0x32u8, 0x30u8, 0x37u8, 0x32u8, 0x32u8, 0x31u8, 0x33u8, 0x32u8, 0x31u8, 0x30u8, 0x30u8, 0x2Eu8, 0x33u8, 0x5Au8]).is_some()) by (compute_only);
    assert(generalized_time_contents(seq![0x31u8, 0x39u8, 0x39u8, 0x32u8, 0x30u8, 0x35u8, 0x32u8, 0x30u8, 0x32u8, 0x34u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x5Au8]).is_none()) by (compute_only);
    assert(generalized_time_contents(seq![0x31u8, 0x39u8, 0x39u8, 0x32u8, 0x30u8, 0x36u8, 0x32u8, 0x32u8, 0x31u8, 0x32u8, 0x33u8, 0x34u8, 0x32u8, 0x31u8, 0x2Eu8, 0x30u8, 0x5Au8]).is_none()) by (compute_only);
    assert(generalized_time_contents(seq![0x31u8, 0x39u8, 0x39u8, 0x32u8, 0x30u8, 0x37u8, 0x32u8, 0x32u8, 0x31u8, 0x33u8, 0x32u8, 0x31u8, 0x30u8, 0x30u8, 0x2Eu8, 0x33u8, 0x30u8, 0x5Au8]).is_none()) by (compute_only);
    // 11.7.4 no comma, 11.7.1 no local time, and February 30.
    assert(generalized_time_contents(seq![0x31u8, 0x39u8, 0x39u8, 0x32u8, 0x30u8, 0x37u8, 0x32u8, 0x32u8, 0x31u8, 0x33u8, 0x32u8, 0x31u8, 0x30u8, 0x30u8, 0x2Cu8, 0x33u8, 0x5Au8]).is_none()) by (compute_only);
    assert(generalized_time_contents(seq![0x31u8, 0x39u8, 0x39u8, 0x32u8, 0x30u8, 0x37u8, 0x32u8, 0x32u8, 0x31u8, 0x33u8, 0x32u8, 0x31u8, 0x30u8, 0x30u8]).is_none()) by (compute_only);
    assert(generalized_time_contents(seq![0x31u8, 0x39u8, 0x39u8, 0x32u8, 0x30u8, 0x32u8, 0x33u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x5Au8]).is_none()) by (compute_only);
    assert(utc_time_contents(seq![0x39u8, 0x32u8, 0x30u8, 0x35u8, 0x32u8, 0x31u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x5Au8]).is_some()) by (compute_only);
    assert(utc_time_contents(seq![0x39u8, 0x32u8, 0x30u8, 0x36u8, 0x32u8, 0x32u8, 0x31u8, 0x32u8, 0x33u8, 0x34u8, 0x32u8, 0x31u8, 0x5Au8]).is_some()) by (compute_only);
    assert(utc_time_contents(seq![0x39u8, 0x32u8, 0x30u8, 0x37u8, 0x32u8, 0x32u8, 0x31u8, 0x33u8, 0x32u8, 0x31u8, 0x30u8, 0x30u8, 0x5Au8]).is_some()) by (compute_only);
    assert(utc_time_contents(seq![0x39u8, 0x32u8, 0x30u8, 0x35u8, 0x32u8, 0x30u8, 0x32u8, 0x34u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x5Au8]).is_none()) by (compute_only);
    assert(utc_time_contents(seq![0x39u8, 0x32u8, 0x30u8, 0x37u8, 0x32u8, 0x32u8, 0x31u8, 0x33u8, 0x32u8, 0x31u8, 0x5Au8]).is_none()) by (compute_only);
    // X.509 7.2.1: the two-digit year's two ranges.
    assert(utc_time_contents(seq![0x34u8, 0x39u8, 0x30u8, 0x31u8, 0x30u8, 0x31u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x5Au8]).unwrap().year == 2049) by (compute_only);
    assert(utc_time_contents(seq![0x35u8, 0x30u8, 0x30u8, 0x31u8, 0x30u8, 0x31u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x5Au8]).unwrap().year == 1950) by (compute_only);
    // 2000 was a leap year, 1900 no.
    assert(utc_time_contents(seq![0x30u8, 0x30u8, 0x30u8, 0x32u8, 0x32u8, 0x39u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x5Au8]).is_some()) by (compute_only);
    assert(generalized_time_contents(seq![0x31u8, 0x39u8, 0x30u8, 0x30u8, 0x30u8, 0x32u8, 0x32u8, 0x39u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x30u8, 0x5Au8]).is_none()) by (compute_only);
}

// ---------------------------------------------------------------------------
// X.509 structures
// ---------------------------------------------------------------------------

/// A v3 certificate with a subjectAltName decodes, and its fields are the
/// parts it was built from.
proof fn example_certificate_decodes() {
    assert(decode_certificate(v3(san(plain(), seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))).is_some()) by (compute_only);
    assert(decode_certificate(v3(san(plain(), seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))).unwrap().to_be_signed.version
        == 2) by (compute_only);
    assert(decode_certificate(
        v3(san(plain(), seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8])),
    ).unwrap().to_be_signed.serial_number == 5) by (compute_only);
    assert(decode_certificate(
        v3(san(plain(), seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8])),
    ).unwrap().to_be_signed.issuer.rdn_sequence.len() == 1) by (compute_only);
    assert(decode_certificate(
        v3(san(plain(), seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8])),
    ).unwrap().to_be_signed.extensions.unwrap().len() == 1) by (compute_only);
    assert(decode_certificate(v3(san(plain(), seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))).unwrap().signature.octets.len()
        == 1) by (compute_only);
    assert(additions_absent(decode_certificate(v3(san(plain(), seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))).unwrap()))
        by (compute_only);
}

/// A v1 certificate has no `version` component.
proof fn example_default_version() {
    assert(decode_certificate(cert(tbs(plain(), name_a(), plain()))).unwrap().to_be_signed.version
        == 0) by (compute_only);
    assert(conforms(cert(tbs(plain(), name_a(), plain())))) by (compute_only);
}

/// `GeneralSubtrees` with a dNSName base and this `minimum` content.
pub open spec fn subtree_with_minimum(minimum: u8) -> Seq<u8> {
    tlv(0x30, tlv(0xA0, tlv(0x30, tlv(0x82, seq![0x61u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8]) + tlv(0x80, seq![minimum]))))
}

/// X.690 11.5: an explicit DEFAULT value is refused, in all four places the
/// certificate has one.
proof fn example_explicit_defaults_refused() {
    // version [0] v1.
    assert(decode_certificate(cert(tbs(version_field(0), name_a(), plain()))).is_none())
        by (compute_only);
    // critical FALSE.
    assert(decode_certificate(v3(san(tlv(0x01, seq![0x00u8]), seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))).is_none())
        by (compute_only);
    // cA FALSE.
    assert(decode_certificate(v3(ext(19, plain(), tlv(0x30, tlv(0x01, seq![0x00u8]))))).is_none())
        by (compute_only);
    // minimum 0, in a GeneralSubtree.
    assert(decode_certificate(v3(ext(30, crit(), subtree_with_minimum(0)))).is_none())
        by (compute_only);
}

/// The same places with their other value are accepted.
proof fn example_non_default_values_accepted() {
    assert(decode_certificate(cert(tbs(version_field(1), name_a(), plain()))).is_some())
        by (compute_only);
    assert(decode_certificate(v3(ext(19, crit(), tlv(0x30, crit())))).is_some()) by (compute_only);
    assert(decode_certificate(v3(ext(30, crit(), subtree_with_minimum(1)))).is_some())
        by (compute_only);
}

/// A certificate that the refusals below start from.
pub open spec fn good() -> Seq<u8> {
    v3(san(plain(), seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))
}

/// Refusals of the whole encoding.
proof fn example_encoding_refusals() {
    // Octets after the encoding.
    assert(decode_certificate(good() + seq![0x00u8]).is_none()) by (compute_only);
    // Cut short.
    assert(decode_certificate(good().subrange(0, good().len() - 1)).is_none()) by (compute_only);
    // No signature.
    assert(decode_certificate(
        tlv_any(0x30, tbs(version_field(2), name_a(), plain()) + alg()),
    ).is_none()) by (compute_only);
    // `Extensions` is SIZE (1..MAX).
    assert(decode_certificate(cert(tbs(version_field(2), name_a(), exts(plain())))).is_none())
        by (compute_only);
    // A BOOLEAN TRUE that is not all ones.
    assert(decode_certificate(v3(san(tlv(0x01, seq![0x01u8]), seq![0x61u8]))).is_none())
        by (compute_only);
    // An extension value with octets after its one encoding.
    assert(decode_certificate(v3(ext(19, plain(), tlv(0x30, plain()) + seq![0x00u8]))).is_none())
        by (compute_only);
    // A non-IA5 dNSName.
    assert(decode_certificate(v3(san(plain(), seq![0xC3u8, 0xA9u8]))).is_none()) by (compute_only);
    // `GeneralNames` is SIZE (1..MAX).
    assert(decode_certificate(v3(ext(17, plain(), tlv(0x30, plain())))).is_none())
        by (compute_only);
    // AuthorityKeyIdentifier: a serial number without an issuer.
    assert(decode_certificate(v3(ext(35, plain(), tlv(0x30, tlv(0x82, seq![0x01u8]))))).is_none())
        by (compute_only);
    // NameConstraintsSyntax with neither component.
    assert(decode_certificate(v3(ext(30, plain(), tlv(0x30, plain())))).is_none())
        by (compute_only);
    // pathLenConstraint below zero.
    assert(decode_certificate(
        v3(ext(19, crit(), tlv(0x30, crit() + tlv(0x02, seq![0xFFu8])))),
    ).is_none()) by (compute_only);
    // A keyUsage with a trailing 0 bit (X.690 11.2.2).
    assert(decode_certificate(v3(ext(15, crit(), tlv(0x03, seq![0x01u8, 0x84u8])))).is_none())
        by (compute_only);
}

/// One attribute of an RDN, with an attribute type ending in `arc`.
pub open spec fn attribute(arc: u8) -> Seq<u8> {
    tlv(0x30, tlv(0x06, seq![0x55u8, 0x04u8, arc]) + tlv(0x13, seq![0x61u8]))
}

/// X.690 11.6 in a Name: the two attributes of an RDN out of order.
proof fn example_rdn_order() {
    assert(decode_name(
        parse_single(tlv(0x30, tlv(0x31, attribute(0x03) + attribute(0x0A)))).unwrap(),
    ).is_some()) by (compute_only);
    assert(decode_name(
        parse_single(tlv(0x30, tlv(0x31, attribute(0x0A) + attribute(0x03)))).unwrap(),
    ).is_none()) by (compute_only);
    // SIZE (1..MAX) on an RDN.
    assert(decode_name(parse_single(tlv(0x30, tlv(0x31, plain()))).unwrap()).is_none())
        by (compute_only);
}

/// A v1 TBSCertificate.
pub open spec fn tbs_v1() -> Seq<u8> {
    tbs(plain(), name_a(), plain())
}

/// 6.2.1's WITH COMPONENTS: altSignature alone is not a value; both are, and
/// 7.2.1 then refuses them; an unknown addition is kept.
proof fn example_alternative_signature() {
    assert(decode_certificate(tlv_any(0x30, tbs_v1() + alg() + signature() + signature())).is_none())
        by (compute_only);
    assert(decode_certificate(
        tlv_any(0x30, tbs_v1() + alg() + signature() + alg() + signature()),
    ).is_some()) by (compute_only);
    assert(!conforms(tlv_any(0x30, tbs_v1() + alg() + signature() + alg() + signature())))
        by (compute_only);
    assert(decode_certificate(
        tlv_any(0x30, tbs_v1() + alg() + signature() + tlv(0x85, seq![0x01u8])),
    ).unwrap().additions.len() == 1) by (compute_only);
    assert(!additions_absent(
        decode_certificate(
            tlv_any(0x30, tbs_v1() + alg() + signature() + tlv(0x85, seq![0x01u8])),
        ).unwrap(),
    )) by (compute_only);
}

// ---------------------------------------------------------------------------
// The prose's requirements
// ---------------------------------------------------------------------------

/// A plain certificate conforms.
proof fn example_conforming() {
    assert(conforms(good())) by (compute_only);
}

/// `issuerUniqueIdentifier` with one bit-string octet.
pub open spec fn unique_id() -> Seq<u8> {
    tlv(0x81, seq![0x00u8, 0x01u8])
}

/// An AlgorithmIdentifier other than `alg()`.
pub open spec fn other_alg() -> Seq<u8> {
    tlv(0x30, tlv(0x06, seq![0x2Au8, 0x04u8]))
}

/// 7.2.1: version rules, and the two algorithms.
proof fn example_version_requirements() {
    assert(!conforms(cert(tbs(version_field(1), name_a(), exts(san(plain(), seq![0x61u8]))))))
        by (compute_only);
    assert(!conforms(cert(tbs(version_field(3), name_a(), plain())))) by (compute_only);
    assert(decode_certificate(cert(tbs(plain(), name_a(), unique_id()))).is_some())
        by (compute_only);
    assert(!conforms(cert(tbs(plain(), name_a(), unique_id())))) by (compute_only);
    assert(conforms(cert(tbs(version_field(1), name_a(), unique_id())))) by (compute_only);
    assert(!conforms(tlv_any(0x30, tbs_v1() + other_alg() + signature()))) by (compute_only);
}

/// 7.2.1: an empty subject needs a critical subjectAltName.
proof fn example_empty_subject() {
    assert(!conforms(cert(tbs(version_field(2), name_empty(), exts(san(plain(), seq![0x61u8]))))))
        by (compute_only);
    assert(conforms(cert(tbs(version_field(2), name_empty(), exts(san(crit(), seq![0x61u8]))))))
        by (compute_only);
}

/// A value with an element no edition defines.
pub open spec fn added() -> Seq<u8> {
    tlv(0x30, tlv(0x85, seq![0x01u8]))
}

/// A subjectAltName value holding only a URI.
pub open spec fn uri_only() -> Seq<u8> {
    tlv(0x30, tlv(0x86, seq![0x61u8]))
}

/// 7.3 b), 7.3 a) and clause 9's one instance.
proof fn example_extension_requirements() {
    // id-ce 99 is not one this decoder knows.
    assert(!conforms(v3(ext(99, crit(), seq![0x05u8, 0x00u8])))) by (compute_only);
    assert(conforms(v3(ext(99, plain(), seq![0x05u8, 0x00u8])))) by (compute_only);
    // Two subjectAltNames, and two extensions unknown to the Specification.
    assert(!conforms(v3(san(plain(), seq![0x61u8]) + san(plain(), seq![0x62u8])))) by (compute_only);
    assert(conforms(
        v3(ext(99, plain(), seq![0x05u8, 0x00u8]) + ext(99, plain(), seq![0x05u8, 0x00u8])),
    )) by (compute_only);
    // 9.2.2.2 "always ... non-critical".
    assert(!conforms(v3(ext(14, crit(), tlv(0x04, seq![0x01u8]))))) by (compute_only);
    // 7.3: unrecognized elements: ignored when not critical, refused when
    // critical.
    assert(conforms(v3(ext(19, plain(), added())))) by (compute_only);
    assert(!conforms(v3(ext(19, crit(), added())))) by (compute_only);
    // 9.3.2.1: a critical subjectAltName with no recognized name form, and a
    // non-critical one.
    assert(!conforms(v3(ext(17, crit(), uri_only())))) by (compute_only);
    assert(conforms(v3(ext(17, plain(), uri_only())))) by (compute_only);
}

/// basicConstraints with cA TRUE.
pub open spec fn ca() -> Seq<u8> {
    ext(19, crit(), tlv(0x30, crit()))
}

/// keyUsage with keyCertSign alone: bit 5, so two unused bits of `04`.
pub open spec fn key_cert_sign() -> Seq<u8> {
    ext(15, crit(), tlv(0x03, seq![0x02u8, 0x04u8]))
}

/// nameConstraints permitting a subtree of this context tag.
pub open spec fn constraint(tag: u8) -> Seq<u8> {
    ext(30, crit(), tlv(0x30, tlv(0xA0, tlv(0x30, tlv(tag, seq![0x61u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8])))))
}

/// 9.2.2.3, 9.3.2.1 and 9.4.2.
proof fn example_constraint_requirements() {
    assert(conforms(v3(ca() + key_cert_sign()))) by (compute_only);
    assert(!conforms(v3(key_cert_sign()))) by (compute_only);
    // cA TRUE not flagged critical.
    assert(!conforms(v3(ext(19, plain(), tlv(0x30, crit()))))) by (compute_only);
    // pathLenConstraint without cA.
    assert(!conforms(v3(ext(19, plain(), tlv(0x30, tlv(0x02, seq![0x00u8])))))) by (compute_only);
    // nameConstraints outside a CA certificate.
    assert(!conforms(v3(constraint(0x82)))) by (compute_only);
    assert(conforms(v3(ca() + constraint(0x82)))) by (compute_only);
    // A critical constraint on a name form rp() does not process.
    assert(!conforms(v3(ca() + constraint(0x81)))) by (compute_only);
    // iPAddress of the wrong size.
    assert(!conforms(v3(ext(17, plain(), tlv(0x30, tlv(0x87, seq![0x01u8])))))) by (compute_only);
    assert(conforms(v3(ext(17, plain(), tlv(0x30, tlv(0x87, seq![1u8, 2u8, 3u8, 4u8]))))))
        by (compute_only);
}

/// The attribute CN=a, decoded.
pub open spec fn cn_attribute() -> AttributeTypeAndValue {
    decode_attribute_type_and_value(parse_single(attribute(0x03)).unwrap()).unwrap()
}

/// X.501 9.3 and the dNSName syntax of 9.3.2.1.
proof fn example_name_rules() {
    assert(dns_name_syntax(seq![0x77u8, 0x77u8, 0x77u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8])) by (compute_only);
    assert(!dns_name_syntax(seq![0x2Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8])) by (compute_only);
    assert(!dns_name_syntax(seq![0x61u8, 0x2Eu8, 0x2Eu8, 0x62u8])) by (compute_only);
    assert(rdn_types_distinct(seq![cn_attribute()], 0)) by (compute_only);
    assert(!rdn_types_distinct(seq![cn_attribute(), cn_attribute()], 0)) by (compute_only);
}

// ---------------------------------------------------------------------------
// RFC 6125
// ---------------------------------------------------------------------------

/// 6.4.1's example, and a label that differs.
proof fn example_traditional_names() {
    assert(domain_name_matches(cautious_choices(), seq![0x77u8, 0x77u8, 0x77u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8], seq![0x57u8, 0x57u8, 0x57u8, 0x2Eu8, 0x45u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x43u8, 0x6Fu8, 0x6Du8]))
        by (compute_only);
    assert(!domain_name_matches(cautious_choices(), seq![0x77u8, 0x77u8, 0x77u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8], seq![0x77u8, 0x77u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))
        by (compute_only);
    assert(!domain_name_matches(cautious_choices(), seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8], seq![0x77u8, 0x77u8, 0x77u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))
        by (compute_only);
    assert(!domain_name_matches(cautious_choices(), seq![0x61u8, 0x2Eu8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8], seq![0x61u8, 0x2Eu8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8])) by (compute_only);
    // A trailing dot differs unless the client ignores it.
    assert(!domain_name_matches(cautious_choices(), seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8], seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Eu8]))
        by (compute_only);
    assert(domain_name_matches(permissive(), seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8], seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Eu8]))
        by (compute_only);
    // 6.4.2: A-labels compare as ASCII.
    assert(domain_name_matches(
        cautious_choices(),
        seq![0x78u8, 0x6Eu8, 0x2Du8, 0x2Du8, 0x62u8, 0x63u8, 0x68u8, 0x65u8, 0x72u8, 0x2Du8, 0x6Bu8, 0x76u8, 0x61u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8],
        seq![0x58u8, 0x4Eu8, 0x2Du8, 0x2Du8, 0x42u8, 0x43u8, 0x48u8, 0x45u8, 0x52u8, 0x2Du8, 0x4Bu8, 0x56u8, 0x41u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8],
    )) by (compute_only);
}

/// A client that takes no wildcards.
pub open spec fn no_wildcards() -> MatchChoices {
    MatchChoices { wildcards: false, ..cautious_choices() }
}

/// 6.4.3 rule 2's examples.
proof fn example_whole_label_wildcard() {
    assert(domain_name_matches(cautious_choices(), seq![0x2Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8], seq![0x66u8, 0x6Fu8, 0x6Fu8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))
        by (compute_only);
    assert(!domain_name_matches(cautious_choices(), seq![0x2Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8], seq![0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))
        by (compute_only);
    assert(!domain_name_matches(cautious_choices(), seq![0x2Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8], seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))
        by (compute_only);
    assert(domain_name_matches(permissive(), seq![0x2Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8], seq![0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))
        by (compute_only);
    // 7.2: `*` may fill the left-most label over A-labels.
    assert(domain_name_matches(
        cautious_choices(),
        seq![0x2Au8, 0x2Eu8, 0x78u8, 0x6Eu8, 0x2Du8, 0x2Du8, 0x6Bu8, 0x63u8, 0x72u8, 0x79u8, 0x36u8, 0x74u8, 0x6Au8, 0x6Bu8, 0x6Fu8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Fu8, 0x72u8, 0x67u8],
        seq![0x61u8, 0x2Eu8, 0x78u8, 0x6Eu8, 0x2Du8, 0x2Du8, 0x6Bu8, 0x63u8, 0x72u8, 0x79u8, 0x36u8, 0x74u8, 0x6Au8, 0x6Bu8, 0x6Fu8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Fu8, 0x72u8, 0x67u8],
    )) by (compute_only);
    assert(!domain_name_matches(no_wildcards(), seq![0x2Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8], seq![0x66u8, 0x6Fu8, 0x6Fu8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))
        by (compute_only);
    // No public suffix rule in 6.4.3.
    assert(domain_name_matches(cautious_choices(), seq![0x2Au8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8], seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))
        by (compute_only);
    // The reference never holds a wildcard.
    assert(!domain_name_matches(cautious_choices(), seq![0x2Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8], seq![0x2Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))
        by (compute_only);
}

/// 6.4.3 rule 1's example.
proof fn example_wildcard_position() {
    assert(!domain_name_matches(
        cautious_choices(),
        seq![0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x2Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8],
        seq![0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8],
    )) by (compute_only);
    assert(domain_name_matches(permissive(), seq![0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x2Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8], seq![0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8]))
        by (compute_only);
}

/// 6.4.3 rule 3's examples.
proof fn example_partial_wildcards() {
    assert(domain_name_matches(partial_only(), seq![0x62u8, 0x61u8, 0x7Au8, 0x2Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8], seq![0x62u8, 0x61u8, 0x7Au8, 0x31u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8]))
        by (compute_only);
    assert(domain_name_matches(partial_only(), seq![0x2Au8, 0x62u8, 0x61u8, 0x7Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8], seq![0x66u8, 0x6Fu8, 0x6Fu8, 0x62u8, 0x61u8, 0x7Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8]))
        by (compute_only);
    assert(domain_name_matches(partial_only(), seq![0x62u8, 0x2Au8, 0x7Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8], seq![0x62u8, 0x75u8, 0x7Au8, 0x7Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8]))
        by (compute_only);
    assert(!domain_name_matches(partial_only(), seq![0x62u8, 0x61u8, 0x7Au8, 0x2Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8], seq![0x62u8, 0x61u8, 0x72u8, 0x31u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8]))
        by (compute_only);
    assert(!domain_name_matches(cautious_choices(), seq![0x62u8, 0x61u8, 0x7Au8, 0x2Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8], seq![0x62u8, 0x61u8, 0x7Au8, 0x31u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8]))
        by (compute_only);
    // The wildcard standing for nothing is a client's choice.
    assert(!domain_name_matches(partial_only(), seq![0x62u8, 0x61u8, 0x7Au8, 0x2Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8], seq![0x62u8, 0x61u8, 0x7Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8]))
        by (compute_only);
    assert(domain_name_matches(permissive(), seq![0x62u8, 0x61u8, 0x7Au8, 0x2Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8], seq![0x62u8, 0x61u8, 0x7Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Eu8, 0x65u8, 0x74u8]))
        by (compute_only);
    // Embedded in an A-label (7.2's example), and two in one label.
    assert(!domain_name_matches(
        partial_only(),
        seq![0x78u8, 0x6Eu8, 0x2Du8, 0x2Du8, 0x6Bu8, 0x63u8, 0x72u8, 0x79u8, 0x36u8, 0x74u8, 0x6Au8, 0x6Bu8, 0x6Fu8, 0x2Au8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Fu8, 0x72u8, 0x67u8],
        seq![0x78u8, 0x6Eu8, 0x2Du8, 0x2Du8, 0x6Bu8, 0x63u8, 0x72u8, 0x79u8, 0x36u8, 0x74u8, 0x6Au8, 0x6Bu8, 0x6Fu8, 0x61u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x6Fu8, 0x72u8, 0x67u8],
    )) by (compute_only);
    assert(!domain_name_matches(partial_only(), seq![0x66u8, 0x2Au8, 0x62u8, 0x2Au8, 0x72u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8], seq![0x66u8, 0x6Fu8, 0x6Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))
        by (compute_only);
}

/// 6.3 over a certificate, and 6.4.4.
proof fn example_certificates() {
    assert(cert_matches(cautious_choices(), v3(san(plain(), seq![0x77u8, 0x77u8, 0x77u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8])), seq![0x77u8, 0x77u8, 0x77u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))
        by (compute_only);
    assert(!cert_matches(cautious_choices(), v3(san(plain(), seq![0x77u8, 0x77u8, 0x77u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8])), seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]))
        by (compute_only);
    // Any presented identifier of several may match.
    assert(cert_matches(
        cautious_choices(),
        v3(ext(17, plain(), tlv(0x30, tlv(0x82, seq![0x61u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8]) + tlv(0x82, seq![0x62u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8])))),
        seq![0x62u8, 0x2Eu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8],
    )) by (compute_only);
    // A CN of `a`, with no subjectAltName: only a CN-ID client matches.
    assert(!cert_matches(cautious_choices(), cert(tbs_v1()), seq![0x61u8])) by (compute_only);
    assert(cert_matches(cn_fallback(), cert(tbs_v1()), seq![0x61u8])) by (compute_only);
    // 6.4.4: a DNS-ID or a URI-ID stops the fallback; an iPAddress does not.
    assert(!cert_matches(cn_fallback(), v3(san(plain(), seq![0x62u8])), seq![0x61u8])) by (compute_only);
    assert(!cert_matches(cn_fallback(), v3(ext(17, plain(), uri_only())), seq![0x61u8]))
        by (compute_only);
    assert(cert_matches(
        cn_fallback(),
        v3(ext(17, plain(), tlv(0x30, tlv(0x87, seq![1u8, 2u8, 3u8, 4u8])))),
        seq![0x61u8],
    )) by (compute_only);
}

} // verus!
