//! One concrete input for each disagreement `equivalence.rs` and
//! `equivalence_matching.rs` exclude, evaluated by Verus: each exclusion is an
//! input the two really decide differently, not a guess.
//!
//! Not here: condition 11 and the pairing of `*.com` with the ICANN table
//! (each needs a large evaluation; `tests/` cover the crate's side), and
//! conditions 5, 8 and 9, which are predicates of `requirements.rs` over a
//! whole certificate.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der as i;
#[cfg(verus_only)]
use super::equivalence::*;
#[cfg(verus_only)]
use super::equivalence_der::*;
#[cfg(verus_only)]
use super::equivalence_name::*;
#[cfg(verus_only)]
use super::equivalence_structures::*;
#[cfg(verus_only)]
use super::equivalence_tbs::*;
#[cfg(verus_only)]
use super::equivalence_time::*;
#[cfg(verus_only)]
use super::extensions as e;
#[cfg(verus_only)]
use super::matching as m;
#[cfg(verus_only)]
use super::requirements as r;
#[cfg(verus_only)]
use super::structures as s;
#[cfg(verus_only)]
use crate::certificate::spec as c;
#[cfg(verus_only)]
use crate::extensions::spec as x;
#[cfg(verus_only)]
use crate::signature_algorithm::spec as g;
#[cfg(verus_only)]
use crate::spec as h;
#[cfg(verus_only)]
use crate::spki::spec as k;
#[cfg(verus_only)]
use crate::tbs::spec as t;
#[cfg(verus_only)]
use crate::time::spec as tm;
#[cfg(verus_only)]
use clazel_der::spec as d;

verus! {

/// Condition 1: universal 0 with empty contents.
pub open spec fn reserved_tag() -> Seq<u8> {
    seq![0x00u8, 0x00]
}

/// Condition 1.
pub proof fn example_reserved_tag()
    ensures
        d::read_tlv(reserved_tag(), 0, 2) is Some,
        i::parse_tlv(reserved_tag()) is None,
{
    assert(d::read_tlv(reserved_tag(), 0, 2) is Some) by (compute_only);
    assert(i::parse_tlv(reserved_tag()) is None) by (compute_only);
}

/// `20161231235960Z`.
pub open spec fn leap_second() -> Seq<u8> {
    seq![0x32u8, 0x30, 0x31, 0x36, 0x31, 0x32, 0x33, 0x31, 0x32, 0x33, 0x35, 0x39, 0x36, 0x30, 0x5A]
}

/// `00000101000000Z`.
pub open spec fn year_zero() -> Seq<u8> {
    seq![0x30u8, 0x30, 0x30, 0x30, 0x30, 0x31, 0x30, 0x31, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x5A]
}

/// `20250101000000.5Z`.
pub open spec fn with_fraction() -> Seq<u8> {
    seq![
        0x32u8, 0x30, 0x32, 0x35, 0x30, 0x31, 0x30, 0x31, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x2E,
        0x35, 0x5A
    ]
}

/// The first 14 octets of a time are digits.
pub proof fn lemma_time_digits(c: Seq<u8>)
    requires
        i::digits_at(c, 0, 14),
    ensures
        tm::digits_only(c, 0, 14),
{
    lemma_digits_at(c, 0, 14);
}

/// Condition 2: `time/spec.rs` reads second 60 at 23:59, `der.rs` does not.
pub proof fn example_leap_second()
    ensures
        tm::decode_time(tm::TimeKind::Generalized, leap_second()) is Some,
        i::generalized_time_contents(leap_second()) is None,
{
    let c = leap_second();
    assert(i::generalized_time_contents(leap_second()) is None) by (compute_only);
    assert(i::digits_at(leap_second(), 0, 14)) by (compute_only);
    lemma_time_digits(c);
    lemma_digits_sub(c, 14, 0, 4);
    lemma_digits_sub(c, 14, 4, 2);
    lemma_digits_sub(c, 14, 6, 2);
    lemma_digits_sub(c, 14, 8, 2);
    lemma_digits_sub(c, 14, 10, 2);
    lemma_digits_sub(c, 14, 12, 2);
    lemma_digits_sub(c, 14, 0, 2);
    lemma_digits_sub(c, 14, 2, 2);
    lemma_four_digits(c);
    lemma_two_digits(c, 4);
    lemma_two_digits(c, 6);
    lemma_two_digits(c, 8);
    lemma_two_digits(c, 10);
    lemma_two_digits(c, 12);
    assert(i::two_digits(leap_second(), 0) == 20) by (compute_only);
    assert(i::two_digits(leap_second(), 2) == 16) by (compute_only);
    assert(i::two_digits(leap_second(), 4) == 12) by (compute_only);
    assert(i::two_digits(leap_second(), 6) == 31) by (compute_only);
    assert(i::two_digits(leap_second(), 8) == 23) by (compute_only);
    assert(i::two_digits(leap_second(), 10) == 59) by (compute_only);
    assert(i::two_digits(leap_second(), 12) == 60) by (compute_only);
}

/// Condition 10: `der.rs` reads a fraction and the year 0000.
pub proof fn example_fraction_and_year_zero()
    ensures
        i::generalized_time_contents(with_fraction()) is Some,
        tm::decode_time(tm::TimeKind::Generalized, with_fraction()) is None,
        i::generalized_time_contents(year_zero()) is Some,
        tm::decode_time(tm::TimeKind::Generalized, year_zero()) is None,
{
    let c = year_zero();
    assert(i::generalized_time_contents(with_fraction()) is Some) by (compute_only);
    assert(with_fraction().len() != 15) by (compute_only);
    assert(i::generalized_time_contents(year_zero()) is Some) by (compute_only);
    assert(i::digits_at(year_zero(), 0, 14)) by (compute_only);
    lemma_time_digits(c);
    lemma_digits_sub(c, 14, 0, 4);
    lemma_digits_sub(c, 14, 0, 2);
    lemma_digits_sub(c, 14, 2, 2);
    lemma_four_digits(c);
    assert(i::two_digits(year_zero(), 0) == 0) by (compute_only);
    assert(i::two_digits(year_zero(), 2) == 0) by (compute_only);
    assert(c.len() == 15 && c[14] == 0x5A);
}

/// `parameters` and one more component.
pub open spec fn algorithm_with_addition() -> Seq<u8> {
    seq![0x30u8, 0x08, 0x06, 0x02, 0x2A, 0x03, 0x05, 0x00, 0x05, 0x00]
}

/// Condition 4.
pub proof fn example_addition()
    ensures
        s::decode_algorithm_identifier(i::parse_tlv(algorithm_with_addition())->Some_0) is Some,
        s::decode_algorithm_identifier(i::parse_tlv(algorithm_with_addition())->Some_0)->Some_0.additions.len() == 1,
        c::parse_algorithm_identifier(algorithm_with_addition(), 0, 10) is None,
{
    assert(s::decode_algorithm_identifier(i::parse_tlv(algorithm_with_addition())->Some_0) is Some)
        by (compute_only);
    assert(s::decode_algorithm_identifier(i::parse_tlv(algorithm_with_addition())->Some_0)->Some_0.additions.len()
        == 1) by (compute_only);
    assert(c::parse_algorithm_identifier(algorithm_with_addition(), 0, 10) is None) by (compute_only);
}

/// Tag number 16384.
pub open spec fn large_tag() -> Seq<u8> {
    seq![0x9Fu8, 0x81, 0x80, 0x00, 0x00]
}

/// A first subidentifier of 2^71.
pub open spec fn large_arc() -> Seq<u8> {
    seq![0x82u8, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00]
}

/// Condition 6.
pub proof fn example_limits()
    ensures
        i::parse_tlv(large_tag()) is Some,
        d::read_tlv(large_tag(), 0, 5) is None,
        i::object_identifier_contents(large_arc()) is Some,
        d::oid_components(large_arc()) is None,
{
    assert(i::parse_tlv(large_tag()) is Some) by (compute_only);
    assert(d::read_tlv(large_tag(), 0, 5) is None) by (compute_only);
    assert(i::object_identifier_contents(large_arc()) is Some) by (compute_only);
    assert(d::oid_components(large_arc()) is None) by (compute_only);
}

/// The serial number -1.
pub open spec fn negative_serial() -> Seq<u8> {
    seq![0x02u8, 0x01, 0xFF]
}

/// The serial number 2^159: 20 octets of value, 21 of contents.
pub open spec fn padded_serial() -> Seq<u8> {
    seq![
        0x02u8, 0x15, 0x00, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
    ]
}

/// Condition 7, with its boundary: `tbs/spec.rs` counts contents octets, so a
/// value of 20 octets with its top bit set is refused.
pub proof fn example_serial()
    ensures
        i::decode_integer(i::parse_tlv(negative_serial())->Some_0) == Some(-1int),
        t::parse_serial(negative_serial(), 0, 3) is None,
        i::decode_integer(i::parse_tlv(padded_serial())->Some_0) is Some,
        t::parse_serial(padded_serial(), 0, 23) is None,
{
    assert(i::decode_integer(i::parse_tlv(negative_serial())->Some_0) == Some(-1int)) by (compute_only);
    assert(t::parse_serial(negative_serial(), 0, 3) is None) by (compute_only);
    assert(i::decode_integer(i::parse_tlv(padded_serial())->Some_0) is Some) by (compute_only);
    assert(t::parse_serial(padded_serial(), 0, 23) is None) by (compute_only);
}

/// `rsaEncryption` with `parameters` absent and an empty key.
pub open spec fn rsa_without_null() -> Seq<u8> {
    seq![
        0x30u8, 0x10, 0x30, 0x0B, 0x06, 0x09, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x01, 0x01,
        0x03, 0x01, 0x00
    ]
}

/// Condition 12.
pub proof fn example_rsa_profile()
    ensures
        s::decode_subject_public_key_info(i::parse_tlv(rsa_without_null())->Some_0) is Some,
        k::parse_subject_public_key_info(rsa_without_null()) is None,
{
    assert(s::decode_subject_public_key_info(i::parse_tlv(rsa_without_null())->Some_0) is Some)
        by (compute_only);
    assert(k::parse_subject_public_key_info(rsa_without_null()) is None) by (compute_only);
}

/// Two extensions with the `extnId` 1.2.3.
pub open spec fn duplicate_extensions() -> Seq<u8> {
    seq![
        0x30u8, 0x12, 0x30, 0x07, 0x06, 0x02, 0x2A, 0x03, 0x04, 0x01, 0x00, 0x30, 0x07, 0x06, 0x02,
        0x2A, 0x03, 0x04, 0x01, 0x00
    ]
}

/// Condition 13.
pub proof fn example_duplicate_extensions()
    ensures
        e::decode_extension_list(s::sequence_elements(i::parse_tlv(duplicate_extensions())->Some_0)->Some_0, 0) is Some,
        x::parse_extensions(duplicate_extensions()) is None,
{
    assert(e::decode_extension_list(
        s::sequence_elements(i::parse_tlv(duplicate_extensions())->Some_0)->Some_0,
        0,
    ) is Some) by (compute_only);
    assert(x::parse_extensions(duplicate_extensions()) is None) by (compute_only);
}

/// keyUsage whose value is the octet 00: not a BIT STRING.
pub open spec fn bad_key_usage() -> Seq<u8> {
    seq![0x30u8, 0x08, 0x06, 0x03, 0x55, 0x1D, 0x0F, 0x04, 0x01, 0x00]
}

/// Condition 3.
pub proof fn example_known_value()
    ensures
        x::parse_extension(bad_key_usage(), 0, 10) is Some,
        e::decode_extension(i::parse_tlv(bad_key_usage())->Some_0) is None,
{
    assert(x::parse_extension(bad_key_usage(), 0, 10) is Some) by (compute_only);
    assert(e::decode_extension(i::parse_tlv(bad_key_usage())->Some_0) is None) by (compute_only);
}

/// `[9]`, a form neither edition defines.
pub open spec fn unknown_form() -> Seq<u8> {
    seq![0x89u8, 0x00]
}

/// An empty dNSName.
pub open spec fn empty_dns_name() -> Seq<u8> {
    seq![0x82u8, 0x00]
}

/// An iPAddress of one octet.
pub open spec fn short_address() -> Seq<u8> {
    seq![0x87u8, 0x01, 0x00]
}

/// An rfc822Name outside IA5.
pub open spec fn bad_rfc822() -> Seq<u8> {
    seq![0x81u8, 0x01, 0xFF]
}

/// `general_name_in_domain`, and `other_form_decodes`.
pub proof fn example_general_names()
    ensures
        e::decode_general_name(i::parse_tlv(unknown_form())->Some_0) is Some,
        x::parse_general_name(unknown_form(), 0, 2) is None,
        e::decode_general_name(i::parse_tlv(empty_dns_name())->Some_0) is Some,
        x::parse_general_name(empty_dns_name(), 0, 2) is None,
        e::decode_general_name(i::parse_tlv(short_address())->Some_0) is Some,
        x::parse_general_name(short_address(), 0, 3) is None,
        x::parse_general_name(bad_rfc822(), 0, 3) is Some,
        e::decode_general_name(i::parse_tlv(bad_rfc822())->Some_0) is None,
{
    assert(e::decode_general_name(i::parse_tlv(unknown_form())->Some_0) is Some) by (compute_only);
    assert(x::parse_general_name(unknown_form(), 0, 2) is None) by (compute_only);
    assert(e::decode_general_name(i::parse_tlv(empty_dns_name())->Some_0) is Some) by (compute_only);
    assert(x::parse_general_name(empty_dns_name(), 0, 2) is None) by (compute_only);
    assert(e::decode_general_name(i::parse_tlv(short_address())->Some_0) is Some) by (compute_only);
    assert(x::parse_general_name(short_address(), 0, 3) is None) by (compute_only);
    assert(x::parse_general_name(bad_rfc822(), 0, 3) is Some) by (compute_only);
    assert(e::decode_general_name(i::parse_tlv(bad_rfc822())->Some_0) is None) by (compute_only);
}

/// sha256WithRSAEncryption with these parameters.
pub open spec fn sha256_rsa(parameters: Option<Seq<u8>>) -> c::AlgorithmIdentifier {
    c::AlgorithmIdentifier {
        oid: seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 11nat],
        parameters_der: parameters,
    }
}

/// The exclusion of `equivalence_signature.rs`: NULL against absent.
pub proof fn example_null_against_absent()
    ensures
        g::prepare_signature(
            sha256_rsa(None),
            sha256_rsa(Some(seq![0x05u8, 0x00])),
            seq![0x30u8, 0x00],
            seq![0x00u8],
            0,
        ) is Some,
        sha256_rsa(None) != sha256_rsa(Some(seq![0x05u8, 0x00])),
{
    assert(g::prepare_signature(
        sha256_rsa(None),
        sha256_rsa(Some(seq![0x05u8, 0x00])),
        seq![0x30u8, 0x00],
        seq![0x00u8],
        0,
    ) is Some) by (compute_only);
}

/// `a_b.example`.
pub open spec fn underscore_name() -> Seq<u8> {
    seq![0x61u8, 0x5F, 0x62, 0x2E, 0x65, 0x78, 0x61, 0x6D, 0x70, 0x6C, 0x65]
}

/// `*`.
pub open spec fn bare_star() -> Seq<u8> {
    seq![0x2Au8]
}

/// `localhost`.
pub open spec fn one_label() -> Seq<u8> {
    seq![0x6Cu8, 0x6F, 0x63, 0x61, 0x6C, 0x68, 0x6F, 0x73, 0x74]
}

/// `*.com`.
pub open spec fn star_com() -> Seq<u8> {
    seq![0x2Au8, 0x2E, 0x63, 0x6F, 0x6D]
}

/// `example.com`'s neighbour `com` with one more label.
pub open spec fn under_com() -> Seq<u8> {
    seq![0x61u8, 0x2E, 0x63, 0x6F, 0x6D]
}

/// Matching conditions 1 and 2, and RFC 6125's side of condition 3.
pub proof fn example_matching()
    ensures
        m::domain_name_matches(m::cautious_choices(), underscore_name(), underscore_name()),
        !h::dns_match(underscore_name(), underscore_name()),
        m::domain_name_matches(m::cautious_choices(), bare_star(), one_label()),
        !h::dns_match(one_label(), bare_star()),
        m::domain_name_matches(m::cautious_choices(), star_com(), under_com()),
{
    assert(m::domain_name_matches(m::cautious_choices(), underscore_name(), underscore_name()))
        by (compute_only);
    assert(!h::dns_name_shape(underscore_name())) by (compute_only);
    assert(m::domain_name_matches(m::cautious_choices(), bare_star(), one_label())) by (compute_only);
    assert(!h::dns_name_shape(bare_star())) by (compute_only);
    assert(bare_star().len() == 1);
    assert(m::domain_name_matches(m::cautious_choices(), star_com(), under_com())) by (compute_only);
}

/// A whole certificate: v1, serial 1, algorithm 1.2.3, issuer `CN=a`, an empty
/// subject, 2025 to 2026.
pub open spec fn sample_certificate() -> Seq<u8> {
    seq![
        0x30u8, 0x4F, 0x30, 0x44, 0x02, 0x01, 0x01, 0x30, 0x04, 0x06, 0x02, 0x2A, 0x03, 0x30, 0x0C,
        0x31, 0x0A, 0x30, 0x08, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0C, 0x01, 0x61, 0x30, 0x1E, 0x17,
        0x0D, 0x32, 0x35, 0x30, 0x31, 0x30, 0x31, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x5A, 0x17,
        0x0D, 0x32, 0x36, 0x30, 0x31, 0x30, 0x31, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x5A, 0x30,
        0x00, 0x30, 0x09, 0x30, 0x04, 0x06, 0x02, 0x2A, 0x03, 0x03, 0x01, 0x00, 0x30, 0x04, 0x06,
        0x02, 0x2A, 0x03, 0x03, 0x01, 0x00
    ]
}

/// What the transcription reads of it.
pub open spec fn sample_value() -> s::Certificate {
    s::decode_certificate(sample_certificate())->Some_0
}

/// The sample's one attribute.
pub open spec fn sample_attribute() -> s::AttributeTypeAndValue {
    sample_value().to_be_signed.issuer.rdn_sequence[0][0]
}

/// The sample is inside conditions 4 to 13.
pub proof fn lemma_sample_in_domain()
    ensures
        s::decode_certificate(sample_certificate()) is Some,
        certificate_in_domain(sample_value()),
{
    hide(s::decode_certificate);
    hide(sample_certificate);
    hide(sample_value);
    assert(s::decode_certificate(sample_certificate()) is Some) by (compute_only);
    let y = sample_value();
    let b = y.to_be_signed;
    assert(sample_value().additions.len() == 0) by (compute_only);
    assert(sample_value().to_be_signed.additions.len() == 0) by (compute_only);
    assert(r::one_signature_only(sample_value())) by (compute_only);
    assert(r::version_rules(sample_value())) by (compute_only);
    assert(r::issuer_non_empty(sample_value())) by (compute_only);
    assert(sample_value().to_be_signed.serial_number == 1) by (compute_only);
    assert(d::pow256(19) > 0) by (compute_only);
    assert(sample_value().to_be_signed.extensions is None) by (compute_only);
    // Each AlgorithmIdentifier: 1.2.3, nothing after it.
    assert(sample_value().algorithm_identifier.additions.len() == 0) by (compute_only);
    assert(sample_value().algorithm_identifier.parameters is None) by (compute_only);
    assert(sample_value().algorithm_identifier.algorithm =~= seq![1nat, 2nat, 3nat]) by (compute_only);
    assert(sample_value().to_be_signed.signature.additions.len() == 0) by (compute_only);
    assert(sample_value().to_be_signed.signature.parameters is None) by (compute_only);
    assert(sample_value().to_be_signed.signature.algorithm =~= seq![1nat, 2nat, 3nat]) by (compute_only);
    let k0 = b.subject_public_key_info;
    assert(sample_value().to_be_signed.subject_public_key_info.additions.len() == 0) by (compute_only);
    assert(sample_value().to_be_signed.subject_public_key_info.algorithm.additions.len() == 0) by (compute_only);
    assert(sample_value().to_be_signed.subject_public_key_info.algorithm.parameters is None) by (compute_only);
    assert(sample_value().to_be_signed.subject_public_key_info.algorithm.algorithm =~= seq![1nat, 2nat, 3nat])
        by (compute_only);
    assert(!k::is_rsa_encryption(k0.algorithm.algorithm)) by {
        assert(k0.algorithm.algorithm.len() == 3);
        assert(seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 1nat].len() == 7);
    }
    // The names.
    assert(sample_value().to_be_signed.subject.rdn_sequence.len() == 0) by (compute_only);
    assert(sample_value().to_be_signed.issuer.rdn_sequence.len() == 1) by (compute_only);
    assert(sample_value().to_be_signed.issuer.rdn_sequence[0].len() == 1) by (compute_only);
    assert(sample_attribute().additions.len() == 0) by (compute_only);
    assert(sample_attribute().value.number == 12) by (compute_only);
    assert(sample_attribute().attribute_type =~= seq![2nat, 5nat, 4nat, 3nat]) by (compute_only);
    assert(attribute_in_domain(sample_attribute()));
    assert(rdn_in_domain(b.issuer.rdn_sequence[0]));
    // The times.
    assert(sample_value().to_be_signed.validity.additions.len() == 0) by (compute_only);
    assert(time_in_domain(sample_value().to_be_signed.validity.not_before)) by (compute_only);
    assert(time_in_domain(sample_value().to_be_signed.validity.not_after)) by (compute_only);
    assert(tm::time_le(
        moment_time(time_moment(sample_value().to_be_signed.validity.not_before)),
        moment_time(time_moment(sample_value().to_be_signed.validity.not_after)),
    )) by (compute_only);
}

/// `sample_value` is what the transcription reads.
pub proof fn lemma_sample_value()
    requires
        s::decode_certificate(sample_certificate()) is Some,
    ensures
        s::decode_certificate(sample_certificate()) == Some(sample_value()),
{
    hide(s::decode_certificate);
    hide(sample_certificate);
}

/// What agrees with the sample is inside conditions 1 to 3.
pub proof fn lemma_sample_crate_side(a: Decoded)
    requires
        certificate_agree(a, sample_value()),
    ensures
        decoded_in_domain(a),
{
    hide(s::decode_certificate);
    hide(sample_certificate);
    hide(sample_value);
    let y = sample_value();
    let b = y.to_be_signed;
    // Condition 1: nothing has the reserved tag.
    assert(sample_value().algorithm_identifier.parameters is None) by (compute_only);
    assert(sample_value().to_be_signed.signature.parameters is None) by (compute_only);
    assert(sample_value().to_be_signed.subject_public_key_info.algorithm.parameters is None) by (compute_only);
    assert(sample_value().to_be_signed.subject.rdn_sequence.len() == 0) by (compute_only);
    assert(sample_value().to_be_signed.issuer.rdn_sequence.len() == 1) by (compute_only);
    assert(sample_value().to_be_signed.issuer.rdn_sequence[0].len() == 1) by (compute_only);
    assert(sample_attribute().value.number == 12) by (compute_only);
    assert(a.issuer.rdns.len() == 1);
    assert(rdn_agree(a.issuer.rdns[0], b.issuer.rdn_sequence[0]));
    assert(attribute_agree(a.issuer.rdns[0].attributes[0], sample_attribute()));
    assert(rdn_tags_plain(a.issuer.rdns[0]));
    assert(name_tags_plain(a.issuer));
    assert(name_tags_plain(a.subject));
    // Condition 2: both seconds are 0.
    assert(time_moment(sample_value().to_be_signed.validity.not_before).second == 0) by (compute_only);
    assert(time_moment(sample_value().to_be_signed.validity.not_after).second == 0) by (compute_only);
    // Condition 3: no extensions.
    assert(sample_value().to_be_signed.extensions is None) by (compute_only);
    assert(a.tbs.extensions_sequence_der is None);
}

/// **The domain is not empty.** Both sides read the sample, inside every
/// condition, so `theorem_certificate_equivalence` says something about it.
pub proof fn example_domain_holds()
    ensures
        equivalence_domain(sample_certificate()),
        crate_decode(sample_certificate()) is Some,
        s::decode_certificate(sample_certificate()) is Some,
{
    hide(s::decode_certificate);
    hide(sample_certificate);
    hide(sample_value);
    hide(crate_decode);
    hide(certificate_in_domain);
    hide(decoded_in_domain);
    hide(certificate_agree);
    lemma_sample_in_domain();
    lemma_sample_value();
    assert(sample_certificate().len() == 81) by (compute_only);
    assert(81 < two64()) by (compute_only);
    theorem_certificate_back(sample_certificate(), sample_value());
    lemma_sample_crate_side(crate_decode(sample_certificate())->Some_0);
}

} // verus!
