//! One concrete input for each one-directional result of
//! `equivalence_values.rs`, `equivalence_name_constraints.rs`,
//! `equivalence_host.rs`, `equivalence_path.rs` and
//! `equivalence_requirements.rs`, evaluated by Verus, in the style of
//! `equivalence_examples.rs`: each condition is an input the two really decide
//! differently, and whole certificates show that no theorem here is vacuous.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der as i;
#[cfg(verus_only)]
use super::equivalence::*;
#[cfg(verus_only)]
use super::equivalence_der::*;
#[cfg(verus_only)]
use super::equivalence_extensions::*;
#[cfg(verus_only)]
use super::equivalence_frame::*;
#[cfg(verus_only)]
use super::equivalence_name_constraints::*;
#[cfg(verus_only)]
use super::equivalence_path::*;
#[cfg(verus_only)]
use super::equivalence_requirements::*;
#[cfg(verus_only)]
use super::equivalence_name::*;
#[cfg(verus_only)]
use super::equivalence_structures::*;
#[cfg(verus_only)]
use super::equivalence_time::*;
#[cfg(verus_only)]
use super::equivalence_values::*;
#[cfg(verus_only)]
use super::extensions as e;
#[cfg(verus_only)]
use super::matching as m;
#[cfg(verus_only)]
use super::requirements as r;
#[cfg(verus_only)]
use super::structures as s;
#[cfg(verus_only)]
use crate::constraints::spec as cs;
#[cfg(verus_only)]
use crate::name_constraints::spec as nc;
#[cfg(verus_only)]
use crate::path::parsed::spec as ps;
#[cfg(verus_only)]
use crate::policy_constraints::spec as pc;
#[cfg(verus_only)]
use crate::signature_algorithm::spec as g;
#[cfg(verus_only)]
use crate::spki::spec as k;
#[cfg(verus_only)]
use crate::tbs::spec as t;
#[cfg(verus_only)]
use crate::time::spec as tm;
#[cfg(verus_only)]
use clazel_der::spec as d;

verus! {

// ---------------------------------------------------------------------
// Values.
// ---------------------------------------------------------------------

/// pathLenConstraint without cA: `SEQUENCE { INTEGER 0 }`.
pub proof fn example_path_len_without_ca()
    ensures
        cs::parse_basic_constraints(seq![0x30u8, 0x03, 0x02, 0x01, 0x00]) is None,
        basic_value(seq![0x30u8, 0x03, 0x02, 0x01, 0x00]) is Some,
{
    assert(cs::parse_basic_constraints(seq![0x30u8, 0x03, 0x02, 0x01, 0x00]) is None) by (compute_only);
    assert(basic_value(seq![0x30u8, 0x03, 0x02, 0x01, 0x00]) is Some) by (compute_only);
}

/// An empty keyUsage, and one with ten bits.
pub proof fn example_key_usage()
    ensures
        cs::parse_key_usage(seq![0x03u8, 0x01, 0x00]) is None,
        key_usage_value(seq![0x03u8, 0x01, 0x00]) is Some,
        cs::parse_key_usage(seq![0x03u8, 0x03, 0x06, 0x80, 0x40]) is None,
        key_usage_value(seq![0x03u8, 0x03, 0x06, 0x80, 0x40]) is Some,
{
    assert(cs::parse_key_usage(seq![0x03u8, 0x01, 0x00]) is None) by (compute_only);
    assert(key_usage_value(seq![0x03u8, 0x01, 0x00]) is Some) by (compute_only);
    assert(cs::parse_key_usage(seq![0x03u8, 0x03, 0x06, 0x80, 0x40]) is None) by (compute_only);
    assert(key_usage_value(seq![0x03u8, 0x03, 0x06, 0x80, 0x40]) is Some) by (compute_only);
}

/// A purpose repeated.
pub open spec fn repeated_purpose() -> Seq<u8> {
    seq![0x30u8, 0x08, 0x06, 0x02, 0x2A, 0x03, 0x06, 0x02, 0x2A, 0x03]
}

/// A repeated purpose.
pub proof fn example_repeated_purpose()
    ensures
        cs::parse_extended_key_usage(repeated_purpose()) is None,
        ext_key_usage_value(repeated_purpose()) is Some,
{
    assert(cs::parse_extended_key_usage(repeated_purpose()) is None) by (compute_only);
    assert(ext_key_usage_value(repeated_purpose()) is Some) by (compute_only);
}

/// `requireExplicitPolicy` of 2^32.
pub open spec fn large_skip_certs() -> Seq<u8> {
    seq![0x30u8, 0x07, 0x80, 0x05, 0x01, 0x00, 0x00, 0x00, 0x00]
}

/// A SkipCerts of 2^32.
pub proof fn example_skip_certs()
    ensures
        pc::parse_policy_constraints(large_skip_certs()) is None,
        policy_constraints_value(large_skip_certs()) is Some,
{
    assert(pc::parse_policy_constraints(large_skip_certs()) is None) by (compute_only);
    assert(policy_constraints_value(large_skip_certs()) is Some) by (compute_only);
}

/// `permittedSubtrees` of one subtree with `minimum` 1.
pub open spec fn minimum_subtree() -> Seq<u8> {
    seq![0x30u8, 0x0A, 0xA0, 0x08, 0x30, 0x06, 0x82, 0x01, 0x61, 0x80, 0x01, 0x01]
}

/// A base of an undefined form, `[9]`.
pub open spec fn unknown_base() -> Seq<u8> {
    seq![0x30u8, 0x09, 0xA0, 0x07, 0x30, 0x05, 0x89, 0x03, 0x61, 0x62, 0x63]
}

/// An iPAddress base of four octets.
pub open spec fn short_ip_base() -> Seq<u8> {
    seq![0x30u8, 0x0A, 0xA0, 0x08, 0x30, 0x06, 0x87, 0x04, 0x0A, 0x00, 0x00, 0x00]
}

/// A directoryName base that is not a Name.
pub open spec fn unread_base() -> Seq<u8> {
    seq![0x30u8, 0x07, 0xA0, 0x05, 0x30, 0x03, 0xA4, 0x01, 0xFF]
}

/// nameConstraints: each row of `equivalence_name_constraints.rs`'s header.
pub proof fn example_name_constraints()
    ensures
        nc::parse_name_constraints(seq![0x30u8, 0x00]) is Some,
        name_constraints_value(seq![0x30u8, 0x00]) is None,
        nc::parse_name_constraints(unread_base()) is Some,
        name_constraints_value(unread_base()) is None,
        nc::parse_name_constraints(minimum_subtree()) is None,
        name_constraints_value(minimum_subtree()) is Some,
        nc::parse_name_constraints(unknown_base()) is None,
        name_constraints_value(unknown_base()) is Some,
        nc::parse_name_constraints(short_ip_base()) is None,
        name_constraints_value(short_ip_base()) is Some,
{
    assert(nc::parse_name_constraints(seq![0x30u8, 0x00]) is Some) by (compute_only);
    assert(name_constraints_value(seq![0x30u8, 0x00]) is None) by (compute_only);
    assert(nc::parse_name_constraints(unread_base()) is Some) by (compute_only);
    assert(name_constraints_value(unread_base()) is None) by (compute_only);
    assert(nc::parse_name_constraints(minimum_subtree()) is None) by (compute_only);
    assert(name_constraints_value(minimum_subtree()) is Some) by (compute_only);
    assert(nc::parse_name_constraints(unknown_base()) is None) by (compute_only);
    assert(name_constraints_value(unknown_base()) is Some) by (compute_only);
    assert(nc::parse_name_constraints(short_ip_base()) is None) by (compute_only);
    assert(name_constraints_value(short_ip_base()) is Some) by (compute_only);
}

// ---------------------------------------------------------------------
// `MatchChoices`.
// ---------------------------------------------------------------------

/// `a.b.c.d`.
pub open spec fn four_labels() -> Seq<u8> {
    seq![0x61u8, 0x2E, 0x62, 0x2E, 0x63, 0x2E, 0x64]
}

/// `a.c.d`.
pub open spec fn three_labels() -> Seq<u8> {
    seq![0x61u8, 0x2E, 0x63, 0x2E, 0x64]
}

/// `*.c.d`.
pub open spec fn star_c_d() -> Seq<u8> {
    seq![0x2Au8, 0x2E, 0x63, 0x2E, 0x64]
}

/// `cautious_choices` with one field changed.
pub open spec fn spanning() -> m::MatchChoices {
    m::MatchChoices { wildcard_spans_labels: true, ..m::cautious_choices() }
}

/// `cautious_choices` taking no wildcard.
pub open spec fn no_wildcards() -> m::MatchChoices {
    m::MatchChoices { wildcards: false, ..m::cautious_choices() }
}

/// **The two choices that change anything on the domain.** Spanning accepts
/// more than `cautious_choices`, and no wildcards accepts less.
pub proof fn example_choices()
    ensures
        m::domain_name_matches(spanning(), star_c_d(), four_labels()),
        !m::domain_name_matches(m::cautious_choices(), star_c_d(), four_labels()),
        m::domain_name_matches(m::cautious_choices(), star_c_d(), three_labels()),
        !m::domain_name_matches(no_wildcards(), star_c_d(), three_labels()),
{
    assert(m::domain_name_matches(spanning(), star_c_d(), four_labels())) by (compute_only);
    assert(!m::domain_name_matches(m::cautious_choices(), star_c_d(), four_labels())) by (compute_only);
    assert(m::domain_name_matches(m::cautious_choices(), star_c_d(), three_labels())) by (compute_only);
    assert(!m::domain_name_matches(no_wildcards(), star_c_d(), three_labels())) by (compute_only);
}

// ---------------------------------------------------------------------
// Whole certificates.
// ---------------------------------------------------------------------

/// **The production path reads less than `decode_certificate`.** The evaluator
/// reaches its recursion limit on the crate's decoders over a whole certificate
/// (`path/parsed/examples.rs`), so this is the two steps that keep the
/// components: a subject that is not a Name and an empty key pass
/// `parse_subject_spki`, and the transcription refuses each. Likewise an issuer
/// that is not a Name passes `parse_signature_issuer`.
pub proof fn example_unread_components()
    ensures
        t::parse_subject_spki(seq![0x30u8, 0x01, 0xFF, 0x30, 0x00], 0, 5) is Some,
        i::parse_single(seq![0x30u8, 0x01, 0xFF]) is Some,
        s::decode_name(i::parse_single(seq![0x30u8, 0x01, 0xFF])->Some_0) is None,
        i::parse_single(seq![0x30u8, 0x00]) is Some,
        s::decode_subject_public_key_info(i::parse_single(seq![0x30u8, 0x00])->Some_0) is None,
        t::parse_signature_issuer(seq![0x30u8, 0x04, 0x06, 0x02, 0x2A, 0x03, 0x30, 0x01, 0xFF], 0, 9) is Some,
{
    assert(t::parse_subject_spki(seq![0x30u8, 0x01, 0xFF, 0x30, 0x00], 0, 5) is Some) by (compute_only);
    assert(i::parse_single(seq![0x30u8, 0x01, 0xFF]) is Some) by (compute_only);
    assert(s::decode_name(i::parse_single(seq![0x30u8, 0x01, 0xFF])->Some_0) is None) by (compute_only);
    assert(i::parse_single(seq![0x30u8, 0x00]) is Some) by (compute_only);
    assert(s::decode_subject_public_key_info(i::parse_single(seq![0x30u8, 0x00])->Some_0) is None) by (compute_only);
    assert(t::parse_signature_issuer(seq![0x30u8, 0x04, 0x06, 0x02, 0x2A, 0x03, 0x30, 0x01, 0xFF], 0, 9) is Some)
        by (compute_only);
}

/// A v3 certificate: `equivalence_examples.rs`'s, with a non-critical
/// subjectAltName of one dNSName, `a.b`. Its subject is empty.
pub open spec fn san_certificate() -> Seq<u8> {
    seq![
        0x30u8, 0x68, 0x30, 0x5D, 0xA0, 0x03, 0x02, 0x01, 0x02, 0x02, 0x01, 0x01, 0x30, 0x04, 0x06,
        0x02, 0x2A, 0x03, 0x30, 0x0C, 0x31, 0x0A, 0x30, 0x08, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0C,
        0x01, 0x61, 0x30, 0x1E, 0x17, 0x0D, 0x32, 0x35, 0x30, 0x31, 0x30, 0x31, 0x30, 0x30, 0x30,
        0x30, 0x30, 0x30, 0x5A, 0x17, 0x0D, 0x32, 0x36, 0x30, 0x31, 0x30, 0x31, 0x30, 0x30, 0x30,
        0x30, 0x30, 0x30, 0x5A, 0x30, 0x00, 0x30, 0x09, 0x30, 0x04, 0x06, 0x02, 0x2A, 0x03, 0x03,
        0x01, 0x00, 0xA3, 0x12, 0x30, 0x10, 0x30, 0x0E, 0x06, 0x03, 0x55, 0x1D, 0x11, 0x04, 0x07,
        0x30, 0x05, 0x82, 0x03, 0x61, 0x2E, 0x62, 0x30, 0x04, 0x06, 0x02, 0x2A, 0x03, 0x03, 0x01,
        0x00
    ]
}

/// What the transcription reads of it.
pub open spec fn san_value() -> s::Certificate {
    s::decode_certificate(san_certificate())->Some_0
}

/// Its one extension.
pub open spec fn san_extension() -> e::Extension {
    r::extensions_of(san_value())[0]
}

/// Its one attribute.
pub open spec fn san_attribute() -> s::AttributeTypeAndValue {
    san_value().to_be_signed.issuer.rdn_sequence[0][0]
}

/// The certificate is inside conditions 4 to 13.
pub proof fn lemma_san_certificate_in_domain()
    ensures
        s::decode_certificate(san_certificate()) is Some,
        certificate_in_domain(san_value()),
{
    hide(s::decode_certificate);
    hide(san_certificate);
    hide(san_value);
    hide(san_extension);
    assert(s::decode_certificate(san_certificate()) is Some) by (compute_only);
    let y = san_value();
    let b = y.to_be_signed;
    assert(san_value().additions.len() == 0) by (compute_only);
    assert(san_value().to_be_signed.additions.len() == 0) by (compute_only);
    assert(r::one_signature_only(san_value())) by (compute_only);
    assert(r::version_rules(san_value())) by (compute_only);
    assert(r::issuer_non_empty(san_value())) by (compute_only);
    assert(san_value().to_be_signed.serial_number == 1) by (compute_only);
    assert(d::pow256(19) > 0) by (compute_only);
    assert(san_value().algorithm_identifier.additions.len() == 0) by (compute_only);
    assert(san_value().algorithm_identifier.parameters is None) by (compute_only);
    assert(san_value().algorithm_identifier.algorithm =~= seq![1nat, 2nat, 3nat]) by (compute_only);
    assert(san_value().to_be_signed.signature.additions.len() == 0) by (compute_only);
    assert(san_value().to_be_signed.signature.parameters is None) by (compute_only);
    assert(san_value().to_be_signed.signature.algorithm =~= seq![1nat, 2nat, 3nat]) by (compute_only);
    let k0 = b.subject_public_key_info;
    assert(san_value().to_be_signed.subject_public_key_info.additions.len() == 0) by (compute_only);
    assert(san_value().to_be_signed.subject_public_key_info.algorithm.additions.len() == 0) by (compute_only);
    assert(san_value().to_be_signed.subject_public_key_info.algorithm.parameters is None) by (compute_only);
    assert(san_value().to_be_signed.subject_public_key_info.algorithm.algorithm =~= seq![1nat, 2nat, 3nat])
        by (compute_only);
    assert(!k::is_rsa_encryption(k0.algorithm.algorithm)) by {
        assert(k0.algorithm.algorithm.len() == 3);
        assert(seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 1nat].len() == 7);
    }
    assert(san_value().to_be_signed.subject.rdn_sequence.len() == 0) by (compute_only);
    assert(san_value().to_be_signed.issuer.rdn_sequence.len() == 1) by (compute_only);
    assert(san_value().to_be_signed.issuer.rdn_sequence[0].len() == 1) by (compute_only);
    assert(san_attribute().additions.len() == 0) by (compute_only);
    assert(san_attribute().value.number == 12) by (compute_only);
    assert(san_attribute().attribute_type =~= seq![2nat, 5nat, 4nat, 3nat]) by (compute_only);
    assert(attribute_in_domain(san_attribute()));
    assert(rdn_in_domain(b.issuer.rdn_sequence[0]));
    assert(san_value().to_be_signed.validity.additions.len() == 0) by (compute_only);
    assert(time_in_domain(san_value().to_be_signed.validity.not_before)) by (compute_only);
    assert(time_in_domain(san_value().to_be_signed.validity.not_after)) by (compute_only);
    assert(tm::time_le(
        moment_time(time_moment(san_value().to_be_signed.validity.not_before)),
        moment_time(time_moment(san_value().to_be_signed.validity.not_after)),
    )) by (compute_only);
    // The one extension.
    assert(san_value().to_be_signed.extensions is Some) by (compute_only);
    assert(r::extensions_of(san_value()).len() == 1) by (compute_only);
    assert(b.extensions == Some(r::extensions_of(y)));
    let v = r::extensions_of(y);
    assert(r::extensions_of(san_value())[0].additions.len() == 0) by (compute_only);
    assert(r::extensions_of(san_value())[0].extn_id =~= seq![2nat, 5nat, 29nat, 17nat]) by (compute_only);
    assert(extension_in_domain(v[0]));
    assert(extensions_in_domain(v));
}

/// The value and the signature are inside what `parse_path_cert` asks.
pub proof fn lemma_san_values_in_domain()
    requires
        s::decode_certificate(san_certificate()) is Some,
    ensures
        values_in_domain(r::extensions_of(san_value())),
        signature_in_domain(san_value()),
{
    hide(s::decode_certificate);
    hide(san_certificate);
    hide(san_value);
    let y = san_value();
    let v = r::extensions_of(y);
    assert(r::extensions_of(san_value()).len() == 1) by (compute_only);
    assert(r::extensions_of(san_value())[0].value is SubjectAltName) by (compute_only);
    assert(r::extensions_of(san_value())[0].value->SubjectAltName_0.len() == 1) by (compute_only);
    assert(r::extensions_of(san_value())[0].value->SubjectAltName_0[0] is DNSName) by (compute_only);
    assert(r::extensions_of(san_value())[0].value->SubjectAltName_0[0]->DNSName_0.len() == 3) by (compute_only);
    let w = v[0].value->SubjectAltName_0;
    assert(general_name_in_domain(w[0]));
    assert(value_in_domain(v[0]));
    assert(values_in_domain(v));
    assert(algorithm_of(san_value().to_be_signed.signature) == algorithm_of(san_value().algorithm_identifier))
        by (compute_only);
    assert(g::classify(algorithm_of(san_value().algorithm_identifier)) is Some) by (compute_only);
    assert(g::classify(algorithm_of(san_value().algorithm_identifier))->Some_0 is Unsupported) by (compute_only);
}

/// A certificate of one subjectAltName of one dNSName meets `path_conditions`.
#[verifier::spinoff_prover]
pub proof fn lemma_one_san_conditions(p: ps::PathCert, y: s::Certificate)
    requires
        path_cert_agree(p, y),
        y.algorithm_identifier.parameters is None,
        y.to_be_signed.signature.parameters is None,
        time_moment(y.to_be_signed.validity.not_before).second == 0,
        time_moment(y.to_be_signed.validity.not_after).second == 0,
        r::extensions_of(y).len() == 1,
        r::extensions_of(y)[0].extn_id == e::id_ce_subject_alt_name(),
        r::extensions_of(y)[0].value is SubjectAltName,
        r::extensions_of(y)[0].value->SubjectAltName_0.len() == 1,
        r::extensions_of(y)[0].value->SubjectAltName_0[0] is DNSName,
    ensures
        path_conditions(p),
{
    hide(basic_found_agree);
    hide(key_usage_found_agree);
    hide(eku_found_agree);
    hide(policy_found_agree);
    hide(san_forms_decode);
    hide(value_decodes);
    let v = r::extensions_of(y);
    assert(extension_agree(p.extensions[0], v[0]));
    lemma_id_ce_differ(17, 35);
    lemma_id_ce_differ(17, 14);
    lemma_id_ce_differ(17, 32);
    lemma_id_ce_differ(17, 54);
    lemma_id_ce_differ(17, 30);
    assert(!unread_by_path(p.extensions[0].oid));
    assert(r::find_extension(v, 1, e::id_ce_name_constraints()) is None);
    assert(r::find_extension(v, 0, e::id_ce_name_constraints()) is None);
    assert(r::find_extension(v, 0, e::id_ce_subject_alt_name()) == Some(v[0]));
    let q = p.san->Some_0;
    let w = v[0].value->SubjectAltName_0;
    assert(subject_alt_name_agree(q, w));
    assert(san_forms_decode(q)) by {
        reveal(san_forms_decode);
        assert forall|k: int| 0 <= k < q.names.len() implies other_form_decodes(#[trigger] q.names[k]) by {
            assert(k == 0);
            assert(general_name_agree(q.names[0], w[0]));
        }
    }
}

/// **`theorem_path_cert_back`'s and `theorem_path_cert_fwd`'s conditions are met
/// by a certificate with an extension,** so they, and `theorem_reading`, are
/// not vacuous. And **`subject_rule` is not enforced:** the certificate's
/// subject is empty and its subjectAltName is not critical, so 7.2.1 refuses
/// it, and `parse_path_cert` keeps it (limbo pins the same for a whole path:
/// `rfc5280::san::noncritical-with-empty-subject`).
#[verifier::spinoff_prover]
pub proof fn example_path_conditions_hold()
    ensures
        ps::parse_path_cert(san_certificate()) is Some,
        path_conditions(ps::parse_path_cert(san_certificate())->Some_0),
        !r::subject_rule(san_value()),
{
    hide(s::decode_certificate);
    hide(san_certificate);
    hide(san_value);
    hide(ps::parse_path_cert);
    hide(certificate_in_domain);
    hide(values_in_domain);
    hide(signature_in_domain);
    hide(path_cert_agree);
    hide(path_conditions);
    hide(r::subject_rule);
    lemma_san_certificate_in_domain();
    lemma_san_values_in_domain();
    assert(san_certificate().len() == 106) by (compute_only);
    assert(106 < two64()) by (compute_only);
    assert(s::decode_certificate(san_certificate()) == Some(san_value())) by {
        reveal(san_value);
    }
    theorem_path_cert_back(san_certificate(), san_value());
    let p = ps::parse_path_cert(san_certificate())->Some_0;
    assert(!r::subject_rule(san_value())) by (compute_only);
    assert(san_value().algorithm_identifier.parameters is None) by (compute_only);
    assert(san_value().to_be_signed.signature.parameters is None) by (compute_only);
    assert(time_moment(san_value().to_be_signed.validity.not_before).second == 0) by (compute_only);
    assert(time_moment(san_value().to_be_signed.validity.not_after).second == 0) by (compute_only);
    assert(r::extensions_of(san_value()).len() == 1) by (compute_only);
    assert(r::extensions_of(san_value())[0].extn_id =~= seq![2nat, 5nat, 29nat, 17nat]) by (compute_only);
    assert(r::extensions_of(san_value())[0].value is SubjectAltName) by (compute_only);
    assert(r::extensions_of(san_value())[0].value->SubjectAltName_0.len() == 1) by (compute_only);
    assert(r::extensions_of(san_value())[0].value->SubjectAltName_0[0] is DNSName) by (compute_only);
    assert(r::extensions_of(san_value())[0].extn_id == e::id_ce_subject_alt_name());
    lemma_one_san_conditions(p, san_value());
}

} // verus!
