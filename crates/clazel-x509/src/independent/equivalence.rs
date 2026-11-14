//! The independent transcription of ITU-T X.509 (10/2019), X.690 (02/2021) and
//! X.501 (`independent/structures.rs`, `independent/extensions.rs`,
//! `independent/der.rs`, written by a separate agent without reading the
//! decoders) **proven equal** to this crate's own decoders on a stated domain:
//! `theorem_certificate_equivalence`. Host matching is in
//! `equivalence_matching.rs`, with its own domain.
//!
//! The crate's decoders are layers: `parse_certificate` keeps the
//! TBSCertificate as octets, `parse_tbs_certificate` keeps names, the key and
//! the extensions as octets, and `parse_name`,
//! `parse_subject_public_key_info` and `parse_extensions` read those.
//! [`crate_decode`] runs all of them. **`parse_path_cert` does not**: it never
//! reads the issuer or subject Name, and reads the key only where a signature
//! needs it. So this theorem is about the decoders, not about which of them
//! production calls on every certificate; `path/independent_equivalence.rs`'s
//! condition 8 already speaks for names under a constraint.
//!
//! **What agrees without narrowing** (proven, not assumed):
//! - **Every encoding's framing.** Identifier octets, low and high form, all
//!   of X.690 8.1.2; length octets in all of 8.1.3 and 10.1; the walk over a
//!   constructed value. `clazel-der` stops at eight length octets and
//!   `der.rs` has no limit, but a length that needs nine is longer than any
//!   input below 2^64 octets (`lemma_length`), which is the theorem's one
//!   precondition.
//! - **UTCTime**, with no condition at all (`lemma_utc_time`): the two pivots,
//!   the seconds bound and the Gregorian month lengths are the same text.
//! - **SET OF order** (X.690 11.6): both allow equal neighbours and pad the
//!   shorter encoding with zero octets (`lemma_not_after`).
//! - **BOOLEAN, BIT STRING, OCTET STRING, INTEGER contents** of 8.2, 8.3, 8.6
//!   and 8.7, exactly (`lemma_bit_string_contents`, `lemma_integer_contents`).
//! - **Object identifiers** below `clazel-der`'s limit (`lemma_oid_contents`).
//! - **Optional fields in the wrong form or order.** `tbs/spec.rs` tests tag
//!   and form together and moves on, so a primitive `[0]` or a constructed
//!   `[1]` fails later, at the next field; `structures.rs` finds the field by
//!   its tag and fails in its decoder. They refuse the same encodings.
//!
//! **The domain.** Each number is one real disagreement, an input the two
//! decide differently; `equivalence_examples.rs` evaluates one for each except
//! 5, 8, 9 and 11, and `example_domain_holds` shows a whole certificate inside
//! all of them, so the theorem is not vacuous. Outside the domain nothing here
//! claims they agree.
//!
//! The crate reads and the transcription refuses ([`decoded_in_domain`]):
//! 1. **Universal 0 as an opaque value** (`parameters`, an attribute value).
//!    X.680 Table 1 reserves the tag for the encoding rules, so no ASN.1 value
//!    has it, and `der.rs` is right by the letter. `clazel-der` reads any tag.
//!    The value is never interpreted, so nothing accepted depends on it.
//! 2. **A leap second in GeneralizedTime.** `time/spec.rs` accepts 60 at
//!    23:59, following X.680 46.3's reference to ISO 8601. `der.rs` applies
//!    UTCTime's "00 to 59" to both, as its stated open choice 6, because ISO
//!    8601 is not freely available to its author. The two read different
//!    sources; neither is corrected.
//! 3. **A value of a known extension that `extensions.rs` refuses.**
//!    `extensions/spec.rs` keeps `extnValue` unread and later decoders read
//!    only what the path needs; a value nobody reads is accepted, even if
//!    malformed. `extensions.rs` reads `ENCODED BY der` for all ten, so one
//!    bad value refuses the whole certificate (open choice 3).
//!    `equivalence_values.rs`, `equivalence_name_constraints.rs` and
//!    `theorem_subject_alt_name_fwd` compare the six values the crate has a
//!    decoder for, and `equivalence_path.rs` narrows this condition to the
//!    rest on the production path.
//!
//! The transcription reads and the crate refuses ([`certificate_in_domain`]):
//! 4. **Additions.** The transcription keeps what follows the known components
//!    of an extensible SEQUENCE (X.690 8.1.1.4 NOTE, open choice 1). RFC 5280's
//!    ASN.1 has no marker, and the crate refuses them. `additions_absent`
//!    leaves out `AttributeTypeAndValue` and `Extension`; this domain covers
//!    them too.
//! 5. **`altAlgorithmIdentifier`, `altSignature`** (X.509 7.2.2, 9.8), which RFC
//!    5280 does not have; 7.2.1 itself refuses them in a public-key
//!    certificate (`one_signature_only`).
//! 6. **A tag number above 16383** in an opaque value, and **a subidentifier of
//!    2^64 or more**: `clazel-der`'s stated limits. X.690 has none.
//! 7. **A serial number that is negative or takes more than 20 contents
//!    octets**: RFC 5280 §4.1.2.2. X.509 sets no limit (open choice 5). So the
//!    domain is `0 <= serial < 2^159`, not 2^160: RFC 5280 says "values up to
//!    20 octets", and `tbs/spec.rs` counts the encoding, sign octet included,
//!    so a 20-octet value with its top bit set is refused
//!    (`example_serial`). The text allows either reading, x509-limbo tests
//!    neither (its long serial has 22 octets) and `rustls-webpki` sets no
//!    limit. Recorded, not changed.
//! 8. **Version rules** (`version_rules`): v4 or above, or a field the version
//!    does not allow. This is a requirement of 7.2.1 that the transcription
//!    keeps out of its decoder (open choice 4).
//! 9. **An empty issuer** (`issuer_non_empty`), the same way.
//! 10. **GeneralizedTime with a fraction, or in the year 0000.** X.690 11.7.3
//!     allows a fraction, RFC 5280 §4.1.2.5.2 forbids it. ISO 8601 has a year
//!     0000, and the crate's calendar starts at 1: a stated choice in
//!     `time/spec.rs`, for a time no live certificate holds.
//! 11. **notBefore after notAfter.** `tbs/spec.rs` refuses it at decoding, and
//!     X.509 states no rule (open choice 16).
//! 12. **An RSA key outside the profile** (`rsa_profile`): RFC 3279 §2.3.1 and
//!     RFC 8017. X.509 leaves key syntax to the algorithm.
//! 13. **Two extensions with one `extnId`** when it is not an X.509 one.
//!     RFC 5280 §4.2 refuses any; X.509 9 speaks of extensions it defines
//!     (open choice 12).
//!
//! **Each condition is one-directional.** Conditions 1 to 3 appear only in
//! [`theorem_certificate_fwd`] and 4 to 13 only in [`theorem_certificate_back`],
//! so where one fails the other direction still holds.
//! `equivalence_exclusions.rs` says which are narrowed, and how.
//!
//! **This theorem is about `crate_decode`, not production.** What every
//! certificate goes through is `equivalence_path.rs`.
//!
//! **Not proven.** Listed so that nobody reads the theorem as more than it is:
//! - `spki/spec.rs`'s classification of keys, which has no counterpart in the
//!   transcription; only its refusals are compared.
//! - The four extension values no decoder of the crate reads:
//!   authorityKeyIdentifier, subjectKeyIdentifier, certificatePolicies and
//!   inhibitAnyPolicy. The crate has nothing to compare.
//! - IP-ID matching: `matching.rs` has no counterpart (RFC 6125 1.7.2).
//! - Anything executable: both sides are spec functions. `exec.rs` is proven
//!   against `spec.rs` elsewhere.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der as i;
#[cfg(verus_only)]
use super::equivalence_der::*;
#[cfg(verus_only)]
use super::equivalence_extensions::*;
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
use super::requirements as r;
#[cfg(verus_only)]
use super::structures as s;
#[cfg(verus_only)]
use crate::certificate::spec as c;
#[cfg(verus_only)]
use crate::extensions::spec as x;
#[cfg(verus_only)]
use crate::name::spec as n;
#[cfg(verus_only)]
use crate::signature_algorithm::spec as g;
#[cfg(verus_only)]
use crate::spki::spec as k;
#[cfg(verus_only)]
use crate::tbs::spec as t;
#[cfg(verus_only)]
use clazel_der::spec as d;

verus! {

// ---------------------------------------------------------------------
// The crate's decoders, composed.
// ---------------------------------------------------------------------

/// What this crate's decoders read of one certificate.
pub struct Decoded {
    /// `parse_certificate`.
    pub envelope: crate::certificate::spec::CertificateEnvelope,
    /// `parse_tbs_certificate` of the envelope's TBSCertificate.
    pub tbs: crate::tbs::spec::TbsCertificate,
    /// `parse_name` of `issuer`.
    pub issuer: crate::name::spec::Name,
    /// `parse_name` of `subject`.
    pub subject: crate::name::spec::Name,
    /// `parse_subject_public_key_info`.
    pub spki: crate::spki::spec::SubjectPublicKeyInfo,
    /// `parse_extensions`, when `[3]` is present.
    pub extensions: Option<Seq<crate::extensions::spec::Extension>>,
}

/// Every decoder of the crate, in the order of RFC 5280 §4.1.
pub open spec fn crate_decode(der: Seq<u8>) -> Option<Decoded> {
    match c::parse_certificate(der) {
        None => None,
        Some(envelope) => match t::parse_tbs_certificate(envelope.tbs_certificate_der) {
            None => None,
            Some(tbs) => match (
                n::parse_name(tbs.issuer_der),
                n::parse_name(tbs.subject_der),
                k::parse_subject_public_key_info(tbs.subject_public_key_info_der),
            ) {
                (Some(issuer), Some(subject), Some(spki)) => match tbs.extensions_sequence_der {
                    None => Some(Decoded { envelope, tbs, issuer, subject, spki, extensions: None }),
                    Some(v) => match x::parse_extensions(v) {
                        None => None,
                        Some(list) => Some(
                            Decoded { envelope, tbs, issuer, subject, spki, extensions: Some(list) },
                        ),
                    },
                },
                _ => None,
            },
        },
    }
}

// ---------------------------------------------------------------------
// The domain.
// ---------------------------------------------------------------------

/// Conditions 1 to 3: what the crate read, the transcription reads too.
pub open spec fn decoded_in_domain(a: Decoded) -> bool {
    // 1.
    &&& parameters_plain(a.envelope.signature_algorithm)
    &&& parameters_plain(a.tbs.signature)
    &&& parameters_plain(a.spki.algorithm)
    &&& name_tags_plain(a.issuer)
    &&& name_tags_plain(a.subject)
    // 2.
    &&& a.tbs.not_before.second != 60
    &&& a.tbs.not_after.second != 60
    // 3.
    &&& extensions_decode(a.tbs.extensions_sequence_der)
}

/// Conditions 4 to 13: what the transcription read, the crate reads too.
pub open spec fn certificate_in_domain(y: s::Certificate) -> bool {
    let b = y.to_be_signed;
    // 4.
    &&& y.additions.len() == 0
    &&& b.additions.len() == 0
    // 5.
    &&& r::one_signature_only(y)
    // 4 and 6, inside each of these. 10 and 11 in `validity_in_domain`, 12 in
    // `spki_in_domain`, 13 in `extensions_in_domain`.
    &&& algorithm_in_domain(y.algorithm_identifier)
    &&& algorithm_in_domain(b.signature)
    &&& name_in_domain(b.issuer)
    &&& name_in_domain(b.subject)
    &&& validity_in_domain(b.validity)
    &&& spki_in_domain(b.subject_public_key_info)
    &&& match b.extensions {
        Some(v) => extensions_in_domain(v),
        None => true,
    }
    // 7.
    &&& 0 <= b.serial_number < serial_limit()
    // 8.
    &&& r::version_rules(y)
    // 9.
    &&& r::issuer_non_empty(y)
}

/// The two values of a certificate agree, field by field.
pub open spec fn certificate_agree(a: Decoded, y: s::Certificate) -> bool {
    let b = y.to_be_signed;
    &&& algorithm_agree(a.envelope.signature_algorithm, y.algorithm_identifier)
    &&& a.envelope.signature_unused_bits as nat == y.signature.unused
    &&& a.envelope.signature_bits == y.signature.octets
    &&& a.envelope.tbs_certificate_der == b.encoding
    &&& a.tbs.version as int == b.version
    &&& i::parse_single(a.tbs.serial_number_der) is Some
    &&& i::decode_integer(i::parse_single(a.tbs.serial_number_der)->Some_0) == Some(b.serial_number)
    &&& algorithm_agree(a.tbs.signature, b.signature)
    &&& name_agree(a.issuer, b.issuer)
    &&& a.tbs.not_before == moment_time(time_moment(b.validity.not_before))
    &&& a.tbs.not_after == moment_time(time_moment(b.validity.not_after))
    &&& name_agree(a.subject, b.subject)
    &&& spki_agree(a.spki, b.subject_public_key_info)
    &&& unique_agree(a.tbs.issuer_unique_id_der, b.issuer_unique_identifier)
    &&& unique_agree(a.tbs.subject_unique_id_der, b.subject_unique_identifier)
    &&& optional_extensions_agree(a.tbs.extensions_sequence_der, b.extensions)
}

// ---------------------------------------------------------------------
// `decode_tbs_certificate`, opened once.
// ---------------------------------------------------------------------

/// The fields a TBSCertificate's list decodes to.
pub open spec fn tbs_fields(l: Seq<i::Tlv>, y: s::TBSCertificate) -> bool {
    let m = s::after_version(l);
    &&& m + 6 <= l.len()
    &&& s::version_component(l) == Some(y.version)
    &&& i::decode_integer(l[m as int]) == Some(y.serial_number)
    &&& s::decode_algorithm_identifier(l[(m + 1) as int]) == Some(y.signature)
    &&& s::decode_name(l[(m + 2) as int]) == Some(y.issuer)
    &&& s::decode_validity(l[(m + 3) as int]) == Some(y.validity)
    &&& s::decode_name(l[(m + 4) as int]) == Some(y.subject)
    &&& s::decode_subject_public_key_info(l[(m + 5) as int]) == Some(y.subject_public_key_info)
    &&& tail_of(l.skip((m + 6) as int)) is Some
    &&& tail_of(l.skip((m + 6) as int))->Some_0.0 == y.issuer_unique_identifier
    &&& tail_of(l.skip((m + 6) as int))->Some_0.1 == y.subject_unique_identifier
    &&& tail_of(l.skip((m + 6) as int))->Some_0.2 == y.extensions
}

/// `decode_tbs_certificate` gives these fields.
#[verifier::spinoff_prover]
pub proof fn lemma_tbs_opens(u: i::Tlv, y: s::TBSCertificate)
    requires
        s::decode_tbs_certificate(u) == Some(y),
    ensures
        s::sequence_elements(u) is Some,
        tbs_fields(s::sequence_elements(u)->Some_0, y),
        y.encoding == u.encoding,
        ({
            let l = s::sequence_elements(u)->Some_0;
            let m = s::after_version(l);
            y.additions == i::from_index(l, m + 6 + tail_of(l.skip((m + 6) as int))->Some_0.3)
        }),
{
    hide(s::decode_algorithm_identifier);
    hide(s::decode_name);
    hide(s::decode_validity);
    hide(s::decode_subject_public_key_info);
    hide(s::decode_version);
    hide(s::extensions_component);
    hide(s::unique_identifier_component);
    let l = s::sequence_elements(u)->Some_0;
    let m = s::after_version(l);
    let j = m + 6;
    let v1 = s::unique_identifier_component(l, j, 1)->Some_0;
    let p = j + s::step(v1);
    let v2 = s::unique_identifier_component(l, p, 2)->Some_0;
    let q = p + s::step(v2);
    lemma_tail_index(l, j, v1, v2);
}

/// Indices of the list and of the tail.
pub proof fn lemma_tail_index(l: Seq<i::Tlv>, j: nat, v1: Option<i::BitString>, v2: Option<i::BitString>)
    requires
        j <= l.len(),
    ensures
        s::unique_identifier_component(l, j, 1) == s::unique_identifier_component(l.skip(j as int), 0, 1),
        s::unique_identifier_component(l, j + s::step(v1), 2) == s::unique_identifier_component(
            l.skip(j as int),
            s::step(v1),
            2,
        ),
        s::extensions_component(l, j + s::step(v1) + s::step(v2)) == s::extensions_component(
            l.skip(j as int),
            s::step(v1) + s::step(v2),
        ),
{
    lemma_unique_skip(l, j, 0, 1);
    lemma_unique_skip(l, j, s::step(v1), 2);
    lemma_extensions_skip(l, j, s::step(v1) + s::step(v2));
}

/// These fields are what `decode_tbs_certificate` gives.
#[verifier::spinoff_prover]
pub proof fn lemma_tbs_closes(u: i::Tlv, l: Seq<i::Tlv>, y: s::TBSCertificate)
    requires
        s::sequence_elements(u) == Some(l),
        tbs_fields(l, y),
        y.encoding == u.encoding,
        y.additions == i::from_index(l, s::after_version(l) + 6 + tail_of(l.skip((s::after_version(l) + 6) as int))->Some_0.3),
    ensures
        s::decode_tbs_certificate(u) == Some(y),
{
    hide(s::decode_algorithm_identifier);
    hide(s::decode_name);
    hide(s::decode_validity);
    hide(s::decode_subject_public_key_info);
    hide(s::decode_version);
    hide(s::extensions_component);
    hide(s::unique_identifier_component);
    let m = s::after_version(l);
    let j = m + 6;
    let v1 = y.issuer_unique_identifier;
    let v2 = y.subject_unique_identifier;
    lemma_tail_index(l, j, v1, v2);
}

/// `tail_of` uses at most the encodings it has.
pub proof fn lemma_tail_used(r: Seq<i::Tlv>)
    requires
        tail_of(r) is Some,
    ensures
        tail_of(r)->Some_0.3 <= r.len(),
{
}

// ---------------------------------------------------------------------
// TBSCertificate, from `tbs/spec.rs`.
// ---------------------------------------------------------------------

/// What `tbs/spec.rs` keeps as octets, the other decoders read.
pub open spec fn tbs_parts_decode(a: t::TbsCertificate) -> bool {
    &&& n::parse_name(a.issuer_der) is Some
    &&& name_tags_plain(n::parse_name(a.issuer_der)->Some_0)
    &&& n::parse_name(a.subject_der) is Some
    &&& name_tags_plain(n::parse_name(a.subject_der)->Some_0)
    &&& k::parse_subject_public_key_info(a.subject_public_key_info_der) is Some
    &&& parameters_plain(k::parse_subject_public_key_info(a.subject_public_key_info_der)->Some_0.algorithm)
    &&& parameters_plain(a.signature)
    &&& a.not_before.second != 60
    &&& a.not_after.second != 60
    &&& extensions_decode(a.extensions_sequence_der)
}

/// The fields of a TBSCertificate agree, in the crate's terms.
pub open spec fn tbs_agree(a: t::TbsCertificate, y: s::TBSCertificate) -> bool {
    &&& a.version as int == y.version
    &&& i::parse_single(a.serial_number_der) is Some
    &&& i::decode_integer(i::parse_single(a.serial_number_der)->Some_0) == Some(y.serial_number)
    &&& algorithm_agree(a.signature, y.signature)
    &&& a.not_before == moment_time(time_moment(y.validity.not_before))
    &&& a.not_after == moment_time(time_moment(y.validity.not_after))
    &&& unique_agree(a.issuer_unique_id_der, y.issuer_unique_identifier)
    &&& unique_agree(a.subject_unique_id_der, y.subject_unique_identifier)
    &&& optional_extensions_agree(a.extensions_sequence_der, y.extensions)
    &&& a.tbs_certificate_der == y.encoding
}

/// From `signature` on, the list of a TBSCertificate, from `tbs/spec.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_tbs_rest_fwd(b: Seq<u8>, p: nat, end: nat, a: t::TbsCertificate, version: nat)
    requires
        wf(b, p, end),
        end - p < two64(),
        tbs_parts_decode(a),
        ({
            match t::parse_signature_issuer(b, p, end) {
                None => false,
                Some((signature, issuer, p4)) => match t::parse_validity(b, p4, end) {
                    None => false,
                    Some((not_before, not_after, p5)) => match t::parse_subject_spki(b, p5, end) {
                        None => false,
                        Some((subject, spki, p7)) => match t::parse_optional_tail(b, p7, end, version) {
                            None => false,
                            Some(tail) => {
                                &&& signature == a.signature
                                &&& issuer == a.issuer_der
                                &&& not_before == a.not_before
                                &&& not_after == a.not_after
                                &&& subject == a.subject_der
                                &&& spki == a.subject_public_key_info_der
                                &&& tail.issuer_unique_id_der == a.issuer_unique_id_der
                                &&& tail.subject_unique_id_der == a.subject_unique_id_der
                                &&& tail.extensions_der == a.extensions_der
                                &&& tail.extensions_sequence_der == a.extensions_sequence_der
                            },
                        },
                    },
                },
            }
        }),
    ensures
        i::parse_tlvs(sl(b, p, end)) is Some,
        ({
            let l = i::parse_tlvs(sl(b, p, end))->Some_0;
            &&& l.len() >= 5
            &&& s::decode_algorithm_identifier(l[0]) is Some
            &&& algorithm_agree(a.signature, s::decode_algorithm_identifier(l[0])->Some_0)
            &&& s::decode_name(l[1]) is Some
            &&& name_agree(n::parse_name(a.issuer_der)->Some_0, s::decode_name(l[1])->Some_0)
            &&& s::decode_validity(l[2]) is Some
            &&& a.not_before == moment_time(time_moment(s::decode_validity(l[2])->Some_0.not_before))
            &&& a.not_after == moment_time(time_moment(s::decode_validity(l[2])->Some_0.not_after))
            &&& s::decode_name(l[3]) is Some
            &&& name_agree(n::parse_name(a.subject_der)->Some_0, s::decode_name(l[3])->Some_0)
            &&& s::decode_subject_public_key_info(l[4]) is Some
            &&& spki_agree(
                k::parse_subject_public_key_info(a.subject_public_key_info_der)->Some_0,
                s::decode_subject_public_key_info(l[4])->Some_0,
            )
            &&& tail_of(l.skip(5)) is Some
            &&& tail_of(l.skip(5))->Some_0.3 == l.skip(5).len()
            &&& unique_agree(a.issuer_unique_id_der, tail_of(l.skip(5))->Some_0.0)
            &&& unique_agree(a.subject_unique_id_der, tail_of(l.skip(5))->Some_0.1)
            &&& optional_extensions_agree(a.extensions_sequence_der, tail_of(l.skip(5))->Some_0.2)
        }),
{
    hide(i::parse_tlv);
    hide(i::parse_tlvs);
    hide(d::read_tlv);
    hide(tail_of);
    hide(name_agree);
    hide(spki_agree);
    hide(algorithm_agree);
    hide(unique_agree);
    hide(optional_extensions_agree);
    hide(moment_time);
    hide(name_tags_plain);
    hide(parameters_plain);
    hide(extensions_decode);
    hide(n::parse_name);
    hide(k::parse_subject_public_key_info);
    hide(s::decode_name);
    hide(s::decode_algorithm_identifier);
    hide(s::decode_subject_public_key_info);
    hide(s::decode_validity);
    hide(t::parse_signature_issuer);
    hide(t::parse_validity);
    hide(t::parse_subject_spki);
    hide(t::parse_optional_tail);
    let (signature, issuer, p4) = t::parse_signature_issuer(b, p, end)->Some_0;
    lemma_signature_issuer_bound(b, p, end);
    let (not_before, not_after, p5) = t::parse_validity(b, p4, end)->Some_0;
    lemma_validity_fwd(b, p4, end);
    let (subject, spki, p7) = t::parse_subject_spki(b, p5, end)->Some_0;
    lemma_subject_spki_bound(b, p5, end);
    lemma_tail_fwd(b, p7, end, version);
    let l6 = i::parse_tlvs(sl(b, p7, end))->Some_0;
    lemma_subject_spki_fwd(b, p5, end, l6);
    let l4 = i::parse_tlvs(sl(b, p5, end))->Some_0;
    lemma_tlvs_cons(b, p4, end, l4);
    let vu = i::parse_tlv(sl(b, p4, end))->Some_0;
    let l3 = seq![vu] + l4;
    lemma_signature_issuer_fwd(b, p, end, l3);
    let l = i::parse_tlvs(sl(b, p, end))->Some_0;
    assert(l.skip(2) == l3);
    assert(l3[0] == vu);
    assert(l3[1] == l4[0]);
    assert(l3[2] == l4[1]);
    assert(l[2] == l.skip(2)[0]);
    assert(l[3] == l.skip(2)[1]);
    assert(l[4] == l.skip(2)[2]);
    lemma_skip_skip(l, 2, 3);
    assert(l3.skip(3) =~= l4.skip(2));
    assert(l.skip(5) == l4.skip(2));
}

/// `parse_signature_issuer` moves forward, inside the range.
pub proof fn lemma_signature_issuer_bound(b: Seq<u8>, pos: nat, end: nat)
    requires
        pos <= end,
        t::parse_signature_issuer(b, pos, end) is Some,
    ensures
        pos <= t::parse_signature_issuer(b, pos, end)->Some_0.2 <= end,
{
    let (a, after) = c::parse_algorithm_identifier(b, pos, end)->Some_0;
    let r = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    clazel_der::lemmas::lemma_read_tlv_bounds(b, after, end);
    assert(after == r.cend) by {
        if d::read_oid(b, r.cstart, r.cend) is Some {
            clazel_der::lemmas::lemma_read_tlv_bounds(b, r.cstart, r.cend);
        }
    }
}

/// `parse_subject_spki` moves forward, inside the range.
pub proof fn lemma_subject_spki_bound(b: Seq<u8>, pos: nat, end: nat)
    requires
        pos <= end,
        t::parse_subject_spki(b, pos, end) is Some,
    ensures
        pos <= t::parse_subject_spki(b, pos, end)->Some_0.2 <= end,
{
    let w = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    clazel_der::lemmas::lemma_read_tlv_bounds(b, w.cend, end);
}

/// `parse_prefix`, opened once.
pub proof fn lemma_prefix_opens(input: Seq<u8>)
    requires
        t::parse_prefix(input) is Some,
    ensures
        ({
            let prefix = t::parse_prefix(input)->Some_0;
            let len = input.len();
            let outer = d::read_tlv(input, 0, len)->Some_0;
            &&& d::read_tlv(input, 0, len) is Some
            &&& outer.tag == d::universal_constructed(d::SEQUENCE)
            &&& outer.cend == len
            &&& 0 < outer.cstart <= len
            &&& prefix.end == len
            &&& t::parse_version(input, outer.cstart, len) is Some
            &&& prefix.version == t::parse_version(input, outer.cstart, len)->Some_0.0
            &&& t::parse_serial(input, t::parse_version(input, outer.cstart, len)->Some_0.1, len) == Some(
                (prefix.serial_der, prefix.pos),
            )
            &&& prefix.tbs_der =~= input
        }),
{
    clazel_der::lemmas::lemma_read_tlv_bounds(input, 0, input.len());
}

/// `parse_prefix`, closed again.
pub proof fn lemma_prefix_closes(input: Seq<u8>)
    requires
        d::read_tlv(input, 0, input.len()) is Some,
        d::read_tlv(input, 0, input.len())->Some_0.tag == d::universal_constructed(d::SEQUENCE),
        d::read_tlv(input, 0, input.len())->Some_0.cend == input.len(),
        ({
            let start = d::read_tlv(input, 0, input.len())->Some_0.cstart;
            &&& t::parse_version(input, start, input.len()) is Some
            &&& t::parse_serial(input, t::parse_version(input, start, input.len())->Some_0.1, input.len()) is Some
        }),
    ensures
        t::parse_prefix(input) is Some,
        ({
            let prefix = t::parse_prefix(input)->Some_0;
            let start = d::read_tlv(input, 0, input.len())->Some_0.cstart;
            let (version, p1) = t::parse_version(input, start, input.len())->Some_0;
            let (serial, p2) = t::parse_serial(input, p1, input.len())->Some_0;
            &&& prefix.version == version
            &&& prefix.serial_der == serial
            &&& prefix.pos == p2
            &&& prefix.end == input.len()
            &&& prefix.tbs_der =~= input
        }),
{
}

/// `version` and `serialNumber`, from `tbs/spec.rs`, before the list `lr`.
#[verifier::spinoff_prover]
pub proof fn lemma_tbs_head_fwd(b: Seq<u8>, start: nat, end: nat, lr: Seq<i::Tlv>)
    requires
        wf(b, start, end),
        end - start < two64(),
        t::parse_version(b, start, end) is Some,
        t::parse_serial(b, t::parse_version(b, start, end)->Some_0.1, end) is Some,
        i::parse_tlvs(
            sl(b, t::parse_serial(b, t::parse_version(b, start, end)->Some_0.1, end)->Some_0.1, end),
        ) == Some(lr),
    ensures
        i::parse_tlvs(sl(b, start, end)) is Some,
        ({
            let l = i::parse_tlvs(sl(b, start, end))->Some_0;
            let m = s::after_version(l);
            let (version, p1) = t::parse_version(b, start, end)->Some_0;
            let (serial, p2) = t::parse_serial(b, p1, end)->Some_0;
            &&& m + 1 + lr.len() == l.len()
            &&& l.skip((m + 1) as int) == lr
            &&& s::version_component(l) == Some(version as int)
            &&& i::decode_integer(l[m as int]) is Some
            &&& i::parse_single(serial) == Some(l[m as int])
        }),
{
    hide(s::decode_version);
    hide(i::parse_tlvs);
    hide(t::parse_serial);
    let (version, p1) = t::parse_version(b, start, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, start, end);
    let w = d::read_tlv(b, start, end)->Some_0;
    assert(start <= p1 <= end) by {
        if w.tag == d::context_specific(0, true) {
            lemma_version_fwd(b, start, end);
        }
    }
    let (serial, p2) = t::parse_serial(b, p1, end)->Some_0;
    lemma_serial_fwd(b, p1, end);
    lemma_tlvs_cons(b, p1, end, lr);
    let su = i::parse_tlv(sl(b, p1, end))->Some_0;
    let l0 = seq![su] + lr;
    assert(su.class == 0 && su.number == 2);
    assert(l0[0] == su);
    if w.tag == d::context_specific(0, true) {
        lemma_version_fwd(b, start, end);
        lemma_tlvs_cons(b, start, end, l0);
        let vu = i::parse_tlv(sl(b, start, end))->Some_0;
        let l = seq![vu] + l0;
        assert(l[0] == vu);
        assert(l[1] == su);
        assert(s::after_version(l) == 1);
        assert(l.skip(2) =~= lr);
    } else {
        assert(p1 == start);
        assert(s::after_version(l0) == 0);
        assert(l0.skip(1) =~= lr);
    }
}

/// The fields of a TBSCertificate, from the list and what follows `serialNumber`.
#[verifier::spinoff_prover]
pub proof fn lemma_tbs_build(u: i::Tlv, l: Seq<i::Tlv>, lr: Seq<i::Tlv>, version: int)
    requires
        s::sequence_elements(u) == Some(l),
        s::after_version(l) + 1 + lr.len() == l.len(),
        l.skip((s::after_version(l) + 1) as int) == lr,
        s::version_component(l) == Some(version),
        i::decode_integer(l[s::after_version(l) as int]) is Some,
        lr.len() >= 5,
        s::decode_algorithm_identifier(lr[0]) is Some,
        s::decode_name(lr[1]) is Some,
        s::decode_validity(lr[2]) is Some,
        s::decode_name(lr[3]) is Some,
        s::decode_subject_public_key_info(lr[4]) is Some,
        tail_of(lr.skip(5)) is Some,
    ensures
        s::decode_tbs_certificate(u) is Some,
        ({
            let y = s::decode_tbs_certificate(u)->Some_0;
            &&& y.version == version
            &&& Some(y.serial_number) == i::decode_integer(l[s::after_version(l) as int])
            &&& Some(y.signature) == s::decode_algorithm_identifier(lr[0])
            &&& Some(y.issuer) == s::decode_name(lr[1])
            &&& Some(y.validity) == s::decode_validity(lr[2])
            &&& Some(y.subject) == s::decode_name(lr[3])
            &&& Some(y.subject_public_key_info) == s::decode_subject_public_key_info(lr[4])
            &&& y.issuer_unique_identifier == tail_of(lr.skip(5))->Some_0.0
            &&& y.subject_unique_identifier == tail_of(lr.skip(5))->Some_0.1
            &&& y.extensions == tail_of(lr.skip(5))->Some_0.2
            &&& y.encoding == u.encoding
        }),
{
    hide(s::decode_algorithm_identifier);
    hide(s::decode_name);
    hide(s::decode_validity);
    hide(s::decode_subject_public_key_info);
    hide(s::decode_tbs_certificate);
    hide(tail_of);
    let m = s::after_version(l);
    assert(forall|q: int| 0 <= q < lr.len() ==> #[trigger] lr[q] == l[m as int + 1 + q]);
    assert(lr[0] == l[(m + 1) as int]);
    assert(lr[1] == l[(m + 2) as int]);
    assert(lr[2] == l[(m + 3) as int]);
    assert(lr[3] == l[(m + 4) as int]);
    assert(lr[4] == l[(m + 5) as int]);
    assert(lr.skip(5) =~= l.skip((m + 6) as int));
    let tail = tail_of(lr.skip(5))->Some_0;
    let y = s::TBSCertificate {
        version,
        serial_number: i::decode_integer(l[m as int])->Some_0,
        signature: s::decode_algorithm_identifier(lr[0])->Some_0,
        issuer: s::decode_name(lr[1])->Some_0,
        validity: s::decode_validity(lr[2])->Some_0,
        subject: s::decode_name(lr[3])->Some_0,
        subject_public_key_info: s::decode_subject_public_key_info(lr[4])->Some_0,
        issuer_unique_identifier: tail.0,
        subject_unique_identifier: tail.1,
        extensions: tail.2,
        additions: i::from_index(l, m + 6 + tail.3),
        encoding: u.encoding,
    };
    assert(tbs_fields(l, y));
    lemma_tbs_closes(u, l, y);
}

/// **`theorem_tbs`, from `tbs/spec.rs`.**
#[verifier::spinoff_prover]
pub proof fn theorem_tbs_fwd(input: Seq<u8>)
    requires
        input.len() < two64(),
        t::parse_tbs_certificate(input) is Some,
        tbs_parts_decode(t::parse_tbs_certificate(input)->Some_0),
    ensures
        i::parse_single(input) is Some,
        s::decode_tbs_certificate(i::parse_single(input)->Some_0) is Some,
        ({
            let a = t::parse_tbs_certificate(input)->Some_0;
            let y = s::decode_tbs_certificate(i::parse_single(input)->Some_0)->Some_0;
            &&& tbs_agree(a, y)
            &&& name_agree(n::parse_name(a.issuer_der)->Some_0, y.issuer)
            &&& name_agree(n::parse_name(a.subject_der)->Some_0, y.subject)
            &&& spki_agree(
                k::parse_subject_public_key_info(a.subject_public_key_info_der)->Some_0,
                y.subject_public_key_info,
            )
        }),
{
    hide(i::parse_tlv);
    hide(i::parse_tlvs);
    hide(d::read_tlv);
    hide(tail_of);
    hide(name_agree);
    hide(spki_agree);
    hide(algorithm_agree);
    hide(unique_agree);
    hide(optional_extensions_agree);
    hide(moment_time);
    hide(name_tags_plain);
    hide(parameters_plain);
    hide(extensions_decode);
    hide(n::parse_name);
    hide(k::parse_subject_public_key_info);
    hide(s::decode_name);
    hide(s::decode_algorithm_identifier);
    hide(s::decode_subject_public_key_info);
    hide(s::decode_validity);
    hide(t::parse_signature_issuer);
    hide(t::parse_validity);
    hide(t::parse_subject_spki);
    hide(t::parse_optional_tail);
    hide(t::parse_prefix);
    hide(t::parse_version);
    hide(t::parse_serial);
    hide(s::decode_tbs_certificate);
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    let a = t::parse_tbs_certificate(input)->Some_0;
    let prefix = t::parse_prefix(input)->Some_0;
    lemma_prefix_opens(input);
    let outer = d::read_tlv(b, 0, len)->Some_0;
    let start = outer.cstart;
    let end = len;
    let (version, p1) = t::parse_version(b, start, end)->Some_0;
    let p2 = prefix.pos;
    lemma_tbs_prefix_position(b, start, end);
    lemma_tbs_rest_fwd(b, p2, end, a, version);
    let lr = i::parse_tlvs(sl(b, p2, end))->Some_0;
    lemma_tbs_head_fwd(b, start, end, lr);
    let l = i::parse_tlvs(sl(b, start, end))->Some_0;
    let m = s::after_version(l);
    lemma_sequence_fwd(b, 0, len, l);
    lemma_read_is_plain(b, 0, len);
    lemma_single(b, 0, len);
    let u = i::parse_single(input)->Some_0;
    lemma_tbs_build(u, l, lr, version as int);
    lemma_single_is_input(input, u);
}

/// The cursor after the serial number is inside the range.
pub proof fn lemma_tbs_prefix_position(b: Seq<u8>, start: nat, end: nat)
    requires
        wf(b, start, end),
        t::parse_version(b, start, end) is Some,
        t::parse_serial(b, t::parse_version(b, start, end)->Some_0.1, end) is Some,
    ensures
        start <= t::parse_version(b, start, end)->Some_0.1 <= end,
        t::parse_version(b, start, end)->Some_0.1 <= t::parse_serial(
            b,
            t::parse_version(b, start, end)->Some_0.1,
            end,
        )->Some_0.1 <= end,
{
    clazel_der::lemmas::lemma_read_tlv_bounds(b, start, end);
    let p1 = t::parse_version(b, start, end)->Some_0.1;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, p1, end);
}

/// A SEQUENCE's tag is not the reserved one.
pub proof fn lemma_read_is_plain(b: Seq<u8>, pos: nat, end: nat)
    requires
        d::read_tlv(b, pos, end) is Some,
        d::read_tlv(b, pos, end)->Some_0.tag == d::universal_constructed(d::SEQUENCE),
    ensures
        !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag),
{
}

/// One encoding's octets are the input.
pub proof fn lemma_single_is_input(input: Seq<u8>, u: i::Tlv)
    requires
        i::parse_single(input) == Some(u),
    ensures
        u.encoding == input,
{
    assert(u.encoding =~= input);
}

// ---------------------------------------------------------------------
// TBSCertificate, from `structures.rs`.
// ---------------------------------------------------------------------

/// What the domain asks of a TBSCertificate.
pub open spec fn tbs_in_domain(y: s::TBSCertificate) -> bool {
    &&& y.additions.len() == 0
    &&& 0 <= y.serial_number < serial_limit()
    &&& 0 <= y.version <= 2
    &&& y.extensions is Some ==> y.version == 2 && extensions_in_domain(y.extensions->Some_0)
    &&& (y.issuer_unique_identifier is Some || y.subject_unique_identifier is Some) ==> y.version >= 1
    &&& algorithm_in_domain(y.signature)
    &&& y.issuer.rdn_sequence.len() > 0
    &&& validity_in_domain(y.validity)
}

/// From `signature` on, from `structures.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_tbs_rest_back(
    b: Seq<u8>,
    p: nat,
    end: nat,
    version: nat,
    l: Seq<i::Tlv>,
    y: s::TBSCertificate,
)
    requires
        wf(b, p, end),
        end - p < two64(),
        i::parse_tlvs(sl(b, p, end)) == Some(l),
        l.len() >= 5,
        s::decode_algorithm_identifier(l[0]) == Some(y.signature),
        s::decode_name(l[1]) == Some(y.issuer),
        s::decode_validity(l[2]) == Some(y.validity),
        s::decode_name(l[3]) == Some(y.subject),
        s::decode_subject_public_key_info(l[4]) == Some(y.subject_public_key_info),
        tail_of(l.skip(5)) is Some,
        tail_of(l.skip(5))->Some_0.0 == y.issuer_unique_identifier,
        tail_of(l.skip(5))->Some_0.1 == y.subject_unique_identifier,
        tail_of(l.skip(5))->Some_0.2 == y.extensions,
        tail_of(l.skip(5))->Some_0.3 == l.skip(5).len(),
        tbs_in_domain(y),
        version as int == y.version,
    ensures
        ({
            match t::parse_signature_issuer(b, p, end) {
                None => false,
                Some((signature, issuer, p4)) => match t::parse_validity(b, p4, end) {
                    None => false,
                    Some((not_before, not_after, p5)) => match t::parse_subject_spki(b, p5, end) {
                        None => false,
                        Some((subject, spki, p7)) => match t::parse_optional_tail(b, p7, end, version) {
                            None => false,
                            Some(tail) => {
                                &&& algorithm_agree(signature, y.signature)
                                &&& i::parse_single(issuer) == Some(l[1])
                                &&& not_before == moment_time(time_moment(y.validity.not_before))
                                &&& not_after == moment_time(time_moment(y.validity.not_after))
                                &&& i::parse_single(subject) == Some(l[3])
                                &&& i::parse_single(spki) == Some(l[4])
                                &&& unique_agree(tail.issuer_unique_id_der, y.issuer_unique_identifier)
                                &&& unique_agree(tail.subject_unique_id_der, y.subject_unique_identifier)
                                &&& optional_extensions_agree(tail.extensions_sequence_der, y.extensions)
                            },
                        },
                    },
                },
            }
        }),
{
    hide(i::parse_tlv);
    hide(i::parse_tlvs);
    hide(d::read_tlv);
    hide(tail_of);
    hide(algorithm_agree);
    hide(unique_agree);
    hide(optional_extensions_agree);
    hide(moment_time);
    hide(extensions_in_domain);
    hide(validity_in_domain);
    hide(algorithm_in_domain);
    hide(s::decode_name);
    hide(s::decode_algorithm_identifier);
    hide(s::decode_subject_public_key_info);
    hide(s::decode_validity);
    hide(t::parse_signature_issuer);
    hide(t::parse_validity);
    hide(t::parse_subject_spki);
    hide(t::parse_optional_tail);
    lemma_signature_issuer_back(b, p, end, l, y.signature, y.issuer);
    let (signature, issuer, p4) = t::parse_signature_issuer(b, p, end)->Some_0;
    let l3 = l.skip(2);
    assert(l3[0] == l[2]);
    lemma_validity_tag(l[2]);
    lemma_tlvs_head(b, p4, end, l3);
    lemma_validity_back(b, p4, end, l3[0], y.validity);
    let (not_before, not_after, p5) = t::parse_validity(b, p4, end)->Some_0;
    let w = d::read_tlv(b, p4, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, p4, end);
    assert(w.cend == p5);
    let l4 = l3.skip(1);
    lemma_skip_skip(l, 2, 1);
    assert(l4[0] == l[3]);
    assert(l4[1] == l[4]);
    lemma_subject_spki_back(b, p5, end, l4);
    let (subject, spki, p7) = t::parse_subject_spki(b, p5, end)->Some_0;
    lemma_skip_skip(l, 3, 2);
    let l6 = l4.skip(2);
    lemma_tail_back(b, p7, end, version, l6);
}

/// Validity is a SEQUENCE.
pub proof fn lemma_validity_tag(u: i::Tlv)
    requires
        s::decode_validity(u) is Some,
    ensures
        tag_fits(u),
{
}

/// **`theorem_tbs`, from `structures.rs`.**
#[verifier::spinoff_prover]
pub proof fn theorem_tbs_back(input: Seq<u8>, u: i::Tlv, y: s::TBSCertificate)
    requires
        input.len() < two64(),
        i::parse_single(input) == Some(u),
        s::decode_tbs_certificate(u) == Some(y),
        tbs_in_domain(y),
    ensures
        t::parse_tbs_certificate(input) is Some,
        tbs_agree(t::parse_tbs_certificate(input)->Some_0, y),
        ({
            let a = t::parse_tbs_certificate(input)->Some_0;
            let l = s::sequence_elements(u)->Some_0;
            let m = s::after_version(l);
            &&& i::parse_single(a.issuer_der) == Some(l[(m + 2) as int])
            &&& i::parse_single(a.subject_der) == Some(l[(m + 4) as int])
            &&& i::parse_single(a.subject_public_key_info_der) == Some(l[(m + 5) as int])
        }),
{
    hide(i::parse_tlv);
    hide(i::parse_tlvs);
    hide(d::read_tlv);
    hide(tail_of);
    hide(algorithm_agree);
    hide(unique_agree);
    hide(optional_extensions_agree);
    hide(moment_time);
    hide(extensions_in_domain);
    hide(validity_in_domain);
    hide(algorithm_in_domain);
    hide(s::decode_name);
    hide(s::decode_algorithm_identifier);
    hide(s::decode_subject_public_key_info);
    hide(s::decode_validity);
    hide(t::parse_signature_issuer);
    hide(t::parse_validity);
    hide(t::parse_subject_spki);
    hide(t::parse_optional_tail);
    hide(t::parse_prefix);
    hide(t::parse_version);
    hide(t::parse_serial);
    hide(s::decode_tbs_certificate);
    hide(s::version_component);
    hide(i::decode_integer);
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    lemma_tbs_opens(u, y);
    let l = s::sequence_elements(u)->Some_0;
    let m = s::after_version(l);
    lemma_tbs_tag(u, y);
    lemma_single_back(b, 0, len, u);
    lemma_tlv_of_single(b, u);
    lemma_sequence_back(b, 0, len, u, l);
    let outer = d::read_tlv(b, 0, len)->Some_0;
    let (start, end) = (outer.cstart, outer.cend);
    assert(end == len);
    lemma_first_tag(l, y);
    lemma_version_back(b, start, end, l, y.version);
    let (version, p1) = t::parse_version(b, start, end)->Some_0;
    let l0 = l.skip(m as int);
    assert(l0[0] == l[m as int]);
    lemma_serial_back(b, p1, end, l0, y.serial_number);
    let (serial, p2) = t::parse_serial(b, p1, end)->Some_0;
    let lr = l0.skip(1);
    lemma_skip_skip(l, m as int, 1);
    assert(lr[0] == l[(m + 1) as int]);
    assert(lr[1] == l[(m + 2) as int]);
    assert(lr[2] == l[(m + 3) as int]);
    assert(lr[3] == l[(m + 4) as int]);
    assert(lr[4] == l[(m + 5) as int]);
    assert(lr.skip(5) =~= l.skip((m + 6) as int));
    let tail = l.skip((m + 6) as int);
    lemma_tail_used(tail);
    let used = tail_of(tail)->Some_0.3;
    assert(used == tail.len()) by {
        if used < tail.len() {
            assert(i::from_index(l, m + 6 + used).len() == l.len() - (m + 6 + used));
        }
    }
    lemma_tbs_rest_back(b, p2, end, version, lr, y);
    lemma_prefix_closes(input);
    let (signature, issuer, p4) = t::parse_signature_issuer(b, p2, end)->Some_0;
    let (not_before, not_after, p5) = t::parse_validity(b, p4, end)->Some_0;
    let (subject, spki, p7) = t::parse_subject_spki(b, p5, end)->Some_0;
    let a = t::parse_tbs_certificate(input)->Some_0;
    lemma_single_is_input(input, u);
    assert(a.tbs_certificate_der =~= u.encoding);
}

/// `decode_tbs_certificate` reads a SEQUENCE, whose tag is small.
pub proof fn lemma_tbs_tag(u: i::Tlv, y: s::TBSCertificate)
    requires
        s::decode_tbs_certificate(u) == Some(y),
    ensures
        tag_fits(u),
{
    lemma_tbs_opens(u, y);
}

/// `parse_single` is `parse_tlv` of the whole slice.
pub proof fn lemma_tlv_of_single(b: Seq<u8>, u: i::Tlv)
    requires
        i::parse_single(b) == Some(u),
    ensures
        i::parse_tlv(sl(b, 0, b.len())) == Some(u),
{
    assert(sl(b, 0, b.len()) =~= b);
}

/// The first encoding of a TBSCertificate is `[0]` or the serial number.
pub proof fn lemma_first_tag(l: Seq<i::Tlv>, y: s::TBSCertificate)
    requires
        tbs_fields(l, y),
    ensures
        l.len() > 0,
        tag_fits(l[0]),
{
}

// ---------------------------------------------------------------------
// Certificate.
// ---------------------------------------------------------------------

/// `parse_algorithm_identifier` ends where its encoding does.
pub proof fn lemma_algorithm_bound(b: Seq<u8>, pos: nat, end: nat)
    requires
        pos <= end,
        c::parse_algorithm_identifier(b, pos, end) is Some,
    ensures
        d::read_tlv(b, pos, end) is Some,
        d::read_tlv(b, pos, end)->Some_0.cend == c::parse_algorithm_identifier(b, pos, end)->Some_0.1,
{
}

/// The three components of the outer SEQUENCE, from `certificate/spec.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_envelope_fwd(input: Seq<u8>)
    requires
        input.len() < two64(),
        c::parse_certificate(input) is Some,
        parameters_plain(c::parse_certificate(input)->Some_0.signature_algorithm),
    ensures
        ({
            let a = c::parse_certificate(input)->Some_0;
            &&& i::parse_single(input) is Some
            &&& s::sequence_elements(i::parse_single(input)->Some_0) is Some
            &&& {
                let l = s::sequence_elements(i::parse_single(input)->Some_0)->Some_0;
                &&& l.len() == 3
                &&& i::parse_single(a.tbs_certificate_der) == Some(l[0])
                &&& s::decode_algorithm_identifier(l[1]) is Some
                &&& algorithm_agree(a.signature_algorithm, s::decode_algorithm_identifier(l[1])->Some_0)
                &&& i::decode_bit_string(l[2]) == Some(
                    i::BitString { octets: a.signature_bits, unused: a.signature_unused_bits as nat },
                )
            }
        }),
{
    hide(s::decode_algorithm_identifier);
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    let a = c::parse_certificate(input)->Some_0;
    let outer = d::read_tlv(b, 0, len)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, 0, len);
    let (start, end) = (outer.cstart, outer.cend);
    let tbs = d::read_tlv(b, start, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, start, end);
    let (algorithm, after) = c::parse_algorithm_identifier(b, tbs.cend, end)->Some_0;
    lemma_algorithm_fwd(b, tbs.cend, end);
    lemma_read_bit_string(b, after, end);
    let none = Seq::<i::Tlv>::empty();
    lemma_tlvs_empty(b, end);
    lemma_tlvs_cons(b, after, end, none);
    let su = i::parse_tlv(sl(b, after, end))->Some_0;
    lemma_tlvs_cons(b, tbs.cend, end, seq![su] + none);
    let au = i::parse_tlv(sl(b, tbs.cend, end))->Some_0;
    assert(!tag_is_reserved(tbs.tag));
    lemma_tlvs_cons(b, start, end, seq![au] + (seq![su] + none));
    lemma_tlv_alone(b, start, end);
    let tu = i::parse_tlv(sl(b, start, end))->Some_0;
    let l = seq![tu] + (seq![au] + (seq![su] + none));
    lemma_sequence_fwd(b, 0, len, l);
    lemma_single(b, 0, len);
    assert(l[0] == tu);
    assert(l[1] == au);
    assert(l[2] == su);
    assert(l.len() == 3);
}

/// The three components of the outer SEQUENCE, from `structures.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_envelope_back(input: Seq<u8>, u: i::Tlv, l: Seq<i::Tlv>, algorithm: s::AlgorithmIdentifier)
    requires
        input.len() < two64(),
        i::parse_single(input) == Some(u),
        s::sequence_elements(u) == Some(l),
        l.len() == 3,
        l[0].class == 0 && l[0].number == 16 && l[0].constructed,
        s::decode_algorithm_identifier(l[1]) == Some(algorithm),
        algorithm_in_domain(algorithm),
        i::decode_bit_string(l[2]) is Some,
    ensures
        c::parse_certificate(input) is Some,
        ({
            let a = c::parse_certificate(input)->Some_0;
            &&& i::parse_single(a.tbs_certificate_der) == Some(l[0])
            &&& algorithm_agree(a.signature_algorithm, algorithm)
            &&& i::decode_bit_string(l[2]) == Some(
                i::BitString { octets: a.signature_bits, unused: a.signature_unused_bits as nat },
            )
        }),
{
    hide(s::decode_algorithm_identifier);
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    assert(tag_fits(u));
    lemma_single_back(b, 0, len, u);
    lemma_sequence_back(b, 0, len, u, l);
    let outer = d::read_tlv(b, 0, len)->Some_0;
    let (start, end) = (outer.cstart, outer.cend);
    assert(outer.cend == len);
    assert(tag_fits(l[0]));
    lemma_tlvs_head(b, start, end, l);
    let tbs = d::read_tlv(b, start, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, start, end);
    lemma_has_universal_tag(b, start, tbs, l[0], d::SEQUENCE, true);
    lemma_tlv_alone(b, start, end);
    let r = l.skip(1);
    assert(r[0] == l[1]);
    assert(r[1] == l[2]);
    lemma_algorithm_tag(l[1]);
    lemma_tlvs_head(b, tbs.cend, end, r);
    lemma_algorithm_back(b, tbs.cend, end, l[1], algorithm);
    let (a, after) = c::parse_algorithm_identifier(b, tbs.cend, end)->Some_0;
    let w = d::read_tlv(b, tbs.cend, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, tbs.cend, end);
    assert(w.cend == after);
    let q = r.skip(1);
    assert(q[0] == l[2]);
    assert(tag_fits(l[2]));
    lemma_tlvs_head(b, after, end, q);
    lemma_read_bit_string(b, after, end);
    let v = d::read_tlv(b, after, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, after, end);
    lemma_tlvs_none_left(b, v.cend, end, q.skip(1));
    assert(d::expect_sequence(b, start, end) == Some((tbs.cstart, tbs.cend)));
}

/// AlgorithmIdentifier is a SEQUENCE.
pub proof fn lemma_algorithm_tag(u: i::Tlv)
    requires
        s::decode_algorithm_identifier(u) is Some,
    ensures
        tag_fits(u),
{
}

/// `decode_certificate`, opened once, for a certificate of the domain.
#[verifier::spinoff_prover]
pub proof fn lemma_certificate_opens(der: Seq<u8>, y: s::Certificate)
    requires
        s::decode_certificate(der) == Some(y),
        y.additions.len() == 0,
        r::one_signature_only(y),
    ensures
        i::parse_single(der) is Some,
        s::sequence_elements(i::parse_single(der)->Some_0) is Some,
        ({
            let l = s::sequence_elements(i::parse_single(der)->Some_0)->Some_0;
            &&& l.len() == 3
            &&& s::decode_tbs_certificate(l[0]) == Some(y.to_be_signed)
            &&& s::decode_algorithm_identifier(l[1]) == Some(y.algorithm_identifier)
            &&& i::decode_bit_string(l[2]) == Some(y.signature)
        }),
{
    hide(s::decode_tbs_certificate);
    hide(s::decode_algorithm_identifier);
    let u = i::parse_single(der)->Some_0;
    let l = s::sequence_elements(u)->Some_0;
    let (first, second, next) = s::alternative_signature(l)->Some_0;
    assert(next == 3);
    assert(i::from_index(l, next).len() == 0);
    if l.len() > 3 {
        assert(i::from_index(l, 3).len() == l.len() - 3);
    }
}

/// `decode_certificate` of the three components.
#[verifier::spinoff_prover]
pub proof fn lemma_certificate_closes(der: Seq<u8>)
    requires
        i::parse_single(der) is Some,
        s::sequence_elements(i::parse_single(der)->Some_0) is Some,
        s::sequence_elements(i::parse_single(der)->Some_0)->Some_0.len() == 3,
        s::decode_tbs_certificate(s::sequence_elements(i::parse_single(der)->Some_0)->Some_0[0]) is Some,
        s::decode_algorithm_identifier(s::sequence_elements(i::parse_single(der)->Some_0)->Some_0[1]) is Some,
        i::decode_bit_string(s::sequence_elements(i::parse_single(der)->Some_0)->Some_0[2]) is Some,
    ensures
        ({
            let l = s::sequence_elements(i::parse_single(der)->Some_0)->Some_0;
            &&& s::decode_certificate(der) is Some
            &&& s::decode_certificate(der)->Some_0.to_be_signed == s::decode_tbs_certificate(l[0])->Some_0
            &&& s::decode_certificate(der)->Some_0.algorithm_identifier == s::decode_algorithm_identifier(
                l[1],
            )->Some_0
            &&& s::decode_certificate(der)->Some_0.signature == i::decode_bit_string(l[2])->Some_0
        }),
{
    hide(s::decode_tbs_certificate);
    hide(s::decode_algorithm_identifier);
}

/// `crate_decode`, when every stage reads.
pub proof fn lemma_crate_decode_opens(der: Seq<u8>)
    requires
        crate_decode(der) is Some,
    ensures
        ({
            let a = crate_decode(der)->Some_0;
            &&& c::parse_certificate(der) == Some(a.envelope)
            &&& t::parse_tbs_certificate(a.envelope.tbs_certificate_der) == Some(a.tbs)
            &&& n::parse_name(a.tbs.issuer_der) == Some(a.issuer)
            &&& n::parse_name(a.tbs.subject_der) == Some(a.subject)
            &&& k::parse_subject_public_key_info(a.tbs.subject_public_key_info_der) == Some(a.spki)
            &&& match a.tbs.extensions_sequence_der {
                Some(v) => x::parse_extensions(v) is Some,
                None => true,
            }
        }),
{
}

/// **`theorem_certificate_equivalence`, from the crate.** What the crate's
/// decoders read, inside conditions 1 to 3, the transcription reads to the
/// same value.
#[verifier::spinoff_prover]
pub proof fn theorem_certificate_fwd(der: Seq<u8>)
    requires
        der.len() < two64(),
        crate_decode(der) is Some,
        decoded_in_domain(crate_decode(der)->Some_0),
    ensures
        s::decode_certificate(der) is Some,
        certificate_agree(crate_decode(der)->Some_0, s::decode_certificate(der)->Some_0),
{
    hide(n::parse_name);
    hide(k::parse_subject_public_key_info);
    hide(t::parse_tbs_certificate);
    hide(c::parse_certificate);
    hide(x::parse_extensions);
    hide(s::decode_tbs_certificate);
    hide(s::decode_algorithm_identifier);
    hide(name_agree);
    hide(spki_agree);
    hide(algorithm_agree);
    hide(unique_agree);
    hide(optional_extensions_agree);
    hide(name_tags_plain);
    hide(parameters_plain);
    hide(extensions_decode);
    hide(moment_time);
    let a = crate_decode(der)->Some_0;
    lemma_crate_decode_opens(der);
    lemma_envelope_fwd(der);
    let input = a.envelope.tbs_certificate_der;
    assert(input.len() < two64()) by {
        lemma_envelope_length(der);
    }
    assert(tbs_parts_decode(a.tbs));
    theorem_tbs_fwd(input);
    let u = i::parse_single(der)->Some_0;
    let l = s::sequence_elements(u)->Some_0;
    assert(i::parse_single(input) == Some(l[0]));
    lemma_certificate_closes(der);
    let y = s::decode_certificate(der)->Some_0;
    lemma_tbs_opens(l[0], y.to_be_signed);
    lemma_single_is_input(input, l[0]);
}

/// The TBSCertificate is shorter than the certificate.
pub proof fn lemma_envelope_length(der: Seq<u8>)
    requires
        c::parse_certificate(der) is Some,
    ensures
        c::parse_certificate(der)->Some_0.tbs_certificate_der.len() <= der.len(),
{
    let outer = d::read_tlv(der, 0, der.len())->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(der, 0, der.len());
    let tbs = d::read_tlv(der, outer.cstart, outer.cend)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(der, outer.cstart, outer.cend);
}

/// **`theorem_certificate_equivalence`, from the transcription.** What the
/// transcription reads, inside conditions 4 to 13, the crate's decoders read
/// to the same value.
#[verifier::spinoff_prover]
pub proof fn theorem_certificate_back(der: Seq<u8>, y: s::Certificate)
    requires
        der.len() < two64(),
        s::decode_certificate(der) == Some(y),
        certificate_in_domain(y),
    ensures
        crate_decode(der) is Some,
        certificate_agree(crate_decode(der)->Some_0, y),
{
    hide(name_agree);
    hide(spki_agree);
    hide(algorithm_agree);
    hide(unique_agree);
    hide(moment_time);
    hide(name_in_domain);
    hide(spki_in_domain);
    hide(algorithm_in_domain);
    hide(validity_in_domain);
    hide(extensions_in_domain);
    hide(n::parse_name);
    hide(k::parse_subject_public_key_info);
    hide(t::parse_tbs_certificate);
    hide(c::parse_certificate);
    hide(x::parse_extensions);
    hide(s::decode_tbs_certificate);
    hide(s::decode_algorithm_identifier);
    hide(s::decode_name);
    hide(s::decode_subject_public_key_info);
    lemma_certificate_opens(der, y);
    let u = i::parse_single(der)->Some_0;
    let l = s::sequence_elements(u)->Some_0;
    let b = y.to_be_signed;
    lemma_tbs_sequence(l[0], b);
    lemma_envelope_back(der, u, l, y.algorithm_identifier);
    let a = c::parse_certificate(der)->Some_0;
    let input = a.tbs_certificate_der;
    assert(input.len() < two64()) by {
        lemma_envelope_length(der);
    }
    assert(tbs_in_domain(b));
    theorem_tbs_back(input, l[0], b);
    let tb = t::parse_tbs_certificate(input)->Some_0;
    lemma_tbs_opens(l[0], b);
    let e0 = s::sequence_elements(l[0])->Some_0;
    let m = s::after_version(e0);
    assert(tb.issuer_der.len() < two64() && tb.subject_der.len() < two64()
        && tb.subject_public_key_info_der.len() < two64()) by {
        lemma_contents_length(input, l[0]);
        lemma_element_length(l[0].contents, e0, (m + 2) as int);
        lemma_element_length(l[0].contents, e0, (m + 4) as int);
        lemma_element_length(l[0].contents, e0, (m + 5) as int);
        lemma_contents_length(tb.issuer_der, e0[(m + 2) as int]);
        lemma_contents_length(tb.subject_der, e0[(m + 4) as int]);
        lemma_contents_length(tb.subject_public_key_info_der, e0[(m + 5) as int]);
    }
    theorem_name_back(tb.issuer_der, e0[(m + 2) as int], b.issuer);
    theorem_name_back(tb.subject_der, e0[(m + 4) as int], b.subject);
    theorem_spki_back(tb.subject_public_key_info_der, e0[(m + 5) as int], b.subject_public_key_info);
    lemma_single_is_input(input, l[0]);
    lemma_tbs_opens(l[0], b);
    assert(a.tbs_certificate_der == b.encoding);
    assert(crate_decode(der) is Some);
}

/// `decode_tbs_certificate` reads a SEQUENCE.
pub proof fn lemma_tbs_sequence(u: i::Tlv, y: s::TBSCertificate)
    requires
        s::decode_tbs_certificate(u) == Some(y),
    ensures
        u.class == 0 && u.number == 16 && u.constructed,
{
    lemma_tbs_opens(u, y);
}

/// An element of a list of encodings is no longer than the octets it came
/// from.
pub proof fn lemma_element_length(v: Seq<u8>, l: Seq<i::Tlv>, m: int)
    requires
        i::parse_tlvs(v) == Some(l),
        0 <= m < l.len(),
    ensures
        l[m].encoding.len() <= v.len(),
    decreases v.len(),
{
    let u = i::parse_tlv(v)->Some_0;
    let size = u.encoding.len();
    let tail = v.subrange(size as int, v.len() as int);
    let rest = i::parse_tlvs(tail)->Some_0;
    assert(l =~= seq![u] + rest);
    if m > 0 {
        assert(l[m] == rest[m - 1]);
        lemma_element_length(tail, rest, m - 1);
    }
}

/// The contents of an encoding are no longer than the encoding.
pub proof fn lemma_contents_length(input: Seq<u8>, u: i::Tlv)
    requires
        i::parse_single(input) == Some(u),
    ensures
        u.contents.len() <= input.len(),
        u.encoding.len() == input.len(),
{
}

/// **The theorem's domain**, on the octets: whichever decoder reads `der`, it
/// reads it inside the conditions.
pub open spec fn equivalence_domain(der: Seq<u8>) -> bool {
    &&& der.len() < two64()
    &&& crate_decode(der) is Some ==> decoded_in_domain(crate_decode(der)->Some_0)
    &&& s::decode_certificate(der) is Some ==> certificate_in_domain(s::decode_certificate(der)->Some_0)
}

/// **`theorem_certificate_equivalence`.** On the domain, the crate's decoders
/// and the transcription read the same octets, to the same values.
pub proof fn theorem_certificate_equivalence(der: Seq<u8>)
    requires
        equivalence_domain(der),
    ensures
        (crate_decode(der) is Some) == (s::decode_certificate(der) is Some),
        crate_decode(der) is Some ==> certificate_agree(
            crate_decode(der)->Some_0,
            s::decode_certificate(der)->Some_0,
        ),
{
    if crate_decode(der) is Some {
        theorem_certificate_fwd(der);
    }
    if s::decode_certificate(der) is Some {
        theorem_certificate_back(der, s::decode_certificate(der)->Some_0);
    }
}

} // verus!
