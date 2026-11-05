//! The "shall" clauses of Rec. ITU-T X.509 (10/2019) | ISO/IEC 9594-8:2020
//! about the content of a decoded certificate (PDF SHA-256
//! `1f4ea2939ecc31a3433c499084d485e770f9b8dcee55a0ba9fe4c27128822e8c`), for the
//! independent transcription: clauses 7.2.1, 7.3, 7.4 and 9, and X.501 9.3.
//!
//! Not read while writing this file: see the list in `independent/mod.rs`.
//!
//! Modelling choices:
//! - Each clause is one predicate over a decoded [`Certificate`], and
//!   [`certificate_requirements`] is their conjunction in clause order.
//!   `structures.rs` answers "is this a value of the type"; this file
//!   answers "does this value say what the prose requires".
//! - Many clauses bind the issuer, not the relying party ("the issuer ...
//!   shall hold a non-empty distinguished name"). A certificate that breaks
//!   one is not a conforming certificate, so each counts here. Which of them
//!   a relying party should enforce is a choice this file does not make: a
//!   caller can test any single predicate.
//! - "Recognized" is relative to a relying party (7.3). Extensions: those
//!   `extensions.rs` decodes. Name forms: the tags in
//!   [`RelyingParty::recognized_name_forms`], a parameter, since 9.3.2.1 and
//!   9.4.2.2 leave them open.
//! - A CA certificate is one with `cA` TRUE (7.4); any other is an end-entity
//!   certificate (9.4.2.1, last paragraph).
//!
//! Open choices, all listed in the pull request:
//! - 9's "no more than one instance of each extension type" covers extensions
//!   "defined in this Specification". Two instances of an extension from
//!   elsewhere are allowed, read literally. The list of extensions defined
//!   here is [`defined_in_this_specification`].
//! - 7.3's default, "treat the entire extension as unrecognized", is applied
//!   to a critical extension with unrecognized elements, and so makes the
//!   certificate invalid, in every extension except the two whose clauses
//!   say otherwise (9.3.2.1 and 9.4.2.2).
//! - 7.2.1 says "the same value" for the two signature algorithms. Two
//!   values of a type with an unread open-type field are compared by their
//!   encodings, which DER makes unique for a value of a known type.
//! - dNSName syntax (9.3.2.1) is [`dns_name_syntax`], which is not part of
//!   [`certificate_requirements`]: the text forbids `*`, while RFC 6125 6.4.3
//!   lets a client match it. See the entry in docs/ERRATA.md.
//! - `validity` has no check that `notBefore` precedes `notAfter`: the text
//!   does not state one.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der::*;
#[cfg(verus_only)]
use super::extensions::*;

#[cfg(verus_only)]
use super::structures::*;

verus! {

/// What 7.3, 9.3.2.1 and 9.4.2.2 leave to the relying party.
pub struct RelyingParty {
    /// The `GeneralName` context tags it processes.
    pub recognized_name_forms: Seq<nat>,
}

/// The first extension from `i` with this `extnId`.
pub open spec fn find_extension(exts: Seq<Extension>, i: nat, id: ObjectIdentifier) -> Option<
    Extension,
>
    decreases exts.len() - i,
{
    if i >= exts.len() {
        None
    } else if exts[i as int].extn_id == id {
        Some(exts[i as int])
    } else {
        find_extension(exts, i + 1, id)
    }
}

/// The certificate's extensions, none being the empty list.
pub open spec fn extensions_of(c: Certificate) -> Seq<Extension> {
    match c.to_be_signed.extensions {
        None => Seq::<Extension>::empty(),
        Some(x) => x,
    }
}

/// The certificate's `basicConstraints` value.
pub open spec fn basic_constraints_of(c: Certificate) -> Option<BasicConstraintsSyntax> {
    match find_extension(extensions_of(c), 0, id_ce_basic_constraints()) {
        None => None,
        Some(x) => match x.value {
            ExtensionValue::BasicConstraints(b) => Some(b),
            _ => None,
        },
    }
}

/// 7.4: "A CA certificate shall include the basicConstraints extension with
/// the cA components set to TRUE".
pub open spec fn is_ca_certificate(c: Certificate) -> bool {
    match basic_constraints_of(c) {
        None => false,
        Some(b) => b.c_a,
    }
}

// ---------------------------------------------------------------------------
// 7.2.1
// ---------------------------------------------------------------------------

/// 7.2.1: "the altAlgorithmIdentifier and the altSignature components shall
/// be absent."
pub open spec fn one_signature_only(c: Certificate) -> bool {
    c.alt_algorithm_identifier.is_none() && c.alt_signature.is_none()
}

/// 7.2.1: "The version component shall hold the version": one of the named
/// numbers. "If the extensions component is present ..., version shall be
/// v3. If the issuerUniqueIdentifier or subjectUniqueIdentifier component is
/// present version shall be v2 or v3."
///
/// The ASN.1 comment on `extensions` says "v2 or v3"; the prose and the
/// comment after it say v3. See docs/ERRATA.md.
pub open spec fn version_rules(c: Certificate) -> bool {
    let t = c.to_be_signed;
    0 <= t.version && t.version <= 2 && (t.extensions.is_some() ==> t.version == 2) && (
    (t.issuer_unique_identifier.is_some() || t.subject_unique_identifier.is_some()) ==> t.version
        >= 1)
}

/// 7.2.1: "It shall be the same value as used in the algorithmIdentifier
/// component of the SIGNATURE data type".
pub open spec fn signature_algorithms_agree(c: Certificate) -> bool {
    c.to_be_signed.signature.encoding == c.algorithm_identifier.encoding
}

/// 7.2.1: "It shall hold a non-empty distinguished name."
pub open spec fn issuer_non_empty(c: Certificate) -> bool {
    c.to_be_signed.issuer.rdn_sequence.len() > 0
}

/// 7.2.1: "If the public-key certificate is an end-entity public-key
/// certificate ..., then the distinguished name may be an empty sequence
/// providing that the subjectAltName extension is present and is flagged as
/// critical .... Otherwise, it shall be a non-empty distinguished name."
pub open spec fn subject_rule(c: Certificate) -> bool {
    c.to_be_signed.subject.rdn_sequence.len() > 0 || (!is_ca_certificate(c) && match find_extension(
        extensions_of(c),
        0,
        id_ce_subject_alt_name(),
    ) {
        None => false,
        Some(x) => x.critical,
    })
}

// ---------------------------------------------------------------------------
// 9 and 7.3
// ---------------------------------------------------------------------------

/// The certificate extensions defined in clause 9: 9.2.2 a) to h), 9.3.2,
/// 9.3.2.4, 9.4.2 a) to d), the distribution points of 9.6.2 used in
/// certificates (`cRLDistributionPoints`, `freshestCRL`), and 9.8.
pub open spec fn defined_in_this_specification(id: ObjectIdentifier) -> bool {
    id == id_ce(35) || id == id_ce(14) || id == id_ce(15) || id == id_ce(37) || id == id_ce(16)
        || id == id_ce(32) || id == id_ce(33) || id == id_ce(70) || id == id_ce(17) || id == id_ce(
        18,
    ) || id == id_ce(9) || id == id_ce(75) || id == id_ce(19) || id == id_ce(30) || id == id_ce(36)
        || id == id_ce(54) || id == id_ce(31) || id == id_ce(46) || id == id_ce(72) || id == id_ce(
        73,
    ) || id == id_ce(74)
}

/// No extension after `i` has `id`.
pub open spec fn absent_from(exts: Seq<Extension>, i: nat, id: ObjectIdentifier) -> bool {
    find_extension(exts, i, id).is_none()
}

/// 9: "there shall be no more than one instance of each extension type".
pub open spec fn no_duplicate_extensions(exts: Seq<Extension>, i: nat) -> bool
    decreases exts.len() - i,
{
    if i >= exts.len() {
        true
    } else {
        (!defined_in_this_specification(exts[i as int].extn_id) || absent_from(
            exts,
            i + 1,
            exts[i as int].extn_id,
        )) && no_duplicate_extensions(exts, i + 1)
    }
}

/// `name` is of a form the relying party processes.
pub open spec fn name_form_tag(name: GeneralName) -> Option<nat> {
    match name {
        GeneralName::OtherName { .. } => Some(0),
        GeneralName::Rfc822Name(_) => Some(1),
        GeneralName::DNSName(_) => Some(2),
        GeneralName::X400Address(_) => Some(3),
        GeneralName::DirectoryName(_) => Some(4),
        GeneralName::EdiPartyName(_) => Some(5),
        GeneralName::UniformResourceIdentifier(_) => Some(6),
        GeneralName::IPAddress(_) => Some(7),
        GeneralName::RegisteredID(_) => Some(8),
        GeneralName::Unknown(_) => None,
    }
}

/// `tag` is in `forms`, from `i`.
pub open spec fn tag_listed(forms: Seq<nat>, i: nat, tag: nat) -> bool
    decreases forms.len() - i,
{
    if i >= forms.len() {
        false
    } else {
        forms[i as int] == tag || tag_listed(forms, i + 1, tag)
    }
}

/// `name`'s form is one of `rp`'s.
pub open spec fn name_form_recognized(rp: RelyingParty, name: GeneralName) -> bool {
    match name_form_tag(name) {
        None => false,
        Some(tag) => tag_listed(rp.recognized_name_forms, 0, tag),
    }
}

/// 9.3.2.1: "If the extension is flagged as critical, at least one of the name
/// forms that is present shall be recognized and processed".
pub open spec fn some_name_form_recognized(rp: RelyingParty, names: Seq<GeneralName>, i: nat) -> bool
    decreases names.len() - i,
{
    if i >= names.len() {
        false
    } else {
        name_form_recognized(rp, names[i as int]) || some_name_form_recognized(rp, names, i + 1)
    }
}

/// 9.4.2.2: every `base` is of a recognized form.
pub open spec fn all_bases_recognized(rp: RelyingParty, trees: Seq<GeneralSubtree>, i: nat) -> bool
    decreases trees.len() - i,
{
    if i >= trees.len() {
        true
    } else {
        name_form_recognized(rp, trees[i as int].base) && all_bases_recognized(rp, trees, i + 1)
    }
}

/// An `Option` of subtrees, all recognized.
pub open spec fn optional_bases_recognized(
    rp: RelyingParty,
    trees: Option<Seq<GeneralSubtree>>,
) -> bool {
    match trees {
        None => true,
        Some(t) => all_bases_recognized(rp, t, 0),
    }
}

/// No PolicyInformation or qualifier from `i` has additions.
pub open spec fn qualifiers_closed(q: Seq<PolicyQualifierInfo>, i: nat) -> bool
    decreases q.len() - i,
{
    if i >= q.len() {
        true
    } else {
        q[i as int].additions.len() == 0 && qualifiers_closed(q, i + 1)
    }
}

/// No PolicyInformation from `i` has additions.
pub open spec fn policies_closed(p: Seq<PolicyInformation>, i: nat) -> bool
    decreases p.len() - i,
{
    if i >= p.len() {
        true
    } else {
        p[i as int].additions.len() == 0 && match p[i as int].policy_qualifiers {
            None => true,
            Some(q) => qualifiers_closed(q, 0),
        } && policies_closed(p, i + 1)
    }
}

/// No subtree from `i` has additions.
pub open spec fn subtrees_closed(t: Seq<GeneralSubtree>, i: nat) -> bool
    decreases t.len() - i,
{
    if i >= t.len() {
        true
    } else {
        t[i as int].additions.len() == 0 && subtrees_closed(t, i + 1)
    }
}

/// An `Option` of subtrees, none with additions.
pub open spec fn optional_subtrees_closed(t: Option<Seq<GeneralSubtree>>) -> bool {
    match t {
        None => true,
        Some(s) => subtrees_closed(s, 0),
    }
}

/// The extension has no unrecognized elements inside its value.
pub open spec fn value_closed(x: Extension) -> bool {
    x.additions.len() == 0 && match x.value {
        ExtensionValue::AuthorityKeyIdentifier(v) => v.additions.len() == 0,
        ExtensionValue::CertificatePolicies(v) => policies_closed(v, 0),
        ExtensionValue::BasicConstraints(v) => v.additions.len() == 0,
        ExtensionValue::NameConstraints(v) => v.additions.len() == 0 && optional_subtrees_closed(
            v.permitted_subtrees,
        ) && optional_subtrees_closed(v.excluded_subtrees),
        ExtensionValue::PolicyConstraints(v) => v.additions.len() == 0,
        _ => true,
    }
}

/// 7.3's relying-party actions a) to c) for one extension.
pub open spec fn extension_acceptable(rp: RelyingParty, x: Extension) -> bool {
    if !x.critical {
        // 7.3 a) "shall ignore the extension", and "If unrecognized elements
        // appear within the extension, and the extension is not flagged as
        // critical, those unrecognized elements shall be ignored".
        true
    } else {
        match x.value {
            // 7.3 b) "if the extension is unrecognized and flagged as
            // critical, the relying party shall consider the public-key
            // certificate as invalid".
            ExtensionValue::Unrecognized => false,
            ExtensionValue::SubjectAltName(names) => x.additions.len() == 0
                && some_name_form_recognized(rp, names, 0),
            // 9.4.2.2: "does not recognize a name form used in any base
            // component ... as if an unrecognized critical extension had been
            // encountered".
            ExtensionValue::NameConstraints(v) => value_closed(x) && optional_bases_recognized(
                rp,
                v.permitted_subtrees,
            ) && optional_bases_recognized(rp, v.excluded_subtrees),
            // 7.3: "the default behaviour, when not specified specifically for
            // an extension, is to treat the entire extension as unrecognized."
            _ => value_closed(x),
        }
    }
}

/// 7.3 for every extension from `i`.
pub open spec fn extensions_acceptable(rp: RelyingParty, exts: Seq<Extension>, i: nat) -> bool
    decreases exts.len() - i,
{
    if i >= exts.len() {
        true
    } else {
        extension_acceptable(rp, exts[i as int]) && extensions_acceptable(rp, exts, i + 1)
    }
}

/// Whether an extension of this id, if present, is non-critical.
pub open spec fn not_flagged_critical(c: Certificate, id: ObjectIdentifier) -> bool {
    match find_extension(extensions_of(c), 0, id) {
        None => true,
        Some(x) => !x.critical,
    }
}

/// 9.2.2.1 and 9.2.2.2: "This extension shall always be flagged as
/// non-critical."
pub open spec fn key_identifiers_non_critical(c: Certificate) -> bool {
    not_flagged_critical(c, id_ce_authority_key_identifier()) && not_flagged_critical(
        c,
        id_ce_subject_key_identifier(),
    )
}

/// 9.2.2.3: "If KeyUsage is set to keyCertSign, the value of the cA component
/// of the basicConstraints extension shall be set to TRUE."
pub open spec fn key_cert_sign_rule(c: Certificate) -> bool {
    match find_extension(extensions_of(c), 0, id_ce_key_usage()) {
        None => true,
        Some(x) => match x.value {
            ExtensionValue::KeyUsage(bits) => !bit_is_set(bits, 5) || is_ca_certificate(c),
            _ => true,
        },
    }
}

/// 9.3.2.1: "(four octets) ... (16 octets)", for each `iPAddress` from `i`.
pub open spec fn ip_addresses_sized(names: Seq<GeneralName>, i: nat) -> bool
    decreases names.len() - i,
{
    if i >= names.len() {
        true
    } else {
        (match names[i as int] {
            GeneralName::IPAddress(a) => a.len() == 4 || a.len() == 16,
            _ => true,
        }) && ip_addresses_sized(names, i + 1)
    }
}

/// 9.3.2.1 for the subject alternative name.
pub open spec fn subject_alt_name_rules(c: Certificate) -> bool {
    match find_extension(extensions_of(c), 0, id_ce_subject_alt_name()) {
        None => true,
        Some(x) => match x.value {
            ExtensionValue::SubjectAltName(names) => ip_addresses_sized(names, 0),
            _ => true,
        },
    }
}

/// 9.4.2.1: "The pathLenConstraint component may be present if cA component
/// is set to TRUE. Otherwise, it shall be absent." and "This extension shall
/// be present in a CA certificate with the cA component set to TRUE and
/// flagged as critical".
pub open spec fn basic_constraints_rules(c: Certificate) -> bool {
    match find_extension(extensions_of(c), 0, id_ce_basic_constraints()) {
        None => true,
        Some(x) => match x.value {
            ExtensionValue::BasicConstraints(b) => (b.path_len_constraint.is_none() || b.c_a) && (
            !b.c_a || x.critical),
            _ => true,
        },
    }
}

/// 9.4.2: "Name constraints and policy constraints shall be used only in CA
/// certificates".
pub open spec fn ca_only_extensions(c: Certificate) -> bool {
    is_ca_certificate(c) || (absent_from(extensions_of(c), 0, id_ce_name_constraints())
        && absent_from(extensions_of(c), 0, id_ce_policy_constraints()))
}

/// Everything above, in clause order. `decode_certificate` and this together
/// say that `der` is a conforming certificate for `rp`.
pub open spec fn certificate_requirements(rp: RelyingParty, c: Certificate) -> bool {
    &&& one_signature_only(c)
    &&& version_rules(c)
    &&& signature_algorithms_agree(c)
    &&& issuer_non_empty(c)
    &&& subject_rule(c)
    &&& extensions_acceptable(rp, extensions_of(c), 0)
    &&& no_duplicate_extensions(extensions_of(c), 0)
    &&& key_identifiers_non_critical(c)
    &&& key_cert_sign_rule(c)
    &&& subject_alt_name_rules(c)
    &&& basic_constraints_rules(c)
    &&& ca_only_extensions(c)
}

/// X.501 9.3: "a given attribute type cannot appear twice in the same RDN",
/// for the attributes after `i`.
pub open spec fn attribute_absent(rdn: RelativeDistinguishedName, i: nat, t: ObjectIdentifier) -> bool
    decreases rdn.len() - i,
{
    if i >= rdn.len() {
        true
    } else {
        rdn[i as int].attribute_type != t && attribute_absent(rdn, i + 1, t)
    }
}

/// X.501 9.3 for one RDN.
pub open spec fn rdn_types_distinct(rdn: RelativeDistinguishedName, i: nat) -> bool
    decreases rdn.len() - i,
{
    if i >= rdn.len() {
        true
    } else {
        attribute_absent(rdn, i + 1, rdn[i as int].attribute_type) && rdn_types_distinct(rdn, i + 1)
    }
}

/// X.501 9.3 for a whole name.
pub open spec fn name_types_distinct(rdns: Seq<RelativeDistinguishedName>, i: nat) -> bool
    decreases rdns.len() - i,
{
    if i >= rdns.len() {
        true
    } else {
        rdn_types_distinct(rdns[i as int], 0) && name_types_distinct(rdns, i + 1)
    }
}

/// 9.3.2.1 a): a label's characters, code points "002D, 0030-0039, 0041-005A
/// and 0061-007A".
pub open spec fn is_ldh(c: u8) -> bool {
    c == 0x2D || (0x30 <= c && c <= 0x39) || (0x41 <= c && c <= 0x5A) || (0x61 <= c && c <= 0x7A)
}

/// The characters of `s` from `i`: LDH, with dots separating non-empty labels
/// of at most 63 octets (9.3.2.1 a)). `run` is the current label's length.
pub open spec fn dns_label_run(s: Seq<u8>, i: nat, run: nat) -> bool
    decreases s.len() - i,
{
    if i >= s.len() {
        run > 0
    } else if s[i as int] == 0x2E {
        run > 0 && dns_label_run(s, i + 1, 0)
    } else {
        is_ldh(s[i as int]) && run < 63 && dns_label_run(s, i + 1, run + 1)
    }
}

/// 9.3.2.1: "a sequence of labels in the letters, digits, hyphen (LDH) format
/// separated by dots". Whether an A-label converts to a valid U-label (item
/// b)) is not checked: that needs IDNA tables.
pub open spec fn dns_name_syntax(s: Seq<u8>) -> bool {
    dns_label_run(s, 0, 0)
}

} // verus!
