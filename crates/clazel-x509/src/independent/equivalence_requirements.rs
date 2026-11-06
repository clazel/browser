//! `requirements.rs`, predicate by predicate, against what production does.
//!
//! Most clauses of X.509 are checked by the crate at decoding or in the path
//! rules, not in one place. So each theorem here takes a certificate
//! `parse_path_cert` kept, [`theorem_reading`] puts the two values side by
//! side, and the theorem says which clause follows and under which role: a
//! target (`leaf/spec.rs`, `path/profile.rs`, §6.1.5) or an intermediate
//! (§6.1.4).
//!
//! | `requirements.rs` | Result | Theorem |
//! |---|---|---|
//! | `one_signature_only` | always | `theorem_one_signature` |
//! | `version_rules` | always | `theorem_version_rules` |
//! | `signature_algorithms_agree` | one way: `equivalence_signature.rs`; RSA NULL against absent stays | `theorem_signature_algorithms` |
//! | `issuer_non_empty` | always | `theorem_issuer_non_empty` |
//! | `subject_rule` | **not enforced** | `example_path_conditions_hold` |
//! | `extensions_acceptable` | any role, for a relying party with every form | `theorem_extensions_acceptable` |
//! | `no_duplicate_extensions` | always, and stricter: RFC 5280 covers foreign ids | `theorem_no_duplicates` |
//! | `key_identifiers_non_critical` | any role | `theorem_key_identifiers` |
//! | `key_cert_sign_rule` | any role | `theorem_key_cert_sign_leaf`, `_ca` |
//! | `subject_alt_name_rules` | always | `theorem_subject_alt_name_rules` |
//! | `basic_constraints_rules` | half: the cA criticality is **not enforced** | `theorem_basic_constraints_rules` |
//! | `ca_only_extensions` | nameConstraints on a target refused; policyConstraints **not enforced** | `theorem_ca_only` |
//! | `dns_name_syntax` | the crate's shape is wider: no 63-octet limit | `theorem_dns_name_syntax` |
//! | `name_types_distinct` | **not enforced**, and outside `certificate_requirements` | below |
//!
//! `is_ca_certificate`, `basic_constraints_of`, `find_extension`, `extensions_of`,
//! `value_closed` and the name form predicates are what those use, and are
//! proven through them. `lemma_is_ca` states the first directly.
//!
//! **The three clauses production does not enforce.** Each binds the issuer,
//! and each is a choice, not an oversight, in the crate's tests or specs:
//! - `subject_rule`, the critical subjectAltName of an empty subject:
//!   `tests/limbo/expected_failures.rs`, `CABF_SAN_CRITICALITY` ("the profile
//!   adds no rule"; `rfc5280::san::noncritical-with-empty-subject`).
//! - `basic_constraints_rules`' "flagged as critical": neither `leaf/spec.rs`
//!   nor §6.1.4 (k) reads the flag of basicConstraints, and RFC 5280 §6.1.4 (k)
//!   does not ask it of a relying party.
//! - `ca_only_extensions`' policyConstraints on a target: `path/profile.rs`
//!   refuses nameConstraints there and has no rule for policyConstraints.
//!
//! X.501 9.3's `name_types_distinct`: `name/spec.rs` has no such rule and
//! production does not parse the Name.

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
use super::equivalence_structures::*;
#[cfg(verus_only)]
use super::equivalence_tbs::*;
#[cfg(verus_only)]
use super::equivalence_values::*;
#[cfg(verus_only)]
use super::extensions as e;
#[cfg(verus_only)]
use super::requirements as r;
#[cfg(verus_only)]
use super::structures as s;
#[cfg(verus_only)]
use crate::certificate::spec as c;
#[cfg(verus_only)]
use crate::constraints::spec as cs;
#[cfg(verus_only)]
use crate::extensions::spec as x;
#[cfg(verus_only)]
use crate::leaf::spec as lf;
#[cfg(verus_only)]
use crate::name_constraints::spec as nc;
#[cfg(verus_only)]
use crate::path::parsed::spec as ps;
#[cfg(verus_only)]
use crate::path::spec as pt;
#[cfg(verus_only)]
use crate::policy_constraints::spec as pc;
#[cfg(verus_only)]
use crate::spec as h;
#[cfg(verus_only)]
use crate::tbs::spec as t;

verus! {

// ---------------------------------------------------------------------
// The two readings, side by side.
// ---------------------------------------------------------------------

/// What holds of the list the crate read and the one the transcription read.
pub open spec fn reading(p: ps::PathCert, v: Seq<e::Extension>) -> bool {
    &&& path_values_agree(p, v)
    &&& values_read(v)
    &&& values_in_domain(v)
    &&& forall|k: int| 0 <= k < v.len() ==> extension_in_domain(#[trigger] v[k])
    &&& forall|j: int, k: int| 0 <= j < k < v.len() ==> #[trigger] v[j].extn_id != #[trigger] v[k].extn_id
}

/// The id that gives each kind of value.
pub proof fn lemma_value_ids(id: Seq<nat>, input: Seq<u8>, val: e::ExtensionValue)
    requires
        e::decode_extension_value(id, input) == Some(val),
    ensures
        val is BasicConstraints ==> id == e::id_ce_basic_constraints(),
        val is KeyUsage ==> id == e::id_ce_key_usage(),
        val is ExtKeyUsage ==> id == e::id_ce_ext_key_usage(),
        val is NameConstraints ==> id == e::id_ce_name_constraints(),
        val is SubjectAltName ==> id == e::id_ce_subject_alt_name(),
        val is PolicyConstraints ==> id == e::id_ce_policy_constraints(),
{
}

/// A value of the six the crate reads is in its domain, once the lookup read it.
#[verifier::spinoff_prover]
pub proof fn lemma_value_in_domain(list: Seq<x::Extension>, v: Seq<e::Extension>, k: int)
    requires
        lookup_ready(list, v),
        0 <= k < v.len(),
        forall|a: int, b: int| 0 <= a < b < list.len() ==> #[trigger] list[a].oid != #[trigger] list[b].oid,
        lf::optional_basic_constraints(list) is Some,
        lf::optional_key_usage(list) is Some,
        lf::optional_extended_key_usage(list) is Some,
        ps::optional_name_constraints(list) is Some,
        ps::optional_subject_alt_name(list) is Some,
        ps::optional_policy_constraints(list) is Some,
        match ps::optional_subject_alt_name(list)->Some_0 {
            Some(q) => san_forms_decode(q),
            None => true,
        },
        match ps::optional_name_constraints(list)->Some_0 {
            Some(q) => name_constraints_decodes(q),
            None => true,
        },
    ensures
        value_in_domain(v[k]),
{
    hide(cs::parse_basic_constraints);
    hide(cs::parse_key_usage);
    hide(cs::parse_extended_key_usage);
    hide(nc::parse_name_constraints);
    hide(x::parse_subject_alt_name);
    hide(pc::parse_policy_constraints);
    hide(e::decode_extension_value);
    hide(name_constraints_decodes);
    hide(san_forms_decode);
    let y = v[k];
    let a = list[k];
    assert(extension_agree(a, y));
    assert(e::decode_extension_value(y.extn_id, y.extn_value) == Some(y.value));
    assert(a.value.len() < two64());
    lemma_lookups_read(list, k);
    assert(value_has_its_id(y.extn_id, y.extn_value, y.value)) by {
        reveal(e::decode_extension_value);
        lemma_value_ids(y.extn_id, y.extn_value, y.value);
    }
    match y.value {
        e::ExtensionValue::BasicConstraints(w) => {
            theorem_basic_constraints_fwd(y.extn_value);
        },
        e::ExtensionValue::KeyUsage(w) => {
            theorem_key_usage_fwd(y.extn_value);
        },
        e::ExtensionValue::ExtKeyUsage(w) => {
            theorem_ext_key_usage_fwd(y.extn_value);
        },
        e::ExtensionValue::NameConstraints(w) => {
            theorem_name_constraints_fwd(y.extn_value);
        },
        e::ExtensionValue::SubjectAltName(w) => {
            reveal(san_forms_decode);
            theorem_subject_alt_name_fwd(y.extn_value);
        },
        e::ExtensionValue::PolicyConstraints(w) => {
            theorem_policy_constraints_fwd(y.extn_value);
        },
        _ => {},
    }
}

/// `lemma_value_ids`' conclusions, as one predicate.
pub open spec fn value_has_its_id(id: Seq<nat>, input: Seq<u8>, val: e::ExtensionValue) -> bool {
    &&& val is BasicConstraints ==> id == e::id_ce_basic_constraints()
    &&& val is KeyUsage ==> id == e::id_ce_key_usage()
    &&& val is ExtKeyUsage ==> id == e::id_ce_ext_key_usage()
    &&& val is NameConstraints ==> id == e::id_ce_name_constraints()
    &&& val is SubjectAltName ==> id == e::id_ce_subject_alt_name()
    &&& val is PolicyConstraints ==> id == e::id_ce_policy_constraints()
}

/// **`theorem_reading`.** Everything the theorems below use, for a certificate
/// `parse_path_cert` kept. The list is the frame's, so nothing here asks that
/// the Names or the key decode.
#[verifier::spinoff_prover]
pub proof fn theorem_reading(der: Seq<u8>)
    requires
        der.len() < two64(),
        ps::parse_path_cert(der) is Some,
        path_conditions(ps::parse_path_cert(der)->Some_0),
    ensures
        decode_certificate_frame(der) is Some,
        reading(ps::parse_path_cert(der)->Some_0, listed(decode_certificate_frame(der)->Some_0.to_be_signed.extensions)),
{
    hide(ps::parse_path_cert);
    hide(c::parse_certificate);
    hide(t::parse_tbs_certificate);
    hide(x::parse_extensions);
    hide(lf::optional_basic_constraints);
    hide(lf::optional_key_usage);
    hide(lf::optional_extended_key_usage);
    hide(ps::optional_name_constraints);
    hide(ps::optional_subject_alt_name);
    hide(ps::optional_policy_constraints);
    hide(decode_certificate_frame);
    hide(path_conditions);
    hide(value_decodes);
    hide(tbs_frame_agree);
    hide(path_values_agree);
    hide(extension_in_domain);
    hide(value_in_domain);
    hide(lookup_ready);
    let p = ps::parse_path_cert(der)->Some_0;
    theorem_path_cert_fwd(der);
    lemma_path_opens(der);
    let f = decode_certificate_frame(der)->Some_0;
    let v = listed(f.to_be_signed.extensions);
    let list = p.extensions;
    let tb = p.tbs;
    let input = p.envelope.tbs_certificate_der;
    assert(input.len() <= der.len()) by {
        reveal(c::parse_certificate);
        lemma_envelope_length(der);
    }
    lemma_sequence_length(input, tb);
    if let Some(q) = tb.extensions_sequence_der {
        lemma_extensions_shape(q, list);
    }
    assert(extensions_agree(list, v)) by {
        reveal(path_values_agree);
    }
    assert(values_read(v)) by {
        if f.to_be_signed.extensions is Some {
            lemma_frame_values(der, f);
        }
    }
    assert(lookup_ready(list, v)) by {
        reveal(lookup_ready);
    }
    assert(optional_extensions_agree(tb.extensions_sequence_der, f.to_be_signed.extensions)) by {
        reveal(tbs_frame_agree);
    }
    assert forall|k: int| 0 <= k < v.len() implies value_in_domain(#[trigger] v[k]) by {
        reveal(path_conditions);
        lemma_value_in_domain(list, v, k);
    }
    assert forall|k: int| 0 <= k < v.len() implies extension_in_domain(#[trigger] v[k]) by {
        assert(f.to_be_signed.extensions is Some);
    }
    assert forall|j: int, k: int| 0 <= j < k < v.len() implies #[trigger] v[j].extn_id != #[trigger] v[k].extn_id by {
        assert(extension_agree(list[j], v[j]));
        assert(extension_agree(list[k], v[k]));
        assert(list[j].oid != list[k].oid);
    }
}

// ---------------------------------------------------------------------
// 7.2.1.
// ---------------------------------------------------------------------

/// **7.2.1, `one_signature_only`.** A certificate `parse_certificate` read has
/// neither alt component, and no addition.
#[verifier::spinoff_prover]
pub proof fn theorem_one_signature(der: Seq<u8>, y: s::Certificate)
    requires
        der.len() < two64(),
        c::parse_certificate(der) is Some,
        parameters_plain(c::parse_certificate(der)->Some_0.signature_algorithm),
        s::decode_certificate(der) == Some(y),
    ensures
        r::one_signature_only(y),
        y.additions.len() == 0,
{
    hide(s::decode_tbs_certificate);
    hide(s::decode_algorithm_identifier);
    hide(c::parse_certificate);
    lemma_envelope_fwd(der);
    let u = i::parse_single(der)->Some_0;
    let l = s::sequence_elements(u)->Some_0;
    assert(s::alternative_signature(l) == Some((None::<s::AlgorithmIdentifier>, None::<i::BitString>, 3nat)));
    assert(i::from_index(l, 3).len() == 0);
}

/// What `parse_tbs_certificate` read about the version.
#[verifier::spinoff_prover]
pub proof fn lemma_tbs_version(input: Seq<u8>, tb: t::TbsCertificate)
    requires
        t::parse_tbs_certificate(input) == Some(tb),
    ensures
        tb.version <= 2,
        tb.extensions_sequence_der is Some ==> tb.version == 2,
        (tb.issuer_unique_id_der is Some || tb.subject_unique_id_der is Some) ==> tb.version >= 1,
{
    hide(t::parse_signature_issuer);
    hide(t::parse_validity);
    hide(t::parse_subject_spki);
    hide(t::parse_serial);
    let prefix = t::parse_prefix(input)->Some_0;
    lemma_prefix_opens(input);
}

/// **7.2.1, `version_rules`.** What `tbs/spec.rs` read keeps them.
pub proof fn theorem_version_rules(input: Seq<u8>, tb: t::TbsCertificate, y: s::Certificate)
    requires
        t::parse_tbs_certificate(input) == Some(tb),
        tbs_read_agree(tb, y.to_be_signed),
    ensures
        r::version_rules(y),
{
    hide(t::parse_tbs_certificate);
    lemma_tbs_version(input, tb);
}

/// An element list of non-empty contents is not empty.
pub proof fn lemma_some_element(u: i::Tlv, l: Seq<i::Tlv>)
    requires
        i::parse_tlvs(u.contents) == Some(l),
        u.contents.len() > 0,
    ensures
        l.len() > 0,
{
}

/// `decode_rdn_list` gives one value for each element.
pub proof fn lemma_rdn_list_len(l: Seq<i::Tlv>, k: nat)
    requires
        k <= l.len(),
        s::decode_rdn_list(l, k) is Some,
    ensures
        s::decode_rdn_list(l, k)->Some_0.len() == l.len() - k,
    decreases l.len() - k,
{
    if k < l.len() {
        lemma_rdn_list_len(l, k + 1);
    }
}

/// **7.2.1, `issuer_non_empty`.** The frame's issuer has contents, so, if it
/// decodes, it has an RDN.
pub proof fn theorem_issuer_non_empty(der: Seq<u8>, f: CertificateFrame)
    requires
        decode_certificate_frame(der) == Some(f),
        s::decode_name(f.to_be_signed.issuer) is Some,
        s::decode_name(f.to_be_signed.subject) is Some,
        s::decode_subject_public_key_info(f.to_be_signed.subject_public_key_info) is Some,
    ensures
        s::decode_certificate(der) is Some,
        r::issuer_non_empty(s::decode_certificate(der)->Some_0),
{
    theorem_frame_completes(der, f);
    let g = f.to_be_signed;
    assert(g.issuer.contents.len() > 0) by {
        let u = i::parse_single(der)->Some_0;
        let l = s::sequence_elements(u)->Some_0;
        lemma_frame_issuer(l[0], g);
    }
    let l = s::sequence_elements(g.issuer)->Some_0;
    lemma_some_element(g.issuer, l);
    lemma_rdn_list_len(l, 0);
}

/// The frame's test of the issuer.
pub proof fn lemma_frame_issuer(u: i::Tlv, g: TbsFrame)
    requires
        decode_tbs_frame(u) == Some(g),
    ensures
        g.issuer.contents.len() > 0,
{
}

// ---------------------------------------------------------------------
// Clause 9: lists.
// ---------------------------------------------------------------------

/// No extension from `k` has `id`.
pub proof fn lemma_absent(v: Seq<e::Extension>, k: nat, id: s::ObjectIdentifier)
    requires
        forall|m: int| k <= m < v.len() ==> (#[trigger] v[m]).extn_id != id,
    ensures
        r::find_extension(v, k, id) is None,
    decreases v.len() - k,
{
    if k < v.len() {
        lemma_absent(v, k + 1, id);
    }
}

/// Distinct identifiers from `k`.
pub proof fn lemma_no_duplicates(v: Seq<e::Extension>, k: nat)
    requires
        forall|a: int, b: int| 0 <= a < b < v.len() ==> #[trigger] v[a].extn_id != #[trigger] v[b].extn_id,
    ensures
        r::no_duplicate_extensions(v, k),
    decreases v.len() - k,
{
    if k < v.len() {
        assert forall|m: int| k + 1 <= m < v.len() implies (#[trigger] v[m]).extn_id != v[k as int].extn_id by {
            assert(v[k as int].extn_id != v[m].extn_id);
        }
        lemma_absent(v, k + 1, v[k as int].extn_id);
        lemma_no_duplicates(v, k + 1);
    }
}

/// **9, `no_duplicate_extensions`.** Every list the crate reads has none, for
/// every extension. The clause covers only those of this Specification; the
/// crate is stricter, by RFC 5280 §4.2 (condition 13 of `equivalence.rs`).
pub proof fn theorem_no_duplicates(p: ps::PathCert, v: Seq<e::Extension>)
    requires
        reading(p, v),
    ensures
        r::no_duplicate_extensions(v, 0),
{
    lemma_no_duplicates(v, 0);
}

/// `intermediate_critical_supported` holds of each extension.
pub proof fn lemma_critical_at(a: Seq<x::Extension>, k: int, m: int)
    requires
        0 <= k <= m < a.len(),
        pt::intermediate_critical_supported(a, k),
    ensures
        !a[m].critical || a[m].oid =~= lf::basic_constraints_oid() || a[m].oid =~= lf::key_usage_oid()
            || a[m].oid =~= lf::extended_key_usage_extension_oid() || a[m].oid =~= nc::name_constraints_oid()
            || a[m].oid =~= x::subject_alt_name_oid() || a[m].oid =~= pc::policy_constraints_oid(),
    decreases m - k,
{
    if k < m {
        lemma_critical_at(a, k + 1, m);
    }
}

/// **The target's set of critical extensions is inside an intermediate's.**
pub proof fn lemma_leaf_critical(a: Seq<x::Extension>, k: int)
    requires
        0 <= k <= a.len(),
        lf::supported_critical_extensions(a, k),
    ensures
        pt::intermediate_critical_supported(a, k),
    decreases a.len() - k,
{
    if k < a.len() {
        lemma_leaf_critical(a, k + 1);
    }
}

/// The one extension of `oid` is not critical, if `oid` is not one of the six.
pub proof fn lemma_not_critical(a: Seq<x::Extension>, v: Seq<e::Extension>, oid: Seq<nat>, last: nat)
    requires
        extensions_agree(a, v),
        pt::intermediate_critical_supported(a, 0),
        oid == e::id_ce(last),
        last != 19 && last != 15 && last != 37 && last != 30 && last != 17 && last != 36,
    ensures
        match r::find_extension(v, 0, oid) {
            None => true,
            Some(y) => !y.critical,
        },
{
    lemma_find(a, v, oid, 0);
    if let Some(idx) = lf::find_extension_index(a, oid, 0) {
        assert(extension_agree(a[idx], v[idx]));
        lemma_critical_at(a, 0, idx);
        lemma_oids();
        lemma_id_ce_differ(last, 19);
        lemma_id_ce_differ(last, 15);
        lemma_id_ce_differ(last, 37);
        lemma_id_ce_differ(last, 30);
        lemma_id_ce_differ(last, 17);
        lemma_id_ce_differ(last, 36);
    }
}

/// **9.2.2.1, 9.2.2.2, `key_identifiers_non_critical`.** Both are outside the
/// set a target or an intermediate may flag critical.
pub proof fn theorem_key_identifiers(p: ps::PathCert, y: s::Certificate)
    requires
        extensions_agree(p.extensions, r::extensions_of(y)),
        pt::intermediate_critical_supported(p.extensions, 0),
    ensures
        r::key_identifiers_non_critical(y),
{
    lemma_not_critical(p.extensions, r::extensions_of(y), e::id_ce_authority_key_identifier(), 35);
    lemma_not_critical(p.extensions, r::extensions_of(y), e::id_ce_subject_key_identifier(), 14);
}

// ---------------------------------------------------------------------
// Clause 7.3.
// ---------------------------------------------------------------------

/// A relying party that recognizes every form of `GeneralName`.
pub open spec fn all_name_forms() -> r::RelyingParty {
    r::RelyingParty { recognized_name_forms: seq![0nat, 1nat, 2nat, 3nat, 4nat, 5nat, 6nat, 7nat, 8nat] }
}

/// `tag_listed` of each of the nine.
pub proof fn lemma_all_forms_listed(tag: nat)
    requires
        tag <= 8,
    ensures
        r::tag_listed(all_name_forms().recognized_name_forms, 0, tag),
{
    let f = all_name_forms().recognized_name_forms;
    reveal_with_fuel(r::tag_listed, 10);
    assert(f[0] == 0nat);
    assert(f[1] == 1nat);
    assert(f[2] == 2nat);
    assert(f[3] == 3nat);
    assert(f[4] == 4nat);
    assert(f[5] == 5nat);
    assert(f[6] == 6nat);
    assert(f[7] == 7nat);
    assert(f[8] == 8nat);
}

/// A form that is not `Unknown` is recognized.
pub proof fn lemma_form_recognized(name: e::GeneralName)
    requires
        !(name is Unknown),
    ensures
        r::name_form_recognized(all_name_forms(), name),
{
    let tag = r::name_form_tag(name)->Some_0;
    assert(tag <= 8);
    lemma_all_forms_listed(tag);
}

/// `all_bases_recognized`, from the domain.
pub proof fn lemma_bases_recognized(t0: Seq<e::GeneralSubtree>, k: nat)
    requires
        subtrees_in_domain(t0),
    ensures
        r::all_bases_recognized(all_name_forms(), t0, k),
        r::subtrees_closed(t0, k),
    decreases t0.len() - k,
{
    if k < t0.len() {
        assert(subtree_in_domain(t0[k as int]));
        lemma_form_recognized(t0[k as int].base);
        lemma_bases_recognized(t0, k + 1);
    }
}

/// A subjectAltName is not an empty list.
pub proof fn lemma_san_not_empty(input: Seq<u8>, w: Seq<e::GeneralName>)
    requires
        san_value(input) == Some(w),
    ensures
        w.len() > 0,
{
    lemma_san_value(input);
    let t0 = i::parse_single(input)->Some_0;
    let l = s::sequence_elements(t0)->Some_0;
    lemma_general_name_list_len(l, 0);
}

/// One extension of the list, critical or not.
#[verifier::spinoff_prover]
pub proof fn lemma_extension_acceptable(a: x::Extension, y: e::Extension)
    requires
        extension_agree(a, y),
        extension_in_domain(y),
        value_in_domain(y),
        e::decode_extension_value(y.extn_id, y.extn_value) == Some(y.value),
        !a.critical || a.oid =~= lf::basic_constraints_oid() || a.oid =~= lf::key_usage_oid() || a.oid
            =~= lf::extended_key_usage_extension_oid() || a.oid =~= nc::name_constraints_oid() || a.oid
            =~= x::subject_alt_name_oid() || a.oid =~= pc::policy_constraints_oid(),
    ensures
        r::extension_acceptable(all_name_forms(), y),
{
    lemma_oids();
    if y.critical {
        assert(a.oid == y.extn_id);
        lemma_value_arms(y.extn_value, y.value);
        match y.value {
            e::ExtensionValue::SubjectAltName(w) => {
                assert(san_value(y.extn_value) == Some(w));
                lemma_san_not_empty(y.extn_value, w);
                assert(general_name_in_domain(w[0]));
                lemma_form_recognized(w[0]);
            },
            e::ExtensionValue::NameConstraints(w) => {
                if let Some(t0) = w.permitted_subtrees {
                    lemma_bases_recognized(t0, 0);
                }
                if let Some(t0) = w.excluded_subtrees {
                    lemma_bases_recognized(t0, 0);
                }
            },
            _ => {},
        }
    }
}

/// `extensions_acceptable` from `k`.
pub proof fn lemma_extensions_acceptable(a: Seq<x::Extension>, v: Seq<e::Extension>, k: nat)
    requires
        extensions_agree(a, v),
        values_read(v),
        values_in_domain(v),
        forall|m: int| 0 <= m < v.len() ==> extension_in_domain(#[trigger] v[m]),
        pt::intermediate_critical_supported(a, 0),
    ensures
        r::extensions_acceptable(all_name_forms(), v, k),
    decreases v.len() - k,
{
    if k < v.len() {
        let m = k as int;
        lemma_critical_at(a, 0, m);
        assert(extension_agree(a[m], v[m]));
        assert(extension_in_domain(v[m]));
        assert(value_in_domain(v[m]));
        lemma_extension_acceptable(a[m], v[m]);
        lemma_extensions_acceptable(a, v, k + 1);
    }
}

/// **7.3, `extensions_acceptable`.** With every name form recognized, as an
/// intermediate's or target's critical set allows it. `value_closed`,
/// `some_name_form_recognized`, `all_bases_recognized` and the rest of 7.3's
/// predicates are what this proves.
pub proof fn theorem_extensions_acceptable(p: ps::PathCert, v: Seq<e::Extension>)
    requires
        reading(p, v),
        pt::intermediate_critical_supported(p.extensions, 0),
    ensures
        r::extensions_acceptable(all_name_forms(), v, 0),
{
    lemma_extensions_acceptable(p.extensions, v, 0);
}

// ---------------------------------------------------------------------
// 7.4, 9.2.2.3, 9.3.2.1, 9.4.2.
// ---------------------------------------------------------------------

/// **7.4, `is_ca_certificate`**, is the crate's cA.
pub proof fn lemma_is_ca(p: ps::PathCert, y: s::Certificate)
    requires
        basic_found_agree(p.basic, r::extensions_of(y)),
    ensures
        r::is_ca_certificate(y) == match p.basic {
            Some(b) => b.ca,
            None => false,
        },
{
}

/// keyCertSign of the crate's keyUsage is bit 5 of the transcription's.
pub proof fn lemma_key_cert_sign_bit(a: cs::KeyUsage, w: i::BitString)
    requires
        key_usage_agree(a, w),
        w.unused <= 7,
    ensures
        cs::key_usage_has(a, cs::KeyUsageBit::KeyCertSign) == i::bit_is_set(w, 5),
{
    lemma_key_usage_has(a, w, cs::KeyUsageBit::KeyCertSign);
}

/// **9.2.2.3, `key_cert_sign_rule`, for a target.** `check_extensions`'
/// `basic_constraints_compatible` is that rule and one more: a
/// pathLenConstraint needs keyCertSign (RFC 5280 §4.2.1.9).
pub proof fn theorem_key_cert_sign_leaf(p: ps::PathCert, y: s::Certificate)
    requires
        basic_found_agree(p.basic, r::extensions_of(y)),
        key_usage_found_agree(p.key_usage, r::extensions_of(y)),
        match p.basic {
            Some(b) => b.path_len_constraint is Some ==> b.ca,
            None => true,
        },
    ensures
        cs::basic_constraints_compatible(p.basic, p.key_usage) == (r::key_cert_sign_rule(y) && match p.basic {
            Some(b) => b.path_len_constraint is None || match p.key_usage {
                Some(usage) => cs::key_usage_has(usage, cs::KeyUsageBit::KeyCertSign),
                None => false,
            },
            None => true,
        }),
{
    lemma_is_ca(p, y);
    let v = r::extensions_of(y);
    if let Some(u) = p.key_usage {
        let found = r::find_extension(v, 0, e::id_ce_key_usage())->Some_0;
        let w = found.value->KeyUsage_0;
        lemma_key_cert_sign_bit(u, w);
    }
}

/// **9.2.2.3, `key_cert_sign_rule`, for an intermediate.** §6.1.4 (k) has made it
/// a CA, which is all the rule asks.
pub proof fn theorem_key_cert_sign_ca(p: ps::PathCert, y: s::Certificate)
    requires
        basic_found_agree(p.basic, r::extensions_of(y)),
        p.basic is Some,
        p.basic->Some_0.ca,
    ensures
        r::key_cert_sign_rule(y),
{
    lemma_is_ca(p, y);
}

/// `ip_addresses_sized`, from the domain.
pub proof fn lemma_ip_sized(w: Seq<e::GeneralName>, k: nat)
    requires
        forall|m: int| 0 <= m < w.len() ==> general_name_in_domain(#[trigger] w[m]),
    ensures
        r::ip_addresses_sized(w, k),
    decreases w.len() - k,
{
    if k < w.len() {
        assert(general_name_in_domain(w[k as int]));
        lemma_ip_sized(w, k + 1);
    }
}

/// `find_extension` gives a member.
pub proof fn lemma_found_member(v: Seq<e::Extension>, k: nat, id: s::ObjectIdentifier)
    requires
        r::find_extension(v, k, id) is Some,
    ensures
        exists|m: int| k <= m < v.len() && v[m] == r::find_extension(v, k, id)->Some_0,
    decreases v.len() - k,
{
    if v[k as int].extn_id != id {
        lemma_found_member(v, k + 1, id);
    }
}

/// **9.3.2.1, `subject_alt_name_rules`.**
pub proof fn theorem_subject_alt_name_rules(p: ps::PathCert, y: s::Certificate)
    requires
        reading(p, r::extensions_of(y)),
    ensures
        r::subject_alt_name_rules(y),
{
    let v = r::extensions_of(y);
    let id = e::id_ce_subject_alt_name();
    if r::find_extension(v, 0, id) is Some {
        lemma_found_member(v, 0, id);
        let found = r::find_extension(v, 0, id)->Some_0;
        let m = choose|m: int| 0 <= m < v.len() && v[m] == found;
        assert(value_in_domain(v[m]));
        if let e::ExtensionValue::SubjectAltName(w) = found.value {
            lemma_ip_sized(w, 0);
        }
    }
}

/// **9.4.2.1, `basic_constraints_rules`.** pathLenConstraint only with cA is
/// the decoder's. What is left of the clause is that a cA is flagged critical,
/// **which production does not ask**.
pub proof fn theorem_basic_constraints_rules(p: ps::PathCert, y: s::Certificate)
    requires
        reading(p, r::extensions_of(y)),
    ensures
        r::basic_constraints_rules(y) == match r::find_extension(r::extensions_of(y), 0, e::id_ce_basic_constraints()) {
            None => true,
            Some(found) => match found.value {
                e::ExtensionValue::BasicConstraints(b) => !b.c_a || found.critical,
                _ => true,
            },
        },
{
    let v = r::extensions_of(y);
    let id = e::id_ce_basic_constraints();
    if r::find_extension(v, 0, id) is Some {
        lemma_found_member(v, 0, id);
        let found = r::find_extension(v, 0, id)->Some_0;
        let m = choose|m: int| 0 <= m < v.len() && v[m] == found;
        assert(value_in_domain(v[m]));
    }
}

/// **9.4.2, `ca_only_extensions`.** A CA keeps it. On a target, `leaf_profile`
/// has refused nameConstraints, so what is left of the clause is that it has
/// no policyConstraints, **which production does not ask**.
pub proof fn theorem_ca_only(p: ps::PathCert, y: s::Certificate)
    requires
        path_values_agree(p, r::extensions_of(y)),
        p.name_constraints is None,
    ensures
        r::ca_only_extensions(y) == (r::is_ca_certificate(y) || r::absent_from(
            r::extensions_of(y),
            0,
            e::id_ce_policy_constraints(),
        )),
{
}

// ---------------------------------------------------------------------
// dNSName.
// ---------------------------------------------------------------------

/// `is_ldh` is `valid_name_from`'s alphabet.
pub proof fn lemma_ldh(b: u8)
    ensures
        r::is_ldh(b) == (b >= 0x61 && b <= 0x7A || b >= 0x41 && b <= 0x5A || b >= 0x30 && b <= 0x39 || b == 0x2D),
{
}

/// What `dns_label_run` accepts is shaped.
pub proof fn lemma_syntax_is_shape(n: Seq<u8>, k: nat, run: nat)
    requires
        k < n.len(),
        r::dns_label_run(n, k, run),
        run > 0 ==> k > 0,
    ensures
        h::valid_name_from(n, k as int),
    decreases n.len() - k,
{
    lemma_ldh(n[k as int]);
    if n[k as int] == 0x2E {
        assert(k + 1 < n.len());
        lemma_syntax_is_shape(n, k + 1, 0);
    } else if k + 1 < n.len() {
        lemma_syntax_is_shape(n, k + 1, run + 1);
    }
}

/// No label of `n` from `k` is longer than 63 octets, `run` of the current one
/// already read.
pub open spec fn labels_short(n: Seq<u8>, k: nat, run: nat) -> bool
    decreases n.len() - k,
{
    if k >= n.len() {
        true
    } else if n[k as int] == 0x2E {
        labels_short(n, k + 1, 0)
    } else {
        run < 63 && labels_short(n, k + 1, run + 1)
    }
}

/// What the crate's shape accepts, with short labels, `dns_label_run` accepts.
pub proof fn lemma_shape_is_syntax(n: Seq<u8>, k: nat, run: nat)
    requires
        k < n.len(),
        h::valid_name_from(n, k as int),
        labels_short(n, k, run),
        n[k as int] == 0x2E ==> run > 0,
    ensures
        r::dns_label_run(n, k, run),
    decreases n.len() - k,
{
    lemma_ldh(n[k as int]);
    if n[k as int] == 0x2E {
        lemma_shape_is_syntax(n, k + 1, 0);
    } else if k + 1 < n.len() {
        lemma_shape_is_syntax(n, k + 1, run + 1);
    } else {
        assert(r::dns_label_run(n, k + 1, run + 1));
    }
}

/// **9.3.2.1, `dns_name_syntax`.** It is the crate's shape with 9.3.2.1 a)'s
/// label length, which `spec.rs` does not have: a longer label is compared, and
/// matches only a reference with the same long label, which DNS cannot hold.
pub proof fn theorem_dns_name_syntax(n: Seq<u8>)
    ensures
        r::dns_name_syntax(n) == (h::dns_name_shape(n) && labels_short(n, 0, 0)),
{
    if r::dns_name_syntax(n) {
        assert(n.len() > 0);
        lemma_syntax_is_shape(n, 0, 0);
        lemma_syntax_short(n, 0, 0);
    }
    if h::dns_name_shape(n) && labels_short(n, 0, 0) {
        assert(n[0] != 0x2E);
        lemma_shape_is_syntax(n, 0, 0);
    }
}

/// `dns_label_run` keeps its labels short.
pub proof fn lemma_syntax_short(n: Seq<u8>, k: nat, run: nat)
    requires
        r::dns_label_run(n, k, run),
    ensures
        labels_short(n, k, run),
    decreases n.len() - k,
{
    if k < n.len() {
        if n[k as int] == 0x2E {
            lemma_syntax_short(n, k + 1, 0);
        } else {
            lemma_syntax_short(n, k + 1, run + 1);
        }
    }
}

} // verus!
