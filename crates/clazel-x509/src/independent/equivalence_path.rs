//! **What `parse_path_cert` runs**, against the transcription, whole.
//! `equivalence_frame.rs` covers its outer decoders, and this file adds the
//! extensions it looks up: `leaf/spec.rs`'s `find_extension_index` and
//! `optional_*`, the six value decoders and `prepare_signature`.
//!
//! - [`theorem_path_cert_fwd`]: every certificate `parse_path_cert` keeps, the
//!   transcription reads to the same values, up to the frame's three unread
//!   components, inside [`path_conditions`].
//! - [`theorem_path_cert_back`]: every certificate the transcription reads,
//!   inside `certificate_in_domain` and [`value_in_domain`] and with a
//!   signature `prepare_signature` takes, `parse_path_cert` reads to the same
//!   values.
//!
//! **What this narrows.** `equivalence.rs`'s condition 3 asks that all ten
//! known extension values decode. On the production path six of them are read,
//! so [`path_conditions`] asks it only of what `parse_path_cert` does not read:
//! the values of authorityKeyIdentifier, subjectKeyIdentifier,
//! certificatePolicies and inhibitAnyPolicy, the forms a subjectAltName or a
//! nameConstraints keeps as octets, and the empty nameConstraints.
//!
//! **What stays unread, on every certificate.** A malformed Name, key or one
//! of those four values passes `parse_path_cert`. The transcription refuses the
//! certificate; production goes on. That is the crate's design, not a
//! disagreement to remove: `path/parsed/spec.rs` says so for the key, and the
//! Names are compared as octets. So there is no theorem that they agree there,
//! and the frame's [`CertificateFrame`] says exactly which components are left.

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
use super::equivalence_signature::*;
#[cfg(verus_only)]
use super::equivalence_structures::*;
#[cfg(verus_only)]
use super::equivalence_tbs::*;
#[cfg(verus_only)]
use super::equivalence_time::*;
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
use crate::policy_constraints::spec as pc;
#[cfg(verus_only)]
use crate::signature_algorithm::spec as g;
#[cfg(verus_only)]
use crate::tbs::spec as t;
#[cfg(verus_only)]
use clazel_der::spec as d;

verus! {

// ---------------------------------------------------------------------
// One name for each extension.
// ---------------------------------------------------------------------

/// The crate's object identifiers are the transcription's.
pub proof fn lemma_oids()
    ensures
        lf::basic_constraints_oid() == e::id_ce_basic_constraints(),
        lf::key_usage_oid() == e::id_ce_key_usage(),
        lf::extended_key_usage_extension_oid() == e::id_ce_ext_key_usage(),
        nc::name_constraints_oid() == e::id_ce_name_constraints(),
        x::subject_alt_name_oid() == e::id_ce_subject_alt_name(),
        pc::policy_constraints_oid() == e::id_ce_policy_constraints(),
        ps::inhibit_any_policy_oid() == e::id_ce_inhibit_any_policy(),
        ps::policy_mappings_oid() == e::id_ce(33),
{
    assert(lf::basic_constraints_oid() =~= e::id_ce_basic_constraints());
    assert(lf::key_usage_oid() =~= e::id_ce_key_usage());
    assert(lf::extended_key_usage_extension_oid() =~= e::id_ce_ext_key_usage());
    assert(nc::name_constraints_oid() =~= e::id_ce_name_constraints());
    assert(x::subject_alt_name_oid() =~= e::id_ce_subject_alt_name());
    assert(pc::policy_constraints_oid() =~= e::id_ce_policy_constraints());
    assert(ps::inhibit_any_policy_oid() =~= e::id_ce_inhibit_any_policy());
    assert(ps::policy_mappings_oid() =~= e::id_ce(33));
}

/// The arm of `decode_extension_value` for each id gives that id's value.
pub proof fn lemma_value_arms(input: Seq<u8>, val: e::ExtensionValue)
    ensures
        e::decode_extension_value(e::id_ce_basic_constraints(), input) == Some(val) ==> val is BasicConstraints,
        e::decode_extension_value(e::id_ce_key_usage(), input) == Some(val) ==> val is KeyUsage,
        e::decode_extension_value(e::id_ce_ext_key_usage(), input) == Some(val) ==> val is ExtKeyUsage,
        e::decode_extension_value(e::id_ce_name_constraints(), input) == Some(val) ==> val is NameConstraints,
        e::decode_extension_value(e::id_ce_subject_alt_name(), input) == Some(val) ==> val is SubjectAltName,
        e::decode_extension_value(e::id_ce_policy_constraints(), input) == Some(val) ==> val is PolicyConstraints,
{
    lemma_id_ce_differ(15, 35);
    lemma_id_ce_differ(15, 14);
    lemma_id_ce_differ(37, 35);
    lemma_id_ce_differ(37, 14);
    lemma_id_ce_differ(37, 15);
    lemma_id_ce_differ(17, 35);
    lemma_id_ce_differ(17, 14);
    lemma_id_ce_differ(17, 15);
    lemma_id_ce_differ(17, 37);
    lemma_id_ce_differ(17, 32);
    lemma_id_ce_differ(19, 35);
    lemma_id_ce_differ(19, 14);
    lemma_id_ce_differ(19, 15);
    lemma_id_ce_differ(19, 37);
    lemma_id_ce_differ(19, 32);
    lemma_id_ce_differ(19, 17);
    lemma_id_ce_differ(30, 35);
    lemma_id_ce_differ(30, 14);
    lemma_id_ce_differ(30, 15);
    lemma_id_ce_differ(30, 37);
    lemma_id_ce_differ(30, 32);
    lemma_id_ce_differ(30, 17);
    lemma_id_ce_differ(30, 19);
    lemma_id_ce_differ(36, 35);
    lemma_id_ce_differ(36, 14);
    lemma_id_ce_differ(36, 15);
    lemma_id_ce_differ(36, 37);
    lemma_id_ce_differ(36, 32);
    lemma_id_ce_differ(36, 17);
    lemma_id_ce_differ(36, 19);
    lemma_id_ce_differ(36, 30);
}

// ---------------------------------------------------------------------
// Looking an extension up, on both sides.
// ---------------------------------------------------------------------

/// `value` of every extension is what `decode_extension_value` read.
pub open spec fn values_read(v: Seq<e::Extension>) -> bool {
    forall|k: int|
        0 <= k < v.len() ==> e::decode_extension_value((#[trigger] v[k]).extn_id, v[k].extn_value) == Some(
            v[k].value,
        )
}

/// A list `decode_extension_list` gives is one of those.
pub proof fn lemma_list_values(l: Seq<i::Tlv>, k: nat)
    requires
        e::decode_extension_list(l, k) is Some,
    ensures
        values_read(e::decode_extension_list(l, k)->Some_0),
    decreases l.len() - k,
{
    if k < l.len() {
        lemma_list_values(l, k + 1);
        let first = e::decode_extension(l[k as int])->Some_0;
        let rest = e::decode_extension_list(l, k + 1)->Some_0;
        let v = seq![first] + rest;
        assert(e::decode_extension_list(l, k)->Some_0 == v);
        assert forall|m: int| 0 <= m < v.len() implies e::decode_extension_value(
            (#[trigger] v[m]).extn_id,
            v[m].extn_value,
        ) == Some(v[m].value) by {
            if m > 0 {
                assert(v[m] == rest[m - 1]);
            }
        }
    }
}

/// The extensions of a decoded component are read.
pub proof fn lemma_component_values(l: Seq<i::Tlv>, m: nat)
    requires
        s::extensions_component(l, m) is Some,
        s::extensions_component(l, m)->Some_0 is Some,
    ensures
        values_read(s::extensions_component(l, m)->Some_0->Some_0),
{
    let u = l[m as int];
    let inner = i::parse_single(u.contents)->Some_0;
    let e0 = s::sequence_elements(inner)->Some_0;
    lemma_list_values(e0, 0);
}

/// The extensions of a tail are read.
pub proof fn lemma_tail_values(l: Seq<i::Tlv>)
    requires
        tail_of(l) is Some,
        tail_of(l)->Some_0.2 is Some,
    ensures
        values_read(tail_of(l)->Some_0.2->Some_0),
{
    let m = s::step(s::unique_identifier_component(l, 0, 1)->Some_0);
    let p = m + s::step(s::unique_identifier_component(l, m, 2)->Some_0);
    lemma_component_values(l, p);
}

/// The extensions of a list, none being the empty list.
pub open spec fn listed(o: Option<Seq<e::Extension>>) -> Seq<e::Extension> {
    match o {
        None => Seq::<e::Extension>::empty(),
        Some(v) => v,
    }
}

/// `find_extension_index` on the crate's list is `find_extension` on the
/// transcription's.
pub proof fn lemma_find(a: Seq<x::Extension>, v: Seq<e::Extension>, oid: Seq<nat>, k: int)
    requires
        extensions_agree(a, v),
        0 <= k <= a.len(),
    ensures
        match lf::find_extension_index(a, oid, k) {
            None => r::find_extension(v, k as nat, oid) is None,
            Some(idx) => {
                &&& k <= idx < a.len()
                &&& r::find_extension(v, k as nat, oid) == Some(v[idx])
                &&& a[idx].oid == oid
                &&& v[idx].extn_id == oid
            },
        },
    decreases a.len() - k,
{
    if k < a.len() {
        assert(extension_agree(a[k], v[k]));
        if a[k].oid =~= oid {
            assert(a[k].oid == oid);
        } else {
            assert(a[k].oid != oid);
            lemma_find(a, v, oid, k + 1);
        }
    }
}

/// What a lookup needs: the two lists agree, and each value is short enough
/// to be an input.
pub open spec fn lookup_ready(a: Seq<x::Extension>, v: Seq<e::Extension>) -> bool {
    &&& extensions_agree(a, v)
    &&& values_read(v)
    &&& forall|k: int| 0 <= k < a.len() ==> (#[trigger] a[k]).value.len() < two64()
}

/// The found value of each extension, and the crate's, agree.
pub open spec fn basic_found_agree(o: Option<cs::BasicConstraints>, v: Seq<e::Extension>) -> bool {
    match (o, r::find_extension(v, 0, e::id_ce_basic_constraints())) {
        (None, None) => true,
        (Some(p), Some(y)) => match y.value {
            e::ExtensionValue::BasicConstraints(w) => basic_agree(p, w),
            _ => false,
        },
        _ => false,
    }
}

/// keyUsage.
pub open spec fn key_usage_found_agree(o: Option<cs::KeyUsage>, v: Seq<e::Extension>) -> bool {
    match (o, r::find_extension(v, 0, e::id_ce_key_usage())) {
        (None, None) => true,
        (Some(p), Some(y)) => match y.value {
            e::ExtensionValue::KeyUsage(w) => key_usage_agree(p, w) && w.unused <= 7,
            _ => false,
        },
        _ => false,
    }
}

/// extKeyUsage.
pub open spec fn eku_found_agree(o: Option<cs::ExtendedKeyUsage>, v: Seq<e::Extension>) -> bool {
    match (o, r::find_extension(v, 0, e::id_ce_ext_key_usage())) {
        (None, None) => true,
        (Some(p), Some(y)) => match y.value {
            e::ExtensionValue::ExtKeyUsage(w) => p.purposes == w,
            _ => false,
        },
        _ => false,
    }
}

/// nameConstraints.
pub open spec fn name_constraints_found_agree(o: Option<nc::NameConstraints>, v: Seq<e::Extension>) -> bool {
    match (o, r::find_extension(v, 0, e::id_ce_name_constraints())) {
        (None, None) => true,
        (Some(p), Some(y)) => match y.value {
            e::ExtensionValue::NameConstraints(w) => name_constraints_agree(p, w),
            _ => false,
        },
        _ => false,
    }
}

/// subjectAltName.
pub open spec fn san_found_agree(o: Option<x::SubjectAltName>, v: Seq<e::Extension>) -> bool {
    match (o, r::find_extension(v, 0, e::id_ce_subject_alt_name())) {
        (None, None) => true,
        (Some(p), Some(y)) => match y.value {
            e::ExtensionValue::SubjectAltName(w) => subject_alt_name_agree(p, w),
            _ => false,
        },
        _ => false,
    }
}

/// policyConstraints.
pub open spec fn policy_found_agree(o: Option<pc::PolicyConstraints>, v: Seq<e::Extension>) -> bool {
    match (o, r::find_extension(v, 0, e::id_ce_policy_constraints())) {
        (None, None) => true,
        (Some(p), Some(y)) => match y.value {
            e::ExtensionValue::PolicyConstraints(w) => policy_constraints_agree(p, w),
            _ => false,
        },
        _ => false,
    }
}

/// A value of the crate's six read extensions that it reads.
pub open spec fn value_in_domain(y: e::Extension) -> bool {
    match y.value {
        e::ExtensionValue::BasicConstraints(w) => basic_in_domain(w),
        e::ExtensionValue::KeyUsage(w) => key_usage_in_domain(w),
        e::ExtensionValue::ExtKeyUsage(w) => eku_in_domain(w),
        e::ExtensionValue::NameConstraints(w) => name_constraints_in_domain(w),
        e::ExtensionValue::SubjectAltName(w) => forall|k: int|
            0 <= k < w.len() ==> general_name_in_domain(#[trigger] w[k]),
        e::ExtensionValue::PolicyConstraints(w) => policy_constraints_in_domain(w),
        _ => true,
    }
}

/// Every value of the list is one the crate reads.
pub open spec fn values_in_domain(v: Seq<e::Extension>) -> bool {
    forall|k: int| 0 <= k < v.len() ==> value_in_domain(#[trigger] v[k])
}

/// `bit_string_contents` keeps `unused` at seven or less.
pub proof fn lemma_key_usage_unused(input: Seq<u8>, w: i::BitString)
    requires
        key_usage_value(input) == Some(w),
    ensures
        w.unused <= 7,
{
    lemma_key_usage_value(input);
}

/// **`leaf/spec.rs`'s `optional_basic_constraints`, from the crate.**
pub proof fn lemma_found_basic(a: Seq<x::Extension>, v: Seq<e::Extension>, o: Option<cs::BasicConstraints>)
    requires
        lookup_ready(a, v),
        lf::optional_basic_constraints(a) == Some(o),
    ensures
        basic_found_agree(o, v),
{
    hide(e::decode_extension_value);
    lemma_oids();
    let oid = lf::basic_constraints_oid();
    lemma_find(a, v, oid, 0);
    if let Some(idx) = lf::find_extension_index(a, oid, 0) {
        let y = v[idx];
        assert(extension_agree(a[idx], y));
        theorem_basic_constraints_fwd(y.extn_value);
        assert(e::decode_extension_value(y.extn_id, y.extn_value) == Some(y.value));
        lemma_value_arms(y.extn_value, y.value);
    }
}

/// **`leaf/spec.rs`'s `optional_basic_constraints`, from the transcription.**
pub proof fn lemma_lookup_basic(a: Seq<x::Extension>, v: Seq<e::Extension>)
    requires
        lookup_ready(a, v),
        values_in_domain(v),
    ensures
        lf::optional_basic_constraints(a) is Some,
        basic_found_agree(lf::optional_basic_constraints(a)->Some_0, v),
{
    hide(e::decode_extension_value);
    lemma_oids();
    let oid = lf::basic_constraints_oid();
    lemma_find(a, v, oid, 0);
    if let Some(idx) = lf::find_extension_index(a, oid, 0) {
        let y = v[idx];
        assert(extension_agree(a[idx], y));
        assert(e::decode_extension_value(y.extn_id, y.extn_value) == Some(y.value));
        lemma_value_arms(y.extn_value, y.value);
        assert(value_in_domain(y));
        theorem_basic_constraints_back(y.extn_value, y.value->BasicConstraints_0);
    }
}

/// `optional_key_usage`, from the crate.
pub proof fn lemma_found_key_usage(a: Seq<x::Extension>, v: Seq<e::Extension>, o: Option<cs::KeyUsage>)
    requires
        lookup_ready(a, v),
        lf::optional_key_usage(a) == Some(o),
    ensures
        key_usage_found_agree(o, v),
{
    hide(e::decode_extension_value);
    lemma_oids();
    let oid = lf::key_usage_oid();
    lemma_find(a, v, oid, 0);
    if let Some(idx) = lf::find_extension_index(a, oid, 0) {
        let y = v[idx];
        assert(extension_agree(a[idx], y));
        theorem_key_usage_fwd(y.extn_value);
        assert(e::decode_extension_value(y.extn_id, y.extn_value) == Some(y.value));
        lemma_value_arms(y.extn_value, y.value);
        lemma_key_usage_unused(y.extn_value, y.value->KeyUsage_0);
    }
}

/// `optional_key_usage`, from the transcription.
pub proof fn lemma_lookup_key_usage(a: Seq<x::Extension>, v: Seq<e::Extension>)
    requires
        lookup_ready(a, v),
        values_in_domain(v),
    ensures
        lf::optional_key_usage(a) is Some,
        key_usage_found_agree(lf::optional_key_usage(a)->Some_0, v),
{
    hide(e::decode_extension_value);
    lemma_oids();
    let oid = lf::key_usage_oid();
    lemma_find(a, v, oid, 0);
    if let Some(idx) = lf::find_extension_index(a, oid, 0) {
        let y = v[idx];
        assert(extension_agree(a[idx], y));
        assert(e::decode_extension_value(y.extn_id, y.extn_value) == Some(y.value));
        lemma_value_arms(y.extn_value, y.value);
        assert(value_in_domain(y));
        theorem_key_usage_back(y.extn_value, y.value->KeyUsage_0);
        lemma_key_usage_unused(y.extn_value, y.value->KeyUsage_0);
    }
}

/// `optional_extended_key_usage`, from the crate.
pub proof fn lemma_found_eku(a: Seq<x::Extension>, v: Seq<e::Extension>, o: Option<cs::ExtendedKeyUsage>)
    requires
        lookup_ready(a, v),
        lf::optional_extended_key_usage(a) == Some(o),
    ensures
        eku_found_agree(o, v),
{
    hide(e::decode_extension_value);
    lemma_oids();
    let oid = lf::extended_key_usage_extension_oid();
    lemma_find(a, v, oid, 0);
    if let Some(idx) = lf::find_extension_index(a, oid, 0) {
        let y = v[idx];
        assert(extension_agree(a[idx], y));
        theorem_ext_key_usage_fwd(y.extn_value);
        assert(e::decode_extension_value(y.extn_id, y.extn_value) == Some(y.value));
        lemma_value_arms(y.extn_value, y.value);
    }
}

/// `optional_extended_key_usage`, from the transcription.
pub proof fn lemma_lookup_eku(a: Seq<x::Extension>, v: Seq<e::Extension>)
    requires
        lookup_ready(a, v),
        values_in_domain(v),
    ensures
        lf::optional_extended_key_usage(a) is Some,
        eku_found_agree(lf::optional_extended_key_usage(a)->Some_0, v),
{
    hide(e::decode_extension_value);
    lemma_oids();
    let oid = lf::extended_key_usage_extension_oid();
    lemma_find(a, v, oid, 0);
    if let Some(idx) = lf::find_extension_index(a, oid, 0) {
        let y = v[idx];
        assert(extension_agree(a[idx], y));
        assert(e::decode_extension_value(y.extn_id, y.extn_value) == Some(y.value));
        lemma_value_arms(y.extn_value, y.value);
        assert(value_in_domain(y));
        theorem_ext_key_usage_back(y.extn_value, y.value->ExtKeyUsage_0);
    }
}

/// `optional_name_constraints`, from the crate.
pub proof fn lemma_found_name_constraints(a: Seq<x::Extension>, v: Seq<e::Extension>, o: Option<nc::NameConstraints>)
    requires
        lookup_ready(a, v),
        ps::optional_name_constraints(a) == Some(o),
        match o {
            Some(p) => name_constraints_decodes(p),
            None => true,
        },
    ensures
        name_constraints_found_agree(o, v),
{
    hide(e::decode_extension_value);
    hide(name_constraints_decodes);
    lemma_oids();
    let oid = nc::name_constraints_oid();
    lemma_find(a, v, oid, 0);
    if let Some(idx) = lf::find_extension_index(a, oid, 0) {
        let y = v[idx];
        assert(extension_agree(a[idx], y));
        theorem_name_constraints_fwd(y.extn_value);
        assert(e::decode_extension_value(y.extn_id, y.extn_value) == Some(y.value));
        lemma_value_arms(y.extn_value, y.value);
    }
}

/// `optional_name_constraints`, from the transcription.
pub proof fn lemma_lookup_name_constraints(a: Seq<x::Extension>, v: Seq<e::Extension>)
    requires
        lookup_ready(a, v),
        values_in_domain(v),
    ensures
        ps::optional_name_constraints(a) is Some,
        name_constraints_found_agree(ps::optional_name_constraints(a)->Some_0, v),
{
    hide(e::decode_extension_value);
    lemma_oids();
    let oid = nc::name_constraints_oid();
    lemma_find(a, v, oid, 0);
    if let Some(idx) = lf::find_extension_index(a, oid, 0) {
        let y = v[idx];
        assert(extension_agree(a[idx], y));
        assert(e::decode_extension_value(y.extn_id, y.extn_value) == Some(y.value));
        lemma_value_arms(y.extn_value, y.value);
        assert(value_in_domain(y));
        theorem_name_constraints_back(y.extn_value, y.value->NameConstraints_0);
    }
}

/// Each name of a value is one `extensions.rs` reads.
pub open spec fn san_forms_decode(p: x::SubjectAltName) -> bool {
    forall|k: int| 0 <= k < p.names.len() ==> other_form_decodes(#[trigger] p.names[k])
}

/// `optional_subject_alt_name`, from the crate.
pub proof fn lemma_found_san(a: Seq<x::Extension>, v: Seq<e::Extension>, o: Option<x::SubjectAltName>)
    requires
        lookup_ready(a, v),
        ps::optional_subject_alt_name(a) == Some(o),
        match o {
            Some(p) => san_forms_decode(p),
            None => true,
        },
    ensures
        san_found_agree(o, v),
{
    hide(e::decode_extension_value);
    lemma_oids();
    let oid = x::subject_alt_name_oid();
    lemma_find(a, v, oid, 0);
    if let Some(idx) = lf::find_extension_index(a, oid, 0) {
        let y = v[idx];
        assert(extension_agree(a[idx], y));
        theorem_subject_alt_name_fwd(y.extn_value);
        assert(e::decode_extension_value(y.extn_id, y.extn_value) == Some(y.value));
        lemma_value_arms(y.extn_value, y.value);
    }
}

/// `optional_subject_alt_name`, from the transcription.
pub proof fn lemma_lookup_san(a: Seq<x::Extension>, v: Seq<e::Extension>)
    requires
        lookup_ready(a, v),
        values_in_domain(v),
    ensures
        ps::optional_subject_alt_name(a) is Some,
        san_found_agree(ps::optional_subject_alt_name(a)->Some_0, v),
{
    hide(e::decode_extension_value);
    lemma_oids();
    let oid = x::subject_alt_name_oid();
    lemma_find(a, v, oid, 0);
    if let Some(idx) = lf::find_extension_index(a, oid, 0) {
        let y = v[idx];
        assert(extension_agree(a[idx], y));
        assert(e::decode_extension_value(y.extn_id, y.extn_value) == Some(y.value));
        lemma_value_arms(y.extn_value, y.value);
        assert(value_in_domain(y));
        theorem_subject_alt_name_back(y.extn_value, y.value->SubjectAltName_0);
    }
}

/// `optional_policy_constraints`, from the crate.
pub proof fn lemma_found_policy(a: Seq<x::Extension>, v: Seq<e::Extension>, o: Option<pc::PolicyConstraints>)
    requires
        lookup_ready(a, v),
        ps::optional_policy_constraints(a) == Some(o),
    ensures
        policy_found_agree(o, v),
{
    hide(e::decode_extension_value);
    lemma_oids();
    let oid = pc::policy_constraints_oid();
    lemma_find(a, v, oid, 0);
    if let Some(idx) = lf::find_extension_index(a, oid, 0) {
        let y = v[idx];
        assert(extension_agree(a[idx], y));
        theorem_policy_constraints_fwd(y.extn_value);
        assert(e::decode_extension_value(y.extn_id, y.extn_value) == Some(y.value));
        lemma_value_arms(y.extn_value, y.value);
    }
}

/// `optional_policy_constraints`, from the transcription.
pub proof fn lemma_lookup_policy(a: Seq<x::Extension>, v: Seq<e::Extension>)
    requires
        lookup_ready(a, v),
        values_in_domain(v),
    ensures
        ps::optional_policy_constraints(a) is Some,
        policy_found_agree(ps::optional_policy_constraints(a)->Some_0, v),
{
    hide(e::decode_extension_value);
    lemma_oids();
    let oid = pc::policy_constraints_oid();
    lemma_find(a, v, oid, 0);
    if let Some(idx) = lf::find_extension_index(a, oid, 0) {
        let y = v[idx];
        assert(extension_agree(a[idx], y));
        assert(e::decode_extension_value(y.extn_id, y.extn_value) == Some(y.value));
        lemma_value_arms(y.extn_value, y.value);
        assert(value_in_domain(y));
        theorem_policy_constraints_back(y.extn_value, y.value->PolicyConstraints_0);
    }
}

// ---------------------------------------------------------------------
// The lengths and the identifiers of a list the crate read.
// ---------------------------------------------------------------------

/// Every extension `parse_extensions_acc` adds has a value inside `b`.
pub proof fn lemma_acc_value_lengths(
    b: Seq<u8>,
    pos: nat,
    end: nat,
    seen: Seq<Seq<nat>>,
    acc: Seq<x::Extension>,
)
    requires
        wf(b, pos, end),
        x::parse_extensions_acc(b, pos, end, seen, acc) is Some,
        forall|k: int| 0 <= k < acc.len() ==> (#[trigger] acc[k]).value.len() <= b.len(),
    ensures
        ({
            let all = x::parse_extensions_acc(b, pos, end, seen, acc)->Some_0.0;
            forall|k: int| 0 <= k < all.len() ==> (#[trigger] all[k]).value.len() <= b.len()
        }),
    decreases end - pos,
{
    if pos < end {
        let (a, next) = x::parse_extension(b, pos, end)->Some_0;
        let outer = d::read_tlv(b, pos, end)->Some_0;
        clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
        let (start, finish) = (outer.cstart, outer.cend);
        let (oid, after_oid) = d::read_oid(b, start, finish)->Some_0;
        let field = d::read_tlv(b, after_oid, finish)->Some_0;
        clazel_der::lemmas::lemma_read_tlv_bounds(b, start, finish);
        clazel_der::lemmas::lemma_read_tlv_bounds(b, after_oid, finish);
        if field.tag == d::universal_primitive(d::BOOLEAN) {
            let (val, after) = d::read_boolean(b, after_oid, finish)->Some_0;
            clazel_der::lemmas::lemma_read_tlv_bounds(b, after, finish);
        }
        let acc2 = acc.push(a);
        assert forall|k: int| 0 <= k < acc2.len() implies (#[trigger] acc2[k]).value.len() <= b.len() by {
            if k < acc.len() {
                assert(acc2[k] == acc[k]);
            }
        }
        assert(x::parse_extensions_acc(b, next, end, seen.push(a.oid), acc2) == x::parse_extensions_acc(b, pos, end, seen, acc));
        lemma_acc_value_lengths(b, next, end, seen.push(a.oid), acc2);
    }
}

/// `oid_seen` of a member.
pub proof fn lemma_oid_seen_member(seen: Seq<Seq<nat>>, oid: Seq<nat>, k: int, m: int)
    requires
        0 <= k <= m < seen.len(),
        seen[m] == oid,
    ensures
        x::oid_seen(seen, oid, k),
    decreases m - k,
{
    if k < m {
        lemma_oid_seen_member(seen, oid, k + 1, m);
    } else {
        assert(seen[k] =~= oid);
    }
}

/// No two extensions `parse_extensions_acc` builds have one identifier.
pub proof fn lemma_acc_distinct(b: Seq<u8>, pos: nat, end: nat, seen: Seq<Seq<nat>>, acc: Seq<x::Extension>)
    requires
        pos <= end,
        x::parse_extensions_acc(b, pos, end, seen, acc) is Some,
        seen.len() == acc.len(),
        forall|k: int| 0 <= k < acc.len() ==> #[trigger] seen[k] == acc[k].oid,
        forall|j: int, k: int| 0 <= j < k < acc.len() ==> #[trigger] acc[j].oid != #[trigger] acc[k].oid,
    ensures
        ({
            let all = x::parse_extensions_acc(b, pos, end, seen, acc)->Some_0.0;
            forall|j: int, k: int| 0 <= j < k < all.len() ==> #[trigger] all[j].oid != #[trigger] all[k].oid
        }),
    decreases end - pos,
{
    hide(x::parse_extension);
    if pos < end {
        let (a, next) = x::parse_extension(b, pos, end)->Some_0;
        let acc2 = acc.push(a);
        let seen2 = seen.push(a.oid);
        assert forall|k: int| 0 <= k < acc2.len() implies #[trigger] seen2[k] == acc2[k].oid by {
            if k < acc.len() {
                assert(seen2[k] == seen[k]);
                assert(acc2[k] == acc[k]);
            }
        }
        assert forall|j: int, k: int| 0 <= j < k < acc2.len() implies #[trigger] acc2[j].oid != #[trigger] acc2[k].oid by {
            assert(acc2[j] == acc[j]);
            if k == acc.len() {
                assert(acc2[k] == a);
                if acc[j].oid == a.oid {
                    assert(seen[j] == a.oid);
                    lemma_oid_seen_member(seen, a.oid, 0, j);
                }
            } else {
                assert(acc2[k] == acc[k]);
            }
        }
        assert(x::parse_extensions_acc(b, next, end, seen2, acc2) == x::parse_extensions_acc(b, pos, end, seen, acc));
        lemma_acc_distinct(b, next, end, seen2, acc2);
    }
}

/// A list `parse_extensions` read: each value shorter than the input, each
/// identifier once.
pub proof fn lemma_extensions_shape(input: Seq<u8>, all: Seq<x::Extension>)
    requires
        x::parse_extensions(input) == Some(all),
    ensures
        forall|k: int| 0 <= k < all.len() ==> (#[trigger] all[k]).value.len() <= input.len(),
        forall|j: int, k: int| 0 <= j < k < all.len() ==> #[trigger] all[j].oid != #[trigger] all[k].oid,
{
    let b = input;
    let len = b.len();
    let t0 = d::read_tlv(b, 0, len)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, 0, len);
    let (start, finish) = (t0.cstart, t0.cend);
    let none = Seq::<Seq<nat>>::empty();
    let empty = Seq::<x::Extension>::empty();
    assert(x::parse_extensions_from(b, start, finish, none) == x::parse_extensions_acc(b, start, finish, none, empty));
    lemma_acc_value_lengths(b, start, finish, none, empty);
    lemma_acc_distinct(b, start, finish, none, empty);
}

/// `find_extension_index` finds the one extension with an identifier.
pub proof fn lemma_found_at(a: Seq<x::Extension>, oid: Seq<nat>, k: int, idx: int)
    requires
        0 <= k <= idx < a.len(),
        a[idx].oid == oid,
        forall|p: int, q: int| 0 <= p < q < a.len() ==> #[trigger] a[p].oid != #[trigger] a[q].oid,
    ensures
        lf::find_extension_index(a, oid, k) == Some(idx),
    decreases idx - k,
{
    if k < idx {
        assert(a[k].oid != a[idx].oid);
        assert(!(a[k].oid =~= oid));
        lemma_found_at(a, oid, k + 1, idx);
    } else {
        assert(a[k].oid =~= oid);
    }
}

/// `optional_extensions`' sequence is inside the range.
pub proof fn lemma_tail_sequence(b: Seq<u8>, pos: nat, end: nat, version: nat)
    requires
        wf(b, pos, end),
        t::parse_optional_tail(b, pos, end, version) is Some,
    ensures
        match t::parse_optional_tail(b, pos, end, version)->Some_0.extensions_sequence_der {
            Some(v) => v.len() <= b.len(),
            None => true,
        },
{
    let (issuer, p1) = t::optional_unique(b, pos, end, 1, version)->Some_0;
    let (subject, p2) = t::optional_unique(b, p1, end, 2, version)->Some_0;
    if p2 != end {
        let w = d::read_tlv(b, p2, end)->Some_0;
        clazel_der::lemmas::lemma_read_tlv_bounds(b, p2, end);
    }
}

/// The inner sequence of `[3]` is no longer than the TBSCertificate.
pub proof fn lemma_sequence_length(input: Seq<u8>, tb: t::TbsCertificate)
    requires
        t::parse_tbs_certificate(input) == Some(tb),
    ensures
        match tb.extensions_sequence_der {
            Some(v) => v.len() <= input.len(),
            None => true,
        },
{
    hide(t::parse_signature_issuer);
    hide(t::parse_validity);
    hide(t::parse_subject_spki);
    hide(t::parse_optional_tail);
    let prefix = t::parse_prefix(input)->Some_0;
    lemma_prefix_opens(input);
    let (signature, issuer, p4) = t::parse_signature_issuer(input, prefix.pos, prefix.end)->Some_0;
    let (not_before, not_after, p5) = t::parse_validity(input, p4, prefix.end)->Some_0;
    let (subject, spki, p7) = t::parse_subject_spki(input, p5, prefix.end)->Some_0;
    assert(p7 <= prefix.end) by {
        reveal(t::parse_subject_spki);
        let w = d::read_tlv(input, p5, prefix.end)->Some_0;
        clazel_der::lemmas::lemma_read_tlv_bounds(input, p5, prefix.end);
        clazel_der::lemmas::lemma_read_tlv_bounds(input, w.cend, prefix.end);
    }
    lemma_tail_sequence(input, p7, prefix.end, prefix.version);
}

// ---------------------------------------------------------------------
// `parse_path_cert`, opened.
// ---------------------------------------------------------------------

/// What `parse_path_cert` read, stage by stage.
pub open spec fn path_stages(der: Seq<u8>, p: ps::PathCert, policy: Option<pc::PolicyConstraints>) -> bool {
    &&& c::parse_certificate(der) == Some(p.envelope)
    &&& t::parse_tbs_certificate(p.envelope.tbs_certificate_der) == Some(p.tbs)
    &&& ps::tbs_extensions(p.tbs) == Some(p.extensions)
    &&& lf::optional_basic_constraints(p.extensions) == Some(p.basic)
    &&& lf::optional_key_usage(p.extensions) == Some(p.key_usage)
    &&& lf::optional_extended_key_usage(p.extensions) == Some(p.eku)
    &&& ps::optional_name_constraints(p.extensions) == Some(p.name_constraints)
    &&& ps::optional_subject_alt_name(p.extensions) == Some(p.san)
    &&& ps::optional_policy_constraints(p.extensions) == Some(policy)
    &&& p.require_explicit_policy == ps::require_explicit_policy_of(policy)
    &&& p.has_policy_mappings == ps::has_extension(p.extensions, ps::policy_mappings_oid())
    &&& g::prepare_signature(
        p.tbs.signature,
        p.envelope.signature_algorithm,
        p.envelope.tbs_certificate_der,
        p.envelope.signature_bits,
        p.envelope.signature_unused_bits,
    ) == Some(p.signature)
}

/// `parse_path_cert` opened.
pub proof fn lemma_path_opens(der: Seq<u8>)
    requires
        ps::parse_path_cert(der) is Some,
    ensures
        ps::optional_policy_constraints(ps::parse_path_cert(der)->Some_0.extensions) is Some,
        path_stages(
            der,
            ps::parse_path_cert(der)->Some_0,
            ps::optional_policy_constraints(ps::parse_path_cert(der)->Some_0.extensions)->Some_0,
        ),
{
}

// ---------------------------------------------------------------------
// From `parse_path_cert`.
// ---------------------------------------------------------------------

/// A value `parse_path_cert` never reads.
pub open spec fn unread_by_path(oid: Seq<nat>) -> bool {
    oid == e::id_ce_authority_key_identifier() || oid == e::id_ce_subject_key_identifier() || oid
        == e::id_ce_certificate_policies() || oid == e::id_ce_inhibit_any_policy()
}

/// What is left of conditions 1 to 3 on the production path. Conditions 1 and
/// 2 are as in `equivalence.rs`, for the parts production reads. Condition 3
/// is now the unread values, the unread forms and the empty nameConstraints.
pub open spec fn path_conditions(p: ps::PathCert) -> bool {
    &&& parameters_plain(p.envelope.signature_algorithm)
    &&& parameters_plain(p.tbs.signature)
    &&& p.tbs.not_before.second != 60
    &&& p.tbs.not_after.second != 60
    &&& forall|k: int|
        0 <= k < p.extensions.len() && unread_by_path((#[trigger] p.extensions[k]).oid) ==> value_decodes(
            p.extensions[k],
        )
    &&& match p.san {
        Some(q) => san_forms_decode(q),
        None => true,
    }
    &&& match p.name_constraints {
        Some(q) => name_constraints_decodes(q),
        None => true,
    }
}

/// The two values of everything `parse_path_cert` looks up agree.
pub open spec fn path_values_agree(p: ps::PathCert, v: Seq<e::Extension>) -> bool {
    &&& extensions_agree(p.extensions, v)
    &&& basic_found_agree(p.basic, v)
    &&& key_usage_found_agree(p.key_usage, v)
    &&& eku_found_agree(p.eku, v)
    &&& name_constraints_found_agree(p.name_constraints, v)
    &&& san_found_agree(p.san, v)
    &&& policy_found_agree(ps::optional_policy_constraints(p.extensions)->Some_0, v)
    &&& p.has_policy_mappings == (r::find_extension(v, 0, e::id_ce(33)) is Some)
}

/// The arms of [`lemma_path_value_decodes`], each from one decoder's reading.
pub proof fn lemma_read_value_decodes(list: Seq<x::Extension>, k: int)
    requires
        0 <= k < list.len(),
        list[k].value.len() < two64(),
    ensures
        (list[k].oid == e::id_ce_basic_constraints() && cs::parse_basic_constraints(list[k].value) is Some)
            ==> value_decodes(list[k]),
        (list[k].oid == e::id_ce_key_usage() && cs::parse_key_usage(list[k].value) is Some) ==> value_decodes(
            list[k],
        ),
        (list[k].oid == e::id_ce_ext_key_usage() && cs::parse_extended_key_usage(list[k].value) is Some)
            ==> value_decodes(list[k]),
        (list[k].oid == e::id_ce_policy_constraints() && pc::parse_policy_constraints(list[k].value) is Some)
            ==> value_decodes(list[k]),
        (list[k].oid == e::id_ce_name_constraints() && nc::parse_name_constraints(list[k].value) is Some
            && name_constraints_decodes(nc::parse_name_constraints(list[k].value)->Some_0)) ==> value_decodes(
            list[k],
        ),
        (list[k].oid == e::id_ce_subject_alt_name() && x::parse_subject_alt_name(list[k].value) is Some
            && san_forms_decode(x::parse_subject_alt_name(list[k].value)->Some_0)) ==> value_decodes(list[k]),
{
    hide(cs::parse_basic_constraints);
    hide(cs::parse_key_usage);
    hide(cs::parse_extended_key_usage);
    hide(nc::parse_name_constraints);
    hide(x::parse_subject_alt_name);
    hide(pc::parse_policy_constraints);
    hide(e::decode_extension_value);
    let a = list[k];
    if a.oid == e::id_ce_basic_constraints() && cs::parse_basic_constraints(a.value) is Some {
        theorem_basic_constraints_fwd(a.value);
    }
    if a.oid == e::id_ce_key_usage() && cs::parse_key_usage(a.value) is Some {
        theorem_key_usage_fwd(a.value);
    }
    if a.oid == e::id_ce_ext_key_usage() && cs::parse_extended_key_usage(a.value) is Some {
        theorem_ext_key_usage_fwd(a.value);
    }
    if a.oid == e::id_ce_policy_constraints() && pc::parse_policy_constraints(a.value) is Some {
        theorem_policy_constraints_fwd(a.value);
    }
    if a.oid == e::id_ce_name_constraints() && nc::parse_name_constraints(a.value) is Some
        && name_constraints_decodes(nc::parse_name_constraints(a.value)->Some_0) {
        theorem_name_constraints_fwd(a.value);
    }
    if a.oid == e::id_ce_subject_alt_name() && x::parse_subject_alt_name(a.value) is Some && san_forms_decode(
        x::parse_subject_alt_name(a.value)->Some_0,
    ) {
        theorem_subject_alt_name_fwd(a.value);
    }
}

/// What an id's lookup read is the value of its one extension.
pub proof fn lemma_lookups_read(list: Seq<x::Extension>, k: int)
    requires
        0 <= k < list.len(),
        forall|a: int, b: int| 0 <= a < b < list.len() ==> #[trigger] list[a].oid != #[trigger] list[b].oid,
    ensures
        (list[k].oid == e::id_ce_basic_constraints() && lf::optional_basic_constraints(list) is Some) ==> (
        lf::optional_basic_constraints(list)->Some_0 == Some(cs::parse_basic_constraints(list[k].value)->Some_0)
            && cs::parse_basic_constraints(list[k].value) is Some),
        (list[k].oid == e::id_ce_key_usage() && lf::optional_key_usage(list) is Some) ==> (
        lf::optional_key_usage(list)->Some_0 == Some(cs::parse_key_usage(list[k].value)->Some_0)
            && cs::parse_key_usage(list[k].value) is Some),
        (list[k].oid == e::id_ce_ext_key_usage() && lf::optional_extended_key_usage(list) is Some) ==> (
        lf::optional_extended_key_usage(list)->Some_0 == Some(cs::parse_extended_key_usage(list[k].value)->Some_0)
            && cs::parse_extended_key_usage(list[k].value) is Some),
        (list[k].oid == e::id_ce_name_constraints() && ps::optional_name_constraints(list) is Some) ==> (
        ps::optional_name_constraints(list)->Some_0 == Some(nc::parse_name_constraints(list[k].value)->Some_0)
            && nc::parse_name_constraints(list[k].value) is Some),
        (list[k].oid == e::id_ce_subject_alt_name() && ps::optional_subject_alt_name(list) is Some) ==> (
        ps::optional_subject_alt_name(list)->Some_0 == Some(x::parse_subject_alt_name(list[k].value)->Some_0)
            && x::parse_subject_alt_name(list[k].value) is Some),
        (list[k].oid == e::id_ce_policy_constraints() && ps::optional_policy_constraints(list) is Some) ==> (
        ps::optional_policy_constraints(list)->Some_0 == Some(pc::parse_policy_constraints(list[k].value)->Some_0)
            && pc::parse_policy_constraints(list[k].value) is Some),
{
    hide(cs::parse_basic_constraints);
    hide(cs::parse_key_usage);
    hide(cs::parse_extended_key_usage);
    hide(nc::parse_name_constraints);
    hide(x::parse_subject_alt_name);
    hide(pc::parse_policy_constraints);
    lemma_oids();
    lemma_found_at(list, list[k].oid, 0, k);
}

/// Each extension of a path certificate is one `extensions.rs` reads.
#[verifier::spinoff_prover]
pub proof fn lemma_path_value_decodes(der: Seq<u8>, p: ps::PathCert, k: int)
    requires
        der.len() < two64(),
        ps::parse_path_cert(der) == Some(p),
        path_conditions(p),
        0 <= k < p.extensions.len(),
        forall|m: int| 0 <= m < p.extensions.len() ==> (#[trigger] p.extensions[m]).value.len() < two64(),
        forall|a: int, b: int| 0 <= a < b < p.extensions.len() ==> #[trigger] p.extensions[a].oid != #[trigger] p.extensions[b].oid,
    ensures
        value_decodes(p.extensions[k]),
{
    hide(ps::parse_path_cert);
    hide(lf::optional_basic_constraints);
    hide(lf::optional_key_usage);
    hide(lf::optional_extended_key_usage);
    hide(ps::optional_name_constraints);
    hide(ps::optional_subject_alt_name);
    hide(ps::optional_policy_constraints);
    hide(cs::parse_basic_constraints);
    hide(cs::parse_key_usage);
    hide(cs::parse_extended_key_usage);
    hide(nc::parse_name_constraints);
    hide(x::parse_subject_alt_name);
    hide(pc::parse_policy_constraints);
    hide(c::parse_certificate);
    hide(t::parse_tbs_certificate);
    hide(g::prepare_signature);
    hide(ps::tbs_extensions);
    hide(ps::has_extension);
    hide(ps::require_explicit_policy_of);
    hide(e::decode_extension_value);
    hide(name_constraints_decodes);
    lemma_path_opens(der);
    let list = p.extensions;
    let a = list[k];
    lemma_lookups_read(list, k);
    lemma_read_value_decodes(list, k);
    if !unread_by_path(a.oid) && a.oid != e::id_ce_basic_constraints() && a.oid != e::id_ce_key_usage()
        && a.oid != e::id_ce_ext_key_usage() && a.oid != e::id_ce_name_constraints() && a.oid
        != e::id_ce_subject_alt_name() && a.oid != e::id_ce_policy_constraints() {
        assert(value_decodes(a)) by {
            reveal(e::decode_extension_value);
        }
    }
}

/// `has_extension` on the crate's list, `find_extension` on the transcription's.
pub proof fn lemma_has_extension(a: Seq<x::Extension>, v: Seq<e::Extension>, oid: Seq<nat>)
    requires
        extensions_agree(a, v),
    ensures
        ps::has_extension(a, oid) == (r::find_extension(v, 0, oid) is Some),
{
    lemma_find(a, v, oid, 0);
}

/// **`theorem_path_cert_fwd`.** A certificate `parse_path_cert` keeps, the
/// transcription reads to the same values, with its Names and key left as
/// encodings. This is what every certificate on the production path passes
/// through.
#[verifier::spinoff_prover]
pub proof fn theorem_path_cert_fwd(der: Seq<u8>)
    requires
        der.len() < two64(),
        ps::parse_path_cert(der) is Some,
        path_conditions(ps::parse_path_cert(der)->Some_0),
    ensures
        decode_certificate_frame(der) is Some,
        ({
            let p = ps::parse_path_cert(der)->Some_0;
            let f = decode_certificate_frame(der)->Some_0;
            &&& tbs_frame_agree(p.tbs, f.to_be_signed)
            &&& algorithm_agree(p.envelope.signature_algorithm, f.algorithm_identifier)
            &&& f.signature.octets == p.envelope.signature_bits
            &&& f.signature.unused == p.envelope.signature_unused_bits as nat
            &&& f.tbs_encoding.encoding == p.envelope.tbs_certificate_der
            &&& path_values_agree(p, listed(f.to_be_signed.extensions))
        }),
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
    hide(g::prepare_signature);
    hide(tbs_frame_agree);
    hide(value_decodes);
    let p = ps::parse_path_cert(der)->Some_0;
    lemma_path_opens(der);
    let a = p.envelope;
    let tb = p.tbs;
    let input = a.tbs_certificate_der;
    let list = p.extensions;
    assert(input.len() <= der.len()) by {
        reveal(c::parse_certificate);
        lemma_envelope_length(der);
    }
    lemma_sequence_length(input, tb);
    if let Some(q) = tb.extensions_sequence_der {
        lemma_extensions_shape(q, list);
    }
    assert forall|k: int| 0 <= k < list.len() implies value_decodes(#[trigger] list[k]) by {
        reveal(path_conditions);
        lemma_path_value_decodes(der, p, k);
    }
    assert(extensions_decode(tb.extensions_sequence_der));
    assert(parameters_plain(a.signature_algorithm) && tbs_frame_conditions(tb)) by {
        reveal(path_conditions);
    }
    theorem_frame_fwd(der, a, tb);
    let f = decode_certificate_frame(der)->Some_0;
    let v = listed(f.to_be_signed.extensions);
    assert(optional_extensions_agree(tb.extensions_sequence_der, f.to_be_signed.extensions)) by {
        reveal(tbs_frame_agree);
    }
    assert(extensions_agree(list, v));
    assert(values_read(v)) by {
        if f.to_be_signed.extensions is Some {
            lemma_frame_values(der, f);
        }
    }
    assert(lookup_ready(list, v));
    assert(match p.san {
        Some(q) => san_forms_decode(q),
        None => true,
    } && match p.name_constraints {
        Some(q) => name_constraints_decodes(q),
        None => true,
    }) by {
        reveal(path_conditions);
    }
    lemma_found_basic(list, v, p.basic);
    lemma_found_key_usage(list, v, p.key_usage);
    lemma_found_eku(list, v, p.eku);
    lemma_found_name_constraints(list, v, p.name_constraints);
    lemma_found_san(list, v, p.san);
    lemma_found_policy(list, v, ps::optional_policy_constraints(list)->Some_0);
    lemma_oids();
    lemma_has_extension(list, v, ps::policy_mappings_oid());
}

/// The extensions of a frame are read.
#[verifier::spinoff_prover]
pub proof fn lemma_frame_values(der: Seq<u8>, f: CertificateFrame)
    requires
        decode_certificate_frame(der) == Some(f),
        f.to_be_signed.extensions is Some,
    ensures
        values_read(f.to_be_signed.extensions->Some_0),
{
    hide(s::decode_algorithm_identifier);
    hide(s::decode_validity);
    hide(tail_of);
    let u = i::parse_single(der)->Some_0;
    let l = s::sequence_elements(u)->Some_0;
    let e0 = s::sequence_elements(l[0])->Some_0;
    let m = s::after_version(e0);
    lemma_tail_values(e0.skip((m + 6) as int));
}

// ---------------------------------------------------------------------
// From the transcription.
// ---------------------------------------------------------------------

/// The crate's value of an AlgorithmIdentifier.
pub open spec fn algorithm_of(y: s::AlgorithmIdentifier) -> c::AlgorithmIdentifier {
    c::AlgorithmIdentifier {
        oid: y.algorithm,
        parameters_der: match y.parameters {
            Some(q) => Some(q.encoding),
            None => None,
        },
    }
}

/// `algorithm_of` is the value that agrees.
pub proof fn lemma_algorithm_of(a: c::AlgorithmIdentifier, y: s::AlgorithmIdentifier)
    requires
        algorithm_agree(a, y),
    ensures
        a == algorithm_of(y),
{
}

/// The signature `prepare_signature` takes: one algorithm in both places, and
/// `classify`'s refusals. X.509 leaves those to the algorithm.
pub open spec fn signature_in_domain(y: s::Certificate) -> bool {
    let a = algorithm_of(y.algorithm_identifier);
    &&& algorithm_of(y.to_be_signed.signature) == a
    &&& g::classify(a) is Some
    &&& !(g::classify(a)->Some_0 is Unsupported) ==> y.signature.unused == 0
}

/// The extensions of a decoded certificate are read.
#[verifier::spinoff_prover]
pub proof fn lemma_certificate_values(der: Seq<u8>, y: s::Certificate)
    requires
        s::decode_certificate(der) == Some(y),
        y.additions.len() == 0,
        r::one_signature_only(y),
    ensures
        values_read(r::extensions_of(y)),
{
    hide(s::decode_tbs_certificate);
    hide(s::decode_algorithm_identifier);
    lemma_certificate_opens(der, y);
    if y.to_be_signed.extensions is Some {
        let u = i::parse_single(der)->Some_0;
        let l = s::sequence_elements(u)->Some_0;
        lemma_tbs_opens(l[0], y.to_be_signed);
        let e0 = s::sequence_elements(l[0])->Some_0;
        let m = s::after_version(e0);
        lemma_tail_values(e0.skip((m + 6) as int));
    }
}

/// `parse_path_cert`, closed: each stage reads.
#[verifier::spinoff_prover]
pub proof fn lemma_path_closes(der: Seq<u8>, a: c::CertificateEnvelope, tb: t::TbsCertificate, list: Seq<x::Extension>)
    requires
        c::parse_certificate(der) == Some(a),
        t::parse_tbs_certificate(a.tbs_certificate_der) == Some(tb),
        ps::tbs_extensions(tb) == Some(list),
        lf::optional_basic_constraints(list) is Some,
        lf::optional_key_usage(list) is Some,
        lf::optional_extended_key_usage(list) is Some,
        ps::optional_name_constraints(list) is Some,
        ps::optional_subject_alt_name(list) is Some,
        ps::optional_policy_constraints(list) is Some,
        g::prepare_signature(
            tb.signature,
            a.signature_algorithm,
            a.tbs_certificate_der,
            a.signature_bits,
            a.signature_unused_bits,
        ) is Some,
    ensures
        ps::parse_path_cert(der) is Some,
        ({
            let p = ps::parse_path_cert(der)->Some_0;
            &&& p.envelope == a
            &&& p.tbs == tb
            &&& p.extensions == list
            &&& Some(p.basic) == lf::optional_basic_constraints(list)
            &&& Some(p.key_usage) == lf::optional_key_usage(list)
            &&& Some(p.eku) == lf::optional_extended_key_usage(list)
            &&& Some(p.name_constraints) == ps::optional_name_constraints(list)
            &&& Some(p.san) == ps::optional_subject_alt_name(list)
            &&& p.has_policy_mappings == ps::has_extension(list, ps::policy_mappings_oid())
        }),
{
    hide(c::parse_certificate);
    hide(t::parse_tbs_certificate);
    hide(lf::optional_basic_constraints);
    hide(lf::optional_key_usage);
    hide(lf::optional_extended_key_usage);
    hide(ps::optional_name_constraints);
    hide(ps::optional_subject_alt_name);
    hide(ps::optional_policy_constraints);
    hide(ps::tbs_extensions);
    hide(g::prepare_signature);
    hide(ps::has_extension);
}

/// The stages of `theorem_path_cert_back`, once the decoders have read.
#[verifier::spinoff_prover]
pub proof fn lemma_path_lookups(list: Seq<x::Extension>, v: Seq<e::Extension>)
    requires
        lookup_ready(list, v),
        values_in_domain(v),
    ensures
        lf::optional_basic_constraints(list) is Some,
        lf::optional_key_usage(list) is Some,
        lf::optional_extended_key_usage(list) is Some,
        ps::optional_name_constraints(list) is Some,
        ps::optional_subject_alt_name(list) is Some,
        ps::optional_policy_constraints(list) is Some,
        basic_found_agree(lf::optional_basic_constraints(list)->Some_0, v),
        key_usage_found_agree(lf::optional_key_usage(list)->Some_0, v),
        eku_found_agree(lf::optional_extended_key_usage(list)->Some_0, v),
        name_constraints_found_agree(ps::optional_name_constraints(list)->Some_0, v),
        san_found_agree(ps::optional_subject_alt_name(list)->Some_0, v),
        policy_found_agree(ps::optional_policy_constraints(list)->Some_0, v),
        ps::has_extension(list, ps::policy_mappings_oid()) == (r::find_extension(v, 0, e::id_ce(33)) is Some),
{
    hide(lf::optional_basic_constraints);
    hide(lf::optional_key_usage);
    hide(lf::optional_extended_key_usage);
    hide(ps::optional_name_constraints);
    hide(ps::optional_subject_alt_name);
    hide(ps::optional_policy_constraints);
    hide(lookup_ready);
    hide(values_in_domain);
    hide(basic_found_agree);
    hide(key_usage_found_agree);
    hide(eku_found_agree);
    hide(name_constraints_found_agree);
    hide(san_found_agree);
    hide(policy_found_agree);
    lemma_lookup_basic(list, v);
    lemma_lookup_key_usage(list, v);
    lemma_lookup_eku(list, v);
    lemma_lookup_name_constraints(list, v);
    lemma_lookup_san(list, v);
    lemma_lookup_policy(list, v);
    lemma_oids();
    assert(extensions_agree(list, v)) by {
        reveal(lookup_ready);
    }
    lemma_has_extension(list, v, ps::policy_mappings_oid());
}

/// The fields of a TBSCertificate agree, as `certificate_agree` states them.
pub open spec fn tbs_read_agree(a: t::TbsCertificate, y: s::TBSCertificate) -> bool {
    &&& a.version as int == y.version
    &&& i::parse_single(a.serial_number_der) is Some
    &&& i::decode_integer(i::parse_single(a.serial_number_der)->Some_0) == Some(y.serial_number)
    &&& algorithm_agree(a.signature, y.signature)
    &&& a.not_before == moment_time(time_moment(y.validity.not_before))
    &&& a.not_after == moment_time(time_moment(y.validity.not_after))
    &&& unique_agree(a.issuer_unique_id_der, y.issuer_unique_identifier)
    &&& unique_agree(a.subject_unique_id_der, y.subject_unique_identifier)
    &&& optional_extensions_agree(a.extensions_sequence_der, y.extensions)
}

/// The certificate-level facts `theorem_path_cert_back` keeps.
pub open spec fn path_cert_agree(p: ps::PathCert, y: s::Certificate) -> bool {
    &&& algorithm_agree(p.envelope.signature_algorithm, y.algorithm_identifier)
    &&& p.envelope.signature_unused_bits as nat == y.signature.unused
    &&& p.envelope.signature_bits == y.signature.octets
    &&& p.envelope.tbs_certificate_der == y.to_be_signed.encoding
    &&& tbs_read_agree(p.tbs, y.to_be_signed)
    &&& path_values_agree(p, r::extensions_of(y))
}

/// The extensions of a TBSCertificate the crate read, on both sides.
#[verifier::spinoff_prover]
pub proof fn lemma_back_list(input: Seq<u8>, tb: t::TbsCertificate, o: Option<Seq<e::Extension>>)
    requires
        input.len() < two64(),
        t::parse_tbs_certificate(input) == Some(tb),
        optional_extensions_agree(tb.extensions_sequence_der, o),
    ensures
        ps::tbs_extensions(tb) is Some,
        extensions_agree(ps::tbs_extensions(tb)->Some_0, listed(o)),
        forall|k: int|
            0 <= k < ps::tbs_extensions(tb)->Some_0.len() ==> (#[trigger] ps::tbs_extensions(tb)->Some_0[k]).value.len()
                < two64(),
{
    hide(t::parse_tbs_certificate);
    hide(x::parse_extensions);
    lemma_sequence_length(input, tb);
    if let Some(q) = tb.extensions_sequence_der {
        lemma_extensions_shape(q, x::parse_extensions(q)->Some_0);
    }
}

/// **`theorem_path_cert_back`.**
/// A certificate the transcription reads, inside
/// `certificate_in_domain`, with values the crate reads and a signature
/// `prepare_signature` takes, `parse_path_cert` keeps, to the same values.
#[verifier::spinoff_prover]
pub proof fn theorem_path_cert_back(der: Seq<u8>, y: s::Certificate)
    requires
        der.len() < two64(),
        s::decode_certificate(der) == Some(y),
        certificate_in_domain(y),
        values_in_domain(r::extensions_of(y)),
        signature_in_domain(y),
    ensures
        ps::parse_path_cert(der) is Some,
        path_cert_agree(ps::parse_path_cert(der)->Some_0, y),
{
    hide(c::parse_certificate);
    hide(t::parse_tbs_certificate);
    hide(lf::optional_basic_constraints);
    hide(lf::optional_key_usage);
    hide(lf::optional_extended_key_usage);
    hide(ps::optional_name_constraints);
    hide(ps::optional_subject_alt_name);
    hide(ps::optional_policy_constraints);
    hide(ps::parse_path_cert);
    hide(ps::has_extension);
    hide(ps::tbs_extensions);
    hide(g::prepare_signature);
    hide(g::classify);
    hide(s::decode_certificate);
    hide(certificate_in_domain);
    hide(crate_decode);
    hide(certificate_agree);
    hide(values_in_domain);
    hide(algorithm_agree);
    hide(tbs_read_agree);
    hide(path_values_agree);
    hide(optional_extensions_agree);
    hide(extensions_agree);
    hide(lookup_ready);
    hide(basic_found_agree);
    hide(key_usage_found_agree);
    hide(eku_found_agree);
    hide(name_constraints_found_agree);
    hide(san_found_agree);
    hide(policy_found_agree);
    theorem_certificate_back(der, y);
    assert(y.additions.len() == 0 && r::one_signature_only(y)) by {
        reveal(certificate_in_domain);
    }
    lemma_certificate_values(der, y);
    let a = crate_decode(der)->Some_0;
    assert(c::parse_certificate(der) == Some(a.envelope) && t::parse_tbs_certificate(
        a.envelope.tbs_certificate_der,
    ) == Some(a.tbs)) by {
        reveal(crate_decode);
        lemma_crate_decode_opens(der);
    }
    let env = a.envelope;
    let tb = a.tbs;
    let input = env.tbs_certificate_der;
    let b = y.to_be_signed;
    let v = r::extensions_of(y);
    assert(input.len() <= der.len()) by {
        reveal(c::parse_certificate);
        lemma_envelope_length(der);
    }
    assert(optional_extensions_agree(tb.extensions_sequence_der, b.extensions) && tbs_read_agree(tb, b)
        && algorithm_agree(env.signature_algorithm, y.algorithm_identifier) && algorithm_agree(
        tb.signature,
        b.signature,
    ) && env.signature_unused_bits as nat == y.signature.unused && env.signature_bits
        == y.signature.octets && env.tbs_certificate_der == b.encoding) by {
        reveal(certificate_agree);
        reveal(tbs_read_agree);
    }
    lemma_back_list(input, tb, b.extensions);
    let list = ps::tbs_extensions(tb)->Some_0;
    assert(listed(b.extensions) == v);
    assert(lookup_ready(list, v)) by {
        reveal(lookup_ready);
    }
    lemma_path_lookups(list, v);
    // One algorithm.
    lemma_algorithm_of(tb.signature, b.signature);
    lemma_algorithm_of(env.signature_algorithm, y.algorithm_identifier);
    assert(tb.signature == env.signature_algorithm);
    let alg = tb.signature;
    theorem_prepare_signature(alg, input, env.signature_bits, env.signature_unused_bits);
    lemma_path_closes(der, env, tb, list);
    let p = ps::parse_path_cert(der)->Some_0;
    assert(path_values_agree(p, v)) by {
        reveal(path_values_agree);
        reveal(lookup_ready);
        assert(ps::optional_policy_constraints(p.extensions)->Some_0 == ps::optional_policy_constraints(list)->Some_0);
    }
}

} // verus!
