//! Executable RFC 5280 §6.1 over decoded certificates, each function proven
//! to meet its predicate in `contract.rs`: §6.1.2 to §6.1.5 one step each,
//! the `process` fold, the browser profile, the comparison bound, the
//! verdict on one candidate path and the chain's inputs.
//!
//! - **The parameters** are the traits of `contract.rs`: signatures go
//!   through a `LinkVerifier`, revocation through a `RevocationOracle`.
//! - **Name constraints** are P5's executable matcher
//!   (`name_constraints::matching::exec`): `certificate_acceptable` for
//!   §6.1.3 (b), (c) and `prepare_name_constraints` for §6.1.4 (g), each equal
//!   to P4's spec; the comparison bound is P5's `charge`.
//! - **The counters** `explicit_policy` and `max_path_length` are `u128`.
//!   Every number the RFC compares them with (requireExplicitPolicy,
//!   pathLenConstraint) is a magnitude of any length, read only as
//!   `min(value, counter)` (`magnitude_at_most`), which is exact. The one
//!   place an unbounded number becomes a counter is the anchor's
//!   pathLenConstraint (RFC 5937 §3.2 bullet 8), which `initialization` holds
//!   at most `n` (`contract::initialization_ensures`); the fold's outcome is
//!   unchanged (`lemmas::lemma_process_from_agree`).
//! - **The fold** keeps, as its loop invariant, the spec state
//!   `contract::state_before` gives for `certs[i]`, with the executable state
//!   agreeing with it (`lemmas::states_agree`), and `decreases n - i`.
//! - **Work.** `candidate_verdict` decides the comparison bound before §6.1
//!   (`verifier::candidate_verdict`), so §6.1's name-constraint checks never
//!   run on a path beyond it.
//! - The candidate search (design §2.6) is not here: P9.

use super::contract::{LinkVerifier, RevocationOracle};
use super::parsed::exec::{Anchor, PathCert};
use super::spec::PathError;
use crate::exec::ReferenceIdentity;
use crate::name_constraints::exec as nc;
use crate::name_constraints::matching::exec as matching;
use crate::time::exec::CertificateTime;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Values and views
// ---------------------------------------------------------------------------

/// The §6.1.2 state variables `spec::State` keeps.
pub struct State<'a> {
    /// (b) permitted_subtrees and (c) excluded_subtrees: the NameConstraints in force.
    pub subtrees: Vec<&'a nc::NameConstraints<'a>>,
    /// (d) explicit_policy.
    pub explicit_policy: u128,
    /// (g), (h), (i): the working SubjectPublicKeyInfo DER.
    pub working_public_key: &'a [u8],
    /// (j) working_issuer_name: a Name DER.
    pub working_issuer_name: &'a [u8],
    /// (k) max_path_length.
    pub max_path_length: u128,
}

/// The spec value of a state.
pub open spec fn view_state(state: &State<'_>) -> super::spec::State {
    super::spec::State {
        subtrees: matching::view_state(state.subtrees@),
        explicit_policy: state.explicit_policy as nat,
        working_public_key: state.working_public_key@,
        working_issuer_name: state.working_issuer_name@,
        max_path_length: state.max_path_length as nat,
    }
}

/// The spec value of a state or an error.
pub open spec fn view_state_result(result: Result<State<'_>, PathError>) -> Result<super::spec::State, PathError> {
    match result {
        Ok(state) => Ok(view_state(&state)),
        Err(e) => Err(e),
    }
}

/// The spec value of a key or an error.
pub open spec fn view_key_result(result: Result<&[u8], PathError>) -> Result<Seq<u8>, PathError> {
    match result {
        Ok(key) => Ok(key@),
        Err(e) => Err(e),
    }
}

/// The spec value of a path.
pub open spec fn view_certs(certs: Seq<&PathCert<'_>>) -> Seq<super::parsed::spec::PathCert> {
    certs.map(|_i: int, cert: &PathCert<'_>| super::parsed::exec::view_path_cert(cert))
}

proof fn lemma_view_certs(certs: Seq<&PathCert<'_>>)
    ensures
        view_certs(certs).len() == certs.len(),
        forall|k: int| 0 <= k < certs.len() ==>
            #[trigger] view_certs(certs)[k] == super::parsed::exec::view_path_cert(certs[k]),
{
}

fn copy_time(value: &CertificateTime) -> (result: CertificateTime)
    ensures result@ == value@
{
    CertificateTime {
        year: value.year, month: value.month, day: value.day,
        hour: value.hour, minute: value.minute, second: value.second,
    }
}

/// Byte equality of two DER encodings.
fn bytes_equal(a: &[u8], b: &[u8]) -> (result: bool)
    ensures result == (a@ == b@)
{
    if a.len() != b.len() { return false; }
    let mut k: usize = 0;
    while k < a.len()
        invariant k <= a.len(), a.len() == b.len(), forall|j: int| 0 <= j < k ==> a@[j] == b@[j],
        decreases a.len() - k
    {
        match (a.get(k), b.get(k)) {
            (Some(x), Some(y)) => if *x != *y { return false; },
            _ => return false,
        }
        k = k.saturating_add(1);
    }
    proof { assert(a@ =~= b@); }
    true
}

// ---------------------------------------------------------------------------
// Magnitudes (`parsed::spec::skip_certs_value`)
// ---------------------------------------------------------------------------

proof fn lemma_be_value_step(s: Seq<u8>, k: int)
    requires 0 <= k < s.len(),
    ensures clazel_der::spec::be_value(s.take(k + 1)) == clazel_der::spec::be_value(s.take(k)) * 256 + s[k] as nat,
{
    assert(s.take(k + 1).drop_last() =~= s.take(k));
    assert(s.take(k + 1).last() == s[k]);
}

proof fn lemma_be_value_monotone(s: Seq<u8>, j: int, k: int)
    requires 0 <= j <= k <= s.len(),
    ensures clazel_der::spec::be_value(s.take(j)) <= clazel_der::spec::be_value(s.take(k)),
    decreases k - j,
{
    if j < k {
        lemma_be_value_monotone(s, j, k - 1);
        lemma_be_value_step(s, k - 1);
        let v = clazel_der::spec::be_value(s.take(k - 1));
        assert(v <= v * 256) by (nonlinear_arith);
    }
}

/// `min(be_value(octets), cap)`, in the spec's `if v < cap { v } else { cap }` form.
fn magnitude_at_most(octets: &[u8], cap: u128) -> (result: u128)
    ensures result as nat == (if clazel_der::spec::be_value(octets@) < cap as nat {
        clazel_der::spec::be_value(octets@) } else { cap as nat })
{
    proof { assert(octets@.take(0) =~= Seq::<u8>::empty()); }
    let mut value: u128 = 0;
    let mut k: usize = 0;
    while k < octets.len()
        invariant
            k <= octets.len(),
            value as nat == clazel_der::spec::be_value(octets@.take(k as int)),
            value <= cap,
        decreases octets.len() - k
    {
        let Some(byte) = octets.get(k) else { return cap; };
        proof {
            lemma_be_value_step(octets@, k as int);
            lemma_be_value_monotone(octets@, k as int + 1, octets.len() as int);
            assert(octets@.take(octets.len() as int) =~= octets@);
        }
        let Some(shifted) = value.checked_mul(256) else { return cap; };
        let Some(next) = shifted.checked_add(*byte as u128) else { return cap; };
        if next > cap { return cap; }
        value = next;
        k = k.saturating_add(1);
    }
    proof { assert(octets@.take(octets.len() as int) =~= octets@); }
    value
}

// ---------------------------------------------------------------------------
// §6.1.2 Initialization
// ---------------------------------------------------------------------------

/// §6.1.2 after RFC 5937 §3.2, for a path of `n` certificates;
/// `max_path_length` is held at most `n` (`contract::initialization_ensures`).
pub fn initialization<'a>(anchor: &'a Anchor<'a>, n: usize) -> (out: Result<State<'a>, PathError>)
    ensures super::contract::initialization_ensures(
        super::parsed::exec::view_anchor(anchor), n as nat, view_state_result(out)),
{
    // RFC 5937 §3.2 bullets 2 and 3, §6.1.2 (b), (c).
    let mut subtrees: Vec<&'a nc::NameConstraints<'a>> = Vec::new();
    proof {
        assert(matching::view_state(subtrees@) =~= crate::name_constraints::matching::spec::initial_state());
    }
    let extension = match &anchor.name_constraints { Some(value) => Some(value), None => None };
    if !matching::prepare_name_constraints(&mut subtrees, extension) {
        return Err(PathError::NameConstraintUnsupported);
    }
    let count = n as u128;
    // (k), RFC 5937 §3.2 bullet 8.
    let max_path_length = match anchor.path_len {
        Some(octets) => magnitude_at_most(octets, count),
        None => count,
    };
    Ok(State {
        subtrees,
        // (d) n + 1.
        explicit_policy: count.saturating_add(1),
        // (g), (h), (i).
        working_public_key: anchor.spki_der,
        // (j).
        working_issuer_name: anchor.subject_der,
        max_path_length,
    })
}

// ---------------------------------------------------------------------------
// §6.1.3 Basic Certificate Processing
// ---------------------------------------------------------------------------

/// §6.1.3 (b), (c) through P5's matcher.
fn names_acceptable(state: &State<'_>, cert: &PathCert<'_>) -> (result: bool)
    ensures result == crate::name_constraints::matching::spec::certificate_acceptable(
        view_state(state).subtrees, super::spec::nc_certificate(super::parsed::exec::view_path_cert(cert))),
{
    let empty: Vec<crate::extensions::exec::GeneralName<'_>> = Vec::new();
    let names = match &cert.san { Some(san) => san.names.as_slice(), None => empty.as_slice() };
    let certificate = matching::NcCertificate {
        subject: cert.tbs.subject_der,
        subject_alt_names: names,
        name_constraints: match &cert.name_constraints { Some(value) => Some(value), None => None },
    };
    proof {
        assert(crate::extensions::exec::view_general_names(empty@) =~= Seq::<crate::extensions::spec::GeneralName>::empty());
        assert(matching::view_nc_certificate(&certificate)
            == super::spec::nc_certificate(super::parsed::exec::view_path_cert(cert)));
    }
    matching::certificate_acceptable(state.subtrees.as_slice(), &certificate)
}

/// §6.1.3 (a)(2): the validity period includes `now`.
fn valid_at(not_before: &CertificateTime, not_after: &CertificateTime, now: &CertificateTime) -> (result: bool)
    ensures result == crate::time::spec::validity_contains(
        crate::time::spec::Validity { not_before: not_before@, not_after: not_after@ }, now@),
{
    match crate::time::exec::make_validity(copy_time(not_before), copy_time(not_after)) {
        Some(validity) => crate::time::exec::validity_contains(validity, copy_time(now)),
        None => {
            proof { crate::time::lemmas::lemma_make_validity_none_excludes_time(not_before@, not_after@, now@); }
            false
        },
    }
}

/// §6.1.3 for certificate `cert` under `state`.
pub fn basic_certificate_processing<L: LinkVerifier, R: RevocationOracle>(
    link: &L, revoked: &R, state: &State<'_>, cert: &PathCert<'_>, now: &CertificateTime,
) -> (out: Result<(), PathError>)
    ensures super::contract::basic_certificate_processing_ensures(
        link.link(), revoked.revoked(), view_state(state), super::parsed::exec::view_path_cert(cert), now@, out),
{
    // (a)(1), (R): an unsupported algorithm first.
    if let crate::signature_algorithm::exec::AlgorithmClass::Unsupported = cert.signature_class {
        return Err(PathError::UnsupportedAlgorithm);
    }
    // (a)(1): the signature, under working_public_key.
    if !link.verify(state.working_public_key, &cert.tbs.signature, cert.envelope.tbs_certificate_der,
        cert.envelope.signature_bits) {
        return Err(PathError::BadSignature);
    }
    // (a)(2): validity.
    if !valid_at(&cert.tbs.not_before, &cert.tbs.not_after, now) { return Err(PathError::Expired); }
    // (a)(3): revocation.
    if revoked.is_revoked(cert) { return Err(PathError::Revoked); }
    // (a)(4): the issuer is working_issuer_name, (R) byte for byte.
    if !bytes_equal(cert.tbs.issuer_der, state.working_issuer_name) { return Err(PathError::NameChaining); }
    // (b), (c): P4 through P5.
    if !names_acceptable(state, cert) { return Err(PathError::NameConstraint); }
    // (f), (R): explicit_policy greater than 0.
    if state.explicit_policy == 0 { return Err(PathError::PolicyRequired); }
    Ok(())
}

// ---------------------------------------------------------------------------
// §6.1.4 Preparation for Certificate i+1
// ---------------------------------------------------------------------------

/// §6.1.4 (o): the critical extensions an intermediate may carry.
fn intermediate_critical_supported(input: &[crate::extensions::exec::Extension<'_>]) -> (result: bool)
    ensures result == super::spec::intermediate_critical_supported(
        crate::extensions::exec::view_extensions(input@), 0),
{
    let basic_oid = crate::leaf::exec::basic_constraints_oid();
    let usage_oid = crate::leaf::exec::key_usage_oid();
    let eku_oid = crate::leaf::exec::extended_key_usage_oid();
    let nc_oid = super::parsed::exec::name_constraints_oid();
    let san_oid = crate::leaf::exec::san_oid();
    let policy_oid = super::parsed::exec::policy_constraints_oid();
    let mut index: usize = 0;
    while index < input.len()
        invariant
            index <= input.len(),
            clazel_der::decode::nats(basic_oid@) =~= crate::leaf::spec::basic_constraints_oid(),
            clazel_der::decode::nats(usage_oid@) =~= crate::leaf::spec::key_usage_oid(),
            clazel_der::decode::nats(eku_oid@) =~= crate::leaf::spec::extended_key_usage_extension_oid(),
            clazel_der::decode::nats(nc_oid@) =~= crate::name_constraints::spec::name_constraints_oid(),
            clazel_der::decode::nats(san_oid@) =~= crate::extensions::spec::subject_alt_name_oid(),
            clazel_der::decode::nats(policy_oid@) =~= crate::policy_constraints::spec::policy_constraints_oid(),
            super::spec::intermediate_critical_supported(crate::extensions::exec::view_extensions(input@), 0)
                == super::spec::intermediate_critical_supported(
                    crate::extensions::exec::view_extensions(input@), index as int),
        decreases input.len() - index
    {
        let Some(extension) = input.get(index) else { return false; };
        let supported = !extension.critical
            || crate::leaf::exec::oid_arcs_equal(&extension.oid, &basic_oid)
            || crate::leaf::exec::oid_arcs_equal(&extension.oid, &usage_oid)
            || crate::leaf::exec::oid_arcs_equal(&extension.oid, &eku_oid)
            || crate::leaf::exec::oid_arcs_equal(&extension.oid, &nc_oid)
            || crate::leaf::exec::oid_arcs_equal(&extension.oid, &san_oid)
            || crate::leaf::exec::oid_arcs_equal(&extension.oid, &policy_oid);
        proof {
            assert(crate::extensions::exec::view_extensions(input@)[index as int]
                == crate::extensions::exec::view_extension(&input@[index as int]));
        }
        if !supported { return false; }
        index = index.saturating_add(1);
    }
    true
}

/// §6.1.4 for certificate `cert` (never the last): `state` becomes the state
/// for the next certificate. On `Err` the state is unspecified.
pub fn preparation_for_next<'a>(state: &mut State<'a>, cert: &'a PathCert<'a>) -> (out: Result<(), PathError>)
    ensures super::contract::preparation_for_next_ensures(
        view_state(old(state)), super::parsed::exec::view_path_cert(cert),
        match out { Ok(()) => Ok(view_state(final(state))), Err(e) => Err(e) }),
{
    let ghost before = view_state(state);
    // (a), (R): any policyMappings.
    if cert.has_policy_mappings { return Err(PathError::PolicyMappings); }
    // (g): P4's §6.1.4 (g) through P5.
    let extension = match &cert.name_constraints { Some(value) => Some(value), None => None };
    if !matching::prepare_name_constraints(&mut state.subtrees, extension) {
        return Err(PathError::NameConstraintUnsupported);
    }
    let self_issued = bytes_equal(cert.tbs.issuer_der, cert.tbs.subject_der);
    // (h)(1): if not self-issued and explicit_policy is not 0, decrement it.
    let explicit_policy = if !self_issued && state.explicit_policy != 0 {
        state.explicit_policy.saturating_sub(1)
    } else {
        state.explicit_policy
    };
    // (i)(1): requireExplicitPolicy, if less.
    let explicit_policy = match cert.require_explicit_policy {
        Some(octets) => magnitude_at_most(octets, explicit_policy),
        None => explicit_policy,
    };
    // (k): v3 with basicConstraints cA TRUE.
    let is_ca = cert.tbs.version == 2 && match cert.basic { Some(basic) => basic.ca, None => false };
    if !is_ca { return Err(PathError::NotCa); }
    // (l): not self-issued: max_path_length greater than 0, then decrement it.
    if !self_issued && state.max_path_length == 0 { return Err(PathError::PathLen); }
    let max_path_length = if !self_issued { state.max_path_length.saturating_sub(1) } else { state.max_path_length };
    // (m): pathLenConstraint, if less.
    let max_path_length = match cert.basic {
        Some(basic) => match basic.path_len_constraint {
            Some(octets) => magnitude_at_most(octets, max_path_length),
            None => max_path_length,
        },
        None => max_path_length,
    };
    // (n): keyUsage, if present, with keyCertSign.
    let usage_refused = match cert.key_usage {
        Some(usage) => !crate::constraints::exec::key_usage_has(usage, crate::constraints::exec::KeyUsageBit::KeyCertSign),
        None => false,
    };
    if usage_refused { return Err(PathError::KeyUsage); }
    // (o): only recognized critical extensions.
    if !intermediate_critical_supported(cert.extensions.as_slice()) {
        return Err(PathError::UnknownCriticalExtension);
    }
    // (c), (d), (e), (f), and the counters.
    state.working_issuer_name = cert.tbs.subject_der;
    state.working_public_key = cert.tbs.subject_public_key_info_der;
    state.explicit_policy = explicit_policy;
    state.max_path_length = max_path_length;
    proof { reveal(crate::constraints::exec::view_key_usage_bit); }
    Ok(())
}

// ---------------------------------------------------------------------------
// §6.1.5 Wrap-Up Procedure
// ---------------------------------------------------------------------------

/// §6.1.5 for the target `cert`: its SubjectPublicKeyInfo DER.
pub fn wrap_up<'a>(state: &State<'_>, cert: &'a PathCert<'a>) -> (out: Result<&'a [u8], PathError>)
    ensures super::contract::wrap_up_ensures(
        view_state(state), super::parsed::exec::view_path_cert(cert), view_key_result(out)),
{
    // (a): if explicit_policy is not 0, decrement it.
    let explicit_policy = if state.explicit_policy != 0 { state.explicit_policy.saturating_sub(1) } else { 0 };
    // (b): requireExplicitPolicy of 0 sets it to 0 (`magnitude_at_most(_, 1)` is 0 exactly then).
    let explicit_policy = match cert.require_explicit_policy {
        Some(octets) => if magnitude_at_most(octets, 1) == 0 { 0 } else { explicit_policy },
        None => explicit_policy,
    };
    // (f): only the leaf's recognized critical extensions.
    if !crate::leaf::exec::critical_extensions_supported(cert.extensions.as_slice()) {
        return Err(PathError::UnknownCriticalExtension);
    }
    // explicit_policy greater than 0, (R) without the tree.
    if explicit_policy == 0 { return Err(PathError::PolicyRequired); }
    // (c), (d), (e), §6.1.6.
    Ok(cert.tbs.subject_public_key_info_der)
}

// ---------------------------------------------------------------------------
// §6.1 The procedure
// ---------------------------------------------------------------------------

/// `spec::der_absent_from(certs, der, from)`.
fn der_absent_from(certs: &[&PathCert<'_>], der: &[u8], from: usize) -> (result: bool)
    requires from <= certs.len(),
    ensures result == super::spec::der_absent_from(view_certs(certs@), der@, from as int),
{
    proof { lemma_view_certs(certs@); }
    let mut k = from;
    while k < certs.len()
        invariant
            from <= k <= certs.len(),
            super::spec::der_absent_from(view_certs(certs@), der@, from as int)
                == super::spec::der_absent_from(view_certs(certs@), der@, k as int),
        decreases certs.len() - k
    {
        let Some(cert) = certs.get(k) else { return false; };
        if bytes_equal(cert.der, der) { return false; }
        k = k.saturating_add(1);
    }
    true
}

/// `spec::certificates_distinct_from(certs, 0)`.
fn certificates_distinct(certs: &[&PathCert<'_>]) -> (result: bool)
    ensures result == super::spec::certificates_distinct_from(view_certs(certs@), 0),
{
    proof { lemma_view_certs(certs@); }
    let mut k: usize = 0;
    while k < certs.len()
        invariant
            k <= certs.len(),
            super::spec::certificates_distinct_from(view_certs(certs@), 0)
                == super::spec::certificates_distinct_from(view_certs(certs@), k as int),
        decreases certs.len() - k
    {
        let Some(cert) = certs.get(k) else { return false; };
        let next = k.saturating_add(1);
        if !der_absent_from(certs, cert.der, next) { return false; }
        k = next;
    }
    true
}

/// RFC 5280 §6.1 Basic Path Validation of `certs` (certificate 1 first)
/// under `anchor` at `now`: the target's SubjectPublicKeyInfo DER.
pub fn process<'a, L: LinkVerifier, R: RevocationOracle>(
    link: &L, revoked: &R, anchor: &'a Anchor<'a>, certs: &[&'a PathCert<'a>], now: &CertificateTime,
) -> (out: Result<&'a [u8], PathError>)
    ensures super::contract::process_ensures(link.link(), revoked.revoked(),
        super::parsed::exec::view_anchor(anchor), view_certs(certs@), now@, view_key_result(out)),
{
    let ghost spec_anchor = super::parsed::exec::view_anchor(anchor);
    let ghost spec_certs = view_certs(certs@);
    proof { lemma_view_certs(certs@); }
    let n = certs.len();
    // §6.1.1 (a).
    if n == 0 { return Err(PathError::EmptyPath); }
    // §6.1: no certificate twice.
    if !certificates_distinct(certs) { return Err(PathError::RepeatedCertificate); }
    // §6.1.2.
    let mut state = initialization(anchor, n)?;
    let ghost mut expected = super::spec::initialization(spec_anchor, n as nat)->Ok_0;
    let mut i: usize = 0;
    while i < n
        invariant
            n == certs.len(), 0 < n, i < n,
            spec_certs == view_certs(certs@),
            spec_anchor == super::parsed::exec::view_anchor(anchor),
            spec_certs.len() == n,
            forall|k: int| 0 <= k < n ==> #[trigger] spec_certs[k] == super::parsed::exec::view_path_cert(certs@[k]),
            super::spec::certificates_distinct_from(spec_certs, 0),
            super::contract::state_before(link.link(), revoked.revoked(), spec_anchor, spec_certs, now@, i as int)
                == Ok::<super::spec::State, PathError>(expected),
            super::lemmas::states_agree(view_state(&state), expected, (n - i) as nat),
        decreases n - i
    {
        proof {
            super::lemmas::lemma_process_from_state_before(
                link.link(), revoked.revoked(), spec_anchor, spec_certs, now@, i as int);
        }
        let Some(cert) = certs.get(i) else { return Err(PathError::EmptyPath); };
        let cert: &'a PathCert<'a> = cert;
        proof {
            assert(spec_certs[i as int] == super::parsed::exec::view_path_cert(cert));
            super::lemmas::lemma_basic_agree(link.link(), revoked.revoked(), view_state(&state), expected,
                spec_certs[i as int], now@, (n - i) as nat);
        }
        // §6.1.3 for certificate i+1.
        basic_certificate_processing(link, revoked, &state, cert, now)?;
        let next = i.saturating_add(1);
        // "If i is equal to n, perform the wrap-up steps".
        if next == n {
            proof {
                super::lemmas::lemma_wrap_up_agree(view_state(&state), expected, spec_certs[i as int], (n - i) as nat);
            }
            return wrap_up(&state, cert);
        }
        // Otherwise §6.1.4.
        let ghost before = view_state(&state);
        proof {
            super::lemmas::lemma_preparation_agree(before, expected, spec_certs[i as int], (n - i) as nat);
        }
        preparation_for_next(&mut state, cert)?;
        proof {
            expected = super::spec::preparation_for_next(expected, spec_certs[i as int])->Ok_0;
        }
        i = next;
    }
    Err(PathError::EmptyPath)
}

// ---------------------------------------------------------------------------
// The profile (`profile.rs`)
// ---------------------------------------------------------------------------

/// `profile::leaf_profile`.
fn leaf_profile(leaf: &PathCert<'_>, reference: ReferenceIdentity<'_>, now: &CertificateTime) -> (out: Result<(), PathError>)
    ensures out == super::profile::leaf_profile(super::parsed::exec::view_path_cert(leaf),
        crate::exec::view_reference_identity(&reference), now@),
{
    let policy = crate::leaf::exec::LeafPolicy { allow_any_extended_key_usage: false };
    // 1. `leaf::spec::check_extensions`.
    let checked = crate::leaf::exec::check_parsed_leaf_extensions(
        leaf.extensions.as_slice(), &leaf.tbs, reference, now, policy);
    if checked.is_none() { return Err(PathError::Leaf); }
    // 2. (R) extKeyUsage present.
    if leaf.eku.is_none() { return Err(PathError::ExtendedKeyUsage); }
    // 3. (R) nameConstraints absent.
    if leaf.name_constraints.is_some() { return Err(PathError::LeafNameConstraints); }
    Ok(())
}

/// `profile::anchor_profile`.
fn anchor_profile(anchor: &Anchor<'_>, leaf: &PathCert<'_>, now: &CertificateTime) -> (out: Result<(), PathError>)
    ensures out == super::profile::anchor_profile(super::parsed::exec::view_anchor(anchor),
        super::parsed::exec::view_path_cert(leaf), now@),
{
    // 1. (R) The anchor certificate is valid at `now`.
    if !valid_at(&anchor.not_before, &anchor.not_after, now) { return Err(PathError::AnchorExpired); }
    // 2. (R) distrust-after.
    let distrusted = match &anchor.server_distrust_after {
        Some(after) => !crate::time::exec::time_le(&leaf.tbs.not_before, after),
        None => false,
    };
    if distrusted { return Err(PathError::Distrusted); }
    Ok(())
}

/// `profile::intermediate_profile`.
fn intermediate_profile(cert: &PathCert<'_>) -> (out: Result<(), PathError>)
    ensures out == super::profile::intermediate_profile(super::parsed::exec::view_path_cert(cert)),
{
    // 1. (R) keyUsage present.
    if cert.key_usage.is_none() { return Err(PathError::KeyUsage); }
    // 2. (R) extKeyUsage absent or with serverAuth.
    let eku_refused = match &cert.eku {
        Some(eku) => !crate::constraints::exec::eku_allows_server_auth_borrowed(eku, false),
        None => false,
    };
    if eku_refused { return Err(PathError::ExtendedKeyUsage); }
    Ok(())
}

/// `profile::intermediates_profile_from(certs, 0)`.
fn intermediates_profile(certs: &[&PathCert<'_>]) -> (out: Result<(), PathError>)
    ensures out == super::profile::intermediates_profile_from(view_certs(certs@), 0),
{
    proof { lemma_view_certs(certs@); }
    let mut i: usize = 0;
    while i.saturating_add(1) < certs.len()
        invariant
            i < certs.len() || certs.len() == 0 && i == 0,
            super::profile::intermediates_profile_from(view_certs(certs@), 0)
                == super::profile::intermediates_profile_from(view_certs(certs@), i as int),
        decreases certs.len() - i
    {
        let Some(cert) = certs.get(i) else { return Ok(()); };
        intermediate_profile(cert)?;
        i = i.saturating_add(1);
    }
    Ok(())
}

/// `profile::path_profile`.
pub fn path_profile(
    anchor: &Anchor<'_>, certs: &[&PathCert<'_>], reference: ReferenceIdentity<'_>, now: &CertificateTime,
) -> (out: Result<(), PathError>)
    ensures super::contract::path_profile_ensures(super::parsed::exec::view_anchor(anchor), view_certs(certs@),
        crate::exec::view_reference_identity(&reference), now@, out),
{
    proof { lemma_view_certs(certs@); }
    let Some(last) = certs.len().checked_sub(1) else { return Err(PathError::EmptyPath); };
    let Some(leaf) = certs.get(last) else { return Err(PathError::EmptyPath); };
    proof { assert(view_certs(certs@).last() == super::parsed::exec::view_path_cert(*leaf)); }
    leaf_profile(leaf, reference, now)?;
    anchor_profile(anchor, leaf, now)?;
    intermediates_profile(certs)
}

// ---------------------------------------------------------------------------
// The comparison bound (`verifier::path_within_budget`)
// ---------------------------------------------------------------------------

/// The subjectAltName entries of a certificate.
fn entry_count(cert: &PathCert<'_>) -> (result: usize)
    ensures result as nat == super::spec::nc_certificate(super::parsed::exec::view_path_cert(cert)).subject_alt_names.len(),
{
    match &cert.san { Some(san) => san.names.len(), None => 0 }
}

/// `verifier::path_within_budget`: P5's comparison bound over the path.
pub fn path_within_budget<'a>(anchor: &'a Anchor<'a>, certs: &[&'a PathCert<'a>]) -> (out: bool)
    ensures super::contract::path_within_budget_ensures(
        super::parsed::exec::view_anchor(anchor), view_certs(certs@), out),
{
    proof {
        lemma_view_certs(certs@);
        super::lemmas::lemma_nc_path(view_certs(certs@));
    }
    let ghost path = super::verifier::nc_path(view_certs(certs@));
    let mut state: Vec<&'a nc::NameConstraints<'a>> = Vec::new();
    proof {
        assert(matching::view_state(state@) =~= crate::name_constraints::matching::spec::initial_state());
    }
    let extension = match &anchor.name_constraints { Some(value) => Some(value), None => None };
    // The anchor's constraints are unsupported: vacuous (§6.1 refuses the path).
    if !matching::prepare_name_constraints(&mut state, extension) { return true; }
    let ghost initial = matching::view_state(state@);
    let mut spent: usize = 0;
    let mut i: usize = 0;
    while i < certs.len()
        invariant
            i <= certs.len(),
            path == super::verifier::nc_path(view_certs(certs@)),
            path.len() == certs.len(),
            forall|k: int| 0 <= k < certs.len() ==>
                #[trigger] path[k] == super::spec::nc_certificate(super::parsed::exec::view_path_cert(certs@[k])),
            super::verifier::anchor_subtrees(super::parsed::exec::view_anchor(anchor)) == Some(initial),
            crate::name_constraints::matching::contract::within_comparison_bound(spent as nat),
            crate::name_constraints::matching::contract::within_budget(path, initial)
                == crate::name_constraints::matching::contract::within_budget_from(
                    path, i as int, matching::view_state(state@), spent as nat),
        decreases certs.len() - i
    {
        let Some(cert) = certs.get(i) else { return false; };
        proof { lemma_view_certs(certs@); assert(path[i as int] == super::spec::nc_certificate(super::parsed::exec::view_path_cert(*cert))); }
        let Some(total) = matching::charge(state.as_slice(), entry_count(cert), spent) else { return false; };
        let next = i.saturating_add(1);
        if next < certs.len() {
            let extension = match &cert.name_constraints { Some(value) => Some(value), None => None };
            // Once a certificate's constraints are refused, §6.1 refuses the path.
            if !matching::prepare_name_constraints(&mut state, extension) { return true; }
        }
        spent = total;
        i = next;
    }
    true
}

// ---------------------------------------------------------------------------
// One candidate (`verifier::candidate_verdict`)
// ---------------------------------------------------------------------------

/// The spec value of the anchors.
pub open spec fn view_anchors(anchors: Seq<Anchor<'_>>) -> Seq<super::parsed::spec::Anchor> {
    anchors.map(|_i: int, anchor: Anchor<'_>| super::parsed::exec::view_anchor(&anchor))
}

/// The spec value of the pool.
pub open spec fn view_pool(pool: Seq<Option<PathCert<'_>>>) -> Seq<Option<super::parsed::spec::PathCert>> {
    pool.map(|_i: int, item: Option<PathCert<'_>>| super::parsed::exec::view_path_cert_result(item))
}

/// The spec value of a candidate's pool indices.
pub open spec fn view_indices(path: Seq<usize>) -> Seq<nat> {
    path.map(|_i: int, index: usize| index as nat)
}

/// The verifier's parameters that are not data from the peer
/// (`verifier::Environment`).
pub struct Environment<'e, L: LinkVerifier, R: RevocationOracle> {
    /// §6.1.3 (a)(1).
    pub link: &'e L,
    /// §6.1.3 (a)(3).
    pub revoked: &'e R,
    /// Design §1.12: the most intermediates a candidate may have.
    pub max_intermediates: usize,
}

/// The spec value of an environment.
pub open spec fn view_environment<L: LinkVerifier, R: RevocationOracle>(environment: &Environment<'_, L, R>)
    -> super::verifier::Environment
{
    super::verifier::Environment {
        link: environment.link.link(),
        revoked: environment.revoked.revoked(),
        max_intermediates: environment.max_intermediates as nat,
    }
}

/// A candidate path (`verifier::Candidate`): an anchor index and pool indices.
pub struct Candidate<'p> {
    /// Index into the anchors.
    pub anchor: usize,
    /// Indices into the pool, the anchor's child first.
    pub path: &'p [usize],
}

/// The spec value of a candidate.
pub open spec fn view_candidate(candidate: &Candidate<'_>) -> super::verifier::Candidate {
    super::verifier::Candidate { anchor: candidate.anchor as nat, path: view_indices(candidate.path@) }
}

proof fn lemma_index_absent(path: Seq<nat>, index: nat, from: int)
    requires 0 <= from, forall|k: int| from <= k < path.len() ==> path[k] != index,
    ensures super::verifier::index_absent_from(path, index, from),
    decreases path.len() - from,
{
    if from < path.len() { lemma_index_absent(path, index, from + 1); }
}

proof fn lemma_index_present(path: Seq<nat>, index: nat, from: int, k: int)
    requires 0 <= from <= k < path.len(), path[k] == index,
    ensures !super::verifier::index_absent_from(path, index, from),
    decreases k - from,
{
    if from < k { lemma_index_present(path, index, from + 1, k); }
}

/// `verifier::index_absent_from(path, index, from)`.
fn index_absent_from(path: &[usize], index: usize, from: usize) -> (result: bool)
    requires from <= path.len(),
    ensures result == super::verifier::index_absent_from(view_indices(path@), index as nat, from as int),
{
    let mut k = from;
    while k < path.len()
        invariant from <= k <= path.len(), view_indices(path@).len() == path.len(),
            forall|j: int| from <= j < k ==> view_indices(path@)[j] != index as nat,
        decreases path.len() - k
    {
        let Some(item) = path.get(k) else { return false; };
        proof { assert(view_indices(path@)[k as int] == *item as nat); }
        if *item == index {
            proof { lemma_index_present(view_indices(path@), index as nat, from as int, k as int); }
            return false;
        }
        k = k.saturating_add(1);
    }
    proof { lemma_index_absent(view_indices(path@), index as nat, from as int); }
    true
}

/// `verifier::indices_distinct_from(path, 0)`.
fn indices_distinct(path: &[usize]) -> (result: bool)
    ensures result == super::verifier::indices_distinct_from(view_indices(path@), 0),
{
    let mut k: usize = 0;
    while k < path.len()
        invariant
            k <= path.len(), view_indices(path@).len() == path.len(),
            super::verifier::indices_distinct_from(view_indices(path@), 0)
                == super::verifier::indices_distinct_from(view_indices(path@), k as int),
        decreases path.len() - k
    {
        let Some(item) = path.get(k) else { return false; };
        let next = k.saturating_add(1);
        if !index_absent_from(path, *item, next) { return false; }
        k = next;
    }
    true
}

/// `verifier::indices_usable_from(pool, path, 0)`.
fn indices_usable(pool: &[Option<PathCert<'_>>], path: &[usize]) -> (result: bool)
    ensures result == super::verifier::indices_usable_from(view_pool(pool@), view_indices(path@), 0),
{
    let mut k: usize = 0;
    while k < path.len()
        invariant
            k <= path.len(), view_indices(path@).len() == path.len(), view_pool(pool@).len() == pool.len(),
            super::verifier::indices_usable_from(view_pool(pool@), view_indices(path@), 0)
                == super::verifier::indices_usable_from(view_pool(pool@), view_indices(path@), k as int),
        decreases path.len() - k
    {
        let Some(item) = path.get(k) else { return false; };
        match pool.get(*item) {
            Some(Some(_)) => {},
            _ => return false,
        }
        k = k.saturating_add(1);
    }
    true
}

proof fn lemma_intermediates_of(pool: Seq<Option<super::parsed::spec::PathCert>>, path: Seq<nat>)
    requires forall|k: int| 0 <= k < path.len() ==> path[k] < pool.len() && (#[trigger] pool[path[k] as int]) is Some,
    ensures
        super::verifier::intermediates_of(pool, path).len() == path.len(),
        forall|k: int| 0 <= k < path.len() ==>
            #[trigger] super::verifier::intermediates_of(pool, path)[k] == pool[path[k] as int]->Some_0,
    decreases path.len(),
{
    if path.len() > 0 {
        let prefix = path.drop_last();
        assert forall|k: int| 0 <= k < prefix.len() implies prefix[k] < pool.len()
            && (#[trigger] pool[prefix[k] as int]) is Some by {
            assert(prefix[k] == path[k]);
        }
        lemma_intermediates_of(pool, prefix);
        assert(pool[path[path.len() - 1] as int] is Some);
        assert forall|k: int| 0 <= k < path.len() implies
            #[trigger] super::verifier::intermediates_of(pool, path)[k] == pool[path[k] as int]->Some_0 by {
            if k < path.len() - 1 { assert(prefix[k] == path[k]); }
        }
    }
}

proof fn lemma_indices_usable(pool: Seq<Option<super::parsed::spec::PathCert>>, path: Seq<nat>, from: int)
    requires super::verifier::indices_usable_from(pool, path, from), 0 <= from,
    ensures forall|k: int| from <= k < path.len() ==> path[k] < pool.len() && (#[trigger] pool[path[k] as int]) is Some,
    decreases path.len() - from,
{
    if from < path.len() { lemma_indices_usable(pool, path, from + 1); }
}

/// `verifier::candidate_certificates` of a well-formed candidate.
fn candidate_certificates<'a>(pool: &'a [Option<PathCert<'a>>], leaf: &'a PathCert<'a>, path: &[usize])
    -> (certs: Vec<&'a PathCert<'a>>)
    requires super::verifier::indices_usable_from(view_pool(pool@), view_indices(path@), 0),
    ensures view_certs(certs@) == super::verifier::candidate_certificates(view_pool(pool@),
        super::parsed::exec::view_path_cert(leaf),
        super::verifier::Candidate { anchor: 0, path: view_indices(path@) }),
{
    let ghost spec_pool = view_pool(pool@);
    let ghost spec_path = view_indices(path@);
    let ghost candidate = super::verifier::Candidate { anchor: 0, path: spec_path };
    proof { lemma_indices_usable(spec_pool, spec_path, 0); }
    // §6.1.1 (a): the prospective path, certificate 1 first.
    let mut certs: Vec<&'a PathCert<'a>> = Vec::new();
    let mut k: usize = 0;
    while k < path.len()
        invariant
            k <= path.len(), spec_path == view_indices(path@), spec_pool == view_pool(pool@),
            spec_path.len() == path.len(), spec_pool.len() == pool.len(),
            forall|j: int| 0 <= j < spec_path.len() ==> spec_path[j] < spec_pool.len()
                && (#[trigger] spec_pool[spec_path[j] as int]) is Some,
            certs.len() == k,
            forall|j: int| 0 <= j < k ==> #[trigger] super::parsed::exec::view_path_cert(certs@[j])
                == spec_pool[spec_path[j] as int]->Some_0,
        decreases path.len() - k
    {
        let Some(index) = path.get(k) else { return certs; };
        proof {
            assert(spec_path[k as int] == *index as nat);
            assert(spec_pool[*index as int] is Some);
            assert(spec_pool[*index as int] == super::parsed::exec::view_path_cert_result(pool@[*index as int]));
        }
        let Some(Some(cert)) = pool.get(*index) else { return certs; };
        certs.push(cert);
        k = k.saturating_add(1);
    }
    certs.push(leaf);
    proof {
        lemma_intermediates_of(spec_pool, spec_path);
        lemma_view_certs(certs@);
        assert(view_certs(certs@) =~= super::verifier::candidate_certificates(
            spec_pool, super::parsed::exec::view_path_cert(leaf), candidate));
    }
    certs
}

/// `verifier::candidate_verdict` on the candidate `anchors[anchor]`, then
/// `pool[path[0]]`, ..., then `leaf`.
pub fn candidate_verdict<'a, L: LinkVerifier, R: RevocationOracle>(
    environment: &Environment<'_, L, R>, anchors: &'a [Anchor<'a>], pool: &'a [Option<PathCert<'a>>],
    leaf: &'a PathCert<'a>, candidate: &Candidate<'_>, reference: ReferenceIdentity<'_>, now: &CertificateTime,
) -> (out: Result<&'a [u8], PathError>)
    ensures super::contract::candidate_verdict_ensures(
        view_environment(environment), view_anchors(anchors@), view_pool(pool@),
        super::parsed::exec::view_path_cert(leaf), view_candidate(candidate),
        crate::exec::view_reference_identity(&reference), now@, view_key_result(out)),
{
    hide(super::spec::process);
    hide(super::profile::path_profile);
    hide(super::verifier::path_within_budget);
    let anchor = candidate.anchor;
    let path = candidate.path;
    let max_intermediates = environment.max_intermediates;
    // Well formed (design §2.6).
    let well_formed = anchor < anchors.len() && path.len() <= max_intermediates
        && indices_usable(pool, path) && indices_distinct(path);
    if !well_formed {
        if path.len() > max_intermediates { return Err(PathError::TooManyIntermediates); }
        return Err(PathError::UnknownIssuer);
    }
    let Some(trust_anchor) = anchors.get(anchor) else { return Err(PathError::UnknownIssuer); };
    let certs = candidate_certificates(pool, leaf, path);
    proof {
        assert(view_anchors(anchors@)[anchor as int] == super::parsed::exec::view_anchor(trust_anchor));
    }
    // The profile, then the comparison bound, then §6.1.
    path_profile(trust_anchor, certs.as_slice(), reference, now)?;
    if !path_within_budget(trust_anchor, certs.as_slice()) { return Err(PathError::TooManyNameComparisons); }
    process(environment.link, environment.revoked, trust_anchor, certs.as_slice(), now)
}

// ---------------------------------------------------------------------------
// The presented chain (`verifier::chain_inputs`)
// ---------------------------------------------------------------------------

/// The leaf, the pool and the time a chain's verdict starts from.
pub struct ChainInputs<'a> {
    /// `presented[0]`, parsed.
    pub leaf: PathCert<'a>,
    /// `presented[1..]`, parsed; `None` where one does not parse.
    pub pool: Vec<Option<PathCert<'a>>>,
    /// `now`, as a certificate time.
    pub now: CertificateTime,
}

/// The spec value of the presented certificates.
pub open spec fn view_presented(presented: Seq<&[u8]>) -> Seq<Seq<u8>> {
    presented.map(|_i: int, der: &[u8]| der@)
}

/// The spec value of the inputs or an error.
pub open spec fn view_chain_inputs_result(result: Result<ChainInputs<'_>, PathError>)
    -> Result<super::verifier::ChainInputs, PathError>
{
    match result {
        Ok(inputs) => Ok(super::verifier::ChainInputs {
            leaf: super::parsed::exec::view_path_cert(&inputs.leaf),
            pool: view_pool(inputs.pool@),
            now: inputs.now@,
        }),
        Err(e) => Err(e),
    }
}

proof fn lemma_parsed_pool(presented: Seq<Seq<u8>>)
    requires presented.len() >= 1,
    ensures
        super::verifier::parsed_pool(presented).len() == presented.len() - 1,
        forall|j: int| 0 <= j < presented.len() - 1 ==>
            #[trigger] super::verifier::parsed_pool(presented)[j] == super::parsed::spec::parse_path_cert(presented[j + 1]),
    decreases presented.len(),
{
    hide(super::parsed::spec::parse_path_cert);
    if presented.len() > 1 {
        let prefix = presented.drop_last();
        lemma_parsed_pool(prefix);
        assert forall|j: int| 0 <= j < presented.len() - 1 implies
            #[trigger] super::verifier::parsed_pool(presented)[j] == super::parsed::spec::parse_path_cert(presented[j + 1]) by {
            if j < presented.len() - 2 { assert(prefix[j + 1] == presented[j + 1]); }
        }
    }
}

/// `verifier::chain_inputs`.
pub fn chain_inputs<'a>(presented: &[&'a [u8]], now: u64) -> (out: Result<ChainInputs<'a>, PathError>)
    ensures super::contract::chain_inputs_ensures(view_presented(presented@), now, view_chain_inputs_result(out)),
{
    hide(super::parsed::spec::parse_path_cert);
    let ghost spec_presented = view_presented(presented@);
    // 1. RFC 8446 §4.4.2: the server's certificate first.
    let Some(first) = presented.first() else { return Err(PathError::Malformed); };
    // 2. The leaf parses and the time is a certificate time.
    let leaf = super::parsed::exec::parse_path_cert(first);
    let time = crate::time::exec::from_unix_seconds(now);
    let (Some(leaf), Some(time)) = (leaf, time) else { return Err(PathError::Malformed); };
    // The pool: every later certificate, parsed or `None`.
    let mut pool: Vec<Option<PathCert<'a>>> = Vec::new();
    let mut k: usize = 1;
    while k < presented.len()
        invariant
            1 <= k <= presented.len(),
            pool.len() == k - 1,
            forall|j: int| 0 <= j < k - 1 ==> #[trigger] super::parsed::exec::view_path_cert_result(pool@[j])
                == super::parsed::spec::parse_path_cert(presented@[j + 1]@),
        decreases presented.len() - k
    {
        let Some(der) = presented.get(k) else { return Err(PathError::Malformed); };
        let ghost before = pool@;
        pool.push(super::parsed::exec::parse_path_cert(der));
        proof {
            assert forall|j: int| 0 <= j < k implies #[trigger] super::parsed::exec::view_path_cert_result(pool@[j])
                == super::parsed::spec::parse_path_cert(presented@[j + 1]@) by {
                if j < k - 1 { assert(pool@[j] == before[j]); }
            }
        }
        k = k.saturating_add(1);
    }
    proof {
        lemma_parsed_pool(spec_presented);
        assert(view_pool(pool@) =~= super::verifier::parsed_pool(spec_presented)) by {
            assert forall|j: int| 0 <= j < pool.len() implies #[trigger] view_pool(pool@)[j]
                == super::verifier::parsed_pool(spec_presented)[j] by {
                assert(spec_presented[j + 1] == presented@[j + 1]@);
            }
        }
        assert(spec_presented[0] == first@);
    }
    Ok(ChainInputs { leaf, pool, now: time })
}

} // verus!
