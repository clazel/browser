//! Proofs about §6.1 (`spec.rs`), the profile (`profile.rs`) and P7's
//! stated theorems (`theorems.rs`).
//!
//! - **The fold.** `lemma_process_from_state_before` proves P7's
//!   `contract::process_from_state_before`: the spec's `process` continues as
//!   `process_from` from `contract::state_before`. `lemma_process_from_agree`
//!   proves that two states whose `max_path_length` are equal, or both at
//!   least the number of certificates still to process, give the same
//!   `process_from`; the executable fold (`exec.rs`) holds its counter that
//!   way (`contract::initialization_ensures`).
//! - **An accepted path, round by round.** `lemma_accepted_rounds`: on a
//!   path `process` accepts, every round of Figure 2 succeeds, so every
//!   step's checks hold of the state `state_before` gives it. Each theorem
//!   below reads its statement off those checks.
//! - **The theorems** (design §3.5), one lemma `lemma_<name>` with
//!   `ensures theorems::<name>(...)` each, for every input, and
//!   `lemma_all_path_theorems` for their conjunction. With
//!   `theorems::lemma_candidate_reduces` they hold of every valid candidate.
//!   `thm_anchored` is proven for the path (its §6.1 part); the enumeration
//!   part is P9's.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The fold
// ---------------------------------------------------------------------------

/// The counter `exec` stands for `spec` while `remaining` certificates are
/// still to process: equal, or both too large to reach 0 in §6.1.4 (l).
pub open spec fn counter_agrees(exec: nat, spec: nat, remaining: nat) -> bool {
    exec == spec || (exec >= remaining && spec >= remaining)
}

/// Two states that differ at most in a `max_path_length` too large to
/// matter for the `remaining` certificates.
pub open spec fn states_agree(a: State, b: State, remaining: nat) -> bool {
    &&& a.subtrees == b.subtrees
    &&& a.explicit_policy == b.explicit_policy
    &&& a.working_public_key == b.working_public_key
    &&& a.working_issuer_name == b.working_issuer_name
    &&& counter_agrees(a.max_path_length, b.max_path_length, remaining)
}

/// §6.1.3 does not read `max_path_length`.
pub proof fn lemma_basic_agree(
    link: LinkFn, revoked: RevokedFn, a: State, b: State, cert: super::parsed::spec::PathCert,
    now: crate::time::spec::CertificateTime, remaining: nat,
)
    requires states_agree(a, b, remaining),
    ensures basic_certificate_processing(link, revoked, a, cert, now)
        == basic_certificate_processing(link, revoked, b, cert, now),
{
}

/// §6.1.5 does not read `max_path_length`.
pub proof fn lemma_wrap_up_agree(a: State, b: State, cert: super::parsed::spec::PathCert, remaining: nat)
    requires states_agree(a, b, remaining),
    ensures wrap_up(a, cert) == wrap_up(b, cert),
{
}

/// §6.1.4 keeps two agreeing states agreeing, for one certificate fewer:
/// both counters are at least 2 or equal, so (l) refuses both or neither,
/// and (l), (m) keep them equal or both at least `remaining - 1`.
pub proof fn lemma_preparation_agree(a: State, b: State, cert: super::parsed::spec::PathCert, remaining: nat)
    requires states_agree(a, b, remaining), remaining >= 2,
    ensures
        match (preparation_for_next(a, cert), preparation_for_next(b, cert)) {
            (Ok(x), Ok(y)) => states_agree(x, y, (remaining - 1) as nat),
            (Err(e), Err(f)) => e == f,
            _ => false,
        },
{
    let after_a = if !self_issued(cert) { (a.max_path_length - 1) as nat } else { a.max_path_length };
    let after_b = if !self_issued(cert) { (b.max_path_length - 1) as nat } else { b.max_path_length };
    assert(counter_agrees(after_a, after_b, (remaining - 1) as nat));
    assert(counter_agrees(max_path_length_after_m(after_a, cert), max_path_length_after_m(after_b, cert),
        (remaining - 1) as nat));
}

/// `process_from` is the same from two agreeing states.
pub proof fn lemma_process_from_agree(
    link: LinkFn, revoked: RevokedFn, certs: Seq<super::parsed::spec::PathCert>, i: int,
    now: crate::time::spec::CertificateTime, a: State, b: State,
)
    requires 0 <= i < certs.len(), states_agree(a, b, (certs.len() - i) as nat),
    ensures process_from(link, revoked, certs, i, now, a) == process_from(link, revoked, certs, i, now, b),
    decreases certs.len() - i,
{
    let remaining = (certs.len() - i) as nat;
    lemma_basic_agree(link, revoked, a, b, certs[i], now, remaining);
    lemma_wrap_up_agree(a, b, certs[i], remaining);
    if i < certs.len() - 1 {
        lemma_preparation_agree(a, b, certs[i], remaining);
        match (preparation_for_next(a, certs[i]), preparation_for_next(b, certs[i])) {
            (Ok(x), Ok(y)) => lemma_process_from_agree(link, revoked, certs, i + 1, now, x, y),
            _ => {},
        }
    }
}

/// P7's `contract::process_from_state_before`, for every `i`.
pub proof fn lemma_process_from_state_before(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime, i: int,
)
    ensures super::contract::process_from_state_before(link, revoked, anchor, certs, now, i),
    decreases i,
{
    if certs.len() > 0 && certificates_distinct_from(certs, 0) && 0 < i < certs.len() {
        lemma_process_from_state_before(link, revoked, anchor, certs, now, i - 1);
    }
}

// ---------------------------------------------------------------------------
// The comparison bound
// ---------------------------------------------------------------------------

/// What P4 reads from each certificate, by index.
pub proof fn lemma_nc_path(certs: Seq<super::parsed::spec::PathCert>)
    ensures
        super::verifier::nc_path(certs).len() == certs.len(),
        forall|i: int| 0 <= i < certs.len() ==>
            #[trigger] super::verifier::nc_path(certs)[i] == nc_certificate(certs[i]),
    decreases certs.len(),
{
    if certs.len() > 0 {
        lemma_nc_path(certs.drop_last());
        assert forall|i: int| 0 <= i < certs.len() implies
            #[trigger] super::verifier::nc_path(certs)[i] == nc_certificate(certs[i]) by {
            if i < certs.len() - 1 {
                assert(certs.drop_last()[i] == certs[i]);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// An accepted path, round by round
// ---------------------------------------------------------------------------

/// The state §6.1.3 finds for `certs[i]`, when `state_before` is `Ok`.
pub open spec fn round_state(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime, i: int,
) -> State {
    super::contract::state_before(link, revoked, anchor, certs, now, i)->Ok_0
}

/// One round of an accepted path: its state exists, §6.1.3 succeeds on it,
/// and §6.1.4 or §6.1.5 is what follows.
pub proof fn lemma_round(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime, i: int,
)
    requires process(link, revoked, anchor, certs, now) is Ok, 0 <= i < certs.len(),
    ensures
        super::contract::state_before(link, revoked, anchor, certs, now, i) is Ok,
        process(link, revoked, anchor, certs, now)
            == process_from(link, revoked, certs, i, now, round_state(link, revoked, anchor, certs, now, i)),
        basic_certificate_processing(link, revoked, round_state(link, revoked, anchor, certs, now, i), certs[i], now) is Ok,
        i < certs.len() - 1 ==> preparation_for_next(round_state(link, revoked, anchor, certs, now, i), certs[i])
            == super::contract::state_before(link, revoked, anchor, certs, now, i + 1),
        i == certs.len() - 1 ==> wrap_up(round_state(link, revoked, anchor, certs, now, i), certs[i])
            == process(link, revoked, anchor, certs, now),
{
    lemma_process_from_state_before(link, revoked, anchor, certs, now, i);
    assert(certs.len() > 0 && certificates_distinct_from(certs, 0));
}

/// Every round of an accepted path succeeds.
pub proof fn lemma_accepted_rounds(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime,
)
    requires process(link, revoked, anchor, certs, now) is Ok,
    ensures
        certs.len() > 0,
        certificates_distinct_from(certs, 0),
        initialization(anchor, certs.len()) == Ok::<State, PathError>(round_state(link, revoked, anchor, certs, now, 0)),
        forall|i: int| 0 <= i < certs.len() ==>
            basic_certificate_processing(link, revoked, #[trigger] round_state(link, revoked, anchor, certs, now, i),
                certs[i], now) is Ok,
        forall|i: int| 0 <= i < certs.len() - 1 ==>
            preparation_for_next(#[trigger] round_state(link, revoked, anchor, certs, now, i), certs[i])
                == Ok::<State, PathError>(round_state(link, revoked, anchor, certs, now, i + 1)),
        wrap_up(round_state(link, revoked, anchor, certs, now, certs.len() - 1), certs[certs.len() - 1])
            == process(link, revoked, anchor, certs, now),
{
    assert(certs.len() > 0 && certificates_distinct_from(certs, 0));
    lemma_round(link, revoked, anchor, certs, now, 0);
    assert forall|i: int| 0 <= i < certs.len() implies
        basic_certificate_processing(link, revoked, #[trigger] round_state(link, revoked, anchor, certs, now, i),
            certs[i], now) is Ok by {
        lemma_round(link, revoked, anchor, certs, now, i);
    }
    assert forall|i: int| 0 <= i < certs.len() - 1 implies
        preparation_for_next(#[trigger] round_state(link, revoked, anchor, certs, now, i), certs[i])
            == Ok::<State, PathError>(round_state(link, revoked, anchor, certs, now, i + 1)) by {
        lemma_round(link, revoked, anchor, certs, now, i);
        lemma_round(link, revoked, anchor, certs, now, i + 1);
    }
    lemma_round(link, revoked, anchor, certs, now, certs.len() - 1);
}

/// What a successful §6.1.3 establishes.
pub proof fn lemma_basic_ok(
    link: LinkFn, revoked: RevokedFn, state: State, cert: super::parsed::spec::PathCert,
    now: crate::time::spec::CertificateTime,
)
    requires basic_certificate_processing(link, revoked, state, cert, now) is Ok,
    ensures
        link(signed_data(state.working_public_key, cert)),
        crate::time::spec::validity_contains(validity(cert), now),
        cert.tbs.issuer_der == state.working_issuer_name,
        crate::name_constraints::matching::spec::certificate_acceptable(state.subtrees, nc_certificate(cert)),
        state.explicit_policy != 0,
{
}

/// What a successful §6.1.4 establishes, and the state it returns.
pub proof fn lemma_preparation_ok(state: State, cert: super::parsed::spec::PathCert)
    requires preparation_for_next(state, cert) is Ok,
    ensures ({
        let next = preparation_for_next(state, cert)->Ok_0;
        &&& !cert.has_policy_mappings
        &&& crate::name_constraints::matching::spec::prepare_name_constraints(state.subtrees, cert.name_constraints)
            == Some(next.subtrees)
        &&& next.working_issuer_name == cert.tbs.subject_der
        &&& next.working_public_key == cert.tbs.subject_public_key_info_der
        &&& next.explicit_policy == explicit_policy_after_i(explicit_policy_after_h(state, cert), cert)
        &&& cert.tbs.version == 2
        &&& match cert.basic { Some(basic) => basic.ca, None => false }
        &&& (!self_issued(cert) ==> state.max_path_length > 0 && next.max_path_length < state.max_path_length)
        &&& (self_issued(cert) ==> next.max_path_length <= state.max_path_length)
        &&& match cert.basic {
            Some(basic) => match basic.path_len_constraint {
                Some(octets) => next.max_path_length <= super::parsed::spec::skip_certs_value(octets),
                None => true,
            },
            None => true,
        }
        &&& match cert.key_usage {
            Some(usage) => crate::constraints::spec::key_usage_has(
                usage, crate::constraints::spec::KeyUsageBit::KeyCertSign),
            None => true,
        }
        &&& intermediate_critical_supported(cert.extensions, 0)
    }),
{
}

/// The state §6.1.3 finds for `certs[i]`: the anchor's name and key for
/// certificate 1, the previous certificate's after that.
pub proof fn lemma_working_names(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime, i: int,
)
    requires process(link, revoked, anchor, certs, now) is Ok, 0 <= i < certs.len(),
    ensures
        i == 0 ==> round_state(link, revoked, anchor, certs, now, i).working_public_key == anchor.spki_der
            && round_state(link, revoked, anchor, certs, now, i).working_issuer_name == anchor.subject_der,
        i > 0 ==> round_state(link, revoked, anchor, certs, now, i).working_public_key
                == certs[i - 1].tbs.subject_public_key_info_der
            && round_state(link, revoked, anchor, certs, now, i).working_issuer_name == certs[i - 1].tbs.subject_der,
{
    lemma_accepted_rounds(link, revoked, anchor, certs, now);
    if i > 0 {
        assert(preparation_for_next(round_state(link, revoked, anchor, certs, now, i - 1), certs[i - 1])
            == Ok::<State, PathError>(round_state(link, revoked, anchor, certs, now, i)));
        lemma_preparation_ok(round_state(link, revoked, anchor, certs, now, i - 1), certs[i - 1]);
    }
}

// ---------------------------------------------------------------------------
// The theorems
// ---------------------------------------------------------------------------

/// `theorems::thm_links_verify`.
pub proof fn lemma_thm_links_verify(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime,
)
    ensures super::theorems::thm_links_verify(link, revoked, anchor, certs, now),
{
    if process(link, revoked, anchor, certs, now) is Ok {
        lemma_accepted_rounds(link, revoked, anchor, certs, now);
        lemma_working_names(link, revoked, anchor, certs, now, 0);
        lemma_basic_ok(link, revoked, round_state(link, revoked, anchor, certs, now, 0), certs[0], now);
        assert forall|i: int| 0 < i < certs.len() implies
            link(#[trigger] signed_data(certs[i - 1].tbs.subject_public_key_info_der, certs[i])) by {
            lemma_working_names(link, revoked, anchor, certs, now, i);
            lemma_basic_ok(link, revoked, round_state(link, revoked, anchor, certs, now, i), certs[i], now);
        }
    }
}

/// No DER of `certs[from..]` is `der`.
pub proof fn lemma_der_absent(certs: Seq<super::parsed::spec::PathCert>, der: Seq<u8>, from: int)
    requires der_absent_from(certs, der, from), 0 <= from,
    ensures forall|k: int| from <= k < certs.len() ==> (#[trigger] certs[k]).der != der,
    decreases certs.len() - from,
{
    if from < certs.len() {
        lemma_der_absent(certs, der, from + 1);
    }
}

/// `certificates_distinct_from` says what its name says.
pub proof fn lemma_distinct(certs: Seq<super::parsed::spec::PathCert>, from: int)
    requires certificates_distinct_from(certs, from), 0 <= from,
    ensures forall|i: int, j: int| from <= i < j < certs.len() ==> (#[trigger] certs[i]).der != (#[trigger] certs[j]).der,
    decreases certs.len() - from,
{
    if from < certs.len() {
        lemma_der_absent(certs, certs[from].der, from + 1);
        lemma_distinct(certs, from + 1);
    }
}

/// On an accepted path, certificate i+1's issuer is certificate i's subject
/// (§6.1.3 (a)(4) against §6.1.4 (c)).
pub proof fn lemma_issuer_chain(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime, i: int,
)
    requires process(link, revoked, anchor, certs, now) is Ok, 0 <= i < certs.len(),
    ensures
        i == 0 ==> certs[i].tbs.issuer_der == anchor.subject_der,
        i > 0 ==> certs[i].tbs.issuer_der == certs[i - 1].tbs.subject_der,
{
    lemma_round(link, revoked, anchor, certs, now, i);
    lemma_working_names(link, revoked, anchor, certs, now, i);
    lemma_basic_ok(link, revoked, round_state(link, revoked, anchor, certs, now, i), certs[i], now);
}

/// Every link of an accepted path chains by name.
pub proof fn lemma_issuer_chain_all(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime,
)
    requires process(link, revoked, anchor, certs, now) is Ok,
    ensures forall|i: int| 0 < i < certs.len() ==>
        (#[trigger] certs[i]).tbs.issuer_der == (#[trigger] certs[i - 1]).tbs.subject_der,
{
    // Two triggers: one would be a matching loop (certs[i] yields certs[i - 1]).
    assert forall|i: int| 0 < i < certs.len() implies
        (#[trigger] certs[i]).tbs.issuer_der == (#[trigger] certs[i - 1]).tbs.subject_der by {
        lemma_issuer_chain(link, revoked, anchor, certs, now, i);
    }
}

/// `theorems::thm_anchored`, the path part.
pub proof fn lemma_thm_anchored(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime,
)
    ensures super::theorems::thm_anchored(link, revoked, anchor, certs, now),
{
    if process(link, revoked, anchor, certs, now) is Ok {
        assert(certs.len() > 0 && certificates_distinct_from(certs, 0));
        lemma_distinct(certs, 0);
        lemma_issuer_chain(link, revoked, anchor, certs, now, 0);
        lemma_issuer_chain_all(link, revoked, anchor, certs, now);
    }
}

/// The intermediates' profile holds of each intermediate.
pub proof fn lemma_intermediates_profile(certs: Seq<super::parsed::spec::PathCert>, from: int)
    requires super::profile::intermediates_profile_from(certs, from) is Ok, 0 <= from,
    ensures forall|i: int| from <= i < certs.len() - 1 ==>
        super::profile::intermediate_profile(#[trigger] certs[i]) is Ok,
    decreases certs.len() - from,
{
    if from < certs.len() - 1 {
        lemma_intermediates_profile(certs, from + 1);
    }
}

/// What a passing profile establishes.
pub proof fn lemma_profile_ok(
    anchor: super::parsed::spec::Anchor, certs: Seq<super::parsed::spec::PathCert>,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
)
    requires super::profile::path_profile(anchor, certs, reference, now) is Ok,
    ensures
        certs.len() > 0,
        super::profile::leaf_profile(certs.last(), reference, now) is Ok,
        super::profile::anchor_profile(anchor, certs.last(), now) is Ok,
        forall|i: int| 0 <= i < certs.len() - 1 ==> super::profile::intermediate_profile(#[trigger] certs[i]) is Ok,
{
    lemma_intermediates_profile(certs, 0);
}

/// `theorems::thm_cas`.
pub proof fn lemma_thm_cas(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime,
)
    ensures super::theorems::thm_cas(link, revoked, anchor, certs, reference, now),
{
    if super::theorems::accepts(link, revoked, anchor, certs, reference, now) {
        lemma_accepted_rounds(link, revoked, anchor, certs, now);
        lemma_profile_ok(anchor, certs, reference, now);
        assert forall|i: int| 0 <= i < certs.len() - 1 implies {
            let cert = #[trigger] certs[i];
            &&& cert.tbs.version == 2
            &&& match cert.basic { Some(basic) => basic.ca, None => false }
            &&& match cert.key_usage {
                Some(usage) => crate::constraints::spec::key_usage_has(
                    usage, crate::constraints::spec::KeyUsageBit::KeyCertSign),
                None => false,
            }
            &&& match cert.eku {
                Some(eku) => crate::constraints::spec::eku_allows_server_auth(eku, false),
                None => true,
            }
            &&& !cert.has_policy_mappings
            &&& intermediate_critical_supported(cert.extensions, 0)
        } by {
            let state = round_state(link, revoked, anchor, certs, now, i);
            assert(preparation_for_next(state, certs[i])
                == Ok::<State, PathError>(round_state(link, revoked, anchor, certs, now, i + 1)));
            lemma_preparation_ok(state, certs[i]);
            assert(super::profile::intermediate_profile(certs[i]) is Ok);
        }
    }
}

/// The count of non-self-issued certificates of `certs[from..to]`, one at a time.
pub proof fn lemma_non_self_issued_step(certs: Seq<super::parsed::spec::PathCert>, from: int, to: int)
    requires 0 <= from < to <= certs.len(),
    ensures super::theorems::non_self_issued_between(certs, from, to)
        == (if self_issued(certs[from]) { 0nat } else { 1nat })
            + super::theorems::non_self_issued_between(certs, from + 1, to),
{
}

/// On an accepted path, the non-self-issued intermediates from `certs[j]`
/// on are at most the `max_path_length` §6.1.3 finds for `certs[j]`
/// (design §1.7: "a lemma relating the counter to a count of
/// non-self-issued certs; induction on i").
pub proof fn lemma_path_len_counter(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime, j: int,
)
    requires process(link, revoked, anchor, certs, now) is Ok, 0 <= j < certs.len(),
    ensures super::theorems::non_self_issued_between(certs, j, certs.len() - 1)
        <= round_state(link, revoked, anchor, certs, now, j).max_path_length,
    decreases certs.len() - j,
{
    lemma_accepted_rounds(link, revoked, anchor, certs, now);
    if j < certs.len() - 1 {
        lemma_path_len_counter(link, revoked, anchor, certs, now, j + 1);
        lemma_non_self_issued_step(certs, j, certs.len() - 1);
        let state = round_state(link, revoked, anchor, certs, now, j);
        assert(preparation_for_next(state, certs[j])
            == Ok::<State, PathError>(round_state(link, revoked, anchor, certs, now, j + 1)));
        lemma_preparation_ok(state, certs[j]);
    }
}

/// `theorems::thm_path_len_respected`.
pub proof fn lemma_thm_path_len_respected(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime,
)
    ensures super::theorems::thm_path_len_respected(link, revoked, anchor, certs, now),
{
    if process(link, revoked, anchor, certs, now) is Ok {
        lemma_accepted_rounds(link, revoked, anchor, certs, now);
        lemma_path_len_counter(link, revoked, anchor, certs, now, 0);
        assert forall|i: int| 0 <= i < certs.len() - 1 implies match (#[trigger] certs[i]).basic {
            Some(basic) => match basic.path_len_constraint {
                Some(octets) => super::theorems::non_self_issued_between(certs, i + 1, certs.len() - 1)
                    <= super::parsed::spec::skip_certs_value(octets),
                None => true,
            },
            None => true,
        } by {
            let state = round_state(link, revoked, anchor, certs, now, i);
            assert(preparation_for_next(state, certs[i])
                == Ok::<State, PathError>(round_state(link, revoked, anchor, certs, now, i + 1)));
            lemma_preparation_ok(state, certs[i]);
            lemma_path_len_counter(link, revoked, anchor, certs, now, i + 1);
        }
    }
}

/// On an accepted path, P4's whole-path statement holds from `certs[j]` on,
/// under the subtrees §6.1.3 finds for `certs[j]` (design §3.5: "state sets
/// = NCs of path[0..i]").
pub proof fn lemma_names_constrained_from(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime, j: int,
)
    requires process(link, revoked, anchor, certs, now) is Ok, 0 <= j < certs.len(),
    ensures crate::name_constraints::matching::spec::names_constrained_from(
        super::verifier::nc_path(certs), j, round_state(link, revoked, anchor, certs, now, j).subtrees),
    decreases certs.len() - j,
{
    lemma_accepted_rounds(link, revoked, anchor, certs, now);
    lemma_nc_path(certs);
    let state = round_state(link, revoked, anchor, certs, now, j);
    lemma_basic_ok(link, revoked, state, certs[j], now);
    assert(super::verifier::nc_path(certs)[j] == nc_certificate(certs[j]));
    if j < certs.len() - 1 {
        assert(preparation_for_next(state, certs[j])
            == Ok::<State, PathError>(round_state(link, revoked, anchor, certs, now, j + 1)));
        lemma_preparation_ok(state, certs[j]);
        lemma_names_constrained_from(link, revoked, anchor, certs, now, j + 1);
    }
}

/// `theorems::thm_names_constrained`.
pub proof fn lemma_thm_names_constrained(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime,
)
    ensures super::theorems::thm_names_constrained(link, revoked, anchor, certs, now),
{
    if process(link, revoked, anchor, certs, now) is Ok {
        lemma_accepted_rounds(link, revoked, anchor, certs, now);
        lemma_names_constrained_from(link, revoked, anchor, certs, now, 0);
        assert(super::verifier::anchor_subtrees(anchor)
            == Some(round_state(link, revoked, anchor, certs, now, 0).subtrees));
    }
}

/// `theorems::thm_valid_at_now`.
pub proof fn lemma_thm_valid_at_now(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime,
)
    ensures super::theorems::thm_valid_at_now(link, revoked, anchor, certs, reference, now),
{
    if super::theorems::accepts(link, revoked, anchor, certs, reference, now) {
        lemma_accepted_rounds(link, revoked, anchor, certs, now);
        lemma_profile_ok(anchor, certs, reference, now);
        assert forall|i: int| 0 <= i < certs.len() implies
            crate::time::spec::validity_contains(validity(#[trigger] certs[i]), now) by {
            lemma_basic_ok(link, revoked, round_state(link, revoked, anchor, certs, now, i), certs[i], now);
        }
    }
}

/// `theorems::thm_leaf_profile`.
pub proof fn lemma_thm_leaf_profile(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime,
)
    ensures super::theorems::thm_leaf_profile(link, revoked, anchor, certs, reference, now),
{
    if super::theorems::accepts(link, revoked, anchor, certs, reference, now) {
        lemma_accepted_rounds(link, revoked, anchor, certs, now);
        lemma_profile_ok(anchor, certs, reference, now);
        assert(certs.last() == certs[certs.len() - 1]);
    }
}

/// The explicit_policy §6.1.3 finds for `certs[i]` is the one
/// `theorems::explicit_policy_at` re-derives.
pub proof fn lemma_explicit_policy_at(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime, i: int,
)
    requires process(link, revoked, anchor, certs, now) is Ok, 0 <= i < certs.len(),
    ensures round_state(link, revoked, anchor, certs, now, i).explicit_policy
        == super::theorems::explicit_policy_at(certs, i),
    decreases i,
{
    lemma_accepted_rounds(link, revoked, anchor, certs, now);
    if i > 0 {
        lemma_explicit_policy_at(link, revoked, anchor, certs, now, i - 1);
        let state = round_state(link, revoked, anchor, certs, now, i - 1);
        assert(preparation_for_next(state, certs[i - 1])
            == Ok::<State, PathError>(round_state(link, revoked, anchor, certs, now, i)));
        lemma_preparation_ok(state, certs[i - 1]);
    }
}

/// `theorems::policy_free_sound` (design `lemma_policy_free_sound`).
pub proof fn lemma_policy_free_sound(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime,
)
    ensures super::theorems::policy_free_sound(link, revoked, anchor, certs, now),
{
    if process(link, revoked, anchor, certs, now) is Ok {
        lemma_accepted_rounds(link, revoked, anchor, certs, now);
        assert forall|i: int| 0 <= i < certs.len() implies
            #[trigger] super::theorems::explicit_policy_at(certs, i) > 0 by {
            lemma_explicit_policy_at(link, revoked, anchor, certs, now, i);
            lemma_basic_ok(link, revoked, round_state(link, revoked, anchor, certs, now, i), certs[i], now);
        }
        lemma_explicit_policy_at(link, revoked, anchor, certs, now, certs.len() - 1);
        assert(certs.last() == certs[certs.len() - 1]);
        assert(super::theorems::explicit_policy_final(certs) > 0);
    }
}

/// Every theorem of §3.5 that is about one path (P8's target).
pub proof fn lemma_all_path_theorems(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime,
)
    ensures super::theorems::all_path_theorems(link, revoked, anchor, certs, reference, now),
{
    lemma_thm_links_verify(link, revoked, anchor, certs, now);
    lemma_thm_anchored(link, revoked, anchor, certs, now);
    lemma_thm_cas(link, revoked, anchor, certs, reference, now);
    lemma_thm_path_len_respected(link, revoked, anchor, certs, now);
    lemma_thm_names_constrained(link, revoked, anchor, certs, now);
    lemma_thm_valid_at_now(link, revoked, anchor, certs, reference, now);
    lemma_thm_leaf_profile(link, revoked, anchor, certs, reference, now);
    lemma_policy_free_sound(link, revoked, anchor, certs, now);
}

} // verus!
