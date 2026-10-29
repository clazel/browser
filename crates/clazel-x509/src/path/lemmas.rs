//! Proofs about §6.1 (`spec.rs`) that the executable fold (`exec.rs`) uses.
//!
//! - **The fold.** `lemma_process_from_state_before` proves P7's
//!   `contract::process_from_state_before`: the spec's `process` continues as
//!   `process_from` from `contract::state_before`. `lemma_process_from_agree`
//!   proves that two states whose `max_path_length` are equal, or both at
//!   least the number of certificates still to process, give the same
//!   `process_from`; the executable fold (`exec.rs`) holds its counter that
//!   way (`contract::initialization_ensures`).

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

} // verus!
