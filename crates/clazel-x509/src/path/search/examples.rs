//! Known answers for the search (`spec.rs`), each proven by evaluation.
//! They are the theorems the certified mutations of `spec.rs` in
//! `mutations.json` contradict. The fixtures are `path::examples`'s:
//! one-RDN names, `link()` accepting a certificate whose signature bytes are
//! its issuer's key, validity 2020 to 2040 and `now` 2026-06-01.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A pool of parsed certificates.
pub open spec fn pool(certs: Seq<super::super::parsed::spec::PathCert>) -> Seq<Option<super::super::parsed::spec::PathCert>> {
    certs.map(|_i: int, c: super::super::parsed::spec::PathCert| Some(c))
}

/// The search over one anchor, `pool`, a leaf, `max_intermediates` m and a budget.
pub open spec fn run(
    m: nat, pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert, budget: nat,
) -> Result<super::super::verifier::Validated, super::super::spec::PathError> {
    search(super::super::examples::environment(m), seq![super::super::examples::anchor()], pool, leaf,
        super::super::examples::reference(), super::super::examples::now(), budget)
}

/// The whole order over one anchor.
pub open spec fn order(
    m: nat, pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
) -> Seq<super::super::verifier::IssuerStep> {
    search_order(super::super::examples::environment(m), seq![super::super::examples::anchor()], pool, leaf)
}

/// An accepted chain through `anchor()` with these pool indices and the leaf's key.
pub open spec fn accepted(path: Seq<nat>) -> Result<super::super::verifier::Validated, super::super::spec::PathError> {
    Ok(super::super::verifier::Validated { anchor: 0, path, leaf_spki: super::super::examples::key(9) })
}

/// A refusal.
pub open spec fn refused(e: super::super::spec::PathError) -> Result<super::super::verifier::Validated, super::super::spec::PathError> {
    Err(e)
}

/// A copy of the root `roo -> roo`, key 1, self-signed, as a CA.
pub open spec fn root_copy() -> super::super::parsed::spec::PathCert {
    super::super::examples::ca(30, super::super::examples::root_name(), super::super::examples::root_name(),
        super::super::examples::key(1), super::super::examples::key(1))
}

/// `int` cross-signed by `in3` (an issuer this example has no anchor for), same key.
pub open spec fn int_cross() -> super::super::parsed::spec::PathCert {
    super::super::examples::ca(31, super::super::examples::in3_name(), super::super::examples::int_name(),
        super::super::examples::key(2), super::super::examples::key(4))
}

/// `int` issued by `in2`, and `in2` issued by `int`: a loop with no anchor.
pub open spec fn loop_a() -> super::super::parsed::spec::PathCert {
    super::super::examples::ca(32, super::super::examples::in2_name(), super::super::examples::int_name(),
        super::super::examples::key(2), super::super::examples::key(3))
}

/// The other half of the loop.
pub open spec fn loop_b() -> super::super::parsed::spec::PathCert {
    super::super::examples::ca(33, super::super::examples::int_name(), super::super::examples::in2_name(),
        super::super::examples::key(3), super::super::examples::key(2))
}

/// Anchors before intermediates (RFC 4158 §3.5.15): with the root's copy
/// sent first, the anchor is examined for `int` before the copy is, so the
/// short path `anchor -> int` is found, not `anchor -> copy -> int`.
pub proof fn lemma_anchor_before_root_copy()
    ensures run(6, pool(seq![root_copy(), super::super::examples::int()]), super::super::examples::leaf(), 200000)
        == accepted(seq![1nat]),
{
    assert(run(6, pool(seq![root_copy(), super::super::examples::int()]), super::super::examples::leaf(), 200000)
        == accepted(seq![1nat])) by (compute_only);
}

/// A cross-signed choice: the cross-sign, sent first, leads to no anchor; the
/// search backtracks to the anchored `int`.
pub proof fn lemma_cross_signed()
    ensures run(6, pool(seq![int_cross(), super::super::examples::int()]), super::super::examples::leaf(), 200000)
        == accepted(seq![1nat]),
{
    assert(run(6, pool(seq![int_cross(), super::super::examples::int()]), super::super::examples::leaf(), 200000)
        == accepted(seq![1nat])) by (compute_only);
}

/// A loop terminates: two steps (the second cannot take the first again),
/// no candidate, `UnknownIssuer`; with a budget of exactly two steps, the
/// budget is not exhausted.
pub proof fn lemma_loop()
    ensures
        order(6, pool(seq![loop_a(), loop_b()]), super::super::examples::leaf()).len() == 2,
        run(6, pool(seq![loop_a(), loop_b()]), super::super::examples::leaf(), 2)
            == refused(super::super::spec::PathError::UnknownIssuer),
{
    assert(order(6, pool(seq![loop_a(), loop_b()]), super::super::examples::leaf()).len() == 2) by (compute_only);
    assert(run(6, pool(seq![loop_a(), loop_b()]), super::super::examples::leaf(), 2)
        == refused(super::super::spec::PathError::UnknownIssuer)) by (compute_only);
}

/// Depth: `anchor -> int -> in2 -> leaf` has two intermediates, found with
/// `max_intermediates` 2 and not with 1.
pub proof fn lemma_depth()
    ensures
        run(2, pool(seq![super::super::examples::int(), super::super::examples::in2()]),
            super::super::examples::leaf_under_in2(), 200000) == accepted(seq![0nat, 1]),
        run(1, pool(seq![super::super::examples::int(), super::super::examples::in2()]),
            super::super::examples::leaf_under_in2(), 200000) == refused(super::super::spec::PathError::UnknownIssuer),
{
    assert(run(2, pool(seq![super::super::examples::int(), super::super::examples::in2()]),
        super::super::examples::leaf_under_in2(), 200000) == accepted(seq![0nat, 1])) by (compute_only);
    assert(run(1, pool(seq![super::super::examples::int(), super::super::examples::in2()]),
        super::super::examples::leaf_under_in2(), 200000) == refused(super::super::spec::PathError::UnknownIssuer))
        by (compute_only);
}

/// The pool `[int_self, int]` under `leaf()`.
pub open spec fn reissued() -> Seq<Option<super::super::parsed::spec::PathCert>> {
    pool(seq![super::super::examples::int_self(), super::super::examples::int()])
}

/// First valid, depth first, in message order: the re-issued `int` comes
/// first, so the first valid candidate is `anchor -> int -> int_self`
/// (the third step), although `anchor -> int` is also valid and shorter.
/// Three steps are examined. A budget of two steps runs out first.
pub proof fn lemma_first_valid_order()
    ensures
        run(6, reissued(), super::super::examples::leaf(), 200000) == accepted(seq![1nat, 0]),
        reissued_count() == 3,
        run(6, reissued(), super::super::examples::leaf(), 3) == accepted(seq![1nat, 0]),
        run(6, reissued(), super::super::examples::leaf(), 2) == refused(super::super::spec::PathError::BuildBudgetExhausted),
{
    assert(run(6, reissued(), super::super::examples::leaf(), 200000) == accepted(seq![1nat, 0])) by (compute_only);
    assert(reissued_count() == 3) by (compute_only);
    assert(run(6, reissued(), super::super::examples::leaf(), 3) == accepted(seq![1nat, 0])) by (compute_only);
    assert(run(6, reissued(), super::super::examples::leaf(), 2)
        == refused(super::super::spec::PathError::BuildBudgetExhausted)) by (compute_only);
}

/// The search over `pool(seq![int()])` under `leaf()` with every signature failing.
pub open spec fn failing() -> Result<super::super::verifier::Validated, super::super::spec::PathError> {
    search(super::super::verifier::Environment { link: super::super::examples::no_link(),
            revoked: super::super::examples::not_revoked(), max_intermediates: 6 },
        seq![super::super::examples::anchor()], pool(seq![super::super::examples::int()]),
        super::super::examples::leaf(), super::super::examples::reference(), super::super::examples::now(), 200000)
}

/// The steps examined over `reissued()`.
pub open spec fn reissued_count() -> nat {
    examined_count(super::super::examples::environment(6), seq![super::super::examples::anchor()], reissued(),
        super::super::examples::leaf(), super::super::examples::reference(), super::super::examples::now(), 200000)
}

/// The error when no candidate is valid is the first candidate's: every
/// signature failing, `BadSignature`.
pub proof fn lemma_first_error()
    ensures failing() == refused(super::super::spec::PathError::BadSignature),
{
    assert(failing() == refused(super::super::spec::PathError::BadSignature)) by (compute_only);
}

} // verus!
