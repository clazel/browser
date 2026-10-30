//! The executable search (design §2.6), proven to meet `contract.rs`: it
//! returns exactly `spec::search`, and the steps it examines are exactly
//! `spec::examined_steps`, a prefix of `spec::search_order`.
//!
//! - **Shape.** A recursive function per node (`search_node`), whose depth
//!   is at most `max_intermediates` + 1, and at each node two loops: the
//!   anchors, then the pool. Recursion `decreases` the depth still
//!   available; each loop `decreases` the issuers still to examine. The
//!   number of pool certificates is not capped, so a node's issuers are a
//!   loop, not recursion.
//! - **Invariant.** At a node `path`, the steps examined so far at this node
//!   (`done`, a ghost sequence) satisfy
//!   `steps_from(path, 0) == done + steps_from(path, i)`; none of them
//!   completes a valid candidate; `examined` has grown by `done.len()`; and
//!   the first candidate error is that of `done`, if any. The steps are
//!   recorded in a ghost trace as they are examined.
//! - **The budget** is checked before each step, as mozilla::pkix checks
//!   `buildForwardCallBudget` in `PathBuildingStep::Check`.
//! - **Work per node.** Every candidate issuer is compared by name; at full
//!   depth the pool is not scanned (no pool step can be name-chained there,
//!   `lemmas::lemma_no_pool_steps`). Candidates go to P8's
//!   `exec::candidate_verdict`, so signatures are verified only for
//!   complete name-chained candidates, from the anchor down, until one
//!   fails.

use super::super::contract::{LinkVerifier, RevocationOracle};
use super::super::exec::{
    Candidate, Environment, bytes_equal, candidate_verdict, chain_inputs, index_absent_from,
};
use super::super::parsed::exec::{Anchor, PathCert};
use super::super::spec::PathError;
use crate::exec::ReferenceIdentity;
use crate::time::exec::CertificateTime;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// An accepted chain (`verifier::Validated`).
pub struct Validated {
    /// Index of the anchor the path reaches.
    pub anchor: usize,
    /// The pool indices of the intermediates, the anchor's child first.
    pub path: Vec<usize>,
    /// The target's complete SubjectPublicKeyInfo DER.
    pub leaf_spki: Vec<u8>,
}

/// The spec value of an accepted chain.
pub open spec fn view_validated(v: &Validated) -> super::super::verifier::Validated {
    super::super::verifier::Validated { anchor: v.anchor as nat, path: super::super::exec::view_indices(v.path@), leaf_spki: v.leaf_spki@ }
}

/// The spec value of a result.
pub open spec fn view_result(out: Result<Validated, PathError>) -> Result<super::super::verifier::Validated, PathError> {
    match out {
        Ok(v) => Ok(view_validated(&v)),
        Err(e) => Err(e),
    }
}

/// What a node's search ended with.
enum Node {
    /// The first valid candidate.
    Found(Validated),
    /// The budget ran out.
    Exhausted,
    /// Every step of the node was examined, none valid.
    Done,
}

/// The steps at the node `path`.
spec fn segment(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    path: Seq<nat>,
) -> Seq<super::super::verifier::IssuerStep> {
    super::spec::steps_from(environment, anchors, pool, leaf, path, 0)
}

/// What one node's search ensures, `seg` being its steps, `n` the steps it
/// examined and `trace` those steps as recorded.
spec fn node_ensures(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime, budget: nat,
    seg: Seq<super::super::verifier::IssuerStep>, before: nat, after: nat,
    error_before: Option<PathError>, error_after: Option<PathError>,
    out: Node, trace: Seq<super::super::verifier::IssuerStep>,
) -> bool {
    &&& before <= after <= budget
    &&& after - before <= seg.len()
    &&& trace == seg.take(after - before)
    &&& match out {
        Node::Found(v) => {
            &&& after - before >= 1
            &&& seg[after - before - 1] == super::theorems::completing_step(
                super::super::verifier::Candidate { anchor: v.anchor as nat, path: super::super::exec::view_indices(v.path@) })
            &&& super::super::verifier::candidate_verdict(environment, anchors, pool, leaf,
                super::super::verifier::Candidate { anchor: v.anchor as nat, path: super::super::exec::view_indices(v.path@) }, reference, now)
                == Ok::<Seq<u8>, PathError>(v.leaf_spki@)
            &&& super::lemmas::none_valid(environment, anchors, pool, leaf, seg.take(after - before - 1), reference, now)
        },
        Node::Exhausted => {
            &&& after == budget
            &&& seg.len() > after - before
            &&& super::lemmas::none_valid(environment, anchors, pool, leaf, seg.take(after - before), reference, now)
        },
        Node::Done => {
            &&& after - before == seg.len()
            &&& super::lemmas::none_valid(environment, anchors, pool, leaf, seg, reference, now)
            &&& error_after == super::lemmas::then_error(error_before,
                super::spec::first_candidate_error(environment, anchors, pool, leaf, seg, 0, reference, now))
        },
    }
}

/// The loop invariant's step: `done` grows by the steps `piece` examined at
/// issuer `i`, none valid.
proof fn lemma_grow(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
    done: Seq<super::super::verifier::IssuerStep>, piece: Seq<super::super::verifier::IssuerStep>,
    error: Option<PathError>, piece_error: Option<PathError>,
)
    requires
        super::lemmas::none_valid(environment, anchors, pool, leaf, done, reference, now),
        super::lemmas::none_valid(environment, anchors, pool, leaf, piece, reference, now),
        piece_error == super::spec::first_candidate_error(environment, anchors, pool, leaf, piece, 0, reference, now),
    ensures
        super::lemmas::none_valid(environment, anchors, pool, leaf, done + piece, reference, now),
        super::lemmas::then_error(error, super::lemmas::then_error(
            super::spec::first_candidate_error(environment, anchors, pool, leaf, done, 0, reference, now), piece_error))
        == super::lemmas::then_error(error,
            super::spec::first_candidate_error(environment, anchors, pool, leaf, done + piece, 0, reference, now)),
{
    hide(super::super::verifier::candidate_verdict);
    super::lemmas::lemma_first_error_concat(environment, anchors, pool, leaf, done, piece, reference, now);
    let all = done + piece;
    assert forall|k: int| 0 <= k < all.len() implies
        !super::spec::step_valid(environment, anchors, pool, leaf, #[trigger] all[k], reference, now) by {
        if k < done.len() { assert(all[k] == done[k]); } else { assert(all[k] == piece[k - done.len()]); }
    }
}

/// Copy a path.
fn copy_indices(path: &[usize]) -> (out: Vec<usize>)
    ensures out@ == path@,
{
    let mut out: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < path.len()
        invariant k <= path.len(), out@ == path@.take(k as int),
        decreases path.len() - k
    {
        let Some(x) = path.get(k) else { return out; };
        out.push(*x);
        proof { assert(out@ =~= path@.take(k as int + 1)); }
        k = k.saturating_add(1);
    }
    proof { assert(path@.take(path.len() as int) =~= path@); }
    out
}

/// Copy bytes.
fn copy_bytes(bytes: &[u8]) -> (out: Vec<u8>)
    ensures out@ == bytes@,
{
    let mut out: Vec<u8> = Vec::new();
    let mut k: usize = 0;
    while k < bytes.len()
        invariant k <= bytes.len(), out@ == bytes@.take(k as int),
        decreases bytes.len() - k
    {
        let Some(x) = bytes.get(k) else { return out; };
        out.push(*x);
        proof { assert(out@ =~= bytes@.take(k as int + 1)); }
        k = k.saturating_add(1);
    }
    proof { assert(bytes@.take(bytes.len() as int) =~= bytes@); }
    out
}

/// `seq![j] + path`, executable.
fn push_top(j: usize, path: &[usize]) -> (out: Vec<usize>)
    ensures super::super::exec::view_indices(out@) == seq![j as nat] + super::super::exec::view_indices(path@), out.len() == path.len() + 1,
{
    let mut out: Vec<usize> = Vec::new();
    out.push(j);
    let mut k: usize = 0;
    while k < path.len()
        invariant k <= path.len(), out@ == seq![j] + path@.take(k as int),
        decreases path.len() - k
    {
        let Some(x) = path.get(k) else { return out; };
        out.push(*x);
        proof { assert(out@ =~= seq![j] + path@.take(k as int + 1)); }
        k = k.saturating_add(1);
    }
    proof {
        assert(path@.take(path.len() as int) =~= path@);
        assert(super::super::exec::view_indices(out@) =~= seq![j as nat] + super::super::exec::view_indices(path@));
    }
    out
}

/// The issuer name sought above `path` (`verifier::sought_issuer`).
fn sought<'a>(pool: &'a [Option<PathCert<'a>>], leaf: &'a PathCert<'a>, path: &[usize]) -> (out: &'a [u8])
    requires super::super::verifier::indices_usable_from(super::super::exec::view_pool(pool@), super::super::exec::view_indices(path@), 0),
    ensures out@ == super::super::verifier::sought_issuer(super::super::exec::view_pool(pool@),
        super::super::parsed::exec::view_path_cert(leaf), super::super::exec::view_indices(path@)),
{
    match path.first() {
        None => leaf.tbs.issuer_der,
        Some(top) => {
            proof { super::lemmas::lemma_usable_iff(super::super::exec::view_pool(pool@), super::super::exec::view_indices(path@), 0); }
            match pool.get(*top) {
                Some(Some(cert)) => cert.tbs.issuer_der,
                _ => leaf.tbs.issuer_der,
            }
        },
    }
}

/// The inputs every node of one search shares.
struct Context<'a, 'b, L: LinkVerifier, R: RevocationOracle> {
    environment: &'b Environment<'b, L, R>,
    anchors: &'a [Anchor<'a>],
    pool: &'a [Option<PathCert<'a>>],
    leaf: &'a PathCert<'a>,
    reference: ReferenceIdentity<'b>,
    now: &'b CertificateTime,
    budget: usize,
}

/// The search at the node `path`, from its first candidate issuer.
fn search_node<'a, 'b, L: LinkVerifier, R: RevocationOracle>(
    context: &Context<'a, 'b, L, R>, path: &[usize], examined_in: usize, error_in: Option<PathError>,
) -> (out: (Node, usize, Option<PathError>, Ghost<Seq<super::super::verifier::IssuerStep>>))
    requires
        path.len() <= context.environment.max_intermediates,
        super::super::verifier::indices_usable_from(super::super::exec::view_pool(context.pool@), super::super::exec::view_indices(path@), 0),
        super::super::verifier::indices_distinct_from(super::super::exec::view_indices(path@), 0),
        examined_in <= context.budget,
    ensures node_ensures(super::super::exec::view_environment(context.environment), super::super::exec::view_anchors(context.anchors@), super::super::exec::view_pool(context.pool@),
        super::super::parsed::exec::view_path_cert(context.leaf), crate::exec::view_reference_identity(&context.reference), context.now@,
        context.budget as nat,
        segment(super::super::exec::view_environment(context.environment), super::super::exec::view_anchors(context.anchors@), super::super::exec::view_pool(context.pool@),
            super::super::parsed::exec::view_path_cert(context.leaf), super::super::exec::view_indices(path@)),
        examined_in as nat, out.1 as nat, error_in, out.2, out.0, out.3@),
    decreases context.environment.max_intermediates - path.len(),
{
    hide(super::super::verifier::candidate_verdict);
    hide(super::spec::steps_from);
    let environment = context.environment;
    let anchors = context.anchors;
    let pool = context.pool;
    let leaf = context.leaf;
    let reference = context.reference;
    let now = context.now;
    let budget = context.budget;
    let ghost e = super::super::exec::view_environment(environment);
    let ghost sa = super::super::exec::view_anchors(anchors@);
    let ghost sp = super::super::exec::view_pool(pool@);
    let ghost sl = super::super::parsed::exec::view_path_cert(leaf);
    let ghost sr = crate::exec::view_reference_identity(&reference);
    let ghost sn = now@;
    let ghost vpath = super::super::exec::view_indices(path@);
    let ghost seg = segment(e, sa, sp, sl, vpath);
    let mut examined = examined_in;
    let mut first_error = error_in;
    let ghost before = examined as nat;
    let ghost error_before = first_error;
    let ghost mut done: Seq<super::super::verifier::IssuerStep> = seq![];
    proof {
        assert(seg == done + super::spec::steps_from(e, sa, sp, sl, vpath, 0));
        assert(sa.len() == anchors.len() && sp.len() == pool.len() && vpath.len() == path.len());
        assert(super::spec::first_candidate_error(e, sa, sp, sl, done, 0, sr, sn) is None);
        assert(first_error == super::lemmas::then_error(error_before,
            super::spec::first_candidate_error(e, sa, sp, sl, done, 0, sr, sn)));
    }
    let name = sought(pool, leaf, path);
    // 1. The anchors, in table order.
    let mut a: usize = 0;
    while a < anchors.len()
        invariant
            e == super::super::exec::view_environment(environment), sa == super::super::exec::view_anchors(anchors@), sp == super::super::exec::view_pool(pool@),
            sl == super::super::parsed::exec::view_path_cert(leaf), sr == crate::exec::view_reference_identity(&reference),
            sn == now@, vpath == super::super::exec::view_indices(path@), sa.len() == anchors.len(), sp.len() == pool.len(),
            vpath.len() == path.len(), path.len() <= environment.max_intermediates,
            super::super::verifier::indices_usable_from(sp, vpath, 0),
            super::super::verifier::indices_distinct_from(vpath, 0),
            name@ == super::super::verifier::sought_issuer(sp, sl, vpath),
            seg == segment(e, sa, sp, sl, vpath),
            a <= anchors.len(),
            seg == done + super::spec::steps_from(e, sa, sp, sl, vpath, a as nat),
            before == examined_in as nat, error_before == error_in,
            environment == context.environment, anchors == context.anchors, pool == context.pool,
            leaf == context.leaf, reference == context.reference, now == context.now, budget == context.budget,
            before <= examined <= budget, examined == before + done.len(),
            super::lemmas::none_valid(e, sa, sp, sl, done, sr, sn),
            first_error == super::lemmas::then_error(error_before,
                super::spec::first_candidate_error(e, sa, sp, sl, done, 0, sr, sn)),
        decreases anchors.len() - a
    {
        let ghost step = super::super::verifier::IssuerStep { path: vpath, issuer: super::spec::issuer_at(sa, a as nat) };
        proof {
            super::lemmas::lemma_unfold(e, sa, sp, sl, vpath, a as nat);
            assert(super::spec::issuer_at(sa, a as nat) == super::super::verifier::Issuer::Anchor(a as nat));
        }
        let Some(anchor) = anchors.get(a) else { return (Node::Done, examined, first_error, Ghost(done)); };
        proof { assert(sa[a as int] == super::super::parsed::exec::view_anchor(anchor)); }
        let chained = bytes_equal(anchor.subject_der, name);
        let ghost piece = super::lemmas::steps_at(e, sa, sp, sl, vpath, a as nat);
        proof {
            assert(chained == super::super::verifier::step_name_chained(e, sa, sp, sl, step));
        }
        if chained {
            proof { assert(piece == seq![step]); }
            if examined >= budget {
                proof {
                    assert(seg.take(examined - before) =~= done);
                    assert(seg[done.len() as int] == step);

                }
                return (Node::Exhausted, examined, first_error, Ghost(done));
            }
            examined = examined.saturating_add(1);
            let ghost trace = done.push(step);
            let candidate = Candidate { anchor: a, path };
            let verdict = candidate_verdict(environment, anchors, pool, leaf, &candidate, reference, now);
            match verdict {
                Ok(key) => {
                    let found = Validated { anchor: a, path: copy_indices(path), leaf_spki: copy_bytes(key) };
                    proof {
                        assert(super::super::exec::view_indices(found.path@) == vpath);
                        assert(seg.take(examined - before) =~= trace);
                        assert(seg[done.len() as int] == step);
                        assert(seg.take(examined - before - 1) =~= done);
                    }
                    return (Node::Found(found), examined, first_error, Ghost(trace));
                },
                Err(err) => {
                    proof {
                        super::lemmas::lemma_first_error_one(e, sa, sp, sl, step, sr, sn);
                        assert(!super::spec::step_valid(e, sa, sp, sl, step, sr, sn));
                        assert(super::lemmas::none_valid(e, sa, sp, sl, piece, sr, sn));
                        lemma_grow(e, sa, sp, sl, sr, sn, done, piece, error_before,
                            super::spec::first_candidate_error(e, sa, sp, sl, piece, 0, sr, sn));
                    }
                    let ghost error_old = first_error;
                    if first_error.is_none() { first_error = Some(err); }
                    proof {
                        assert(super::spec::first_candidate_error(e, sa, sp, sl, piece, 0, sr, sn) == Some(err));
                        assert(first_error == super::lemmas::then_error(error_old, Some(err)));
                        assert(done + piece =~= trace);
                        assert(seg == trace + super::spec::steps_from(e, sa, sp, sl, vpath, a as nat + 1));
                        done = trace;
                    }
                },
            }
        } else {
            proof {
                assert(piece == Seq::<super::super::verifier::IssuerStep>::empty());
                assert(done + piece =~= done);
                assert(seg == done + super::spec::steps_from(e, sa, sp, sl, vpath, a as nat + 1));
            }
        }
        a = a.saturating_add(1);
    }
    // 2. The pool certificates, in message order, unless the path is at full
    //    depth (then none is a step).
    if path.len() >= environment.max_intermediates {
        proof {
            super::lemmas::lemma_no_pool_steps(e, sa, sp, sl, vpath, sa.len());
            assert(seg =~= done);
            assert(seg.take(examined - before) =~= done);
        }
        return (Node::Done, examined, first_error, Ghost(done));
    }
    let mut j: usize = 0;
    while j < pool.len()
        invariant
            e == super::super::exec::view_environment(environment), sa == super::super::exec::view_anchors(anchors@), sp == super::super::exec::view_pool(pool@),
            sl == super::super::parsed::exec::view_path_cert(leaf), sr == crate::exec::view_reference_identity(&reference),
            sn == now@, vpath == super::super::exec::view_indices(path@), sa.len() == anchors.len(), sp.len() == pool.len(),
            vpath.len() == path.len(), path.len() < environment.max_intermediates,
            super::super::verifier::indices_usable_from(sp, vpath, 0),
            super::super::verifier::indices_distinct_from(vpath, 0),
            name@ == super::super::verifier::sought_issuer(sp, sl, vpath),
            seg == segment(e, sa, sp, sl, vpath),
            j <= pool.len(),
            seg == done + super::spec::steps_from(e, sa, sp, sl, vpath, (sa.len() + j) as nat),
            before == examined_in as nat, error_before == error_in,
            environment == context.environment, anchors == context.anchors, pool == context.pool,
            leaf == context.leaf, reference == context.reference, now == context.now, budget == context.budget,
            before <= examined <= budget, examined == before + done.len(),
            super::lemmas::none_valid(e, sa, sp, sl, done, sr, sn),
            first_error == super::lemmas::then_error(error_before,
                super::spec::first_candidate_error(e, sa, sp, sl, done, 0, sr, sn)),
        decreases pool.len() - j
    {
        let ghost i = (sa.len() + j) as nat;
        let ghost step = super::super::verifier::IssuerStep { path: vpath, issuer: super::spec::issuer_at(sa, i) };
        let ghost piece = super::lemmas::steps_at(e, sa, sp, sl, vpath, i);
        proof {
            super::lemmas::lemma_unfold(e, sa, sp, sl, vpath, i);
            assert(super::spec::issuer_at(sa, i) == super::super::verifier::Issuer::Pool(j as nat));
            assert(sp[j as int] == super::super::parsed::exec::view_path_cert_result(pool@[j as int]));
            super::lemmas::lemma_absent_iff(vpath, j as nat, 0);
        }
        let absent = index_absent_from(path, j, 0);
        let chained = absent && match pool.get(j) {
            Some(Some(cert)) => bytes_equal(cert.tbs.subject_der, name),
            _ => false,
        };
        proof {
            assert(chained == super::super::verifier::step_name_chained(e, sa, sp, sl, step));
        }
        if chained {
            if examined >= budget {
                proof {
                    assert(seg.take(examined - before) =~= done);
                    assert(seg[done.len() as int] == step);
                }
                return (Node::Exhausted, examined, first_error, Ghost(done));
            }
            examined = examined.saturating_add(1);
            let ghost head = done.push(step);
            let child = push_top(j, path);
            let ghost vchild = super::super::exec::view_indices(child@);
            let ghost inner = super::spec::steps_from(e, sa, sp, sl, vchild, 0);
            proof {
                assert(vchild == seq![j as nat] + vpath);
                assert(piece == seq![step] + inner);
                super::lemmas::lemma_usable_iff(sp, vpath, 0);
                super::lemmas::lemma_usable_iff(sp, vchild, 0);
                super::lemmas::lemma_distinct_iff(vpath, 0);
                super::lemmas::lemma_distinct_iff(vchild, 0);
                assert forall|k: int| 0 <= k < vchild.len() implies vchild[k] < sp.len()
                    && (#[trigger] sp[vchild[k] as int]) is Some by {
                    if k > 0 { assert(vchild[k] == vpath[k - 1]); }
                }
                assert forall|k1: int, k2: int| 0 <= k1 < k2 < vchild.len() implies vchild[k1] != vchild[k2] by {
                    if k1 > 0 { assert(vchild[k1] == vpath[k1 - 1]); }
                    assert(vchild[k2] == vpath[k2 - 1]);
                }
            }
            let ghost error_mid = first_error;
            let ghost examined_mid = examined as nat;
            let (result, examined_out, error_out, Ghost(below)) = search_node(context, child.as_slice(),
                examined, first_error);
            examined = examined_out;
            first_error = error_out;
            proof {
                assert(seg == head + inner + super::spec::steps_from(e, sa, sp, sl, vpath, i + 1));
            }
            match result {
                Node::Found(found) => {
                    let ghost trace = head + below;
                    proof {
                        let n_in = (examined - examined_mid) as int;
                        assert(seg.take(examined - before) =~= trace);
                        assert(seg[examined - before - 1] == inner[n_in - 1]);
                        assert(seg.take(examined - before - 1) =~= head + inner.take(n_in - 1));
                        assert(!super::spec::step_valid(e, sa, sp, sl, step, sr, sn));
                        super::lemmas::lemma_first_error_one(e, sa, sp, sl, step, sr, sn);
                        assert(super::lemmas::none_valid(e, sa, sp, sl, seq![step], sr, sn));
                        lemma_grow(e, sa, sp, sl, sr, sn, done, seq![step], error_before, None);
                        assert(head =~= done + seq![step]);
                        lemma_grow(e, sa, sp, sl, sr, sn, head, inner.take(n_in - 1), error_before,
                            super::spec::first_candidate_error(e, sa, sp, sl, inner.take(n_in - 1), 0, sr, sn));
                    }
                    return (Node::Found(found), examined, first_error, Ghost(trace));
                },
                Node::Exhausted => {
                    let ghost trace = head + below;
                    proof {
                        let n_in = (examined - examined_mid) as int;
                        assert(seg.take(examined - before) =~= trace);
                        assert(!super::spec::step_valid(e, sa, sp, sl, step, sr, sn));
                        super::lemmas::lemma_first_error_one(e, sa, sp, sl, step, sr, sn);
                        assert(super::lemmas::none_valid(e, sa, sp, sl, seq![step], sr, sn));
                        lemma_grow(e, sa, sp, sl, sr, sn, done, seq![step], error_before, None);
                        assert(head =~= done + seq![step]);
                        lemma_grow(e, sa, sp, sl, sr, sn, head, inner.take(n_in), error_before,
                            super::spec::first_candidate_error(e, sa, sp, sl, inner.take(n_in), 0, sr, sn));
                    }
                    return (Node::Exhausted, examined, first_error, Ghost(trace));
                },
                Node::Done => {
                    proof {
                        assert(below =~= inner);
                        assert(!super::spec::step_valid(e, sa, sp, sl, step, sr, sn));
                        super::lemmas::lemma_first_error_one(e, sa, sp, sl, step, sr, sn);
                        super::lemmas::lemma_first_error_concat(e, sa, sp, sl, seq![step], inner, sr, sn);
                        assert(super::lemmas::none_valid(e, sa, sp, sl, piece, sr, sn)) by {
                            assert forall|k: int| 0 <= k < piece.len() implies
                                !super::spec::step_valid(e, sa, sp, sl, #[trigger] piece[k], sr, sn) by {
                                if k > 0 { assert(piece[k] == inner[k - 1]); }
                            }
                        }
                        lemma_grow(e, sa, sp, sl, sr, sn, done, piece, error_before,
                            super::spec::first_candidate_error(e, sa, sp, sl, piece, 0, sr, sn));
                        assert(first_error == super::lemmas::then_error(error_mid,
                            super::spec::first_candidate_error(e, sa, sp, sl, inner, 0, sr, sn)));
                        assert(head + inner =~= done + piece);
                        done = done + piece;
                    }
                },
            }
        } else {
            proof {
                assert(piece == Seq::<super::super::verifier::IssuerStep>::empty());
                assert(done + piece =~= done);
            }
        }
        j = j.saturating_add(1);
    }
    proof {
        super::lemmas::lemma_unfold(e, sa, sp, sl, vpath, (sa.len() + pool.len()) as nat);
        assert(seg =~= done);
        assert(seg.take(examined - before) =~= done);
    }
    (Node::Done, examined, first_error, Ghost(done))
}

/// `spec::search`, with the steps examined: `contract::search_ensures`.
fn search_traced<'a, L: LinkVerifier, R: RevocationOracle>(
    environment: &Environment<'_, L, R>, anchors: &'a [Anchor<'a>], pool: &'a [Option<PathCert<'a>>],
    leaf: &'a PathCert<'a>, reference: ReferenceIdentity<'_>, now: &CertificateTime, budget: usize,
) -> (out: (Result<Validated, PathError>, Ghost<Seq<super::super::verifier::IssuerStep>>))
    ensures super::contract::search_ensures(super::super::exec::view_environment(environment), super::super::exec::view_anchors(anchors@), super::super::exec::view_pool(pool@),
        super::super::parsed::exec::view_path_cert(leaf), crate::exec::view_reference_identity(&reference), now@,
        budget as nat, view_result(out.0), out.1@),
{
    hide(super::super::verifier::candidate_verdict);
    hide(super::spec::steps_from);
    let ghost e = super::super::exec::view_environment(environment);
    let ghost sa = super::super::exec::view_anchors(anchors@);
    let ghost sp = super::super::exec::view_pool(pool@);
    let ghost sl = super::super::parsed::exec::view_path_cert(leaf);
    let ghost sr = crate::exec::view_reference_identity(&reference);
    let ghost sn = now@;
    let ghost order = super::spec::search_order(e, sa, sp, sl);
    let root: Vec<usize> = Vec::new();
    proof {
        assert(super::super::exec::view_indices(root@) =~= Seq::<nat>::empty());
    }
    let context = Context { environment, anchors, pool, leaf, reference, now, budget };
    let (node, _examined, first_error, Ghost(trace)) = search_node(&context, root.as_slice(), 0, None);
    proof { assert(segment(e, sa, sp, sl, super::super::exec::view_indices(root@)) == order); }
    match node {
        Node::Found(v) => {
            proof {
                let k = _examined as int - 1;
                assert forall|k2: int| 0 <= k2 < k implies
                    !super::spec::step_valid(e, sa, sp, sl, #[trigger] order[k2], sr, sn) by {
                    assert(order.take(k)[k2] == order[k2]);
                }
                let candidate = super::super::verifier::Candidate { anchor: v.anchor as nat, path: super::super::exec::view_indices(v.path@) };
                assert(super::super::verifier::step_candidate(order[k]) == Some(candidate));
                assert(super::spec::step_valid(e, sa, sp, sl, order[k], sr, sn));
                super::lemmas::lemma_first_valid_at(e, sa, sp, sl, order, k, budget as int, sr, sn);
            }
            (Ok(v), Ghost(trace))
        },
        Node::Exhausted => {
            proof {
                assert forall|k2: int| 0 <= k2 < budget && k2 < order.len() implies
                    !super::spec::step_valid(e, sa, sp, sl, #[trigger] order[k2], sr, sn) by {
                    assert(order.take(budget as int)[k2] == order[k2]);
                }
                super::lemmas::lemma_first_valid_none(e, sa, sp, sl, order, budget as int, sr, sn);
            }
            (Err(PathError::BuildBudgetExhausted), Ghost(trace))
        },
        Node::Done => {
            proof {
                super::lemmas::lemma_first_valid_none(e, sa, sp, sl, order, budget as int, sr, sn);
                assert(order.take(order.len() as int) =~= order);
            }
            match first_error {
                Some(err) => (Err(err), Ghost(trace)),
                None => (Err(PathError::UnknownIssuer), Ghost(trace)),
            }
        },
    }
}

/// `spec::search` on a leaf and pool, with at most `budget` steps.
pub fn search<'a, L: LinkVerifier, R: RevocationOracle>(
    environment: &Environment<'_, L, R>, anchors: &'a [Anchor<'a>], pool: &'a [Option<PathCert<'a>>],
    leaf: &'a PathCert<'a>, reference: ReferenceIdentity<'_>, now: &CertificateTime, budget: usize,
) -> (out: Result<Validated, PathError>)
    ensures view_result(out) == super::spec::search(super::super::exec::view_environment(environment), super::super::exec::view_anchors(anchors@),
        super::super::exec::view_pool(pool@), super::super::parsed::exec::view_path_cert(leaf),
        crate::exec::view_reference_identity(&reference), now@, budget as nat),
{
    let (out, Ghost(_examined)) = search_traced(environment, anchors, pool, leaf, reference, now, budget);
    out
}

/// The verdict on a presented TLS server chain (`presented[0]` the server's
/// certificate, the rest a pool in message order) against `anchors` at Unix
/// time `now`: `contract::verify_server_chain_ensures`, which includes P7's
/// `verifier::verify_server_chain_ensures`.
pub fn verify_server_chain<L: LinkVerifier, R: RevocationOracle>(
    environment: &Environment<'_, L, R>, anchors: &[Anchor<'_>], presented: &[&[u8]],
    reference: ReferenceIdentity<'_>, now: u64,
) -> (out: Result<Validated, PathError>)
    ensures super::contract::verify_server_chain_ensures(super::super::exec::view_environment(environment), super::super::exec::view_anchors(anchors@),
        super::super::exec::view_presented(presented@), crate::exec::view_reference_identity(&reference), now,
        view_result(out)),
{
    hide(super::super::verifier::candidate_verdict);
    hide(super::spec::steps_from);
    hide(super::super::parsed::spec::parse_path_cert);
    proof {
        super::lemmas::lemma_meets_verifier_contract(super::super::exec::view_environment(environment), super::super::exec::view_anchors(anchors@),
            super::super::exec::view_presented(presented@), crate::exec::view_reference_identity(&reference), now);
    }
    let inputs = chain_inputs(presented, now)?;
    // Design §1.12: mozilla::pkix `buildForwardCallBudget`.
    let budget: usize = 200000;
    proof { assert(super::super::verifier::build_budget() == budget as nat); }
    search(environment, anchors, inputs.pool.as_slice(), &inputs.leaf, reference, &inputs.now, budget)
}

} // verus!
