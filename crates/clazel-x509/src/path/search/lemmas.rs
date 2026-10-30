//! Proofs of the search's theorems (`theorems.rs`), and the facts about
//! `spec.rs` the executable search's proof uses.
//!
//! - **The shape of the order.** `lemma_steps_from`: every step of
//!   `steps_from(path, i)` is name-chained, extends `path`, has rank at
//!   least `i` (its issuer's position at the node `path`, or the position of
//!   the pool certificate it was found under), and no step occurs twice.
//!   `lemma_order_well_formed` reads P7's `search_order_well_formed_from`
//!   off it.
//! - **Completeness.** `lemma_contains_step` and `lemma_contains_node`: a
//!   name-chained step at a node is in that node's steps, and so are the
//!   steps of the node it pushes. `lemma_candidates_complete` walks a
//!   candidate's path from the leaf to the anchor.
//! - **First valid.** `lemma_thm_first_valid` from completeness, the
//!   definition of `search`, and `lemma_verdict_not_budget` (no candidate's
//!   verdict is `BuildBudgetExhausted`); `lemma_meets_verifier_contract` for
//!   the presented chain.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// P7's index predicates, quantified
// ---------------------------------------------------------------------------

/// `verifier::index_absent_from`, quantified.
pub proof fn lemma_absent_iff(path: Seq<nat>, index: nat, from: int)
    requires 0 <= from,
    ensures super::super::verifier::index_absent_from(path, index, from)
        <==> (forall|k: int| from <= k < path.len() ==> path[k] != index),
    decreases path.len() - from,
{
    if from < path.len() { lemma_absent_iff(path, index, from + 1); }
}

/// `verifier::indices_distinct_from`, quantified.
pub proof fn lemma_distinct_iff(path: Seq<nat>, from: int)
    requires 0 <= from,
    ensures super::super::verifier::indices_distinct_from(path, from)
        <==> (forall|k1: int, k2: int| from <= k1 < k2 < path.len() ==> path[k1] != path[k2]),
    decreases path.len() - from,
{
    if from < path.len() {
        lemma_distinct_iff(path, from + 1);
        lemma_absent_iff(path, path[from], from + 1);
        if super::super::verifier::indices_distinct_from(path, from) {
            assert forall|k1: int, k2: int| from <= k1 < k2 < path.len() implies path[k1] != path[k2] by {
                if k1 > from { assert(from + 1 <= k1 < k2 < path.len()); }
            }
        }
        if forall|k1: int, k2: int| from <= k1 < k2 < path.len() ==> path[k1] != path[k2] {
            assert forall|k: int| from + 1 <= k < path.len() implies path[k] != path[from] by {
                assert(from < k);
            }
            assert forall|k1: int, k2: int| from + 1 <= k1 < k2 < path.len() implies path[k1] != path[k2] by {
                assert(from <= k1);
            }
        }
    }
}

/// `verifier::indices_usable_from`, quantified.
pub proof fn lemma_usable_iff(pool: Seq<Option<super::super::parsed::spec::PathCert>>, path: Seq<nat>, from: int)
    requires 0 <= from,
    ensures super::super::verifier::indices_usable_from(pool, path, from)
        <==> (forall|k: int| from <= k < path.len() ==> path[k] < pool.len() && (#[trigger] pool[path[k] as int]) is Some),
    decreases path.len() - from,
{
    if from < path.len() { lemma_usable_iff(pool, path, from + 1); }
}

// ---------------------------------------------------------------------------
// The shape of the order
// ---------------------------------------------------------------------------

/// The position of an issuer among a node's candidate issuers (`issuer_at`).
pub open spec fn issuer_index(anchors_len: nat, issuer: super::super::verifier::Issuer) -> nat {
    match issuer {
        super::super::verifier::Issuer::Anchor(a) => a,
        super::super::verifier::Issuer::Pool(j) => anchors_len + j,
    }
}

/// The rank of a step below the node of length `n`: its issuer's position
/// when it is examined at that node, else the position of the pool
/// certificate pushed at that node on the way to it.
pub open spec fn rank(anchors_len: nat, n: nat, step: super::super::verifier::IssuerStep) -> nat {
    if step.path.len() == n { issuer_index(anchors_len, step.issuer) }
    else { anchors_len + step.path[step.path.len() - n - 1] }
}

/// `path` is a suffix of `p` (the partial path `p` extends `path` upward).
pub open spec fn has_suffix(p: Seq<nat>, path: Seq<nat>) -> bool {
    p.len() >= path.len() && p.subrange(p.len() - path.len(), p.len() as int) == path
}

/// No step occurs twice in `s`.
pub open spec fn steps_distinct(s: Seq<super::super::verifier::IssuerStep>) -> bool {
    forall|k1: int, k2: int| 0 <= k1 < k2 < s.len() ==> s[k1] != s[k2]
}

/// The properties `lemma_steps_from` proves of the steps at the node `path`
/// from issuer `i` on.
pub open spec fn segment_shape(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    path: Seq<nat>, i: nat, seg: Seq<super::super::verifier::IssuerStep>,
) -> bool {
    &&& forall|k: int| 0 <= k < seg.len() ==>
        super::super::verifier::step_name_chained(environment, anchors, pool, leaf, #[trigger] seg[k])
    &&& forall|k: int| 0 <= k < seg.len() ==> has_suffix((#[trigger] seg[k]).path, path)
    &&& forall|k: int| 0 <= k < seg.len() ==> rank(anchors.len(), path.len(), #[trigger] seg[k]) >= i
    &&& steps_distinct(seg)
}

proof fn lemma_issuer_at_index(anchors: Seq<super::super::parsed::spec::Anchor>, i: nat)
    ensures issuer_index(anchors.len(), issuer_at(anchors, i)) == i,
{
}

/// Two distinct-step sequences whose ranks are `i` and more than `i` join
/// into one.
proof fn lemma_join_distinct(
    a: Seq<super::super::verifier::IssuerStep>, b: Seq<super::super::verifier::IssuerStep>,
    anchors_len: nat, n: nat, i: nat,
)
    requires
        steps_distinct(a), steps_distinct(b),
        forall|k: int| 0 <= k < a.len() ==> rank(anchors_len, n, #[trigger] a[k]) == i,
        forall|k: int| 0 <= k < b.len() ==> rank(anchors_len, n, #[trigger] b[k]) > i,
    ensures steps_distinct(a + b),
{
    let s = a + b;
    assert forall|k1: int, k2: int| 0 <= k1 < k2 < s.len() implies s[k1] != s[k2] by {
        if k2 < a.len() { assert(s[k1] == a[k1] && s[k2] == a[k2]); }
        else if k1 >= a.len() { assert(s[k1] == b[k1 - a.len()] && s[k2] == b[k2 - a.len()]); }
        else {
            assert(s[k1] == a[k1] && s[k2] == b[k2 - a.len()]);
            assert(rank(anchors_len, n, a[k1]) == i);
            assert(rank(anchors_len, n, b[k2 - a.len()]) > i);
        }
    }
}

/// The shape of the steps at a node.
pub proof fn lemma_steps_from(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    path: Seq<nat>, i: nat,
)
    ensures segment_shape(environment, anchors, pool, leaf, path, i, steps_from(environment, anchors, pool, leaf, path, i)),
    decreases environment.max_intermediates - path.len(), anchors.len() + pool.len() - i
{
    let seg = steps_from(environment, anchors, pool, leaf, path, i);
    if path.len() > environment.max_intermediates || i >= anchors.len() + pool.len() {
        assert(seg.len() == 0);
    } else {
        let step = super::super::verifier::IssuerStep { path, issuer: issuer_at(anchors, i) };
        let rest = steps_from(environment, anchors, pool, leaf, path, i + 1);
        lemma_steps_from(environment, anchors, pool, leaf, path, i + 1);
        lemma_issuer_at_index(anchors, i);
        assert(path.subrange(path.len() - path.len(), path.len() as int) =~= path);
        assert(has_suffix(step.path, path));
        assert(rank(anchors.len(), path.len(), step) == i);
        assert forall|k: int| 0 <= k < rest.len() implies rank(anchors.len(), path.len(), #[trigger] rest[k]) > i by {
            assert(rank(anchors.len(), path.len(), rest[k]) >= i + 1);
        }
        if !super::super::verifier::step_name_chained(environment, anchors, pool, leaf, step) {
            assert(seg == rest);
        } else {
            match step.issuer {
                super::super::verifier::Issuer::Anchor(_) => {
                    let here = seq![step];
                    assert(seg == here + rest);
                    assert forall|k: int| 0 <= k < here.len() implies rank(anchors.len(), path.len(), #[trigger] here[k]) == i by {
                        assert(here[k] == step);
                    }
                    lemma_join_distinct(here, rest, anchors.len(), path.len(), i);
                    assert forall|k: int| 0 <= k < seg.len() implies
                        super::super::verifier::step_name_chained(environment, anchors, pool, leaf, #[trigger] seg[k])
                        && has_suffix(seg[k].path, path) && rank(anchors.len(), path.len(), seg[k]) >= i by {
                        if k > 0 { assert(seg[k] == rest[k - 1]); }
                    }
                },
                super::super::verifier::Issuer::Pool(j) => {
                    let child = seq![j] + path;
                    let inner = steps_from(environment, anchors, pool, leaf, child, 0);
                    lemma_steps_from(environment, anchors, pool, leaf, child, 0);
                    assert forall|k: int| 0 <= k < inner.len() implies
                        has_suffix((#[trigger] inner[k]).path, path)
                        && inner[k].path.len() > path.len()
                        && rank(anchors.len(), path.len(), inner[k]) == i by {
                        let p = inner[k].path;
                        assert(has_suffix(p, child));
                        let tail = p.subrange(p.len() - child.len(), p.len() as int);
                        assert(tail == child);
                        assert(p[p.len() - path.len() - 1] == tail[0]);
                        assert(child[0] == j);
                        assert(p.subrange(p.len() - path.len(), p.len() as int) =~= tail.subrange(1, tail.len() as int));
                        assert(child.subrange(1, child.len() as int) =~= path);
                    }
                    let here = seq![step] + inner;
                    assert(seg == here + rest);
                    assert forall|k1: int, k2: int| 0 <= k1 < k2 < here.len() implies here[k1] != here[k2] by {
                        if k1 == 0 {
                            assert(here[k2] == inner[k2 - 1]);
                            assert(inner[k2 - 1].path.len() > path.len());
                        } else {
                            assert(here[k1] == inner[k1 - 1] && here[k2] == inner[k2 - 1]);
                        }
                    }
                    assert forall|k: int| 0 <= k < here.len() implies rank(anchors.len(), path.len(), #[trigger] here[k]) == i by {
                        if k > 0 { assert(here[k] == inner[k - 1]); }
                    }
                    lemma_join_distinct(here, rest, anchors.len(), path.len(), i);
                    assert forall|k: int| 0 <= k < seg.len() implies
                        super::super::verifier::step_name_chained(environment, anchors, pool, leaf, #[trigger] seg[k])
                        && has_suffix(seg[k].path, path) && rank(anchors.len(), path.len(), seg[k]) >= i by {
                        if k == 0 { assert(seg[k] == step); }
                        else if k < here.len() { assert(seg[k] == inner[k - 1]); }
                        else { assert(seg[k] == rest[k - here.len()]); }
                    }
                },
            }
        }
    }
}

proof fn lemma_step_absent(order: Seq<super::super::verifier::IssuerStep>, step: super::super::verifier::IssuerStep, from: int)
    requires 0 <= from, forall|k: int| from <= k < order.len() ==> order[k] != step,
    ensures super::super::verifier::step_absent_from(order, step, from),
    decreases order.len() - from,
{
    if from < order.len() { lemma_step_absent(order, step, from + 1); }
}

proof fn lemma_well_formed_from(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    order: Seq<super::super::verifier::IssuerStep>, from: int,
)
    requires
        0 <= from, steps_distinct(order),
        forall|k: int| 0 <= k < order.len() ==>
            super::super::verifier::step_name_chained(environment, anchors, pool, leaf, #[trigger] order[k]),
    ensures super::super::verifier::search_order_well_formed_from(environment, anchors, pool, leaf, order, from),
    decreases order.len() - from,
{
    if from < order.len() {
        assert forall|k: int| from + 1 <= k < order.len() implies order[k] != order[from] by {
            assert(from < k);
        }
        lemma_step_absent(order, order[from], from + 1);
        lemma_well_formed_from(environment, anchors, pool, leaf, order, from + 1);
    }
}

/// `theorems::order_well_formed`.
pub proof fn lemma_order_well_formed(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
)
    ensures super::theorems::order_well_formed(environment, anchors, pool, leaf),
{
    lemma_steps_from(environment, anchors, pool, leaf, seq![], 0);
    lemma_well_formed_from(environment, anchors, pool, leaf, search_order(environment, anchors, pool, leaf), 0);
}

// ---------------------------------------------------------------------------
// Completeness
// ---------------------------------------------------------------------------

/// A name-chained step at the node `path` is among the node's steps from
/// any earlier issuer on.
pub proof fn lemma_contains_step(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    path: Seq<nat>, i: nat, target: nat,
)
    requires
        path.len() <= environment.max_intermediates, i <= target < anchors.len() + pool.len(),
        super::super::verifier::step_name_chained(environment, anchors, pool, leaf,
            super::super::verifier::IssuerStep { path, issuer: issuer_at(anchors, target) }),
    ensures steps_from(environment, anchors, pool, leaf, path, i).contains(
        super::super::verifier::IssuerStep { path, issuer: issuer_at(anchors, target) }),
    decreases target - i,
{
    let seg = steps_from(environment, anchors, pool, leaf, path, i);
    let goal = super::super::verifier::IssuerStep { path, issuer: issuer_at(anchors, target) };
    let step = super::super::verifier::IssuerStep { path, issuer: issuer_at(anchors, i) };
    let rest = steps_from(environment, anchors, pool, leaf, path, i + 1);
    if i == target {
        assert(seg[0] == goal);
    } else {
        lemma_contains_step(environment, anchors, pool, leaf, path, i + 1, target);
        let k = choose|k: int| 0 <= k < rest.len() && rest[k] == goal;
        if !super::super::verifier::step_name_chained(environment, anchors, pool, leaf, step) {
            assert(seg[k] == goal);
        } else {
            match step.issuer {
                super::super::verifier::Issuer::Anchor(_) => {
                    assert(seg == seq![step] + rest);
                    assert(seg[k + 1] == goal);
                },
                super::super::verifier::Issuer::Pool(j) => {
                    let inner = steps_from(environment, anchors, pool, leaf, seq![j] + path, 0);
                    let here = seq![step] + inner;
                    assert(seg == here + rest);
                    assert(seg[here.len() + k] == goal);
                },
            }
        }
    }
}

/// The steps of the node a name-chained pool step pushes are among the
/// steps of its own node, from any earlier issuer on.
pub proof fn lemma_contains_node(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    path: Seq<nat>, i: nat, j: nat,
)
    requires
        path.len() <= environment.max_intermediates, i <= anchors.len() + j, j < pool.len(),
        super::super::verifier::step_name_chained(environment, anchors, pool, leaf,
            super::super::verifier::IssuerStep { path, issuer: super::super::verifier::Issuer::Pool(j) }),
    ensures forall|x: super::super::verifier::IssuerStep|
        #[trigger] steps_from(environment, anchors, pool, leaf, seq![j] + path, 0).contains(x)
            ==> steps_from(environment, anchors, pool, leaf, path, i).contains(x),
    decreases anchors.len() + j - i,
{
    let seg = steps_from(environment, anchors, pool, leaf, path, i);
    let inner = steps_from(environment, anchors, pool, leaf, seq![j] + path, 0);
    let step = super::super::verifier::IssuerStep { path, issuer: issuer_at(anchors, i) };
    let rest = steps_from(environment, anchors, pool, leaf, path, i + 1);
    if i == anchors.len() + j {
        assert(issuer_at(anchors, i) == super::super::verifier::Issuer::Pool(j));
        let here = seq![step] + inner;
        assert(seg == here + rest);
        assert forall|x: super::super::verifier::IssuerStep| #[trigger] inner.contains(x) implies seg.contains(x) by {
            let k = choose|k: int| 0 <= k < inner.len() && inner[k] == x;
            assert(seg[k + 1] == x);
        }
    } else {
        lemma_contains_node(environment, anchors, pool, leaf, path, i + 1, j);
        assert forall|x: super::super::verifier::IssuerStep| #[trigger] inner.contains(x) implies seg.contains(x) by {
            assert(rest.contains(x));
            let k = choose|k: int| 0 <= k < rest.len() && rest[k] == x;
            if !super::super::verifier::step_name_chained(environment, anchors, pool, leaf, step) {
                assert(seg[k] == x);
            } else {
                match step.issuer {
                    super::super::verifier::Issuer::Anchor(_) => {
                        assert(seg == seq![step] + rest);
                        assert(seg[k + 1] == x);
                    },
                    super::super::verifier::Issuer::Pool(j2) => {
                        let inner2 = steps_from(environment, anchors, pool, leaf, seq![j2] + path, 0);
                        let here = seq![step] + inner2;
                        assert(seg == here + rest);
                        assert(seg[here.len() + k] == x);
                    },
                }
            }
        }
    }
}

/// The facts about a well-formed, name-chained candidate the walk uses.
proof fn lemma_candidate_facts(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    candidate: super::super::verifier::Candidate,
)
    requires super::super::verifier::candidate_well_formed(anchors, pool, candidate, environment.max_intermediates),
    ensures
        forall|k: int| 0 <= k < candidate.path.len() ==> candidate.path[k] < pool.len()
            && (#[trigger] pool[candidate.path[k] as int]) is Some,
        forall|k1: int, k2: int| 0 <= k1 < k2 < candidate.path.len() ==> candidate.path[k1] != candidate.path[k2],
        candidate.path.len() <= environment.max_intermediates,
        super::super::verifier::candidate_certificates(pool, leaf, candidate).len() == candidate.path.len() + 1,
        super::super::verifier::candidate_certificates(pool, leaf, candidate)[candidate.path.len() as int] == leaf,
        forall|k: int| 0 <= k < candidate.path.len() ==>
            #[trigger] super::super::verifier::candidate_certificates(pool, leaf, candidate)[k]
                == pool[candidate.path[k] as int]->Some_0,
{
    hide(super::super::verifier::candidate_verdict);
    hide(super::super::spec::process);
    hide(super::super::profile::path_profile);
    lemma_usable_iff(pool, candidate.path, 0);
    lemma_distinct_iff(candidate.path, 0);
    super::super::exec::lemma_intermediates_of(pool, candidate.path);
    let mids = super::super::verifier::intermediates_of(pool, candidate.path);
    let certs = super::super::verifier::candidate_certificates(pool, leaf, candidate);
    assert(certs == mids.push(leaf));
    assert forall|k: int| 0 <= k < candidate.path.len() implies
        #[trigger] certs[k] == pool[candidate.path[k] as int]->Some_0 by {
        assert(certs[k] == mids[k]);
    }
}

/// A pool step is name-chained from its parts.
proof fn lemma_pool_step_chained(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    path: Seq<nat>, j: nat,
)
    requires
        path.len() < environment.max_intermediates, j < pool.len(), pool[j as int] is Some,
        forall|k: int| 0 <= k < path.len() ==> path[k] < pool.len() && (#[trigger] pool[path[k] as int]) is Some,
        forall|k1: int, k2: int| 0 <= k1 < k2 < path.len() ==> path[k1] != path[k2],
        forall|k: int| 0 <= k < path.len() ==> path[k] != j,
        pool[j as int]->Some_0.tbs.subject_der == super::super::verifier::sought_issuer(pool, leaf, path),
    ensures super::super::verifier::step_name_chained(environment, anchors, pool, leaf,
        super::super::verifier::IssuerStep { path, issuer: super::super::verifier::Issuer::Pool(j) }),
{
    lemma_usable_iff(pool, path, 0);
    lemma_distinct_iff(path, 0);
    lemma_absent_iff(path, j, 0);
}

/// The step that finds `pool[path[m]]` above the suffix of a candidate's
/// path from `m + 1` on is name-chained.
proof fn lemma_suffix_step(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    candidate: super::super::verifier::Candidate, m: int,
)
    requires
        0 <= m < candidate.path.len(),
        super::super::verifier::candidate_well_formed(anchors, pool, candidate, environment.max_intermediates),
        super::theorems::candidate_name_chained(anchors, pool, leaf, candidate),
    ensures
        super::super::verifier::step_name_chained(environment, anchors, pool, leaf, super::super::verifier::IssuerStep {
            path: candidate.path.subrange(m + 1, candidate.path.len() as int),
            issuer: super::super::verifier::Issuer::Pool(candidate.path[m]),
        }),
        seq![candidate.path[m]] + candidate.path.subrange(m + 1, candidate.path.len() as int)
            == candidate.path.subrange(m, candidate.path.len() as int),
        candidate.path[m] < pool.len(),
        candidate.path.len() <= environment.max_intermediates,
{
    hide(super::super::verifier::candidate_verdict);
    hide(super::super::spec::process);
    hide(super::super::profile::path_profile);
    hide(super::super::verifier::step_name_chained);
    hide(super::super::verifier::candidate_certificates);
    hide(super::super::verifier::candidate_well_formed);
    let p = candidate.path;
    let n = p.len() as int;
    lemma_candidate_facts(environment, anchors, pool, leaf, candidate);
    let certs = super::super::verifier::candidate_certificates(pool, leaf, candidate);
    let above = p.subrange(m + 1, n);
    let j = p[m];
    assert forall|k: int| 0 <= k < above.len() implies above[k] < pool.len()
        && (#[trigger] pool[above[k] as int]) is Some by {
        assert(above[k] == p[m + 1 + k]);
    }
    assert forall|k1: int, k2: int| 0 <= k1 < k2 < above.len() implies above[k1] != above[k2] by {
        assert(above[k1] == p[m + 1 + k1] && above[k2] == p[m + 1 + k2]);
    }
    assert forall|k: int| 0 <= k < above.len() implies above[k] != j by {
        assert(above[k] == p[m + 1 + k]);
    }
    assert(certs[m + 1].tbs.issuer_der == certs[m].tbs.subject_der);
    if m + 1 < n {
        assert(above[0] == p[m + 1]);
        assert(certs[m + 1] == pool[p[m + 1] as int]->Some_0);
    }
    assert(super::super::verifier::sought_issuer(pool, leaf, above) == certs[m + 1].tbs.issuer_der);
    assert(certs[m] == pool[j as int]->Some_0);
    lemma_pool_step_chained(environment, anchors, pool, leaf, above, j);
    assert(seq![j] + above =~= p.subrange(m, n));
}

/// Every suffix of a candidate's path, from position `m` on, is a node whose
/// steps are all in the whole order.
proof fn lemma_suffix_reached(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    candidate: super::super::verifier::Candidate, m: int,
)
    requires
        0 <= m <= candidate.path.len(),
        super::super::verifier::candidate_well_formed(anchors, pool, candidate, environment.max_intermediates),
        super::theorems::candidate_name_chained(anchors, pool, leaf, candidate),
    ensures forall|x: super::super::verifier::IssuerStep|
        #[trigger] steps_from(environment, anchors, pool, leaf,
            candidate.path.subrange(m, candidate.path.len() as int), 0).contains(x)
            ==> search_order(environment, anchors, pool, leaf).contains(x),
    decreases candidate.path.len() - m,
{
    hide(super::super::verifier::candidate_verdict);
    hide(super::super::spec::process);
    hide(super::super::profile::path_profile);
    hide(steps_from);
    hide(super::super::verifier::step_name_chained);
    hide(super::super::verifier::candidate_well_formed);
    hide(super::theorems::candidate_name_chained);
    let p = candidate.path;
    let n = p.len() as int;
    if m == n {
        assert(p.subrange(n, n) =~= Seq::<nat>::empty());
    } else {
        lemma_suffix_reached(environment, anchors, pool, leaf, candidate, m + 1);
        lemma_suffix_step(environment, anchors, pool, leaf, candidate, m);
        reveal(super::super::verifier::candidate_well_formed);
        assert(p.len() <= environment.max_intermediates);
        lemma_contains_node(environment, anchors, pool, leaf, p.subrange(m + 1, n), 0, p[m]);
    }
}

/// `theorems::candidates_complete` (the design's `lemma_candidates_complete`).
pub proof fn lemma_candidates_complete(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    candidate: super::super::verifier::Candidate,
)
    ensures super::theorems::candidates_complete(environment, anchors, pool, leaf, candidate),
{
    hide(super::super::verifier::candidate_verdict);
    hide(super::super::spec::process);
    hide(super::super::profile::path_profile);
    if super::super::verifier::candidate_well_formed(anchors, pool, candidate, environment.max_intermediates)
        && super::theorems::candidate_name_chained(anchors, pool, leaf, candidate) {
        let p = candidate.path;
        let a = candidate.anchor;
        lemma_suffix_reached(environment, anchors, pool, leaf, candidate, 0);
        assert(p.subrange(0, p.len() as int) =~= p);
        lemma_candidate_facts(environment, anchors, pool, leaf, candidate);
        let certs = super::super::verifier::candidate_certificates(pool, leaf, candidate);
        if p.len() > 0 { assert(certs[0] == pool[p[0] as int]->Some_0); }
        assert(super::super::verifier::sought_issuer(pool, leaf, p) == certs[0].tbs.issuer_der);
        assert(issuer_at(anchors, a) == super::super::verifier::Issuer::Anchor(a));
        lemma_contains_step(environment, anchors, pool, leaf, p, 0, a);
        assert(steps_from(environment, anchors, pool, leaf, p, 0).contains(super::theorems::completing_step(candidate)));
    }
}

// ---------------------------------------------------------------------------
// A valid candidate is well formed and name-chained
// ---------------------------------------------------------------------------

/// A valid candidate is well formed.
proof fn lemma_valid_well_formed(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    candidate: super::super::verifier::Candidate, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime,
)
    requires super::super::verifier::candidate_valid(environment, anchors, pool, leaf, candidate, reference, now),
    ensures super::super::verifier::candidate_well_formed(anchors, pool, candidate, environment.max_intermediates),
{
    hide(super::super::spec::process);
    hide(super::super::profile::path_profile);
    hide(super::super::verifier::path_within_budget);
    hide(super::super::verifier::candidate_certificates);
}

/// A valid candidate is well formed and name-chained (P8's `thm_anchored`).
pub proof fn lemma_valid_chained(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    candidate: super::super::verifier::Candidate, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime,
)
    requires super::super::verifier::candidate_valid(environment, anchors, pool, leaf, candidate, reference, now),
    ensures
        super::super::verifier::candidate_well_formed(anchors, pool, candidate, environment.max_intermediates),
        super::theorems::candidate_name_chained(anchors, pool, leaf, candidate),
{
    hide(super::super::verifier::candidate_verdict);
    hide(super::super::spec::process);
    hide(super::super::profile::path_profile);
    lemma_valid_well_formed(environment, anchors, pool, leaf, candidate, reference, now);
    super::super::theorems::lemma_candidate_reduces(environment, anchors, pool, leaf, candidate, reference, now);
    let certs = super::super::verifier::candidate_certificates(pool, leaf, candidate);
    super::super::lemmas::lemma_thm_anchored(environment.link, environment.revoked,
        anchors[candidate.anchor as int], certs, now);
}

// ---------------------------------------------------------------------------
// No candidate's verdict is BuildBudgetExhausted
// ---------------------------------------------------------------------------

proof fn lemma_process_from_not_budget(
    link: super::super::spec::LinkFn, revoked: super::super::spec::RevokedFn,
    certs: Seq<super::super::parsed::spec::PathCert>, i: int, now: crate::time::spec::CertificateTime,
    state: super::super::spec::State,
)
    ensures super::super::spec::process_from(link, revoked, certs, i, now, state)
        != Err::<Seq<u8>, super::super::spec::PathError>(super::super::spec::PathError::BuildBudgetExhausted),
    decreases certs.len() - i,
{
    if 0 <= i < certs.len() {
        reveal_with_fuel(super::super::spec::process_from, 1);
        if i < certs.len() - 1 {
            if let Ok(next) = super::super::spec::preparation_for_next(state, certs[i]) {
                lemma_process_from_not_budget(link, revoked, certs, i + 1, now, next);
            }
        }
    }
}

proof fn lemma_intermediates_profile_not_budget(certs: Seq<super::super::parsed::spec::PathCert>, i: int)
    ensures super::super::profile::intermediates_profile_from(certs, i)
        != Err::<(), super::super::spec::PathError>(super::super::spec::PathError::BuildBudgetExhausted),
    decreases certs.len() - i,
{
    if 0 <= i < certs.len() - 1 { lemma_intermediates_profile_not_budget(certs, i + 1); }
}

/// No candidate's verdict is `BuildBudgetExhausted`: only the search
/// reports it.
pub proof fn lemma_verdict_not_budget(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    candidate: super::super::verifier::Candidate, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime,
)
    ensures super::super::verifier::candidate_verdict(environment, anchors, pool, leaf, candidate, reference, now)
        != Err::<Seq<u8>, super::super::spec::PathError>(super::super::spec::PathError::BuildBudgetExhausted),
{
    let certs = super::super::verifier::candidate_certificates(pool, leaf, candidate);
    if super::super::verifier::candidate_well_formed(anchors, pool, candidate, environment.max_intermediates) {
        let anchor = anchors[candidate.anchor as int];
        lemma_intermediates_profile_not_budget(certs, 0);
        if let Ok(state) = super::super::spec::initialization(anchor, certs.len()) {
            lemma_process_from_not_budget(environment.link, environment.revoked, certs, 0, now, state);
        }
    }
}

// ---------------------------------------------------------------------------
// First valid
// ---------------------------------------------------------------------------

/// No step of `s` completes a valid candidate.
pub open spec fn none_valid(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    s: Seq<super::super::verifier::IssuerStep>,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
) -> bool {
    forall|k: int| 0 <= k < s.len() ==> !step_valid(environment, anchors, pool, leaf, #[trigger] s[k], reference, now)
}

/// What `first_valid_from` returns.
pub proof fn lemma_first_valid(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    order: Seq<super::super::verifier::IssuerStep>, from: int, to: int,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
)
    requires 0 <= from,
    ensures match first_valid_from(environment, anchors, pool, leaf, order, from, to, reference, now) {
        Some(k) => from <= k < to && k < order.len()
            && step_valid(environment, anchors, pool, leaf, order[k as int], reference, now)
            && forall|k2: int| from <= k2 < k ==> !step_valid(environment, anchors, pool, leaf, #[trigger] order[k2], reference, now),
        None => forall|k2: int| from <= k2 < to && k2 < order.len() ==>
            !step_valid(environment, anchors, pool, leaf, #[trigger] order[k2], reference, now),
    },
    decreases to - from,
{
    if from < to && from < order.len()
        && !step_valid(environment, anchors, pool, leaf, order[from], reference, now) {
        lemma_first_valid(environment, anchors, pool, leaf, order, from + 1, to, reference, now);
        match first_valid_from(environment, anchors, pool, leaf, order, from, to, reference, now) {
            Some(k) => {
                assert forall|k2: int| from <= k2 < k implies
                    !step_valid(environment, anchors, pool, leaf, #[trigger] order[k2], reference, now) by {
                    if k2 > from { assert(from + 1 <= k2); }
                }
            },
            None => {
                assert forall|k2: int| from <= k2 < to && k2 < order.len() implies
                    !step_valid(environment, anchors, pool, leaf, #[trigger] order[k2], reference, now) by {
                    if k2 > from { assert(from + 1 <= k2); }
                }
            },
        }
    }
}

/// P7's `no_valid_step_between`, from the quantified form.
pub proof fn lemma_no_valid_between(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    order: Seq<super::super::verifier::IssuerStep>, from: int, to: int,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
)
    requires
        0 <= from,
        forall|k: int| from <= k < to && k < order.len() ==>
            !step_valid(environment, anchors, pool, leaf, #[trigger] order[k], reference, now),
    ensures super::super::verifier::no_valid_step_between(environment, anchors, pool, leaf, order, from, to, reference, now),
    decreases to - from,
{
    if from < to && from < order.len() {
        lemma_no_valid_between(environment, anchors, pool, leaf, order, from + 1, to, reference, now);
        assert(!step_valid(environment, anchors, pool, leaf, order[from], reference, now));
    }
}

/// `first_candidate_error` never returns `BuildBudgetExhausted`.
proof fn lemma_first_error_not_budget(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    order: Seq<super::super::verifier::IssuerStep>, from: int,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
)
    ensures first_candidate_error(environment, anchors, pool, leaf, order, from, reference, now)
        != Some(super::super::spec::PathError::BuildBudgetExhausted),
    decreases order.len() - from,
{
    if 0 <= from < order.len() {
        lemma_first_error_not_budget(environment, anchors, pool, leaf, order, from + 1, reference, now);
        if let Some(candidate) = super::super::verifier::step_candidate(order[from]) {
            lemma_verdict_not_budget(environment, anchors, pool, leaf, candidate, reference, now);
        }
    }
}

/// When no step of the whole order completes a valid candidate, no
/// candidate is valid (completeness).
proof fn lemma_order_complete_none_valid(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
)
    requires forall|k: int| 0 <= k < search_order(environment, anchors, pool, leaf).len() ==>
        !step_valid(environment, anchors, pool, leaf, #[trigger] search_order(environment, anchors, pool, leaf)[k], reference, now),
    ensures forall|candidate: super::super::verifier::Candidate|
        !super::super::verifier::candidate_valid(environment, anchors, pool, leaf, candidate, reference, now),
{
    hide(super::super::verifier::candidate_verdict);
    hide(super::super::spec::process);
    hide(super::super::profile::path_profile);
    hide(steps_from);
    hide(search_order);
    hide(super::super::verifier::candidate_well_formed);
    hide(super::theorems::candidate_name_chained);
    let order = search_order(environment, anchors, pool, leaf);
    assert forall|candidate: super::super::verifier::Candidate|
        !super::super::verifier::candidate_valid(environment, anchors, pool, leaf, candidate, reference, now) by {
        if super::super::verifier::candidate_valid(environment, anchors, pool, leaf, candidate, reference, now) {
            lemma_valid_chained(environment, anchors, pool, leaf, candidate, reference, now);
            lemma_candidates_complete(environment, anchors, pool, leaf, candidate);
            let k = choose|k: int| 0 <= k < order.len() && order[k] == super::theorems::completing_step(candidate);
            assert(super::super::verifier::step_candidate(order[k]) == Some(candidate));
            assert(step_valid(environment, anchors, pool, leaf, order[k], reference, now));
        }
    }
}

/// `theorems::thm_first_valid`.
pub proof fn lemma_thm_first_valid(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime, budget: nat,
)
    ensures super::theorems::thm_first_valid(environment, anchors, pool, leaf, reference, now, budget),
{
    hide(super::super::verifier::candidate_verdict);
    hide(super::super::spec::process);
    hide(super::super::profile::path_profile);
    hide(steps_from);
    let order = search_order(environment, anchors, pool, leaf);
    lemma_first_valid(environment, anchors, pool, leaf, order, 0, budget as int, reference, now);
    match first_valid_from(environment, anchors, pool, leaf, order, 0, budget as int, reference, now) {
        Some(k) => {
            let candidate = super::super::verifier::step_candidate(order[k as int])->Some_0;
            assert(super::super::verifier::step_candidate(order[k as int]) is Some);
            assert(order[k as int] == super::theorems::completing_step(candidate));
            lemma_no_valid_between(environment, anchors, pool, leaf, order, 0, k as int, reference, now);
            let v = super::spec::search(environment, anchors, pool, leaf, reference, now, budget)->Ok_0;
            assert(super::super::verifier::Candidate { anchor: v.anchor, path: v.path } == candidate);
            assert(order[k as int] == super::theorems::completing_step(
                super::super::verifier::Candidate { anchor: v.anchor, path: v.path }));
        },
        None => {
            if order.len() > budget {
                lemma_no_valid_between(environment, anchors, pool, leaf, order, 0, budget as int, reference, now);
            } else {
                lemma_first_error_not_budget(environment, anchors, pool, leaf, order, 0, reference, now);
                lemma_order_complete_none_valid(environment, anchors, pool, leaf, reference, now);
            }
        },
    }
}

/// `theorems::meets_verifier_contract`.
pub proof fn lemma_meets_verifier_contract(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    presented: Seq<Seq<u8>>, reference: crate::spec::ReferenceIdentity, now: u64,
)
    ensures super::theorems::meets_verifier_contract(environment, anchors, presented, reference, now),
{
    hide(super::super::verifier::candidate_verdict);
    hide(super::super::spec::process);
    hide(super::super::profile::path_profile);
    hide(steps_from);
    hide(super::super::parsed::spec::parse_path_cert);
    match super::super::verifier::chain_inputs(presented, now) {
        Err(e) => {
            assert(e == super::super::spec::PathError::Malformed);
        },
        Ok(inputs) => {
            lemma_thm_first_valid(environment, anchors, inputs.pool, inputs.leaf, reference, inputs.now,
                super::super::verifier::build_budget());
            lemma_order_well_formed(environment, anchors, inputs.pool, inputs.leaf);
        },
    }
}

// ---------------------------------------------------------------------------
// Facts the executable search's proof uses
// ---------------------------------------------------------------------------

/// The first of two errors that is present.
pub open spec fn then_error(first: Option<super::super::spec::PathError>, next: Option<super::super::spec::PathError>)
    -> Option<super::super::spec::PathError>
{
    if first is Some { first } else { next }
}

/// What the node `path` examines at issuer `i`, before the issuers after it.
pub open spec fn steps_at(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    path: Seq<nat>, i: nat,
) -> Seq<super::super::verifier::IssuerStep> {
    let step = super::super::verifier::IssuerStep { path, issuer: issuer_at(anchors, i) };
    if !super::super::verifier::step_name_chained(environment, anchors, pool, leaf, step) { seq![] }
    else { match step.issuer {
        super::super::verifier::Issuer::Anchor(_) => seq![step],
        super::super::verifier::Issuer::Pool(j) => seq![step] + steps_from(environment, anchors, pool, leaf, seq![j] + path, 0),
    }}
}

/// One unfolding of `steps_from`.
pub proof fn lemma_unfold(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    path: Seq<nat>, i: nat,
)
    requires path.len() <= environment.max_intermediates,
    ensures
        i < anchors.len() + pool.len() ==> steps_from(environment, anchors, pool, leaf, path, i)
            == steps_at(environment, anchors, pool, leaf, path, i) + steps_from(environment, anchors, pool, leaf, path, i + 1),
        i >= anchors.len() + pool.len() ==> steps_from(environment, anchors, pool, leaf, path, i) == Seq::<super::super::verifier::IssuerStep>::empty(),
{
    hide(super::super::verifier::step_name_chained);
    let rest = steps_from(environment, anchors, pool, leaf, path, i + 1);
    if i < anchors.len() + pool.len() {
        let step = super::super::verifier::IssuerStep { path, issuer: issuer_at(anchors, i) };
        if super::super::verifier::step_name_chained(environment, anchors, pool, leaf, step) {
            match step.issuer {
                super::super::verifier::Issuer::Anchor(_) => {},
                super::super::verifier::Issuer::Pool(j) => {
                    let inner = steps_from(environment, anchors, pool, leaf, seq![j] + path, 0);
                    assert(seq![step] + inner + rest == (seq![step] + inner) + rest);
                },
            }
        } else {
            assert(Seq::<super::super::verifier::IssuerStep>::empty() + rest =~= rest);
        }
    }
}

/// At full depth a node has no pool steps.
pub proof fn lemma_no_pool_steps(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    path: Seq<nat>, i: nat,
)
    requires path.len() == environment.max_intermediates, i >= anchors.len(),
    ensures steps_from(environment, anchors, pool, leaf, path, i) == Seq::<super::super::verifier::IssuerStep>::empty(),
    decreases anchors.len() + pool.len() - i,
{
    lemma_unfold(environment, anchors, pool, leaf, path, i);
    if i < anchors.len() + pool.len() {
        lemma_no_pool_steps(environment, anchors, pool, leaf, path, i + 1);
        assert(steps_at(environment, anchors, pool, leaf, path, i) =~= Seq::<super::super::verifier::IssuerStep>::empty());
        assert(Seq::<super::super::verifier::IssuerStep>::empty() + Seq::<super::super::verifier::IssuerStep>::empty()
            =~= Seq::<super::super::verifier::IssuerStep>::empty());
    }
}

proof fn lemma_first_error_shift(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    a: Seq<super::super::verifier::IssuerStep>, b: Seq<super::super::verifier::IssuerStep>, t: int,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
)
    requires 0 <= t,
    ensures first_candidate_error(environment, anchors, pool, leaf, a + b, a.len() + t, reference, now)
        == first_candidate_error(environment, anchors, pool, leaf, b, t, reference, now),
    decreases b.len() - t,
{
    hide(super::super::verifier::candidate_verdict);
    if t < b.len() {
        lemma_first_error_shift(environment, anchors, pool, leaf, a, b, t + 1, reference, now);
        assert((a + b)[a.len() + t] == b[t]);
    }
}

proof fn lemma_first_error_from(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    a: Seq<super::super::verifier::IssuerStep>, b: Seq<super::super::verifier::IssuerStep>, from: int,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
)
    requires 0 <= from <= a.len(),
    ensures first_candidate_error(environment, anchors, pool, leaf, a + b, from, reference, now)
        == then_error(first_candidate_error(environment, anchors, pool, leaf, a, from, reference, now),
            first_candidate_error(environment, anchors, pool, leaf, b, 0, reference, now)),
    decreases a.len() - from,
{
    hide(super::super::verifier::candidate_verdict);
    if from == a.len() {
        lemma_first_error_shift(environment, anchors, pool, leaf, a, b, 0, reference, now);
    } else {
        lemma_first_error_from(environment, anchors, pool, leaf, a, b, from + 1, reference, now);
        assert((a + b)[from] == a[from]);
    }
}

/// `first_candidate_error` of a concatenation.
pub proof fn lemma_first_error_concat(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    a: Seq<super::super::verifier::IssuerStep>, b: Seq<super::super::verifier::IssuerStep>,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
)
    ensures first_candidate_error(environment, anchors, pool, leaf, a + b, 0, reference, now)
        == then_error(first_candidate_error(environment, anchors, pool, leaf, a, 0, reference, now),
            first_candidate_error(environment, anchors, pool, leaf, b, 0, reference, now)),
{
    lemma_first_error_from(environment, anchors, pool, leaf, a, b, 0, reference, now);
}

/// `first_candidate_error` of one step.
pub proof fn lemma_first_error_one(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    step: super::super::verifier::IssuerStep,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
)
    ensures first_candidate_error(environment, anchors, pool, leaf, seq![step], 0, reference, now)
        == match super::super::verifier::step_candidate(step) {
            Some(candidate) => match super::super::verifier::candidate_verdict(environment, anchors, pool, leaf, candidate, reference, now) {
                Err(e) => Some(e),
                Ok(_) => None,
            },
            None => None,
        },
{
    hide(super::super::verifier::candidate_verdict);
    reveal_with_fuel(first_candidate_error, 2);
}

/// The first valid step of `order[0..to]` is at `k`.
pub proof fn lemma_first_valid_at(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    order: Seq<super::super::verifier::IssuerStep>, k: int, to: int,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
)
    requires
        0 <= k < to, k < order.len(),
        step_valid(environment, anchors, pool, leaf, order[k], reference, now),
        forall|k2: int| 0 <= k2 < k ==> !step_valid(environment, anchors, pool, leaf, #[trigger] order[k2], reference, now),
    ensures first_valid_from(environment, anchors, pool, leaf, order, 0, to, reference, now) == Some(k as nat),
{
    hide(step_valid);
    lemma_first_valid(environment, anchors, pool, leaf, order, 0, to, reference, now);
}

/// No step of `order[0..to]` is valid.
pub proof fn lemma_first_valid_none(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>,
    pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    order: Seq<super::super::verifier::IssuerStep>, to: int,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
)
    requires forall|k2: int| 0 <= k2 < to && k2 < order.len() ==>
        !step_valid(environment, anchors, pool, leaf, #[trigger] order[k2], reference, now),
    ensures first_valid_from(environment, anchors, pool, leaf, order, 0, to, reference, now) is None,
{
    hide(step_valid);
    lemma_first_valid(environment, anchors, pool, leaf, order, 0, to, reference, now);
}

} // verus!
