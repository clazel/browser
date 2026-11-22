//! Host-including inclusive ancestors (`host::hi`) under the DOM operations
//! the parser calls: which pairs of nodes can become related.
//!
//! Two shapes of change cover every operation.
//! - [`up_same`]: the arena grows, or kinds change, and no node of the old
//!   arena gets another step up (its parent, or a parentless fragment's
//!   host). Then the old nodes are related as before ([`lemma_hi_same`]),
//!   and a new node is no host-including inclusive ancestor of an old one
//!   ([`lemma_new_not_hi`]). Creating a node, establishing a template's
//!   contents, and changing data, attributes or the document's mode are
//!   such changes.
//! - [`grafted`]: some nodes are given the parent `pp`, and every other
//!   node keeps its step up or loses it. Then a new relation goes through
//!   a grafted node: `a` is a host-including inclusive ancestor of `x`
//!   after the change only if it was before, or `x` was below a grafted
//!   node and `a` was a host-including inclusive ancestor of `pp`
//!   ([`lemma_hi_graft`]). "Remove" (no grafted node), "insert" (the node)
//!   and "take all the children" (the children) are such changes.

#[cfg(verus_only)]
use crate::host::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use clazel_dom::deep_clone_size_lemmas::{
    lemma_hi_rank, lemma_hi_self, lemma_hi_unfold, lemma_rank_witness, lemma_up_rank,
    lemma_wf_facts, up,
};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Basic facts

/// A host-including inclusive ancestor of a node of the arena is a node of
/// the arena.
#[verifier::spinoff_prover]
pub proof fn lemma_hi_valid(d: Document, a: NodeId, x: NodeId)
    requires
        dom::host_acyclic(d),
        dom::valid(d, x),
        hi(d, a, x),
    ensures
        dom::valid(d, a),
{
    let r = lemma_rank_witness(d);
    lemma_hi_rank(d, r, a, x);
}

/// [`hi`] is transitive.
#[verifier::spinoff_prover]
pub proof fn lemma_hi_trans(d: Document, a: NodeId, b: NodeId, x: NodeId)
    requires
        dom::host_acyclic(d),
        dom::valid(d, x),
        hi(d, a, b),
        hi(d, b, x),
    ensures
        hi(d, a, x),
{
    let r = lemma_rank_witness(d);
    clazel_dom::host_acyclic_lemmas::lemma_hi_trans(d, r, a, b, x);
}

/// Two nodes that are host-including inclusive ancestors of each other are
/// the same node.
#[verifier::spinoff_prover]
pub proof fn lemma_hi_antisym(d: Document, a: NodeId, x: NodeId)
    requires
        dom::host_acyclic(d),
        dom::valid(d, x),
        dom::valid(d, a),
        hi(d, a, x),
        hi(d, x, a),
    ensures
        a == x,
{
    let r = lemma_rank_witness(d);
    lemma_hi_rank(d, r, a, x);
    lemma_hi_rank(d, r, x, a);
    if x != a {
        lemma_hi_unfold(d, r, a, x);
        lemma_up_rank(d, r, x);
        let y = up(d, x)->Some_0;
        lemma_hi_rank(d, r, a, y);
    }
}

/// A host-including inclusive ancestor of a node's parent is one of the
/// node.
#[verifier::spinoff_prover]
pub proof fn lemma_hi_parent(d: Document, a: NodeId, c: NodeId)
    requires
        dom::host_acyclic(d),
        dom::valid(d, c),
        d.nodes[c as int].parent is Some,
        hi(d, a, d.nodes[c as int].parent->Some_0),
    ensures
        hi(d, a, c),
{
    let r = lemma_rank_witness(d);
    clazel_dom::deep_clone_size_lemmas::lemma_hi_child(d, r, a, d.nodes[c as int].parent->Some_0, c);
}

/// A node is no host-including inclusive ancestor of its parent.
#[verifier::spinoff_prover]
pub proof fn lemma_child_not_above(d: Document, c: NodeId)
    requires
        dom::host_acyclic(d),
        dom::valid(d, c),
        d.nodes[c as int].parent is Some,
    ensures
        !hi(d, c, d.nodes[c as int].parent->Some_0),
{
    let r = lemma_rank_witness(d);
    let pp = d.nodes[c as int].parent->Some_0;
    assert(up(d, c) == Some(pp));
    lemma_up_rank(d, r, c);
    if hi(d, c, pp) {
        lemma_hi_rank(d, r, c, pp);
    }
}

/// A host-including inclusive ancestor of a node other than itself is one
/// of the node's step up, which exists.
#[verifier::spinoff_prover]
pub proof fn lemma_hi_step(d: Document, a: NodeId, x: NodeId)
    requires
        dom::host_acyclic(d),
        dom::valid(d, x),
        x != a,
    ensures
        hi(d, a, x) <==> (up(d, x) is Some && hi(d, a, up(d, x)->Some_0)),
        up(d, x) is Some ==> dom::valid(d, up(d, x)->Some_0),
{
    let r = lemma_rank_witness(d);
    lemma_hi_unfold(d, r, a, x);
    if up(d, x) is Some {
        lemma_up_rank(d, r, x);
    }
}

/// A node with no step up (no parent, and not a fragment with a host) has
/// no host-including inclusive ancestor but itself.
#[verifier::spinoff_prover]
pub proof fn lemma_hi_root(d: Document, a: NodeId, x: NodeId)
    requires
        dom::host_acyclic(d),
        dom::valid(d, x),
        up(d, x) is None,
        hi(d, a, x),
    ensures
        a == x,
{
    if x != a {
        lemma_hi_step(d, a, x);
    }
}

/// Node `n` has no step up: it has no parent, and is no fragment with a
/// host. A node the parser has just created is so until it is inserted.
pub open spec fn top(d: Document, n: NodeId) -> bool {
    up(d, n) is None
}

/// A node with no parent that is no fragment has no step up.
pub proof fn lemma_top_of(d: Document, n: NodeId)
    requires
        d.nodes[n as int].parent is None,
        !(d.nodes[n as int].kind is DocumentFragment),
    ensures
        top(d, n),
{
}

/// A node with no step up has no parent.
pub proof fn lemma_top_parentless(d: Document, n: NodeId)
    requires
        top(d, n),
    ensures
        d.nodes[n as int].parent is None,
{
}

/// A node with no step up has no host-including inclusive ancestor but
/// itself ([`lemma_hi_root`]).
#[verifier::spinoff_prover]
pub proof fn lemma_hi_top(d: Document, a: NodeId, x: NodeId)
    requires
        dom::host_acyclic(d),
        dom::valid(d, x),
        top(d, x),
        hi(d, a, x),
    ensures
        a == x,
{
    lemma_hi_root(d, a, x);
}

/// A node that is not a fragment and is no host-including inclusive
/// ancestor of a template element is none of its template contents.
#[verifier::spinoff_prover]
pub proof fn lemma_not_hi_contents(d: Document, a: NodeId, t: NodeId)
    requires
        dom::wf(d),
        dom::host_acyclic(d),
        has_template_contents(d, t),
        dom::valid(d, a),
        !(d.nodes[a as int].kind is DocumentFragment),
        !hi(d, a, t),
    ensures
        !hi(d, a, template_contents(d, t)),
        dom::valid(d, template_contents(d, t)),
{
    lemma_wf_facts(d);
    let c = template_contents(d, t);
    assert(d.nodes[c as int].kind is DocumentFragment);
    assert(d.nodes[c as int].kind->DocumentFragment_host == Some(t));
    assert(d.nodes[c as int].parent is None);
    assert(up(d, c) == Some(t));
    lemma_hi_step(d, a, c);
}

// ---------------------------------------------------------------------
// Changes that keep every step up

/// `d2` has every node of `d`, with the step up it has in `d`.
pub open spec fn up_same(d: Document, d2: Document) -> bool {
    &&& d.nodes.len() <= d2.nodes.len()
    &&& forall|y: NodeId| dom::valid(d, y) ==> #[trigger] up(d2, y) == up(d, y)
}

/// [`lemma_hi_same`], with the rankings.
#[verifier::spinoff_prover]
proof fn lemma_hi_same_ranked(d: Document, d2: Document, r: Seq<nat>, r2: Seq<nat>, a: NodeId, x: NodeId)
    requires
        dom::host_ranked(d, r),
        dom::host_ranked(d2, r2),
        up_same(d, d2),
        dom::valid(d, x),
    ensures
        hi(d2, a, x) == hi(d, a, x),
    decreases r[x as int],
{
    if x != a {
        lemma_hi_unfold(d, r, a, x);
        lemma_hi_unfold(d2, r2, a, x);
        assert(up(d2, x) == up(d, x));
        if up(d, x) is Some {
            lemma_up_rank(d, r, x);
            lemma_hi_same_ranked(d, d2, r, r2, a, up(d, x)->Some_0);
        }
    }
}

/// With [`up_same`], a node of the old arena has the host-including
/// inclusive ancestors it had.
#[verifier::spinoff_prover]
pub proof fn lemma_hi_same(d: Document, d2: Document, a: NodeId, x: NodeId)
    requires
        dom::host_acyclic(d),
        dom::host_acyclic(d2),
        up_same(d, d2),
        dom::valid(d, x),
    ensures
        hi(d2, a, x) == hi(d, a, x),
{
    let r = lemma_rank_witness(d);
    let r2 = lemma_rank_witness(d2);
    lemma_hi_same_ranked(d, d2, r, r2, a, x);
}

/// With [`up_same`], a new node is no host-including inclusive ancestor of
/// a node of the old arena.
#[verifier::spinoff_prover]
pub proof fn lemma_new_not_hi(d: Document, d2: Document, n: NodeId, x: NodeId)
    requires
        dom::host_acyclic(d),
        dom::host_acyclic(d2),
        up_same(d, d2),
        dom::valid(d, x),
        n >= d.nodes.len(),
    ensures
        !hi(d2, n, x),
{
    lemma_hi_same(d, d2, n, x);
    if hi(d, n, x) {
        lemma_hi_valid(d, n, x);
    }
}

/// [`lemma_new_low`] for one node of the old arena, with the ranking: the
/// steps up from it stay in the old arena, which is well formed.
#[verifier::spinoff_prover]
proof fn lemma_new_not_hi_ranked(d: Document, d2: Document, r2: Seq<nat>, n: NodeId, x: NodeId)
    requires
        dom::wf(d),
        dom::host_ranked(d2, r2),
        up_same(d, d2),
        dom::valid(d, x),
        n >= d.nodes.len(),
    ensures
        !hi(d2, n, x),
    decreases r2[x as int],
{
    lemma_wf_facts(d);
    lemma_hi_unfold(d2, r2, n, x);
    if up(d2, x) is Some {
        let y = up(d2, x)->Some_0;
        assert(up(d, x) == Some(y));
        assert(dom::valid(d, y));
        lemma_up_rank(d2, r2, x);
        lemma_new_not_hi_ranked(d, d2, r2, n, y);
    }
}

/// With [`up_same`] from a well-formed arena `d`, the first new node `n`
/// is `host::low` in `d2`, if `d2` is `clazel_dom::spec::host_acyclic`
/// (nothing is assumed of `d`).
#[verifier::spinoff_prover]
pub proof fn lemma_new_low(d: Document, d2: Document, n: NodeId)
    requires
        dom::wf(d),
        up_same(d, d2),
        n == d.nodes.len(),
    ensures
        dom::host_acyclic(d2) ==> low(d2, n),
{
    if dom::host_acyclic(d2) {
        let r2 = lemma_rank_witness(d2);
        assert forall|x: NodeId| #![trigger hi(d2, n, x)] x < n implies !hi(d2, n, x) by {
            lemma_new_not_hi_ranked(d, d2, r2, n, x);
        }
    }
}

/// With [`up_same`], a node of the old arena with no step up has none.
pub proof fn lemma_up_same_top(d: Document, d2: Document, n: NodeId)
    requires
        up_same(d, d2),
        dom::valid(d, n),
        top(d, n),
    ensures
        top(d2, n),
{
    assert(up(d2, n) == up(d, n));
}

/// A node just created has no step up.
#[verifier::spinoff_prover]
pub proof fn lemma_create_top(d: Document, k: NodeKind)
    requires
        dom::wf(d),
        dom::creatable(d, k),
        dom::can_create(d, 1),
    ensures
        top(dom::create_node(d, k).0, dom::create_node(d, k).1),
{
    clazel_dom::lemmas::theorem_create_node_wf(d, k);
}

/// [`up_same`] is reflexive and transitive.
pub proof fn lemma_up_same_trans(d: Document, d1: Document, d2: Document)
    requires
        up_same(d, d1),
        up_same(d1, d2),
    ensures
        up_same(d, d2),
        up_same(d, d),
{
    assert forall|y: NodeId| dom::valid(d, y) implies #[trigger] up(d2, y) == up(d, y) by {
        assert(up(d1, y) == up(d, y));
        assert(dom::valid(d1, y));
        assert(up(d2, y) == up(d1, y));
    }
}

/// Creating a node keeps every step up.
#[verifier::spinoff_prover]
pub proof fn lemma_create_up_same(d: Document, k: NodeKind)
    ensures
        up_same(d, dom::create_node(d, k).0),
{
    let d2 = dom::create_node(d, k).0;
    assert forall|y: NodeId| dom::valid(d, y) implies #[trigger] up(d2, y) == up(d, y) by {
        assert(d2.nodes[y as int] == d.nodes[y as int]);
    }
}

/// Establishing the template contents of the element `t` keeps every step
/// up.
#[verifier::spinoff_prover]
pub proof fn lemma_ctc_up_same(d: Document, t: NodeId)
    requires
        dom::valid(d, t),
        d.nodes[t as int].kind is Element,
    ensures
        up_same(d, dom::create_template_contents(d, t).0),
{
    let d2 = dom::create_template_contents(d, t).0;
    assert forall|y: NodeId| dom::valid(d, y) implies #[trigger] up(d2, y) == up(d, y) by {
        if y != t {
            assert(d2.nodes[y as int] == d.nodes[y as int]);
        } else {
            assert(d2.nodes[y as int].parent == d.nodes[y as int].parent);
            assert(d2.nodes[y as int].kind is Element);
        }
    }
}

/// A change of the kind of one node that is not a fragment, to a kind
/// that is not one, keeps every step up.
#[verifier::spinoff_prover]
pub proof fn lemma_kind_up_same(d: Document, d2: Document, n: NodeId)
    requires
        d2.nodes.len() == d.nodes.len(),
        forall|y: int| 0 <= y < d.nodes.len() && y != n ==> #[trigger] d2.nodes[y] == d.nodes[y],
        dom::valid(d, n) ==> d2.nodes[n as int].parent == d.nodes[n as int].parent && !(d.nodes[n as int].kind is DocumentFragment)
            && !(d2.nodes[n as int].kind is DocumentFragment),
    ensures
        up_same(d, d2),
{
    assert forall|y: NodeId| dom::valid(d, y) implies #[trigger] up(d2, y) == up(d, y) by {
        if y != n {
            assert(d2.nodes[y as int] == d.nodes[y as int]);
        }
    }
}

/// Appending data to a node keeps every step up.
#[verifier::spinoff_prover]
pub proof fn lemma_append_data_up_same(d: Document, n: NodeId, data: Seq<u32>)
    requires
        dom::valid(d, n),
        d.nodes[n as int].kind is Text,
    ensures
        up_same(d, dom::append_data(d, n, data)),
{
    lemma_kind_up_same(d, dom::append_data(d, n, data), n);
}

/// Appending an attribute to an element keeps every step up.
#[verifier::spinoff_prover]
pub proof fn lemma_append_attribute_up_same(d: Document, e: NodeId, a: Attr)
    requires
        dom::valid(d, e),
        d.nodes[e as int].kind is Element,
    ensures
        up_same(d, dom::append_attribute(d, e, a)),
{
    lemma_kind_up_same(d, dom::append_attribute(d, e, a), e);
}

/// Setting the document's mode keeps every step up.
#[verifier::spinoff_prover]
pub proof fn lemma_set_mode_up_same(d: Document, mode: DocumentMode)
    requires
        d.nodes.len() > 0,
        d.nodes[0].kind is Document,
    ensures
        up_same(d, dom::set_mode(d, mode)),
{
    lemma_kind_up_same(d, dom::set_mode(d, mode), 0);
}

// ---------------------------------------------------------------------
// Grafting

/// `d2` is `d` with some of the nodes `g` given the parent `pp`: every
/// node keeps its step up, or loses it, or is in `g` and has the step up
/// `pp`.
pub open spec fn grafted(d: Document, d2: Document, g: Set<NodeId>, pp: NodeId) -> bool {
    &&& d2.nodes.len() == d.nodes.len()
    &&& forall|y: NodeId|
        dom::valid(d, y) ==> (#[trigger] up(d2, y)) == up(d, y) || up(d2, y) is None || (g.contains(y) && up(d2, y) == Some(pp))
}

/// The walk of [`lemma_hi_graft`] up from `x` in `d2`: it reaches `a` by
/// steps of `d` alone, or passes a grafted node `n` (the first one), which
/// `x` is below in `d`, and goes on from `pp`.
#[verifier::spinoff_prover]
proof fn lemma_graft_walk(d: Document, d2: Document, r: Seq<nat>, r2: Seq<nat>, g: Set<NodeId>, pp: NodeId, a: NodeId, x: NodeId) -> (m: Option<NodeId>)
    requires
        dom::host_ranked(d, r),
        dom::host_ranked(d2, r2),
        grafted(d, d2, g, pp),
        dom::valid(d, x),
        hi(d2, a, x),
    ensures
        match m {
            None => hi(d, a, x),
            Some(n) => g.contains(n) && dom::valid(d, n) && hi(d, n, x) && hi(d2, a, pp),
        },
    decreases r2[x as int],
{
    if x == a {
        None
    } else {
        lemma_hi_unfold(d2, r2, a, x);
        lemma_up_rank(d2, r2, x);
        let y = up(d2, x)->Some_0;
        if up(d2, x) == up(d, x) {
            let m = lemma_graft_walk(d, d2, r, r2, g, pp, a, y);
            match m {
                None => {
                    lemma_hi_unfold(d, r, a, x);
                },
                Some(n) => {
                    if x != n {
                        lemma_hi_unfold(d, r, n, x);
                    }
                },
            }
            m
        } else {
            lemma_hi_self(d, x);
            Some(x)
        }
    }
}

/// With [`grafted`], where no node of `g` is a host-including inclusive
/// ancestor of `pp` in `d`: a host-including inclusive ancestor `a` of `x`
/// in `d2` is one in `d`, or `x` is below a node `n` of `g` in `d` and `a`
/// is a host-including inclusive ancestor of `pp` in `d`.
#[verifier::spinoff_prover]
pub proof fn lemma_hi_graft(d: Document, d2: Document, g: Set<NodeId>, pp: NodeId, a: NodeId, x: NodeId) -> (m: Option<NodeId>)
    requires
        dom::host_acyclic(d),
        dom::host_acyclic(d2),
        grafted(d, d2, g, pp),
        dom::valid(d, x),
        dom::valid(d, pp),
        forall|n: NodeId| #[trigger] g.contains(n) && dom::valid(d, n) ==> !hi(d, n, pp),
        hi(d2, a, x),
    ensures
        match m {
            None => hi(d, a, x),
            Some(n) => g.contains(n) && dom::valid(d, n) && hi(d, n, x) && hi(d, a, pp),
        },
{
    let r = lemma_rank_witness(d);
    let r2 = lemma_rank_witness(d2);
    let m = lemma_graft_walk(d, d2, r, r2, g, pp, a, x);
    if m is Some {
        let m2 = lemma_graft_walk(d, d2, r, r2, g, pp, a, pp);
        if let Some(n2) = m2 {
            assert(g.contains(n2));
            assert(false);
        }
    }
    m
}

/// With [`grafted`] and no grafted node (links are only lost), nothing
/// becomes related.
#[verifier::spinoff_prover]
pub proof fn lemma_hi_lost(d: Document, d2: Document, a: NodeId, x: NodeId)
    requires
        dom::host_acyclic(d),
        dom::host_acyclic(d2),
        grafted(d, d2, Set::empty(), 0),
        dom::valid(d, x),
        d.nodes.len() > 0,
        hi(d2, a, x),
    ensures
        hi(d, a, x),
{
    let m = lemma_hi_graft(d, d2, Set::empty(), 0, a, x);
}

/// DOM "remove" only takes a link away.
#[verifier::spinoff_prover]
pub proof fn lemma_remove_grafted(d: Document, node: NodeId)
    requires
        clazel_dom::contract::remove_requires(d, node),
    ensures
        grafted(d, dom::remove(d, node), Set::empty(), 0),
{
    clazel_dom::lemmas::theorem_remove_keeps_record(d, node);
    lemma_wf_facts(d);
    let d2 = dom::remove(d, node);
    assert forall|y: NodeId| dom::valid(d, y) implies (#[trigger] up(d2, y)) == up(d, y) || up(d2, y) is None by {
        assert(d2.nodes[y as int].kind == d.nodes[y as int].kind);
        if y == node {
            assert(d2.nodes[y as int].parent is None);
            assert(!(d.nodes[y as int].kind is DocumentFragment));
        } else {
            assert(d2.nodes[y as int].parent == d.nodes[y as int].parent);
        }
    }
}

/// DOM "insert" grafts `node` below `parent`.
#[verifier::spinoff_prover]
pub proof fn lemma_insert_grafted(d: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        dom::insert_requires(d, node, parent, child),
    ensures
        grafted(d, dom::insert(d, node, parent, child), Set::<NodeId>::empty().insert(node), parent),
        up(dom::insert(d, node, parent, child), node) == Some(parent),
{
    clazel_dom::lemmas::theorem_insert_wf(d, node, parent, child);
    let d2 = dom::insert(d, node, parent, child);
    assert forall|y: NodeId| dom::valid(d, y) implies (#[trigger] up(d2, y)) == up(d, y) || (Set::<NodeId>::empty().insert(node).contains(y) && up(d2, y) == Some(
        parent,
    )) by {
        assert(d2.nodes[y as int].kind == d.nodes[y as int].kind);
        if y != node {
            assert(d2.nodes[y as int].parent == d.nodes[y as int].parent);
        }
    }
}

/// "Take all of the child nodes of `from` and append them to `to`" grafts
/// the children of `from` below `to`.
#[verifier::spinoff_prover]
pub proof fn lemma_reparent_grafted(d: Document, from: NodeId, to: NodeId)
    requires
        dom::reparent_children_requires(d, from, to),
    ensures
        grafted(d, dom::reparent_children(d, from, to), d.nodes[from as int].children.to_set(), to),
{
    clazel_dom::lemmas::theorem_reparent_children_wf(d, from, to);
    let d2 = dom::reparent_children(d, from, to);
    let kids = d.nodes[from as int].children;
    assert forall|y: NodeId| dom::valid(d, y) implies (#[trigger] up(d2, y)) == up(d, y) || (kids.to_set().contains(y) && up(d2, y)
        == Some(to)) by {
        assert(d2.nodes[y as int].kind == d.nodes[y as int].kind);
        if kids.contains(y) {
            let j = choose|j: int| 0 <= j < kids.len() && kids[j] == y;
            assert(dom::parent(d2, dom::children(d, from)[j]) == Some(to));
        } else {
            assert(d2.nodes[y as int].parent == d.nodes[y as int].parent);
        }
    }
}

} // verus!
