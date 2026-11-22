//! Every operation keeps [`host_acyclic`]: no cycle through parents and a
//! template's host. [`wf`] forbids a cycle of parents only (its `paths`
//! follow parents), so a template that is a child of its own contents is
//! well formed but not host-acyclic, and the unfolding of its subtree is
//! infinite (`clone_deep`'s precondition, `contract::clone_deep_requires`).
//! The theorems here say that DOM's algorithms never build one, so
//! [`host_acyclic`] is an invariant of the tree: a caller that starts from
//! [`new_document`] and uses only the operations below has it for free.
//!
//! The key fact is the "host-including inclusive ancestor" check of DOM
//! §4.2.3† "ensure pre-insertion validity", step 2 (and "replace", step 2),
//! which exists to forbid such cycles. The raw [`insert`] and
//! [`reparent_children`], which the parser calls after its own checks, carry
//! only [`insert_requires`]'s inclusive-ancestor half of it, which is not
//! enough (a template inserted below a node of its own contents has
//! `!is_inclusive_ancestor(node, parent)`); they need the host half as well
//! (`host_acyclic_contract::insert_acyclic_requires`,
//! `host_acyclic_contract::reparent_children_acyclic_requires`). Pre-insert, replace and
//! replace all make the check themselves.
//!
//! Everything rests on one lemma, [`lemma_graft`]: if some nodes are given
//! the new parent `p` (and no other link is added), none of them a
//! host-including inclusive ancestor of `p`, a ranking of the old arena
//! (parents and hosts rank below their children) is changed into one of the
//! new arena by raising the rank of everything below a grafted node above
//! `p`'s rank. That ranking is not below the node count any more;
//! [`lemma_ranked_u_acyclic`] compresses it (a node's compressed rank is the
//! number of nodes ranked below it).

#[cfg(verus_only)]
use super::contract::*;
#[cfg(verus_only)]
use super::deep_clone_lemmas::*;
#[cfg(verus_only)]
use super::deep_clone_size_lemmas::*;
#[cfg(verus_only)]
use super::host_acyclic_contract::*;
#[cfg(verus_only)]
use super::lemmas::*;
#[cfg(verus_only)]
use super::ops_lemmas::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Rankings that need not be below the node count

/// A ranking of the arena's nodes that grows along every parent edge and
/// every host edge, at node `i`: like [`ranked_at`], but its ranks are not
/// bounded by the node count.
pub open spec fn ranked_u_at(doc: Document, rank: Seq<nat>, i: int) -> bool {
    let n = doc.nodes.len();
    let node = doc.nodes[i];
    &&& node.parent is Some ==> node.parent->Some_0 < n && rank[node.parent->Some_0 as int] < rank[i]
    &&& (node.kind is DocumentFragment && node.kind->DocumentFragment_host is Some) ==> {
        let h = node.kind->DocumentFragment_host->Some_0;
        h < n && rank[h as int] < rank[i]
    }
}

/// `rank` ranks every node of the arena ([`ranked_u_at`]).
pub open spec fn ranked_u(doc: Document, rank: Seq<nat>) -> bool {
    &&& rank.len() == doc.nodes.len()
    &&& forall|i: int| 0 <= i < doc.nodes.len() ==> #[trigger] ranked_u_at(doc, rank, i)
}

/// How many of the first `k` entries of `rank` are below `b`.
pub open spec fn rank_below(rank: Seq<nat>, k: nat, b: nat) -> nat
    decreases k,
{
    if k == 0 {
        0
    } else {
        rank_below(rank, (k - 1) as nat, b) + (if rank[(k - 1) as int] < b {
            1nat
        } else {
            0nat
        })
    }
}

/// At most `k`.
proof fn lemma_rank_below_le(rank: Seq<nat>, k: nat, b: nat)
    ensures
        rank_below(rank, k, b) <= k,
    decreases k,
{
    if k > 0 {
        lemma_rank_below_le(rank, (k - 1) as nat, b);
    }
}

/// A higher bound counts at least as many.
proof fn lemma_rank_below_mono(rank: Seq<nat>, k: nat, b1: nat, b2: nat)
    requires
        b1 <= b2,
    ensures
        rank_below(rank, k, b1) <= rank_below(rank, k, b2),
    decreases k,
{
    if k > 0 {
        lemma_rank_below_mono(rank, (k - 1) as nat, b1, b2);
    }
}

/// An entry between the bounds makes the higher bound count more.
proof fn lemma_rank_below_strict(rank: Seq<nat>, k: nat, b1: nat, b2: nat, j: int)
    requires
        k <= rank.len(),
        0 <= j < k,
        b1 <= rank[j] < b2,
    ensures
        rank_below(rank, k, b1) < rank_below(rank, k, b2),
    decreases k,
{
    if j == k - 1 {
        lemma_rank_below_mono(rank, (k - 1) as nat, b1, b2);
    } else {
        lemma_rank_below_strict(rank, (k - 1) as nat, b1, b2, j);
    }
}

/// An entry at least `b` keeps the count below `k`.
proof fn lemma_rank_below_lt(rank: Seq<nat>, k: nat, b: nat, j: int)
    requires
        k <= rank.len(),
        0 <= j < k,
        b <= rank[j],
    ensures
        rank_below(rank, k, b) < k,
    decreases k,
{
    if j == k - 1 {
        lemma_rank_below_le(rank, (k - 1) as nat, b);
    } else {
        lemma_rank_below_lt(rank, (k - 1) as nat, b, j);
    }
}

/// A ranking with ranks that need not be below the node count gives one
/// that is: a node's new rank is how many nodes are ranked below it.
pub proof fn lemma_ranked_u_acyclic(doc: Document, rank: Seq<nat>)
    requires
        ranked_u(doc, rank),
    ensures
        host_acyclic(doc),
{
    let n = doc.nodes.len();
    let cr = Seq::new(n, |i: int| rank_below(rank, n as nat, rank[i]));
    assert forall|i: int| 0 <= i < n implies #[trigger] ranked_at(doc, cr, i) by {
        assert(ranked_u_at(doc, rank, i));
        lemma_rank_below_lt(rank, n as nat, rank[i], i);
        let node = doc.nodes[i];
        if node.parent is Some {
            let q = node.parent->Some_0 as int;
            lemma_rank_below_strict(rank, n as nat, rank[q], rank[i], q);
        }
        if node.kind is DocumentFragment && node.kind->DocumentFragment_host is Some {
            let h = node.kind->DocumentFragment_host->Some_0 as int;
            lemma_rank_below_strict(rank, n as nat, rank[h], rank[i], h);
        }
    }
    assert(host_ranked(doc, cr));
}

/// What [`wf`] gives of a fragment, which is all the lemmas below need of
/// it: a fragment has no parent.
pub open spec fn frag_parentless(doc: Document) -> bool {
    forall|i: int| 0 <= i < doc.nodes.len() && (#[trigger] doc.nodes[i]).kind is DocumentFragment ==> doc.nodes[i].parent is None
}

/// A well-formed arena is [`frag_parentless`].
pub proof fn lemma_wf_frag_parentless(doc: Document)
    requires
        wf(doc),
    ensures
        frag_parentless(doc),
{
    lemma_wf_facts(doc);
}

// ---------------------------------------------------------------------
// Facts about host-including ancestors under a ranking

/// A host-including inclusive ancestor of a host-including inclusive
/// ancestor of `x` is one of `x`.
pub proof fn lemma_hi_trans(doc: Document, rank: Seq<nat>, a: NodeId, b: NodeId, x: NodeId)
    requires
        host_ranked(doc, rank),
        valid(doc, x),
        is_host_including_inclusive_ancestor(doc, a, b),
        is_host_including_inclusive_ancestor(doc, b, x),
    ensures
        is_host_including_inclusive_ancestor(doc, a, x),
    decreases rank[x as int],
{
    if x != b {
        lemma_hi_unfold(doc, rank, b, x);
        lemma_up_rank(doc, rank, x);
        let y = up(doc, x)->Some_0;
        lemma_hi_trans(doc, rank, a, b, y);
        if x != a {
            lemma_hi_unfold(doc, rank, a, x);
        }
    }
}

/// Chains read in an arena that has only lost links (a parent that was
/// there is kept or gone, kinds are kept) are chains of the old arena.
pub proof fn lemma_hw_sub(d: Document, d2: Document, a: NodeId, x: NodeId, f: nat)
    requires
        wf(d),
        d2.nodes.len() == d.nodes.len(),
        valid(d, x),
        forall|y: int| 0 <= y < d.nodes.len() ==> {
            &&& (#[trigger] d2.nodes[y]).kind == d.nodes[y].kind
            &&& (d2.nodes[y].parent == d.nodes[y].parent || d2.nodes[y].parent is None)
        },
        host_including_within(d2, a, x, f),
    ensures
        host_including_within(d, a, x, f),
    decreases f,
{
    lemma_wf_facts(d);
    if x != a {
        assert(f > 0);
        match up(d2, x) {
            Some(y) => {
                if d2.nodes[x as int].parent is Some {
                    assert(d.nodes[x as int].parent == d2.nodes[x as int].parent);
                } else {
                    assert(d.nodes[x as int].kind is DocumentFragment);
                    assert(d.nodes[x as int].parent is None);
                }
                assert(up(d, x) == Some(y));
                lemma_hw_sub(d, d2, a, y, (f - 1) as nat);
            },
            None => {},
        }
    }
}

/// Chains that do not pass through the node `n` do not see its new parent.
pub proof fn lemma_hw_unchanged(d: Document, d2: Document, n: NodeId, a: NodeId, x: NodeId, f: nat)
    requires
        wf(d),
        d2.nodes.len() == d.nodes.len(),
        valid(d, x),
        forall|y: int| 0 <= y < d.nodes.len() ==> (#[trigger] d2.nodes[y]).kind == d.nodes[y].kind,
        forall|y: int| 0 <= y < d.nodes.len() && y != n ==> (#[trigger] d2.nodes[y]).parent == d.nodes[y].parent,
        !host_including_within(d, n, x, f),
    ensures
        host_including_within(d2, a, x, f) == host_including_within(d, a, x, f),
    decreases f,
{
    lemma_wf_facts(d);
    if x != a {
        assert(x != n);
        if f > 0 {
            assert(up(d2, x) == up(d, x));
            match up(d, x) {
                Some(y) => {
                    lemma_hw_unchanged(d, d2, n, a, y, (f - 1) as nat);
                },
                None => {},
            }
        }
    }
}

// ---------------------------------------------------------------------
// Grafting

/// `x` is below one of `nodes`: a host-including descendant of one of them
/// (or one of them).
pub open spec fn in_graft(d: Document, nodes: Seq<NodeId>, x: NodeId) -> bool {
    exists|i: int| 0 <= i < nodes.len() && #[trigger] is_host_including_inclusive_ancestor(d, nodes[i], x)
}

/// A node below a grafted node, and not itself grafted, has its step up
/// below one too.
proof fn lemma_graft_up(d: Document, rank: Seq<nat>, nodes: Seq<NodeId>, x: NodeId, y: NodeId)
    requires
        host_ranked(d, rank),
        valid(d, x),
        up(d, x) == Some(y),
        !nodes.contains(x),
        in_graft(d, nodes, x),
    ensures
        in_graft(d, nodes, y),
{
    let i = choose|i: int| 0 <= i < nodes.len() && #[trigger] is_host_including_inclusive_ancestor(d, nodes[i], x);
    assert(nodes[i] != x);
    lemma_hi_unfold(d, rank, nodes[i], x);
    assert(is_host_including_inclusive_ancestor(d, nodes[i], y));
}

/// A node whose parent is below a grafted node is below it.
proof fn lemma_graft_child(d: Document, rank: Seq<nat>, nodes: Seq<NodeId>, c: NodeId, y: NodeId)
    requires
        host_ranked(d, rank),
        valid(d, c),
        d.nodes[c as int].parent == Some(y),
        in_graft(d, nodes, y),
    ensures
        in_graft(d, nodes, c),
{
    let i = choose|i: int| 0 <= i < nodes.len() && #[trigger] is_host_including_inclusive_ancestor(d, nodes[i], y);
    lemma_hi_child(d, rank, nodes[i], y, c);
    assert(is_host_including_inclusive_ancestor(d, nodes[i], c));
}

/// A fragment whose host is below a grafted node is below it.
proof fn lemma_graft_contents(d: Document, rank: Seq<nat>, nodes: Seq<NodeId>, f: NodeId, h: NodeId)
    requires
        host_ranked(d, rank),
        valid(d, f),
        d.nodes[f as int].parent is None,
        d.nodes[f as int].kind is DocumentFragment,
        d.nodes[f as int].kind->DocumentFragment_host == Some(h),
        in_graft(d, nodes, h),
    ensures
        in_graft(d, nodes, f),
{
    let i = choose|i: int| 0 <= i < nodes.len() && #[trigger] is_host_including_inclusive_ancestor(d, nodes[i], h);
    lemma_hi_contents(d, rank, nodes[i], h, f);
    assert(is_host_including_inclusive_ancestor(d, nodes[i], f));
}

/// Grafting: `d2` is `d` with each of `nodes` given the parent `p`, and no
/// other node given a parent it did not have (it may lose its parent), the
/// kinds unchanged. If no grafted node is a host-including inclusive
/// ancestor of `p` and none is a fragment, `d2` is [`host_acyclic`] if `d`
/// is. With no nodes this is losing links, which never makes a cycle.
///
/// The ranking of `d2`: raise everything below a grafted node by `rank[p] +
/// 1`. A grafted node then ranks above `p` (which is not below one), every
/// edge below a grafted node is between nodes raised alike, and an edge
/// from outside into the nodes below a grafted node is only the new one.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn lemma_graft(d: Document, d2: Document, nodes: Seq<NodeId>, p: NodeId)
    requires
        host_acyclic(d),
        frag_parentless(d),
        d.nodes.len() <= max_nodes(),
        valid(d, p),
        d2.nodes.len() == d.nodes.len(),
        forall|x: int| 0 <= x < d.nodes.len() ==> (#[trigger] d2.nodes[x]).kind == d.nodes[x].kind,
        forall|i: int| 0 <= i < nodes.len() ==> {
            let c = #[trigger] nodes[i];
            &&& valid(d, c)
            &&& !(d.nodes[c as int].kind is DocumentFragment)
            &&& !is_host_including_inclusive_ancestor(d, c, p)
            &&& d2.nodes[c as int].parent == Some(p)
        },
        forall|x: int| 0 <= x < d.nodes.len() && !nodes.contains(x as NodeId) ==> {
            (#[trigger] d2.nodes[x]).parent == d.nodes[x].parent || d2.nodes[x].parent is None
        },
    ensures
        host_acyclic(d2),
{
    let n = d.nodes.len();
    let r = lemma_rank_witness(d);
    let k = r[p as int] + 1;
    let r2 = Seq::new(n, |x: int| if in_graft(d, nodes, x as NodeId) {
        r[x] + k
    } else {
        r[x]
    });
    // `p` is not below a grafted node.
    assert(!in_graft(d, nodes, p)) by {
        if in_graft(d, nodes, p) {
            let i = choose|i: int| 0 <= i < nodes.len() && #[trigger] is_host_including_inclusive_ancestor(d, nodes[i], p);
            assert(!is_host_including_inclusive_ancestor(d, nodes[i], p));
        }
    }
    assert forall|i: int| 0 <= i < n implies ranked_u_at(d2, r2, i) by {
        assert(ranked_at(d, r, i));
        theorem_ranked_at_facts(d, r, i);
        let node2 = d2.nodes[i];
        let ig = in_graft(d, nodes, i as NodeId);
        if node2.parent is Some {
            let q = node2.parent->Some_0;
            if nodes.contains(i as NodeId) {
                let j = choose|j: int| 0 <= j < nodes.len() && nodes[j] == i as NodeId;
                assert(nodes[j] as int == i);
                assert(d2.nodes[nodes[j] as int].parent == Some(p));
                assert(q == p);
                lemma_hi_self(d, i as NodeId);
                assert(is_host_including_inclusive_ancestor(d, nodes[j], i as NodeId));
                assert(ig);
            } else {
                assert(d.nodes[i].parent == Some(q));
                assert((i as NodeId) as int == i);
                assert(parent(d, i as NodeId) == Some(q));
                assert(up(d, i as NodeId) == Some(q));
                if ig {
                    lemma_graft_up(d, r, nodes, i as NodeId, q);
                } else if in_graft(d, nodes, q) {
                    lemma_graft_child(d, r, nodes, i as NodeId, q);
                }
            }
        }
        if node2.kind is DocumentFragment && node2.kind->DocumentFragment_host is Some {
            let h = node2.kind->DocumentFragment_host->Some_0;
            assert(d.nodes[i].kind is DocumentFragment);
            assert(!nodes.contains(i as NodeId)) by {
                if nodes.contains(i as NodeId) {
                    let j = choose|j: int| 0 <= j < nodes.len() && nodes[j] == i as NodeId;
                    assert(!(d.nodes[nodes[j] as int].kind is DocumentFragment));
                }
            }
            assert(d.nodes[i].parent is None);
            assert((i as NodeId) as int == i);
            assert(parent(d, i as NodeId) is None);
            assert(up(d, i as NodeId) == Some(h));
            if ig {
                lemma_graft_up(d, r, nodes, i as NodeId, h);
            } else if in_graft(d, nodes, h) {
                lemma_graft_contents(d, r, nodes, i as NodeId, h);
            }
        }
    }
    assert(ranked_u(d2, r2));
    lemma_ranked_u_acyclic(d2, r2);
}
// ---------------------------------------------------------------------
// What `wf` gives

/// A well-formed arena is within the node limit.
proof fn lemma_wf_limit(doc: Document)
    requires
        wf(doc),
    ensures
        doc.nodes.len() <= max_nodes(),
{
    let paths = lemma_wf_witness(doc);
    assert(wf_with(doc, paths));
}

/// A node with a parent is not the document node.
proof fn lemma_child_not_document(doc: Document, c: NodeId)
    requires
        wf(doc),
        valid(doc, c),
        doc.nodes[c as int].parent is Some,
    ensures
        !(doc.nodes[c as int].kind is Document),
{
    let paths = lemma_wf_witness(doc);
    assert(wf_with(doc, paths));
}

// ---------------------------------------------------------------------
// New document, creating nodes, kinds

/// A new document is [`host_acyclic`].
pub proof fn theorem_new_document_host_acyclic(url: Seq<u32>)
    ensures
        host_acyclic(new_document(url)),
{
    let d = new_document(url);
    let rank = seq![0nat];
    assert forall|i: int| 0 <= i < d.nodes.len() implies #[trigger] ranked_at(d, rank, i) by {}
    assert(host_ranked(d, rank));
}

/// Creating a node keeps [`host_acyclic`]: the new node has no parent and,
/// being [`creatable`], no host.
pub proof fn theorem_create_node_host_acyclic(doc: Document, k: NodeKind)
    requires
        host_acyclic(doc),
        creatable(doc, k),
    ensures
        host_acyclic(create_node(doc, k).0),
{
    let r = lemma_rank_witness(doc);
    let n = doc.nodes.len();
    let d2 = create_node(doc, k).0;
    let r2 = r.push(0nat);
    assert forall|i: int| 0 <= i < n + 1 implies #[trigger] ranked_at(d2, r2, i) by {
        if i < n {
            assert(ranked_at(doc, r, i));
            theorem_ranked_at_facts(doc, r, i);
            assert(d2.nodes[i] == doc.nodes[i]);
        } else {
            assert(d2.nodes[i].parent is None);
        }
    }
    assert(host_ranked(d2, r2));
}

/// Creating a template's contents keeps [`host_acyclic`]: the contents is
/// ranked just above its host, and the host stays an element.
pub proof fn theorem_create_template_contents_host_acyclic(doc: Document, t: NodeId)
    requires
        host_acyclic(doc),
        valid(doc, t),
        doc.nodes[t as int].kind is Element,
    ensures
        host_acyclic(create_template_contents(doc, t).0),
{
    let r = lemma_rank_witness(doc);
    let n = doc.nodes.len();
    let d2 = create_template_contents(doc, t).0;
    let r2 = r.push(r[t as int] + 1);
    assert(ranked_at(doc, r, t as int));
    theorem_ranked_at_facts(doc, r, t as int);
    assert forall|i: int| 0 <= i < n + 1 implies #[trigger] ranked_at(d2, r2, i) by {
        if i < n {
            assert(ranked_at(doc, r, i));
            theorem_ranked_at_facts(doc, r, i);
            if i == t {
                assert(d2.nodes[i].parent == doc.nodes[i].parent);
                assert(d2.nodes[i].kind is Element);
            } else {
                assert(d2.nodes[i] == doc.nodes[i]);
            }
        } else {
            assert(d2.nodes[i].parent is None);
            assert(d2.nodes[i].kind == (NodeKind::DocumentFragment { host: Some(t) }));
        }
    }
    assert(host_ranked(d2, r2));
}

/// Replacing a node's kind by one of the same shape keeps [`host_acyclic`]:
/// no parent or host changes.
pub proof fn lemma_set_kind_acyclic(doc: Document, x: NodeId, k: NodeKind)
    requires
        host_acyclic(doc),
        valid(doc, x),
        same_shape(doc.nodes[x as int].kind, k),
    ensures
        host_acyclic(set_kind(doc, x, k)),
{
    let r = lemma_rank_witness(doc);
    let d2 = set_kind(doc, x, k);
    assert forall|i: int| 0 <= i < doc.nodes.len() implies #[trigger] ranked_at(d2, r, i) by {
        assert(ranked_at(doc, r, i));
        theorem_ranked_at_facts(doc, r, i);
        assert(d2.nodes[i].parent == doc.nodes[i].parent);
    }
    assert(host_ranked(d2, r));
}

/// "Replace data" at the end of a text keeps [`host_acyclic`].
pub proof fn theorem_append_data_host_acyclic(doc: Document, n: NodeId, data: Seq<u32>)
    requires
        host_acyclic(doc),
        append_data_requires(doc, n),
    ensures
        host_acyclic(append_data(doc, n, data)),
{
    let k = append_data(doc, n, data).nodes[n as int].kind;
    assert(append_data(doc, n, data) == set_kind(doc, n, k));
    lemma_set_kind_acyclic(doc, n, k);
}

/// "Append an attribute" keeps [`host_acyclic`].
pub proof fn theorem_append_attribute_host_acyclic(doc: Document, e: NodeId, attr: Attr)
    requires
        host_acyclic(doc),
        append_attribute_requires(doc, e),
    ensures
        host_acyclic(append_attribute(doc, e, attr)),
{
    let k = append_attribute(doc, e, attr).nodes[e as int].kind;
    assert(append_attribute(doc, e, attr) == set_kind(doc, e, k));
    lemma_set_kind_acyclic(doc, e, k);
}

/// Setting the document's mode keeps [`host_acyclic`].
pub proof fn theorem_set_mode_host_acyclic(doc: Document, mode: DocumentMode)
    requires
        host_acyclic(doc),
        wf(doc),
    ensures
        host_acyclic(set_mode(doc, mode)),
{
    let k = set_mode(doc, mode).nodes[0].kind;
    assert(set_mode(doc, mode) == set_kind(doc, 0, k));
    lemma_set_kind_acyclic(doc, 0, k);
}

/// Setting an element's attribute list keeps [`host_acyclic`].
pub proof fn lemma_set_attributes_acyclic(doc: Document, e: NodeId, attrs: Seq<Attr>)
    requires
        host_acyclic(doc),
        valid(doc, e),
        doc.nodes[e as int].kind is Element,
    ensures
        host_acyclic(set_attributes(doc, e, attrs)),
{
    let k = set_attributes(doc, e, attrs).nodes[e as int].kind;
    assert(set_attributes(doc, e, attrs) == set_kind(doc, e, k));
    lemma_set_kind_acyclic(doc, e, k);
}

/// "Change an attribute" keeps [`host_acyclic`].
pub proof fn theorem_change_attribute_host_acyclic(doc: Document, e: NodeId, i: nat, value: Seq<u32>)
    requires
        host_acyclic(doc),
        attribute_requires(doc, e, i),
    ensures
        host_acyclic(change_attribute(doc, e, i, value)),
{
    let attrs = doc.nodes[e as int].kind->Element_attributes;
    lemma_set_attributes_acyclic(doc, e, attrs.update(i as int, Attr { value, ..attrs[i as int] }));
}

/// "Remove an attribute" keeps [`host_acyclic`].
pub proof fn theorem_remove_attribute_host_acyclic(doc: Document, e: NodeId, i: nat)
    requires
        host_acyclic(doc),
        attribute_requires(doc, e, i),
    ensures
        host_acyclic(remove_attribute(doc, e, i)),
{
    lemma_set_attributes_acyclic(doc, e, doc.nodes[e as int].kind->Element_attributes.remove(i as int));
}

/// "Replace an attribute" keeps [`host_acyclic`].
pub proof fn theorem_replace_attribute_host_acyclic(doc: Document, e: NodeId, i: nat, new_attr: Attr)
    requires
        host_acyclic(doc),
        attribute_requires(doc, e, i),
    ensures
        host_acyclic(replace_attribute(doc, e, i, new_attr)),
{
    lemma_set_attributes_acyclic(doc, e, doc.nodes[e as int].kind->Element_attributes.update(i as int, new_attr));
}

// ---------------------------------------------------------------------
// remove, adopt

/// "Remove" keeps [`host_acyclic`]: it only takes a parent link away.
pub proof fn theorem_remove_host_acyclic(doc: Document, node: NodeId)
    requires
        host_acyclic(doc),
        remove_requires(doc, node),
    ensures
        host_acyclic(remove(doc, node)),
{
    theorem_remove_keeps_record(doc, node);
    lemma_wf_frag_parentless(doc);
    lemma_wf_limit(doc);
    let d2 = remove(doc, node);
    assert forall|x: int| 0 <= x < doc.nodes.len() && !(Seq::<NodeId>::empty()).contains(x as NodeId) implies {
        (#[trigger] d2.nodes[x]).parent == doc.nodes[x].parent || d2.nodes[x].parent is None
    } by {
        if x == node {
            assert(d2.nodes[x].parent is None);
        }
    }
    lemma_graft(doc, d2, Seq::<NodeId>::empty(), node);
}

/// "Adopt" keeps [`host_acyclic`].
pub proof fn theorem_adopt_host_acyclic(doc: Document, node: NodeId)
    requires
        host_acyclic(doc),
        adopt_requires(doc, node),
    ensures
        host_acyclic(adopt(doc, node)),
{
    if doc.nodes[node as int].parent is Some {
        theorem_remove_host_acyclic(doc, node);
    }
}

// ---------------------------------------------------------------------
// insert

/// A child of a fragment that is not a host-including inclusive ancestor of
/// `parent` is a node that is not a fragment and is not one either.
proof fn lemma_frag_child_graftable(doc: Document, r: Seq<nat>, frag: NodeId, parent: NodeId, i: int)
    requires
        wf(doc),
        host_ranked(doc, r),
        valid(doc, frag),
        valid(doc, parent),
        0 <= i < doc.nodes[frag as int].children.len(),
        !is_host_including_inclusive_ancestor(doc, frag, parent),
    ensures
        valid(doc, doc.nodes[frag as int].children[i]),
        !(doc.nodes[doc.nodes[frag as int].children[i] as int].kind is DocumentFragment),
        !is_host_including_inclusive_ancestor(doc, doc.nodes[frag as int].children[i], parent),
{
    lemma_wf_facts(doc);
    lemma_wf_frag_parentless(doc);
    let c = doc.nodes[frag as int].children[i];
    assert(doc.nodes[c as int].parent == Some(frag));
    lemma_hi_self(doc, frag);
    lemma_hi_child(doc, r, frag, frag, c);
    if is_host_including_inclusive_ancestor(doc, c, parent) {
        lemma_hi_trans(doc, r, frag, c, parent);
    }
}

/// A fragment of a well-formed arena has no parent.
proof fn lemma_frag_parentless_at(doc: Document, x: int)
    requires
        wf(doc),
        0 <= x < doc.nodes.len(),
        doc.nodes[x].kind is DocumentFragment,
    ensures
        doc.nodes[x].parent is None,
{
    lemma_wf_frag_parentless(doc);
}

/// A node that is neither `node` nor (if `node` is a fragment) one of its
/// children keeps its parent, or loses it (a fragment is parentless in the
/// arena after "insert" too).
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
proof fn lemma_insert_any_parents(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>, x: int)
    requires
        insert_any_requires(doc, node, parent, child),
        0 <= x < doc.nodes.len(),
        doc.nodes[node as int].kind is DocumentFragment || x != node,
        !(doc.nodes[node as int].kind is DocumentFragment && doc.nodes[node as int].children.contains(x as NodeId)),
    ensures
        ({
            let d2 = insert_any(doc, node, parent, child);
            d2.nodes[x].parent == doc.nodes[x].parent || d2.nodes[x].parent is None
        }),
{
    theorem_insert_any_wf(doc, node, parent, child);
    let d2 = insert_any(doc, node, parent, child);
    if x == node {
        assert(d2.nodes[x].kind == doc.nodes[x].kind);
        lemma_frag_parentless_at(d2, x);
    }
}

/// What "insert" of any node grafts: `node`, or a fragment's children.
pub open spec fn graft_nodes(doc: Document, node: NodeId) -> Seq<NodeId> {
    if doc.nodes[node as int].kind is DocumentFragment {
        doc.nodes[node as int].children
    } else {
        seq![node]
    }
}

/// The premises of [`lemma_graft`] about the arena `d2` after the graft.
pub open spec fn graft_premises(doc: Document, d2: Document, nodes: Seq<NodeId>, parent: NodeId) -> bool {
    &&& d2.nodes.len() == doc.nodes.len()
    &&& forall|x: int| 0 <= x < doc.nodes.len() ==> (#[trigger] d2.nodes[x]).kind == doc.nodes[x].kind
    &&& forall|i: int| 0 <= i < nodes.len() ==> {
        let c = #[trigger] nodes[i];
        &&& valid(doc, c)
        &&& !(doc.nodes[c as int].kind is DocumentFragment)
        &&& !is_host_including_inclusive_ancestor(doc, c, parent)
        &&& d2.nodes[c as int].parent == Some(parent)
    }
    &&& forall|x: int| 0 <= x < doc.nodes.len() && !nodes.contains(x as NodeId) ==> {
        (#[trigger] d2.nodes[x]).parent == doc.nodes[x].parent || d2.nodes[x].parent is None
    }
}

/// "Insert" of a node that is not a fragment is a graft of that node.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
proof fn lemma_graftable_node(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_any_requires(doc, node, parent, child),
        !(doc.nodes[node as int].kind is DocumentFragment),
        !is_host_including_inclusive_ancestor(doc, node, parent),
    ensures
        graft_premises(doc, insert_any(doc, node, parent, child), seq![node], parent),
{
    assert(insert_requires(doc, node, parent, child));
    theorem_insert_wf(doc, node, parent, child);
    lemma_wf_limit(doc);
    assert(insert_any(doc, node, parent, child) == insert(doc, node, parent, child));
    let d2 = insert(doc, node, parent, child);
    assert(seq![node][0] == node);
    assert forall|x: int| 0 <= x < doc.nodes.len() && !(seq![node]).contains(x as NodeId) implies {
        (#[trigger] d2.nodes[x]).parent == doc.nodes[x].parent || d2.nodes[x].parent is None
    } by {
        assert(x != node);
    }
}

/// "Insert" of a fragment is a graft of its children.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
proof fn lemma_graftable_frag(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>, r: Seq<nat>)
    requires
        insert_any_requires(doc, node, parent, child),
        doc.nodes[node as int].kind is DocumentFragment,
        host_ranked(doc, r),
        !is_host_including_inclusive_ancestor(doc, node, parent),
    ensures
        graft_premises(doc, insert_any(doc, node, parent, child), doc.nodes[node as int].children, parent),
{
    theorem_insert_any_wf(doc, node, parent, child);
    lemma_wf_limit(doc);
    let d2 = insert_any(doc, node, parent, child);
    let nodes = doc.nodes[node as int].children;
    assert forall|i: int| 0 <= i < nodes.len() implies {
        let c = #[trigger] nodes[i];
        &&& valid(doc, c)
        &&& !(doc.nodes[c as int].kind is DocumentFragment)
        &&& !is_host_including_inclusive_ancestor(doc, c, parent)
        &&& d2.nodes[c as int].parent == Some(parent)
    } by {
        lemma_frag_child_graftable(doc, r, node, parent, i);
    }
    assert forall|x: int| 0 <= x < doc.nodes.len() && !nodes.contains(x as NodeId) implies {
        (#[trigger] d2.nodes[x]).parent == doc.nodes[x].parent || d2.nodes[x].parent is None
    } by {
        lemma_insert_any_parents(doc, node, parent, child, x);
    }
}

/// "Insert" of any node (a fragment inserts its children) keeps
/// [`host_acyclic`] if `node` is not a host-including inclusive ancestor of
/// `parent`: the grafted nodes are `node`, or a fragment's children (below
/// a fragment that is not an ancestor of `parent`, so none of them is).
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn theorem_insert_any_host_acyclic(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_any_requires(doc, node, parent, child),
        host_acyclic(doc),
        !is_host_including_inclusive_ancestor(doc, node, parent),
    ensures
        host_acyclic(insert_any(doc, node, parent, child)),
{
    lemma_wf_frag_parentless(doc);
    lemma_wf_limit(doc);
    let d2 = insert_any(doc, node, parent, child);
    if doc.nodes[node as int].kind is DocumentFragment {
        let r = lemma_rank_witness(doc);
        lemma_graftable_frag(doc, node, parent, child, r);
        lemma_graft(doc, d2, doc.nodes[node as int].children, parent);
    } else {
        lemma_graftable_node(doc, node, parent, child);
        lemma_graft(doc, d2, seq![node], parent);
    }
}

/// The raw "insert" (the parser's) keeps [`host_acyclic`] when `node` is not
/// a host-including inclusive ancestor of `parent`. [`insert_requires`]'s
/// inclusive-ancestor check is not enough: a template inserted below a node
/// of its own contents passes it, and makes a cycle through the host.
pub proof fn theorem_insert_host_acyclic(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_acyclic_requires(doc, node, parent, child),
    ensures
        host_acyclic(insert(doc, node, parent, child)),
{
    assert(insert_any_requires(doc, node, parent, child));
    theorem_insert_any_host_acyclic(doc, node, parent, child);
    assert(insert_any(doc, node, parent, child) == insert(doc, node, parent, child));
}

/// "Append" keeps [`host_acyclic`], under [`insert_acyclic_requires`].
pub proof fn theorem_append_host_acyclic(doc: Document, parent: NodeId, node: NodeId)
    requires
        insert_acyclic_requires(doc, node, parent, None),
    ensures
        host_acyclic(append(doc, parent, node)),
{
    theorem_insert_host_acyclic(doc, node, parent, None);
}

/// "Insert before" keeps [`host_acyclic`], under [`insert_acyclic_requires`].
pub proof fn theorem_insert_before_host_acyclic(doc: Document, parent: NodeId, node: NodeId, child: NodeId)
    requires
        insert_acyclic_requires(doc, node, parent, Some(child)),
    ensures
        host_acyclic(insert_before(doc, parent, node, child)),
{
    theorem_insert_host_acyclic(doc, node, parent, Some(child));
}

/// DOM §4.2.3† "pre-insert" keeps [`host_acyclic`], with no precondition
/// beyond [`host_acyclic`] of the input: its step 2 refuses a host-including
/// inclusive ancestor of `parent`, and an error leaves the tree as it is.
pub proof fn theorem_pre_insert_host_acyclic(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        pre_insert_requires(doc, node, parent, child),
        host_acyclic(doc),
    ensures
        host_acyclic(pre_insert(doc, node, parent, child)),
{
    if pre_insert_error(doc, node, parent, child) is None {
        lemma_pre_insert_valid(doc, node, parent, child);
        assert(!is_host_including_inclusive_ancestor(doc, node, parent));
        theorem_insert_any_host_acyclic(doc, node, parent, pre_insert_reference(doc, node, child));
    }
}

/// A node that is not a host-including inclusive ancestor of `x` before
/// links are taken away (`d2` has them only as `d` has them, or has none)
/// is not one after it.
proof fn lemma_not_hi_after_removal(d: Document, d2: Document, a: NodeId, x: NodeId)
    requires
        wf(d),
        d2.nodes.len() == d.nodes.len(),
        valid(d, x),
        forall|y: int| 0 <= y < d.nodes.len() ==> {
            &&& (#[trigger] d2.nodes[y]).kind == d.nodes[y].kind
            &&& (d2.nodes[y].parent == d.nodes[y].parent || d2.nodes[y].parent is None)
        },
        !is_host_including_inclusive_ancestor(d, a, x),
    ensures
        !is_host_including_inclusive_ancestor(d2, a, x),
{
    if is_host_including_inclusive_ancestor(d2, a, x) {
        lemma_hw_sub(d, d2, a, x, d.nodes.len());
    }
}

/// DOM §4.2.3† "replace" keeps [`host_acyclic`], with no precondition
/// beyond [`host_acyclic`] of the input: its step 2 refuses a host-including
/// inclusive ancestor of `parent`, and removing `child` first only takes a
/// link away.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn theorem_replace_host_acyclic(doc: Document, child: NodeId, node: NodeId, parent: NodeId)
    requires
        replace_requires(doc, child, node, parent),
        host_acyclic(doc),
    ensures
        host_acyclic(replace(doc, child, node, parent)),
{
    if replace_error(doc, child, node, parent) is None {
        lemma_replace_valid(doc, child, node, parent);
        let d1 = remove(doc, child);
        theorem_remove_host_acyclic(doc, child);
        theorem_remove_keeps_record(doc, child);
        assert(!is_host_including_inclusive_ancestor(doc, node, parent));
        assert forall|y: int| 0 <= y < doc.nodes.len() implies {
            &&& (#[trigger] d1.nodes[y]).kind == doc.nodes[y].kind
            &&& (d1.nodes[y].parent == doc.nodes[y].parent || d1.nodes[y].parent is None)
        } by {
            if y == child {
                assert(d1.nodes[y].parent is None);
            }
        }
        lemma_not_hi_after_removal(doc, d1, node, parent);
        theorem_insert_any_host_acyclic(d1, node, parent, replace_reference(doc, child, node));
    }
}

// ---------------------------------------------------------------------
// replace all

/// A record after removing a prefix of a node's children keeps its kind, and
/// its parent or loses it.
proof fn lemma_removed_prefix_links(d: Document, p: NodeId, k: int, y: int)
    requires
        valid(d, p),
        0 <= y < d.nodes.len(),
    ensures
        removed_prefix(d, p, k)[y].kind == d.nodes[y].kind,
        removed_prefix(d, p, k)[y].parent == d.nodes[y].parent || removed_prefix(d, p, k)[y].parent is None,
{
}

/// Removing all of a node's children only takes parent links away.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
proof fn lemma_remove_children_links(doc: Document, parent: NodeId)
    requires
        wf(doc),
        valid(doc, parent),
    ensures
        remove_children(doc, parent).nodes.len() == doc.nodes.len(),
        forall|y: int| 0 <= y < doc.nodes.len() ==> {
            &&& (#[trigger] remove_children(doc, parent).nodes[y]).kind == doc.nodes[y].kind
            &&& (remove_children(doc, parent).nodes[y].parent == doc.nodes[y].parent || remove_children(doc, parent).nodes[y].parent is None)
        },
{
    let d1 = remove_children(doc, parent);
    let len = doc.nodes[parent as int].children.len();
    lemma_remove_children_n(doc, parent, len);
    assert(children(doc, parent) == doc.nodes[parent as int].children);
    assert(d1.nodes == removed_prefix(doc, parent, len as int));
    assert forall|y: int| 0 <= y < doc.nodes.len() implies {
        &&& (#[trigger] d1.nodes[y]).kind == doc.nodes[y].kind
        &&& (d1.nodes[y].parent == doc.nodes[y].parent || d1.nodes[y].parent is None)
    } by {
        lemma_removed_prefix_links(doc, parent, len as int, y);
    }
}

/// DOM §4.2.3† "replace all" keeps [`host_acyclic`], under what it asks of
/// its caller ([`replace_all_requires`]: `node` is not a host-including
/// inclusive ancestor of `parent`) and [`host_acyclic`] of the input.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn theorem_replace_all_host_acyclic(doc: Document, node: Option<NodeId>, parent: NodeId)
    requires
        replace_all_requires(doc, node, parent),
        host_acyclic(doc),
    ensures
        host_acyclic(replace_all(doc, node, parent)),
{
    lemma_replace_all_valid(doc, node, parent);
    lemma_wf_frag_parentless(doc);
    lemma_wf_limit(doc);
    lemma_remove_children_links(doc, parent);
    let d1 = remove_children(doc, parent);
    lemma_graft(doc, d1, Seq::<NodeId>::empty(), parent);
    if let Some(n) = node {
        lemma_not_hi_after_removal(doc, d1, n, parent);
        theorem_insert_any_host_acyclic(d1, n, parent, None);
    }
}

// ---------------------------------------------------------------------
// reparent children

/// Moving `k` children of `from` to the end of `to`, one by one, keeps
/// [`host_acyclic`] if `from` is not a host-including inclusive ancestor of
/// `to`. (Nor is a child of `from`, and moving a child under `to` does not
/// change the chain above `to`.)
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn lemma_reparent_n_host_acyclic(d: Document, from: NodeId, to: NodeId, k: nat)
    requires
        wf(d),
        host_acyclic(d),
        valid(d, from),
        valid(d, to),
        may_have_children(d.nodes[to as int].kind),
        !is_host_including_inclusive_ancestor(d, from, to),
    ensures
        host_acyclic(reparent_children_n(d, from, to, k)),
    decreases k,
{
    if k == 0 || d.nodes[from as int].children.len() == 0 {
    } else {
        let c = d.nodes[from as int].children[0];
        lemma_wf_facts(d);
        lemma_wf_frag_parentless(d);
        let r = lemma_rank_witness(d);
        assert(valid(d, c));
        assert(d.nodes[c as int].parent == Some(from));
        lemma_child_not_document(d, c);
        lemma_hi_self(d, from);
        lemma_hi_child(d, r, from, from, c);
        assert(!is_host_including_inclusive_ancestor(d, c, to)) by {
            if is_host_including_inclusive_ancestor(d, c, to) {
                lemma_hi_trans(d, r, from, c, to);
            }
        }
        lemma_not_host_not_incl(d, c, to);
        assert(insert_requires(d, c, to, None));
        assert(insert_acyclic_requires(d, c, to, None));
        theorem_insert_wf(d, c, to, None);
        theorem_insert_host_acyclic(d, c, to, None);
        let d1 = append(d, to, c);
        assert(d1 == insert(d, c, to, None));
        lemma_wf_limit(d);
        lemma_hw_unchanged(d, d1, c, from, to, d.nodes.len());
        assert(!is_host_including_inclusive_ancestor(d1, from, to));
        lemma_reparent_n_host_acyclic(d1, from, to, (k - 1) as nat);
    }
}

/// The adoption agency's "take all of the child nodes of furthest block and
/// append them to the element" keeps [`host_acyclic`], under
/// [`reparent_children_acyclic_requires`].
pub proof fn theorem_reparent_children_host_acyclic(doc: Document, from: NodeId, to: NodeId)
    requires
        reparent_children_acyclic_requires(doc, from, to),
    ensures
        host_acyclic(reparent_children(doc, from, to)),
{
    lemma_reparent_n_host_acyclic(doc, from, to, doc.nodes[from as int].children.len());
}

// ---------------------------------------------------------------------
// clone

/// Shallow "clone a node" keeps [`host_acyclic`]: a new parentless node, and
/// for a template its contents, ranked just above it.
pub proof fn theorem_clone_node_host_acyclic(doc: Document, node: NodeId)
    requires
        clone_requires(doc, node),
        host_acyclic(doc),
    ensures
        host_acyclic(clone_node(doc, node).0),
{
    let k = doc.nodes[node as int].kind;
    let ck = clone_kind(k);
    assert(creatable(doc, ck));
    theorem_create_node_host_acyclic(doc, ck);
    let (d1, copy) = create_node(doc, ck);
    if is_template(k) {
        assert(d1.nodes[copy as int].kind is Element);
        theorem_create_template_contents_host_acyclic(d1, copy);
    }
}

/// A new node of a deep clone with a parent has a new node as its parent,
/// which copies the parent of what the node copies.
proof fn lemma_deep_parent(doc: Document, out: Document, src: Seq<NodeId>, t: int) -> (u: int)
    requires
        wf(doc),
        wf(out),
        out.nodes.len() == doc.nodes.len() + src.len(),
        forall|i: int| 0 <= i < doc.nodes.len() ==> #[trigger] out.nodes[i] == doc.nodes[i],
        forall|t: int| 0 <= t < src.len() ==> valid(doc, #[trigger] src[t]),
        forall|t: int| 0 <= t < src.len() ==> #[trigger] deep_copy_children(doc, out, src, t),
        0 <= t < src.len(),
        out.nodes[doc.nodes.len() + t].parent is Some,
    ensures
        0 <= u < src.len(),
        out.nodes[doc.nodes.len() + t].parent == Some((doc.nodes.len() + u) as NodeId),
        doc.nodes[src[t] as int].parent == Some(src[u]),
{
    let b = doc.nodes.len();
    let i = b + t;
    let q = out.nodes[i].parent->Some_0;
    lemma_wf_facts(out);
    lemma_wf_facts(doc);
    lemma_wf_limit(out);
    assert((i as NodeId) as int == i);
    assert(out.nodes[q as int].children.contains(i as NodeId));
    if (q as int) < b {
        assert(out.nodes[q as int] == doc.nodes[q as int]);
        let j = choose|j: int| 0 <= j < doc.nodes[q as int].children.len() && doc.nodes[q as int].children[j] == i as NodeId;
        assert(doc.nodes[q as int].children[j] < b);
    }
    let u = q as int - b;
    assert(deep_copy_children(doc, out, src, u));
    let j = choose|j: int| 0 <= j < out.nodes[q as int].children.len() && out.nodes[q as int].children[j] == i as NodeId;
    theorem_deep_copy_children_facts(doc, out, src, u, j);
    assert(src[t] == doc.nodes[src[u] as int].children[j]);
    u
}

/// A new fragment of a deep clone with a host has a new node as its host,
/// which copies the host of what the fragment copies.
proof fn lemma_deep_host(doc: Document, out: Document, src: Seq<NodeId>, t: int) -> (u: int)
    requires
        wf(doc),
        wf(out),
        out.nodes.len() == doc.nodes.len() + src.len(),
        forall|i: int| 0 <= i < doc.nodes.len() ==> #[trigger] out.nodes[i] == doc.nodes[i],
        forall|t: int| 0 <= t < src.len() ==> valid(doc, #[trigger] src[t]),
        forall|t: int| 0 <= t < src.len() ==> #[trigger] deep_copy_kind(doc, out, src, t),
        0 <= t < src.len(),
        out.nodes[doc.nodes.len() + t].kind is DocumentFragment,
        out.nodes[doc.nodes.len() + t].kind->DocumentFragment_host is Some,
    ensures
        0 <= u < src.len(),
        out.nodes[doc.nodes.len() + t].kind->DocumentFragment_host == Some((doc.nodes.len() + u) as NodeId),
        doc.nodes[src[t] as int].kind is DocumentFragment,
        doc.nodes[src[t] as int].kind->DocumentFragment_host == Some(src[u]),
{
    let b = doc.nodes.len();
    let i = b + t;
    let h = out.nodes[i].kind->DocumentFragment_host->Some_0;
    lemma_wf_facts(out);
    lemma_wf_facts(doc);
    lemma_wf_limit(out);
    assert((i as NodeId) as int == i);
    assert(out.nodes[h as int].kind is Element);
    assert(out.nodes[h as int].kind->Element_template_contents == Some(i as NodeId));
    if (h as int) < b {
        assert(out.nodes[h as int] == doc.nodes[h as int]);
        assert(doc.nodes[h as int].kind->Element_template_contents->Some_0 < b);
    }
    let u = h as int - b;
    assert(deep_copy_kind(doc, out, src, u));
    theorem_deep_copy_kind_fields(doc, out, src, u);
    assert(doc.nodes[src[u] as int].kind is Element);
    u
}

/// The ranking of a deep clone: a new node is ranked as the node it copies.
pub open spec fn deep_rank(doc: Document, src: Seq<NodeId>, r: Seq<nat>) -> Seq<nat> {
    Seq::new(doc.nodes.len() + src.len(), |i: int| if i < doc.nodes.len() {
        r[i]
    } else {
        r[src[i - doc.nodes.len()] as int]
    })
}

/// A new node of a deep clone with a parent ranks above it.
proof fn lemma_deep_parent_ranked(doc: Document, out: Document, src: Seq<NodeId>, r: Seq<nat>, t: int)
    requires
        wf(doc),
        wf(out),
        host_ranked(doc, r),
        out.nodes.len() == doc.nodes.len() + src.len(),
        forall|i: int| 0 <= i < doc.nodes.len() ==> #[trigger] out.nodes[i] == doc.nodes[i],
        forall|t: int| 0 <= t < src.len() ==> valid(doc, #[trigger] src[t]),
        forall|t: int| 0 <= t < src.len() ==> #[trigger] deep_copy_children(doc, out, src, t),
        0 <= t < src.len(),
        out.nodes[doc.nodes.len() + t].parent is Some,
    ensures
        ({
            let q = out.nodes[doc.nodes.len() + t].parent->Some_0;
            deep_rank(doc, src, r)[q as int] < deep_rank(doc, src, r)[doc.nodes.len() + t]
        }),
{
    let b = doc.nodes.len();
    let r2 = deep_rank(doc, src, r);
    let s = src[t];
    let u = lemma_deep_parent(doc, out, src, t);
    assert(valid(doc, src[u]));
    assert(ranked_at(doc, r, s as int));
    theorem_ranked_at_facts(doc, r, s as int);
    assert(r2[b + t] == r[s as int]);
    assert(r2[b + u] == r[src[u] as int]);
}

/// A new fragment of a deep clone with a host ranks above it.
proof fn lemma_deep_host_ranked(doc: Document, out: Document, src: Seq<NodeId>, r: Seq<nat>, t: int)
    requires
        wf(doc),
        wf(out),
        host_ranked(doc, r),
        out.nodes.len() == doc.nodes.len() + src.len(),
        forall|i: int| 0 <= i < doc.nodes.len() ==> #[trigger] out.nodes[i] == doc.nodes[i],
        forall|t: int| 0 <= t < src.len() ==> valid(doc, #[trigger] src[t]),
        forall|t: int| 0 <= t < src.len() ==> #[trigger] deep_copy_kind(doc, out, src, t),
        0 <= t < src.len(),
        out.nodes[doc.nodes.len() + t].kind is DocumentFragment,
        out.nodes[doc.nodes.len() + t].kind->DocumentFragment_host is Some,
    ensures
        ({
            let h = out.nodes[doc.nodes.len() + t].kind->DocumentFragment_host->Some_0;
            deep_rank(doc, src, r)[h as int] < deep_rank(doc, src, r)[doc.nodes.len() + t]
        }),
{
    let b = doc.nodes.len();
    let r2 = deep_rank(doc, src, r);
    let s = src[t];
    let u = lemma_deep_host(doc, out, src, t);
    assert(valid(doc, src[u]));
    assert(ranked_at(doc, r, s as int));
    theorem_ranked_at_facts(doc, r, s as int);
    assert(r2[b + t] == r[s as int]);
    assert(r2[b + u] == r[src[u] as int]);
}

/// A new node of a deep clone is ranked above its parent and its host.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
proof fn lemma_deep_new_ranked(doc: Document, out: Document, src: Seq<NodeId>, r: Seq<nat>, t: int)
    requires
        wf(doc),
        wf(out),
        host_ranked(doc, r),
        out.nodes.len() == doc.nodes.len() + src.len(),
        forall|i: int| 0 <= i < doc.nodes.len() ==> #[trigger] out.nodes[i] == doc.nodes[i],
        forall|t: int| 0 <= t < src.len() ==> valid(doc, #[trigger] src[t]),
        forall|t: int| 0 <= t < src.len() ==> #[trigger] deep_copy_children(doc, out, src, t),
        forall|t: int| 0 <= t < src.len() ==> #[trigger] deep_copy_kind(doc, out, src, t),
        0 <= t < src.len(),
    ensures
        ranked_at(out, deep_rank(doc, src, r), doc.nodes.len() + t),
{
    let b = doc.nodes.len();
    let s = src[t];
    assert(ranked_at(doc, r, s as int));
    theorem_ranked_at_facts(doc, r, s as int);
    if out.nodes[b + t].parent is Some {
        lemma_deep_parent_ranked(doc, out, src, r, t);
    }
    if out.nodes[b + t].kind is DocumentFragment && out.nodes[b + t].kind->DocumentFragment_host is Some {
        lemma_deep_host_ranked(doc, out, src, r, t);
    }
}

/// A deep clone of a [`host_acyclic`] arena is [`host_acyclic`]: each new node
/// is ranked as the node it copies, and an edge between new nodes copies an
/// edge of the source arena.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn theorem_deep_clone_src_host_acyclic(doc: Document, node: NodeId, out: Document, src: Seq<NodeId>)
    requires
        wf(doc),
        host_acyclic(doc),
        wf(out),
        deep_clone_src(doc, node, out, src),
    ensures
        host_acyclic(out),
{
    let b = doc.nodes.len();
    let m = src.len();
    let r = lemma_rank_witness(doc);
    let r2 = deep_rank(doc, src, r);
    assert forall|t: int| 0 <= t < m implies #[trigger] deep_copy_children(doc, out, src, t) by {
        assert(deep_copy_node(doc, out, src, t));
    }
    assert forall|t: int| 0 <= t < m implies #[trigger] deep_copy_kind(doc, out, src, t) by {
        assert(deep_copy_node(doc, out, src, t));
    }
    assert forall|i: int| 0 <= i < b + m implies #[trigger] ranked_at(out, r2, i) by {
        if i < b {
            assert(ranked_at(doc, r, i));
            theorem_ranked_at_facts(doc, r, i);
            assert(out.nodes[i] == doc.nodes[i]);
        } else {
            lemma_deep_new_ranked(doc, out, src, r, i - b);
            let s = src[i - b];
            assert(valid(doc, s));
            assert(ranked_at(doc, r, s as int));
            theorem_ranked_at_facts(doc, r, s as int);
        }
    }
    assert(host_ranked(out, r2));
}

/// A deep clone of a [`host_acyclic`] arena is [`host_acyclic`], as
/// [`deep_clone`] (the relation) says it.
pub proof fn theorem_deep_clone_host_acyclic(doc: Document, node: NodeId, out: Document, copy: NodeId)
    requires
        wf(doc),
        host_acyclic(doc),
        wf(out),
        deep_clone(doc, node, out, copy),
    ensures
        host_acyclic(out),
{
    let src = choose|src: Seq<NodeId>| deep_clone_src(doc, node, out, src);
    theorem_deep_clone_src_host_acyclic(doc, node, out, src);
}

/// `Arena::clone_deep` keeps [`host_acyclic`]: on a copy the arena is the
/// copy of a [`host_acyclic`] one, and on a refusal it is as it was.
pub proof fn theorem_clone_deep_host_acyclic(doc: Document, node: NodeId, out: Document, id: Option<NodeId>)
    requires
        clone_deep_requires(doc, node),
        clone_deep_ensures(doc, node, out, id),
    ensures
        host_acyclic(out),
{
    if let Some(copy) = id {
        theorem_deep_clone_host_acyclic(doc, node, out, copy);
    }
}

} // verus!
