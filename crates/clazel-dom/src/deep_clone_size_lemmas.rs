//! The size of a deep clone: a valid deep clone adds exactly
//! [`subtree_size`] nodes (`theorem_deep_clone_size`), and the worklist of
//! `exec::Arena::clone_deep` is never longer than [`subtree_size`], not
//! even with the next node it would clone (`lemma_step_fits`,
//! `lemma_root_fits`), so it refuses only if the copy cannot fit.
//!
//! All of it rests on a ranking of the arena that grows along every parent
//! edge and every host edge ([`host_ranked`], the precondition
//! [`host_acyclic`] of `clone_deep`). The source of every new node is a
//! host-including descendant of the cloned node, and distinct new nodes have
//! distinct sources (`lemma_image`, `lemma_inj`); with every descendant
//! copied (`lemma_surj`), the new nodes are counted by the descendants
//! (`lemma_count_eq`).
//!
//! The facts about a copy are stated for [`copy_map`], a predicate that
//! holds of every partial copy of the loop (`lemma_inv_copy_map`, from
//! [`deep_inv`]) and of every complete one (`lemma_src_copy_map`, from
//! [`deep_clone_src`] and `wf`): the new nodes are copies by kind, and the
//! children of each new node are a prefix of the copies of its source's.

#[cfg(verus_only)]
use super::contract::*;
#[cfg(verus_only)]
use super::deep_clone_lemmas::*;
#[cfg(verus_only)]
use super::lemmas::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// What `wf` says, as facts

/// The links of a well-formed arena, as facts.
pub proof fn lemma_wf_facts(doc: Document)
    requires
        wf(doc),
    ensures
        forall|i: int, j: int| 0 <= i < doc.nodes.len() && 0 <= j < doc.nodes[i].children.len() ==> {
            let c = (#[trigger] doc.nodes[i].children[j]);
            &&& c < doc.nodes.len()
            &&& doc.nodes[c as int].parent == Some(i as NodeId)
        },
        forall|i: int| 0 <= i < doc.nodes.len() && (#[trigger] doc.nodes[i]).parent is Some ==> {
            let p = doc.nodes[i].parent->Some_0;
            &&& p < doc.nodes.len()
            &&& doc.nodes[p as int].children.contains(i as NodeId)
        },
        forall|i: int| 0 <= i < doc.nodes.len() ==> (#[trigger] doc.nodes[i]).children.no_duplicates(),
        forall|i: int| 0 <= i < doc.nodes.len() && (#[trigger] doc.nodes[i]).kind is DocumentFragment ==> doc.nodes[i].parent is None,
        forall|i: int| 0 <= i < doc.nodes.len() && (#[trigger] doc.nodes[i]).kind is Element && doc.nodes[i].kind->Element_template_contents is Some ==> {
            let f = doc.nodes[i].kind->Element_template_contents->Some_0;
            &&& f < doc.nodes.len()
            &&& doc.nodes[f as int].kind is DocumentFragment
            &&& doc.nodes[f as int].kind->DocumentFragment_host == Some(i as NodeId)
        },
        forall|i: int| 0 <= i < doc.nodes.len() && (#[trigger] doc.nodes[i]).kind is DocumentFragment && doc.nodes[i].kind->DocumentFragment_host is Some ==> {
            let h = doc.nodes[i].kind->DocumentFragment_host->Some_0;
            &&& h < doc.nodes.len()
            &&& doc.nodes[h as int].kind is Element
            &&& doc.nodes[h as int].kind->Element_template_contents == Some(i as NodeId)
        },
{
    let paths = lemma_wf_witness(doc);
    assert(wf_with(doc, paths));
}

// ---------------------------------------------------------------------
// The ranking

/// A ranking of a host-acyclic arena.
pub proof fn lemma_rank_witness(doc: Document) -> (rank: Seq<nat>)
    requires
        host_acyclic(doc),
    ensures
        host_ranked(doc, rank),
{
    choose|rank: Seq<nat>| host_ranked(doc, rank)
}

/// What a ranking says of node `i`, as facts.
pub proof fn theorem_ranked_at_facts(doc: Document, rank: Seq<nat>, i: int)
    requires
        0 <= i < doc.nodes.len(),
        rank.len() == doc.nodes.len(),
        ranked_at(doc, rank, i),
    ensures
        rank[i] < doc.nodes.len(),
        doc.nodes[i].parent is Some ==> {
            let p = doc.nodes[i].parent->Some_0;
            &&& p < doc.nodes.len()
            &&& rank[p as int] < rank[i]
        },
        (doc.nodes[i].kind is DocumentFragment && doc.nodes[i].kind->DocumentFragment_host is Some) ==> {
            let h = doc.nodes[i].kind->DocumentFragment_host->Some_0;
            &&& h < doc.nodes.len()
            &&& rank[h as int] < rank[i]
        },
{
}

/// The step up from `x`: its parent, or, for a parentless fragment, its host.
/// This is the step of [`host_including_within`].
pub open spec fn up(doc: Document, x: NodeId) -> Option<NodeId> {
    match parent(doc, x) {
        Some(p) => Some(p),
        None => match doc.nodes[x as int].kind {
            NodeKind::DocumentFragment { host: Some(h) } => Some(h),
            _ => None,
        },
    }
}

/// A step up lands on a node of the arena with a lower rank.
pub proof fn lemma_up_rank(doc: Document, rank: Seq<nat>, x: NodeId)
    requires
        host_ranked(doc, rank),
        valid(doc, x),
        up(doc, x) is Some,
    ensures
        valid(doc, up(doc, x)->Some_0),
        rank[up(doc, x)->Some_0 as int] < rank[x as int],
{
    assert(ranked_at(doc, rank, x as int));
    theorem_ranked_at_facts(doc, rank, x as int);
}

/// Fuel only helps. (No node is read but through `up`, so no validity is
/// needed: the statement is about the function `host_including_within`.)
pub proof fn lemma_hw_mono(doc: Document, a: NodeId, x: NodeId, f: nat, g: nat)
    requires
        f <= g,
        host_including_within(doc, a, x, f),
    ensures
        host_including_within(doc, a, x, g),
    decreases f,
{
    if x != a {
        assert(f > 0);
        match up(doc, x) {
            Some(y) => {
                lemma_hw_mono(doc, a, y, (f - 1) as nat, (g - 1) as nat);
            },
            None => {},
        }
    }
}

/// With a ranking, fuel beyond the rank of `x` is not needed.
pub proof fn lemma_hw_sat(doc: Document, rank: Seq<nat>, a: NodeId, x: NodeId, f: nat)
    requires
        host_ranked(doc, rank),
        valid(doc, x),
        host_including_within(doc, a, x, f),
    ensures
        host_including_within(doc, a, x, rank[x as int]),
    decreases f,
{
    if x != a {
        assert(f > 0);
        match up(doc, x) {
            Some(y) => {
                lemma_up_rank(doc, rank, x);
                lemma_hw_sat(doc, rank, a, y, (f - 1) as nat);
                lemma_hw_mono(doc, a, y, rank[y as int], (rank[x as int] - 1) as nat);
            },
            None => {},
        }
    }
}

/// [`is_host_including_inclusive_ancestor`] of a non-trivial pair is the
/// same as of the step up: `a` is a host-including inclusive ancestor of
/// `x` (not `a`) iff `x` has a step up and `a` is one of that node.
pub proof fn lemma_hi_unfold(doc: Document, rank: Seq<nat>, a: NodeId, x: NodeId)
    requires
        host_ranked(doc, rank),
        valid(doc, x),
        x != a,
    ensures
        is_host_including_inclusive_ancestor(doc, a, x) <==> (up(doc, x) is Some && is_host_including_inclusive_ancestor(doc, a, up(doc, x)->Some_0)),
{
    let n = doc.nodes.len();
    match up(doc, x) {
        Some(y) => {
            lemma_up_rank(doc, rank, x);
            if is_host_including_inclusive_ancestor(doc, a, x) {
                lemma_hw_mono(doc, a, y, (n - 1) as nat, n);
            }
            if is_host_including_inclusive_ancestor(doc, a, y) {
                lemma_hw_sat(doc, rank, a, y, n);
                assert(ranked_at(doc, rank, x as int));
                theorem_ranked_at_facts(doc, rank, x as int);
                lemma_hw_mono(doc, a, y, rank[y as int], (n - 1) as nat);
            }
        },
        None => {},
    }
}

/// An ancestor ranks no higher than its descendants.
pub proof fn lemma_hi_rank(doc: Document, rank: Seq<nat>, a: NodeId, x: NodeId)
    requires
        host_ranked(doc, rank),
        valid(doc, x),
        is_host_including_inclusive_ancestor(doc, a, x),
    ensures
        valid(doc, a),
        rank[a as int] <= rank[x as int],
    decreases rank[x as int],
{
    if x != a {
        lemma_hi_unfold(doc, rank, a, x);
        lemma_up_rank(doc, rank, x);
        let y = up(doc, x)->Some_0;
        lemma_hi_rank(doc, rank, a, y);
    }
}

/// `c`, a child of `p`, is in the subtree of `a` if `p` is.
pub proof fn lemma_hi_child(doc: Document, rank: Seq<nat>, a: NodeId, p: NodeId, c: NodeId)
    requires
        host_ranked(doc, rank),
        valid(doc, c),
        doc.nodes[c as int].parent == Some(p),
        is_host_including_inclusive_ancestor(doc, a, p),
    ensures
        is_host_including_inclusive_ancestor(doc, a, c),
{
    if c != a {
        lemma_hi_unfold(doc, rank, a, c);
    }
}

/// `f`, the contents of `h`, is in the subtree of `a` if `h` is.
pub proof fn lemma_hi_contents(doc: Document, rank: Seq<nat>, a: NodeId, h: NodeId, f: NodeId)
    requires
        host_ranked(doc, rank),
        valid(doc, f),
        doc.nodes[f as int].parent is None,
        doc.nodes[f as int].kind is DocumentFragment,
        doc.nodes[f as int].kind->DocumentFragment_host == Some(h),
        is_host_including_inclusive_ancestor(doc, a, h),
    ensures
        is_host_including_inclusive_ancestor(doc, a, f),
{
    if f != a {
        lemma_hi_unfold(doc, rank, a, f);
    }
}

/// A node is in its own subtree.
pub proof fn lemma_hi_self(doc: Document, a: NodeId)
    requires
        valid(doc, a),
    ensures
        is_host_including_inclusive_ancestor(doc, a, a),
{
}

// ---------------------------------------------------------------------
// Counting

/// A list without duplicates of nodes of the subtree, all below `k`, is no
/// longer than [`subtree_count`] of `k`.
pub proof fn lemma_count_le(doc: Document, node: NodeId, s: Seq<NodeId>, k: nat)
    requires
        k <= max_nodes(),
        s.no_duplicates(),
        forall|i: int| 0 <= i < s.len() ==> (s[i] as nat) < k && is_host_including_inclusive_ancestor(doc, node, #[trigger] s[i]),
    ensures
        s.len() <= subtree_count(doc, node, k),
    decreases k,
{
    if k == 0 {
        if s.len() > 0 {
            assert((s[0] as nat) < k);
        }
    } else if exists|j: int| 0 <= j < s.len() && s[j] as int == k - 1 {
        let j = choose|j: int| 0 <= j < s.len() && s[j] as int == k - 1;
        lemma_seq_remove(s, j);
        let t = s.remove(j);
        assert(is_host_including_inclusive_ancestor(doc, node, (k - 1) as NodeId));
        assert forall|i: int| 0 <= i < t.len() implies (t[i] as nat) < (k - 1) as nat && is_host_including_inclusive_ancestor(doc, node, #[trigger] t[i]) by {
            let si = if i < j { i } else { i + 1 };
            assert(t[i] == s[si]);
            assert(si != j);
        }
        lemma_count_le(doc, node, t, (k - 1) as nat);
    } else {
        assert forall|i: int| 0 <= i < s.len() implies (s[i] as nat) < (k - 1) as nat && is_host_including_inclusive_ancestor(doc, node, #[trigger] s[i]) by {
            assert((s[i] as nat) < k);
        }
        lemma_count_le(doc, node, s, (k - 1) as nat);
    }
}

/// If the list holds every node of the subtree below `k`, it is as long as
/// [`subtree_count`] of `k`.
pub proof fn lemma_count_eq(doc: Document, node: NodeId, s: Seq<NodeId>, k: nat)
    requires
        k <= max_nodes(),
        s.no_duplicates(),
        forall|i: int| 0 <= i < s.len() ==> (s[i] as nat) < k && is_host_including_inclusive_ancestor(doc, node, #[trigger] s[i]),
        forall|x: NodeId| (x as nat) < k && is_host_including_inclusive_ancestor(doc, node, x) ==> s.contains(x),
    ensures
        s.len() == subtree_count(doc, node, k),
    decreases k,
{
    if k == 0 {
        if s.len() > 0 {
            assert((s[0] as nat) < k);
        }
    } else if exists|j: int| 0 <= j < s.len() && s[j] as int == k - 1 {
        let j = choose|j: int| 0 <= j < s.len() && s[j] as int == k - 1;
        lemma_seq_remove(s, j);
        let t = s.remove(j);
        assert(is_host_including_inclusive_ancestor(doc, node, (k - 1) as NodeId));
        assert forall|i: int| 0 <= i < t.len() implies (t[i] as nat) < (k - 1) as nat && is_host_including_inclusive_ancestor(doc, node, #[trigger] t[i]) by {
            let si = if i < j { i } else { i + 1 };
            assert(t[i] == s[si]);
            assert(si != j);
        }
        assert forall|x: NodeId| (x as nat) < (k - 1) as nat && is_host_including_inclusive_ancestor(doc, node, x) implies t.contains(x) by {
            assert(s.contains(x));
            assert(x != s[j]);
        }
        lemma_count_eq(doc, node, t, (k - 1) as nat);
    } else {
        assert forall|i: int| 0 <= i < s.len() implies (s[i] as nat) < (k - 1) as nat && is_host_including_inclusive_ancestor(doc, node, #[trigger] s[i]) by {
            assert((s[i] as nat) < k);
        }
        assert(!is_host_including_inclusive_ancestor(doc, node, (k - 1) as NodeId)) by {
            if is_host_including_inclusive_ancestor(doc, node, (k - 1) as NodeId) {
                assert(s.contains((k - 1) as NodeId));
                let j = choose|j: int| 0 <= j < s.len() && s[j] == (k - 1) as NodeId;
                assert(s[j] as int == k - 1);
                assert(false);
            }
        }
        assert forall|x: NodeId| (x as nat) < (k - 1) as nat && is_host_including_inclusive_ancestor(doc, node, x) implies s.contains(x) by {}
        lemma_count_eq(doc, node, s, (k - 1) as nat);
    }
}

/// A list without duplicates of nodes of the subtree is no longer than
/// [`subtree_size`].
pub proof fn lemma_size_ge(doc: Document, node: NodeId, s: Seq<NodeId>)
    requires
        doc.nodes.len() <= max_nodes(),
        s.no_duplicates(),
        forall|i: int| 0 <= i < s.len() ==> valid(doc, #[trigger] s[i]) && is_host_including_inclusive_ancestor(doc, node, s[i]),
    ensures
        s.len() <= subtree_size(doc, node),
{
    lemma_count_le(doc, node, s, doc.nodes.len());
}

// ---------------------------------------------------------------------
// The copy map

/// The children of new node `k` are a prefix of the copies of its source's
/// children, in order.
pub open spec fn children_prefix(d0: Document, a: Document, order: Seq<NodeId>, k: int) -> bool {
    let b = d0.nodes.len();
    let s = d0.nodes[order[k] as int];
    let cn = a.nodes[b + k];
    &&& cn.children.len() <= s.children.len()
    &&& forall|q: int| 0 <= q < cn.children.len() ==> {
        let c = #[trigger] cn.children[q] as int;
        &&& b <= c < b + order.len()
        &&& order[c - b] == s.children[q]
    }
}

/// `a` is `d0` with the nodes `d0.nodes.len() ..` added, each a copy by
/// kind of the node of `order` at its offset, whose children are a prefix of
/// the copies of its source's: what a partial copy and a complete one have
/// in common.
pub open spec fn copy_map(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>) -> bool {
    let b = d0.nodes.len();
    let n = order.len();
    &&& wf(d0)
    &&& wf(a)
    &&& n >= 1
    &&& a.nodes.len() == b + n
    &&& order[0] == node
    &&& forall|k: int| 0 <= k < b ==> #[trigger] a.nodes[k] == d0.nodes[k]
    &&& forall|t: int| 0 <= t < n ==> valid(d0, #[trigger] order[t])
    &&& forall|t: int| 0 <= t < n ==> #[trigger] deep_copy_kind(d0, a, order, t)
    &&& forall|k: int| 0 <= k < n ==> #[trigger] children_prefix(d0, a, order, k)
}

/// A partial copy of the loop is a [`copy_map`].
pub proof fn lemma_inv_copy_map(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>, i: int, j: int)
    requires
        deep_inv(d0, node, a, order, i, j),
    ensures
        copy_map(d0, node, a, order),
{
    reveal(deep_inv);
    let b = d0.nodes.len();
    let n = order.len() as int;
    assert forall|k: int| 0 <= k < n implies #[trigger] children_prefix(d0, a, order, k) by {
        if k < i {
            assert(deep_copy_children(d0, a, order, k));
        } else if k == i {
        } else {
            assert(a.nodes[b + k].children.len() == 0);
        }
    }
}

/// A complete copy is a [`copy_map`], with every child copied.
pub proof fn lemma_src_copy_map(doc: Document, node: NodeId, out: Document, src: Seq<NodeId>)
    requires
        wf(doc),
        wf(out),
        deep_clone_src(doc, node, out, src),
    ensures
        copy_map(doc, node, out, src),
        forall|k: int| 0 <= k < src.len() ==> #[trigger] deep_copy_children(doc, out, src, k),
{
    let b = doc.nodes.len();
    assert forall|t: int| 0 <= t < src.len() implies #[trigger] deep_copy_kind(doc, out, src, t) by {
        assert(deep_copy_node(doc, out, src, t));
    }
    assert forall|k: int| 0 <= k < src.len() implies #[trigger] deep_copy_children(doc, out, src, k) by {
        assert(deep_copy_node(doc, out, src, k));
    }
    assert forall|k: int| 0 <= k < src.len() implies #[trigger] children_prefix(doc, out, src, k) by {
        assert(deep_copy_children(doc, out, src, k));
    }
}

/// Every new node but the first hangs under a new node, which is the copy
/// of its source's parent (or host): node `t` of the copy is the `q`th child
/// of node `u` (the source of `t` is the `q`th child of the source of `u`),
/// or the template contents of node `u` (the source of `t` is the contents
/// of the source of `u`).
pub proof fn lemma_up_copy(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>, t: int) -> (u: int)
    requires
        copy_map(d0, node, a, order),
        1 <= t < order.len(),
    ensures
        0 <= u < order.len(),
        up(d0, order[t]) == Some(order[u]),
        d0.nodes[order[t] as int].parent is Some ==> exists|q: int| 0 <= q < a.nodes[d0.nodes.len() + u].children.len()
            && a.nodes[d0.nodes.len() + u].children[q] == (d0.nodes.len() + t) as NodeId && d0.nodes[order[u] as int].children[q] == order[t],
        d0.nodes[order[t] as int].parent is None ==> {
            &&& a.nodes[d0.nodes.len() + u].kind is Element
            &&& a.nodes[d0.nodes.len() + u].kind->Element_template_contents == Some((d0.nodes.len() + t) as NodeId)
            &&& d0.nodes[order[t] as int].kind is DocumentFragment
            &&& d0.nodes[order[t] as int].kind->DocumentFragment_host == Some(order[u])
        },
{
    let b = d0.nodes.len();
    let n = order.len() as int;
    lemma_wf_facts(d0);
    lemma_wf_facts(a);
    assert(deep_copy_kind(d0, a, order, t));
    let nt = a.nodes[b + t];
    if nt.parent is Some {
        let p = nt.parent->Some_0;
        assert(a.nodes[p as int].children.contains((b + t) as NodeId));
        if p < b {
            assert(a.nodes[p as int] == d0.nodes[p as int]);
            let j = choose|j: int| 0 <= j < d0.nodes[p as int].children.len() && d0.nodes[p as int].children[j] == (b + t) as NodeId;
            assert(d0.nodes[p as int].children[j] < b);
        }
        let u = p as int - b;
        assert(0 <= u < n);
        assert(b + u == p);
        let q = choose|q: int| 0 <= q < a.nodes[p as int].children.len() && a.nodes[p as int].children[q] == (b + t) as NodeId;
        assert(children_prefix(d0, a, order, u));
        let s = d0.nodes[order[u] as int];
        assert(order[t] == s.children[q]);
        let x = order[t];
        assert(d0.nodes[x as int].parent == Some(order[u]));
        assert(up(d0, x) == Some(order[u]));
        u
    } else {
        assert(nt.kind is DocumentFragment && nt.kind->DocumentFragment_host is Some);
        let h = nt.kind->DocumentFragment_host->Some_0;
        assert(a.nodes[h as int].kind is Element);
        assert(a.nodes[h as int].kind->Element_template_contents == Some((b + t) as NodeId));
        if h < b {
            assert(a.nodes[h as int] == d0.nodes[h as int]);
            assert(d0.nodes[h as int].kind->Element_template_contents->Some_0 < b);
        }
        let u = h as int - b;
        assert(0 <= u < n);
        assert(b + u == h);
        assert(deep_copy_kind(d0, a, order, u));
        theorem_deep_copy_kind_fields(d0, a, order, u);
        let s = d0.nodes[order[u] as int];
        assert(s.kind is Element);
        assert(s.kind->Element_template_contents is Some);
        let x = order[t];
        assert(x == s.kind->Element_template_contents->Some_0);
        assert(d0.nodes[x as int].kind is DocumentFragment);
        assert(d0.nodes[x as int].kind->DocumentFragment_host == Some(order[u]));
        assert(d0.nodes[x as int].parent is None);
        assert(up(d0, x) == Some(order[u]));
        u
    }
}

/// Every new node copies a node of the subtree of `node`.
pub proof fn lemma_image(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>, rank: Seq<nat>, t: int)
    requires
        copy_map(d0, node, a, order),
        host_ranked(d0, rank),
        0 <= t < order.len(),
    ensures
        is_host_including_inclusive_ancestor(d0, node, order[t]),
    decreases rank[order[t] as int],
{
    let x = order[t];
    if t == 0 {
        lemma_hi_self(d0, node);
    } else {
        let u = lemma_up_copy(d0, node, a, order, t);
        let y = order[u];
        assert(valid(d0, x) && valid(d0, y));
        lemma_up_rank(d0, rank, x);
        lemma_image(d0, node, a, order, rank, u);
        lemma_wf_facts(d0);
        if d0.nodes[x as int].parent is Some {
            assert(d0.nodes[x as int].parent == Some(y));
            lemma_hi_child(d0, rank, node, y, x);
        } else {
            lemma_hi_contents(d0, rank, node, y, x);
        }
    }
}

/// No new node but the first copies `node` itself.
pub proof fn lemma_only_first_copies_node(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>, rank: Seq<nat>, t: int)
    requires
        copy_map(d0, node, a, order),
        host_ranked(d0, rank),
        1 <= t < order.len(),
    ensures
        order[t] != node,
{
    let u = lemma_up_copy(d0, node, a, order, t);
    lemma_image(d0, node, a, order, rank, u);
    let x = order[t];
    assert(valid(d0, x) && valid(d0, order[u]));
    if x == node {
        lemma_up_rank(d0, rank, x);
        lemma_hi_rank(d0, rank, node, order[u]);
    }
}

/// Distinct new nodes copy distinct nodes.
pub proof fn lemma_inj(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>, rank: Seq<nat>, t1: int, t2: int)
    requires
        copy_map(d0, node, a, order),
        host_ranked(d0, rank),
        0 <= t1 < order.len(),
        0 <= t2 < order.len(),
        order[t1] == order[t2],
    ensures
        t1 == t2,
    decreases rank[order[t1] as int],
{
    let b = d0.nodes.len();
    if t1 == 0 && t2 != 0 {
        lemma_only_first_copies_node(d0, node, a, order, rank, t2);
    } else if t2 == 0 && t1 != 0 {
        lemma_only_first_copies_node(d0, node, a, order, rank, t1);
    } else if t1 != 0 && t2 != 0 {
        let x = order[t1];
        let u1 = lemma_up_copy(d0, node, a, order, t1);
        let u2 = lemma_up_copy(d0, node, a, order, t2);
        assert(valid(d0, x));
        lemma_up_rank(d0, rank, x);
        assert(order[u1] == order[u2]);
        lemma_inj(d0, node, a, order, rank, u1, u2);
        lemma_wf_facts(d0);
        if d0.nodes[x as int].parent is Some {
            let q1 = choose|q: int| 0 <= q < a.nodes[b + u1].children.len() && a.nodes[b + u1].children[q] == (b + t1) as NodeId
                && d0.nodes[order[u1] as int].children[q] == order[t1];
            let q2 = choose|q: int| 0 <= q < a.nodes[b + u2].children.len() && a.nodes[b + u2].children[q] == (b + t2) as NodeId
                && d0.nodes[order[u2] as int].children[q] == order[t2];
            let kids = d0.nodes[order[u1] as int].children;
            assert(kids.no_duplicates());
            assert(children_prefix(d0, a, order, u1));
            assert(q1 < kids.len() && q2 < kids.len());
            assert(kids[q1] == kids[q2]);
            assert(q1 == q2);
        }
    }
}

/// The copies' sources are distinct.
pub proof fn lemma_order_nodups(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>, rank: Seq<nat>)
    requires
        copy_map(d0, node, a, order),
        host_ranked(d0, rank),
    ensures
        order.no_duplicates(),
{
    assert forall|i: int, j: int| 0 <= i < order.len() && 0 <= j < order.len() && i != j implies order[i] != order[j] by {
        if order[i] == order[j] {
            lemma_inj(d0, node, a, order, rank, i, j);
        }
    }
}

/// In a complete copy, every node of the subtree of `node` has a copy.
pub proof fn lemma_surj(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>, rank: Seq<nat>, x: NodeId) -> (t: int)
    requires
        copy_map(d0, node, a, order),
        forall|k: int| 0 <= k < order.len() ==> #[trigger] deep_copy_children(d0, a, order, k),
        host_ranked(d0, rank),
        valid(d0, x),
        is_host_including_inclusive_ancestor(d0, node, x),
    ensures
        0 <= t < order.len(),
        order[t] == x,
    decreases rank[x as int],
{
    let b = d0.nodes.len();
    if x == node {
        0
    } else {
        lemma_hi_unfold(d0, rank, node, x);
        lemma_up_rank(d0, rank, x);
        let y = up(d0, x)->Some_0;
        let ty = lemma_surj(d0, node, a, order, rank, y);
        lemma_wf_facts(d0);
        assert(order[ty] == y);
        assert(deep_copy_kind(d0, a, order, ty));
        assert(deep_copy_children(d0, a, order, ty));
        if d0.nodes[x as int].parent is Some {
            assert(d0.nodes[x as int].parent == Some(y));
            assert(d0.nodes[y as int].children.contains(x));
            let q = choose|q: int| 0 <= q < d0.nodes[y as int].children.len() && d0.nodes[y as int].children[q] == x;
            let c = a.nodes[b + ty].children[q] as int;
            assert(order[c - b] == x);
            c - b
        } else {
            assert(d0.nodes[x as int].kind is DocumentFragment);
            assert(d0.nodes[x as int].kind->DocumentFragment_host == Some(y));
            assert(d0.nodes[y as int].kind->Element_template_contents == Some(x));
            theorem_deep_copy_kind_fields(d0, a, order, ty);
            let c = a.nodes[b + ty].kind->Element_template_contents->Some_0 as int;
            assert(order[c - b] == x);
            c - b
        }
    }
}

/// A well-formed arena that grew by [`subtree_size`] nodes is within the node
/// limit, so a refusal of [`clone_deep_ensures`] is exactly the case where
/// the copy does not fit: `clone_deep` refuses only if the arena cannot hold
/// [`subtree_size`] more nodes, and, since it then cannot be well formed,
/// refuses whenever it cannot.
pub proof fn theorem_clone_deep_refuses_exactly_when_full(doc: Document, node: NodeId, out: Document, id: Option<NodeId>)
    requires
        clone_deep_requires(doc, node),
        clone_deep_ensures(doc, node, out, id),
    ensures
        id is None <==> !can_create(doc, subtree_size(doc, node)),
{
    match id {
        Some(copy) => {
            lemma_wf_bound_dom(out);
        },
        None => {},
    }
}

/// A refusal needs the arena to be too full for the copy.
pub proof fn theorem_clone_deep_refused_only_if_full(doc: Document, node: NodeId, out: Document)
    requires
        clone_deep_refused(doc, node, out),
    ensures
        doc.nodes.len() + subtree_size(doc, node) > max_nodes(),
{
}

/// A valid deep clone meets the size clause of the contract.
pub proof fn theorem_deep_clone_grew(doc: Document, node: NodeId, out: Document, src: Seq<NodeId>)
    requires
        wf(doc),
        wf(out),
        host_acyclic(doc),
        deep_clone_src(doc, node, out, src),
    ensures
        clone_deep_grew(doc, node, out),
{
    theorem_deep_clone_size(doc, node, out, src);
}

/// The size clause says the arena grew by exactly [`subtree_size`] nodes.
pub proof fn theorem_clone_deep_grew_means(doc: Document, node: NodeId, out: Document)
    requires
        clone_deep_grew(doc, node, out),
    ensures
        out.nodes.len() == doc.nodes.len() + subtree_size(doc, node),
{
}

/// A well-formed arena is within the node limit.
pub proof fn lemma_wf_bound_dom(a: Document)
    requires
        wf(a),
    ensures
        a.nodes.len() <= max_nodes(),
{
    let _ = lemma_wf_witness(a);
}

// ---------------------------------------------------------------------
// The worklist never outgrows the subtree

/// Pushing a node not in the list keeps it free of duplicates.
pub proof fn lemma_push_nodups(s: Seq<NodeId>, x: NodeId)
    requires
        s.no_duplicates(),
        forall|k: int| 0 <= k < s.len() ==> s[k] != x,
    ensures
        s.push(x).no_duplicates(),
{
    let t = s.push(x);
    assert forall|i: int, j: int| 0 <= i < t.len() && 0 <= j < t.len() && i != j implies t[i] != t[j] by {
        if i < s.len() && j < s.len() {
            assert(t[i] == s[i] && t[j] == s[j]);
        } else if i < s.len() {
            assert(t[i] == s[i] && t[j] == x);
        } else {
            assert(t[j] == s[j] && t[i] == x);
        }
    }
}

/// The child `ch` the loop is about to clone (the `j`th of the source of node
/// `i`) is in the subtree, and no node listed so far copies it: it is the
/// `j`th child of its parent, whose copy has only `j` children so far.
pub proof fn lemma_unlisted_child(
    d0: Document,
    node: NodeId,
    a: Document,
    order: Seq<NodeId>,
    rank: Seq<nat>,
    i: int,
    j: int,
    ch: NodeId,
)
    requires
        copy_map(d0, node, a, order),
        host_ranked(d0, rank),
        order.no_duplicates(),
        0 <= i < order.len(),
        j < d0.nodes[order[i] as int].children.len(),
        ch == d0.nodes[order[i] as int].children[j],
        a.nodes[d0.nodes.len() + i].children.len() == j,
    ensures
        valid(d0, ch),
        d0.nodes[ch as int].parent == Some(order[i]),
        is_host_including_inclusive_ancestor(d0, node, ch),
        forall|k: int| 0 <= k < order.len() ==> order[k] != ch,
{
    lemma_wf_facts(d0);
    let b = d0.nodes.len();
    let n = order.len() as int;
    let s = order[i];
    assert(valid(d0, s));
    assert(d0.nodes[s as int].children[j] == ch);
    assert(up(d0, ch) == Some(s));
    lemma_image(d0, node, a, order, rank, i);
    lemma_hi_child(d0, rank, node, s, ch);
    assert forall|k: int| 0 <= k < n implies order[k] != ch by {
        if order[k] == ch {
            if k == 0 {
                lemma_up_rank(d0, rank, ch);
                lemma_hi_rank(d0, rank, node, s);
            } else {
                let u = lemma_up_copy(d0, node, a, order, k);
                assert(order[u] == s);
                assert(u == i);
                let q = choose|q: int| 0 <= q < a.nodes[b + u].children.len() && a.nodes[b + u].children[q] == (b + k) as NodeId
                    && d0.nodes[order[u] as int].children[q] == order[k];
                let kids = d0.nodes[s as int].children;
                assert(kids.no_duplicates());
                assert(q < j);
                assert(kids[q] == kids[j]);
                assert(false);
            }
        }
    }
}

/// The contents `f` of the template `ch` that the loop is about to clone is
/// in the subtree, and no node listed so far copies it, nor is it `ch`.
pub proof fn lemma_unlisted_contents(
    d0: Document,
    node: NodeId,
    a: Document,
    order: Seq<NodeId>,
    rank: Seq<nat>,
    ch: NodeId,
)
    requires
        copy_map(d0, node, a, order),
        host_ranked(d0, rank),
        valid(d0, ch),
        d0.nodes[ch as int].parent is Some,
        is_host_including_inclusive_ancestor(d0, node, ch),
        forall|k: int| 0 <= k < order.len() ==> order[k] != ch,
        is_template(d0.nodes[ch as int].kind),
    ensures
        ({
            let f = d0.nodes[ch as int].kind->Element_template_contents->Some_0;
            &&& valid(d0, f)
            &&& is_host_including_inclusive_ancestor(d0, node, f)
            &&& f != ch
            &&& forall|k: int| 0 <= k < order.len() ==> order[k] != f
        }),
{
    lemma_wf_facts(d0);
    let f = d0.nodes[ch as int].kind->Element_template_contents->Some_0;
    assert(valid(d0, f));
    assert(d0.nodes[f as int].kind is DocumentFragment);
    assert(d0.nodes[f as int].kind->DocumentFragment_host == Some(ch));
    assert(d0.nodes[f as int].parent is None);
    lemma_hi_contents(d0, rank, node, ch, f);
    assert(f != ch);
    assert forall|k: int| 0 <= k < order.len() implies order[k] != f by {
        if order[k] == f {
            if k == 0 {
                lemma_up_rank(d0, rank, f);
                lemma_hi_rank(d0, rank, node, ch);
            } else {
                let u = lemma_up_copy(d0, node, a, order, k);
                assert(up(d0, f) == Some(ch));
                assert(order[u] == ch);
                assert(order[u] != ch);
            }
        }
    }
}

/// The worklist after cloning `ch`, the `j`th child of the source of node
/// `i`, off it ([`order_after`]) still lists distinct nodes of the subtree:
/// so the nodes `clone_deep` has made plus the ones it is about to make are
/// no more than [`subtree_size`]. This is why a clone that does not fit
/// cannot fit at all.
pub proof fn lemma_step_fits(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>, i: int, j: int, ch: NodeId)
    requires
        deep_inv(d0, node, a, order, i, j),
        host_acyclic(d0),
        i < order.len(),
        j < d0.nodes[order[i] as int].children.len(),
        ch == d0.nodes[order[i] as int].children[j],
    ensures
        order.len() + clone_count(d0, ch) <= subtree_size(d0, node),
{
    lemma_inv_copy_map(d0, node, a, order, i, j);
    reveal(deep_inv);
    let rank = lemma_rank_witness(d0);
    lemma_order_nodups(d0, node, a, order, rank);
    lemma_wf_bound_dom(d0);
    assert(a.nodes[d0.nodes.len() + i].children.len() == j);
    lemma_unlisted_child(d0, node, a, order, rank, i, j, ch);
    let n = order.len() as int;
    let o2 = order_after(d0, order, ch);
    assert(o2.len() == n + clone_count(d0, ch));
    assert forall|x: int| 0 <= x < n implies o2[x] == order[x] by {}
    lemma_push_nodups(order, ch);
    assert forall|x: int| 0 <= x < n implies valid(d0, #[trigger] order[x]) && is_host_including_inclusive_ancestor(d0, node, order[x]) by {
        lemma_image(d0, node, a, order, rank, x);
    }
    if is_template(d0.nodes[ch as int].kind) {
        lemma_unlisted_contents(d0, node, a, order, rank, ch);
        let f = d0.nodes[ch as int].kind->Element_template_contents->Some_0;
        assert(o2 == order.push(ch).push(f));
        assert forall|k: int| 0 <= k < n + 1 implies order.push(ch)[k] != f by {
            if k < n {
                assert(order.push(ch)[k] == order[k]);
            }
        }
        lemma_push_nodups(order.push(ch), f);
    }
    assert forall|x: int| 0 <= x < o2.len() implies valid(d0, #[trigger] o2[x]) && is_host_including_inclusive_ancestor(d0, node, o2[x]) by {
        if x >= n {
            let f = d0.nodes[ch as int].kind->Element_template_contents->Some_0;
            if x == n {
                assert(o2[x] == ch);
            } else {
                assert(o2[x] == f);
            }
        }
    }
    lemma_size_ge(d0, node, o2);
}

/// The first copy (a template and its contents) is no more than
/// [`subtree_size`].
pub proof fn lemma_root_fits(d0: Document, node: NodeId)
    requires
        clone_deep_requires(d0, node),
    ensures
        clone_count(d0, node) <= subtree_size(d0, node),
{
    let rank = lemma_rank_witness(d0);
    lemma_wf_bound_dom(d0);
    lemma_wf_facts(d0);
    let o = order_after(d0, Seq::empty(), node);
    lemma_hi_self(d0, node);
    if is_template(d0.nodes[node as int].kind) {
        let f = d0.nodes[node as int].kind->Element_template_contents->Some_0;
        assert(o[1] == f);
        assert(valid(d0, f));
        assert(d0.nodes[f as int].kind is DocumentFragment);
        assert(d0.nodes[f as int].kind->DocumentFragment_host == Some(node));
        assert(d0.nodes[f as int].parent is None);
        lemma_hi_contents(d0, rank, node, node, f);
        assert(f != node);
    }
    assert(o.no_duplicates());
    assert forall|x: int| 0 <= x < o.len() implies valid(d0, #[trigger] o[x]) && is_host_including_inclusive_ancestor(d0, node, o[x]) by {}
    lemma_size_ge(d0, node, o);
}

/// A valid deep clone adds exactly [`subtree_size`] nodes: the copy is the
/// unfolding of the host-including subtree of `node`, and nothing else. (The
/// relation alone, without `wf(out)`, would leave room for unreachable new
/// nodes; it is `wf(out)` that rules them out.)
pub proof fn theorem_deep_clone_size(doc: Document, node: NodeId, out: Document, src: Seq<NodeId>)
    requires
        wf(doc),
        wf(out),
        host_acyclic(doc),
        deep_clone_src(doc, node, out, src),
    ensures
        src.len() == subtree_size(doc, node),
        out.nodes.len() == doc.nodes.len() + subtree_size(doc, node),
{
    lemma_src_copy_map(doc, node, out, src);
    let rank = lemma_rank_witness(doc);
    lemma_order_nodups(doc, node, out, src, rank);
    lemma_wf_bound_dom(doc);
    assert forall|i: int| 0 <= i < src.len() implies (src[i] as nat) < doc.nodes.len() && is_host_including_inclusive_ancestor(doc, node, #[trigger] src[i]) by {
        lemma_image(doc, node, out, src, rank, i);
    }
    assert forall|x: NodeId| (x as nat) < doc.nodes.len() && is_host_including_inclusive_ancestor(doc, node, x) implies src.contains(x) by {
        let t = lemma_surj(doc, node, out, src, rank, x);
        assert(src[t] == x);
    }
    lemma_count_eq(doc, node, src, doc.nodes.len());
}

} // verus!
