//! The proof that deep "clone a node" (`exec::Arena::clone_deep`, a
//! worklist over the source subtree) meets [`clone_deep_ensures`]. The loop
//! keeps [`deep_inv`]: a well-formed partial copy whose nodes `base ..` are
//! the copies of the nodes listed so far in `order` (breadth first), the
//! ones before the cursor `i` complete, the one at it holding the first `j`
//! of its children, the rest childless. Each lemma here is one step of it.
//!
//! `theorem_deep_clone_leaf` ties the relational spec to the shallow
//! [`clone_node`], the one that was proven first.

#[cfg(verus_only)]
use super::contract::*;
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
// The worklist

/// The worklist after cloning `x` (a source node) off it: `x`, and, if it
/// is a template, its contents, whose copy `clone_node` made as well.
pub open spec fn order_after(d0: Document, order: Seq<NodeId>, x: NodeId) -> Seq<NodeId> {
    if is_template(d0.nodes[x as int].kind) {
        order.push(x).push(d0.nodes[x as int].kind->Element_template_contents->Some_0)
    } else {
        order.push(x)
    }
}

/// The loop invariant of `clone_deep`: `a` is the partial copy of `d0`'s
/// subtree at `node`, `order` the source of each new node, and the cursor is
/// at child `j` of the source of new node `i`.
#[verifier::opaque]
pub open spec fn deep_inv(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>, i: int, j: int) -> bool {
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
    &&& 0 <= i <= n
    &&& forall|t: int| 0 <= t < i ==> #[trigger] deep_copy_children(d0, a, order, t)
    &&& forall|t: int| i < t < n ==> #[trigger] a.nodes[b + t].children.len() == 0
    &&& i < n ==> {
        let s = d0.nodes[order[i] as int];
        &&& 0 <= j <= s.children.len()
        &&& a.nodes[b + i].children.len() == j
        &&& forall|q: int| 0 <= q < j ==> {
            let c = #[trigger] a.nodes[b + i].children[q] as int;
            &&& b <= c < b + n
            &&& order[c - b] == s.children[q]
        }
    }
}

/// What [`deep_inv`] gives the executable loop.
pub proof fn lemma_inv_facts(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>, i: int, j: int)
    requires
        deep_inv(d0, node, a, order, i, j),
    ensures
        wf(a),
        wf(d0),
        order.len() >= 1,
        a.nodes.len() == d0.nodes.len() + order.len(),
        0 <= i <= order.len(),
        forall|k: int| 0 <= k < d0.nodes.len() ==> #[trigger] a.nodes[k] == d0.nodes[k],
        forall|t: int| 0 <= t < order.len() ==> valid(d0, #[trigger] order[t]),
        i < order.len() ==> 0 <= j <= d0.nodes[order[i] as int].children.len(),
{
    reveal(deep_inv);
}

/// A well-formed arena is within the node limit.
pub proof fn lemma_wf_bound(a: Document)
    requires
        wf(a),
    ensures
        a.nodes.len() <= max_nodes(),
{
    let _ = lemma_wf_witness(a);
}

// ---------------------------------------------------------------------
// Facts about the shallow clone, and leaves

/// The copy and the contents `clone_node` makes are new, empty nodes.
pub proof fn lemma_clone_records(doc: Document, node: NodeId)
    requires
        clone_requires(doc, node),
        can_create(doc, clone_count(doc, node)),
    ensures
        ({
            let (d, copy) = clone_node(doc, node);
            &&& d.nodes[copy as int].children.len() == 0
            &&& d.nodes[copy as int].parent is None
            &&& d.nodes[copy as int].wrapper is None
            &&& is_template(doc.nodes[node as int].kind) ==> {
                &&& d.nodes[(copy + 1) as int].children.len() == 0
                &&& d.nodes[(copy + 1) as int].parent is None
                &&& d.nodes[(copy + 1) as int].wrapper is None
            }
        }),
{
    theorem_clone_node_wf(doc, node);
    let k = doc.nodes[node as int].kind;
    let (d1, copy) = create_node(doc, clone_kind(k));
    if is_template(k) {
        let (d2, f) = create_template_contents(d1, copy);
        assert(f == copy + 1);
    }
}

/// A node with no children is an inclusive ancestor only of itself.
pub proof fn lemma_childless_not_ancestor(doc: Document, a: NodeId, x: NodeId)
    requires
        wf(doc),
        valid(doc, a),
        valid(doc, x),
        a != x,
        doc.nodes[a as int].children.len() == 0,
    ensures
        !is_inclusive_ancestor(doc, a, x),
{
    let paths = lemma_wf_witness(doc);
    lemma_ancestor_iff_path(doc, paths, a, x);
    if paths[x as int].contains(a) {
        lemma_path_prefix(doc, paths, a, x);
        lemma_path(doc, paths, x);
        let k = choose|k: int| 0 <= k < paths[x as int].len() && paths[x as int][k] == a && paths[a as int] == paths[x as int].subrange(0, k + 1);
        // `a` is not the last of x's path (that is x), so the path goes on.
        assert(paths[x as int].last() == x);
        assert(k < paths[x as int].len() - 1);
        let z = paths[x as int][k + 1];
        assert(paths[z as int] == paths[x as int].subrange(0, k + 2));
        assert(z < doc.nodes.len());
        lemma_path(doc, paths, z);
        assert(paths[z as int].len() == k + 2);
        match doc.nodes[z as int].parent {
            None => {
                assert(paths[z as int] == seq![z]);
            },
            Some(p) => {
                assert(paths[z as int] == paths[p as int].push(z));
                lemma_path(doc, paths, p);
                assert(paths[p as int] =~= paths[x as int].subrange(0, k + 1));
                assert(paths[p as int].last() == p);
                assert(paths[a as int].last() == a);
                assert(p == a);
                assert(doc.nodes[a as int].children.contains(z));
            },
        }
    }
}

/// Appending a parentless node: the arena is the two records updated.
pub proof fn lemma_append_leaf(doc: Document, p: NodeId, c: NodeId)
    requires
        insert_requires(doc, c, p, None),
        doc.nodes[c as int].parent is None,
        p != c,
    ensures
        append(doc, p, c).nodes == doc.nodes.update(p as int, Node { children: doc.nodes[p as int].children.push(c), ..doc.nodes[p as int] }).update(
            c as int,
            Node { parent: Some(p), ..doc.nodes[c as int] },
        ),
{
    assert(adopt(doc, c) == doc);
}

// ---------------------------------------------------------------------
// The theorems about the relation itself

/// What [`deep_copy_kind`] says of a copy's own fields, stated by cases on
/// its source's kind: an element's copy has the source's name, namespace,
/// prefix and attributes and no form owner, and has template contents
/// exactly when the source has, copying the source's (HTML §4.12.3); a
/// fragment's copy is a fragment (hostless if it is the root); any other
/// node's copy has the same kind. No copy has a wrapper, and the root has
/// no parent.
pub proof fn theorem_deep_copy_kind_fields(doc: Document, out: Document, src: Seq<NodeId>, t: int)
    requires
        0 <= t < src.len(),
        valid(doc, src[t]),
        out.nodes.len() == doc.nodes.len() + src.len(),
        deep_copy_kind(doc, out, src, t),
    ensures
        ({
            let b = doc.nodes.len();
            let s = doc.nodes[src[t] as int];
            let n = out.nodes[b + t];
            &&& n.wrapper is None
            &&& t == 0 ==> n.parent is None
            &&& !(s.kind is Document)
            &&& s.kind is Element ==> {
                &&& n.kind is Element
                &&& n.kind->Element_namespace == s.kind->Element_namespace
                &&& n.kind->Element_prefix == s.kind->Element_prefix
                &&& n.kind->Element_local_name == s.kind->Element_local_name
                &&& n.kind->Element_attributes == s.kind->Element_attributes
                &&& n.kind->Element_form_owner is None
                &&& (s.kind->Element_template_contents is None) == (n.kind->Element_template_contents is None)
                &&& s.kind->Element_template_contents is Some ==> {
                    let c = n.kind->Element_template_contents->Some_0 as int;
                    &&& b <= c < b + src.len()
                    &&& src[c - b] == s.kind->Element_template_contents->Some_0
                }
            }
            &&& s.kind is DocumentFragment ==> {
                &&& n.kind is DocumentFragment
                &&& t == 0 ==> n.kind->DocumentFragment_host is None
            }
            &&& !(s.kind is Element) && !(s.kind is DocumentFragment) ==> n.kind == s.kind
        }),
{
}

/// The children clause says what step 6 does: a copy has as many children
/// as its source, and the `j`th is a new node copying the source's `j`th.
pub proof fn theorem_deep_copy_children_facts(doc: Document, out: Document, src: Seq<NodeId>, t: int, j: int)
    requires
        0 <= t < src.len(),
        valid(doc, src[t]),
        out.nodes.len() == doc.nodes.len() + src.len(),
        deep_copy_children(doc, out, src, t),
        0 <= j < doc.nodes[src[t] as int].children.len(),
    ensures
        ({
            let b = doc.nodes.len();
            let c = out.nodes[b + t].children[j] as int;
            &&& out.nodes[b + t].children.len() == doc.nodes[src[t] as int].children.len()
            &&& b <= c < b + src.len()
            &&& src[c - b] == doc.nodes[src[t] as int].children[j]
        }),
{
}

/// The relation agrees with the shallow clone on a childless, non-template
/// source: the copy (the first new node) is exactly what [`clone_node`]
/// makes, and no existing node changes. (That nothing else is made needs
/// `wf`: a new node must have a parent or a host.)
pub proof fn theorem_deep_clone_leaf(doc: Document, node: NodeId, out: Document, src: Seq<NodeId>)
    requires
        clone_requires(doc, node),
        deep_clone_src(doc, node, out, src),
        doc.nodes[node as int].children.len() == 0,
        !is_template(doc.nodes[node as int].kind),
    ensures
        out.nodes[doc.nodes.len() as int] == clone_node(doc, node).0.nodes[doc.nodes.len() as int],
        forall|i: int| 0 <= i < doc.nodes.len() ==> #[trigger] out.nodes[i] == doc.nodes[i],
{
    let b = doc.nodes.len();
    assert(deep_copy_node(doc, out, src, 0));
    assert(deep_copy_kind(doc, out, src, 0));
    assert(deep_copy_children(doc, out, src, 0));
    theorem_deep_copy_kind_fields(doc, out, src, 0);
    let k = doc.nodes[node as int].kind;
    let n = out.nodes[b as int];
    let c = clone_node(doc, node).0.nodes[b as int];
    assert(src[0] == node);
    assert(n.kind == clone_kind(k)) by {
        match k {
            NodeKind::Element { .. } => {
                assert(k->Element_template_contents is None);
                assert(n.kind->Element_template_contents is None);
            },
            _ => {},
        }
    }
    assert(n.children =~= Seq::<NodeId>::empty());
    assert(c.children =~= Seq::<NodeId>::empty());
    assert(n == c);
}

// ---------------------------------------------------------------------
// The kinds of the new copies

/// The copy `clone_node(a, x)` makes of a source node `x` (and a template's
/// contents) meets [`deep_copy_kind`] as the nodes `a.len() ..` of any
/// arena `e` that has the clone's kinds and wrappers and gives the copy a
/// parent unless it is the root (the first, when `order` is empty).
pub proof fn lemma_new_copy_kind(d0: Document, a: Document, x: NodeId, order: Seq<NodeId>, e: Document)
    requires
        wf(d0),
        a.nodes.len() == d0.nodes.len() + order.len(),
        x < d0.nodes.len(),
        a.nodes[x as int] == d0.nodes[x as int],
        clone_requires(a, x),
        can_create(a, clone_count(a, x)),
        e.nodes.len() == clone_node(a, x).0.nodes.len(),
        forall|k: int| 0 <= k < e.nodes.len() ==> {
            &&& (#[trigger] e.nodes[k]).kind == clone_node(a, x).0.nodes[k].kind
            &&& e.nodes[k].wrapper == clone_node(a, x).0.nodes[k].wrapper
        },
        order.len() == 0 ==> e.nodes[a.nodes.len() as int].parent is None,
        order.len() > 0 ==> e.nodes[a.nodes.len() as int].parent is Some,
    ensures
        ({
            let o2 = order_after(d0, order, x);
            let t = order.len() as int;
            &&& deep_copy_kind(d0, e, o2, t)
            &&& is_template(d0.nodes[x as int].kind) ==> deep_copy_kind(d0, e, o2, t + 1)
        }),
{
    theorem_clone_node_wf(a, x);
    lemma_clone_records(a, x);
    let k = d0.nodes[x as int].kind;
    let o2 = order_after(d0, order, x);
    let t = order.len() as int;
    let b = d0.nodes.len();
    assert(o2[t] == x);
    if is_template(k) {
        // wf(d0): the contents of a template is a fragment, hosted by it.
        let f = k->Element_template_contents->Some_0;
        assert(d0.nodes[x as int].kind is Element);
        assert(f < b);
        assert(d0.nodes[f as int].kind is DocumentFragment);
        assert(o2[t + 1] == f);
        assert(o2.len() == t + 2);
    } else {
        assert(o2.len() == t + 1);
    }
}

// ---------------------------------------------------------------------
// One step of the loop

/// `ch`, the `j`th child of the source of node `i`, is a node that can be
/// cloned: neither the document nor a fragment.
pub proof fn lemma_child_requires(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>, i: int, j: int, ch: NodeId)
    requires
        deep_inv(d0, node, a, order, i, j),
        i < order.len(),
        j < d0.nodes[order[i] as int].children.len(),
        ch == d0.nodes[order[i] as int].children[j],
    ensures
        clone_requires(a, ch),
        a.nodes[ch as int] == d0.nodes[ch as int],
        !(d0.nodes[ch as int].kind is DocumentFragment),
        ch < d0.nodes.len(),
{
    reveal(deep_inv);
    let b = d0.nodes.len();
    let s = order[i];
    // wf(d0): `ch` is a node whose parent is `s`; so it is neither the
    // document nor a fragment.
    assert(d0.nodes[ch as int].parent == Some(s));
    assert(ch < b);
    assert(ch != 0);
    assert(!(d0.nodes[ch as int].kind is Document));
    assert(!(d0.nodes[ch as int].kind is DocumentFragment));
    assert(a.nodes[ch as int] == d0.nodes[ch as int]);
}

/// With room, `ch` is cloned and the copy appended to node `i`.
pub proof fn lemma_step_requires(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>, i: int, j: int, ch: NodeId)
    requires
        deep_inv(d0, node, a, order, i, j),
        i < order.len(),
        j < d0.nodes[order[i] as int].children.len(),
        ch == d0.nodes[order[i] as int].children[j],
        can_create(a, clone_count(a, ch)),
    ensures
        clone_requires(a, ch),
        ({
            let (a1, cc) = clone_node(a, ch);
            insert_requires(a1, cc, (d0.nodes.len() + i) as NodeId, None)
        }),
{
    reveal(deep_inv);
    let b = d0.nodes.len();
    let s = order[i];
    lemma_child_requires(d0, node, a, order, i, j, ch);
    theorem_clone_node_wf(a, ch);
    lemma_clone_records(a, ch);
    let (a1, cc) = clone_node(a, ch);
    let p = (b + i) as NodeId;
    // The source has children, so it may have them, so does its copy.
    assert(d0.nodes[s as int].children.len() > 0);
    assert(may_have_children(d0.nodes[s as int].kind));
    assert(deep_copy_kind(d0, a, order, i));
    assert(a1.nodes[p as int] == a.nodes[p as int]);
    assert(may_have_children(a1.nodes[p as int].kind));
    assert(cc != p);
    lemma_childless_not_ancestor(a1, cc, p);
}

/// What the step does to the arena: only node `p` (the new copy's parent)
/// and the new nodes differ, the copy is appended to `p`, and the new nodes
/// are copies by kind.
#[verifier::rlimit(100)]
pub proof fn lemma_step_frame(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>, i: int, j: int, ch: NodeId)
    requires
        deep_inv(d0, node, a, order, i, j),
        i < order.len(),
        j < d0.nodes[order[i] as int].children.len(),
        ch == d0.nodes[order[i] as int].children[j],
        can_create(a, clone_count(a, ch)),
    ensures
        ({
            let (a1, cc) = clone_node(a, ch);
            let p = (d0.nodes.len() + i) as NodeId;
            let a2 = append(a1, p, cc);
            let n = order.len() as int;
            let o2 = order_after(d0, order, ch);
            &&& cc == a.nodes.len()
            &&& wf(a2)
            &&& a2.nodes.len() == a.nodes.len() + clone_count(a, ch)
            &&& forall|k: int| 0 <= k < a.nodes.len() && k != p ==> #[trigger] a2.nodes[k] == a.nodes[k]
            &&& a2.nodes[p as int].kind == a.nodes[p as int].kind
            &&& a2.nodes[p as int].parent == a.nodes[p as int].parent
            &&& a2.nodes[p as int].wrapper == a.nodes[p as int].wrapper
            &&& a2.nodes[p as int].children == a.nodes[p as int].children.push(cc)
            &&& a2.nodes[cc as int].children.len() == 0
            &&& is_template(d0.nodes[ch as int].kind) ==> a2.nodes[(cc + 1) as int].children.len() == 0
            &&& deep_copy_kind(d0, a2, o2, n)
            &&& is_template(d0.nodes[ch as int].kind) ==> deep_copy_kind(d0, a2, o2, n + 1)
        }),
{
    reveal(deep_inv);
    let b = d0.nodes.len();
    let n = order.len() as int;
    lemma_step_requires(d0, node, a, order, i, j, ch);
    assert(a.nodes[ch as int] == d0.nodes[ch as int]);
    theorem_clone_node_wf(a, ch);
    lemma_clone_records(a, ch);
    let (a1, cc) = clone_node(a, ch);
    let p = (b + i) as NodeId;
    let a2 = append(a1, p, cc);
    assert(cc == a.nodes.len());
    assert(cc == b + n);
    assert(a1.nodes[cc as int].parent is None);
    assert(p != cc);
    theorem_append_wf(a1, p, cc);
    lemma_append_leaf(a1, p, cc);
    lemma_new_copy_kind(d0, a, ch, order, a2);
    assert(a2.nodes.len() == a1.nodes.len());
    assert forall|k: int| 0 <= k < a.nodes.len() && k != p implies #[trigger] a2.nodes[k] == a.nodes[k] by {
        assert(a1.nodes[k] == a.nodes[k]);
    }
}

/// The step keeps the invariant: clone `ch`, append the copy to node `i`.
#[verifier::rlimit(100)]
pub proof fn lemma_step_inv(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>, i: int, j: int, ch: NodeId)
    requires
        deep_inv(d0, node, a, order, i, j),
        i < order.len(),
        j < d0.nodes[order[i] as int].children.len(),
        ch == d0.nodes[order[i] as int].children[j],
        can_create(a, clone_count(a, ch)),
    ensures
        ({
            let (a1, cc) = clone_node(a, ch);
            let p = (d0.nodes.len() + i) as NodeId;
            let a2 = append(a1, p, cc);
            deep_inv(d0, node, a2, order_after(d0, order, ch), i, j + 1)
        }),
{
    let b = d0.nodes.len();
    let n = order.len() as int;
    reveal(deep_inv);
    let s = order[i];
    lemma_step_frame(d0, node, a, order, i, j, ch);
    assert(a.nodes[ch as int] == d0.nodes[ch as int]);
    let (a1, cc) = clone_node(a, ch);
    let p = (b + i) as NodeId;
    let a2 = append(a1, p, cc);
    let o2 = order_after(d0, order, ch);
    let n2 = o2.len() as int;
    assert(cc == b + n);
    assert(n2 == n + clone_count(a, ch));
    // o2 extends order.
    assert forall|x: int| 0 <= x < n implies o2[x] == order[x] by {}
    assert(o2[n] == ch);
    // The invariant, piece by piece.
    assert(a2.nodes.len() == b + n2);
    assert(o2[0] == node);
    assert forall|k: int| 0 <= k < b implies #[trigger] a2.nodes[k] == d0.nodes[k] by {
        assert(a2.nodes[k] == a.nodes[k]);
    }
    assert forall|t: int| 0 <= t < n2 implies valid(d0, #[trigger] o2[t]) by {
        if t < n {
            assert(o2[t] == order[t]);
        } else if t == n {
            assert(o2[t] == ch);
        } else {
            assert(is_template(d0.nodes[ch as int].kind));
            let f = d0.nodes[ch as int].kind->Element_template_contents->Some_0;
            assert(o2[t] == f);
        }
    }
    assert forall|t: int| 0 <= t < n2 implies #[trigger] deep_copy_kind(d0, a2, o2, t) by {
        if t < n {
            // An old node: only node p's children and cc's parent change.
            assert(deep_copy_kind(d0, a, order, t));
            if (b + t) as NodeId == p {
                assert(a2.nodes[p as int].kind == a.nodes[p as int].kind);
            } else {
                assert(a2.nodes[(b + t) as int] == a.nodes[(b + t) as int]);
            }
            assert(a2.nodes[(b + t) as int].kind == a.nodes[(b + t) as int].kind);
            assert(a2.nodes[(b + t) as int].wrapper == a.nodes[(b + t) as int].wrapper);
            assert(a2.nodes[(b + t) as int].parent == a.nodes[(b + t) as int].parent);
            assert(o2[t] == order[t]);
        } else if t == n {
            assert(deep_copy_kind(d0, a2, o2, n));
        } else {
            assert(t == n + 1);
            assert(deep_copy_kind(d0, a2, o2, n + 1));
        }
    }
    assert forall|t: int| 0 <= t < i implies #[trigger] deep_copy_children(d0, a2, o2, t) by {
        assert(deep_copy_children(d0, a, order, t));
        assert(a2.nodes[(b + t) as int] == a.nodes[(b + t) as int]);
        assert(o2[t] == order[t]);
        let sn = d0.nodes[order[t] as int];
        let cn = a.nodes[(b + t) as int];
        assert forall|q: int| 0 <= q < sn.children.len() implies {
            let c = #[trigger] cn.children[q] as int;
            &&& b <= c < b + n2
            &&& o2[c - b] == sn.children[q]
        } by {
            let c = cn.children[q] as int;
            assert(b <= c < b + n);
            assert(o2[c - b] == order[c - b]);
        }
    }
    assert forall|t: int| i < t < n2 implies #[trigger] a2.nodes[b + t].children.len() == 0 by {
        if t < n {
            assert((b + t) as NodeId != p);
            assert(a2.nodes[(b + t) as int] == a.nodes[(b + t) as int]);
        } else if t == n {
            assert(a2.nodes[cc as int].children.len() == 0);
        } else {
            assert(t == n + 1);
            assert(a2.nodes[(cc + 1) as int].children.len() == 0);
        }
    }
    let sn = d0.nodes[s as int];
    let kids2 = a2.nodes[p as int].children;
    assert(kids2 == a.nodes[p as int].children.push(cc));
    assert forall|q: int| 0 <= q < j + 1 implies {
        let c = #[trigger] kids2[q] as int;
        &&& b <= c < b + n2
        &&& o2[c - b] == sn.children[q]
    } by {
        if q < j {
            let c = a.nodes[p as int].children[q] as int;
            assert(kids2[q] == a.nodes[p as int].children[q]);
            assert(b <= c < b + n);
            assert(o2[c - b] == order[c - b]);
        } else {
            assert(kids2[q] == cc);
            assert(o2[cc - b] == ch);
        }
    }
}

/// The cursor passes the end of node `i`'s source's children: node `i` is
/// complete.
pub proof fn lemma_advance(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>, i: int, j: int)
    requires
        deep_inv(d0, node, a, order, i, j),
        i < order.len(),
        j == d0.nodes[order[i] as int].children.len(),
    ensures
        deep_inv(d0, node, a, order, i + 1, 0),
{
    reveal(deep_inv);
    let b = d0.nodes.len();
    let n = order.len() as int;
    lemma_complete(d0, a, order, i);
    assert forall|t: int| 0 <= t < i + 1 implies #[trigger] deep_copy_children(d0, a, order, t) by {
        if t < i {
            assert(deep_copy_children(d0, a, order, t));
        }
    }
    assert forall|t: int| i + 1 < t < n implies #[trigger] a.nodes[b + t].children.len() == 0 by {
        assert(i < t);
    }
    if i + 1 < n {
        let t1 = i + 1;
        assert(a.nodes[b + t1].children.len() == 0);
        assert(0 <= 0 <= d0.nodes[order[t1] as int].children.len());
    }
}

/// With the cursor at the end of node `i`'s source's children, node `i` is
/// complete ([`deep_copy_children`]).
pub proof fn lemma_complete(d0: Document, a: Document, order: Seq<NodeId>, i: int)
    requires
        0 <= i < order.len(),
        a.nodes.len() == d0.nodes.len() + order.len(),
        ({
            let b = d0.nodes.len();
            let s = d0.nodes[order[i] as int];
            let cn = a.nodes[b + i];
            &&& cn.children.len() == s.children.len()
            &&& forall|q: int| 0 <= q < s.children.len() ==> {
                let c = #[trigger] cn.children[q] as int;
                &&& b <= c < b + order.len()
                &&& order[c - b] == s.children[q]
            }
        }),
    ensures
        deep_copy_children(d0, a, order, i),
{
}

/// The loop is over: the invariant at the end of the worklist is the
/// relational spec.
pub proof fn lemma_deep_done(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>, i: int, j: int)
    requires
        deep_inv(d0, node, a, order, i, j),
        i == order.len(),
    ensures
        wf(a),
        deep_clone_src(d0, node, a, order),
        deep_clone(d0, node, a, d0.nodes.len() as NodeId),
{
    reveal(deep_inv);
    assert forall|t: int| 0 <= t < order.len() implies #[trigger] deep_copy_node(d0, a, order, t) by {
        assert(deep_copy_kind(d0, a, order, t));
        assert(deep_copy_children(d0, a, order, t));
    }
    assert(deep_clone_src(d0, node, a, order));
}

/// The first copy: the loop starts with `node`'s copy (and a template's
/// contents) and the cursor at its first child.
pub proof fn lemma_deep_init(d0: Document, node: NodeId)
    requires
        clone_requires(d0, node),
        can_create(d0, clone_count(d0, node)),
    ensures
        deep_inv(d0, node, clone_node(d0, node).0, order_after(d0, Seq::empty(), node), 0, 0),
{
    reveal(deep_inv);
    let b = d0.nodes.len();
    theorem_clone_node_wf(d0, node);
    lemma_clone_records(d0, node);
    let (a, copy) = clone_node(d0, node);
    let order = order_after(d0, Seq::empty(), node);
    assert(a.nodes[copy as int].parent is None);
    lemma_new_copy_kind(d0, d0, node, Seq::empty(), a);
    assert(copy == b);
    let n = order.len() as int;
    assert(order[0] == node);
    assert(n == clone_count(d0, node));
    assert(a.nodes.len() == b + n);
    if is_template(d0.nodes[node as int].kind) {
        let f = d0.nodes[node as int].kind->Element_template_contents->Some_0;
        assert(f < b);
        assert(order[1] == f);
        assert(a.nodes[(b + 1) as int].children.len() == 0);
    }
    assert forall|t: int| 0 <= t < n implies valid(d0, #[trigger] order[t]) by {}
    assert forall|t: int| 0 <= t < n implies #[trigger] deep_copy_kind(d0, a, order, t) by {
        if t == 1 {
            assert(is_template(d0.nodes[node as int].kind));
        }
    }
    assert forall|t: int| 0 < t < n implies #[trigger] a.nodes[b + t].children.len() == 0 by {
        assert(t == 1);
    }
    assert(a.nodes[b as int].children.len() == 0);
    assert forall|k: int| 0 <= k < b implies #[trigger] a.nodes[k] == d0.nodes[k] by {}
}

/// A failed clone's partial copy is the new nodes after the old ones: the
/// arena cut back to the old length is the old arena.
pub proof fn lemma_deep_rollback(d0: Document, node: NodeId, a: Document, order: Seq<NodeId>, i: int, j: int)
    requires
        deep_inv(d0, node, a, order, i, j),
    ensures
        (Document { nodes: a.nodes.take(d0.nodes.len() as int) }) == d0,
{
    reveal(deep_inv);
    assert(a.nodes.take(d0.nodes.len() as int) =~= d0.nodes);
}

} // verus!
