//! The helpers of the transcription keep the host invariant
//! (`host::host_inv`): the changes of the stack of open elements, and the
//! guarded DOM calls under `host::insert_keeps_host` and
//! `host::reparent_keeps_host`. A node just created is `host::low`, which
//! gives `host::insert_keeps_host` for its insertion below an older node
//! ([`lemma_low_keeps`]): the "easy sites".

#[cfg(verus_only)]
use super::hi::*;
#[cfg(verus_only)]
use crate::host::*;
#[cfg(verus_only)]
use crate::reachable::doc::*;
#[cfg(verus_only)]
use crate::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// What the invariant says

/// What [`host_inv`] says.
pub proof fn lemma_host_inv(p: Parser)
    requires
        host_inv(p),
    ensures
        dom::host_acyclic(p.doc),
        !p.stopped ==> stack_ordered_of(p.doc, p.open) && redirect_above_of(p.doc, p.open, p.redirect),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    reveal(host_inv_of);
}

/// [`host_inv`] from its parts.
pub proof fn lemma_host_inv_intro(p: Parser)
    requires
        dom::host_acyclic(p.doc),
        !p.stopped ==> stack_ordered_of(p.doc, p.open) && redirect_above_of(p.doc, p.open, p.redirect),
    ensures
        host_inv(p),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    reveal(host_inv_of);
}

/// A stopped parser with the document of a parser that has [`host_inv`]
/// has it.
pub proof fn lemma_host_stopped(p: Parser, q: Parser)
    requires
        host_inv(p),
        q.doc == p.doc,
        q.stopped,
    ensures
        host_inv(q),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    reveal(host_inv_of);
}

/// Every id of the stack, and the redirection map's fragment, is a node of
/// the document.
#[verifier::opaque]
pub open spec fn ids_valid(p: Parser) -> bool {
    &&& forall|i: int| 0 <= i < p.open.len() ==> dom::valid(p.doc, (#[trigger] p.open[i]).id)
    &&& match p.redirect {
        None => true,
        Some((r, f)) => dom::valid(p.doc, f),
    }
}

/// `doc::dinv` gives [`ids_valid`] and a well-formed document.
pub proof fn lemma_dinv_ids(p: Parser)
    requires
        crate::reachable::doc::dinv(p),
    ensures
        ids_valid(p),
        dom::wf(p.doc),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    crate::reachable::doc::lemma_dinv(p);
    assert forall|i: int| 0 <= i < p.open.len() implies dom::valid(p.doc, (#[trigger] p.open[i]).id) by {
        assert(crate::exec::frame::elem_ok(p.doc, p.open[i]));
    }
}

// ---------------------------------------------------------------------
// The stack of open elements

/// A prefix of the stack.
pub proof fn lemma_host_prefix(p: Parser, q: Parser)
    requires
        host_inv(p),
        q == (Parser { open: q.open, ..p }),
        q.open.len() <= p.open.len(),
        forall|j: int| 0 <= j < q.open.len() ==> #[trigger] q.open[j] == p.open[j],
    ensures
        host_inv(q),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    reveal(host_inv_of);
    if !p.stopped {
        assert forall|i: int, j: int| #![trigger q.open[j], q.open[i]] 0 <= i < j < q.open.len() implies !hi(
            q.doc,
            q.open[j].id,
            q.open[i].id,
        ) by {
            assert(q.open[j] == p.open[j] && q.open[i] == p.open[i]);
        }
        if let Some((r, f)) = p.redirect {
            assert forall|j: int| 0 <= j < q.open.len() implies !hi(q.doc, (#[trigger] q.open[j]).id, f) by {
                assert(q.open[j] == p.open[j]);
            }
        }
    }
}

/// The stack with the entry at index `i` removed.
pub proof fn lemma_host_remove_open(p: Parser, i: int)
    requires
        host_inv(p),
        0 <= i < p.open.len(),
    ensures
        host_inv(Parser { open: p.open.remove(i), ..p }),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    reveal(host_inv_of);
    let q = Parser { open: p.open.remove(i), ..p };
    if !p.stopped {
        assert forall|a: int, b: int| #![trigger q.open[b], q.open[a]] 0 <= a < b < q.open.len() implies !hi(
            q.doc,
            q.open[b].id,
            q.open[a].id,
        ) by {
            let a2 = if a < i {
                a
            } else {
                a + 1
            };
            let b2 = if b < i {
                b
            } else {
                b + 1
            };
            assert(q.open[a] == p.open[a2] && q.open[b] == p.open[b2]);
        }
        if let Some((r, f)) = p.redirect {
            assert forall|j: int| 0 <= j < q.open.len() implies !hi(q.doc, (#[trigger] q.open[j]).id, f) by {
                let j2 = if j < i {
                    j
                } else {
                    j + 1
                };
                assert(q.open[j] == p.open[j2]);
            }
        }
    }
}

/// Element `e` may go on the stack at index `k` (so that the entries from
/// `k` on come after it): it is no host-including inclusive ancestor of an
/// entry before index `k` nor of the redirection map's fragment, and no
/// entry from index `k` on is one of it.
#[verifier::opaque]
pub open spec fn entry_ok(p: Parser, k: int, e: Elem) -> bool {
    &&& forall|i: int| 0 <= i < k && i < p.open.len() ==> !hi(p.doc, e.id, (#[trigger] p.open[i]).id)
    &&& forall|j: int| k <= j < p.open.len() ==> !hi(p.doc, (#[trigger] p.open[j]).id, e.id)
    &&& match p.redirect {
        None => true,
        Some((r, f)) => !hi(p.doc, e.id, f),
    }
}

/// Push an element that is [`entry_ok`] at the end.
pub proof fn lemma_host_push(p: Parser, e: Elem)
    requires
        host_inv(p),
        !p.stopped ==> entry_ok(p, p.open.len() as int, e),
    ensures
        host_inv(push(p, e)),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    reveal(host_inv_of);
    let q = push(p, e);
    if !p.stopped {
        let n = p.open.len() as int;
        assert forall|i: int, j: int| #![trigger q.open[j], q.open[i]] 0 <= i < j < q.open.len() implies !hi(
            q.doc,
            q.open[j].id,
            q.open[i].id,
        ) by {
            assert(q.open[i] == p.open[i]);
            if j < n {
                assert(q.open[j] == p.open[j]);
            } else {
                assert(q.open[j] == e);
            }
        }
        if let Some((r, f)) = p.redirect {
            assert forall|j: int| 0 <= j < q.open.len() implies !hi(q.doc, (#[trigger] q.open[j]).id, f) by {
                if j < n {
                    assert(q.open[j] == p.open[j]);
                }
            }
        }
    }
}

/// Insert an element that is [`entry_ok`] at index `k`.
pub proof fn lemma_host_insert_open(p: Parser, k: int, e: Elem)
    requires
        host_inv(p),
        0 <= k <= p.open.len(),
        !p.stopped ==> entry_ok(p, k, e),
    ensures
        host_inv(Parser { open: p.open.insert(k, e), ..p }),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    reveal(host_inv_of);
    let q = Parser { open: p.open.insert(k, e), ..p };
    if !p.stopped {
        assert forall|i: int, j: int| #![trigger q.open[j], q.open[i]] 0 <= i < j < q.open.len() implies !hi(
            q.doc,
            q.open[j].id,
            q.open[i].id,
        ) by {
            if j == k {
                assert(q.open[j] == e);
                assert(q.open[i] == p.open[i]);
            } else if i == k {
                assert(q.open[i] == e);
                assert(q.open[j] == p.open[j - 1]);
            } else {
                let i2 = if i < k {
                    i
                } else {
                    i - 1
                };
                let j2 = if j < k {
                    j
                } else {
                    j - 1
                };
                assert(q.open[i] == p.open[i2] && q.open[j] == p.open[j2]);
            }
        }
        if let Some((r, f)) = p.redirect {
            assert forall|j: int| 0 <= j < q.open.len() implies !hi(q.doc, (#[trigger] q.open[j]).id, f) by {
                if j < k {
                    assert(q.open[j] == p.open[j]);
                } else if j > k {
                    assert(q.open[j] == p.open[j - 1]);
                }
            }
        }
    }
}

/// Replace the entry at index `k` by an element that is [`entry_ok`]
/// between its neighbours.
pub proof fn lemma_host_update_open(p: Parser, k: int, e: Elem)
    requires
        host_inv(p),
        0 <= k < p.open.len(),
        !p.stopped ==> entry_ok(Parser { open: p.open.remove(k), ..p }, k, e),
    ensures
        host_inv(Parser { open: p.open.update(k, e), ..p }),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    let p1 = Parser { open: p.open.remove(k), ..p };
    lemma_host_remove_open(p, k);
    lemma_host_insert_open(p1, k, e);
    assert(p1.open.insert(k, e) =~= p.open.update(k, e));
}

// ---------------------------------------------------------------------
// The document

/// A document that keeps every step up of the parser's
/// (`hi::up_same`).
pub proof fn lemma_host_up_same(p: Parser, d2: Document)
    requires
        host_inv(p),
        ids_valid(p),
        dom::host_acyclic(d2),
        up_same(p.doc, d2),
    ensures
        host_inv(Parser { doc: d2, ..p }),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    reveal(host_inv_of);
    let q = Parser { doc: d2, ..p };
    if !p.stopped {
        assert forall|i: int, j: int| #![trigger q.open[j], q.open[i]] 0 <= i < j < q.open.len() implies !hi(
            q.doc,
            q.open[j].id,
            q.open[i].id,
        ) by {
            lemma_hi_same(p.doc, d2, p.open[j].id, p.open[i].id);
        }
        if let Some((r, f)) = p.redirect {
            assert forall|j: int| 0 <= j < q.open.len() implies !hi(q.doc, (#[trigger] q.open[j]).id, f) by {
                lemma_hi_same(p.doc, d2, p.open[j].id, f);
            }
        }
    }
}

/// [`create`]: the new node is [`low`].
pub proof fn lemma_host_create(p: Parser, k: NodeKind)
    requires
        host_inv(p),
        ids_valid(p),
        !p.stopped ==> dom::creatable(p.doc, k),
    ensures
        host_inv(create(p, k).0),
        !create(p, k).0.stopped ==> low(create(p, k).0.doc, create(p, k).1) && up_same(p.doc, create(p, k).0.doc),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    if p.stopped {
    } else if !dom::can_create(p.doc, 1) {
        lemma_host_stopped(p, stop_parsing(p));
    } else {
        lemma_host_inv(p);
        let (d2, id) = dom::create_node(p.doc, k);
        clazel_dom::host_acyclic_lemmas::theorem_create_node_host_acyclic(p.doc, k);
        lemma_create_up_same(p.doc, k);
        lemma_host_up_same(p, d2);
        assert forall|x: NodeId| #![trigger hi(d2, id, x)] x < id implies !hi(d2, id, x) by {
            lemma_new_not_hi(p.doc, d2, id, x);
        }
    }
}

/// [`dom_remove`]: a link is taken away.
pub proof fn lemma_host_dom_remove(p: Parser, node: NodeId)
    requires
        host_inv(p),
        ids_valid(p),
        dom::wf(p.doc),
    ensures
        host_inv(dom_remove(p, node)),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    if !(p.stopped || !dom::valid(p.doc, node) || p.doc.nodes[node as int].parent is None) {
        reveal(host_inv_of);
        let d = p.doc;
        let d2 = dom::remove(d, node);
        let q = dom_remove(p, node);
        clazel_dom::host_acyclic_lemmas::theorem_remove_host_acyclic(d, node);
        lemma_remove_grafted(d, node);
        assert forall|i: int, j: int| #![trigger q.open[j], q.open[i]] 0 <= i < j < q.open.len() implies !hi(
            q.doc,
            q.open[j].id,
            q.open[i].id,
        ) by {
            if hi(d2, p.open[j].id, p.open[i].id) {
                lemma_hi_lost(d, d2, p.open[j].id, p.open[i].id);
            }
        }
        if let Some((r, f)) = p.redirect {
            assert forall|j: int| 0 <= j < q.open.len() implies !hi(q.doc, (#[trigger] q.open[j]).id, f) by {
                if hi(d2, p.open[j].id, f) {
                    lemma_hi_lost(d, d2, p.open[j].id, f);
                }
            }
        }
    }
}

/// [`dom_insert`], under `host::insert_keeps_host`: the call meets
/// `clazel_dom::host_acyclic_contract::insert_acyclic_requires`, and the
/// stack stays ordered as the document.
pub proof fn lemma_host_dom_insert(p: Parser, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        host_inv(p),
        ids_valid(p),
        dom::wf(p.doc),
        !p.stopped && insert_valid(p.doc, node, parent, child) ==> insert_keeps_host(p, node, parent),
    ensures
        host_inv(dom_insert(p, node, parent, child)),
        !p.stopped && insert_valid(p.doc, node, parent, child) ==> clazel_dom::host_acyclic_contract::insert_acyclic_requires(
            p.doc,
            node,
            parent,
            child,
        ),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    if !p.stopped && insert_valid(p.doc, node, parent, child) {
        reveal(host_inv_of);
        let d = p.doc;
        let d2 = dom::insert(d, node, parent, child);
        let q = dom_insert(p, node, parent, child);
        let g = Set::<NodeId>::empty().insert(node);
        assert(dom::insert_requires(d, node, parent, child));
        assert(clazel_dom::host_acyclic_contract::insert_acyclic_requires(d, node, parent, child));
        clazel_dom::host_acyclic_lemmas::theorem_insert_host_acyclic(d, node, parent, child);
        lemma_insert_grafted(d, node, parent, child);
        assert forall|i: int, j: int| #![trigger q.open[j], q.open[i]] 0 <= i < j < q.open.len() implies !hi(
            q.doc,
            q.open[j].id,
            q.open[i].id,
        ) by {
            if hi(d2, p.open[j].id, p.open[i].id) {
                let m = lemma_hi_graft(d, d2, g, parent, p.open[j].id, p.open[i].id);
                assert(m is Some ==> m->Some_0 == node);
            }
        }
        if let Some((r, f)) = p.redirect {
            assert forall|j: int| 0 <= j < q.open.len() implies !hi(q.doc, (#[trigger] q.open[j]).id, f) by {
                if hi(d2, p.open[j].id, f) {
                    let m = lemma_hi_graft(d, d2, g, parent, p.open[j].id, f);
                    assert(m is Some ==> m->Some_0 == node);
                }
            }
        }
    }
}

/// [`dom_reparent_children`], under `host::reparent_keeps_host`: the call
/// meets
/// `clazel_dom::host_acyclic_contract::reparent_children_acyclic_requires`,
/// and the stack stays ordered as the document.
pub proof fn lemma_host_reparent(p: Parser, from: NodeId, to: NodeId)
    requires
        host_inv(p),
        ids_valid(p),
        dom::wf(p.doc),
        !p.stopped && dom::reparent_children_requires(p.doc, from, to) ==> reparent_keeps_host(p, from, to),
    ensures
        host_inv(dom_reparent_children(p, from, to)),
        !p.stopped && dom::reparent_children_requires(p.doc, from, to)
            ==> clazel_dom::host_acyclic_contract::reparent_children_acyclic_requires(p.doc, from, to),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    let d = p.doc;
    if !p.stopped && dom::reparent_children_requires(d, from, to) {
        reveal(host_inv_of);
        let d2 = dom::reparent_children(d, from, to);
        let q = dom_reparent_children(p, from, to);
        assert(q.doc == d2);
        let kids = d.nodes[from as int].children;
        let g = kids.to_set();
        clazel_dom::host_acyclic_lemmas::theorem_reparent_children_host_acyclic(d, from, to);
        lemma_reparent_grafted(d, from, to);
        clazel_dom::lemmas::lemma_reparent_facts(d, from, to);
        // A child of `from` is below `from`, so it is no host-including
        // inclusive ancestor of `to`, and what is below it is below `from`.
        assert forall|n: NodeId| #[trigger] g.contains(n) && dom::valid(d, n) implies !hi(d, n, to) && d.nodes[n as int].parent == Some(
            from,
        ) by {
            let j = choose|j: int| 0 <= j < kids.len() && kids[j] == n;
            assert(d.nodes[kids[j] as int].parent == Some(from));
            if hi(d, n, to) {
                lemma_hi_self(d, from);
                lemma_hi_parent(d, from, n);
                lemma_hi_trans(d, from, n, to);
            }
        }
        assert forall|i: int, j: int| #![trigger q.open[j], q.open[i]] 0 <= i < j < q.open.len() implies !hi(
            q.doc,
            q.open[j].id,
            q.open[i].id,
        ) by {
            if hi(d2, p.open[j].id, p.open[i].id) {
                let m = lemma_hi_graft(d, d2, g, to, p.open[j].id, p.open[i].id);
                if let Some(n) = m {
                    lemma_below_child(d, from, n, p.open[i].id);
                }
            }
        }
        if let Some((r, f)) = p.redirect {
            assert forall|j: int| 0 <= j < q.open.len() implies !hi(q.doc, (#[trigger] q.open[j]).id, f) by {
                if hi(d2, p.open[j].id, f) {
                    let m = lemma_hi_graft(d, d2, g, to, p.open[j].id, f);
                    if let Some(n) = m {
                        lemma_below_child(d, from, n, f);
                    }
                }
            }
        }
    }
}

/// A node below a child `n` of `from` is below `from`, and is not `from`.
pub proof fn lemma_below_child(d: Document, from: NodeId, n: NodeId, x: NodeId)
    requires
        dom::host_acyclic(d),
        dom::valid(d, n),
        dom::valid(d, x),
        dom::valid(d, from),
        d.nodes[n as int].parent == Some(from),
        hi(d, n, x),
    ensures
        hi(d, from, x),
        x != from,
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    lemma_hi_self(d, from);
    lemma_hi_parent(d, from, n);
    lemma_hi_trans(d, from, n, x);
    if x == from {
        lemma_child_not_above(d, n);
    }
}

/// A node is a host-including inclusive ancestor of itself.
pub proof fn lemma_hi_self(d: Document, a: NodeId)
    requires
        dom::valid(d, a),
    ensures
        hi(d, a, a),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    clazel_dom::deep_clone_size_lemmas::lemma_hi_self(d, a);
}

// ---------------------------------------------------------------------
// Nodes just created (the "easy sites")

/// Every entry of the stack but the last has an id below `n`, and so has
/// the redirection map's fragment: `n` was created after them (the last
/// entry may be `n` itself, pushed before it is inserted).
#[verifier::opaque]
pub open spec fn ids_below(p: Parser, n: NodeId) -> bool {
    &&& forall|i: int| 0 <= i < p.open.len() - 1 ==> (#[trigger] p.open[i]).id < n
    &&& p.open.len() > 0 ==> p.open[p.open.len() - 1].id <= n
    &&& match p.redirect {
        None => true,
        Some((r, f)) => f < n,
    }
}

/// **The fresh-node lemma**: a [`low`] node, inserted below a node created
/// before it, with a stack of nodes created before it, meets
/// `host::insert_keeps_host`.
pub proof fn lemma_low_keeps(p: Parser, node: NodeId, parent: NodeId)
    requires
        low(p.doc, node),
        parent < node,
        ids_below(p, node),
    ensures
        insert_keeps_host(p, node, parent),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    assert forall|i: int, j: int| #![trigger p.open[j], p.open[i]] 0 <= i < j < p.open.len() implies !(hi(
        p.doc,
        p.open[j].id,
        parent,
    ) && hi(p.doc, node, p.open[i].id)) by {
        assert(p.open[i].id < node);
    }
}

/// A [`low`] node inserted below a node created before it stays [`low`].
pub proof fn lemma_low_insert(d: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        dom::host_acyclic(d),
        dom::insert_requires(d, node, parent, child),
        low(d, node),
        parent < node,
    ensures
        low(dom::insert(d, node, parent, child), node),
{
    hide(dom::insert);
    let d2 = dom::insert(d, node, parent, child);
    let g = Set::<NodeId>::empty().insert(node);
    assert(!hi(d, node, parent));
    assert(clazel_dom::host_acyclic_contract::insert_acyclic_requires(d, node, parent, child));
    clazel_dom::host_acyclic_lemmas::theorem_insert_host_acyclic(d, node, parent, child);
    lemma_insert_grafted(d, node, parent, child);
    assert forall|x: NodeId| #![trigger hi(d2, node, x)] x < node implies !hi(d2, node, x) by {
        if hi(d2, node, x) {
            let m = lemma_hi_graft(d, d2, g, parent, node, x);
            assert(m is Some ==> m->Some_0 == node);
        }
    }
}

/// `d2` has every node of `d`, unchanged.
#[verifier::opaque]
pub open spec fn old_same(d: Document, d2: Document) -> bool {
    &&& d.nodes.len() <= d2.nodes.len()
    &&& forall|i: int| 0 <= i < d.nodes.len() ==> #[trigger] d2.nodes[i] == d.nodes[i]
}

/// [`old_same`] is transitive.
pub proof fn lemma_old_same_trans(d: Document, d1: Document, d2: Document)
    requires
        old_same(d, d1),
        old_same(d1, d2),
    ensures
        old_same(d, d2),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    assert forall|i: int| 0 <= i < d.nodes.len() implies #[trigger] d2.nodes[i] == d.nodes[i] by {
        assert(d1.nodes[i] == d.nodes[i]);
    }
}

/// A change of the document that keeps every step up (`hi::up_same`) and
/// `clazel_dom::spec::host_acyclic` keeps the invariant, as a
/// `host::host_step`.
pub proof fn lemma_host_step_up_same(p: Parser, q: Parser)
    requires
        ids_valid(p),
        q == (Parser { doc: q.doc, ..p }),
        dom::host_acyclic(p.doc) ==> dom::host_acyclic(q.doc),
        up_same(p.doc, q.doc),
    ensures
        host_step(p, q),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    if host_inv(p) {
        lemma_host_inv(p);
        lemma_host_up_same(p, q.doc);
    }
}

/// "The appropriate place for inserting a node" reads only nodes of the
/// arena as it was (the stack's, their parents and their template
/// contents): it is the same in a parser whose document has every node of
/// `p`'s unchanged ([`old_same`]), and its parent is a node of `p`'s
/// document.
pub proof fn lemma_place_same(p: Parser, p1: Parser, ov: Option<Elem>)
    requires
        dinv(p),
        rooted(p),
        match ov {
            Some(e) => crate::exec::frame::elem_ok(p.doc, e),
            None => true,
        },
        p1 == (Parser { doc: p1.doc, ..p }),
        old_same(p.doc, p1.doc),
    ensures
        appropriate_place(p1, ov) == appropriate_place(p, ov),
        dom::valid(p.doc, appropriate_place(p, ov).parent),
        adjusted_location(p1, None) == adjusted_location(p, None),
        dom::valid(p.doc, adjusted_location(p, None).parent),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    lemma_place_same_at(p, p1, ov);
    lemma_place_same_at(p, p1, None);
    lemma_dinv(p);
}

/// [`lemma_place_same`], for one override target.
pub proof fn lemma_place_same_at(p: Parser, p1: Parser, ov: Option<Elem>)
    requires
        dinv(p),
        rooted(p),
        match ov {
            Some(e) => crate::exec::frame::elem_ok(p.doc, e),
            None => true,
        },
        p1 == (Parser { doc: p1.doc, ..p }),
        old_same(p.doc, p1.doc),
    ensures
        appropriate_place(p1, ov) == appropriate_place(p, ov),
        dom::valid(p.doc, appropriate_place(p, ov).parent),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    lemma_dinv(p);
    lemma_place_pok(p, ov);
    let target = match ov {
        Some(e) => e,
        None => current_node(p),
    };
    assert(crate::exec::frame::elem_ok(p.doc, target)) by {
        if ov is None {
            assert(crate::exec::frame::elem_ok(p.doc, p.open[p.open.len() - 1]));
        }
    }
    assert(p1.doc.nodes[target.id as int] == p.doc.nodes[target.id as int]);
    if p.foster && is_table_like(target) {
        let f = |e: Elem| is_html(e, Tag::Template) || is_html(e, Tag::Table);
        let i = last_index_where(p.open, p.open.len() as int, f);
        crate::exec::stack::lemma_last_index_where(p.open, p.open.len() as int, f);
        if i < 0 {
            assert(crate::exec::frame::elem_ok(p.doc, p.open[0]));
        } else if is_html(p.open[i], Tag::Template) {
            assert(crate::exec::frame::elem_ok(p.doc, p.open[i]));
            assert(p1.doc.nodes[p.open[i].id as int] == p.doc.nodes[p.open[i].id as int]);
        } else {
            let t = p.open[i].id;
            assert(crate::exec::frame::elem_ok(p.doc, p.open[i]));
            assert(p1.doc.nodes[t as int] == p.doc.nodes[t as int]);
            match p.doc.nodes[t as int].parent {
                Some(par) => {
                    crate::exec::insert::lemma_wf_parent(p.doc, t);
                    assert(p1.doc.nodes[par as int] == p.doc.nodes[par as int]);
                },
                None => {
                    assert(i != 0);
                    assert(crate::exec::frame::elem_ok(p.doc, p.open[i - 1]));
                    assert(p1.doc.nodes[p.open[i - 1].id as int] == p.doc.nodes[p.open[i - 1].id as int]);
                },
            }
        }
    }
}

/// With `doc::dinv`, every id of the stack but possibly a last entry `n`
/// itself, and the redirection map's fragment, is below a node `n` created
/// at or after the arena's size ([`ids_below`]).
pub proof fn lemma_dinv_ids_below(p: Parser, n: NodeId)
    requires
        dinv(p),
        n >= p.doc.nodes.len(),
    ensures
        ids_below(p, n),
        forall|i: int| 0 <= i < p.open.len() ==> (#[trigger] p.open[i]).id < n,
        match p.redirect {
            None => true,
            Some((r, f)) => f < n,
        },
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    lemma_dinv_ids(p);
}

/// The template contents step of "create an element for a token", for the
/// element `id` just created from the well-formed arena `d0`: the step
/// keeps the invariant, the older nodes and their steps up, and `id` is
/// [`low`].
pub proof fn lemma_ctc_step(d0: Document, p1: Parser, id: NodeId)
    requires
        dom::wf(d0),
        ids_valid(p1),
        old_same(d0, p1.doc),
        up_same(d0, p1.doc),
        id == d0.nodes.len(),
        dom::valid(p1.doc, id),
        p1.doc.nodes[id as int].kind is Element,
    ensures
        ({
            let d = dom::create_template_contents(p1.doc, id).0;
            &&& host_step(p1, Parser { doc: d, ..p1 })
            &&& old_same(d0, d)
            &&& up_same(d0, d)
            &&& dom::host_acyclic(d) ==> low(d, id)
            &&& top(p1.doc, id) ==> top(d, id)
        }),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    let d = dom::create_template_contents(p1.doc, id).0;
    lemma_ctc_up_same(p1.doc, id);
    if host_inv(p1) {
        lemma_host_inv(p1);
        clazel_dom::host_acyclic_lemmas::theorem_create_template_contents_host_acyclic(p1.doc, id);
        lemma_host_up_same(p1, d);
    }
    lemma_up_same_trans(d0, p1.doc, d);
    lemma_new_low(d0, d, id);
    if top(p1.doc, id) {
        lemma_up_same_top(p1.doc, d, id);
    }
    assert forall|i: int| 0 <= i < d0.nodes.len() implies #[trigger] d.nodes[i] == d0.nodes[i] by {
        assert(p1.doc.nodes[i] == d0.nodes[i]);
        let d1 = dom::create_node(p1.doc, NodeKind::DocumentFragment { host: Some(id) }).0;
        assert(d1.nodes[i] == p1.doc.nodes[i]);
    }
}

/// Creating a node keeps the older nodes ([`old_same`]).
pub proof fn lemma_create_old_same(d: Document, k: NodeKind)
    ensures
        old_same(d, dom::create_node(d, k).0),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    let d2 = dom::create_node(d, k).0;
    assert forall|i: int| 0 <= i < d.nodes.len() implies #[trigger] d2.nodes[i] == d.nodes[i] by {}
}

/// What "insert an element at the adjusted insertion location" needs of
/// an element `n` just created (parser `p1`, from the parser `p`): it is
/// [`low`], the appropriate place's parent was created before it, and so
/// were the entries of the stack ([`ids_below`]).
pub proof fn lemma_fresh_place(p: Parser, p1: Parser, n: NodeId)
    requires
        dinv(p),
        rooted(p),
        p1 == (Parser { doc: p1.doc, ..p }),
        old_same(p.doc, p1.doc),
        n >= p.doc.nodes.len(),
        dom::host_acyclic(p1.doc) ==> low(p1.doc, n),
    ensures
        host_inv(p1) ==> low(p1.doc, n) && adjusted_location(p1, None).parent < n && ids_below(p1, n),
        forall|i: int| 0 <= i < p1.open.len() ==> (#[trigger] p1.open[i]).id < n,
        match p1.redirect {
            None => true,
            Some((r, f)) => f < n,
        },
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    lemma_place_same(p, p1, None);
    lemma_dinv_ids_below(p, n);
    lemma_dinv(p);
    if host_inv(p1) {
        lemma_host_inv(p1);
    }
}

/// What "insert" needs of a node `n` just created (parser `p1`, from the
/// parser `p`), below a parent that is a node of `p`'s document:
/// `host::insert_keeps_host`.
pub proof fn lemma_fresh_insert(p: Parser, p1: Parser, n: NodeId, parent: NodeId)
    requires
        dinv(p),
        p1 == (Parser { doc: p1.doc, ..p }),
        n >= p.doc.nodes.len(),
        dom::valid(p.doc, parent),
        dom::host_acyclic(p1.doc) ==> low(p1.doc, n),
    ensures
        host_inv(p1) ==> insert_keeps_host(p1, n, parent),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    lemma_dinv_ids_below(p, n);
    if host_inv(p1) {
        lemma_host_inv(p1);
        lemma_low_keeps(p1, n, parent);
    }
}

// ---------------------------------------------------------------------
// The adoption agency algorithm (§13.2.6.4.7)

/// An element just created (with no step up, [`low`], created after every
/// entry of the stack) may go on the stack at any index.
pub proof fn lemma_top_entry_ok(p: Parser, k: int, e: Elem)
    requires
        0 <= k,
        dom::host_acyclic(p.doc),
        ids_valid(p),
        dom::valid(p.doc, e.id),
        top(p.doc, e.id),
        low(p.doc, e.id),
        forall|i: int| 0 <= i < p.open.len() ==> (#[trigger] p.open[i]).id < e.id,
        match p.redirect {
            None => true,
            Some((r, f)) => f < e.id,
        },
    ensures
        entry_ok(p, k, e),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    assert forall|j: int| k <= j < p.open.len() implies !hi(p.doc, (#[trigger] p.open[j]).id, e.id) by {
        if hi(p.doc, p.open[j].id, e.id) {
            lemma_hi_top(p.doc, p.open[j].id, e.id);
        }
    }
}

/// [`lemma_top_entry_ok`] for the stack with the entry at index `i`
/// removed: the element may replace that entry.
pub proof fn lemma_top_update_ok(p: Parser, i: int, e: Elem)
    requires
        dom::host_acyclic(p.doc),
        ids_valid(p),
        dom::valid(p.doc, e.id),
        top(p.doc, e.id),
        low(p.doc, e.id),
        0 <= i < p.open.len(),
        forall|j: int| 0 <= j < p.open.len() ==> (#[trigger] p.open[j]).id < e.id,
        match p.redirect {
            None => true,
            Some((r, f)) => f < e.id,
        },
    ensures
        entry_ok(Parser { open: p.open.remove(i), ..p }, i, e),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    let q = Parser { open: p.open.remove(i), ..p };
    assert forall|j: int| 0 <= j < q.open.len() implies (#[trigger] q.open[j]).id < e.id && dom::valid(q.doc, q.open[j].id) by {
        let j2 = if j < i {
            j
        } else {
            j + 1
        };
        assert(q.open[j] == p.open[j2]);
    }
    lemma_top_entry_ok(q, i, e);
}

/// Step 4.24's stack, for the host invariant: with formattingElement's
/// entry (index `r`) removed, the new element `e` (no step up, [`low`],
/// created after every entry) may go on the stack at index `k`.
pub proof fn lemma_mid_entry(p: Parser, r: int, k: int, e: Elem)
    requires
        !p.stopped,
        ids_valid(p),
        0 <= r < p.open.len(),
        0 <= k,
        dom::valid(p.doc, e.id),
        top(p.doc, e.id),
        dom::host_acyclic(p.doc) ==> low(p.doc, e.id),
        forall|j: int| 0 <= j < p.open.len() ==> (#[trigger] p.open[j]).id < e.id,
        match p.redirect {
            None => true,
            Some((r, f)) => f < e.id,
        },
    ensures
        host_inv(remove_open_at(p, r)) ==> entry_ok(remove_open_at(p, r), k, e),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    let pc = remove_open_at(p, r);
    if host_inv(pc) {
        lemma_host_inv(pc);
        assert forall|j: int| 0 <= j < pc.open.len() implies (#[trigger] pc.open[j]).id < e.id && dom::valid(pc.doc, pc.open[j].id) by {
            let j2 = if j < r {
                j
            } else {
                j + 1
            };
            assert(pc.open[j] == p.open[j2]);
        }
        lemma_top_entry_ok(pc, k, e);
    }
}

/// Step 4.24's stack: the stack `o` with the entry at index `r` removed
/// and `e` inserted at index `k`, just below an entry with id `fb_id`,
/// holds `e` at index `k` below that entry, and every other entry has an
/// id below `e`'s if every entry of `o` has.
pub proof fn lemma_mid_shape(o: Seq<Elem>, r: int, k: int, e: Elem, fb_id: NodeId)
    requires
        0 <= r < o.len(),
        1 <= k <= o.len() - 1,
        o.remove(r)[k - 1].id == fb_id,
        forall|j: int| 0 <= j < o.len() ==> (#[trigger] o[j]).id < e.id,
    ensures
        ({
            let q = o.remove(r).insert(k, e);
            &&& q.len() == o.len()
            &&& q[k] == e
            &&& q[k - 1].id == fb_id
            &&& forall|j: int| 0 <= j < q.len() && j != k ==> (#[trigger] q[j]).id < e.id
        }),
{
    let o1 = o.remove(r);
    let q = o1.insert(k, e);
    assert forall|j: int| 0 <= j < o1.len() implies (#[trigger] o1[j]).id < e.id by {
        if j < r {
            assert(o1[j] == o[j]);
        } else {
            assert(o1[j] == o[j + 1]);
        }
    }
    assert(q[k - 1] == o1[k - 1]);
    assert forall|j: int| 0 <= j < q.len() && j != k implies (#[trigger] q[j]).id < e.id by {
        if j < k {
            assert(q[j] == o1[j]);
        } else {
            assert(q[j] == o1[j - 1]);
        }
    }
}

/// Step 4.16.11, "append lastNode to node": node is the element just
/// created (no step up), at index `i` of the stack, and lastNode an entry
/// below it in the stack (index `l`).
pub proof fn lemma_append_to_top(p: Parser, last_id: NodeId, ne_id: NodeId, i: int, l: int)
    requires
        host_inv(p),
        !p.stopped,
        ids_valid(p),
        dom::valid(p.doc, ne_id),
        top(p.doc, ne_id),
        0 <= i < l < p.open.len(),
        p.open[i].id == ne_id,
        p.open[l].id == last_id,
        forall|j: int| 0 <= j < p.open.len() && j != i ==> (#[trigger] p.open[j]).id != ne_id,
    ensures
        insert_keeps_host(p, last_id, ne_id),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    lemma_host_inv(p);
    if hi(p.doc, last_id, ne_id) {
        lemma_hi_top(p.doc, last_id, ne_id);
    }
    assert forall|a: int, b: int| #![trigger p.open[b], p.open[a]] 0 <= a < b < p.open.len() implies !(hi(
        p.doc,
        p.open[b].id,
        ne_id,
    ) && hi(p.doc, last_id, p.open[a].id)) by {
        if hi(p.doc, p.open[b].id, ne_id) && hi(p.doc, last_id, p.open[a].id) {
            lemma_hi_top(p.doc, p.open[b].id, ne_id);
            assert(b == i);
            assert(!hi(p.doc, p.open[l].id, p.open[a].id));
        }
    }
    if let Some((r, f)) = p.redirect {
        assert(!hi(p.doc, p.open[l].id, f));
    }
}

/// What relates the parent `t` of an insertion location to the entry
/// `s` of the stack it was computed from: it is the entry, its template
/// contents, its parent, or the template contents of its parent.
pub open spec fn anchored(d: Document, t: NodeId, s: NodeId) -> bool {
    ||| t == s
    ||| (has_template_contents(d, s) && t == template_contents(d, s))
    ||| d.nodes[s as int].parent == Some(t)
    ||| (d.nodes[s as int].parent is Some && has_template_contents(d, d.nodes[s as int].parent->Some_0) && t
        == template_contents(d, d.nodes[s as int].parent->Some_0))
}

/// An entry below the entry at index `a` in the stack is no host-including
/// inclusive ancestor of a node [`anchored`] at that entry.
pub proof fn lemma_anchor(p: Parser, a: int, t: NodeId, j: int)
    requires
        host_inv(p),
        !p.stopped,
        dinv(p),
        0 <= a < j < p.open.len(),
        anchored(p.doc, t, p.open[a].id),
    ensures
        !hi(p.doc, p.open[j].id, t),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    lemma_host_inv(p);
    lemma_dinv(p);
    let d = p.doc;
    let s = p.open[a].id;
    let x = p.open[j].id;
    assert(crate::exec::frame::elem_ok(d, p.open[a]));
    assert(crate::exec::frame::elem_ok(d, p.open[j]));
    assert(!hi(d, p.open[j].id, p.open[a].id));
    if t == s {
    } else if has_template_contents(d, s) && t == template_contents(d, s) {
        lemma_not_hi_contents(d, x, s);
    } else if d.nodes[s as int].parent == Some(t) {
        if hi(d, x, t) {
            lemma_hi_parent(d, x, s);
        }
    } else {
        let par = d.nodes[s as int].parent->Some_0;
        if hi(d, x, par) {
            lemma_hi_parent(d, x, s);
        }
        lemma_not_hi_contents(d, x, par);
    }
}

/// "The appropriate place for inserting a node" given the entry at index
/// `c` of the stack as override target, when no entry after index `m >= c`
/// is a `table` or `template` element (`host::wall_clear`): the adjusted
/// insertion location's parent is a node of which no entry after index `m`
/// is a host-including inclusive ancestor (`host::place_bound`). Foster
/// parenting included: the last `table` or `template` element is at index
/// `m` or above it.
pub proof fn lemma_place_bound(p: Parser, c: int, m: int)
    requires
        dinv(p),
        rooted(p),
        host_inv(p),
        !p.stopped,
        0 <= c <= m < p.open.len(),
        wall_clear(p.open, m),
    ensures
        place_bound(p, adjusted_location(p, Some(appropriate_place(p, Some(p.open[c])))).parent, m),
        dom::valid(p.doc, adjusted_location(p, Some(appropriate_place(p, Some(p.open[c])))).parent),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    lemma_host_inv(p);
    lemma_dinv(p);
    let d = p.doc;
    let target = p.open[c];
    assert(crate::exec::frame::elem_ok(d, target));
    lemma_place_pok(p, Some(target));
    let pl = appropriate_place(p, Some(target));
    lemma_adjusted_pok(p, Some(pl));
    let t0 = pl.parent;
    let t = adjusted_location(p, Some(pl)).parent;
    // The entry the place is anchored at, at index `m` or above.
    let a = lemma_place_anchor(p, c, m);
    assert forall|j: int| m < j < p.open.len() implies !hi(d, (#[trigger] p.open[j]).id, t) by {
        if t == t0 {
            lemma_anchor(p, a, t0, j);
        }
    }
}

/// The entry of the stack "the appropriate place for inserting a node"
/// given the entry at index `c` is [`anchored`] at: one at index `m` or
/// above, when no entry after index `m >= c` is a `table` or `template`
/// element.
pub proof fn lemma_place_anchor(p: Parser, c: int, m: int) -> (a: int)
    requires
        dinv(p),
        rooted(p),
        !p.stopped,
        0 <= c <= m < p.open.len(),
        wall_clear(p.open, m),
    ensures
        0 <= a <= m,
        anchored(p.doc, appropriate_place(p, Some(p.open[c])).parent, p.open[a].id),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    lemma_dinv(p);
    let d = p.doc;
    let target = p.open[c];
    assert(crate::exec::frame::elem_ok(d, target));
    if p.foster && is_table_like(target) {
        let f = |e: Elem| is_html(e, Tag::Template) || is_html(e, Tag::Table);
        let i = last_index_where(p.open, p.open.len() as int, f);
        crate::exec::stack::lemma_last_index_where(p.open, p.open.len() as int, f);
        if i < 0 {
            0
        } else {
            assert(f(p.open[i]));
            assert(crate::invariant::table_wall(p.open[i]));
            assert(i <= m);
            assert(crate::exec::frame::elem_ok(d, p.open[i]));
            if is_html(p.open[i], Tag::Template) {
                i
            } else {
                let tb = p.open[i].id;
                match d.nodes[tb as int].parent {
                    Some(par) => {
                        crate::exec::insert::lemma_wf_parent(d, tb);
                        i
                    },
                    None => {
                        assert(i != 0);
                        assert(crate::exec::frame::elem_ok(d, p.open[i - 1]));
                        i - 1
                    },
                }
            }
        }
    } else {
        c
    }
}

/// DOM "remove" relates no nodes: a host-including inclusive ancestor in
/// the document after [`dom_remove`] is one before it.
pub proof fn lemma_remove_hi(p: Parser, node: NodeId, a: NodeId, x: NodeId)
    requires
        dom::host_acyclic(p.doc),
        dom::wf(p.doc),
        dom::valid(p.doc, x),
        hi(dom_remove(p, node).doc, a, x),
    ensures
        hi(p.doc, a, x),
{
    let p1 = dom_remove(p, node);
    if p1.doc != p.doc {
        clazel_dom::host_acyclic_lemmas::theorem_remove_host_acyclic(p.doc, node);
        lemma_remove_grafted(p.doc, node);
        lemma_hi_lost(p.doc, p1.doc, a, x);
    }
}

/// Steps 4.20 and 4.21, "remove lastNode" and "insert lastNode into
/// target": lastNode is the entry at index `l` of the stack, and no entry
/// after index `m < l` is a host-including inclusive ancestor of target
/// (`host::place_bound`). The insertion, made after the removal, meets
/// `host::insert_keeps_host`.
pub proof fn lemma_move_ok(p: Parser, last_id: NodeId, target: NodeId, m: int, l: int)
    requires
        host_inv(p),
        !p.stopped,
        ids_valid(p),
        dom::wf(p.doc),
        place_bound(p, target, m),
        0 <= m < l < p.open.len(),
        p.open[l].id == last_id,
        dom::valid(p.doc, target),
    ensures
        insert_keeps_host(dom_remove(p, last_id), last_id, target),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    lemma_host_inv(p);
    let p1 = dom_remove(p, last_id);
    assert(p1.open == p.open && p1.redirect == p.redirect);
    assert(!hi(p.doc, p.open[l].id, target));
    if hi(p1.doc, last_id, target) {
        lemma_remove_hi(p, last_id, last_id, target);
    }
    assert forall|a: int, b: int| #![trigger p1.open[b], p1.open[a]] 0 <= a < b < p1.open.len() implies !(hi(
        p1.doc,
        p1.open[b].id,
        target,
    ) && hi(p1.doc, last_id, p1.open[a].id)) by {
        if hi(p1.doc, p1.open[b].id, target) && hi(p1.doc, last_id, p1.open[a].id) {
            lemma_remove_hi(p, last_id, p.open[b].id, target);
            lemma_remove_hi(p, last_id, last_id, p.open[a].id);
            // In `p`'s document: `b <= m` and `a >= l`.
            assert(!(m < b));
            assert(!hi(p.doc, p.open[l].id, p.open[a].id) || a >= l);
        }
    }
    if let Some((r, f)) = p.redirect {
        assert(!hi(p.doc, p.open[l].id, f));
        if hi(p1.doc, last_id, f) {
            lemma_remove_hi(p, last_id, last_id, f);
        }
    }
}

/// What steps 4.27.1 and 4.27.3 need of the stack: furthestBlock at index
/// `ib`, the new element `ne_id` just below it (index `ib + 1`), created
/// after every other entry and after the redirection map's fragment, with
/// no step up and [`low`].
pub open spec fn end_pre(p: Parser, fb_id: NodeId, ne_id: NodeId, ib: int) -> bool {
    &&& 0 <= ib
    &&& ib + 1 < p.open.len()
    &&& p.open[ib].id == fb_id
    &&& p.open[ib + 1].id == ne_id
    &&& dom::valid(p.doc, ne_id)
    &&& top(p.doc, ne_id)
    &&& low(p.doc, ne_id)
    &&& forall|j: int| 0 <= j < p.open.len() && j != ib + 1 ==> (#[trigger] p.open[j]).id < ne_id
    &&& match p.redirect {
        None => true,
        Some((r, f)) => f < ne_id,
    }
}

/// Step 4.27.1, "take all of the child nodes of furthestBlock and append
/// them to newElement", meets `host::reparent_keeps_host`.
pub proof fn lemma_end_reparent(p: Parser, fb_id: NodeId, ne_id: NodeId, ib: int)
    requires
        host_inv(p),
        !p.stopped,
        ids_valid(p),
        end_pre(p, fb_id, ne_id, ib),
    ensures
        reparent_keeps_host(p, fb_id, ne_id),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    lemma_host_inv(p);
    let d = p.doc;
    if hi(d, fb_id, ne_id) {
        lemma_hi_top(d, fb_id, ne_id);
    }
    assert forall|a: int, b: int| #![trigger p.open[b], p.open[a]] 0 <= a < b < p.open.len() implies !(hi(d, p.open[b].id, ne_id)
        && p.open[a].id != fb_id && hi(d, fb_id, p.open[a].id)) by {
        if hi(d, p.open[b].id, ne_id) && p.open[a].id != fb_id && hi(d, fb_id, p.open[a].id) {
            lemma_hi_top(d, p.open[b].id, ne_id);
            assert(b == ib + 1);
            if a < ib {
                assert(!hi(d, p.open[ib].id, p.open[a].id));
            }
        }
    }
    if let Some((r, f)) = p.redirect {
        assert(!hi(d, p.open[ib].id, f));
    }
}

/// After step 4.27.1 (parser `p5`), a node below newElement was created
/// after it or was below furthestBlock (and is not furthestBlock) before
/// the step.
pub proof fn lemma_end_below(p: Parser, fb_id: NodeId, ne_id: NodeId, ib: int, x: NodeId)
    requires
        host_inv(p),
        !p.stopped,
        ids_valid(p),
        dom::wf(p.doc),
        end_pre(p, fb_id, ne_id, ib),
        dom::valid(p.doc, x),
        hi(dom_reparent_children(p, fb_id, ne_id).doc, ne_id, x),
    ensures
        x >= ne_id || (hi(p.doc, fb_id, x) && x != fb_id),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    lemma_host_inv(p);
    let d = p.doc;
    let p5 = dom_reparent_children(p, fb_id, ne_id);
    if p5.doc == d {
        assert(!(x < ne_id) || !hi(d, ne_id, x));
    } else {
        assert(dom::reparent_children_requires(d, fb_id, ne_id));
        lemma_end_reparent(p, fb_id, ne_id, ib);
        lemma_host_reparent(p, fb_id, ne_id);
        lemma_host_inv(p5);
        lemma_reparent_grafted(d, fb_id, ne_id);
        clazel_dom::lemmas::lemma_reparent_facts(d, fb_id, ne_id);
        let kids = d.nodes[fb_id as int].children;
        let g = kids.to_set();
        lemma_end_kids(p, fb_id, ne_id, ib);
        let m = lemma_hi_graft(d, p5.doc, g, ne_id, ne_id, x);
        match m {
            None => {
                assert(!(x < ne_id) || !hi(d, ne_id, x));
            },
            Some(n) => {
                let j = choose|j: int| 0 <= j < kids.len() && kids[j] == n;
                assert(d.nodes[kids[j] as int].parent == Some(fb_id));
                lemma_below_child(d, fb_id, n, x);
            },
        }
    }
}

/// No child of furthestBlock is a host-including inclusive ancestor of the
/// new element (which has no step up).
pub proof fn lemma_end_kids(p: Parser, fb_id: NodeId, ne_id: NodeId, ib: int)
    requires
        host_inv(p),
        !p.stopped,
        ids_valid(p),
        dom::wf(p.doc),
        end_pre(p, fb_id, ne_id, ib),
        dom::reparent_children_requires(p.doc, fb_id, ne_id),
    ensures
        forall|n: NodeId| #[trigger]
            p.doc.nodes[fb_id as int].children.to_set().contains(n) && dom::valid(p.doc, n) ==> !hi(p.doc, n, ne_id),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    lemma_host_inv(p);
    let d = p.doc;
    clazel_dom::lemmas::lemma_reparent_facts(d, fb_id, ne_id);
    let kids = d.nodes[fb_id as int].children;
    assert forall|n: NodeId| #[trigger] kids.to_set().contains(n) && dom::valid(d, n) implies !hi(d, n, ne_id) by {
        if hi(d, n, ne_id) {
            lemma_hi_top(d, n, ne_id);
            let j = choose|j: int| 0 <= j < kids.len() && kids[j] == n;
            assert(d.nodes[kids[j] as int].parent == Some(fb_id));
            lemma_top_parentless(d, ne_id);
        }
    }
}

/// After step 4.27.1 (parser `p5`), a host-including inclusive ancestor of
/// furthestBlock, or of the redirection map's fragment, was one before the
/// step.
pub proof fn lemma_end_above(p: Parser, fb_id: NodeId, ne_id: NodeId, ib: int, a: NodeId, t: NodeId)
    requires
        host_inv(p),
        !p.stopped,
        ids_valid(p),
        dom::wf(p.doc),
        end_pre(p, fb_id, ne_id, ib),
        t == fb_id || (p.redirect is Some && t == p.redirect->Some_0.1),
        hi(dom_reparent_children(p, fb_id, ne_id).doc, a, t),
    ensures
        hi(p.doc, a, t),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    lemma_host_inv(p);
    let d = p.doc;
    let p5 = dom_reparent_children(p, fb_id, ne_id);
    if p5.doc != d {
        assert(dom::reparent_children_requires(d, fb_id, ne_id));
        lemma_end_reparent(p, fb_id, ne_id, ib);
        lemma_host_reparent(p, fb_id, ne_id);
        lemma_host_inv(p5);
        lemma_reparent_grafted(d, fb_id, ne_id);
        clazel_dom::lemmas::lemma_reparent_facts(d, fb_id, ne_id);
        let kids = d.nodes[fb_id as int].children;
        let g = kids.to_set();
        lemma_end_kids(p, fb_id, ne_id, ib);
        let m = lemma_hi_graft(d, p5.doc, g, ne_id, a, t);
        if let Some(n) = m {
            let j = choose|j: int| 0 <= j < kids.len() && kids[j] == n;
            assert(d.nodes[kids[j] as int].parent == Some(fb_id));
            if t == fb_id {
                lemma_child_not_above(d, n);
            } else {
                lemma_below_child(d, fb_id, n, t);
                assert(!hi(d, p.open[ib].id, t));
            }
        }
    }
}

/// Step 4.27.3, "insert newElement into newElementParent" (furthestBlock,
/// or the redirection map's fragment in its place), after step 4.27.1,
/// meets `host::insert_keeps_host`.
pub proof fn lemma_end_insert(p: Parser, fb_id: NodeId, ne_id: NodeId, ib: int, t: NodeId)
    requires
        host_inv(p),
        !p.stopped,
        ids_valid(p),
        dom::wf(p.doc),
        end_pre(p, fb_id, ne_id, ib),
        t == fb_id || (p.redirect is Some && t == p.redirect->Some_0.1),
    ensures
        insert_keeps_host(dom_reparent_children(p, fb_id, ne_id), ne_id, t),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    lemma_host_inv(p);
    let d = p.doc;
    let p5 = dom_reparent_children(p, fb_id, ne_id);
    assert(p5.open == p.open && p5.redirect == p.redirect);
    assert(dom::valid(d, t));
    // newElement is no host-including inclusive ancestor of the parent.
    if hi(p5.doc, ne_id, t) {
        lemma_end_above(p, fb_id, ne_id, ib, ne_id, t);
        assert(!(t < ne_id) || !hi(d, ne_id, t));
    }
    assert forall|a: int, b: int| #![trigger p5.open[b], p5.open[a]] 0 <= a < b < p5.open.len() implies !(hi(
        p5.doc,
        p5.open[b].id,
        t,
    ) && hi(p5.doc, ne_id, p5.open[a].id)) by {
        if hi(p5.doc, p5.open[b].id, t) && hi(p5.doc, ne_id, p5.open[a].id) {
            lemma_end_below(p, fb_id, ne_id, ib, p.open[a].id);
            // `a` is below furthestBlock in the stack.
            if a < ib {
                assert(!hi(d, p.open[ib].id, p.open[a].id));
            }
            assert(a >= ib + 1);
            lemma_end_above(p, fb_id, ne_id, ib, p.open[b].id, t);
            if t == fb_id {
                assert(!hi(d, p.open[b].id, p.open[ib].id));
            }
        }
    }
    if let Some((r, f)) = p.redirect {
        if hi(p5.doc, ne_id, f) {
            lemma_end_above(p, fb_id, ne_id, ib, ne_id, f);
            assert(!(f < ne_id) || !hi(d, ne_id, f));
        }
    }
}

/// Step 4.5 gives `host::wall_clear` (and `host::scope_clear`):
/// formattingElement is in scope, so no entry after it in the stack is one
/// of the elements a search in scope stops at, among them `table` and
/// `template`.
pub proof fn lemma_scope_wall_clear(o: Seq<Elem>, f: spec_fn(Elem) -> bool)
    requires
        in_scope_from(o, o.len() as int, f, Scope::Default),
    ensures
        scope_clear(o, last_index_where(o, o.len() as int, f)),
        wall_clear(o, last_index_where(o, o.len() as int, f)),
{
    crate::reachable::cells::lemma_scope_above(o, o.len() as int, f, Scope::Default);
    let k = last_index_where(o, o.len() as int, f);
    assert forall|j: int| k < j < o.len() implies !crate::invariant::table_wall(#[trigger] o[j]) && !scope_wall(o[j]) by {
        assert(!in_scope_list(o[j], Scope::Default));
    }
}

/// The "in head" `template` start tag pushes the `template` element it
/// has just created (parser `p3`, from the parser `p2`) before inserting it
/// at the place computed before the push: the push keeps the invariant,
/// and the insertion has what "insert an element at the adjusted insertion
/// location" needs of a new element.
pub proof fn lemma_template_start_host(p2: Parser, p3: Parser, template: Elem)
    requires
        dinv(p2),
        rooted(p2),
        !p3.stopped,
        p3 == (Parser { doc: p3.doc, ..p2 }),
        old_same(p2.doc, p3.doc),
        template.id == p2.doc.nodes.len(),
        dom::host_acyclic(p3.doc) ==> low(p3.doc, template.id),
    ensures
        ({
            let loc = appropriate_place(p3, None);
            let p4 = push(p3, template);
            &&& host_inv(p3) ==> host_inv(p4)
            &&& host_inv(p4) ==> low(p4.doc, template.id) && adjusted_location(p4, Some(loc)).parent < template.id && ids_below(
                p4,
                template.id,
            )
            &&& dom::valid(p2.doc, adjusted_location(p4, Some(loc)).parent)
        }),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
    let loc = appropriate_place(p3, None);
    let p4 = push(p3, template);
    lemma_place_same(p2, p3, None);
    lemma_dinv_ids_below(p2, template.id);
    lemma_dinv_ids(p2);
    lemma_dinv(p2);
    if host_inv(p3) {
        lemma_host_inv(p3);
        lemma_low_entry_ok(p3, template);
        lemma_host_push(p3, template);
    }
    if host_inv(p4) {
        lemma_host_inv(p4);
    }
    let n = p3.open.len() as int;
    assert forall|i: int| 0 <= i < p4.open.len() - 1 implies (#[trigger] p4.open[i]).id < template.id by {
        assert(p4.open[i] == p3.open[i]);
    }
    assert(p4.open[n] == template);
}

/// A [`low`] node above the whole stack may be pushed.
pub proof fn lemma_low_entry_ok(p: Parser, e: Elem)
    requires
        low(p.doc, e.id),
        forall|i: int| 0 <= i < p.open.len() ==> (#[trigger] p.open[i]).id < e.id,
        match p.redirect {
            None => true,
            Some((r, f)) => f < e.id,
        },
    ensures
        entry_ok(p, p.open.len() as int, e),
{
    reveal(ids_valid);
    reveal(entry_ok);
    reveal(ids_below);
    reveal(old_same);
}

} // verus!
