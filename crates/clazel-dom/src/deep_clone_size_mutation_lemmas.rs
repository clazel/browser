//! Concrete instances of the size theorems of deep clone, the kill
//! certificates of the mutations of [`subtree_count`], [`subtree_size`],
//! [`clone_deep_refused`], [`clone_deep_grew`] and [`ranked_at`] in
//! `mutations.json` (`xtask/src/mutate.rs`). Each lemma states a fact about
//! a concrete arena that a proven theorem implies for the real spec, and
//! that a mutant makes false (the certificate's witness).
//!
//! The arenas: [`ds_leaf`] is a document (0) and an element (1), and
//! [`ds_tmpl`] a document, a template element (1) and its contents, the
//! fragment (2). A deep clone of node 1 is [`ds_leaf_copy`], resp.
//! [`ds_tmpl_copy`]: the shallow clone, which is a valid deep clone of a node
//! with no children.

#[cfg(verus_only)]
use super::contract::*;
#[cfg(verus_only)]
use super::deep_clone_size_lemmas::*;
#[cfg(verus_only)]
use super::lemmas::*;
#[cfg(verus_only)]
use super::mutation_lemmas::*;
#[cfg(verus_only)]
use super::ops_lemmas::*;
#[cfg(verus_only)]
use super::ops_mutation_lemmas::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A document and an element (1).
pub open spec fn ds_leaf() -> Document {
    ol_d1()
}

/// The shallow clone of node 1 of [`ds_leaf`]: node 2.
pub open spec fn ds_leaf_copy() -> Document {
    clone_node(ds_leaf(), 1).0
}

/// The source of the copy of [`ds_leaf`].
pub open spec fn ds_leaf_src() -> Seq<NodeId> {
    seq![1usize]
}

/// The sources of the copies of [`ds_tmpl`].
pub open spec fn ds_tmpl_src() -> Seq<NodeId> {
    seq![1usize, 2usize]
}

/// A document, a template element (1) and its contents (2).
pub open spec fn ds_tmpl() -> Document {
    ol_template()
}

/// The shallow clone of node 1 of [`ds_tmpl`]: a template (3) and its
/// contents (4).
pub open spec fn ds_tmpl_copy() -> Document {
    clone_node(ds_tmpl(), 1).0
}

/// A ranking of [`ds_leaf`].
pub open spec fn ds_rank_leaf() -> Seq<nat> {
    seq![0nat, 0nat]
}

/// A ranking of [`ds_tmpl`]: the contents ranks above the template.
pub open spec fn ds_rank_tmpl() -> Seq<nat> {
    seq![0nat, 0nat, 1nat]
}

/// [`ds_leaf`] is well formed and host-acyclic, and node 1 may be cloned.
pub proof fn ds_leaf_facts()
    ensures
        wf(ds_leaf()),
        ds_leaf().nodes.len() == 2,
        host_acyclic(ds_leaf()),
        clone_deep_requires(ds_leaf(), 1),
        can_create(ds_leaf(), clone_count(ds_leaf(), 1)),
        wf(ds_leaf_copy()),
        ds_leaf_copy().nodes.len() == 3,
{
    theorem_new_document_wf(seq![]);
    assert(creatable(ol_d0(), ml_element())) by (compute_only);
    assert(can_create(ol_d0(), 1)) by (compute_only);
    theorem_create_node_wf(ol_d0(), ml_element());
    assert(ds_leaf().nodes.len() == 2) by (compute_only);
    let rank = ds_rank_leaf();
    assert(ranked_at(ds_leaf(), ds_rank_leaf(), 0)) by (compute_only);
    assert(ranked_at(ds_leaf(), ds_rank_leaf(), 1)) by (compute_only);
    assert(host_ranked(ds_leaf(), rank)) by {
        assert forall|i: int| 0 <= i < ds_leaf().nodes.len() implies #[trigger] ranked_at(ds_leaf(), rank, i) by {
            if i == 0 {
            } else {
                assert(i == 1);
            }
        }
    }
    assert(valid(ds_leaf(), 1));
    assert(!(ds_leaf().nodes[1].kind is Document)) by (compute_only);
    assert(clone_requires(ds_leaf(), 1));
    assert(can_create(ds_leaf(), clone_count(ds_leaf(), 1))) by (compute_only);
    theorem_clone_node_wf(ds_leaf(), 1);
    assert(ds_leaf_copy().nodes.len() == 3) by (compute_only);
}

/// The deep clone of node 1 of [`ds_leaf`] is its shallow clone, and its
/// subtree is one node.
pub proof fn ds_leaf_exact()
    ensures
        subtree_size(ds_leaf(), 1) == 1,
{
    ds_leaf_facts();
    theorem_clone_node_wf(ds_leaf(), 1);
    assert(ds_leaf().nodes[1].children.len() == 0) by (compute_only);
    assert(ds_leaf_copy().nodes[2].children.len() == 0) by (compute_only);
    assert(deep_copy_kind(ds_leaf(), ds_leaf_copy(), ds_leaf_src(), 0)) by (compute_only);
    assert(deep_copy_children(ds_leaf(), ds_leaf_copy(), ds_leaf_src(), 0));
    assert(deep_copy_node(ds_leaf(), ds_leaf_copy(), ds_leaf_src(), 0));
    assert(deep_clone_src(ds_leaf(), 1, ds_leaf_copy(), ds_leaf_src())) by {
        assert forall|t: int| 0 <= t < ds_leaf_src().len() implies valid(ds_leaf(), #[trigger] ds_leaf_src()[t]) by {}
        assert forall|t: int| 0 <= t < ds_leaf_src().len() implies #[trigger] deep_copy_node(ds_leaf(), ds_leaf_copy(), ds_leaf_src(), t) by {}
    }
    theorem_deep_clone_size(ds_leaf(), 1, ds_leaf_copy(), ds_leaf_src());
}

/// [`ds_tmpl`] is well formed and host-acyclic, and node 1 may be cloned.
pub proof fn ds_tmpl_facts()
    ensures
        wf(ds_tmpl()),
        ds_tmpl().nodes.len() == 3,
        host_acyclic(ds_tmpl()),
        clone_deep_requires(ds_tmpl(), 1),
        can_create(ds_tmpl(), clone_count(ds_tmpl(), 1)),
        wf(ds_tmpl_copy()),
        ds_tmpl_copy().nodes.len() == 5,
{
    theorem_new_document_wf(seq![]);
    assert(creatable(ol_d0(), ml_element())) by (compute_only);
    assert(can_create(ol_d0(), 1)) by (compute_only);
    theorem_create_node_wf(ol_d0(), ml_element());
    assert(ol_d1().nodes[1].kind is Element) by (compute_only);
    assert(ol_d1().nodes[1].kind->Element_template_contents is None) by (compute_only);
    theorem_create_template_contents_wf(ol_d1(), 1);
    assert(ds_tmpl().nodes.len() == 3) by (compute_only);
    let rank = ds_rank_tmpl();
    assert(ranked_at(ds_tmpl(), ds_rank_tmpl(), 0)) by (compute_only);
    assert(ranked_at(ds_tmpl(), ds_rank_tmpl(), 1)) by (compute_only);
    assert(ranked_at(ds_tmpl(), ds_rank_tmpl(), 2)) by (compute_only);
    assert(host_ranked(ds_tmpl(), rank)) by {
        assert forall|i: int| 0 <= i < ds_tmpl().nodes.len() implies #[trigger] ranked_at(ds_tmpl(), rank, i) by {
            if i == 0 {
            } else if i == 1 {
            } else {
                assert(i == 2);
            }
        }
    }
    assert(valid(ds_tmpl(), 1));
    assert(!(ds_tmpl().nodes[1].kind is Document)) by (compute_only);
    assert(clone_requires(ds_tmpl(), 1));
    assert(ds_tmpl().nodes[1].kind is Element) by (compute_only);
    assert(ds_tmpl().nodes[1].kind->Element_template_contents is Some) by (compute_only);
    assert(can_create(ds_tmpl(), clone_count(ds_tmpl(), 1))) by (compute_only);
    theorem_clone_node_wf(ds_tmpl(), 1);
    assert(ds_tmpl_copy().nodes.len() == 5) by (compute_only);
}

/// The deep clone of the template, node 1 of [`ds_tmpl`], is its shallow
/// clone (the template and its contents), and its subtree is two nodes:
/// the template and its contents.
pub proof fn ds_tmpl_exact()
    ensures
        subtree_size(ds_tmpl(), 1) == 2,
{
    ds_tmpl_facts();
    theorem_clone_node_wf(ds_tmpl(), 1);
    assert(ds_tmpl().nodes[1].children.len() == 0) by (compute_only);
    assert(ds_tmpl().nodes[2].children.len() == 0) by (compute_only);
    assert(ds_tmpl_copy().nodes[3].children.len() == 0) by (compute_only);
    assert(ds_tmpl_copy().nodes[4].children.len() == 0) by (compute_only);
    assert(deep_copy_kind(ds_tmpl(), ds_tmpl_copy(), ds_tmpl_src(), 0)) by (compute_only);
    assert(deep_copy_kind(ds_tmpl(), ds_tmpl_copy(), ds_tmpl_src(), 1)) by (compute_only);
    assert(deep_copy_children(ds_tmpl(), ds_tmpl_copy(), ds_tmpl_src(), 0));
    assert(deep_copy_children(ds_tmpl(), ds_tmpl_copy(), ds_tmpl_src(), 1));
    assert(deep_clone_src(ds_tmpl(), 1, ds_tmpl_copy(), ds_tmpl_src())) by {
        assert forall|t: int| 0 <= t < ds_tmpl_src().len() implies valid(ds_tmpl(), #[trigger] ds_tmpl_src()[t]) by {}
        assert forall|t: int| 0 <= t < ds_tmpl_src().len() implies #[trigger] deep_copy_node(ds_tmpl(), ds_tmpl_copy(), ds_tmpl_src(), t) by {
            assert(deep_copy_kind(ds_tmpl(), ds_tmpl_copy(), ds_tmpl_src(), t));
            assert(deep_copy_children(ds_tmpl(), ds_tmpl_copy(), ds_tmpl_src(), t));
        }
    }
    theorem_deep_clone_size(ds_tmpl(), 1, ds_tmpl_copy(), ds_tmpl_src());
}

/// The deep clone of the leaf meets the size clause of the contract.
pub proof fn ds_leaf_grew()
    ensures
        clone_deep_grew(ds_leaf(), 1, ds_leaf_copy()),
{
    ds_leaf_exact();
    ds_leaf_facts();
    assert(ds_leaf_copy().nodes.len() == 3) by (compute_only);
}

/// Refusing to clone the leaf, leaving the arena as it was, is not allowed:
/// the copy fits.
pub proof fn ds_leaf_cannot_refuse()
    ensures
        !clone_deep_refused(ds_leaf(), 1, ds_leaf()),
{
    ds_leaf_exact();
    ds_leaf_facts();
    if clone_deep_refused(ds_leaf(), 1, ds_leaf()) {
        theorem_clone_deep_refuses_exactly_when_full(ds_leaf(), 1, ds_leaf(), None);
        assert(can_create(ds_leaf(), 1)) by (compute_only);
        assert(false);
    }
}

/// An arena that does not grow is not a clone of the leaf.
pub proof fn ds_leaf_unchanged_is_not_grown()
    ensures
        !clone_deep_grew(ds_leaf(), 1, ds_leaf()),
{
    ds_leaf_exact();
    if clone_deep_grew(ds_leaf(), 1, ds_leaf()) {
        theorem_clone_deep_grew_means(ds_leaf(), 1, ds_leaf());
        assert(false);
    }
}

/// The ranking of a node and its parent is strict: nodes 1 and 0 of a
/// document with node 1 appended to it, ranked alike, are not ranked.
pub proof fn ds_rank_parent_strict()
    ensures
        !ranked_at(ml_doc_child(), seq![0nat, 0nat, 0nat], 1),
{
    ml_doc_child_wf();
    ml_doc3_wf();
    assert(ml_doc_child().nodes.len() == 3) by (compute_only);
    if ranked_at(ml_doc_child(), seq![0nat, 0nat, 0nat], 1) {
        theorem_ranked_at_facts(ml_doc_child(), seq![0nat, 0nat, 0nat], 1);
        assert(ml_doc_child().nodes[1].parent == Some(0usize));
        assert(false);
    }
}

/// The ranking of a fragment and its host is strict: a template's contents
/// ranked like the template is not ranked.
pub proof fn ds_rank_host_strict()
    ensures
        !ranked_at(ds_tmpl(), seq![0nat, 0nat, 0nat], 2),
{
    ds_tmpl_facts();
    assert(ds_tmpl().nodes[2].kind is DocumentFragment) by (compute_only);
    assert(ds_tmpl().nodes[2].kind->DocumentFragment_host == Some(1usize)) by (compute_only);
    if ranked_at(ds_tmpl(), seq![0nat, 0nat, 0nat], 2) {
        theorem_ranked_at_facts(ds_tmpl(), seq![0nat, 0nat, 0nat], 2);
        assert(false);
    }
}

/// A rank is below the node count.
pub proof fn ds_rank_bounded()
    ensures
        !ranked_at(ds_leaf(), seq![5nat, 0nat], 0),
{
    ds_leaf_facts();
    if ranked_at(ds_leaf(), seq![5nat, 0nat], 0) {
        theorem_ranked_at_facts(ds_leaf(), seq![5nat, 0nat], 0);
        assert(false);
    }
}

} // verus!
