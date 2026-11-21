//! Concrete instances of the theorems of [`super::ops_lemmas`], the kill
//! certificates of Phase 7 item 7.13's mutations in `mutations.json`
//! (`xtask/src/mutate.rs`). Each lemma states what a theorem says about a
//! small concrete arena; a certificate evaluates the mutated spec on that
//! arena (`compute_only`) and shows it contradicts the lemma.
//!
//! The arenas: [`ol_base`] is a document (0) with an element `A` (1) child,
//! an element `B` (2) child of `A`, a text node (3) child of `B`, a
//! parentless text node (4), a parentless element (5), and a fragment (6)
//! with two text children (7 and 8). [`ol_attrs`] is a document and a
//! parentless element (1) with two attributes. [`ol_template`] is a
//! document and a parentless template element (1) whose contents is the
//! fragment 2.
//!
//! Every `by (compute_only)` here is evaluated whenever this module is
//! built, mutants included, so each evaluates only spec parts that no
//! mutation changes; facts that a mutation would change come from the
//! theorems instead.

use super::lemmas::*;
use super::mutation_lemmas::*;
use super::ops_lemmas::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The base arena, step by step: the document.
pub open spec fn ol_d0() -> Document {
    new_document(seq![])
}

/// Node 1, an element.
pub open spec fn ol_d1() -> Document {
    create_node(ol_d0(), ml_element()).0
}

/// Node 2, an element.
pub open spec fn ol_d2() -> Document {
    create_node(ol_d1(), ml_element()).0
}

/// Node 3, a text node.
pub open spec fn ol_d3() -> Document {
    create_node(ol_d2(), ml_text()).0
}

/// Node 4, a text node.
pub open spec fn ol_d4() -> Document {
    create_node(ol_d3(), ml_text()).0
}

/// Node 5, an element.
pub open spec fn ol_d5() -> Document {
    create_node(ol_d4(), ml_element()).0
}

/// Node 6, a fragment.
pub open spec fn ol_d6() -> Document {
    create_node(ol_d5(), NodeKind::DocumentFragment { host: None }).0
}

/// Node 7, a text node.
pub open spec fn ol_d7() -> Document {
    create_node(ol_d6(), ml_text()).0
}

/// Node 8, a text node.
pub open spec fn ol_d8() -> Document {
    create_node(ol_d7(), ml_text()).0
}

/// Node 1 appended to the document.
pub open spec fn ol_d9() -> Document {
    append(ol_d8(), 0, 1)
}

/// Node 2 appended to node 1.
pub open spec fn ol_d10() -> Document {
    append(ol_d9(), 1, 2)
}

/// Node 3 appended to node 2.
pub open spec fn ol_d11() -> Document {
    append(ol_d10(), 2, 3)
}

/// Node 7 appended to the fragment.
pub open spec fn ol_d12() -> Document {
    append(ol_d11(), 6, 7)
}

/// The base arena: node 8 appended to the fragment.
pub open spec fn ol_base() -> Document {
    append(ol_d12(), 6, 8)
}

/// Creating a node of kind `k` in a well-formed arena that holds `n` nodes
/// is allowed.
proof fn ol_create(d: Document, k: NodeKind, n: nat)
    requires
        wf(d),
        creatable(d, k),
        d.nodes.len() == n,
        n + 1 <= max_nodes(),
    ensures
        wf(create_node(d, k).0),
        create_node(d, k).0.nodes.len() == n + 1,
{
    theorem_create_node_wf(d, k);
}

/// The base arena is well formed and has the parents and kinds the
/// description says.
pub proof fn ol_base_wf()
    ensures
        wf(ol_base()),
        ol_base().nodes.len() == 9,
{
    theorem_new_document_wf(seq![]);
    ol_create(ol_d0(), ml_element(), 1);
    ol_create(ol_d1(), ml_element(), 2);
    ol_create(ol_d2(), ml_text(), 3);
    ol_create(ol_d3(), ml_text(), 4);
    ol_create(ol_d4(), ml_element(), 5);
    ol_create(ol_d5(), NodeKind::DocumentFragment { host: None }, 6);
    ol_create(ol_d6(), ml_text(), 7);
    ol_create(ol_d7(), ml_text(), 8);
    assert(ol_d8().nodes.len() == 9) by (compute_only);
    assert(ol_d8().nodes[0].kind is Document) by (compute_only);
    assert(ol_d8().nodes[1].kind is Element) by (compute_only);
    assert(!is_inclusive_ancestor(ol_d8(), 1, 0)) by (compute_only);
    theorem_append_wf(ol_d8(), 0, 1);
    assert(ol_d9().nodes.len() == 9) by (compute_only);
    assert(ol_d9().nodes[2].kind is Element) by (compute_only);
    assert(ol_d9().nodes[1].kind is Element) by (compute_only);
    assert(!is_inclusive_ancestor(ol_d9(), 2, 1)) by (compute_only);
    theorem_append_wf(ol_d9(), 1, 2);
    assert(ol_d10().nodes.len() == 9) by (compute_only);
    assert(ol_d10().nodes[3].kind is Text) by (compute_only);
    assert(ol_d10().nodes[2].kind is Element) by (compute_only);
    assert(!is_inclusive_ancestor(ol_d10(), 3, 2)) by (compute_only);
    theorem_append_wf(ol_d10(), 2, 3);
    assert(ol_d11().nodes.len() == 9) by (compute_only);
    assert(ol_d11().nodes[7].kind is Text) by (compute_only);
    assert(ol_d11().nodes[6].kind is DocumentFragment) by (compute_only);
    assert(!is_inclusive_ancestor(ol_d11(), 7, 6)) by (compute_only);
    theorem_append_wf(ol_d11(), 6, 7);
    assert(ol_d12().nodes.len() == 9) by (compute_only);
    assert(ol_d12().nodes[8].kind is Text) by (compute_only);
    assert(ol_d12().nodes[6].kind is DocumentFragment) by (compute_only);
    assert(!is_inclusive_ancestor(ol_d12(), 8, 6)) by (compute_only);
    theorem_append_wf(ol_d12(), 6, 8);
}

/// "Ensure pre-insertion validity" (step 2): inserting `A` into its
/// descendant `B` is an error.
pub proof fn ol_validity_ancestor()
    ensures
        pre_insert_error(ol_base(), 1, 2, None) is Some,
{
    ol_base_wf();
    if pre_insert_error(ol_base(), 1, 2, None) is None {
        lemma_pre_insert_valid(ol_base(), 1, 2, None);
        assert(is_inclusive_ancestor(ol_base(), 1, 2)) by (compute_only);
    }
}

/// "Ensure pre-insertion validity" (step 3): a reference child that is not
/// a child of the parent is an error.
pub proof fn ol_validity_not_found()
    ensures
        pre_insert_error(ol_base(), 5, 2, Some(1)) is Some,
{
    ol_base_wf();
    if pre_insert_error(ol_base(), 5, 2, Some(1)) is None {
        lemma_pre_insert_valid(ol_base(), 5, 2, Some(1));
        assert(ol_base().nodes[1].parent == Some(0usize)) by (compute_only);
    }
}

/// "Ensure pre-insertion validity" (step 1): a text node cannot be a
/// parent.
pub proof fn ol_validity_leaf_parent()
    ensures
        pre_insert_error(ol_base(), 5, 3, None) is Some,
{
    ol_base_wf();
    if pre_insert_error(ol_base(), 5, 3, None) is None {
        lemma_pre_insert_valid(ol_base(), 5, 3, None);
        assert(ol_base().nodes[3].kind is Text) by (compute_only);
    }
}

/// "Ensure pre-insertion validity" (step 4): a document cannot be
/// inserted.
pub proof fn ol_validity_document_node()
    ensures
        pre_insert_error(ol_base(), 0, 5, None) is Some,
{
    ol_base_wf();
    if pre_insert_error(ol_base(), 0, 5, None) is None {
        lemma_pre_insert_valid(ol_base(), 0, 5, None);
        assert(ol_base().nodes[0].kind is Document) by (compute_only);
    }
}

/// `theorem_replace_wf`: replacing the text node 3 of `B` by the
/// parentless text node 4 leaves 3 without a parent.
pub proof fn ol_replace_detaches()
    ensures
        replace(ol_base(), 3, 4, 2).nodes[3].parent is None,
{
    ol_base_wf();
    assert(replace_error(ol_base(), 3, 4, 2) is None) by (compute_only);
    theorem_replace_wf(ol_base(), 3, 4, 2);
}

/// `theorem_replace_all_wf`: replacing all of `B`'s children by the text
/// node 4 leaves it that one child.
pub proof fn ol_replace_all_clears()
    ensures
        children(replace_all(ol_base(), Some(4), 2), 2).len() == 1,
{
    ol_base_wf();
    assert(ol_base().nodes[2].kind is Element) by (compute_only);
    assert(ol_base().nodes[4].kind is Text) by (compute_only);
    assert(!is_host_including_inclusive_ancestor(ol_base(), 4, 2)) by (compute_only);
    theorem_replace_all_wf(ol_base(), Some(4), 2);
}

/// `theorem_insert_any_wf` through `lemma_pre_insert_valid`: inserting the
/// fragment 6 into `B` gives `B` the children 3, 7, 8, in that order.
#[verifier::rlimit(400)]
pub proof fn ol_fragment_order()
    ensures
        pre_insert(ol_base(), 6, 2, None).nodes[2].children == seq![3usize, 7usize, 8usize],
{
    ol_base_wf();
    assert(pre_insert_error(ol_base(), 6, 2, None) is None) by (compute_only);
    lemma_pre_insert_valid(ol_base(), 6, 2, None);
    assert(pre_insert_reference(ol_base(), 6, None) == None::<NodeId>);
    assert(ol_base().nodes[6].kind is DocumentFragment) by (compute_only);
    lemma_insert_fragment_children(ol_base(), 6, 2, None);
    assert(ol_base().nodes[2].children == seq![3usize]) by (compute_only);
    assert(ol_base().nodes[6].children == seq![7usize, 8usize]) by (compute_only);
    assert(seq![3usize] + seq![7usize, 8usize] =~= seq![3usize, 7usize, 8usize]);
}

/// The element kind of [`ol_attrs`]: attributes `a1` and `a2`.
pub open spec fn ol_attr(n: u32) -> Attr {
    Attr { namespace: None, prefix: None, local_name: seq![n], value: seq![n] }
}

/// An element with two attributes.
pub open spec fn ol_attr_kind() -> NodeKind {
    NodeKind::Element {
        namespace: Some(Namespace::Html),
        prefix: None,
        local_name: seq![],
        attributes: seq![ol_attr(1), ol_attr(2)],
        template_contents: None,
        form_owner: None,
    }
}

/// A document and a parentless element (1) with two attributes.
pub open spec fn ol_attrs() -> Document {
    create_node(ol_d0(), ol_attr_kind()).0
}

/// [`ol_attrs`] is well formed.
pub proof fn ol_attrs_wf()
    ensures
        wf(ol_attrs()),
        ol_attrs().nodes.len() == 2,
        attribute_requires(ol_attrs(), 1, 0),
        attribute_requires(ol_attrs(), 1, 1),
        clone_requires(ol_attrs(), 1),
        can_create(ol_attrs(), 1),
{
    theorem_new_document_wf(seq![]);
    assert(creatable(ol_d0(), ol_attr_kind()));
    theorem_create_node_wf(ol_d0(), ol_attr_kind());
    assert(ol_attrs().nodes.len() == 2) by (compute_only);
    assert(ol_attrs().nodes[1].kind is Element) by (compute_only);
    assert(ol_attrs().nodes[1].kind->Element_attributes.len() == 2) by (compute_only);
    assert(clone_count(ol_attrs(), 1) == 1) by (compute_only);
}

/// `theorem_change_attribute_wf`: the new value is the attribute's value.
pub proof fn ol_change_value()
    ensures
        change_attribute(ol_attrs(), 1, 0, seq![9u32]).nodes[1].kind->Element_attributes[0].value == seq![9u32],
{
    ol_attrs_wf();
    theorem_change_attribute_wf(ol_attrs(), 1, 0, seq![9u32]);
    assert(ol_attrs().nodes[1].kind->Element_attributes[0] == ol_attr(1)) by (compute_only);
}

/// `theorem_remove_attribute_wf`: removing the second attribute leaves the
/// first.
pub proof fn ol_remove_index()
    ensures
        remove_attribute(ol_attrs(), 1, 1).nodes[1].kind->Element_attributes[0].local_name == seq![1u32],
{
    ol_attrs_wf();
    theorem_remove_attribute_wf(ol_attrs(), 1, 1);
    assert(ol_attrs().nodes[1].kind->Element_attributes.remove(1)[0].local_name == seq![1u32]) by (compute_only);
}

/// `theorem_replace_attribute_wf`: replacing an attribute keeps the length
/// of the list.
pub proof fn ol_replace_attribute_length()
    ensures
        replace_attribute(ol_attrs(), 1, 0, ol_attr(3)).nodes[1].kind->Element_attributes.len() == 2,
{
    ol_attrs_wf();
    theorem_replace_attribute_wf(ol_attrs(), 1, 0, ol_attr(3));
    assert(ol_attrs().nodes[1].kind->Element_attributes.len() == 2) by (compute_only);
}

/// `theorem_clone_node_wf`: the copy of an element has the element's two
/// attributes.
pub proof fn ol_clone_attributes()
    ensures
        clone_node(ol_attrs(), 1).0.nodes[2].kind->Element_attributes.len() == 2,
{
    ol_attrs_wf();
    assert(clone_count(ol_attrs(), 1) == 1) by (compute_only);
    theorem_clone_node_wf(ol_attrs(), 1);
    assert(clone_node(ol_attrs(), 1).1 == 2usize) by (compute_only);
    assert(ol_attrs().nodes[1].kind->Element_attributes.len() == 2) by (compute_only);
}

/// A document and a parentless template element (1) with its contents (2).
pub open spec fn ol_template() -> Document {
    create_template_contents(create_node(ol_d0(), ml_element()).0, 1).0
}

/// `theorem_clone_node_wf`: cloning a template creates two nodes.
pub proof fn ol_clone_count()
    ensures
        clone_count(ol_template(), 1) == 2,
{
    theorem_new_document_wf(seq![]);
    ol_create(ol_d0(), ml_element(), 1);
    assert(ol_d1().nodes[1].kind is Element) by (compute_only);
    assert(ol_d1().nodes[1].kind->Element_template_contents is None) by (compute_only);
    theorem_create_template_contents_wf(ol_d1(), 1);
    assert(ol_template().nodes.len() == 3) by (compute_only);
    assert(ol_template().nodes[1].kind is Element) by (compute_only);
    assert(ol_template().nodes[1].kind->Element_template_contents is Some) by (compute_only);
    assert(can_create(ol_template(), clone_count(ol_template(), 1))) by (compute_only);
    theorem_clone_node_wf(ol_template(), 1);
    assert(clone_node(ol_template(), 1).0.nodes.len() == 5) by (compute_only);
}

} // verus!
