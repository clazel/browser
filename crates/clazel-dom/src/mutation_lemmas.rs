//! Concrete instances of the theorems of [`super::lemmas`], used as the
//! kill certificates of `mutations.json` (`xtask/src/mutate.rs`). Each
//! lemma states what a theorem says about a small concrete arena; a
//! certificate evaluates the mutated spec on that arena (`compute_only`)
//! and shows it contradicts the lemma.
//!
//! The arenas: [`ml_doc3`] is a document (node 0) and two parentless,
//! empty `Text` nodes (1 and 2); [`ml_doc_child`] is that with node 1
//! appended to the document; [`ml_doc_reparent`] has nodes 1 and 2 as the
//! document's children and a parentless element (3).
//!
//! Every `by (compute_only)` here is evaluated whenever this module is
//! built, mutants included, so each evaluates only spec parts that no
//! mutation changes; facts that a mutation would change (a parent after
//! `append`) come from the theorems instead.

#[allow(unused_imports)]
use super::lemmas::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// An empty `Text` node's kind.
pub open spec fn ml_text() -> NodeKind {
    NodeKind::Text { data: seq![] }
}

/// An HTML element without a name, attributes or template contents.
pub open spec fn ml_element() -> NodeKind {
    NodeKind::Element {
        namespace: Some(Namespace::Html),
        prefix: None,
        local_name: seq![],
        attributes: seq![],
        template_contents: None,
        form_owner: None,
    }
}

/// A document and two parentless `Text` nodes.
pub open spec fn ml_doc3() -> Document {
    create_node(create_node(new_document(seq![]), ml_text()).0, ml_text()).0
}

/// [`ml_doc3`] with node 1 appended to the document.
pub open spec fn ml_doc_child() -> Document {
    append(ml_doc3(), 0, 1)
}

/// [`ml_doc3`] and a parentless element 3.
pub open spec fn ml_doc4() -> Document {
    create_node(ml_doc3(), ml_element()).0
}

/// [`ml_doc4`] with node 1 appended to the document.
pub open spec fn ml_doc5() -> Document {
    append(ml_doc4(), 0, 1)
}

/// The document with children 1 and 2, and a parentless element 3.
pub open spec fn ml_doc_reparent() -> Document {
    append(ml_doc5(), 0, 2)
}

/// [`ml_doc3`] is well formed.
pub proof fn ml_doc3_wf()
    ensures
        wf(ml_doc3()),
        ml_doc3().nodes.len() == 3,
{
    let d0 = new_document(seq![]);
    theorem_new_document_wf(seq![]);
    theorem_create_node_wf(d0, ml_text());
    let d1 = create_node(d0, ml_text()).0;
    theorem_create_node_wf(d1, ml_text());
}

/// Appending node 1 to the document is a valid call.
pub proof fn ml_doc_child_wf()
    ensures
        insert_requires(ml_doc3(), 1, 0, None),
        wf(ml_doc_child()),
        ml_doc_child().nodes[1].parent == Some(0usize),
{
    ml_doc3_wf();
    assert(ml_doc3().nodes[1].kind == ml_text()) by (compute_only);
    assert(ml_doc3().nodes[0].kind is Document) by (compute_only);
    assert(!is_inclusive_ancestor(ml_doc3(), 1, 0)) by (compute_only);
    theorem_append_wf(ml_doc3(), 0, 1);
}

/// `theorem_append_wf` on [`ml_doc3`]: the appended node's parent is the
/// document.
pub proof fn ml_append_sets_parent()
    ensures
        append(ml_doc3(), 0, 1).nodes[1].parent == Some(0usize),
{
    ml_doc_child_wf();
    theorem_append_wf(ml_doc3(), 0, 1);
}

/// `theorem_insert_before_wf` on [`ml_doc_child`]: node 2 inserted before
/// node 1 is the document's first child.
pub proof fn ml_insert_before_index()
    ensures
        insert_before(ml_doc_child(), 0, 2, 1).nodes[0].children[0] == 2usize,
{
    ml_doc_child_wf();
    assert(ml_doc_child().nodes[2].kind == ml_text()) by (compute_only);
    assert(ml_doc_child().nodes[0].kind is Document) by (compute_only);
    assert(ml_doc_child().nodes.len() == 3) by (compute_only);
    assert(!is_inclusive_ancestor(ml_doc_child(), 2, 0)) by (compute_only);
    assert(index_of(children(adopt(ml_doc_child(), 2), 0), 1) == 0) by (compute_only);
    theorem_insert_before_wf(ml_doc_child(), 0, 2, 1);
}

/// `theorem_remove_wf` on [`ml_doc_child`]: removing the document's only
/// child leaves it with none.
pub proof fn ml_remove_detaches()
    ensures
        remove(ml_doc_child(), 1).nodes[0].children.len() == 0,
{
    ml_doc_child_wf();
    assert(ml_doc_child().nodes[0].children.len() == 1) by (compute_only);
    assert(ml_doc_child().nodes.len() == 3) by (compute_only);
    theorem_remove_wf(ml_doc_child(), 1);
}

/// `theorem_reparent_children_wf` on [`ml_doc_reparent`]: moving the
/// document's children to element 3 keeps their order.
pub proof fn ml_reparent_keeps_order()
    ensures
        reparent_children(ml_doc_reparent(), 0, 3).nodes[3].children[0] == 1usize,
{
    ml_doc3_wf();
    theorem_create_node_wf(ml_doc3(), ml_element());
    assert(ml_doc4().nodes[1].kind == ml_text()) by (compute_only);
    assert(ml_doc4().nodes[2].kind == ml_text()) by (compute_only);
    assert(ml_doc4().nodes[0].kind is Document) by (compute_only);
    assert(ml_doc4().nodes.len() == 4) by (compute_only);
    assert(!is_inclusive_ancestor(ml_doc4(), 1, 0)) by (compute_only);
    theorem_append_wf(ml_doc4(), 0, 1);
    assert(ml_doc5().nodes[2].kind == ml_text()) by (compute_only);
    assert(ml_doc5().nodes[0].kind is Document) by (compute_only);
    assert(ml_doc5().nodes.len() == 4) by (compute_only);
    assert(!is_inclusive_ancestor(ml_doc5(), 2, 0)) by (compute_only);
    theorem_append_wf(ml_doc5(), 0, 2);
    assert(ml_doc_reparent().nodes.len() == 4) by (compute_only);
    assert(ml_doc_reparent().nodes[0].kind is Document) by (compute_only);
    assert(ml_doc_reparent().nodes[3].kind is Element) by (compute_only);
    assert(!is_inclusive_ancestor(ml_doc_reparent(), 0, 3)) by (compute_only);
    assert(children(ml_doc_reparent(), 3) + children(ml_doc_reparent(), 0) == seq![1usize, 2usize]) by (compute_only);
    theorem_reparent_children_wf(ml_doc_reparent(), 0, 3);
}

/// `lemma_limit_exact` on a new document: it may grow to exactly
/// 4,000,000 nodes.
pub proof fn ml_limit()
    ensures
        can_create(new_document(seq![]), 3_999_999),
{
    lemma_limit_exact(new_document(seq![]), 3_999_999);
}

} // verus!
