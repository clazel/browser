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

#[cfg(verus_only)]
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

// ---------------------------------------------------------------------
// Certificates for the mutations that need the strengthened theorems.

/// [`ml_doc_reparent`] is well formed.
pub proof fn ml_doc_reparent_wf()
    ensures
        wf(ml_doc_reparent()),
        ml_doc_reparent().nodes.len() == 4,
        ml_doc_reparent().nodes[2].parent == Some(0usize),
{
    ml_doc3_wf();
    theorem_create_node_wf(ml_doc3(), ml_element());
    assert(ml_doc4().nodes[1].kind == ml_text()) by (compute_only);
    assert(ml_doc4().nodes[0].kind is Document) by (compute_only);
    assert(ml_doc4().nodes.len() == 4) by (compute_only);
    assert(!is_inclusive_ancestor(ml_doc4(), 1, 0)) by (compute_only);
    theorem_append_wf(ml_doc4(), 0, 1);
    assert(ml_doc5().nodes[2].kind == ml_text()) by (compute_only);
    assert(ml_doc5().nodes[0].kind is Document) by (compute_only);
    assert(ml_doc5().nodes.len() == 4) by (compute_only);
    assert(!is_inclusive_ancestor(ml_doc5(), 2, 0)) by (compute_only);
    theorem_append_wf(ml_doc5(), 0, 2);
}

/// A document with a parentless `Text` node 1 whose data is `[1]`.
pub open spec fn ml_doc_data() -> Document {
    create_node(new_document(seq![]), NodeKind::Text { data: seq![1u32] }).0
}

/// A document whose URL is `[1]` and base URL `[2]`.
pub open spec fn ml_doc_urls() -> Document {
    set_kind(new_document(seq![]), 0, NodeKind::Document { mode: DocumentMode::NoQuirks, url: seq![1u32], base_url: seq![2u32] })
}

/// An HTML element (node 3 of [`ml_doc_form`]) whose form owner is node 0.
pub open spec fn ml_element_form() -> NodeKind {
    NodeKind::Element {
        namespace: Some(Namespace::Html),
        prefix: None,
        local_name: seq![],
        attributes: seq![],
        template_contents: None,
        form_owner: Some(0usize),
    }
}

/// [`ml_doc3`] and the element [`ml_element_form`] as node 3.
pub open spec fn ml_doc_form() -> Document {
    create_node(ml_doc3(), ml_element_form()).0
}

/// [`ml_doc4`] with template contents for its element 3 (the fragment is
/// node 4).
pub open spec fn ml_doc_template() -> Document {
    create_template_contents(ml_doc4(), 3).0
}

/// An attribute whose value is `[v]`.
pub open spec fn ml_attr(v: u32) -> Attr {
    Attr { namespace: None, prefix: None, local_name: seq![], value: seq![v] }
}

/// `theorem_set_mode_frame` on [`ml_doc_urls`]: the base URL stays `[2]`.
pub proof fn ml_set_mode_keeps_urls()
    ensures
        set_mode(ml_doc_urls(), DocumentMode::Quirks).nodes[0].kind->Document_base_url[0] == 2u32,
{
    let d0 = new_document(seq![]);
    theorem_new_document_wf(seq![]);
    let paths = lemma_wf_witness(d0);
    let k = NodeKind::Document { mode: DocumentMode::NoQuirks, url: seq![1u32], base_url: seq![2u32] };
    assert(same_shape(d0.nodes[0].kind, k));
    lemma_set_kind_wf(d0, paths, 0, k);
    assert(ml_doc_urls().nodes[0].kind == k);
    theorem_set_mode_wf(ml_doc_urls(), DocumentMode::Quirks);
    theorem_set_mode_frame(ml_doc_urls(), DocumentMode::Quirks);
}

/// `theorem_append_attribute_wf` twice on an element: the first attribute
/// stays first.
pub proof fn ml_append_attribute_order()
    ensures
        append_attribute(append_attribute(ml_doc4(), 3, ml_attr(1)), 3, ml_attr(2)).nodes[3].kind->Element_attributes[0].value[0] == 1u32,
{
    ml_doc3_wf();
    theorem_create_node_wf(ml_doc3(), ml_element());
    assert(ml_doc4().nodes[3].kind == ml_element()) by (compute_only);
    assert(ml_doc4().nodes.len() == 4) by (compute_only);
    let d1 = append_attribute(ml_doc4(), 3, ml_attr(1));
    theorem_append_attribute_wf(ml_doc4(), 3, ml_attr(1));
    theorem_append_attribute_wf(d1, 3, ml_attr(2));
}

/// `theorem_create_template_contents_frame` on [`ml_doc_form`]: the element's
/// form owner stays set.
pub proof fn ml_ctc_keeps_form_owner()
    ensures
        create_template_contents(ml_doc_form(), 3).0.nodes[3].kind->Element_form_owner is Some,
{
    ml_doc3_wf();
    assert(creatable(ml_doc3(), ml_element_form())) by (compute_only);
    assert(can_create(ml_doc3(), 1)) by (compute_only);
    theorem_create_node_wf(ml_doc3(), ml_element_form());
    assert(ml_doc_form().nodes[3].kind == ml_element_form()) by (compute_only);
    assert(ml_doc_form().nodes.len() == 4) by (compute_only);
    assert(can_create(ml_doc_form(), 1)) by (compute_only);
    theorem_create_template_contents_wf(ml_doc_form(), 3);
    theorem_create_template_contents_frame(ml_doc_form(), 3);
}

/// `theorem_remove_keeps_order` on the document with children 1, 2 and 3: removing
/// 3 leaves 1 first.
pub proof fn ml_remove_keeps_order()
    ensures
        remove(append(ml_doc_reparent(), 0, 3), 3).nodes[0].children[0] == 1usize,
{
    ml_doc_reparent_wf();
    assert(ml_doc_reparent().nodes[0].kind is Document) by (compute_only);
    assert(ml_doc_reparent().nodes[3].kind is Element) by (compute_only);
    assert(ml_doc_reparent().nodes[3].parent is None) by (compute_only);
    assert(!is_inclusive_ancestor(ml_doc_reparent(), 3, 0)) by (compute_only);
    assert(ml_doc_reparent().nodes[0].children.len() == 2) by (compute_only);
    assert(ml_doc_reparent().nodes[0].children[0] == 1usize) by (compute_only);
    theorem_append_wf(ml_doc_reparent(), 0, 3);
    theorem_insert_wf(ml_doc_reparent(), 3, 0, None);
    let d = append(ml_doc_reparent(), 0, 3);
    let kids = d.nodes[0].children;
    assert(adopt(ml_doc_reparent(), 3) == ml_doc_reparent());
    assert(kids.len() == 3);
    assert(kids[0] == 1usize);
    assert(kids[2] == 3usize);
    assert(kids.no_duplicates());
    lemma_index_of_unique(kids, 2);
    theorem_remove_wf(d, 3);
    theorem_remove_keeps_order(d, 3);
}

/// `theorem_append_wf` on [`ml_doc_child`], moving its child 1 to the end
/// of its own parent: 1 is listed once.
pub proof fn ml_append_moves_once()
    ensures
        append(ml_doc_child(), 0, 1).nodes[0].children.len() == 1,
{
    ml_doc_child_wf();
    assert(ml_doc_child().nodes[1].kind == ml_text()) by (compute_only);
    assert(ml_doc_child().nodes[0].kind is Document) by (compute_only);
    assert(ml_doc_child().nodes.len() == 3) by (compute_only);
    assert(!is_inclusive_ancestor(ml_doc_child(), 1, 0)) by (compute_only);
    assert(ml_doc_child().nodes[0].children.len() == 1) by (compute_only);
    theorem_remove_wf(ml_doc_child(), 1);
    theorem_append_wf(ml_doc_child(), 0, 1);
}

/// `theorem_insert_before_wf` on [`ml_doc_reparent`]: node 3 inserted
/// before node 2 (children 1, 3, 2) is node 2's previous sibling.
pub proof fn ml_previous_sibling()
    ensures
        previous_sibling(insert_before(ml_doc_reparent(), 0, 3, 2), 2) == Some(3usize),
{
    ml_doc_reparent_wf();
    assert(ml_doc_reparent().nodes[0].kind is Document) by (compute_only);
    assert(ml_doc_reparent().nodes[3].kind is Element) by (compute_only);
    assert(!is_inclusive_ancestor(ml_doc_reparent(), 3, 0)) by (compute_only);
    theorem_insert_before_wf(ml_doc_reparent(), 0, 3, 2);
}

/// `theorem_append_wf` on [`ml_doc_reparent`]: the last child after
/// appending 3 to the document is 3.
pub proof fn ml_last_child()
    ensures
        last_child(append(ml_doc_reparent(), 0, 3), 0) == Some(3usize),
{
    ml_doc_reparent_wf();
    assert(ml_doc_reparent().nodes[0].kind is Document) by (compute_only);
    assert(ml_doc_reparent().nodes[3].kind is Element) by (compute_only);
    assert(!is_inclusive_ancestor(ml_doc_reparent(), 3, 0)) by (compute_only);
    theorem_append_wf(ml_doc_reparent(), 0, 3);
}

/// `theorem_append_data_wf` on [`ml_doc_data`]: appending `[2]` to the data
/// `[1]` keeps 1 first.
pub proof fn ml_append_data_order()
    ensures
        append_data(ml_doc_data(), 1, seq![2u32]).nodes[1].kind->Text_data[0] == 1u32,
{
    let d0 = new_document(seq![]);
    theorem_new_document_wf(seq![]);
    assert(creatable(new_document(seq![]), NodeKind::Text { data: seq![1u32] })) by (compute_only);
    assert(can_create(new_document(seq![]), 1)) by (compute_only);
    theorem_create_node_wf(d0, NodeKind::Text { data: seq![1u32] });
    assert(ml_doc_data().nodes[1].kind == (NodeKind::Text { data: seq![1u32] })) by (compute_only);
    assert(ml_doc_data().nodes.len() == 2) by (compute_only);
    theorem_append_data_wf(ml_doc_data(), 1, seq![2u32]);
}

/// `theorem_append_wf` on [`ml_doc_template`]: appending text 1 to the
/// template contents (node 4) gives a well-formed arena, so a fragment
/// may have children.
pub proof fn ml_fragment_takes_children()
    ensures
        wf(append(ml_doc_template(), 4, 1)),
{
    ml_doc3_wf();
    theorem_create_node_wf(ml_doc3(), ml_element());
    assert(ml_doc4().nodes[3].kind == ml_element()) by (compute_only);
    assert(ml_doc4().nodes.len() == 4) by (compute_only);
    assert(can_create(ml_doc4(), 1)) by (compute_only);
    theorem_create_template_contents_wf(ml_doc4(), 3);
    assert(ml_doc_template().nodes.len() == 5);
    assert(ml_doc_template().nodes[4].kind is DocumentFragment) by (compute_only);
    assert(ml_doc_template().nodes[1].kind == ml_text()) by (compute_only);
    assert(!is_inclusive_ancestor(ml_doc_template(), 1, 4)) by (compute_only);
    theorem_append_wf(ml_doc_template(), 4, 1);
}

} // verus!
