//! Concrete instances of `theorem_deep_copy_kind_fields`, the kill
//! certificates of the mutations of `deep_copy_kind` in `mutations.json`
//! (`xtask/src/mutate.rs`). Each lemma says that one concrete, wrong copy is
//! not a copy ([`deep_copy_kind`] is false for it): true of the real spec
//! by the theorem, so a mutant that makes [`deep_copy_kind`] accept it (the
//! certificate's witness) contradicts the theorem.
//!
//! The arenas: [`dm_doc`] is a document (0), an element (1) and a text node
//! (2), and [`ol_template`] a document, a template element (1) and its
//! contents, the fragment (2). A copy is the next node, 3.

#[cfg(verus_only)]
use super::deep_clone_lemmas::*;
#[cfg(verus_only)]
use super::mutation_lemmas::*;
#[cfg(verus_only)]
use super::ops_mutation_lemmas::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A document, an element (1) and a text node (2).
pub open spec fn dm_doc() -> Document {
    create_node(create_node(new_document(seq![]), ml_element()).0, ml_text()).0
}

/// An element kind with the given name, attributes, form owner and
/// template contents, in the HTML namespace.
pub open spec fn dm_el(local_name: Seq<u32>, attributes: Seq<Attr>, form_owner: Option<NodeId>, template_contents: Option<NodeId>) -> NodeKind {
    NodeKind::Element { namespace: Some(Namespace::Html), prefix: None, local_name, attributes, template_contents, form_owner }
}

/// `doc` with one more node, of kind `k`: the candidate copy.
pub open spec fn dm_out(doc: Document, k: NodeKind) -> Document {
    create_node(doc, k).0
}

/// An attribute.
pub open spec fn dm_attr() -> Attr {
    Attr { namespace: None, prefix: None, local_name: seq![], value: seq![] }
}

/// The witnesses below are evaluated by `compute_only`: it does evaluate
/// [`deep_copy_kind`] (sequence equalities and all) on a correct copy.
pub proof fn dm_sanity()
    ensures
        deep_copy_kind(dm_doc(), dm_out(dm_doc(), dm_el(seq![], seq![], None, None)), seq![1usize], 0),
{
    assert(deep_copy_kind(dm_doc(), dm_out(dm_doc(), dm_el(seq![], seq![], None, None)), seq![1usize], 0)) by (compute_only);
}

/// A copy with a form owner is not a copy.
pub proof fn dm_form_owner()
    ensures
        !deep_copy_kind(dm_doc(), dm_out(dm_doc(), dm_el(seq![], seq![], Some(0), None)), seq![1usize], 0),
{
    let out = dm_out(dm_doc(), dm_el(seq![], seq![], Some(0), None));
    if deep_copy_kind(dm_doc(), out, seq![1usize], 0) {
        theorem_deep_copy_kind_fields(dm_doc(), out, seq![1usize], 0);
        assert(out.nodes[3].kind->Element_form_owner is None);
        assert(false);
    }
}

/// A copy with other attributes is not a copy.
pub proof fn dm_attributes()
    ensures
        !deep_copy_kind(dm_doc(), dm_out(dm_doc(), dm_el(seq![], seq![dm_attr()], None, None)), seq![1usize], 0),
{
    let out = dm_out(dm_doc(), dm_el(seq![], seq![dm_attr()], None, None));
    if deep_copy_kind(dm_doc(), out, seq![1usize], 0) {
        theorem_deep_copy_kind_fields(dm_doc(), out, seq![1usize], 0);
        assert(out.nodes[3].kind->Element_attributes.len() == 1);
        assert(false);
    }
}

/// A copy with another local name is not a copy.
pub proof fn dm_local_name()
    ensures
        !deep_copy_kind(dm_doc(), dm_out(dm_doc(), dm_el(seq![1u32], seq![], None, None)), seq![1usize], 0),
{
    let out = dm_out(dm_doc(), dm_el(seq![1u32], seq![], None, None));
    if deep_copy_kind(dm_doc(), out, seq![1usize], 0) {
        theorem_deep_copy_kind_fields(dm_doc(), out, seq![1usize], 0);
        assert(out.nodes[3].kind->Element_local_name.len() == 1);
        assert(false);
    }
}

/// A copy in another namespace is not a copy.
pub proof fn dm_namespace()
    ensures
        !deep_copy_kind(
            dm_doc(),
            dm_out(dm_doc(), NodeKind::Element { namespace: Some(Namespace::Svg), prefix: None, local_name: seq![], attributes: seq![], template_contents: None, form_owner: None }),
            seq![1usize],
            0,
        ),
{
    let out = dm_out(
        dm_doc(),
        NodeKind::Element { namespace: Some(Namespace::Svg), prefix: None, local_name: seq![], attributes: seq![], template_contents: None, form_owner: None },
    );
    if deep_copy_kind(dm_doc(), out, seq![1usize], 0) {
        theorem_deep_copy_kind_fields(dm_doc(), out, seq![1usize], 0);
        assert(out.nodes[3].kind->Element_namespace == Some(Namespace::Svg));
        assert(false);
    }
}

/// A copy with a prefix the source lacks is not a copy.
pub proof fn dm_prefix()
    ensures
        !deep_copy_kind(
            dm_doc(),
            dm_out(dm_doc(), NodeKind::Element { namespace: Some(Namespace::Html), prefix: Some(seq![]), local_name: seq![], attributes: seq![], template_contents: None, form_owner: None }),
            seq![1usize],
            0,
        ),
{
    let out = dm_out(
        dm_doc(),
        NodeKind::Element { namespace: Some(Namespace::Html), prefix: Some(seq![]), local_name: seq![], attributes: seq![], template_contents: None, form_owner: None },
    );
    if deep_copy_kind(dm_doc(), out, seq![1usize], 0) {
        theorem_deep_copy_kind_fields(dm_doc(), out, seq![1usize], 0);
        assert(out.nodes[3].kind->Element_prefix is Some);
        assert(false);
    }
}

/// A copy of a text node that is a comment is not a copy.
pub proof fn dm_other_kind()
    ensures
        !deep_copy_kind(dm_doc(), dm_out(dm_doc(), NodeKind::Comment { data: seq![] }), seq![2usize], 0),
{
    let out = dm_out(dm_doc(), NodeKind::Comment { data: seq![] });
    if deep_copy_kind(dm_doc(), out, seq![2usize], 0) {
        theorem_deep_copy_kind_fields(dm_doc(), out, seq![2usize], 0);
        assert(out.nodes[3].kind is Comment);
        assert(false);
    }
}

/// A copy of a plain element that has template contents is not a copy.
pub proof fn dm_gains_contents()
    ensures
        !deep_copy_kind(dm_doc(), dm_out(dm_doc(), dm_el(seq![], seq![], None, Some(0))), seq![1usize], 0),
{
    let out = dm_out(dm_doc(), dm_el(seq![], seq![], None, Some(0)));
    if deep_copy_kind(dm_doc(), out, seq![1usize], 0) {
        theorem_deep_copy_kind_fields(dm_doc(), out, seq![1usize], 0);
        assert(out.nodes[3].kind->Element_template_contents is Some);
        assert(false);
    }
}

/// A copy of a template whose contents copies the wrong node is not a copy
/// (the source of node 4, the contents, is 1, not the source's contents 2).
pub proof fn dm_wrong_contents()
    ensures
        !deep_copy_kind(
            ol_template(),
            dm_out(dm_out(ol_template(), dm_el(seq![], seq![], None, Some(4))), NodeKind::DocumentFragment { host: Some(3) }),
            seq![1usize, 1usize],
            0,
        ),
{
    let out = dm_out(dm_out(ol_template(), dm_el(seq![], seq![], None, Some(4))), NodeKind::DocumentFragment { host: Some(3) });
    if deep_copy_kind(ol_template(), out, seq![1usize, 1usize], 0) {
        theorem_deep_copy_kind_fields(ol_template(), out, seq![1usize, 1usize], 0);
        assert(ol_template().nodes[1].kind->Element_template_contents == Some(2usize));
        assert(out.nodes[3].kind->Element_template_contents == Some(4usize));
        assert(false);
    }
}

/// A copy of a fragment, the root, that has a host is not a copy.
pub proof fn dm_root_fragment_host()
    ensures
        !deep_copy_kind(ol_template(), dm_out(ol_template(), NodeKind::DocumentFragment { host: Some(1) }), seq![2usize], 0),
{
    let out = dm_out(ol_template(), NodeKind::DocumentFragment { host: Some(1) });
    if deep_copy_kind(ol_template(), out, seq![2usize], 0) {
        theorem_deep_copy_kind_fields(ol_template(), out, seq![2usize], 0);
        assert(out.nodes[3].kind->DocumentFragment_host == Some(1usize));
        assert(false);
    }
}

/// The root's copy with a parent is not a copy.
pub proof fn dm_root_parent()
    ensures
        !deep_copy_kind(
            dm_doc(),
            Document { nodes: dm_out(dm_doc(), dm_el(seq![], seq![], None, None)).nodes.update(3, Node { parent: Some(0usize), ..dm_out(dm_doc(), dm_el(seq![], seq![], None, None)).nodes[3] }) },
            seq![1usize],
            0,
        ),
{
    let o = dm_out(dm_doc(), dm_el(seq![], seq![], None, None));
    let out = Document { nodes: o.nodes.update(3, Node { parent: Some(0usize), ..o.nodes[3] }) };
    if deep_copy_kind(dm_doc(), out, seq![1usize], 0) {
        theorem_deep_copy_kind_fields(dm_doc(), out, seq![1usize], 0);
        assert(out.nodes[3].parent is Some);
        assert(false);
    }
}

/// A copy with a wrapper is not a copy.
pub proof fn dm_wrapper()
    ensures
        !deep_copy_kind(
            dm_doc(),
            Document { nodes: dm_out(dm_doc(), dm_el(seq![], seq![], None, None)).nodes.update(3, Node { wrapper: Some(0nat), ..dm_out(dm_doc(), dm_el(seq![], seq![], None, None)).nodes[3] }) },
            seq![1usize],
            0,
        ),
{
    let o = dm_out(dm_doc(), dm_el(seq![], seq![], None, None));
    let out = Document { nodes: o.nodes.update(3, Node { wrapper: Some(0nat), ..o.nodes[3] }) };
    if deep_copy_kind(dm_doc(), out, seq![1usize], 0) {
        theorem_deep_copy_kind_fields(dm_doc(), out, seq![1usize], 0);
        assert(out.nodes[3].wrapper is Some);
        assert(false);
    }
}

} // verus!
