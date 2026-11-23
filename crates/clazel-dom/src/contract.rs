//! Contracts the executable arena (`exec`) must be proven to meet. Each
//! mutating exec function's `requires` and `ensures` are exactly the
//! predicates here, stated over the spec's [`Document`] (the exec arena's
//! view), so reviewing these and [`super::spec`] is enough to know what the
//! mutators guarantee. The readers (`kind`, `parent`, `children`, `wrapper`,
//! `last_child`, `has_child`, `previous_sibling`, `is_inclusive_ancestor`)
//! have no predicate here: each states in its own `ensures`, in
//! `exec.rs`, that it returns the spec reader of the same name.
//!
//! Every mutation keeps [`wf`]; that is proven once about the spec
//! (`lemmas`: `theorem_insert_wf`, …), so the exec functions need only be
//! equal to the spec functions.
//!
//! Every mutation also keeps `host_acyclic`, the one thing [`wf`] does not
//! say (no cycle through a template's host): see `host_acyclic_contract` and
//! `host_acyclic_lemmas`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `Arena::new(url)`: the new document.
pub open spec fn new_ensures(url: Seq<u32>, out: Document) -> bool {
    out == new_document(url)
}

/// Precondition of `Arena::create(kind)`: a well-formed arena and a kind it
/// may hold.
pub open spec fn create_requires(doc: Document, k: NodeKind) -> bool {
    wf(doc) && creatable(doc, k)
}

/// Contract for `Arena::create(kind) -> Option<usize>`: refused (`None`,
/// nothing changed) exactly at the node limit, and otherwise
/// [`create_node`].
pub open spec fn create_ensures(doc: Document, k: NodeKind, out: Document, id: Option<NodeId>) -> bool {
    if can_create(doc, 1) {
        id == Some(create_node(doc, k).1) && out == create_node(doc, k).0
    } else {
        id is None && out == doc
    }
}

/// Precondition of `Arena::create_template_contents(t)`: `t` is an element
/// without template contents.
pub open spec fn create_template_contents_requires(doc: Document, t: NodeId) -> bool {
    &&& wf(doc)
    &&& valid(doc, t)
    &&& doc.nodes[t as int].kind is Element
    &&& doc.nodes[t as int].kind->Element_template_contents is None
}

/// Contract for `Arena::create_template_contents(t) -> Option<usize>`:
/// refused at the node limit, and otherwise [`create_template_contents`].
pub open spec fn create_template_contents_ensures(doc: Document, t: NodeId, out: Document, id: Option<NodeId>) -> bool {
    if can_create(doc, 1) {
        id == Some(create_template_contents(doc, t).1) && out == create_template_contents(doc, t).0
    } else {
        id is None && out == doc
    }
}

/// Contract for `Arena::append(parent, node)`, under
/// `insert_requires(doc, node, parent, None)`.
pub open spec fn append_ensures(doc: Document, parent: NodeId, node: NodeId, out: Document) -> bool {
    out == append(doc, parent, node)
}

/// Contract for `Arena::insert_before(parent, node, child)`, under
/// `insert_requires(doc, node, parent, Some(child))`.
pub open spec fn insert_before_ensures(doc: Document, parent: NodeId, node: NodeId, child: NodeId, out: Document) -> bool {
    out == insert_before(doc, parent, node, child)
}

/// Precondition of `Arena::remove(node)`: DOM's assertion, "parent is
/// non-null".
pub open spec fn remove_requires(doc: Document, node: NodeId) -> bool {
    wf(doc) && valid(doc, node) && doc.nodes[node as int].parent is Some
}

/// Contract for `Arena::remove(node)`.
pub open spec fn remove_ensures(doc: Document, node: NodeId, out: Document) -> bool {
    out == remove(doc, node)
}

/// Contract for `Arena::reparent_children(from, to)`, under
/// [`reparent_children_requires`].
pub open spec fn reparent_children_ensures(doc: Document, from: NodeId, to: NodeId, out: Document) -> bool {
    out == reparent_children(doc, from, to)
}

/// Precondition of `Arena::append_data(n, data)`: `n` is a `Text` node.
pub open spec fn append_data_requires(doc: Document, n: NodeId) -> bool {
    wf(doc) && valid(doc, n) && doc.nodes[n as int].kind is Text
}

/// Contract for `Arena::append_data(n, data)`.
pub open spec fn append_data_ensures(doc: Document, n: NodeId, data: Seq<u32>, out: Document) -> bool {
    out == append_data(doc, n, data)
}

/// Precondition of `Arena::set_data(n, data)`: `n` is a `Text`, `Comment`
/// or `ProcessingInstruction` node (DOM's `CharacterData`).
pub open spec fn set_data_requires(doc: Document, n: NodeId) -> bool {
    &&& wf(doc)
    &&& valid(doc, n)
    &&& (doc.nodes[n as int].kind is Text || doc.nodes[n as int].kind is Comment
        || doc.nodes[n as int].kind is ProcessingInstruction)
}

/// Contract for `Arena::set_data(n, data)`.
pub open spec fn set_data_ensures(doc: Document, n: NodeId, data: Seq<u32>, out: Document) -> bool {
    out == set_data(doc, n, data)
}

/// Precondition of `Arena::set_wrapper(n, w)`: `n` is a node of the arena.
pub open spec fn set_wrapper_requires(doc: Document, n: NodeId) -> bool {
    wf(doc) && valid(doc, n)
}

/// Contract for `Arena::set_wrapper(n, w)`.
pub open spec fn set_wrapper_ensures(doc: Document, n: NodeId, w: Option<nat>, out: Document) -> bool {
    out == set_wrapper(doc, n, w)
}

/// Precondition of `Arena::append_attribute(e, attr)`: `e` is an element.
pub open spec fn append_attribute_requires(doc: Document, e: NodeId) -> bool {
    wf(doc) && valid(doc, e) && doc.nodes[e as int].kind is Element
}

/// Contract for `Arena::append_attribute(e, attr)`.
pub open spec fn append_attribute_ensures(doc: Document, e: NodeId, attr: Attr, out: Document) -> bool {
    out == append_attribute(doc, e, attr)
}

/// Contract for `Arena::set_mode(mode)`, under `wf(doc)`.
pub open spec fn set_mode_ensures(doc: Document, mode: DocumentMode, out: Document) -> bool {
    out == set_mode(doc, mode)
}

// ---------------------------------------------------------------------
// Phase 7 item 7.13 (see `spec.rs`, "the mutation algorithms scripts
// call"). Their section and step numbers carry the mark † there.

/// Precondition of `Arena::ensure_pre_insertion_validity(node, parent,
/// child)` and `Arena::pre_insert(node, parent, child)`: ids of a
/// well-formed arena. Any node, parent and child are allowed: the
/// algorithm's job is to refuse the invalid ones.
pub open spec fn pre_insert_requires(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> bool {
    ids_requires(doc, node, parent, child)
}

/// Contract for `Arena::ensure_pre_insertion_validity(node, parent,
/// child) -> Option<DomError>`: the error DOM §4.2.3† throws, or none.
pub open spec fn ensure_pre_insertion_validity_ensures(
    doc: Document,
    node: NodeId,
    parent: NodeId,
    child: Option<NodeId>,
    err: Option<DomError>,
) -> bool {
    err == pre_insert_error(doc, node, parent, child)
}

/// Contract for `Arena::pre_insert(node, parent, child) ->
/// Option<DomError>`: the error is [`pre_insert_error`], and the arena is
/// [`pre_insert`] (unchanged if there is an error).
pub open spec fn pre_insert_ensures(
    doc: Document,
    node: NodeId,
    parent: NodeId,
    child: Option<NodeId>,
    out: Document,
    err: Option<DomError>,
) -> bool {
    &&& err == pre_insert_error(doc, node, parent, child)
    &&& out == pre_insert(doc, node, parent, child)
}

/// Precondition of `Arena::replace(child, node, parent)`: ids of a
/// well-formed arena.
pub open spec fn replace_requires(doc: Document, child: NodeId, node: NodeId, parent: NodeId) -> bool {
    &&& ids_requires(doc, node, parent, Some(child))
}

/// Contract for `Arena::replace(child, node, parent) -> Option<DomError>`.
pub open spec fn replace_ensures(
    doc: Document,
    child: NodeId,
    node: NodeId,
    parent: NodeId,
    out: Document,
    err: Option<DomError>,
) -> bool {
    &&& err == replace_error(doc, child, node, parent)
    &&& out == replace(doc, child, node, parent)
}

/// Contract for `Arena::replace_all(node, parent)`, under
/// [`replace_all_requires`].
pub open spec fn replace_all_ensures(doc: Document, node: Option<NodeId>, parent: NodeId, out: Document) -> bool {
    out == replace_all(doc, node, parent)
}

/// Precondition of `Arena::adopt(node)`: a node of a well-formed arena.
pub open spec fn adopt_requires(doc: Document, node: NodeId) -> bool {
    wf(doc) && valid(doc, node)
}

/// Contract for `Arena::adopt(node)`.
pub open spec fn adopt_ensures(doc: Document, node: NodeId, out: Document) -> bool {
    out == adopt(doc, node)
}

/// Contract for `Arena::clone_node(node) -> Option<usize>`, under
/// [`clone_requires`]: refused (`None`, nothing changed) unless the arena
/// can hold the copy (and a template's contents), and otherwise
/// [`clone_node`].
pub open spec fn clone_node_ensures(doc: Document, node: NodeId, out: Document, id: Option<NodeId>) -> bool {
    if can_create(doc, clone_count(doc, node)) {
        id == Some(clone_node(doc, node).1) && out == clone_node(doc, node).0
    } else {
        id is None && out == doc
    }
}

/// Precondition of `Arena::clone_deep(node)`: [`clone_requires`], and an
/// arena with no cycle through template hosts ([`host_acyclic`]; [`wf`]
/// does not give it, and the unfolding of such a cycle is infinite).
pub open spec fn clone_deep_requires(doc: Document, node: NodeId) -> bool {
    &&& clone_requires(doc, node)
    &&& host_acyclic(doc)
}

/// The arena `out` grew by exactly [`subtree_size`] nodes: the copy is the
/// whole host-including subtree of `node`, and nothing else.
pub open spec fn clone_deep_grew(doc: Document, node: NodeId, out: Document) -> bool {
    out.nodes.len() == doc.nodes.len() + subtree_size(doc, node)
}

/// A refusal of `Arena::clone_deep(node)`: the arena is exactly as it was,
/// and it could not have held the copy ([`subtree_size`] more nodes).
pub open spec fn clone_deep_refused(doc: Document, node: NodeId, out: Document) -> bool {
    &&& out == doc
    &&& !can_create(doc, subtree_size(doc, node))
}

/// Contract for `Arena::clone_deep(node) -> Option<usize>`, under
/// [`clone_deep_requires`]: refused (`None`) only if the copy does not fit
/// ([`clone_deep_refused`]), and then the arena is exactly as it was;
/// otherwise the arena is well formed, holds [`deep_clone`] of `node`, whose
/// copy is the id returned, and grew by [`subtree_size`] nodes.
pub open spec fn clone_deep_ensures(doc: Document, node: NodeId, out: Document, id: Option<NodeId>) -> bool {
    match id {
        Some(copy) => wf(out) && deep_clone(doc, node, out, copy) && clone_deep_grew(doc, node, out),
        None => clone_deep_refused(doc, node, out),
    }
}

/// Contract for `Arena::change_attribute(e, i, value)`, under
/// [`attribute_requires`].
pub open spec fn change_attribute_ensures(doc: Document, e: NodeId, i: nat, value: Seq<u32>, out: Document) -> bool {
    out == change_attribute(doc, e, i, value)
}

/// Contract for `Arena::remove_attribute(e, i)`, under
/// [`attribute_requires`].
pub open spec fn remove_attribute_ensures(doc: Document, e: NodeId, i: nat, out: Document) -> bool {
    out == remove_attribute(doc, e, i)
}

/// Contract for `Arena::replace_attribute(e, i, new_attr)`, under
/// [`attribute_requires`].
pub open spec fn replace_attribute_ensures(doc: Document, e: NodeId, i: nat, new_attr: Attr, out: Document) -> bool {
    out == replace_attribute(doc, e, i, new_attr)
}

} // verus!
