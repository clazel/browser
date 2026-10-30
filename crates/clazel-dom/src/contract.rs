//! Contracts the executable arena (`exec`) must be proven to meet. Each exec
//! function's `requires` and `ensures` are exactly these predicates, stated
//! over the spec's [`Document`] (the exec arena's view), so reviewing these
//! and [`super::spec`] is enough to know what the implementation guarantees.
//!
//! Every mutation keeps [`wf`]; that is proven once about the spec
//! (`lemmas`: `theorem_insert_wf`, …), so the exec functions need only be
//! equal to the spec functions.

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

/// Contract for the readers `Arena::parent(n)`, `Arena::previous_sibling(n)`
/// and `Arena::last_child(n)`, under `wf(doc)` and `valid(doc, n)`.
pub open spec fn readers_ensures(doc: Document, n: NodeId, parent_out: Option<NodeId>, prev_out: Option<NodeId>, last_out: Option<NodeId>) -> bool {
    &&& parent_out == parent(doc, n)
    &&& prev_out == previous_sibling(doc, n)
    &&& last_out == last_child(doc, n)
}

} // verus!
