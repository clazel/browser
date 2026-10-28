//! `parser_wf`, the invariant of every reachable parser state, which the
//! step's contract assumes and its theorems preserve (Phase 4 item 4.9:
//! `theorem_doc_wf`, `theorem_open_elements_in_doc`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `e` is an element of the arena whose namespace and local name are the
/// record's.
pub open spec fn elem_in_doc(doc: Document, e: Elem) -> bool {
    &&& dom::valid(doc, e.id)
    &&& doc.nodes[e.id as int].kind is Element
    &&& doc.nodes[e.id as int].kind->Element_namespace == Some(e.ns)
    &&& doc.nodes[e.id as int].kind->Element_local_name == e.name
}

/// An optional node of the arena.
pub open spec fn opt_valid(doc: Document, n: Option<NodeId>) -> bool {
    match n {
        None => true,
        Some(x) => dom::valid(doc, x),
    }
}

/// Every id the parse state holds names a node of the document: the stack
/// of open elements and the list of active formatting elements hold
/// elements of the arena (with their own namespace and name), and the
/// element pointers, the fragment context and the redirection map name
/// nodes of it.
pub open spec fn ids_in_doc(p: Parser) -> bool {
    &&& forall|i: int| 0 <= i < p.open.len() ==> elem_in_doc(p.doc, #[trigger] p.open[i])
    &&& forall|i: int|
        0 <= i < p.formatting.len() && (#[trigger] p.formatting[i]) is Entry ==> elem_in_doc(p.doc, p.formatting[i]->Entry_elem)
    &&& opt_valid(p.doc, p.head)
    &&& opt_valid(p.doc, p.form)
    &&& match p.context {
        None => true,
        Some(c) => elem_in_doc(p.doc, c),
    }
    &&& match p.redirect {
        None => true,
        Some((r, f)) => dom::valid(p.doc, r) && dom::valid(p.doc, f) && p.doc.nodes[f as int].kind is DocumentFragment,
    }
}

/// The invariant of every reachable parser state: the document is
/// well formed (`clazel_dom::spec::wf`) and every id of the parse state is a
/// node of it.
pub open spec fn parser_wf(p: Parser) -> bool {
    dom::wf(p.doc) && ids_in_doc(p)
}

} // verus!
