//! Contracts the executable form functions must be proven to meet. Each
//! exec function's `ensures` clause is exactly one of these predicates (and
//! its `requires`, where it has one), so reviewing these and
//! [`super::spec`] is enough to know what the implementation guarantees.
//!
//! The functions that read the DOM take a `clazel_dom` arena that is
//! well-formed ([`clazel_dom::spec::wf`]): the fuel of [`super::spec`]'s
//! walks never runs out in it, and every child, parent and form owner is a
//! node of the arena. Strings are code points as `u32`.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use clazel_dom::spec as dom;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `find_attr(&[ExecAttr], &[u8])`: the value of the first
/// attribute with a null namespace and the ASCII local name `name`.
pub open spec fn find_attr_ensures(list: Seq<Attr>, name: Seq<u8>, out: Option<Seq<u32>>) -> bool {
    out == find_attr(list, ascii(name))
}

/// Contract for `ci_eq(&[u32], &[u8])`: ASCII case-insensitive match with a
/// lowercase keyword.
pub open spec fn ci_eq_ensures(s: Seq<u32>, k: Seq<u8>, out: bool) -> bool {
    out == ci_eq(s, k)
}

/// Contract for `strip_newlines(&[u32])`.
pub open spec fn strip_newlines_ensures(s: Seq<u32>, out: Seq<u32>) -> bool {
    out == strip_newlines(s)
}

/// Contract for `strip_whitespace(&[u32])`.
pub open spec fn strip_whitespace_ensures(s: Seq<u32>, out: Seq<u32>) -> bool {
    out == strip_whitespace(s)
}

/// Contract for `normalize_newlines(&[u32])`.
pub open spec fn normalize_newlines_ensures(s: Seq<u32>, out: Seq<u32>) -> bool {
    out == normalize_newlines(s)
}

/// Contract for `wrap_hard(&[u32], usize)`: the wrapping transformation's
/// line breaking at `cols` characters.
pub open spec fn wrap_hard_ensures(s: Seq<u32>, cols: usize, out: Seq<u32>) -> bool {
    out == wrap_from(s, cols as nat, 0)
}

/// Contract for `decimal(u32)`.
pub open spec fn decimal_ensures(n: u32, out: Seq<u32>) -> bool {
    out == decimal(n as nat)
}

/// Contract for `character_width(Option<&[u32]>)`: the character width of
/// a `cols` attribute, cut off at `usize::MAX` (no line is longer).
pub open spec fn character_width_ensures(a: Option<Seq<u32>>, out: usize) -> bool {
    out as nat == if width_of(a) > usize::MAX as nat {
        usize::MAX as nat
    } else {
        width_of(a)
    }
}

/// Precondition of `tree_order(&Arena, usize)`.
pub open spec fn tree_order_requires(doc: Document, n: NodeId) -> bool {
    dom::wf(doc) && dom::valid(doc, n)
}

/// Contract for `tree_order(&Arena, usize)`: the tree order of the tree
/// below `n`.
pub open spec fn tree_order_ensures(doc: Document, n: NodeId, out: Seq<NodeId>) -> bool {
    out == tree_order(doc, n, doc.nodes.len())
}

/// Precondition of `root(&Arena, usize)`.
pub open spec fn root_requires(doc: Document, n: NodeId) -> bool {
    dom::wf(doc) && dom::valid(doc, n)
}

/// Contract for `root(&Arena, usize)`.
pub open spec fn root_ensures(doc: Document, n: NodeId, out: NodeId) -> bool {
    out == root(doc, n)
}

/// Precondition of `controls(&Arena, usize)`: `form` is a node of a
/// well-formed arena.
pub open spec fn controls_requires(doc: Document, form: NodeId) -> bool {
    dom::wf(doc) && dom::valid(doc, form)
}

/// Contract for `controls(&Arena, usize)`: the submittable elements whose
/// form owner is `form`, in tree order.
pub open spec fn controls_ensures(doc: Document, form: NodeId, out: Seq<NodeId>) -> bool {
    out == controls(doc, form)
}

/// Precondition of `field_entries(…)`: a well-formed arena, a field that is
/// a node, and a submitter that, if there is one, is a node.
pub open spec fn field_entries_requires(doc: Document, submitter: Option<NodeId>, field: NodeId) -> bool {
    &&& dom::wf(doc)
    &&& dom::valid(doc, field)
    &&& is_submittable(doc, field)
    &&& submitter is Some ==> dom::valid(doc, submitter->Some_0)
}

/// Contract for `field_entries(…)`: step 5's body for one field.
pub open spec fn field_entries_ensures(
    doc: Document,
    st: FormState,
    submitter: Option<NodeId>,
    encoding: Seq<u32>,
    field: NodeId,
    out: Seq<Entry>,
) -> bool {
    out == field_entries(doc, st, submitter, encoding, field)
}

/// Precondition of `construct_entry_list(…)`: a well-formed arena, a node
/// as the form, and a submitter that, if there is one, is a node.
pub open spec fn construct_entry_list_requires(doc: Document, form: NodeId, submitter: Option<NodeId>) -> bool {
    &&& dom::wf(doc)
    &&& dom::valid(doc, form)
    &&& submitter is Some ==> dom::valid(doc, submitter->Some_0)
}

/// Contract for `construct_entry_list(…)`: HTML "construct the entry list".
pub open spec fn construct_entry_list_ensures(
    doc: Document,
    st: FormState,
    form: NodeId,
    submitter: Option<NodeId>,
    encoding: Seq<u32>,
    constructing: bool,
    out: Option<Seq<Entry>>,
) -> bool {
    out == construct_entry_list(doc, st, form, submitter, encoding, constructing)
}

} // verus!
