//! Reading elements of a `clazel-dom` arena: attributes, names, the `type`
//! of an `input`, and the walks up the ancestors. Each function is proven
//! equal to the spec function it names, in a well-formed arena where it
//! follows parent links.

use super::strings::*;
#[cfg(verus_only)]
use crate::contract::*;
use crate::spec::*;
#[cfg(verus_only)]
use clazel_dom::exec::attrs_view;
use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
#[cfg(verus_only)]
use clazel_dom::lemmas::lemma_wf_witness;
#[cfg(verus_only)]
use clazel_dom::spec as dom;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Facts of a well-formed arena

/// A node's parent is a node of the arena.
pub proof fn lemma_parent_valid(doc: Document, x: NodeId)
    requires
        dom::wf(doc),
        dom::valid(doc, x),
        doc.nodes[x as int].parent is Some,
    ensures
        dom::valid(doc, doc.nodes[x as int].parent->Some_0),
{
    let paths = lemma_wf_witness(doc);
}

/// A child of a node is a node of the arena, and its parent is that node.
pub proof fn lemma_child_valid(doc: Document, x: NodeId, k: int)
    requires
        dom::wf(doc),
        dom::valid(doc, x),
        0 <= k < doc.nodes[x as int].children.len(),
    ensures
        dom::valid(doc, doc.nodes[x as int].children[k]),
        doc.nodes[doc.nodes[x as int].children[k] as int].parent == Some(x),
{
    let paths = lemma_wf_witness(doc);
}

// ---------------------------------------------------------------------
// Attributes

/// The view of an optional reference to a string.
pub open spec fn ref_view(r: Option<&Vec<u32>>) -> Option<Seq<u32>> {
    match r {
        Some(v) => Some(v@),
        None => None,
    }
}

/// [`find_attr`]: the value of the first attribute with a null namespace
/// and the local name `name`.
pub fn find_attr_exec<'a>(list: &'a [ExecAttr], name: &[u8]) -> (r: Option<&'a Vec<u32>>)
    ensures
        find_attr_ensures(attrs_view(list@), name@, ref_view(r)),
{
    let ghost av = attrs_view(list@);
    let mut i: usize = 0;
    proof {
        assert(av.skip(0) =~= av);
    }
    while i < list.len()
        invariant
            i <= list.len(),
            av == attrs_view(list@),
            find_attr(av, ascii(name@)) == find_attr(av.skip(i as int), ascii(name@)),
        decreases list.len() - i,
    {
        match list.get(i) {
            Some(a) => {
                proof {
                    assert(av.skip(i as int).drop_first() =~= av.skip(i as int + 1));
                    assert(av.skip(i as int)[0] == av[i as int]);
                    assert(av[i as int] == list@[i as int]@);
                }
                let is_null = a.namespace.is_none();
                if is_null && eq_ascii(a.local_name.as_slice(), name) {
                    return Some(&a.value);
                }
            },
            None => {
                return None;
            },
        }
        // Never saturates: i < list.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(av.skip(list.len() as int) =~= Seq::<Attr>::empty());
    }
    None
}

/// [`is_element`].
pub fn is_element_exec(arena: &Arena, n: usize) -> (r: bool)
    requires
        dom::valid(arena@, n),
    ensures
        r == is_element(arena@, n),
{
    matches!(arena.kind(n), ExecKind::Element { .. })
}

/// Element `n` is an element of the HTML namespace with local name `name`.
pub fn is_html_exec(arena: &Arena, n: usize, name: &[u8]) -> (r: bool)
    requires
        dom::valid(arena@, n),
    ensures
        r == is_html(arena@, n, name@),
{
    match arena.kind(n) {
        ExecKind::Element { namespace: Some(Namespace::Html), local_name, .. } => eq_ascii(local_name.as_slice(), name),
        _ => false,
    }
}

/// The value of attribute `name` of element `n`.
pub fn attr_exec<'a>(arena: &'a Arena, n: usize, name: &[u8]) -> (r: Option<&'a Vec<u32>>)
    requires
        is_element(arena@, n),
    ensures
        ref_view(r) == attr(arena@, n, name@),
{
    match arena.kind(n) {
        ExecKind::Element { attributes, .. } => find_attr_exec(attributes.as_slice(), name),
        _ => None,
    }
}

/// Element `n` has attribute `name` specified.
pub fn has_attr_exec(arena: &Arena, n: usize, name: &[u8]) -> (r: bool)
    requires
        is_element(arena@, n),
    ensures
        r == has_attr(arena@, n, name@),
{
    attr_exec(arena, n, name).is_some()
}

/// [`element_id`].
pub fn element_id_exec(arena: &Arena, n: usize) -> (r: Option<&Vec<u32>>)
    requires
        is_element(arena@, n),
    ensures
        ref_view(r) == element_id(arena@, n),
{
    match attr_exec(arena, n, b"id") {
        Some(v) => {
            if !v.is_empty() {
                Some(v)
            } else {
                None
            }
        },
        None => None,
    }
}

/// [`input_type`].
pub fn input_type_exec(arena: &Arena, n: usize) -> (r: InputType)
    requires
        is_element(arena@, n),
    ensures
        r == input_type(arena@, n),
{
    match attr_exec(arena, n, b"type") {
        None => InputType::Text,
        Some(v) => {
            let v = v.as_slice();
            if ci_eq_exec(v, b"hidden") {
                InputType::Hidden
            } else if ci_eq_exec(v, b"search") {
                InputType::Search
            } else if ci_eq_exec(v, b"tel") {
                InputType::Tel
            } else if ci_eq_exec(v, b"url") {
                InputType::Url
            } else if ci_eq_exec(v, b"email") {
                InputType::Email
            } else if ci_eq_exec(v, b"password") {
                InputType::Password
            } else if ci_eq_exec(v, b"checkbox") {
                InputType::Checkbox
            } else if ci_eq_exec(v, b"radio") {
                InputType::Radio
            } else if ci_eq_exec(v, b"file") {
                InputType::File
            } else if ci_eq_exec(v, b"submit") {
                InputType::Submit
            } else if ci_eq_exec(v, b"image") {
                InputType::Image
            } else if ci_eq_exec(v, b"reset") {
                InputType::Reset
            } else if ci_eq_exec(v, b"button") {
                InputType::Button
            } else if ci_eq_exec(v, b"number") || ci_eq_exec(v, b"date") || ci_eq_exec(v, b"month") || ci_eq_exec(
                v,
                b"week",
            ) || ci_eq_exec(v, b"time") || ci_eq_exec(v, b"datetime-local") || ci_eq_exec(v, b"range")
                || ci_eq_exec(v, b"color") {
                InputType::Other
            } else {
                InputType::Text
            }
        },
    }
}

// ---------------------------------------------------------------------
// Element classes

/// [`is_submittable`].
pub fn is_submittable_exec(arena: &Arena, n: usize) -> (r: bool)
    requires
        dom::valid(arena@, n),
    ensures
        r == is_submittable(arena@, n),
{
    is_html_exec(arena, n, b"button") || is_html_exec(arena, n, b"input") || is_html_exec(arena, n, b"select")
        || is_html_exec(arena, n, b"textarea")
}

/// [`is_button`].
pub fn is_button_exec(arena: &Arena, n: usize) -> (r: bool)
    requires
        dom::valid(arena@, n),
    ensures
        r == is_button(arena@, n),
{
    if is_html_exec(arena, n, b"button") {
        return true;
    }
    if !is_html_exec(arena, n, b"input") {
        return false;
    }
    matches!(input_type_exec(arena, n), InputType::Submit | InputType::Image | InputType::Reset | InputType::Button)
}

/// [`is_auto_directionality`].
pub fn is_auto_directionality_exec(arena: &Arena, n: usize) -> (r: bool)
    requires
        dom::valid(arena@, n),
    ensures
        r == is_auto_directionality(arena@, n),
{
    if is_html_exec(arena, n, b"textarea") {
        return true;
    }
    if !is_html_exec(arena, n, b"input") {
        return false;
    }
    matches!(
        input_type_exec(arena, n),
        InputType::Hidden
            | InputType::Text
            | InputType::Search
            | InputType::Tel
            | InputType::Url
            | InputType::Email
            | InputType::Password
            | InputType::Submit
            | InputType::Reset
            | InputType::Button
    )
}

} // verus!
