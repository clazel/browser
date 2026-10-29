//! W3C HTML 5.2 §8.2.3 "Parse state": the two algorithms of it that the
//! modes call and that this module transcribes itself rather than reusing
//! [`crate::spec::base`]'s (source and modelling choices: [`super`]):
//! - §8.2.3.2 "has an element in table scope" (the stack of open
//!   elements);
//! - §8.2.3.3 "push onto the list of active formatting elements", with its
//!   three-element clause (the "Noah's Ark" clause).
//!
//! Modelling choices (as in [`crate::spec`], whose `Parser`, `Elem` and
//! `Fmt` these read):
//! - The stack of open elements is `Seq<Elem>`, the bottommost (the `html`
//!   element) first; "the current node" is the last entry.
//! - An element's "tag name" is its `name`, and its attributes "as they
//!   were when the element was created by the parser" are those of the
//!   token it was created for, kept with it in the list (`Fmt::Entry`).
//!   Attributes "can be paired such that the two attributes in each pair
//!   have identical names, namespaces, and values (the order of the
//!   attributes does not matter)" exactly when the two lists are equal as
//!   multisets.
//! - A stopped parser (the node limit) changes nothing.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// §8.2.3.2 The stack of open elements: "has an element in table scope"

/// The list of element types of "has an element in table scope": "html in
/// the HTML namespace, table in the HTML namespace, template in the HTML
/// namespace".
pub open spec fn w3c_table_scope_type(e: Elem) -> bool {
    e.ns == Namespace::Html && (e.tag == Tag::Html || e.tag == Tag::Table || e.tag == Tag::Template)
}

/// "The stack of open elements is said to have a particular element in a
/// specific scope when the following algorithm terminates in a match
/// state", with the list of [`w3c_table_scope_type`], the target given by
/// `target`, and `node` the `i`th entry from the bottom (step 1 starts with
/// `i` the length of the stack: "Initialize node to be the current node").
/// The stack always has an `html` element at the bottom, which is in the
/// list, so the algorithm never runs off it; if it does, it fails.
pub open spec fn w3c_in_table_scope(open: Seq<Elem>, i: int, target: spec_fn(Elem) -> bool) -> bool
    decreases i,
{
    if i <= 0 {
        false
    } else if target(open[i - 1]) {
        // 2. "If node is the target node, terminate in a match state."
        true
    } else if w3c_table_scope_type(open[i - 1]) {
        // 3. "Otherwise, if node is one of the element types in list,
        // terminate in a failure state."
        false
    } else {
        // 4. "Otherwise, set node to the previous entry in the stack of open
        // elements and return to step 2."
        w3c_in_table_scope(open, i - 1, target)
    }
}

/// "The stack of open elements has a `tag` element in table scope" (an
/// HTML element with that tag name).
pub open spec fn w3c_has_in_table_scope(p: Parser, tag: Tag) -> bool {
    w3c_in_table_scope(p.open, p.open.len() as int, |e: Elem| is_html(e, tag))
}

// ---------------------------------------------------------------------
// §8.2.3.3 The list of active formatting elements: "push onto the list
// of active formatting elements"

/// The entry is an element that has "the same tag name, namespace, and
/// attributes as element", the element `e` created for the token `t`.
pub open spec fn w3c_same_as_element(x: Fmt, e: Elem, t: TagTok) -> bool {
    match x {
        Fmt::Marker => false,
        Fmt::Entry { elem, token } => elem.name == e.name && elem.ns == e.ns && token.attrs.to_multiset()
            == t.attrs.to_multiset(),
    }
}

/// Where "after the last marker, if any, or anywhere in the list if there
/// are no markers" begins, looking at the first `i` entries of the list
/// from the end: the index after the last marker, or 0.
pub open spec fn w3c_after_last_marker(list: Seq<Fmt>, i: int) -> int
    decreases i,
{
    if i <= 0 {
        0
    } else if list[i - 1] is Marker {
        i
    } else {
        w3c_after_last_marker(list, i - 1)
    }
}

/// How many entries at indices `from..to` of the list are
/// [`w3c_same_as_element`].
pub open spec fn w3c_count_same(list: Seq<Fmt>, from: int, to: int, e: Elem, t: TagTok) -> nat
    decreases to - from,
{
    if from >= to {
        0
    } else if w3c_same_as_element(list[from], e, t) {
        1 + w3c_count_same(list, from + 1, to, e, t)
    } else {
        w3c_count_same(list, from + 1, to, e, t)
    }
}

/// "The earliest such element": the first index in `from..to` of an entry
/// that is [`w3c_same_as_element`] (`to` if there is none).
pub open spec fn w3c_earliest_same(list: Seq<Fmt>, from: int, to: int, e: Elem, t: TagTok) -> int
    decreases to - from,
{
    if from >= to {
        to
    } else if w3c_same_as_element(list[from], e, t) {
        from
    } else {
        w3c_earliest_same(list, from + 1, to, e, t)
    }
}

/// W3C HTML 5.2 §8.2.3.3 "push onto the list of active formatting
/// elements" the element `e`, created for the token `t`
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#push-onto-the-list-of-active-formatting-elements>).
pub open spec fn w3c_push_formatting(p: Parser, e: Elem, t: TagTok) -> Parser {
    if p.stopped {
        p
    } else {
        let list = p.formatting;
        let start = w3c_after_last_marker(list, list.len() as int);
        // 1. "If there are already three elements in the list of active
        // formatting elements after the last marker, if any, or anywhere in
        // the list if there are no markers, that have the same tag name,
        // namespace, and attributes as element, then remove the earliest
        // such element from the list of active formatting elements."
        let list1 = if w3c_count_same(list, start, list.len() as int, e, t) >= 3 {
            list.remove(w3c_earliest_same(list, start, list.len() as int, e, t))
        } else {
            list
        };
        // 2. "Add element to the list of active formatting elements."
        Parser { formatting: list1.push(Fmt::Entry { elem: e, token: t }), ..p }
    }
}

} // verus!
