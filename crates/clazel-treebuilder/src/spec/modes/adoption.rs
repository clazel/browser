//! HTML §13.2.6.4.7 the "adoption agency algorithm" (run by the "in body"
//! rules for formatting element tags), with its numbered steps.
//!
//! Modelling choices (see also [`super::super`]):
//! - **The fallback.** Step 4.3's "act as described in the "any other end
//!   tag" entry above and return" is the result
//!   [`AdoptionOutcome::AnyOtherEndTag`]; the caller (the "in body" rules,
//!   [`super::in_body_adoption`]) then runs that entry for the token. This
//!   keeps the "in body" rules out of this file.
//! - **The loops** are recursive functions: the outer loop
//!   ([`aa_outer`]) on `8 - outerLoopCounter` (step 4.1 returns once the
//!   counter reaches 8), the inner loop ([`aa_inner`]) on node's index in
//!   the stack of open elements.
//! - **node** is held by its index in the stack. Step 4.16.2's "the
//!   element immediately above node …, or if node is no longer in the stack
//!   …, the element that was immediately above node … before node was
//!   removed" is the entry at index − 1 in both cases: removing node (step
//!   4.16.5) leaves the entries above it where they were, and replacing it
//!   (4.16.6) keeps its index.
//! - **The bookmark** (step 4.10) is [`Bookmark`]: either still at
//!   formattingElement's position, or "immediately after" a new element's
//!   entry (4.16.7). bookmarkMoved (4.15) is `bookmark is After`. Neither
//!   position can disappear before step 4.23: formattingElement stays in the
//!   list (the inner loop stops at it), and an entry created by 4.16.6 is
//!   for an element at or below node's index, which the inner loop never
//!   revisits.
//! - **The sanitizer** is null ([`super::super`]): no element is "replaced
//!   with its children" and every sanitizer action is "Keep". So steps 4.12,
//!   4.13, 4.16.8 to 4.16.10, 4.19, 4.25, 4.26 and 4.28 to 4.29 do nothing:
//!   pendingRedirects stays empty, lastNode is never null, only the "Keep"
//!   branches of 4.16.11 and 4.27 run, and the redirection map's only entry
//!   (the fragment case's root, the first element of the stack) is never
//!   below newElement in the stack (step 4.29). Each place says so.
//! - **Node limit.** When creating an element stops parsing, the algorithm
//!   returns at once (a stopped parser changes nothing).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// How the adoption agency algorithm ended.
pub enum AdoptionOutcome {
    /// It returned.
    Done(Parser),
    /// Step 4.3: "act as described in the "any other end tag" entry above
    /// and return" (the caller does so with this parser).
    AnyOtherEndTag(Parser),
}

/// Step 4.10's bookmark in the list of active formatting elements.
pub enum Bookmark {
    /// "the position of formattingElement in the list of active formatting
    /// elements relative to the elements on either side of it".
    FormattingElement,
    /// Step 4.16.7: "immediately after the new node" with this id.
    After(NodeId),
}

/// The index of the last element entry of `f` among `from..i` whose
/// element satisfies `pred`, or -1.
pub open spec fn fmt_last_where(f: Seq<Fmt>, from: int, i: int, pred: spec_fn(Elem) -> bool) -> int
    decreases i - from,
{
    if i <= from {
        -1
    } else if f[i - 1] is Entry && pred(f[i - 1]->Entry_elem) {
        i - 1
    } else {
        fmt_last_where(f, from, i - 1, pred)
    }
}

/// The index of the first entry of `open` from index `j` on that is in the
/// special category, or -1.
pub open spec fn first_special_from(open: Seq<Elem>, j: int) -> int
    decreases open.len() - j,
{
    if j < 0 || j >= open.len() {
        -1
    } else if is_special(open[j]) {
        j
    } else {
        first_special_from(open, j + 1)
    }
}

/// "Take all of the child nodes of `from` and append them to `to`", as the
/// parser calls it: made only when `clazel_dom::spec::
/// reparent_children_requires` holds (apart from `wf`, which the parser
/// keeps), which it always does in step 4.27.1 (`to` is the new element),
/// so the guard only makes that explicit.
pub open spec fn dom_reparent_children(p: Parser, from: NodeId, to: NodeId) -> Parser {
    let d = p.doc;
    if p.stopped || !(dom::valid(d, from) && dom::valid(d, to) && from != to && dom::may_have_children(d.nodes[from as int].kind)
        && dom::may_have_children(d.nodes[to as int].kind) && !dom::is_inclusive_ancestor(d, from, to)) {
        p
    } else {
        Parser { doc: dom::reparent_children(d, from, to), ..p }
    }
}

/// Step 4.16, the inner loop, from node at index `node_idx` (step 4.11 sets
/// it to furthestBlock's), with lastNode `last_node`, innerLoopCounter
/// `counter` and the bookmark. Returns the parser, lastNode and the
/// bookmark when the loop breaks (4.16.3).
pub open spec fn aa_inner(p: Parser, fe: Elem, ca: Elem, node_idx: int, last_node: Elem, counter: nat, bookmark: Bookmark) -> (
    Parser,
    Elem,
    Bookmark,
)
    decreases node_idx,
{
    if p.stopped || node_idx <= 0 {
        // Unreachable while running: formattingElement is above node in the
        // stack, so 4.16.3 breaks first.
        (p, last_node, bookmark)
    } else {
        // 4.16.1 "Increment innerLoopCounter by 1."
        let counter = counter + 1;
        // 4.16.2 "Let node be the element immediately above node in the
        // stack of open elements, or if node is no longer in the stack …, the
        // element that was immediately above node … before node was removed."
        let i = node_idx - 1;
        let node = p.open[i];
        if node.id == fe.id {
            // 4.16.3 "If node is formattingElement, then break."
            (p, last_node, bookmark)
        } else {
            // 4.16.4 "If innerLoopCounter is greater than 3 and node is in the
            // list of active formatting elements, then remove node from the
            // list of active formatting elements."
            let p1 = if counter > 3 && in_formatting(p, node.id) {
                Parser { formatting: p.formatting.remove(fmt_index_of(p.formatting, p.formatting.len() as int, node.id)), ..p }
            } else {
                p
            };
            if !in_formatting(p1, node.id) {
                // 4.16.5 "If node is not in the list of active formatting
                // elements, then remove node from the stack of open elements
                // and continue."
                aa_inner(remove_open_at(p1, i), fe, ca, i, last_node, counter, bookmark)
            } else {
                // 4.16.6 "Create an element for the token for which the
                // element node was created, in the HTML namespace, with
                // commonAncestor as the intended parent; replace the entry for
                // node in the list of active formatting elements with an entry
                // for the new element, replace the entry for node in the stack
                // of open elements with an entry for the new element, and set
                // node to the new element."
                let k = fmt_index_of(p1.formatting, p1.formatting.len() as int, node.id);
                let token = p1.formatting[k]->Entry_token;
                let (p2, new_element) = create_element_for_token(p1, token, Namespace::Html, ca.id);
                if p2.stopped {
                    (p2, last_node, bookmark)
                } else {
                    let p3 = Parser {
                        formatting: p2.formatting.update(k, Fmt::Entry { elem: new_element, token }),
                        open: p2.open.update(i, new_element),
                        ..p2
                    };
                    // 4.16.7 "If bookmarkMoved is false, then move the
                    // aforementioned bookmark to be immediately after the new
                    // node in the list of active formatting elements, and set
                    // bookmarkMoved to true."
                    let bm = match bookmark {
                        Bookmark::FormattingElement => Bookmark::After(new_element.id),
                        Bookmark::After(b) => Bookmark::After(b),
                    };
                    // 4.16.8 "Let nodeAction be "Keep"." 4.16.9: the sanitizer
                    // is null, so it stays "Keep". 4.16.10: nodeAction is not
                    // "Replace with children", and pendingRedirects is empty
                    // (nothing to set or empty).
                    // 4.16.11 "Keep": "If lastNode is non-null, then append
                    // lastNode to node. Set lastNode to node." (lastNode is never
                    // null: the sanitizer is null.)
                    let p4 = dom_insert(p3, last_node.id, new_element.id, None);
                    aa_inner(p4, fe, ca, i, new_element, counter, bm)
                }
            }
        }
    }
}

/// Steps 4.17 to 4.29, after the inner loop: formattingElement `fe`,
/// furthestBlock `fb`, commonAncestor `ca`, lastNode and the bookmark.
pub open spec fn aa_finish(p: Parser, fe: Elem, fb: Elem, ca: Elem, last_node: Elem, bookmark: Bookmark) -> Parser {
    if p.stopped {
        p
    } else {
        // 4.17 "Let insertionLocation be the appropriate place for inserting a
        // node given commonAncestor."
        let insertion_location = appropriate_place(p, Some(ca));
        // 4.18 "Let (target, refNode) be the adjusted insertion location given
        // insertionLocation."
        let l = adjusted_location(p, Some(insertion_location));
        let target = l.parent;
        let ref_node = l.child;
        // 4.19: pendingRedirects is empty (the sanitizer is null).
        // 4.20 "If lastNode is non-null and lastNode's parent is non-null,
        // then remove lastNode." (`dom_remove` checks the parent.)
        let p1 = dom_remove(p, last_node.id);
        let d = p1.doc;
        // 4.21 "If all of the following are true: lastNode is non-null;
        // lastNode's parent is null; lastNode is not a host-including
        // inclusive ancestor of target; target is not a Document node, or it
        // does not have an element child; and refNode is null or its parent is
        // target, then: 4.21.1 Assert: ensure pre-insert validity … does not
        // throw. 4.21.2 Insert lastNode into target before refNode."
        let p2 = if dom::valid(d, last_node.id) && d.nodes[last_node.id as int].parent is None && !dom::is_inclusive_ancestor(
            d,
            last_node.id,
            target,
        ) && !(d.nodes[target as int].kind is Document && has_element_child(d, target)) && match ref_node {
            None => true,
            Some(r) => d.nodes[r as int].parent == Some(target),
        } {
            dom_insert(p1, last_node.id, target, ref_node)
        } else {
            p1
        };
        // 4.22 "Let newElement be the result of creating an element for the
        // token for which formattingElement was created, in the HTML
        // namespace, with furthestBlock as the intended parent."
        let fi = fmt_index_of(p2.formatting, p2.formatting.len() as int, fe.id);
        let token = p2.formatting[fi]->Entry_token;
        let (p3, new_element) = create_element_for_token(p2, token, Namespace::Html, fb.id);
        if p3.stopped {
            p3
        } else {
            // 4.23 "Remove formattingElement from the list of active
            // formatting elements, and insert newElement into the list of
            // active formatting elements at the position of the aforementioned
            // bookmark."
            let entry = Fmt::Entry { elem: new_element, token };
            let f1 = p3.formatting.remove(fi);
            let f2 = match bookmark {
                // At formattingElement's position: between the entries that
                // were on either side of it.
                Bookmark::FormattingElement => f1.insert(fi, entry),
                Bookmark::After(b) => f1.insert(fmt_index_of(f1, f1.len() as int, b) + 1, entry),
            };
            // 4.24 "Remove formattingElement from the stack of open elements,
            // and insert newElement into the stack of open elements
            // immediately below the position of furthestBlock in that stack."
            let o1 = p3.open.remove(open_index_of(p3, fe.id));
            let o2 = o1.insert(last_index_where(o1, o1.len() as int, |e: Elem| e.id == fb.id) + 1, new_element);
            let p4 = Parser { formatting: f2, open: o2, ..p3 };
            // 4.25 "Let sanitizerAction be "Keep"." 4.26: the sanitizer is
            // null, so it stays "Keep".
            // 4.27 "Keep": 4.27.1 "Take all of the child nodes of
            // furthestBlock and append them to newElement."
            let p5 = dom_reparent_children(p4, fb.id, new_element.id);
            // 4.27.2 "Let (newElementParent, newElementRefNode) be the adjusted
            // insertion location given (furthestBlock, null)."
            let l2 = adjusted_location(p5, Some(Location { parent: fb.id, child: None }));
            // 4.27.3 "Insert newElement into newElementParent before
            // newElementRefNode."
            // 4.28, 4.29: the redirection map's only entry is the fragment
            // case's root, the first element of the stack, never below
            // newElement; the loop does nothing.
            dom_insert(p5, new_element.id, l2.parent, l2.child)
        }
    }
}

/// Step 4, the outer loop ("While true:"), with outerLoopCounter `counter`,
/// for subject `tt.name`.
pub open spec fn aa_outer(p: Parser, tt: TagTok, counter: nat) -> AdoptionOutcome
    decreases 8 - counter,
{
    if p.stopped || counter >= 8 {
        // 4.1 "If outerLoopCounter is greater than or equal to 8, then
        // return."
        AdoptionOutcome::Done(p)
    } else {
        // 4.2 "Increment outerLoopCounter by 1." (The recursive call below
        // passes `counter + 1`.)
        // 4.3 "Let formattingElement be the last element in the list of active
        // formatting elements that: is between the end of the list and the
        // last marker in the list, if any, or the start of the list otherwise,
        // and has the tag name subject."
        let f = p.formatting;
        let fi = fmt_last_where(f, after_last_marker(f, f.len() as int), f.len() as int, |e: Elem| e.name == tt.name);
        if fi < 0 {
            // "If there is no such element, then act as described in the "any
            // other end tag" entry above and return."
            AdoptionOutcome::AnyOtherEndTag(p)
        } else {
            let fe = f[fi]->Entry_elem;
            let fe_idx = open_index_of(p, fe.id);
            if fe_idx < 0 {
                // 4.4 "If formattingElement is not in the stack of open
                // elements, then this is a parse error; remove the element from
                // the list, and return."
                AdoptionOutcome::Done(Parser { formatting: f.remove(fi), ..p })
            } else if !has_node_in_scope(p, fe.id, Scope::Default) {
                // 4.5 "If formattingElement is in the stack of open elements,
                // but the element is not in scope, then this is a parse error;
                // return."
                AdoptionOutcome::Done(p)
            } else {
                // 4.6 "If formattingElement is not the current node, this is a
                // parse error. (But do not return.)"
                // 4.7 "Let furthestBlock be the topmost node in the stack of
                // open elements that is lower in the stack than
                // formattingElement, and is an element in the special
                // category. There might not be one."
                let fb_idx = first_special_from(p.open, fe_idx + 1);
                if fb_idx < 0 {
                    // 4.8 "If there is no furthestBlock, then the UA must first
                    // pop all the nodes from the bottom of the stack of open
                    // elements, from the current node up to and including
                    // formattingElement, then remove formattingElement from the
                    // list of active formatting elements, and finally return."
                    let q = pop_until_node_popped(p, fe.id);
                    AdoptionOutcome::Done(Parser { formatting: q.formatting.remove(fi), ..q })
                } else {
                    let fb = p.open[fb_idx];
                    // 4.9 "Let commonAncestor be the element immediately above
                    // formattingElement in the stack of open elements."
                    let ca = p.open[fe_idx - 1];
                    // 4.10 "Let a bookmark note the position of
                    // formattingElement in the list of active formatting
                    // elements …" (`Bookmark::FormattingElement`).
                    // 4.11 "Let node and lastNode be furthestBlock."
                    // 4.12 "Let pendingRedirects be an empty list." 4.13: the
                    // sanitizer is null (pendingRedirects stays empty).
                    // 4.14 "Let innerLoopCounter be 0." 4.15 "Let bookmarkMoved
                    // be false." 4.16 the inner loop.
                    let (p1, last_node, bm) = aa_inner(p, fe, ca, fb_idx, fb, 0, Bookmark::FormattingElement);
                    // 4.17 to 4.29, then back to the top of the loop.
                    aa_outer(aa_finish(p1, fe, fb, ca, last_node, bm), tt, counter + 1)
                }
            }
        }
    }
}

/// The adoption agency algorithm for token `tt` ("which takes as its only
/// argument a token token for which the algorithm is being run").
pub open spec fn adoption_agency(p: Parser, tt: TagTok) -> AdoptionOutcome {
    // 1. "Let subject be token's tag name." (`tt.name`)
    // 2. "If the current node is an HTML element whose tag name is subject,
    // and the current node is not in the list of active formatting elements,
    // then pop the current node off the stack of open elements and return."
    if p.open.len() > 0 && current_node(p).ns == Namespace::Html && current_node(p).name == tt.name && !in_formatting(
        p,
        current_node(p).id,
    ) {
        AdoptionOutcome::Done(pop(p))
    } else {
        // 3. "Let outerLoopCounter be 0." 4. "While true:"
        aa_outer(p, tt, 0)
    }
}

} // verus!
