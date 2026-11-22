//! The invariants that rule out a cycle through a template's host in the
//! document the tree builder builds: what a reachable parser state
//! satisfies so that `clazel_dom::spec::host_acyclic` holds of its document,
//! and what each rule must keep. This file holds spec functions only. The
//! proofs are in its submodules ([`hi`]: host-including ancestors under the
//! DOM calls; [`hostinv`]: the helpers; [`rules`]: the rules that do not go
//! by `reachable::keeps`; [`theorems`]: `theorem_reachable_host_acyclic`)
//! and in `reachable`, whose `keeps` carries [`host_step`].
//!
//! Why this is needed. `clazel-dom`'s `wf` forbids a cycle of parents, not
//! one through a template's host (a template inserted below a node of its
//! own contents). Its raw "insert" and "take all the children", which the
//! parser calls after its own checks, keep `host_acyclic` only under
//! `clazel_dom::host_acyclic_contract::insert_acyclic_requires` and
//! `reparent_children_acyclic_requires`: the node inserted is not a
//! *host-including* inclusive ancestor of its new parent. The
//! transcription's guards ([`insert_valid`], "insert an element at the
//! adjusted insertion location" step 2, the adoption agency algorithm's
//! step 4.21) check the inclusive-ancestor half only. The other half
//! follows from the invariants here.
//!
//! The invariants.
//! - **The stack's order is the document's order** ([`stack_ordered_of`]):
//!   no entry of the stack of open elements is a host-including inclusive
//!   ancestor of an entry above it in the stack (an earlier one). The
//!   fragment case's fragment, which the insertion target redirection map
//!   puts in place of the root, is treated as an entry above the whole
//!   stack ([`redirect_above_of`]).
//! - **No scope boundary below formattingElement** ([`scope_clear`]). This
//!   is not an invariant of the state but a fact of the adoption agency
//!   algorithm's step 4.5 (formattingElement is in scope), so nothing
//!   relating the markers of the list of active formatting elements to the
//!   stack is needed: no `table` or `template` element (nor any other
//!   element that pushes a marker) is below formattingElement in the stack
//!   ([`wall_clear`], which the inner loop keeps), so "the appropriate
//!   place for inserting a node" given commonAncestor, foster parenting
//!   included, is computed from entries above formattingElement, and
//!   lastNode, which the inner loop leaves an entry below formattingElement,
//!   is by the first invariant no host-including inclusive ancestor of it
//!   ([`place_bound`]).
//!
//! Every other DOM call of the rules inserts a node it has just created,
//! which is no host-including inclusive ancestor of a node created before
//! it ([`low`]).
//!
//! One rule does not keep the stack's order step by step: case 8 of "after
//! head" pushes the `head` element back, runs the "in head" rules and
//! removes it. Nothing here says that the `head` element is no ancestor of
//! an entry of the stack in that mode (the reachable-state invariant does
//! not pin the stack of "after head" to the `html` element alone), so
//! [`host_inv`] is stated of the parser before and after the rule, not in
//! between; in between only nodes just created are inserted
//! (`rules::wdoc`).
//!
//! What each rule keeps is [`host_step`]: [`host_inv`] of the parser before
//! gives [`host_inv`] of the parser after, stopped or not. What a guarded
//! DOM call needs for that is [`insert_keeps_host`] and
//! [`reparent_keeps_host`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

pub mod hi;
pub mod hostinv;
pub mod rules;
pub mod theorems;

verus! {

/// DOM §4.2 "host-including inclusive ancestor": `a` is one of `x` in `doc`
/// (`clazel_dom::spec::is_host_including_inclusive_ancestor`).
pub open spec fn hi(doc: Document, a: NodeId, x: NodeId) -> bool {
    dom::is_host_including_inclusive_ancestor(doc, a, x)
}

/// **The stack's order is the document's order**: no entry of the stack
/// `open` is a host-including inclusive ancestor, in `doc`, of an entry
/// above it in the stack (one with a smaller index). So the entries are
/// distinct, and an element is never moved below an element that is lower
/// in the stack.
pub open spec fn stack_ordered_of(doc: Document, open: Seq<Elem>) -> bool {
    forall|i: int, j: int| #![trigger open[j], open[i]] 0 <= i < j < open.len() ==> !hi(doc, open[j].id, open[i].id)
}

/// No entry of the stack is a host-including inclusive ancestor of the
/// fragment the insertion target redirection map names (the fragment
/// case's, in place of the root `html` element: HTML §13.2.4.5, §13.4
/// step 15).
pub open spec fn redirect_above_of(doc: Document, open: Seq<Elem>, redirect: Option<(NodeId, NodeId)>) -> bool {
    match redirect {
        None => true,
        Some((r, f)) => forall|j: int| 0 <= j < open.len() ==> !hi(doc, (#[trigger] open[j]).id, f),
    }
}

/// The host invariant of a document, a stack of open elements and a
/// redirection map: the document is `clazel_dom::spec::host_acyclic`, and
/// until parsing stops the stack is ordered as the document
/// ([`stack_ordered_of`], [`redirect_above_of`]).
#[verifier::opaque]
pub open spec fn host_inv_of(doc: Document, open: Seq<Elem>, redirect: Option<(NodeId, NodeId)>, stopped: bool) -> bool {
    &&& dom::host_acyclic(doc)
    &&& !stopped ==> stack_ordered_of(doc, open) && redirect_above_of(doc, open, redirect)
}

/// **The host invariant** of a parser state ([`host_inv_of`]): its document
/// has no cycle through a parent or a template's host, and until parsing
/// stops its stack of open elements is ordered as the document.
pub open spec fn host_inv(p: Parser) -> bool {
    host_inv_of(p.doc, p.open, p.redirect, p.stopped)
}

/// What every rule and every helper of the transcription keeps: the host
/// invariant of the parser after it, given that of the parser before.
pub open spec fn host_step(p: Parser, q: Parser) -> bool {
    host_inv(p) ==> host_inv(q)
}

/// What a rule application from `p` with outcome `o` keeps: [`host_step`]
/// to the outcome's parser (whether the token is handled, reprocessed, or
/// passed to another mode's rules).
pub open spec fn host_next(p: Parser, o: Outcome) -> bool {
    host_step(p, outcome_parser(o))
}

/// Node `n` is no host-including inclusive ancestor of a node created
/// before it. A node the parser has just created is so (it has no child,
/// and a `template` element's contents are created after it), and stays so
/// when it is inserted.
pub open spec fn low(doc: Document, n: NodeId) -> bool {
    forall|x: NodeId| #![trigger hi(doc, n, x)] x < n ==> !hi(doc, n, x)
}

/// What a guarded DOM "insert" of `node` into `parent` ([`dom_insert`])
/// needs to keep [`host_inv`], when the call is made: `node` is no
/// host-including inclusive ancestor of `parent`
/// (`clazel_dom::host_acyclic_contract::insert_acyclic_requires`, the half
/// [`insert_valid`] does not check), no entry of the stack that is a
/// host-including inclusive ancestor of `parent` is below an entry `node`
/// is one of, and `node` is not one of the redirection map's fragment.
pub open spec fn insert_keeps_host(p: Parser, node: NodeId, parent: NodeId) -> bool {
    &&& !hi(p.doc, node, parent)
    &&& forall|i: int, j: int|
        #![trigger p.open[j], p.open[i]]
        0 <= i < j < p.open.len() ==> !(hi(p.doc, p.open[j].id, parent) && hi(p.doc, node, p.open[i].id))
    &&& match p.redirect {
        None => true,
        Some((r, f)) => !hi(p.doc, node, f),
    }
}

/// What the guarded "take all of the child nodes of `from` and append them
/// to `to`" ([`dom_reparent_children`]) needs to keep [`host_inv`], when
/// the call is made: `from` is no host-including inclusive ancestor of `to`
/// (`clazel_dom::host_acyclic_contract::reparent_children_acyclic_requires`),
/// and the same of the stack and the redirection map's fragment as
/// [`insert_keeps_host`], for the nodes below `from`.
pub open spec fn reparent_keeps_host(p: Parser, from: NodeId, to: NodeId) -> bool {
    &&& !hi(p.doc, from, to)
    &&& forall|i: int, j: int|
        #![trigger p.open[j], p.open[i]]
        0 <= i < j < p.open.len() ==> !(hi(p.doc, p.open[j].id, to) && p.open[i].id != from && hi(p.doc, from, p.open[i].id))
    &&& match p.redirect {
        None => true,
        Some((r, f)) => !hi(p.doc, from, f),
    }
}

/// The element `e` is one of the elements a search "in scope" stops at
/// (§13.2.4.2, the default list): among them HTML `table` and `template`,
/// the elements "the appropriate place for inserting a node" looks for
/// when foster parenting, and every element that comes with a marker in
/// the list of active formatting elements (`applet`, `caption`, `marquee`,
/// `object`, `td`, `th`, `template`).
pub open spec fn scope_wall(e: Elem) -> bool {
    in_scope_list(e, Scope::Default)
}

/// **No scope boundary below entry `i`**: no entry of the stack `open`
/// after index `i` is a [`scope_wall`]. With `i` formattingElement's index
/// this is the adoption agency algorithm's step 4.5 ("formattingElement is
/// … in scope"). It gives [`wall_clear`], the part the inner loop keeps.
pub open spec fn scope_clear(open: Seq<Elem>, i: int) -> bool {
    forall|j: int| i < j < open.len() ==> !scope_wall(#[trigger] open[j])
}

/// No entry of the stack `open` after index `i` is an HTML `table` or
/// `template` element (`invariant::table_wall`), the elements "the
/// appropriate place for inserting a node" looks for when foster parenting.
/// [`scope_clear`] gives it, and the adoption agency algorithm's inner loop
/// keeps it: the elements it puts on the stack are created for tokens of
/// the list of active formatting elements, none a `table` or `template`
/// start tag.
pub open spec fn wall_clear(open: Seq<Elem>, i: int) -> bool {
    forall|j: int| i < j < open.len() ==> !crate::invariant::table_wall(#[trigger] open[j])
}

/// Every host-including inclusive ancestor, among the entries of the
/// stack, of node `target` is at index `k` or above it in the stack (a
/// smaller index). Of the parent of "the appropriate place for inserting a
/// node" given an override target at index `k` or above, with
/// [`wall_clear`] of `k`, this is what steps 4.17 to 4.21 of the adoption
/// agency algorithm need (with `k` formattingElement's index): lastNode, an
/// entry below index `k`, is no host-including inclusive ancestor of the
/// place.
pub open spec fn place_bound(p: Parser, target: NodeId, k: int) -> bool {
    forall|j: int| k < j < p.open.len() ==> !hi(p.doc, (#[trigger] p.open[j]).id, target)
}

/// What the corollary gives a caller of `clazel-dom`'s deep clone: every
/// node of the parser's document that may be cloned
/// (`clazel_dom::spec::clone_requires`) meets
/// `clazel_dom::contract::clone_deep_requires`.
pub open spec fn clone_deep_ready(p: Parser) -> bool {
    forall|n: NodeId| #[trigger] dom::clone_requires(p.doc, n) ==> clazel_dom::contract::clone_deep_requires(p.doc, n)
}

} // verus!
