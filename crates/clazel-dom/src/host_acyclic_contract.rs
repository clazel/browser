//! What the raw operations need to keep [`host_acyclic`]. Every mutation of
//! the tree keeps [`wf`] (`contract`), and also keeps [`host_acyclic`], the
//! one thing [`wf`] does not say (no cycle through a template's host),
//! proven about the spec in `host_acyclic_lemmas`. Two raw operations need a
//! precondition beyond their `wf` one for that: [`insert_acyclic_requires`]
//! and [`reparent_children_acyclic_requires`], DOM's "host-including
//! inclusive ancestor" check (§4.2.3† "ensure pre-insertion validity", step
//! 2) in place of the inclusive-ancestor check the parser's calls carry.
//! Every operation that makes that check itself (pre-insert, replace) needs
//! nothing more than [`host_acyclic`] of its input.
//!
//! (This is a module of its own, and not part of `contract`, which other
//! proofs import: an unrelated spec function there changes what the solver
//! does with the failing proofs of their mutations.)

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What `Arena::append`, `Arena::insert_before` and the spec's [`insert`] need
/// to keep [`host_acyclic`] (`host_acyclic_lemmas::theorem_insert_host_acyclic`):
/// [`insert_requires`] on a [`host_acyclic`] arena, where `node` is not a
/// host-including inclusive ancestor of `parent` (DOM §4.2.3† "ensure
/// pre-insertion validity" step 2; [`insert_requires`] only has the
/// inclusive-ancestor half of it). Without the host half, a template
/// inserted below a node of its own contents makes a cycle through the host.
pub open spec fn insert_acyclic_requires(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>) -> bool {
    &&& insert_requires(doc, node, parent, child)
    &&& host_acyclic(doc)
    &&& !is_host_including_inclusive_ancestor(doc, node, parent)
}

/// What `Arena::reparent_children(from, to)` needs to keep [`host_acyclic`]:
/// [`reparent_children_requires`] on a [`host_acyclic`] arena, where `from`
/// is not a host-including inclusive ancestor of `to`.
pub open spec fn reparent_children_acyclic_requires(doc: Document, from: NodeId, to: NodeId) -> bool {
    &&& reparent_children_requires(doc, from, to)
    &&& host_acyclic(doc)
    &&& !is_host_including_inclusive_ancestor(doc, from, to)
}

} // verus!
