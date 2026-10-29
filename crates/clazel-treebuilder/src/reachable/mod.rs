//! The reachable-state invariant ([`crate::invariant::reachable_inv`]) is
//! kept by every rule application and so by [`dispatch`], and every parser
//! reachable from [`new_parser`] or [`fragment_parser`] satisfies it
//! (Phase 4 item 4.10).
//!
//! The proof. A running parser is [`good`] when its stack is rooted at the
//! `html` element, the `html` element's id is fresh for the list of active
//! formatting elements and the form element pointer ([`root_ids`]), and
//! its records are tagged ([`tags_wf`]). Each helper of the transcription
//! [`keeps`] that (the `helpers` submodule), under the condition its
//! callers check (an element in scope above `html`, a fresh element); the
//! per-mode lemmas compose them and check each mode's [`shape`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

pub mod adoption;
pub mod body;
pub mod body_tags;
pub mod early;
pub mod helpers;
pub mod lists;
pub mod rest;
pub mod tables;

/// Every name of the transcription and of this module, for the ghost
/// imports of the submodules (`use super::spec::*;`).
mod spec {
    #[cfg(verus_only)]
    pub use super::*;
    #[cfg(verus_only)]
    pub use crate::spec::*;
    #[cfg(verus_only)]
    pub use crate::termination::{
        formatting_ok, headish, is_end, is_start, modes_ok, rules_ok, template_count, templates_in,
    };
}

verus! {

/// A running parser's stack is rooted, the `html` element's id is fresh,
/// its records are tagged, and no entry of the list of active formatting
/// elements is for a `template` start tag.
pub open spec fn good(p: Parser) -> bool {
    &&& rooted_seq(p.open)
    &&& root_ids(p)
    &&& tags_wf(p)
    &&& crate::termination::formatting_ok(p)
}

/// A stopped or [`good`] parser.
pub open spec fn live(p: Parser) -> bool {
    p.stopped || good(p)
}

/// `q` comes from `p` by steps that keep [`good`], the `html` element, the
/// modes, the context and the stack of template insertion modes, grow the
/// document and add no `template` element to the stack; or `q` has stopped.
/// A stopped parser stays stopped.
pub open spec fn keeps(p: Parser, q: Parser) -> bool {
    &&& p.stopped ==> q.stopped
    &&& !q.stopped ==> {
        &&& good(q)
        &&& q.open[0] == p.open[0]
        &&& q.doc.nodes.len() >= p.doc.nodes.len()
        &&& q.mode == p.mode
        &&& q.original_mode == p.original_mode
        &&& q.context == p.context
        &&& q.template_modes == p.template_modes
        &&& crate::termination::template_count(q) <= crate::termination::template_count(p)
    }
}

/// [`keeps`] is reflexive on live parsers.
pub proof fn lemma_keeps_refl(p: Parser)
    requires
        live(p),
    ensures
        keeps(p, p),
{
}

/// [`keeps`] leads to a live parser.
pub proof fn lemma_keeps_live(p: Parser, q: Parser)
    requires
        keeps(p, q),
    ensures
        live(q),
{
}

/// [`keeps`] is transitive.
pub proof fn lemma_keeps_trans(p: Parser, q: Parser, r: Parser)
    requires
        keeps(p, q),
        keeps(q, r),
    ensures
        keeps(p, r),
{
}

/// What a rule application's outcome gives the next step: a stopped
/// parser, or a running one with [`reach_core`], and `modes_ok` when the
/// token is handled (the edge lemmas of `termination` give it otherwise),
/// and [`rules_need`] of the rules it continues with.
pub open spec fn next_core(o: Outcome) -> bool {
    match o {
        Outcome::Done(q) => q.stopped || (crate::termination::modes_ok(q) && reach_core(q)),
        Outcome::Reprocess(q, t2) => q.stopped || reach_core(q),
        Outcome::Using(m, q, t2) => q.stopped || (reach_core(q) && rules_need(Rules::Html(m), q, t2)),
    }
}

/// A parser with the stack, list, pointers, modes and context of one with
/// [`reach_core`] and `modes_ok`, and an arena at least as large, has them.
pub proof fn lemma_core_frame(p: Parser, q: Parser)
    requires
        reach_core(p),
        crate::termination::modes_ok(p),
        q.open == p.open,
        q.formatting == p.formatting,
        q.form == p.form,
        q.context == p.context,
        q.mode == p.mode,
        q.original_mode == p.original_mode,
        q.template_modes == p.template_modes,
        q.doc.nodes.len() >= p.doc.nodes.len(),
    ensures
        reach_core(q),
        crate::termination::modes_ok(q),
{
}

/// A parser [`keeps`] made, put in a [`rooted_mode`], has [`reach_core`]
/// and `modes_ok`.
pub proof fn lemma_finish(p: Parser, q1: Parser, q: Parser)
    requires
        crate::termination::modes_ok(p),
        keeps(p, q1),
        q.open == q1.open,
        q.doc == q1.doc,
        q.formatting == q1.formatting,
        q.form == q1.form,
        q.context == q1.context,
        q.template_modes == q1.template_modes,
        q.stopped == q1.stopped,
        rooted_mode(q.mode),
        q.mode == Mode::InTemplate ==> q.template_modes.len() > 0,
    ensures
        !q.stopped ==> reach_core(q) && crate::termination::modes_ok(q),
{
    if !q.stopped {
        assert(crate::termination::template_count(q) == crate::termination::template_count(q1));
        assert(crate::termination::formatting_ok(q) == crate::termination::formatting_ok(q1));
    }
}

/// An HTML element pushed onto a rooted stack is above `html`.
pub proof fn lemma_html_above_push(o: Seq<Elem>, e: Elem)
    requires
        rooted_seq(o),
        e.ns == Namespace::Html,
    ensures
        html_above(o.push(e)),
        rooted_seq(o.push(e)),
{
    let o2 = o.push(e);
    assert(o2[0] == o[0]);
    crate::exec::stack::lemma_last_index_where_found(o2, o2.len() as int, html_ns(), o.len() as int);
}

/// A stack with an HTML element above `html` has two entries.
pub proof fn lemma_html_above_len(o: Seq<Elem>)
    requires
        html_above(o),
    ensures
        o.len() >= 2,
{
    crate::termination::helpers_ranking::lemma_last_index_where(o, o.len() as int, html_ns());
}

} // verus!
