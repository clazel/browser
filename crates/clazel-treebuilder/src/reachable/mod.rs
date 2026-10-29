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
//!
//! The cells. In the "in cell" mode the stack holds a cell with no `table`
//! or `template` element above it ([`cell_ok`], [`cell_scoped`]), and
//! [`keeps`] keeps its last cell ([`cell_kept`]): every pop a rule
//! applied in that mode makes stops above the last cell (a scope search
//! whose list holds `td` and `th` finds its target above it, "any other
//! end tag" and foreign content stop at special or HTML elements, the
//! adoption agency's formattingElement is in scope), and the rules that
//! remove an element by id never name a cell ([`cells_wf`]: no entry of the
//! list of active formatting elements, nor the form element pointer, has a
//! cell's id). The rules that do pop the cell switch the mode ("close the
//! cell", the `template` end tag, "in template"'s end of file, the
//! `frameset` start tag); they are proven on the parser put in another mode
//! (`cells::mode_as`). The elements pushed in the "in cell" mode are not
//! `table` or `template` elements, but for the `table` and `template` start
//! tags, which switch the mode (the `table` one is proven on the parser put
//! in the "in table" mode); "reset the insertion mode appropriately"
//! chooses "in cell" only below every such element (`walls`).
//!
//! The `html` element. No element above the root is an `html` element
//! ([`html_once`]): the parser never inserts one for an `html` start tag
//! after "before html", and the list of active formatting elements holds
//! no entry for one ([`cells_wf`]).
//!
//! Stopped parsers. [`keeps`] and the per-mode lemmas say nothing of a
//! parser a rule stops; [`stopped`] proves that it has an empty stack and
//! satisfies `termination::modes_ok`, by frame lemmas of its own
//! ([`stop_frame`], [`stop_body`]: every helper keeps the modes, stopped or
//! not) and per-mode lemmas ([`stop_early`], [`stop_in_body`],
//! [`stop_tables`]).
//!
//! The document. A running parser also keeps [`doc::dinv`]: the document is
//! well formed, every record of the stack is an element of it (with
//! template contents if it is a `template`), and no `template` element
//! without template contents has a child. Every DOM call of the rules
//! extends the document (`exec::frame::doc_extends`), and the parent of
//! every insertion may receive a child ([`doc::pok`]): the appropriate
//! place for inserting a node is computed from the rooted stack, whose
//! records are tagged by their names, so a parent that is a `template`
//! element is one by its record's tag, and the rules insert into its
//! template contents instead ([`doc::lemma_place_pok`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

pub mod adoption;
pub mod body;
pub mod body_tags;
pub mod cells;
pub mod doc;
pub mod early;
pub mod helpers;
pub mod lists;
pub mod rest;
pub mod run;
pub mod stop_body;
pub mod stop_early;
pub mod stop_frame;
pub mod stop_in_body;
pub mod stop_tables;
pub mod stopped;
pub mod tables;
pub mod walls;

/// Every name of the transcription and of this module, for the ghost
/// imports of the submodules (`use super::spec::*;`).
mod spec {
    #[cfg(verus_only)]
    pub use super::*;
    #[cfg(verus_only)]
    pub use crate::spec::*;
    #[cfg(verus_only)]
    pub use crate::termination::{
        formatting_ok, headish, is_end, is_start, modes_ok, rules_ok, template_count,
        template_mode_ok, templates_in,
    };
}

verus! {

/// A running parser's stack is rooted, the `html` element's id is fresh,
/// its records are tagged, no entry of the list of active formatting
/// elements is for a `template` start tag, the cells' ids are fresh
/// ([`cells_wf`]), in the "in cell" mode the stack holds a cell in table
/// scope, the root is the stack's only `html` element, and the document
/// facts [`doc::dinv`] hold.
pub open spec fn good(p: Parser) -> bool {
    &&& rooted_seq(p.open)
    &&& root_ids(p)
    &&& tags_wf(p)
    &&& crate::termination::formatting_ok(p)
    &&& cells_wf(p)
    &&& in_cell_ok(p)
    &&& doc::dinv(p)
    &&& html_once(p.open)
}

/// In the "in cell" mode, `q`'s stack holds a cell, its last cell `p`'s
/// last cell (the record).
pub open spec fn cell_kept(p: Parser, q: Parser) -> bool {
    p.mode == Mode::InCell && has_cell(p.open) ==> has_cell(q.open) && q.open[last_cell(q.open)] == p.open[last_cell(
        p.open,
    )]
}

/// A stopped or [`good`] parser.
pub open spec fn live(p: Parser) -> bool {
    p.stopped || good(p)
}

/// `q` comes from `p` by steps that keep [`good`], the `html` element, the
/// modes, the context and the stack of template insertion modes, grow the
/// document, add no `template` element to the stack and (in the "in cell"
/// mode) keep the last cell ([`cell_kept`]); or `q` has stopped. A stopped
/// parser stays stopped.
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
        &&& cell_kept(p, q)
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
/// [`reach_core`] and `modes_ok`, and its document or one that extends it
/// (`exec::frame::doc_extends`), has them.
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
        q.head == p.head,
        q.redirect == p.redirect,
        q.doc == p.doc || crate::exec::frame::doc_extends(p.doc, q.doc),
    ensures
        reach_core(q),
        crate::termination::modes_ok(q),
{
    if q.doc != p.doc {
        doc::lemma_dinv_doc(p, q.doc);
    }
}

/// A parser [`keeps`] made, put in a [`rooted_mode`] (one other than "in
/// cell" unless it has a cell), has [`reach_core`] and `modes_ok`.
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
        q.head == q1.head,
        q.redirect == q1.redirect,
        rooted_mode(q.mode),
        q.mode == Mode::InTemplate ==> q.template_modes.len() > 0,
        q.mode == Mode::InCell && q.mode != q1.mode ==> cell_scoped(q.open),
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
