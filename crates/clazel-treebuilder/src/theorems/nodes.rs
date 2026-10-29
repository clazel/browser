//! `theorem_nodes_per_token` (Phase 4 item 4.9): how many nodes one
//! `dispatch` step creates.
//!
//! The bound. With T the length of the stack of template insertion modes,
//! F that of the list of active formatting elements and P the number of
//! pending table character tokens, one step creates at most
//! `44 + 6 T + 2 F + P (F + 1)` nodes. The plan's "1 + F" is too small:
//! - handling a token ("Done") creates at most `33 + 2 F`: the adoption
//!   agency creates at most 32 (eight outer rounds, each with at most three
//!   new elements in the inner loop, whose counter passes 3 after three
//!   rounds, and one in step 4.22), and "in body"'s `nobr` start tag
//!   reconstructs the active formatting elements (F new elements) both
//!   before and after it, then inserts one (so `<nobr><b><i></p><nobr>`
//!   creates 2 F); a `template` element is two nodes (its contents);
//! - before that, the token can create the implicit elements a
//!   reprocessing edge inserts (`html`, `head`, `body`, `colgroup`,
//!   `tbody`, `tr`): each lowers `termination::growth` (at most 5), and
//!   the growth budget is reset only when the stack of template insertion
//!   modes or the `image` token shrinks, so at most `5 + 6 T + 6` of them.
//!   The T term is needed under these hypotheses: in a `parser_wf` state
//!   whose stack holds `html, template, head, template, head, template` in
//!   "in template", one end-of-file token creates a `body` element per
//!   template ("in head" pops the `head`, "after head" inserts `body`, "in
//!   body" sends the token back to "in template"); whether reachable states
//!   need it is not shown;
//! - "in table text"'s anything else reprocesses each of the P pending
//!   characters with the "in body" rules: a reconstruction (F elements)
//!   and a `Text` node each (the characters are not shown to merge).
//!
//! The proof is [`super::open_elements`]'s: every rule application
//! satisfies `open_elements::app_ok`, and along the run the new nodes plus
//! the budget `open_elements::pot` never increase
//! (`open_elements::lemma_edge_pot`, from the ranking edges of
//! `termination`).
//!
//! The hypotheses: those of `theorem_open_elements_in_doc`, and that no two
//! entries of the list of active formatting elements are for the same
//! element (`open_elements::fmt_unique`, which the step keeps): with two
//! entries for one element the adoption agency's inner loop can clone it
//! past its third round, and its count would grow with the stack.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// **Nodes per token** (Phase 4 item 4.9): for a parser satisfying
/// `parser_wf`, the head element pointer's fact (`invariant::head_ok`) and
/// [`super::open_elements::fmt_unique`], and a token whose step meets
/// `invariant::dispatch_needs`, the step creates at most
/// `44 + 6 T + 2 F + P (F + 1)` nodes (see the module comment), and the
/// new state keeps `fmt_unique`.
pub proof fn theorem_nodes_per_token(env: EncFns, p: Parser, token: Token)
    requires
        parser_wf(p),
        p.stopped || head_ok(p),
        super::open_elements::fmt_unique(p),
        dispatch_needs(env, p, token),
    ensures
        dispatch(env, p, token).0.doc.nodes.len() <= p.doc.nodes.len() + 44 + 6 * p.template_modes.len() + 2
            * p.formatting.len() + p.pending_table_text.len() * (p.formatting.len() + 1),
        super::open_elements::fmt_unique(dispatch(env, p, token).0),
{
    super::open_elements::lemma_dispatch(env, p, token);
    super::open_elements::lemma_kpu(p, dispatch(env, p, token).0);
}

} // verus!
