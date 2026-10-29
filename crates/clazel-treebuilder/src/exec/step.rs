//! HTML §13.2.6 "the tree construction dispatcher", "reprocess the token"
//! and "using the rules for", over [`ParserBuf`] (`spec/base/dispatch.rs`):
//! the one-token step [`step`], proven equal to [`dispatch`], and the
//! parsers' initial states ([`new_parser_exec`], [`fragment_parser_exec`]).
//!
//! The reprocessing loop of [`run`] is [`run_exec`], a `while` loop whose
//! fuel is a ghost counter: `termination::theorem_dispatch_total` proves
//! `run` ends within `fuel_bound` applications, so the exec loop needs no
//! fuel of its own and is proven to return `run`'s result.
//!
//! What the step needs beyond [`parser_inv`]. The exec insertion modes
//! require that the stack of open elements is rooted at `html` (most modes;
//! `crate::invariant::rooted_needs`), at every rule application of the
//! run. That follows from the reachable-state invariant
//! [`crate::invariant::reachable_inv`] of the parser the step starts from:
//! `reachable::lemma_dispatch_reach` proves that it gives
//! [`dispatch_needs`] and that `dispatch` keeps it, so [`step`] requires and
//! ensures it, and [`new_parser_exec`] and [`fragment_parser_exec`] return
//! parsers satisfying it. That proof has one hypothesis not yet proven,
//! [`crate::invariant::cells_kept`] (the "in cell" mode always has a cell
//! on the stack), which [`step`] requires explicitly. Everything else the
//! modes require is proven here: `parser_inv` (their contracts keep it),
//! `!stopped` (the loop ends when parsing stops), the tags of the
//! reprocessed tokens ([`lemma_rules_tok`]), `termination::rules_ok` (from
//! `termination::lemma_rules_edges`), the mode of "text", and
//! `in_foreign_content` for the rules of foreign content (the dispatcher).

#[cfg(verus_only)]
use super::frame::*;
use super::insert::annotation_html_exec;
use super::modes::after_after_body::*;
use super::modes::after_after_frameset::*;
use super::modes::after_body::*;
use super::modes::after_frameset::*;
use super::modes::after_head::*;
use super::modes::before_head::*;
use super::modes::before_html::*;
use super::modes::foreign::*;
use super::modes::in_body::mode_in_body_exec;
use super::modes::in_caption::*;
use super::modes::in_cell::*;
use super::modes::in_column_group::*;
use super::modes::in_frameset::*;
use super::modes::in_head::*;
use super::modes::in_head_noscript::*;
use super::modes::in_row::*;
use super::modes::in_table::*;
use super::modes::in_table_body::*;
use super::modes::in_table_text::*;
use super::modes::in_template::*;
use super::modes::initial::mode_initial_exec;
use super::modes::text::*;
use super::names::{copy_tag, tag_of_exec};
#[allow(unused_imports)]
use super::spec::*;
use super::stack::*;
use super::types::*;
#[cfg(verus_only)]
use crate::exec::modes::initial::tok_ok;
#[cfg(verus_only)]
use crate::termination::helpers_in_body::image_as_img;
#[cfg(verus_only)]
use clazel_dom::exec::attrs_view;
use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The tokens the rules reprocess

/// The token a rule application reprocesses is the token it was given, or
/// for an `image` start tag, the `img` start tag "in body" makes of it.
pub open spec fn tok_next(t: Tok, t2: Tok) -> bool {
    t2 == t || (t is Start && t2 == image_as_img(t->Start_0))
}

/// [`tok_next`] of an outcome's token.
pub open spec fn outcome_tok_next(t: Tok, o: Outcome) -> bool {
    match o {
        Outcome::Done(_) => true,
        Outcome::Reprocess(_, t2) => tok_next(t, t2),
        Outcome::Using(_, _, t2) => tok_next(t, t2),
    }
}

/// "img" is the tag `img`.
pub proof fn lemma_tag_of_img()
    ensures
        tag_of(name_img()) == Tag::Img,
{
    assert(tag_of(seq![0x69u32, 0x6d, 0x67]) == Tag::Img) by (compute);
    assert(name_img() =~= seq![0x69u32, 0x6d, 0x67]);
}

/// A reprocessed token of a tagged token is tagged.
pub proof fn lemma_tok_next_ok(t: Tok, t2: Tok)
    requires
        tok_ok(t),
        tok_next(t, t2),
    ensures
        tok_ok(t2),
{
    if t2 != t {
        lemma_tag_of_img();
    }
}

/// The "in body" rules reprocess the token or `img`.
pub proof fn lemma_in_body_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_in_body(env, p, t)),
{
    hide(in_body_start_tag);
    hide(in_body_end_tag);
    hide(in_body_eof);
    hide(in_body_char);
    hide(insert_comment);
    hide(insert_pi);
    match t {
        Tok::Start(tt) => {
            crate::termination::helpers_in_body::lemma_in_body_start_tag_outcome(p, t, tt);
        },
        Tok::End(tt) => {
            crate::termination::helpers_in_body::lemma_in_body_end_tag_outcome(p, t, tt);
        },
        Tok::Eof => {
            crate::termination::helpers_in_body::lemma_in_body_eof_outcome(p, t);
        },
        _ => {},
    }
}

/// The "in head" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_in_head_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_in_head(env, p, t)),
{
    hide(insert_html_element);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_char);
    hide(pop);
    hide(pop_until_popped);
    hide(reset_insertion_mode);
    hide(push_marker);
    hide(clear_to_last_marker);
    hide(generic_text_parsing);
    hide(create_element_for_token);
    hide(insert_element_at);
    hide(push);
}

/// "In table"'s anything else reprocesses the token or `img`.
pub proof fn lemma_in_table_anything_else_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, in_table_anything_else(env, p, t)),
{
    let p1 = Parser { foster: true, ..p };
    lemma_in_body_tok(env, p1, t);
    match mode_in_body(env, p1, t) {
        Outcome::Using(Mode::InHead, q, t2) => {
            lemma_in_head_tok(env, q, t2);
        },
        _ => {},
    }
}

/// The "in table" rules reprocess the token or `img`.
#[verifier::spinoff_prover]
pub proof fn lemma_in_table_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_in_table(env, p, t)),
{
    hide(insert_html_element);
    hide(insert_comment);
    hide(insert_pi);
    hide(pop);
    hide(pop_until_popped);
    hide(reset_insertion_mode);
    hide(clear_stack_back_to_table_context);
    hide(push_marker);
    hide(has_in_scope);
    hide(mode_in_body);
    hide(mode_in_head);
    hide(pop_while);
    lemma_in_table_anything_else_tok(env, p, t);
}

/// The "initial" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_initial_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_initial(env, p, t)),
{
    hide(insert_comment);
    hide(insert_pi);
    hide(set_document_mode);
}

/// The "before html" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_before_html_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_before_html(env, p, t)),
{
    hide(insert_comment);
    hide(insert_pi);
    hide(create_element_for_token);
    hide(insert_element_at);
    hide(push);
}

/// The "before head" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_before_head_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_before_head(env, p, t)),
{
    hide(insert_html_element);
    hide(insert_comment);
    hide(insert_pi);
}

/// The "in head noscript" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_in_head_noscript_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_in_head_noscript(env, p, t)),
{
}

/// The "after head" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_after_head_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_after_head(env, p, t)),
{
    hide(insert_html_element);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_char);
    hide(push);
    hide(mode_in_head);
    hide(remove_open_at);
    if let Some(h) = p.head {
        lemma_in_head_tok(env, push(p, head_elem(h)), t);
    }
}

/// The "text" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_text_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_text(env, p, t)),
{
    hide(insert_char);
    hide(pop);
}

/// The "in table text" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_in_table_text_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_in_table_text(env, p, t)),
{
    hide(insert_characters);
    hide(in_table_anything_else);
    hide(reprocess_pending);
}

/// The "in caption" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_in_caption_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_in_caption(env, p, t)),
{
    hide(pop_until_popped);
    hide(has_in_scope);
    hide(generate_implied_end_tags);
    hide(clear_to_last_marker);
}

/// The "in column group" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_in_column_group_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_in_column_group(env, p, t)),
{
    hide(insert_html_element);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_char);
    hide(pop);
}

/// The "in table body" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_in_table_body_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_in_table_body(env, p, t)),
{
    hide(insert_html_element);
    hide(clear_stack_back_to_table_body_context);
    hide(pop_while);
}

/// The "in row" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_in_row_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_in_row(env, p, t)),
{
    hide(insert_html_element);
    hide(clear_stack_back_to_table_row_context);
    hide(push_marker);
    hide(has_in_scope);
    hide(pop_while);
}

/// The "in cell" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_in_cell_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_in_cell(env, p, t)),
{
    hide(pop);
    hide(pop_until_popped);
    hide(generate_implied_end_tags);
    hide(clear_to_last_marker);
    hide(close_the_cell);
    hide(pop_until_cell_popped);
}

/// The "in template" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_in_template_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_in_template(env, p, t)),
{
    hide(pop_until_popped);
    hide(reset_insertion_mode);
    hide(stop_parsing);
    hide(clear_to_last_marker);
}

/// The "after body" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_after_body_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_after_body(env, p, t)),
{
    hide(insert_comment);
    hide(insert_pi);
    hide(stop_parsing);
}

/// The "in frameset" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_in_frameset_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_in_frameset(env, p, t)),
{
    hide(insert_html_element);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_char);
    hide(pop);
    hide(stop_parsing);
}

/// The "after frameset" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_after_frameset_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_after_frameset(env, p, t)),
{
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_char);
    hide(stop_parsing);
}

/// The "after after body" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_after_after_body_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_after_after_body(env, p, t)),
{
    hide(insert_comment);
    hide(insert_pi);
    hide(stop_parsing);
}

/// The "after after frameset" rules reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_after_after_frameset_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, mode_after_after_frameset(env, p, t)),
{
    hide(insert_comment);
    hide(insert_pi);
    hide(stop_parsing);
}

/// The rules of foreign content reprocess the token.
#[verifier::spinoff_prover]
pub proof fn lemma_foreign_tok(env: EncFns, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, foreign_content(env, p, t)),
{
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_char);
    hide(pop);
    hide(pop_while);
    hide(insert_foreign_element);
    hide(foreign_end_tag_loop);
    if t is End {
        crate::termination::helpers_early::lemma_foreign_end_tag_loop(p, t, p.open.len() - 1);
    }
}

/// Every set of rules reprocesses the token, or `img` for `image`.
pub proof fn lemma_rules_tok(env: EncFns, r: Rules, p: Parser, t: Tok)
    ensures
        outcome_tok_next(t, apply_rules(env, r, p, t)),
{
    match r {
        Rules::Foreign => lemma_foreign_tok(env, p, t),
        Rules::Html(m) => match m {
            Mode::InBody => lemma_in_body_tok(env, p, t),
            Mode::InHead => lemma_in_head_tok(env, p, t),
            Mode::InTable => lemma_in_table_tok(env, p, t),
            Mode::Initial => lemma_initial_tok(env, p, t),
            Mode::BeforeHtml => lemma_before_html_tok(env, p, t),
            Mode::BeforeHead => lemma_before_head_tok(env, p, t),
            Mode::InHeadNoscript => lemma_in_head_noscript_tok(env, p, t),
            Mode::AfterHead => lemma_after_head_tok(env, p, t),
            Mode::Text => lemma_text_tok(env, p, t),
            Mode::InTableText => lemma_in_table_text_tok(env, p, t),
            Mode::InCaption => lemma_in_caption_tok(env, p, t),
            Mode::InColumnGroup => lemma_in_column_group_tok(env, p, t),
            Mode::InTableBody => lemma_in_table_body_tok(env, p, t),
            Mode::InRow => lemma_in_row_tok(env, p, t),
            Mode::InCell => lemma_in_cell_tok(env, p, t),
            Mode::InTemplate => lemma_in_template_tok(env, p, t),
            Mode::AfterBody => lemma_after_body_tok(env, p, t),
            Mode::InFrameset => lemma_in_frameset_tok(env, p, t),
            Mode::AfterFrameset => lemma_after_frameset_tok(env, p, t),
            Mode::AfterAfterBody => lemma_after_after_body_tok(env, p, t),
            Mode::AfterAfterFrameset => lemma_after_after_frameset_tok(env, p, t),
        },
    }
}

// ---------------------------------------------------------------------
// The rules

/// What [`mode_rules_exec`] and [`apply_rules_exec`] require of the parser
/// and the token: the invariant, a parser that has not stopped, a tagged
/// token, `termination::rules_ok`, the mode's own needs
/// ([`crate::invariant::rooted_needs`]), and for foreign content, a parser
/// in foreign content.
pub open spec fn rules_pre(r: Rules, p: Parser, t: Tok) -> bool {
    &&& parser_inv(p)
    &&& !p.stopped
    &&& tok_ok(t)
    &&& crate::termination::rules_ok(r, p)
    &&& rooted_needs(r, p)
    &&& r is Foreign ==> in_foreign_content(p)
}

/// The rules of insertion mode `m` ([`mode_rules`]).
pub fn mode_rules_exec<E: EncFnsExec>(env: &E, m: Mode, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        rules_pre(Rules::Html(m), old(p)@, t@),
    ensures
        outcome_view(o, final(p)@) == mode_rules(env.enc(), m, old(p)@, t@),
        parser_inv(final(p)@),
{
    match m {
        Mode::Initial => mode_initial_exec(env, p, t),
        Mode::BeforeHtml => mode_before_html_exec(env, p, t),
        Mode::BeforeHead => mode_before_head_exec(env, p, t),
        Mode::InHead => mode_in_head_exec(env, p, t),
        Mode::InHeadNoscript => mode_in_head_noscript_exec(env, p, t),
        Mode::AfterHead => mode_after_head_exec(env, p, t),
        Mode::InBody => mode_in_body_exec(env, p, t),
        Mode::Text => mode_text_exec(env, p, t),
        Mode::InTable => mode_in_table_exec(env, p, t),
        Mode::InTableText => mode_in_table_text_exec(env, p, t),
        Mode::InCaption => mode_in_caption_exec(env, p, t),
        Mode::InColumnGroup => mode_in_column_group_exec(env, p, t),
        Mode::InTableBody => mode_in_table_body_exec(env, p, t),
        Mode::InRow => mode_in_row_exec(env, p, t),
        Mode::InCell => mode_in_cell_exec(env, p, t),
        Mode::InTemplate => mode_in_template_exec(env, p, t),
        Mode::AfterBody => mode_after_body_exec(env, p, t),
        Mode::InFrameset => mode_in_frameset_exec(env, p, t),
        Mode::AfterFrameset => mode_after_frameset_exec(env, p, t),
        Mode::AfterAfterBody => mode_after_after_body_exec(env, p, t),
        Mode::AfterAfterFrameset => mode_after_after_frameset_exec(env, p, t),
    }
}

/// Apply a set of rules to the token ([`apply_rules`]).
pub fn apply_rules_exec<E: EncFnsExec>(env: &E, r: Rules, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        rules_pre(r, old(p)@, t@),
    ensures
        outcome_view(o, final(p)@) == apply_rules(env.enc(), r, old(p)@, t@),
        parser_inv(final(p)@),
{
    match r {
        Rules::Html(m) => mode_rules_exec(env, m, p, t),
        Rules::Foreign => foreign_content_exec(env, p, t),
    }
}

// ---------------------------------------------------------------------
// The dispatcher

/// §13.2.6 the tree construction dispatcher ([`dispatcher`]).
pub fn dispatcher_exec(p: &ParserBuf, t: &ExecTok) -> (r: Rules)
    ensures
        r == dispatcher(p@, t@),
{
    if p.open.is_empty() {
        // "If the stack of open elements is empty"
        return Rules::Html(copy_mode(&p.mode));
    }
    let a = adjusted_current_node_exec(p);
    let html = if matches!(a.ns, Namespace::Html) {
        // "If the adjusted current node is an element in the HTML namespace"
        true
    } else {
        let mtip = is_mathml_text_integration_point_exec(a);
        let hip = is_html_integration_point_exec(a);
        match t {
            // "If the adjusted current node is a MathML text integration
            // point and the token is a start tag whose tag name is neither
            // "mglyph" nor "malignmark"", "If the adjusted current node is a
            // MathML annotation-xml element and the token is a start tag whose
            // tag name is "svg"", "If the adjusted current node is an HTML
            // integration point and the token is a start tag"
            ExecTok::Start(tt) => (mtip && !matches!(tt.tag, Tag::Mglyph | Tag::Malignmark)) || (matches!(a.ns, Namespace::MathMl)
                && matches!(a.tag, Tag::AnnotationXml) && matches!(tt.tag, Tag::Svg)) || hip,
            // "If the adjusted current node is a MathML text integration
            // point and the token is a character token", "If the adjusted
            // current node is an HTML integration point and the token is a
            // character token"
            ExecTok::Char(_) => mtip || hip,
            // "If the token is an end-of-file token"
            ExecTok::Eof => true,
            _ => false,
        }
    };
    if html {
        // "Process the token according to the rules given in the section
        // corresponding to the current insertion mode in HTML content."
        Rules::Html(copy_mode(&p.mode))
    } else {
        // "Otherwise: Process the token according to the rules given in
        // the section for parsing tokens in foreign content."
        Rules::Foreign
    }
}

// ---------------------------------------------------------------------
// The reprocessing loop

/// What the reprocessing loop continues with after one rule application
/// `o` of `r` to `(p, t)`: if the token is handled or parsing stopped, the
/// run's result is the outcome's parser; otherwise the next application
/// meets [`rules_pre`] and [`run_needs`] and has the same run.
pub open spec fn run_next(env: EncFns, o: Outcome, f: nat, target: Option<Parser>) -> bool {
    match o {
        Outcome::Done(q) => target == Some(q),
        Outcome::Reprocess(q, t2) => if q.stopped {
            target == Some(q)
        } else {
            &&& rules_pre(Rules::Html(q.mode), q, t2)
            &&& run_needs(env, q, t2, Rules::Html(q.mode), (f - 1) as nat)
            &&& run(env, q, t2, Rules::Html(q.mode), (f - 1) as nat) == target
        },
        Outcome::Using(m, q, t2) => if q.stopped {
            target == Some(q)
        } else {
            &&& rules_pre(Rules::Html(m), q, t2)
            &&& run_needs(env, q, t2, Rules::Html(m), (f - 1) as nat)
            &&& run(env, q, t2, Rules::Html(m), (f - 1) as nat) == target
        },
    }
}

/// The parser of an outcome.
pub open spec fn outcome_q(o: Outcome) -> Parser {
    match o {
        Outcome::Done(q) => q,
        Outcome::Reprocess(q, _) => q,
        Outcome::Using(_, q, _) => q,
    }
}

/// `parser_inv` gives `termination::modes_ok`.
pub proof fn lemma_inv_modes_ok(p: Parser)
    requires
        parser_inv(p),
    ensures
        crate::termination::modes_ok(p),
{
}

/// One step of the loop of [`run`]: the edge lemmas give the next rules'
/// `rules_ok`, [`lemma_rules_tok`] the next token's tags, and the run's
/// definition the rest.
pub proof fn lemma_run_next(env: EncFns, r: Rules, p: Parser, t: Tok, f: nat, target: Option<Parser>)
    requires
        rules_pre(r, p, t),
        run_needs(env, p, t, r, f),
        run(env, p, t, r, f) == target,
        target is Some,
        parser_inv(outcome_q(apply_rules(env, r, p, t))),
    ensures
        f > 0,
        run_next(env, apply_rules(env, r, p, t), f, target),
{
    hide(apply_rules);
    hide(parser_inv);
    let o = apply_rules(env, r, p, t);
    assert(f > 0);
    lemma_inv_modes_ok(p);
    crate::termination::lemma_rules_edges(env, r, p, t);
    lemma_rules_tok(env, r, p, t);
    match o {
        Outcome::Done(q) => {},
        Outcome::Reprocess(q, t2) => {
            if !q.stopped {
                let r2 = Rules::Html(q.mode);
                lemma_tok_next_ok(t, t2);
                assert(run(env, q, t2, r2, (f - 1) as nat) == target);
                assert((f - 1) as nat > 0);
                assert(run_needs(env, q, t2, r2, (f - 1) as nat));
                assert(rooted_needs(r2, q));
                assert(crate::termination::rules_ok(r2, q));
                assert(rules_pre(r2, q, t2));
            }
        },
        Outcome::Using(m, q, t2) => {
            if !q.stopped {
                let r2 = Rules::Html(m);
                lemma_tok_next_ok(t, t2);
                assert(run(env, q, t2, r2, (f - 1) as nat) == target);
                assert((f - 1) as nat > 0);
                assert(run_needs(env, q, t2, r2, (f - 1) as nat));
                assert(rooted_needs(r2, q));
                assert(crate::termination::rules_ok(r2, q));
                assert(rules_pre(r2, q, t2));
            }
        },
    }
}

/// [`run`]: apply rules until the token is handled. The fuel is ghost: the
/// loop runs while the spec's run has fuel, which `run(...) is Some`
/// guarantees.
pub fn run_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, t: ExecTok, r: Rules, Ghost(fuel): Ghost<nat>)
    requires
        rules_pre(r, old(p)@, t@),
        run_needs(env.enc(), old(p)@, t@, r, fuel),
        run(env.enc(), old(p)@, t@, r, fuel) is Some,
    ensures
        run(env.enc(), old(p)@, t@, r, fuel) == Some(final(p)@),
        parser_inv(final(p)@),
{
    hide(apply_rules);
    hide(run);
    hide(run_needs);
    hide(rules_pre);
    let ghost target = run(env.enc(), p@, t@, r, fuel);
    let ghost mut f: nat = fuel;
    let mut t = t;
    let mut r = r;
    let mut done = false;
    proof {
        reveal(rules_pre);
    }
    while !done
        invariant
            target is Some,
            parser_inv(p@),
            done ==> target == Some(p@),
            !done ==> rules_pre(r, p@, t@) && run_needs(env.enc(), p@, t@, r, f) && run(env.enc(), p@, t@, r, f) == target,
        decreases f + if done {
            0nat
        } else {
            1nat
        },
    {
        let ghost (p0, t0, r0, f0) = (p@, t@, r, f);
        let cur = t;
        t = ExecTok::Eof;
        let rules = r;
        r = Rules::Foreign;
        proof {
            reveal(rules_pre);
        }
        let o = apply_rules_exec(env, rules, p, cur);
        proof {
            assert(outcome_q(outcome_view(o, p@)) == p@);
            lemma_run_next(env.enc(), r0, p0, t0, f0, target);
        }
        match o {
            ExecOutcome::Done => {
                done = true;
            },
            ExecOutcome::Reprocess(t2) => {
                if p.stopped {
                    done = true;
                } else {
                    proof {
                        f = (f0 - 1) as nat;
                    }
                    r = Rules::Html(copy_mode(&p.mode));
                    t = t2;
                }
            },
            ExecOutcome::Using(m, t2) => {
                if p.stopped {
                    done = true;
                } else {
                    proof {
                        f = (f0 - 1) as nat;
                    }
                    r = Rules::Html(m);
                    t = t2;
                }
            },
        }
    }
}

// ---------------------------------------------------------------------
// The step

/// A copy of an action.
fn copy_action(a: &ExecAction) -> (r: ExecAction)
    ensures
        r@ == a@,
{
    match a {
        ExecAction::ChangeEncoding(e) => ExecAction::ChangeEncoding(*e),
        ExecAction::ScriptReady(n) => ExecAction::ScriptReady(*n),
        ExecAction::StopParsing => ExecAction::StopParsing,
    }
}

/// A copy of a list of actions.
fn copy_actions(s: &[ExecAction]) -> (r: Vec<ExecAction>)
    ensures
        actions_view(r@) == actions_view(s@),
{
    let mut out: Vec<ExecAction> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> (#[trigger] out@[j])@ == s@[j]@,
        decreases s.len() - i,
    {
        if let Some(a) = s.get(i) {
            out.push(copy_action(a));
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(actions_view(out@) =~= actions_view(s@));
    }
    out
}

/// `parser_inv` reads none of the step's bookkeeping fields.
proof fn lemma_inv_bookkeeping(p: Parser, q: Parser)
    requires
        parser_inv(p),
        q == (Parser { actions: q.actions, tokenizer: q.tokenizer, skip_lf: q.skip_lf, ..p }),
    ensures
        parser_inv(q),
{
    crate::exec::frame::lemma_inv_iff(p);
    crate::exec::frame::lemma_inv_iff(q);
}

/// The one-token step (Phase 4 item 4.9's contract
/// `contract::step_ensures`, [`dispatch`]): the new state and the actions
/// for the driver, in order. The state's `tokenizer` field is the
/// tokenizer state switch the step asks for, if any.
///
/// Requires, beyond `contract::step_requires` (`parser_wf`), the rest of
/// [`parser_inv`] and the reachable-state invariant
/// [`crate::invariant::reachable_inv`], both of which it keeps (so every
/// parser [`new_parser_exec`] or [`fragment_parser_exec`] returns can be
/// stepped any number of times), and the hypothesis
/// [`crate::invariant::cells_kept`] (a closed statement about the spec's
/// rules, not yet proven; see the module comment).
pub fn step<E: EncFnsExec>(p: &mut ParserBuf, env: &E, token: ExecToken) -> (actions: Vec<ExecAction>)
    requires
        parser_inv(old(p)@),
        reachable_inv(old(p)@),
        cells_kept(),
    ensures
        (final(p)@, actions_view(actions@)) == dispatch(env.enc(), old(p)@, token@),
        parser_inv(final(p)@),
        reachable_inv(final(p)@),
{
    proof {
        crate::reachable::run::lemma_dispatch_reach(env.enc(), p@, token@);
    }
    let ghost p_in = p@;
    p.actions = Vec::new();
    p.tokenizer = None;
    proof {
        assert(actions_view(p.actions@) =~= Seq::<Action>::empty());
        lemma_inv_bookkeeping(p_in, p@);
    }
    if p.stopped {
        return Vec::new();
    }
    if p.skip_lf {
        // "If the next token is a U+000A LINE FEED (LF) character token,
        // then ignore that token and move on to the next one."
        p.skip_lf = false;
        proof {
            lemma_inv_bookkeeping(p_in, p@);
        }
        let is_lf = match &token {
            ExecToken::Character { c } => *c == 0x0A,
            _ => false,
        };
        if is_lf {
            return Vec::new();
        }
    }
    let ghost p1 = p@;
    proof {
        assert(p1 == Parser { skip_lf: false, actions: seq![], tokenizer: None, ..p_in });
    }
    let t = classify_exec(token);
    proof {
        crate::termination::theorem_dispatch_total(env.enc(), p1, t@);
        crate::termination::lemma_dispatcher_rules_ok(p1, t@);
    }
    let r = dispatcher_exec(p, &t);
    run_exec(env, p, t, r, Ghost(fuel_bound(p1)));
    copy_actions(p.actions.as_slice())
}

// ---------------------------------------------------------------------
// The parsers' initial states

/// Setting a new document's mode extends it.
pub proof fn lemma_new_doc_extends(url: Seq<u32>, mode: DocumentMode)
    ensures
        doc_extends(dom::new_document(url), dom::set_mode(dom::new_document(url), mode)),
        dom::wf(dom::new_document(url)),
{
    clazel_dom::lemmas::theorem_new_document_wf(url);
    clazel_dom::lemmas::theorem_set_mode_wf(dom::new_document(url), mode);
}

/// A document extending a new document has no template element with a
/// child that lacks template contents ([`templates_wf`]'s second part).
pub proof fn lemma_templates_from_new(url: Seq<u32>, d: Document)
    requires
        doc_extends(dom::new_document(url), d),
    ensures
        forall|n: NodeId|
            dom::valid(d, n) && #[trigger] node_is_template(d, n) && d.nodes[n as int].children.len() > 0 ==> has_template_contents(d, n),
{
    assert forall|n: NodeId|
        dom::valid(d, n) && #[trigger] node_is_template(d, n) && d.nodes[n as int].children.len() > 0 implies has_template_contents(d, n) by {
        if !has_template_contents(d, n) {
            assert(n < dom::new_document(url).nodes.len() && dom::new_document(url).nodes[n as int].children.len() > 0);
        }
    }
}

/// [`new_parser`]: a new parser for a new document with the given URL.
pub fn new_parser_exec(url: Vec<u32>, scripting: bool, tentative: bool) -> (p: ParserBuf)
    ensures
        p@ == new_parser(url@, scripting, tentative),
        parser_inv(p@),
        reachable_inv(p@),
{
    let ghost u = url@;
    let arena = Arena::new(url);
    let p = ParserBuf {
        arena,
        mode: Mode::Initial,
        original_mode: Mode::Initial,
        template_modes: Vec::new(),
        open: Vec::new(),
        formatting: Vec::new(),
        head: None,
        form: None,
        context: None,
        scripting,
        frameset_ok: true,
        foster: false,
        pending_table_text: Vec::new(),
        skip_lf: false,
        tokenizer: None,
        tentative,
        redirect: None,
        stopped: false,
        actions: Vec::new(),
    };
    proof {
        crate::reachable::run::lemma_new_parser_reach(u, scripting, tentative);
        clazel_dom::lemmas::theorem_new_document_wf(u);
        assert(elems_view(p.open@) =~= Seq::<Elem>::empty());
        assert(fmts_view(p.formatting@) =~= Seq::<Fmt>::empty());
        assert(actions_view(p.actions@) =~= Seq::<Action>::empty());
        assert(p.template_modes@ =~= Seq::<Mode>::empty());
        assert(p.pending_table_text@ =~= Seq::<u32>::empty());
        assert(p@ == new_parser(u, scripting, tentative));
        assert(crate::termination::templates_in(p@.open, 0) == 0);
        assert forall|n: NodeId|
            dom::valid(p@.doc, n) && #[trigger] node_is_template(p@.doc, n) && p@.doc.nodes[n as int].children.len() > 0 implies has_template_contents(
            p@.doc,
            n,
        ) by {
            assert(n == 0);
        }
    }
    p
}

/// The fragment parsing algorithm's context element ([`Context`]).
pub struct ExecContext {
    /// The context element's namespace.
    pub ns: Namespace,
    /// Its local name.
    pub name: Vec<u32>,
    /// Its attributes.
    pub attrs: Vec<ExecAttr>,
    /// Its node document's mode.
    pub mode: DocumentMode,
}

impl View for ExecContext {
    type V = Context;

    open spec fn view(&self) -> Context {
        Context { ns: self.ns, name: self.name@, attrs: attrs_view(self.attrs@), mode: self.mode }
    }
}

/// "html"
fn name_html_exec() -> (r: Vec<u32>)
    ensures
        r@ == seq![0x68u32, 0x74, 0x6d, 0x6c],
{
    let l: &[u32] = &[0x68u32, 0x74u32, 0x6du32, 0x6cu32];
    proof {
        assert(l@ =~= seq![0x68u32, 0x74, 0x6d, 0x6c]);
    }
    copy_str(l)
}

/// "html" is the tag `html`.
pub proof fn lemma_tag_of_html()
    ensures
        tag_of(seq![0x68u32, 0x74, 0x6d, 0x6c]) == Tag::Html,
{
    assert(tag_of(seq![0x68u32, 0x74, 0x6d, 0x6c]) == Tag::Html) by (compute);
}

/// §13.4 step 10: the tokenizer state for the context element.
fn fragment_tokenizer_state(ns: &Namespace, tag: &Tag, scripting: bool) -> (r: Option<TokenizerState>)
    ensures
        r == (if *ns != Namespace::Html {
            None
        } else {
            match *tag {
                Tag::Title | Tag::Textarea => Some(TokenizerState::Rcdata),
                Tag::Style | Tag::Xmp | Tag::Iframe | Tag::Noembed | Tag::Noframes => Some(TokenizerState::Rawtext),
                Tag::Script => Some(TokenizerState::ScriptData),
                Tag::Noscript => if scripting {
                    Some(TokenizerState::Rawtext)
                } else {
                    None
                },
                Tag::Plaintext => Some(TokenizerState::Plaintext),
                _ => None,
            }
        }),
{
    if !matches!(ns, Namespace::Html) {
        return None;
    }
    match tag {
        Tag::Title | Tag::Textarea => Some(TokenizerState::Rcdata),
        Tag::Style | Tag::Xmp | Tag::Iframe | Tag::Noembed | Tag::Noframes => Some(TokenizerState::Rawtext),
        Tag::Script => Some(TokenizerState::ScriptData),
        Tag::Noscript => if scripting {
            Some(TokenizerState::Rawtext)
        } else {
            None
        },
        Tag::Plaintext => Some(TokenizerState::Plaintext),
        _ => None,
    }
}

/// The element kind of the context element as [`fragment_parser`] creates
/// it.
pub open spec fn context_kind(ctx: Context) -> NodeKind {
    NodeKind::Element {
        namespace: Some(ctx.ns),
        prefix: None,
        local_name: ctx.name,
        attributes: ctx.attrs,
        template_contents: None,
        form_owner: None,
    }
}

/// The element kind of the fragment's root `html` element.
pub open spec fn root_kind() -> NodeKind {
    NodeKind::Element {
        namespace: Some(Namespace::Html),
        prefix: None,
        local_name: seq![0x68u32, 0x74, 0x6d, 0x6c],
        attributes: seq![],
        template_contents: None,
        form_owner: None,
    }
}

/// The fragment parser's arena ([`fragment_parser`] steps 4 to 7, 11, 12
/// and 14): the document, the context element, root and the fragment.
pub open spec fn fragment_doc(ctx: Context) -> (Document, NodeId, NodeId, NodeId) {
    let d0 = dom::set_mode(dom::new_document(seq![]), ctx.mode);
    let (d1, ctx_id) = dom::create_node(d0, context_kind(ctx));
    let (d2, root) = dom::create_node(d1, root_kind());
    let d3 = dom::append(d2, 0, root);
    let (d4, fragment) = dom::create_node(d3, NodeKind::DocumentFragment { host: None });
    (d4, ctx_id, root, fragment)
}

/// What [`fragment_parser_exec`] needs of [`fragment_doc`]: a well-formed
/// arena holding the context element, root and the fragment, with no
/// template element with a child lacking template contents.
pub open spec fn fragment_doc_ok(ctx: Context, d: Document, ctx_id: NodeId, root: NodeId, fragment: NodeId) -> bool {
    &&& dom::wf(d)
    &&& dom::valid(d, ctx_id)
    &&& kind_kept(context_kind(ctx), d.nodes[ctx_id as int].kind)
    &&& dom::valid(d, root)
    &&& kind_kept(root_kind(), d.nodes[root as int].kind)
    &&& dom::valid(d, fragment)
    &&& d.nodes[fragment as int].kind is DocumentFragment
    &&& forall|n: NodeId|
        dom::valid(d, n) && #[trigger] node_is_template(d, n) && d.nodes[n as int].children.len() > 0 ==> has_template_contents(d, n)
}

/// §13.4 steps 4 to 7, 11, 12 and 14: the fragment parser's arena
/// ([`fragment_doc`]).
fn fragment_doc_exec(ns: &Namespace, name: Vec<u32>, attrs: Vec<ExecAttr>, mode: DocumentMode) -> (r: (Arena, usize, usize, usize))
    ensures
        ({
            let cv = Context { ns: *ns, name: name@, attrs: attrs_view(attrs@), mode };
            &&& (r.0@, r.1, r.2, r.3) == fragment_doc(cv)
            &&& fragment_doc_ok(cv, r.0@, r.1, r.2, r.3)
        }),
{
    hide(dom::insert);
    hide(dom::wf);
    hide(tag_of);
    let ghost cv = Context { ns: *ns, name: name@, attrs: attrs_view(attrs@), mode };
    // 4. "Let document be a Document node whose type is "html"." 5. to 7.:
    // its mode is the context document's.
    let mut arena = Arena::new(Vec::new());
    let ghost dn = arena@;
    proof {
        assert(dn == dom::new_document(seq![]));
        lemma_new_doc_extends(seq![], mode);
        clazel_dom::lemmas::theorem_set_mode_wf(dn, mode);
    }
    arena.set_mode(mode);
    let ghost d0 = arena@;
    // The context element, in the same arena with no parent.
    proof {
        assert(d0.nodes.len() == 1);
        lemma_create_extends(d0, context_kind(cv));
    }
    let ctx_id = match arena.create(
        ExecKind::Element {
            namespace: Some(copy_ns(ns)),
            prefix: None,
            local_name: name,
            attributes: attrs,
            template_contents: None,
            form_owner: None,
        },
    ) {
        Some(i) => i,
        None => vstd::pervasive::unreached(),
    };
    let ghost d1 = arena@;
    // 11. "Let root be the result of creating an element given document,
    // "html", the HTML namespace, …"
    proof {
        lemma_create_extends(d1, root_kind());
    }
    let root_attrs: Vec<ExecAttr> = Vec::new();
    proof {
        assert(attrs_view(root_attrs@) =~= Seq::<Attr>::empty());
    }
    let root = match arena.create(
        ExecKind::Element {
            namespace: Some(Namespace::Html),
            prefix: None,
            local_name: name_html_exec(),
            attributes: root_attrs,
            template_contents: None,
            form_owner: None,
        },
    ) {
        Some(i) => i,
        None => vstd::pervasive::unreached(),
    };
    let ghost d2 = arena@;
    // 12. "Append root to document."
    proof {
        assert(ctx_id == 1 && root == 2 && d2.nodes.len() == 3);
        assert(d2.nodes[0] == d0.nodes[0]);
        assert(d2.nodes[root as int].kind == root_kind());
        assert(!dom::is_inclusive_ancestor(d2, root, 0)) by {
            assert(d2.nodes[0].parent is None);
        }
        lemma_insert_extends(d2, root, 0, None);
        clazel_dom::lemmas::theorem_append_wf(d2, 0, root);
    }
    arena.append(0, root);
    let ghost d3 = arena@;
    // 14. "Let fragment be the result of creating a document fragment …"
    proof {
        assert(d3.nodes.len() == 3);
        lemma_create_extends(d3, NodeKind::DocumentFragment { host: None });
    }
    let fragment = match arena.create(ExecKind::DocumentFragment { host: None }) {
        Some(i) => i,
        None => vstd::pervasive::unreached(),
    };
    let ghost d4 = arena@;
    proof {
        lemma_doc_extends_trans(dn, d0, d1);
        lemma_doc_extends_trans(dn, d1, d2);
        lemma_doc_extends_trans(dn, d2, d3);
        lemma_doc_extends_trans(dn, d3, d4);
        lemma_doc_extends_trans(d1, d2, d3);
        lemma_doc_extends_trans(d1, d3, d4);
        lemma_doc_extends_trans(d2, d3, d4);
        lemma_templates_from_new(seq![], d4);
        assert(kind_kept(d1.nodes[ctx_id as int].kind, d4.nodes[ctx_id as int].kind));
        assert(kind_kept(d2.nodes[root as int].kind, d4.nodes[root as int].kind));
    }
    (arena, ctx_id, root, fragment)
}

/// The record of the fragment's root `html` element.
pub open spec fn root_elem(root: NodeId) -> Elem {
    Elem { id: root, ns: Namespace::Html, tag: Tag::Html, name: seq![0x68u32, 0x74, 0x6d, 0x6c], annotation_html: false }
}

/// The fragment parser's state before "reset the insertion mode
/// appropriately" satisfies [`parser_inv`].
pub proof fn lemma_fragment_start_inv(ctx: Context, p: Parser, ctx_id: NodeId, root: NodeId, fragment: NodeId)
    requires
        fragment_doc_ok(ctx, p.doc, ctx_id, root, fragment),
        p.open == seq![root_elem(root)],
        p.formatting.len() == 0,
        p.context is Some,
        p.context->Some_0.id == ctx_id,
        p.context->Some_0.ns == ctx.ns,
        p.context->Some_0.name == ctx.name,
        p.context->Some_0.tag == tag_of(ctx.name),
        p.template_modes == (if is_html(p.context->Some_0, Tag::Template) {
            seq![Mode::InTemplate]
        } else {
            Seq::<Mode>::empty()
        }),
        p.head is None,
        p.form is None,
        p.redirect == Some((root, fragment)),
        p.mode == Mode::Initial,
        p.original_mode == Mode::Initial,
    ensures
        parser_inv(p),
{
    lemma_tag_of_html();
    assert(crate::termination::templates_in(p.open, 1) == 0) by {
        assert(crate::termination::templates_in(p.open, 0) == 0);
    }
    lemma_inv_iff(p);
    assert(elem_ok(p.doc, p.open[0]));
    assert(open_ok(p.doc, p.open));
    assert(fmts_ok(p.doc, p.formatting));
    assert(rest_ok(p));
}

/// Setting the form element pointer to a node of the document keeps
/// [`parser_inv`].
pub proof fn lemma_inv_form(p: Parser, id: NodeId)
    requires
        parser_inv(p),
        dom::valid(p.doc, id),
    ensures
        parser_inv(Parser { form: Some(id), ..p }),
{
    lemma_inv_iff(p);
    lemma_inv_iff(Parser { form: Some(id), ..p });
}

/// §13.4 the HTML fragment parsing algorithm, steps 1 to 19
/// ([`fragment_parser`]): the parser before its first token, the
/// fragment's id (step 23 returns its children), and the tokenizer state
/// of step 10 (`None`: the data state).
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
pub fn fragment_parser_exec(ctx: ExecContext, scripting: bool) -> (r: (ParserBuf, usize, Option<TokenizerState>))
    ensures
        (r.0@, r.1, r.2) == fragment_parser(ctx@, scripting),
        parser_inv(r.0@),
        reachable_inv(r.0@),
{
    hide(reset_from);
    hide(dom::insert);
    hide(dom::wf);
    hide(annotation_html);
    hide(tag_of);
    hide(parser_inv);
    let ghost cv = ctx@;
    proof {
        crate::reachable::run::lemma_fragment_parser_reach(cv, scripting);
    }
    let ns = ctx.ns;
    let name = ctx.name;
    let attrs = ctx.attrs;
    let mode = ctx.mode;
    // 17. "Create a start tag token whose name is the local name of context
    // and whose attributes are the attributes of context."
    let tag = tag_of_exec(name.as_slice());
    let ctx_tok = ExecTagTok {
        name: copy_str(name.as_slice()),
        tag: copy_tag(&tag),
        attrs: copy_attrs(attrs.as_slice()),
        self_closing: false,
    };
    let ann = annotation_html_exec(&ns, &ctx_tok);
    let ctx_name = copy_str(name.as_slice());
    let (arena, ctx_id, root, fragment) = fragment_doc_exec(&ns, name, attrs, mode);
    let ghost d4 = arena@;
    let is_template = matches!(ns, Namespace::Html) && matches!(tag, Tag::Template);
    let is_form = matches!(ns, Namespace::Html) && matches!(tag, Tag::Form);
    // 10. The tokenizer state.
    let st = fragment_tokenizer_state(&ns, &tag, scripting);
    let ctx_el = ExecElem { id: ctx_id, ns, tag, name: ctx_name, annotation_html: ann };
    // 16. "If context is a template element, then push "in template" onto
    // the stack of template insertion modes …"
    let mut template_modes: Vec<Mode> = Vec::new();
    if is_template {
        template_modes.push(Mode::InTemplate);
    }
    // 13. "Set up the HTML parser's stack of open elements so that it
    // contains just the single element root."
    let root_el = ExecElem { id: root, ns: Namespace::Html, tag: Tag::Html, name: name_html_exec(), annotation_html: false };
    let open: Vec<ExecElem> = vec![root_el];
    // 9. A new HTML parser with the scripting mode and the fragment context
    // element; 15. the insertion target redirection map; 20. the encoding
    // confidence is irrelevant.
    let mut p = ParserBuf {
        arena,
        mode: Mode::Initial,
        original_mode: Mode::Initial,
        template_modes,
        open,
        formatting: Vec::new(),
        head: None,
        form: None,
        context: Some(ctx_el),
        scripting,
        frameset_ok: true,
        foster: false,
        pending_table_text: Vec::new(),
        skip_lf: false,
        tokenizer: None,
        tentative: false,
        redirect: Some((root, fragment)),
        stopped: false,
        actions: Vec::new(),
    };
    let ghost p1 = p@;
    proof {
        assert(elems_view(p.open@) =~= seq![root_elem(root)]);
        assert(fmts_view(p.formatting@) =~= Seq::<Fmt>::empty());
        assert(actions_view(p.actions@) =~= Seq::<Action>::empty());
        assert(p.pending_table_text@ =~= Seq::<u32>::empty());
        if is_template {
            assert(p.template_modes@ =~= seq![Mode::InTemplate]);
        } else {
            assert(p.template_modes@ =~= Seq::<Mode>::empty());
        }
        lemma_fragment_start_inv(cv, p1, ctx_id, root, fragment);
    }
    // 18. "Reset the parser's insertion mode appropriately."
    reset_insertion_mode_exec(&mut p);
    // 19. The form element pointer: the context element itself if it is a
    // form (it has no ancestors here).
    if is_form {
        let ghost q = p@;
        p.form = Some(ctx_id);
        proof {
            lemma_inv_form(q, ctx_id);
        }
    }
    (p, fragment, st)
}

} // verus!
