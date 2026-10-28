//! The edges of the "initial", "before html", "before head", "in head", "in head noscript", "after head", "text" modes are ranked
//! (see [`super`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The edges of the "initial" mode are ranked.
pub proof fn lemma_initial_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::Initial), p),
    ensures
        edge_ok(Rules::Html(Mode::Initial), p, t, mode_initial(env, p, t)),
{
}

/// The edges of the "before html" mode are ranked.
pub proof fn lemma_before_html_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::BeforeHtml), p),
    ensures
        edge_ok(Rules::Html(Mode::BeforeHtml), p, t, mode_before_html(env, p, t)),
{
}

/// The edges of the "before head" mode are ranked.
pub proof fn lemma_before_head_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::BeforeHead), p),
    ensures
        edge_ok(Rules::Html(Mode::BeforeHead), p, t, mode_before_head(env, p, t)),
{
}

/// The edges of the "in head" mode are ranked.
pub proof fn lemma_in_head_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InHead), p),
    ensures
        edge_ok(Rules::Html(Mode::InHead), p, t, mode_in_head(env, p, t)),
{
    let o = mode_in_head(env, p, t);
    if headish(t) || t is Doctype || is_start(t, Tag::Html) {
        assert(o is Done || o == Outcome::Using(Mode::InBody, p, t));
    } else if o is Reprocess {
        // "Anything else": pop the current node, switch to "after head" and
        // reprocess (same growth, the stack shortens by one).
        assert(o == in_head_anything_else(p, t));
        if p.open.len() > 0 {
            helpers_early::lemma_pop_nonempty(p);
        }
    }
    // Proven for every parser that has stopped or has a non-empty stack. The
    // remaining case, a running parser with an empty stack, is not proven:
    // `pop` of an empty stack has no known length (`Seq::drop_last` of an
    // empty sequence), so neither `L` nor the budget can be bounded; it needs
    // an invariant that the stack is non-empty here.
    if p.stopped || p.open.len() > 0 {
        assert(edge_ok(Rules::Html(Mode::InHead), p, t, o));
    }
}

/// The edges of the "in head noscript" mode are ranked.
pub proof fn lemma_in_head_noscript_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InHeadNoscript), p),
    ensures
        edge_ok(Rules::Html(Mode::InHeadNoscript), p, t, mode_in_head_noscript(env, p, t)),
{
    let o = mode_in_head_noscript(env, p, t);
    if o is Reprocess {
        // "Anything else": pop the current node, switch to "in head" and
        // reprocess (growth no larger, the stack shortens by one).
        assert(o == in_head_noscript_anything_else(p, t));
        if p.open.len() > 0 {
            helpers_early::lemma_pop_nonempty(p);
        }
    }
    // Proven for every parser that has stopped or has a non-empty stack. The
    // remaining case, a running parser with an empty stack, is not proven:
    // `pop` of an empty stack has no known length (`Seq::drop_last` of an
    // empty sequence), so neither `L` nor the budget can be bounded; it needs
    // an invariant that the stack is non-empty here.
    if p.stopped || p.open.len() > 0 {
        assert(edge_ok(Rules::Html(Mode::InHeadNoscript), p, t, o));
    }
}

/// The edges of the "after head" mode are ranked.
pub proof fn lemma_after_head_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::AfterHead), p),
    ensures
        edge_ok(Rules::Html(Mode::AfterHead), p, t, mode_after_head(env, p, t)),
{
}

/// The edges of the "text" mode are ranked.
pub proof fn lemma_text_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::Text), p),
    ensures
        edge_ok(Rules::Html(Mode::Text), p, t, mode_text(env, p, t)),
{
    if t is Eof {
        // "An end-of-file token": pop the current node, switch to the
        // original insertion mode and reprocess (growth no larger, the
        // stack shortens by one).
        helpers_early::lemma_below_foreign(p.original_mode, t);
        if p.open.len() > 0 {
            helpers_early::lemma_pop_nonempty(p);
        }
    }
    // Proven for every parser that has stopped, or has a non-empty stack and
    // an original insertion mode other than "in table text". The remaining
    // cases are not proven: with an empty stack `pop` has no known length;
    // with original mode "in table text" the reprocessed parser is in "in
    // table text" with original mode "in table text", which breaks
    // `modes_ok`. Both need invariants of the "text" mode.
    if p.stopped || (p.open.len() > 0 && p.original_mode != Mode::InTableText) {
        assert(edge_ok(Rules::Html(Mode::Text), p, t, mode_text(env, p, t)));
    }
}

} // verus!
