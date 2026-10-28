//! The edges of the "after body", "in frameset", "after frameset", "after after body", "after after frameset" modes and foreign content are ranked
//! (see [`super`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The edges of the "after body" mode are ranked.
pub proof fn lemma_after_body_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::AfterBody), p),
    ensures
        edge_ok(Rules::Html(Mode::AfterBody), p, t, mode_after_body(env, p, t)),
{
}

/// The edges of the "in frameset" mode are ranked.
pub proof fn lemma_in_frameset_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InFrameset), p),
    ensures
        edge_ok(Rules::Html(Mode::InFrameset), p, t, mode_in_frameset(env, p, t)),
{
}

/// The edges of the "after frameset" mode are ranked.
pub proof fn lemma_after_frameset_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::AfterFrameset), p),
    ensures
        edge_ok(Rules::Html(Mode::AfterFrameset), p, t, mode_after_frameset(env, p, t)),
{
}

/// The edges of the "after after body" mode are ranked.
pub proof fn lemma_after_after_body_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::AfterAfterBody), p),
    ensures
        edge_ok(Rules::Html(Mode::AfterAfterBody), p, t, mode_after_after_body(env, p, t)),
{
}

/// The edges of the "after after frameset" mode are ranked.
pub proof fn lemma_after_after_frameset_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::AfterAfterFrameset), p),
    ensures
        edge_ok(Rules::Html(Mode::AfterAfterFrameset), p, t, mode_after_after_frameset(env, p, t)),
{
}

/// The edges of the rules for foreign content are ranked.
pub proof fn lemma_foreign_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
    ensures
        edge_ok(Rules::Foreign, p, t, foreign_content(env, p, t)),
{
    if is_foreign_breakout(t) && !(t is Char || t is Comment || t is Pi || t is Doctype) {
        lemma_foreign_breakout(env, p, t);
    } else {
        lemma_foreign_other(env, p, t);
    }
}

/// A breakout token: pop the foreign elements and reprocess in the current
/// insertion mode: G no larger, L no larger, the order 30 to below.
#[verifier::spinoff_prover]
pub proof fn lemma_foreign_breakout(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        is_foreign_breakout(t),
        !(t is Char || t is Comment || t is Pi || t is Doctype),
    ensures
        edge_ok(Rules::Foreign, p, t, foreign_content(env, p, t)),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_foreign_element);
    hide(foreign_end_tag_loop);
    helpers_tables::lemma_pop_while_all(p);
    let o = foreign_content(env, p, t);
    assert(o is Reprocess);
    let q = o->Reprocess_0;
    assert(o->Reprocess_1 == t);
    assert(q == (Parser { open: q.open, ..p }));
    assert(helpers_tables::is_prefix(q.open, p.open));
    helpers_ranking::lemma_template_count_prefix(p, q);
    helpers_ranking::lemma_modes_ok_from(p, q);
    helpers_tables::lemma_pop_while_all(p);
    helpers_early::lemma_foreign_reprocess(p, q, t);
}

/// The other tokens: handled, or (an end tag whose loop meets an HTML
/// element) reprocessed unchanged in the current insertion mode.
#[verifier::spinoff_prover]
pub proof fn lemma_foreign_other(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        !(is_foreign_breakout(t) && !(t is Char || t is Comment || t is Pi || t is Doctype)),
    ensures
        edge_ok(Rules::Foreign, p, t, foreign_content(env, p, t)),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_foreign_element);
    hide(pop_while);
    hide(svg_script_end);
    hide(pop);
    if t is End && !(t->End_0.tag == Tag::Script && p.open.len() > 0 && is_svg(current_node(p), Tag::Script)) {
        helpers_early::lemma_foreign_end_tag_loop(p, t, p.open.len() - 1);
        assert(foreign_content(env, p, t) == foreign_end_tag_loop(p, t, p.open.len() - 1));
        helpers_early::lemma_foreign_reprocess(p, p, t);
    } else {
        assert(foreign_content(env, p, t) is Done);
    }
}

} // verus!
