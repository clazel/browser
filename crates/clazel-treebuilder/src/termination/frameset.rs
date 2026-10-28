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
    if t is Char || t is Comment || t is Pi || t is Doctype {
        assert(foreign_content(env, p, t) is Done);
    } else if is_foreign_breakout(t) {
        assert forall|f: spec_fn(Elem) -> bool| #[trigger] pop_while(p, f).open.len() <= p.open.len() && pop_while(p, f).mode
            == p.mode && pop_while(p, f).original_mode == p.original_mode && pop_while(p, f).template_modes
            == p.template_modes by {
            helpers_early::lemma_pop_while(p, f);
        }
        let o = foreign_content(env, p, t);
        assert(o is Reprocess);
        let q = o->Reprocess_0;
        assert(o->Reprocess_1 == t);
        assert(q.open.len() <= p.open.len() && q.template_modes == p.template_modes && q.mode == p.mode && q.original_mode
            == p.original_mode);
        helpers_early::lemma_foreign_reprocess(p, q, t);
    } else if t is Start {
        assert(foreign_content(env, p, t) is Done);
    } else if t is End && t->End_0.tag == Tag::Script && p.open.len() > 0 && is_svg(current_node(p), Tag::Script) {
        assert(foreign_content(env, p, t) is Done);
    } else if t is End {
        helpers_early::lemma_foreign_end_tag_loop(p, t, p.open.len() - 1);
        assert(foreign_content(env, p, t) == foreign_end_tag_loop(p, t, p.open.len() - 1));
        helpers_early::lemma_foreign_reprocess(p, p, t);
    }
}

} // verus!
