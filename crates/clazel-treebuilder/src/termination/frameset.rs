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
}

} // verus!
