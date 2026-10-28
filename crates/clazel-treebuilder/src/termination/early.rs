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
}

/// The edges of the "in head noscript" mode are ranked.
pub proof fn lemma_in_head_noscript_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InHeadNoscript), p),
    ensures
        edge_ok(Rules::Html(Mode::InHeadNoscript), p, t, mode_in_head_noscript(env, p, t)),
{
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
}

} // verus!
