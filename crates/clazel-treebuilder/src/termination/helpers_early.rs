//! Helper lemmas for the edges of the "in head", "in head noscript" and
//! "text" modes and of foreign content (see [`super`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "Pop the current node" of a non-empty stack shortens it by exactly one
/// and changes nothing else that the ranking reads.
pub proof fn lemma_pop_nonempty(p: Parser)
    requires
        p.open.len() > 0,
    ensures
        pop(p).open.len() == p.open.len() - 1,
        pop(p).mode == p.mode,
        pop(p).original_mode == p.original_mode,
        pop(p).template_modes == p.template_modes,
        pop(p).stopped == p.stopped,
{
}

/// [`pop_while`] never lengthens the stack and keeps the modes and the
/// stopped flag.
pub proof fn lemma_pop_while(p: Parser, f: spec_fn(Elem) -> bool)
    ensures
        pop_while(p, f).open.len() <= p.open.len(),
        pop_while(p, f).mode == p.mode,
        pop_while(p, f).original_mode == p.original_mode,
        pop_while(p, f).template_modes == p.template_modes,
        pop_while(p, f).stopped == p.stopped,
    decreases p.open.len(),
{
    if p.open.len() > 0 && f(current_node(p)) {
        lemma_pop_nonempty(p);
        lemma_pop_while(pop(p), f);
    }
}

/// The loop of foreign content's "any other end tag" either handles the
/// token or reprocesses it unchanged, with the parser unchanged.
pub proof fn lemma_foreign_end_tag_loop(p: Parser, t: Tok, i: int)
    ensures
        foreign_end_tag_loop(p, t, i) is Done || foreign_end_tag_loop(p, t, i) == Outcome::Reprocess(p, t),
    decreases i,
{
    if i <= 0 || i >= p.open.len() {
    } else if ascii_lowercase(p.open[i].name) == t->End_0.name {
    } else if p.open[i - 1].ns != clazel_dom::spec::Namespace::Html {
        lemma_foreign_end_tag_loop(p, t, i - 1);
    }
}

/// Every set of rules has growth at most [`growth_max`] and order at most
/// [`order_max`], and order below that of foreign content unless it is
/// foreign content.
pub proof fn lemma_below_foreign(m: Mode, t: Tok)
    ensures
        growth(Rules::Html(m), t) <= growth_max(),
        order(Rules::Html(m), t) < order(Rules::Foreign, t),
{
}

/// Reprocessing a token in the current insertion mode from foreign content
/// with a parser whose stack is no longer and whose template modes are
/// the same is ranked.
pub proof fn lemma_foreign_reprocess(p: Parser, q: Parser, t: Tok)
    requires
        q.open.len() <= p.open.len(),
        q.template_modes == p.template_modes,
    ensures
        decreases_to(Rules::Foreign, p, t, Rules::Html(q.mode), q, t),
{
    lemma_below_foreign(q.mode, t);
}

} // verus!
