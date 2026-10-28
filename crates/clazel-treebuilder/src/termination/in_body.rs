//! The edges of the "in body" mode are ranked
//! (see [`super`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The edges of the "in body" mode are ranked.
pub proof fn lemma_in_body_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InBody), p),
    ensures
        edge_ok(Rules::Html(Mode::InBody), p, t, mode_in_body(env, p, t)),
{
}

} // verus!
