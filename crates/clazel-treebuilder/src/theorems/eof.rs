//! `theorem_eof_stops`: the end-of-file token stops the parser. Every
//! insertion mode's rules for an end-of-file token stop parsing (§13.2.7),
//! or reprocess it, or process it using another mode's rules
//! ([`eof_ok`]); the dispatcher sends it to the rules of the current
//! insertion mode, never to foreign content; so whatever the reprocessing
//! loop returns has stopped, and so has `tree_construction`'s fallback.
//! No hypothesis on the parser is needed.
//!
//! The driver (`exec::driver`) uses it: after the tokenizer has emitted its
//! end-of-file token, the parser has stopped, so its loop ends.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What a set of rules does with an end-of-file token: it stops parsing
/// (§13.2.7) or hands the same token on.
pub open spec fn eof_ok(o: Outcome) -> bool {
    match o {
        Outcome::Done(q) => q.stopped,
        Outcome::Reprocess(_, t2) => t2 == Tok::Eof,
        Outcome::Using(_, _, t2) => t2 == Tok::Eof,
    }
}

/// Every insertion mode's rules stop parsing at an end-of-file token or
/// hand it on.
#[verifier::spinoff_prover]
pub proof fn lemma_mode_eof(env: EncFns, m: Mode, p: Parser)
    ensures
        eof_ok(mode_rules(env, m, p, Tok::Eof)),
{
}

/// The reprocessing loop, started on an end-of-file token with the rules
/// of an insertion mode, returns a stopped parser or runs out of fuel.
pub proof fn lemma_run_eof(env: EncFns, p: Parser, m: Mode, fuel: nat)
    ensures
        run(env, p, Tok::Eof, Rules::Html(m), fuel) matches Some(q) ==> q.stopped,
    decreases fuel,
{
    if fuel > 0 {
        lemma_mode_eof(env, m, p);
        match mode_rules(env, m, p, Tok::Eof) {
            Outcome::Done(_) => {},
            Outcome::Reprocess(q, _) => if !q.stopped {
                lemma_run_eof(env, q, q.mode, (fuel - 1) as nat);
            },
            Outcome::Using(m2, q, _) => if !q.stopped {
                lemma_run_eof(env, q, m2, (fuel - 1) as nat);
            },
        }
    }
}

/// **The end-of-file token stops the parser**: the one-token step on an
/// end-of-file token returns a stopped parser, from every parser.
pub proof fn theorem_eof_stops(env: EncFns, p: Parser)
    ensures
        dispatch(env, p, Token::Eof).0.stopped,
{
    let p0 = Parser { actions: seq![], tokenizer: None, ..p };
    let p1 = if p0.skip_lf {
        Parser { skip_lf: false, ..p0 }
    } else {
        p0
    };
    if !p0.stopped {
        // The dispatcher sends an end-of-file token to the rules of the
        // current insertion mode.
        assert(dispatcher(p1, Tok::Eof) == Rules::Html(p1.mode));
        assert(classify(Token::Eof) == Tok::Eof);
        lemma_run_eof(env, p1, p1.mode, fuel_bound(p1));
        assert(dispatch(env, p, Token::Eof).0 == tree_construction(env, p1, Tok::Eof));
    }
}

} // verus!
