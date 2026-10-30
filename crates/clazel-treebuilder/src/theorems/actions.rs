//! From one rule application to the whole parse: the reprocessing loop
//! `run`, the tree construction stage, the one-token step `dispatch` and
//! `parse_steps` keep the order of the actions.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every run of the reprocessing loop satisfies [`step_ok`].
pub proof fn lemma_run(env: EncFns, p: Parser, t: Tok, r: Rules, fuel: nat)
    ensures
        run(env, p, t, r, fuel) matches Some(q) ==> step_ok(p, q),
    decreases fuel,
{
    hide(apply_rules);
    if fuel > 0 {
        let o = apply_rules(env, r, p, t);
        super::frame_modes::lemma_apply_rules(env, r, p, t);
        match o {
            Outcome::Done(_) => {},
            Outcome::Reprocess(q, t2) => {
                if !q.stopped {
                    lemma_run(env, q, t2, Rules::Html(q.mode), (fuel - 1) as nat);
                    if let Some(x) = run(env, q, t2, Rules::Html(q.mode), (fuel - 1) as nat) {
                        lemma_step_ok_trans(p, q, x);
                    }
                }
            },
            Outcome::Using(m, q, t2) => {
                if !q.stopped {
                    lemma_run(env, q, t2, Rules::Html(m), (fuel - 1) as nat);
                    if let Some(x) = run(env, q, t2, Rules::Html(m), (fuel - 1) as nat) {
                        lemma_step_ok_trans(p, q, x);
                    }
                }
            },
        }
    }
}

/// The tree construction stage satisfies [`step_ok`] (its fallback, never
/// taken by `theorem_dispatch_total`, stops parsing, which does too).
pub proof fn lemma_tree_construction(env: EncFns, p: Parser, t: Tok)
    ensures
        step_ok(p, tree_construction(env, p, t)),
{
    hide(run);
    lemma_run(env, p, t, dispatcher(p, t), fuel_bound(p));
    if run(env, p, t, dispatcher(p, t), fuel_bound(p)) is None {
        lemma_grows_step_ok(p, stop_parsing(p));
    }
}

/// The actions `a` of one step from `p` to `q`: those `q` carries; a
/// `StopParsing` is the last of them and `q` is stopped; at most one is a
/// `ChangeEncoding`, and only from a tentative confidence in `p` to a
/// certain one in `q`; the confidence never becomes tentative.
pub open spec fn step_actions_ok(p: Parser, q: Parser, a: Seq<Action>) -> bool {
    &&& a == q.actions
    &&& forall|i: int| 0 <= i < a.len() && (#[trigger] a[i]) is StopParsing ==> i == a.len() - 1 && q.stopped
    &&& forall|i: int| 0 <= i < a.len() && (#[trigger] a[i]) is ChangeEncoding ==> p.tentative && !q.tentative
    &&& forall|i: int, j: int| 0 <= i < j < a.len() && (#[trigger] a[i]) is ChangeEncoding ==> !((#[trigger] a[j]) is ChangeEncoding)
    &&& q.tentative ==> p.tentative
}

/// **The per-step lemma**: one step of a running parser satisfies
/// [`step_actions_ok`].
pub proof fn lemma_dispatch(env: EncFns, p: Parser, token: Token)
    requires
        !p.stopped,
    ensures
        step_actions_ok(p, dispatch(env, p, token).0, dispatch(env, p, token).1),
{
    hide(tree_construction);
    let p0 = Parser { actions: seq![], tokenizer: None, ..p };
    if p0.skip_lf {
        let p1 = Parser { skip_lf: false, ..p0 };
        if token != (Token::Character { c: 0x0A }) {
            lemma_tree_construction(env, p1, classify(token));
        }
    } else {
        lemma_tree_construction(env, p0, classify(token));
    }
}

/// The parser state `p` and the actions `acts` so far, from a confidence
/// that started tentative if `t0`: a `StopParsing` is the last action and
/// the parser is stopped; at most one `ChangeEncoding`, only if
/// `t0`, and then the confidence is certain; the confidence is tentative
/// only if it started so.
pub open spec fn acts_ok(acts: Seq<Action>, p: Parser, t0: bool) -> bool {
    &&& forall|i: int| 0 <= i < acts.len() && (#[trigger] acts[i]) is StopParsing ==> i == acts.len() - 1 && p.stopped
    &&& forall|i: int| 0 <= i < acts.len() && (#[trigger] acts[i]) is ChangeEncoding ==> t0 && !p.tentative
    &&& forall|i: int, j: int|
        0 <= i < j < acts.len() && (#[trigger] acts[i]) is ChangeEncoding ==> !((#[trigger] acts[j]) is ChangeEncoding)
    &&& p.tentative ==> t0
}

/// `StopParsing` occurs at most once, and only as the last action.
pub open spec fn stop_last(acts: Seq<Action>) -> bool {
    forall|i: int| 0 <= i < acts.len() && (#[trigger] acts[i]) is StopParsing ==> i == acts.len() - 1
}

/// `ChangeEncoding` occurs at most once, and only if the confidence started
/// tentative (`t0`).
pub open spec fn change_encoding_once(acts: Seq<Action>, t0: bool) -> bool {
    &&& forall|i: int, j: int|
        0 <= i < j < acts.len() && (#[trigger] acts[i]) is ChangeEncoding ==> !((#[trigger] acts[j]) is ChangeEncoding)
    &&& forall|i: int| 0 <= i < acts.len() && (#[trigger] acts[i]) is ChangeEncoding ==> t0
}

/// One more step keeps [`acts_ok`].
pub proof fn lemma_acts_ok_step(acts: Seq<Action>, p: Parser, p1: Parser, a: Seq<Action>, t0: bool)
    requires
        acts_ok(acts, p, t0),
        !p.stopped,
        step_actions_ok(p, p1, a),
    ensures
        acts_ok(acts + a, p1, t0),
{
    let c = acts + a;
    let k = acts.len() as int;
    assert forall|i: int| 0 <= i < c.len() && (#[trigger] c[i]) is StopParsing implies i == c.len() - 1 && p1.stopped by {
        if i >= k {
            assert(a[i - k] == c[i]);
        }
    }
    assert forall|i: int| 0 <= i < c.len() && (#[trigger] c[i]) is ChangeEncoding implies t0 && !p1.tentative by {
        if i >= k {
            assert(a[i - k] == c[i]);
        }
    }
    assert forall|i: int, j: int| 0 <= i < j < c.len() && (#[trigger] c[i]) is ChangeEncoding implies !((#[trigger] c[j]) is ChangeEncoding) by {
        if i >= k {
            assert(a[i - k] == c[i]);
            assert(a[j - k] == c[j]);
        } else if j >= k {
            assert(acts[i] == c[i]);
            assert(a[j - k] == c[j]);
        } else {
            assert(acts[i] == c[i]);
            assert(acts[j] == c[j]);
        }
    }
}

/// `parse_steps` keeps the order of the actions: `StopParsing` last, and at
/// most one `ChangeEncoding`, only from a tentative start.
pub proof fn lemma_parse_steps<S>(env: EncFns, tf: TokFns<S>, s: S, p: Parser, acts: Seq<Action>, n: nat, t0: bool)
    requires
        acts_ok(acts, p, t0),
    ensures
        stop_last(parse_steps(env, tf, s, p, acts, n).1),
        change_encoding_once(parse_steps(env, tf, s, p, acts, n).1, t0),
    decreases n,
{
    hide(dispatch);
    if p.stopped {
    } else if n == 0 {
        // `parse_steps` appends the actions of stopping a parser with no
        // actions of its own: just `StopParsing`.
        let q = stop_parsing(Parser { actions: seq![], ..p });
        assert(q.actions =~= seq![Action::StopParsing]);
        let c = acts + q.actions;
        let k = acts.len() as int;
        assert forall|i: int| 0 <= i < c.len() && (#[trigger] c[i]) is StopParsing implies i == c.len() - 1 by {
            if i < k {
                assert(acts[i] == c[i]);
            }
        }
        assert forall|i: int| 0 <= i < c.len() && (#[trigger] c[i]) is ChangeEncoding implies t0 by {
            if i < k {
                assert(acts[i] == c[i]);
            }
        }
        assert forall|i: int, j: int| 0 <= i < j < c.len() && (#[trigger] c[i]) is ChangeEncoding implies !((#[trigger] c[j]) is ChangeEncoding) by {
            if j < k {
                assert(acts[i] == c[i]);
                assert(acts[j] == c[j]);
            }
        }
    } else {
        let (s1, token) = (tf.next)(s);
        let (p1, a) = dispatch(env, p, token);
        lemma_dispatch(env, p, token);
        lemma_acts_ok_step(acts, p, p1, a, t0);
        let s2 = match p1.tokenizer {
            Some(st) => (tf.set_state)(s1, st),
            None => s1,
        };
        let s3 = (tf.set_foreign)(s2, in_foreign_content(p1));
        lemma_parse_steps(env, tf, s3, p1, acts + a, (n - 1) as nat, t0);
    }
}

} // verus!
