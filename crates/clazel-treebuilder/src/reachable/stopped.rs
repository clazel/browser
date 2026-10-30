//! **Stopped reachable parsers** (Phase 4 items 4.9, 4.10): every parser
//! reachable from [`new_parser`] or [`fragment_parser`] that has stopped
//! has an empty stack of open elements and satisfies
//! `termination::modes_ok` ([`theorem_reachable_stopped`]), so with
//! [`super::run::theorem_reachable`] every reachable parser, stopped or
//! not, satisfies `modes_ok`.
//!
//! The proof. A rule that stops parsing part-way ("stop parsing", or the
//! node limit in `insert::create`) has popped the whole stack, and the
//! helpers after it keep the modes ([`super::stop_frame`],
//! [`super::stop_body`]): a stopped parser's `template` count is the
//! context's, which the template insertion modes cover, and the modes the
//! rule sets after the stop are fine ([`super::stop_early`],
//! [`super::stop_in_body`], [`super::stop_tables`]). The run of the
//! reprocessing loop meets those lemmas' hypotheses at every rule
//! application (it meets `invariant::rules_inv`, as
//! [`super::run::lemma_run_reach`] shows), and a step from a stopped
//! parser changes only its actions and tokenizer switch.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::stop_early::*;
#[cfg(verus_only)]
use super::stop_in_body::*;
#[cfg(verus_only)]
use super::stop_tables::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The rules of every insertion mode.
pub proof fn lemma_mode_rules_stop(env: EncFns, m: Mode, p: Parser, t: Tok)
    requires
        stop_pre(m, p),
    ensures
        stop_ok(outcome_parser(mode_rules(env, m, p, t))),
{
    hide(mode_initial);
    hide(mode_before_html);
    hide(mode_before_head);
    hide(mode_in_head);
    hide(mode_in_head_noscript);
    hide(mode_after_head);
    hide(mode_in_body);
    hide(mode_text);
    hide(mode_in_table);
    hide(mode_in_table_text);
    hide(mode_in_caption);
    hide(mode_in_column_group);
    hide(mode_in_table_body);
    hide(mode_in_row);
    hide(mode_in_cell);
    hide(mode_in_template);
    hide(mode_after_body);
    hide(mode_in_frameset);
    hide(mode_after_frameset);
    hide(mode_after_after_body);
    hide(mode_after_after_frameset);
    match m {
        Mode::Initial => lemma_initial_stop(env, p, t),
        Mode::BeforeHtml => lemma_before_html_stop(env, p, t),
        Mode::BeforeHead => lemma_before_head_stop(env, p, t),
        Mode::InHead => lemma_in_head_stop(env, p, t),
        Mode::InHeadNoscript => lemma_in_head_noscript_stop(env, p, t),
        Mode::AfterHead => lemma_after_head_stop(env, p, t),
        Mode::InBody => lemma_in_body_stop(env, p, t),
        Mode::Text => lemma_text_stop(env, p, t),
        Mode::InTable => lemma_in_table_stop(env, p, t),
        Mode::InTableText => lemma_in_table_text_stop(env, p, t),
        Mode::InCaption => lemma_in_caption_stop(env, p, t),
        Mode::InColumnGroup => lemma_in_column_group_stop(env, p, t),
        Mode::InTableBody => lemma_in_table_body_stop(env, p, t),
        Mode::InRow => lemma_in_row_stop(env, p, t),
        Mode::InCell => lemma_in_cell_stop(env, p, t),
        Mode::InTemplate => lemma_in_template_stop(env, p, t),
        Mode::AfterBody => lemma_after_body_stop(env, p, t),
        Mode::InFrameset => lemma_in_frameset_stop(env, p, t),
        Mode::AfterFrameset => lemma_after_frameset_stop(env, p, t),
        Mode::AfterAfterBody => lemma_after_after_body_stop(env, p, t),
        Mode::AfterAfterFrameset => lemma_after_after_frameset_stop(env, p, t),
    }
}

/// Every set of rules, applied to a running parser whose modes are fine.
pub proof fn lemma_rules_stop(env: EncFns, r: Rules, p: Parser, t: Tok)
    requires
        !p.stopped,
        modes_ok(p),
        rules_ok(r, p),
    ensures
        stop_ok(outcome_parser(apply_rules(env, r, p, t))),
{
    hide(mode_rules);
    hide(foreign_content);
    match r {
        Rules::Html(m) => lemma_mode_rules_stop(env, m, p, t),
        Rules::Foreign => lemma_foreign_stop(env, p, t),
    }
}

/// The run of the reprocessing loop from a parser satisfying
/// `invariant::rules_inv` ends, if it stops, with an empty stack and
/// `termination::modes_ok`.
pub proof fn lemma_run_stop(env: EncFns, p: Parser, t: Tok, r: Rules, fuel: nat)
    requires
        rules_inv(r, p, t),
    ensures
        run(env, p, t, r, fuel) is Some ==> stop_ok(run(env, p, t, r, fuel)->Some_0),
    decreases fuel,
{
    if fuel > 0 {
        let o = apply_rules(env, r, p, t);
        lemma_rules_stop(env, r, p, t);
        super::run::lemma_rules_reach(env, r, p, t);
        crate::termination::lemma_rules_edges(env, r, p, t);
        crate::exec::step::lemma_rules_tok(env, r, p, t);
        match o {
            Outcome::Done(q) => {},
            Outcome::Reprocess(q, t2) => {
                if !q.stopped {
                    crate::exec::step::lemma_tok_next_ok(t, t2);
                    assert(rules_inv(Rules::Html(q.mode), q, t2));
                    lemma_run_stop(env, q, t2, Rules::Html(q.mode), (fuel - 1) as nat);
                }
            },
            Outcome::Using(m, q, t2) => {
                if !q.stopped {
                    crate::exec::step::lemma_tok_next_ok(t, t2);
                    assert(rules_inv(Rules::Html(m), q, t2));
                    lemma_run_stop(env, q, t2, Rules::Html(m), (fuel - 1) as nat);
                }
            },
        }
    }
}

/// **A step keeps [`stop_ok`]**: from a parser satisfying
/// `invariant::reachable_inv` and [`stop_ok`], the next parser satisfies
/// [`stop_ok`].
pub proof fn lemma_dispatch_stop(env: EncFns, p: Parser, token: Token)
    requires
        reachable_inv(p),
        stop_ok(p),
    ensures
        stop_ok(dispatch(env, p, token).0),
{
    hide(run);
    hide(dispatcher);
    hide(rules_inv);
    hide(classify);
    let p0 = Parser { actions: seq![], tokenizer: None, ..p };
    if p0.stopped {
        assert(crate::termination::template_count(p0) == crate::termination::template_count(p));
        return;
    }
    let p1 = Parser { skip_lf: false, ..p0 };
    if p0.skip_lf && token == (Token::Character { c: 0x0A }) {
        return;
    }
    let t = classify(token);
    super::run::lemma_classify_ok(token);
    crate::theorems::equivalence::lemma_classify_plain(token);
    let r = dispatcher(p1, t);
    assert(reachable_inv(p1));
    super::run::lemma_dispatch_inv(p1, t);
    crate::termination::theorem_dispatch_total(env, p1, t);
    lemma_run_stop(env, p1, t, r, fuel_bound(p1));
    if p0.skip_lf {
        assert(dispatch(env, p, token).0 == tree_construction(env, p1, t));
    } else {
        assert(p1 == p0);
    }
}

/// [`stop_ok`] survives every sequence of steps from a parser satisfying
/// `invariant::reachable_inv`.
pub proof fn lemma_steps_stop(env: EncFns, p: Parser, tokens: Seq<Token>)
    requires
        reachable_inv(p),
        stop_ok(p),
    ensures
        stop_ok(super::run::dispatch_steps(env, p, tokens)),
    decreases tokens.len(),
{
    if tokens.len() > 0 {
        lemma_dispatch_stop(env, p, tokens[0]);
        super::run::lemma_dispatch_reach(env, p, tokens[0]);
        lemma_steps_stop(env, dispatch(env, p, tokens[0]).0, tokens.drop_first());
    }
}

/// **Every stopped reachable parser has an empty stack and fine modes**
/// (Phase 4 items 4.9, 4.10): for every parser reached from [`new_parser`]
/// or from [`fragment_parser`] by [`dispatch`] steps (any tokens, any
/// encoding functions), if it has stopped, its stack of open elements is
/// empty and it satisfies `termination::modes_ok`; so, with
/// `invariant::reachable_inv` ([`super::run::theorem_reachable`]), every
/// reachable parser satisfies `termination::modes_ok`.
pub proof fn theorem_reachable_stopped(
    env: EncFns,
    url: Seq<u32>,
    ctx: Context,
    scripting: bool,
    tentative: bool,
    tokens: Seq<Token>,
)
    ensures
        stop_ok(super::run::dispatch_steps(env, new_parser(url, scripting, tentative), tokens)),
        stop_ok(super::run::dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens)),
        crate::termination::modes_ok(super::run::dispatch_steps(env, new_parser(url, scripting, tentative), tokens)),
        crate::termination::modes_ok(super::run::dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens)),
{
    super::run::lemma_new_parser_reach(url, scripting, tentative);
    super::run::lemma_fragment_parser_reach(ctx, scripting);
    lemma_steps_stop(env, new_parser(url, scripting, tentative), tokens);
    lemma_steps_stop(env, fragment_parser(ctx, scripting).0, tokens);
    super::run::theorem_reachable(env, url, ctx, scripting, tentative, tokens);
}

} // verus!
