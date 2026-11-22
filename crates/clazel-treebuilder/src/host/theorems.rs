//! **The tree builder never builds a cycle through a template's host**:
//! every parser reachable from [`new_parser`] or [`fragment_parser`] by
//! [`dispatch`] steps, stopped or not, has the host invariant
//! (`host::host_inv`), so its document is
//! `clazel_dom::spec::host_acyclic` ([`theorem_reachable_host_acyclic`]),
//! and so is the document [`parse`] and [`parse_fragment`] return
//! ([`theorem_parse_host_acyclic`]): every node of it may be deep-cloned
//! (`clazel_dom::contract::clone_deep_requires`).
//!
//! The proof. Every rule application keeps the invariant
//! (`reachable::run::lemma_rules_reach`: `host::host_next`), by the lemmas of
//! `reachable` for the helpers (`reachable::keeps` carries
//! `host::host_step`) and of [`super::hostinv`] and [`super::rules`]; a run
//! of the reprocessing loop is rule applications ([`lemma_run_host`]); the
//! initial states have it ([`lemma_new_parser_host`],
//! [`lemma_fragment_parser_host`]).
//!
//! What this says of the DOM calls. Every guarded DOM "insert" and "take
//! all the children" the rules make, from a reachable parser, meets
//! `clazel_dom::host_acyclic_contract::insert_acyclic_requires` and
//! `reparent_children_acyclic_requires`
//! (`hostinv::lemma_host_dom_insert`, `hostinv::lemma_host_reparent`): the
//! host-including half of DOM's "ensure pre-insertion validity" step 2,
//! which the transcription's guards do not check, never fails where the
//! inclusive-ancestor half passes.

#[cfg(verus_only)]
use super::hi::*;
#[cfg(verus_only)]
use super::hostinv::*;
#[cfg(verus_only)]
use crate::host::*;
#[cfg(verus_only)]
use crate::invariant::*;
#[cfg(verus_only)]
use crate::reachable::run::*;
#[cfg(verus_only)]
use crate::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The step

/// A run of the reprocessing loop keeps the host invariant.
pub proof fn lemma_run_host(env: EncFns, p: Parser, t: Tok, r: Rules, fuel: nat)
    requires
        rules_inv(r, p, t),
        host_inv(p),
    ensures
        run(env, p, t, r, fuel) is Some ==> host_inv(run(env, p, t, r, fuel)->Some_0),
    decreases fuel,
{
    if fuel > 0 {
        let o = apply_rules(env, r, p, t);
        lemma_rules_reach(env, r, p, t);
        crate::termination::lemma_rules_edges(env, r, p, t);
        crate::exec::step::lemma_rules_tok(env, r, p, t);
        match o {
            Outcome::Done(q) => {},
            Outcome::Reprocess(q, t2) => {
                if !q.stopped {
                    crate::exec::step::lemma_tok_next_ok(t, t2);
                    assert(rules_inv(Rules::Html(q.mode), q, t2));
                    lemma_run_host(env, q, t2, Rules::Html(q.mode), (fuel - 1) as nat);
                }
            },
            Outcome::Using(m, q, t2) => {
                if !q.stopped {
                    crate::exec::step::lemma_tok_next_ok(t, t2);
                    assert(rules_inv(Rules::Html(m), q, t2));
                    lemma_run_host(env, q, t2, Rules::Html(m), (fuel - 1) as nat);
                }
            },
        }
    }
}

/// **The step keeps the host invariant**: for a parser satisfying
/// `invariant::reachable_inv` and `host::host_inv`, the state after
/// `dispatch(env, p, token)` satisfies `host::host_inv` (`host::host_step`).
pub proof fn theorem_host_step(env: EncFns, p: Parser, token: Token)
    requires
        reachable_inv(p),
        host_inv(p),
    ensures
        host_inv(dispatch(env, p, token).0),
{
    hide(run);
    hide(dispatcher);
    hide(rules_inv);
    hide(classify);
    let p0 = Parser { actions: seq![], tokenizer: None, ..p };
    if p0.stopped {
        return;
    }
    let p1 = Parser { skip_lf: false, ..p0 };
    if p0.skip_lf && token == (Token::Character { c: 0x0A }) {
        return;
    }
    let t = classify(token);
    lemma_classify_ok(token);
    crate::theorems::equivalence::lemma_classify_plain(token);
    let r = dispatcher(p1, t);
    assert(reachable_inv(p1));
    lemma_dispatch_inv(p1, t);
    crate::termination::theorem_dispatch_total(env, p1, t);
    lemma_run_host(env, p1, t, r, fuel_bound(p1));
    if p0.skip_lf {
        assert(dispatch(env, p, token).0 == tree_construction(env, p1, t));
    } else {
        assert(p1 == p0);
    }
}

// ---------------------------------------------------------------------
// The initial states

/// A new parser has the host invariant.
pub proof fn lemma_new_parser_host(url: Seq<u32>, scripting: bool, tentative: bool)
    ensures
        host_inv(new_parser(url, scripting, tentative)),
{
    clazel_dom::host_acyclic_lemmas::theorem_new_document_host_acyclic(url);
    lemma_host_inv_intro(new_parser(url, scripting, tentative));
}

/// The fragment parser's arena is `clazel_dom::spec::host_acyclic`, and
/// root is no host-including inclusive ancestor of the fragment.
pub proof fn lemma_fragment_doc_host(ctx: Context)
    ensures
        ({
            let (d, c, r, f) = crate::exec::step::fragment_doc(ctx);
            dom::host_acyclic(d) && !hi(d, r, f)
        }),
{
    hide(dom::insert);
    let ck = crate::exec::step::context_kind(ctx);
    let rk = crate::exec::step::root_kind();
    let fk = NodeKind::DocumentFragment { host: None };
    let dn = dom::new_document(seq![]);
    clazel_dom::lemmas::theorem_new_document_wf(seq![]);
    clazel_dom::host_acyclic_lemmas::theorem_new_document_host_acyclic(seq![]);
    clazel_dom::lemmas::theorem_set_mode_wf(dn, ctx.mode);
    clazel_dom::host_acyclic_lemmas::theorem_set_mode_host_acyclic(dn, ctx.mode);
    let d0 = dom::set_mode(dn, ctx.mode);
    assert(d0.nodes.len() == 1);
    clazel_dom::lemmas::theorem_create_node_wf(d0, ck);
    clazel_dom::host_acyclic_lemmas::theorem_create_node_host_acyclic(d0, ck);
    let (d1, c1) = dom::create_node(d0, ck);
    clazel_dom::lemmas::theorem_create_node_wf(d1, rk);
    clazel_dom::host_acyclic_lemmas::theorem_create_node_host_acyclic(d1, rk);
    let (d2, root) = dom::create_node(d1, rk);
    assert(d2.nodes.len() == 3 && root == 2);
    // The Document has no step up, so root is no ancestor of it.
    assert(d2.nodes[0] == d0.nodes[0]);
    assert(d2.nodes[0].parent is None && d2.nodes[0].kind is Document) by {
        let paths = clazel_dom::lemmas::lemma_wf_witness(d0);
    }
    lemma_top_of(d2, 0);
    if hi(d2, root, 0) {
        lemma_hi_top(d2, root, 0);
    }
    assert(!dom::is_inclusive_ancestor(d2, root, 0)) by {
        assert(d2.nodes[0].parent is None);
    }
    assert(d2.nodes[root as int].kind == rk);
    assert(dom::insert_requires(d2, root, 0, None));
    assert(clazel_dom::host_acyclic_contract::insert_acyclic_requires(d2, root, 0, None));
    clazel_dom::lemmas::theorem_append_wf(d2, 0, root);
    clazel_dom::host_acyclic_lemmas::theorem_append_host_acyclic(d2, 0, root);
    let d3 = dom::append(d2, 0, root);
    assert(d3.nodes.len() == 3) by {
        clazel_dom::lemmas::theorem_insert_wf(d2, root, 0, None);
    }
    clazel_dom::lemmas::theorem_create_node_wf(d3, fk);
    clazel_dom::host_acyclic_lemmas::theorem_create_node_host_acyclic(d3, fk);
    lemma_create_top(d3, fk);
    let (d4, fragment) = dom::create_node(d3, fk);
    assert(fragment == 3);
    if hi(d4, root, fragment) {
        lemma_hi_top(d4, root, fragment);
    }
}

/// The fragment parser has the host invariant.
pub proof fn lemma_fragment_parser_host(ctx: Context, scripting: bool)
    ensures
        host_inv(fragment_parser(ctx, scripting).0),
{
    hide(reset_from);
    hide(annotation_html);
    hide(dom::insert);
    let (d4, ctx_id, root, fragment) = crate::exec::step::fragment_doc(ctx);
    lemma_fragment_doc_host(ctx);
    let p = fragment_parser(ctx, scripting).0;
    assert(p.doc == d4);
    assert(p.open.len() == 1 && p.open[0].id == root);
    assert(p.redirect == Some((root, fragment)));
    assert(!p.stopped);
    lemma_host_inv_intro(p);
}

// ---------------------------------------------------------------------
// The theorems

/// The host invariant survives every sequence of steps.
pub proof fn lemma_steps_host(env: EncFns, p: Parser, tokens: Seq<Token>)
    requires
        reachable_inv(p),
        host_inv(p),
    ensures
        host_inv(dispatch_steps(env, p, tokens)),
    decreases tokens.len(),
{
    if tokens.len() > 0 {
        lemma_dispatch_reach(env, p, tokens[0]);
        theorem_host_step(env, p, tokens[0]);
        lemma_steps_host(env, dispatch(env, p, tokens[0]).0, tokens.drop_first());
    }
}

/// A document with the host invariant may be deep-cloned at every node
/// (`host::clone_deep_ready`).
pub proof fn lemma_clone_deep_ready(p: Parser)
    requires
        host_inv(p),
    ensures
        dom::host_acyclic(p.doc),
        clone_deep_ready(p),
{
    lemma_host_inv(p);
}

/// **Every reachable parser has a host-acyclic document**: for every
/// parser reached from [`new_parser`] or from [`fragment_parser`] by
/// [`dispatch`] steps (any tokens, any encoding functions), stopped or not,
/// `host::host_inv` holds: its document is
/// `clazel_dom::spec::host_acyclic` (no cycle through a parent or a
/// template's host), and until it stops its stack of open elements is
/// ordered as the document (`host::stack_ordered_of`,
/// `host::redirect_above_of`). So every node of the document meets
/// `clazel_dom::contract::clone_deep_requires` (`host::clone_deep_ready`).
/// No hypotheses.
pub proof fn theorem_reachable_host_acyclic(
    env: EncFns,
    url: Seq<u32>,
    ctx: Context,
    scripting: bool,
    tentative: bool,
    tokens: Seq<Token>,
)
    ensures
        host_inv(dispatch_steps(env, new_parser(url, scripting, tentative), tokens)),
        host_inv(dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens)),
        dom::host_acyclic(dispatch_steps(env, new_parser(url, scripting, tentative), tokens).doc),
        dom::host_acyclic(dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens).doc),
        clone_deep_ready(dispatch_steps(env, new_parser(url, scripting, tentative), tokens)),
        clone_deep_ready(dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens)),
{
    lemma_new_parser_reach(url, scripting, tentative);
    lemma_fragment_parser_reach(ctx, scripting);
    lemma_new_parser_host(url, scripting, tentative);
    lemma_fragment_parser_host(ctx, scripting);
    lemma_steps_host(env, new_parser(url, scripting, tentative), tokens);
    lemma_steps_host(env, fragment_parser(ctx, scripting).0, tokens);
    lemma_clone_deep_ready(dispatch_steps(env, new_parser(url, scripting, tentative), tokens));
    lemma_clone_deep_ready(dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens));
}

/// [`parse_steps`] keeps `invariant::reachable_inv` and the host invariant.
pub proof fn lemma_parse_steps_host<S>(env: EncFns, tf: TokFns<S>, s: S, p: Parser, acts: Seq<Action>, n: nat)
    requires
        reachable_inv(p),
        host_inv(p),
    ensures
        host_inv(parse_steps(env, tf, s, p, acts, n).0),
    decreases n,
{
    hide(dispatch);
    if p.stopped {
    } else if n == 0 {
        lemma_host_stopped(p, stop_parsing(Parser { actions: seq![], ..p }));
    } else {
        let (s1, token) = (tf.next)(s);
        let (p1, a) = dispatch(env, p, token);
        lemma_dispatch_reach(env, p, token);
        theorem_host_step(env, p, token);
        let s2 = match p1.tokenizer {
            Some(st) => (tf.set_state)(s1, st),
            None => s1,
        };
        let s3 = (tf.set_foreign)(s2, in_foreign_content(p1));
        lemma_parse_steps_host(env, tf, s3, p1, acts + a, (n - 1) as nat);
    }
}

/// **The parser's output is host-acyclic**: the document [`parse`] returns,
/// and the one [`parse_fragment`] returns, for any tokenizer, any encoding
/// functions and any bound, is `clazel_dom::spec::host_acyclic`; so each of
/// its nodes that may be cloned (`clazel_dom::spec::clone_requires`) meets
/// the precondition of `clazel-dom`'s deep clone,
/// `clazel_dom::contract::clone_deep_requires`. No hypotheses.
pub proof fn theorem_parse_host_acyclic<S>(
    env: EncFns,
    tf: TokFns<S>,
    s0: S,
    url: Seq<u32>,
    ctx: Context,
    scripting: bool,
    tentative: bool,
    n: nat,
)
    ensures
        dom::host_acyclic(parse(env, tf, s0, url, scripting, tentative, n).0),
        dom::host_acyclic(parse_fragment(env, tf, s0, ctx, scripting, n).0),
        forall|x: NodeId| #[trigger]
            dom::clone_requires(parse(env, tf, s0, url, scripting, tentative, n).0, x) ==> clazel_dom::contract::clone_deep_requires(
                parse(env, tf, s0, url, scripting, tentative, n).0,
                x,
            ),
        forall|x: NodeId| #[trigger]
            dom::clone_requires(parse_fragment(env, tf, s0, ctx, scripting, n).0, x) ==> clazel_dom::contract::clone_deep_requires(
                parse_fragment(env, tf, s0, ctx, scripting, n).0,
                x,
            ),
{
    let p = new_parser(url, scripting, tentative);
    lemma_new_parser_reach(url, scripting, tentative);
    lemma_new_parser_host(url, scripting, tentative);
    lemma_parse_steps_host(env, tf, s0, p, seq![], n);
    lemma_host_inv(parse_steps(env, tf, s0, p, seq![], n).0);
    let (pf, fragment, st) = fragment_parser(ctx, scripting);
    lemma_fragment_parser_reach(ctx, scripting);
    lemma_fragment_parser_host(ctx, scripting);
    let s1 = match st {
        Some(x) => (tf.set_state)(s0, x),
        None => s0,
    };
    let s2 = (tf.set_foreign)(s1, in_foreign_content(pf));
    lemma_parse_steps_host(env, tf, s2, pf, seq![], n);
    lemma_host_inv(parse_steps(env, tf, s2, pf, seq![], n).0);
}

} // verus!
