//! Every rule application, so every run of the reprocessing loop and every
//! [`dispatch`] step, keeps [`reachable_inv`]; the parsers' initial states
//! satisfy it; [`theorem_reachable`].

#[cfg(verus_only)]
use super::body_tags::*;
#[cfg(verus_only)]
use super::early::*;
#[cfg(verus_only)]
use super::helpers::*;
#[cfg(verus_only)]
use super::lists::*;
#[cfg(verus_only)]
use super::rest::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::tables::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// One rule application

/// Every set of rules keeps [`next_core`].
pub proof fn lemma_rules_reach(env: EncFns, r: Rules, p: Parser, t: Tok)
    requires
        rules_inv(r, p, t),
    ensures
        next_core(apply_rules(env, r, p, t)),
{
    match r {
        Rules::Foreign => lemma_foreign_reach(env, p, t),
        Rules::Html(m) => match m {
            Mode::Initial => lemma_initial_reach(env, p, t),
            Mode::BeforeHtml => lemma_before_html_reach(env, p, t),
            Mode::BeforeHead => lemma_before_head_reach(env, p, t),
            Mode::InHead => lemma_in_head_reach(env, p, t),
            Mode::InHeadNoscript => lemma_in_head_noscript_reach(env, p, t),
            Mode::AfterHead => lemma_after_head_reach(env, p, t),
            Mode::InBody => lemma_in_body_reach(env, p, t),
            Mode::Text => lemma_text_reach(env, p, t),
            Mode::InTable => lemma_in_table_reach(env, p, t),
            Mode::InTableText => lemma_in_table_text_reach(env, p, t),
            Mode::InCaption => lemma_in_caption_reach(env, p, t),
            Mode::InColumnGroup => lemma_in_column_group_reach(env, p, t),
            Mode::InTableBody => lemma_in_table_body_reach(env, p, t),
            Mode::InRow => lemma_in_row_reach(env, p, t),
            Mode::InCell => lemma_in_cell_reach(env, p, t),
            Mode::InTemplate => lemma_in_template_reach(env, p, t),
            Mode::AfterBody => lemma_after_body_reach(env, p, t),
            Mode::InFrameset => lemma_in_frameset_reach(env, p, t),
            Mode::AfterFrameset => lemma_after_frameset_reach(env, p, t),
            Mode::AfterAfterBody => lemma_after_after_body_reach(env, p, t),
            Mode::AfterAfterFrameset => lemma_after_after_frameset_reach(env, p, t),
        },
    }
}

/// The "in row" rules keep [`cell_ok`].
pub proof fn lemma_row_cell(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InRow), p, t),
    ensures
        outcome_parser(mode_in_row(env, p, t)).stopped || cell_ok(outcome_parser(mode_in_row(env, p, t))),
{
    hide(clear_stack_back_to_table_row_context);
    hide(push_marker);
    hide(insert_html_element);
    assert(p.mode == Mode::InRow);
    if t is Start && (t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Td) {
        let p1 = clear_stack_back_to_table_row_context(p);
        let (p2, e) = insert_html_element(p1, t->Start_0);
        assert(e.tag == t->Start_0.tag && e.ns == Namespace::Html) by {
            reveal(insert_html_element);
            lemma_insert_html_keeps_frame(p1, t->Start_0);
            lemma_ceft_frame(p1, t->Start_0, Namespace::Html, appropriate_place(p1, None).parent);
        }
        assert(!p2.stopped ==> p2.open == p1.open.push(e)) by {
            reveal(insert_html_element);
            lemma_insert_html_keeps_frame(p1, t->Start_0);
        }
        let q = push_marker(Parser { mode: Mode::InCell, ..p2 });
        assert(q.open == p2.open && q.stopped == p2.stopped) by {
            reveal(push_marker);
        }
        if !q.stopped {
            assert(q.open[q.open.len() - 1] == e);
            assert(cell_pred()(e));
            crate::exec::stack::lemma_last_index_where_found(q.open, q.open.len() as int, cell_pred(), q.open.len() - 1);
        }
    }
}

/// The "in cell" rules keep [`cell_ok`].
pub proof fn lemma_cell_cell(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InCell), p, t),
    ensures
        outcome_parser(mode_in_cell(env, p, t)).stopped || cell_ok(outcome_parser(mode_in_cell(env, p, t))),
{
    hide(generate_implied_end_tags);
    hide(pop_until_cell_popped);
    hide(pop_until_popped);
    hide(clear_to_last_marker);
    assert(p.mode == Mode::InCell);
}

/// The "in row" and "in cell" rules keep [`cell_ok`]; the others do under
/// the hypothesis [`cells_kept`].
pub proof fn lemma_rules_cell(env: EncFns, r: Rules, p: Parser, t: Tok)
    requires
        rules_inv(r, p, t),
        cells_kept(),
    ensures
        outcome_parser(apply_rules(env, r, p, t)).stopped || cell_ok(outcome_parser(apply_rules(env, r, p, t))),
{
    if r == Rules::Html(Mode::InRow) {
        lemma_row_cell(env, p, t);
    } else if r == Rules::Html(Mode::InCell) {
        lemma_cell_cell(env, p, t);
    } else {
        assert(rules_inv(r, p, t) && r != Rules::Html(Mode::InCell) && r != Rules::Html(Mode::InRow));
    }
}

/// [`rules_inv`] gives what the executable rules need of the stack.
pub proof fn lemma_rules_inv_rooted(r: Rules, p: Parser, t: Tok)
    requires
        rules_inv(r, p, t),
    ensures
        rooted_needs(r, p),
{
    if p.mode != Mode::Initial && p.mode != Mode::BeforeHtml {
        if p.mode == Mode::Text {
            assert(p.open.drop_last()[0] == p.open[0]);
        }
        assert(stack_rooted(p));
    }
}

// ---------------------------------------------------------------------
// The run

/// Every rule application of a run from a parser satisfying [`rules_inv`]
/// meets `rooted_needs`, and the run's result satisfies [`reachable_inv`].
pub proof fn lemma_run_reach(env: EncFns, p: Parser, t: Tok, r: Rules, fuel: nat)
    requires
        rules_inv(r, p, t),
        cells_kept(),
    ensures
        run_needs(env, p, t, r, fuel),
        run(env, p, t, r, fuel) is Some ==> reachable_inv(run(env, p, t, r, fuel)->Some_0),
    decreases fuel,
{
    if fuel > 0 {
        let o = apply_rules(env, r, p, t);
        lemma_rules_inv_rooted(r, p, t);
        lemma_rules_reach(env, r, p, t);
        lemma_rules_cell(env, r, p, t);
        crate::termination::lemma_rules_edges(env, r, p, t);
        crate::exec::step::lemma_rules_tok(env, r, p, t);
        match o {
            Outcome::Done(q) => {},
            Outcome::Reprocess(q, t2) => {
                if !q.stopped {
                    crate::exec::step::lemma_tok_next_ok(t, t2);
                    assert(rules_inv(Rules::Html(q.mode), q, t2));
                    lemma_run_reach(env, q, t2, Rules::Html(q.mode), (fuel - 1) as nat);
                }
            },
            Outcome::Using(m, q, t2) => {
                if !q.stopped {
                    crate::exec::step::lemma_tok_next_ok(t, t2);
                    assert(rules_inv(Rules::Html(m), q, t2));
                    lemma_run_reach(env, q, t2, Rules::Html(m), (fuel - 1) as nat);
                }
            },
        }
    }
}

/// A classified token is tagged.
pub proof fn lemma_classify_ok(token: Token)
    ensures
        crate::exec::modes::initial::tok_ok(classify(token)),
{
}

/// The dispatcher's rules for a running parser satisfying
/// [`reachable_inv`] meet [`rules_inv`].
pub proof fn lemma_dispatch_inv(p1: Parser, t: Tok)
    requires
        reachable_inv(p1),
        !p1.stopped,
        crate::exec::modes::initial::tok_ok(t),
    ensures
        rules_inv(dispatcher(p1, t), p1, t),
{
    crate::termination::lemma_dispatcher_rules_ok(p1, t);
}

/// **The step keeps the reachable-state invariant** (Phase 4 item 4.10):
/// for a parser satisfying [`reachable_inv`], under the hypothesis
/// [`cells_kept`], every rule application of `dispatch(env, p, token)`
/// meets `rooted_needs` ([`dispatch_needs`], what the executable step
/// needs), and the new state satisfies [`reachable_inv`].
pub proof fn lemma_dispatch_reach(env: EncFns, p: Parser, token: Token)
    requires
        reachable_inv(p),
        cells_kept(),
    ensures
        dispatch_needs(env, p, token),
        reachable_inv(dispatch(env, p, token).0),
{
    hide(run);
    hide(run_needs);
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
    let r = dispatcher(p1, t);
    assert(reachable_inv(p1));
    lemma_dispatch_inv(p1, t);
    crate::termination::theorem_dispatch_total(env, p1, t);
    lemma_run_reach(env, p1, t, r, fuel_bound(p1));
    if p0.skip_lf {
        assert(dispatch(env, p, token).0 == tree_construction(env, p1, t));
    } else {
        assert(p1 == p0);
    }
}

// ---------------------------------------------------------------------
// The initial states

/// A new parser satisfies [`reachable_inv`].
pub proof fn lemma_new_parser_reach(url: Seq<u32>, scripting: bool, tentative: bool)
    ensures
        reachable_inv(new_parser(url, scripting, tentative)),
{
    let p = new_parser(url, scripting, tentative);
    assert(crate::termination::templates_in(p.open, 0) == 0);
}

/// The fragment parser satisfies [`reachable_inv`].
pub proof fn lemma_fragment_parser_reach(ctx: Context, scripting: bool)
    ensures
        reachable_inv(fragment_parser(ctx, scripting).0),
{
    hide(reset_from);
    hide(annotation_html);
    let (d4, ctx_id, root, fragment) = crate::exec::step::fragment_doc(ctx);
    let d0 = dom::set_mode(dom::new_document(seq![]), ctx.mode);
    let (d1, c1) = dom::create_node(d0, crate::exec::step::context_kind(ctx));
    let (d2, r2) = dom::create_node(d1, crate::exec::step::root_kind());
    lemma_insert_len(d2, r2, 0, None);
    assert(d4.nodes.len() == 4);
    assert(root == 2);
    crate::exec::step::lemma_tag_of_html();
    let html = seq![0x68u32, 0x74, 0x6d, 0x6c];
    let ctx_tok = TagTok { name: ctx.name, tag: tag_of(ctx.name), attrs: ctx.attrs, self_closing: false };
    let ctx_el = Elem { id: ctx_id, ns: ctx.ns, tag: ctx_tok.tag, name: ctx.name, annotation_html: annotation_html(ctx.ns, ctx_tok) };
    let root_el = Elem { id: root, ns: Namespace::Html, tag: Tag::Html, name: html, annotation_html: false };
    let p0 = Parser {
        doc: d4,
        context: Some(ctx_el),
        open: seq![root_el],
        redirect: Some((root, fragment)),
        template_modes: if is_html(ctx_el, Tag::Template) {
            seq![Mode::InTemplate]
        } else {
            seq![]
        },
        tentative: false,
        ..new_parser(seq![], scripting, false)
    };
    let p1 = Parser { doc: d4, ..p0 };
    assert(crate::termination::templates_in(p1.open, 1) == crate::termination::templates_in(p1.open, 0));
    assert(good(p1));
    assert(crate::termination::helpers_ranking::count_ok(p1));
    lemma_reset_keeps(p1);
    crate::termination::helpers_ranking::lemma_reset_modes_ok(p1);
    let p2 = reset_insertion_mode(p1);
    assert(reset_from(p1, 0) != Mode::InCell) by {
        reveal(reset_from);
        if is_html(ctx_el, Tag::Template) {
            assert(p1.template_modes.last() == Mode::InTemplate);
        }
    }
    let p3 = if is_html(ctx_el, Tag::Form) {
        Parser { form: Some(ctx_id), ..p2 }
    } else {
        p2
    };
    assert(fragment_parser(ctx, scripting).0 == p3);
    assert(reach_core(p3));
}

// ---------------------------------------------------------------------
// Reachable parsers

/// The parser after the tokens `tokens`, one [`dispatch`] step each.
pub open spec fn dispatch_steps(env: EncFns, p: Parser, tokens: Seq<Token>) -> Parser
    decreases tokens.len(),
{
    if tokens.len() == 0 {
        p
    } else {
        dispatch_steps(env, dispatch(env, p, tokens[0]).0, tokens.drop_first())
    }
}

/// [`reachable_inv`] survives every sequence of steps.
pub proof fn lemma_steps_reach(env: EncFns, p: Parser, tokens: Seq<Token>)
    requires
        reachable_inv(p),
        cells_kept(),
    ensures
        reachable_inv(dispatch_steps(env, p, tokens)),
    decreases tokens.len(),
{
    if tokens.len() > 0 {
        lemma_dispatch_reach(env, p, tokens[0]);
        lemma_steps_reach(env, dispatch(env, p, tokens[0]).0, tokens.drop_first());
    }
}

/// A running parser satisfying [`reachable_inv`] handles every token within
/// its fuel (`termination::theorem_dispatch_total`'s hypothesis holds).
pub proof fn lemma_reach_total(env: EncFns, q: Parser)
    requires
        reachable_inv(q),
    ensures
        !q.stopped ==> forall|t: Tok| #[trigger] run(env, q, t, dispatcher(q, t), fuel_bound(q)) is Some,
{
    if !q.stopped {
        assert forall|t: Tok| #[trigger] run(env, q, t, dispatcher(q, t), fuel_bound(q)) is Some by {
            crate::termination::theorem_dispatch_total(env, q, t);
        }
    }
}

/// **Every reachable parser satisfies the reachable-state invariant**
/// (Phase 4 item 4.10): for every parser reached from [`new_parser`] or from
/// [`fragment_parser`] by [`dispatch`] steps (any tokens, any encoding
/// functions), [`reachable_inv`] holds: a parser that has not stopped
/// satisfies `termination::modes_ok`, so `termination::theorem_dispatch_total`
/// applies to it and the tree construction stage never takes its fallback;
/// and every rule application of its next step meets what the executable
/// step needs ([`lemma_dispatch_reach`]).
///
/// Hypothesis: [`cells_kept`] (not yet proven; see there). Not stated:
/// `parser_wf` of reachable parsers (`clazel_dom::spec::wf` of the
/// document and the ids of the parse state), which the executable step
/// keeps (`exec::step::step` ensures `parser_inv`) but which has no
/// spec-level proof yet.
pub proof fn theorem_reachable(
    env: EncFns,
    url: Seq<u32>,
    ctx: Context,
    scripting: bool,
    tentative: bool,
    tokens: Seq<Token>,
)
    requires
        cells_kept(),
    ensures
        reachable_inv(dispatch_steps(env, new_parser(url, scripting, tentative), tokens)),
        reachable_inv(dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens)),
        ({
            let q = dispatch_steps(env, new_parser(url, scripting, tentative), tokens);
            !q.stopped ==> forall|t: Tok| #[trigger] run(env, q, t, dispatcher(q, t), fuel_bound(q)) is Some
        }),
        ({
            let q = dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens);
            !q.stopped ==> forall|t: Tok| #[trigger] run(env, q, t, dispatcher(q, t), fuel_bound(q)) is Some
        }),
{
    lemma_new_parser_reach(url, scripting, tentative);
    lemma_fragment_parser_reach(ctx, scripting);
    lemma_steps_reach(env, new_parser(url, scripting, tentative), tokens);
    lemma_steps_reach(env, fragment_parser(ctx, scripting).0, tokens);
    lemma_reach_total(env, dispatch_steps(env, new_parser(url, scripting, tentative), tokens));
    lemma_reach_total(env, dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens));
}

} // verus!
