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
    ensures
        run_needs(env, p, t, r, fuel),
        run(env, p, t, r, fuel) is Some ==> reachable_inv(run(env, p, t, r, fuel)->Some_0),
    decreases fuel,
{
    if fuel > 0 {
        let o = apply_rules(env, r, p, t);
        lemma_rules_inv_rooted(r, p, t);
        lemma_rules_reach(env, r, p, t);
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
        tok_plain(t),
    ensures
        rules_inv(dispatcher(p1, t), p1, t),
{
    crate::termination::lemma_dispatcher_rules_ok(p1, t);
}

/// **The step keeps the reachable-state invariant** (Phase 4 item 4.10):
/// for a parser satisfying [`reachable_inv`], every rule application of
/// `dispatch(env, p, token)` meets `rooted_needs` ([`dispatch_needs`], what
/// the executable step needs), and the new state satisfies
/// [`reachable_inv`].
pub proof fn lemma_dispatch_reach(env: EncFns, p: Parser, token: Token)
    requires
        reachable_inv(p),
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
    crate::theorems::equivalence::lemma_classify_plain(token);
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
    clazel_dom::lemmas::theorem_new_document_wf(url);
    assert(p.doc.nodes.len() == 1 && p.doc.nodes[0].kind is Document);
    assert(super::doc::html_plain(p.doc, p.context)) by {
        reveal(super::doc::html_plain);
    }
    assert(fmt_plain(p.formatting)) by {
        reveal(fmt_plain);
    }
    super::doc::lemma_dinv_intro(p);
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
    crate::theorems::reachable::lemma_fragment_doc_ok(ctx);
    assert(crate::exec::frame::kind_kept(crate::exec::step::root_kind(), d4.nodes[root as int].kind));
    assert(crate::exec::frame::elem_ok(d4, root_el));
    lemma_fragment_plain(ctx, Some(ctx_el));
    assert(fmt_plain(p1.formatting)) by {
        reveal(fmt_plain);
    }
    assert forall|i: int| 0 <= i < p1.open.len() implies crate::exec::frame::elem_ok(d4, #[trigger] p1.open[i]) by {
        assert(p1.open[i] == root_el);
    }
    super::doc::lemma_dinv_intro(p1);
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

/// The fragment parser's arena is `doc::html_plain` but for the context
/// element (node 1): the root `html` element has no attributes.
pub proof fn lemma_fragment_plain(ctx: Context, c: Option<Elem>)
    requires
        c is Some && c->Some_0.id == 1,
    ensures
        super::doc::html_plain(crate::exec::step::fragment_doc(ctx).0, c),
{
    hide(dom::insert);
    hide(dom::wf);
    hide(tag_of);
    let dn = dom::new_document(seq![]);
    assert(dn.nodes.len() == 1 && dn.nodes[0].kind is Document);
    assert(super::doc::html_plain(dn, c)) by {
        reveal(super::doc::html_plain);
    }
    crate::exec::step::lemma_new_doc_extends(seq![], ctx.mode);
    clazel_dom::lemmas::theorem_set_mode_wf(dn, ctx.mode);
    super::doc::lemma_set_mode_plain(dn, ctx.mode, c);
    let d0 = dom::set_mode(dn, ctx.mode);
    assert(d0.nodes.len() == 1);
    crate::exec::frame::lemma_create_extends(d0, crate::exec::step::context_kind(ctx));
    let (d1, ctx_id) = dom::create_node(d0, crate::exec::step::context_kind(ctx));
    assert forall|i: int| 0 <= i < d0.nodes.len() && i != 1 implies (#[trigger] d1.nodes[i]).kind == d0.nodes[i].kind by {
        assert(d1.nodes[i] == d0.nodes[i]);
    }
    super::doc::lemma_plain_update(d0, d1, 1, c);
    crate::exec::frame::lemma_create_extends(d1, crate::exec::step::root_kind());
    super::doc::lemma_create_plain(d1, crate::exec::step::root_kind(), c);
    let (d2, root) = dom::create_node(d1, crate::exec::step::root_kind());
    assert(ctx_id == 1 && root == 2 && d2.nodes.len() == 3);
    assert(d2.nodes[0] == d0.nodes[0]);
    assert(d2.nodes[root as int].kind == crate::exec::step::root_kind());
    assert(!dom::is_inclusive_ancestor(d2, root, 0)) by {
        assert(d2.nodes[0].parent is None);
    }
    crate::exec::frame::lemma_insert_extends(d2, root, 0, None);
    super::doc::lemma_insert_plain(d2, root, 0, None, c);
    let d3 = dom::append(d2, 0, root);
    super::doc::lemma_create_plain(d3, NodeKind::DocumentFragment { host: None }, c);
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
/// `parser_wf` of reachable parsers (`clazel_dom::spec::wf` of the document
/// and the ids of the parse state) is the companion theorem
/// `theorems::reachable::theorem_reachable_wf`.
pub proof fn theorem_reachable(
    env: EncFns,
    url: Seq<u32>,
    ctx: Context,
    scripting: bool,
    tentative: bool,
    tokens: Seq<Token>,
)
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
