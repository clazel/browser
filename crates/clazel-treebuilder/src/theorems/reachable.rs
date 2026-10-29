//! The document theorems for every reachable parser (Phase 4 item 4.9):
//! [`theorem_reachable_wf`] (every parser reachable from `new_parser` or
//! `fragment_parser` has a well-formed document, every id of its parse
//! state in the document, and, until it stops, `parser_wf` and the head
//! element pointer's fact; and no element has two entries in its list of
//! active formatting elements), and the corollaries of
//! `theorem_doc_wf`, `theorem_open_elements_in_doc` and
//! `theorem_nodes_per_token` for a step from every reachable parser, with
//! no hypotheses.
//!
//! The proof. [`reach_wf`] is `invariant::reachable_inv` and those facts.
//! Both initial states have it ([`lemma_new_parser_wf`],
//! [`lemma_fragment_parser_wf`]). A step from a stopped parser changes only
//! its actions and tokenizer switch. A step from a running one meets the
//! hypotheses of the three step theorems: `parser_wf` is the document's
//! facts and `termination::modes_ok`, which `reachable_inv` gives;
//! `dispatch_needs` comes from `reachable::run::lemma_dispatch_reach`;
//! and `theorem_nodes_per_token` keeps `open_elements::fmt_unique`.
//!
//! Not stated: `termination::modes_ok` of a stopped parser (the rule that
//! stops parsing may have changed the modes half way; a stopped parser
//! takes no further step, so nothing needs it). The rest of
//! `invariant::parser_inv` for running reachable parsers (`tags_wf` and
//! `templates_wf`, which `reachable_inv` carries) is
//! `super::parser_inv::theorem_reachable_parser_inv`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The document facts of a reachable parser, with
/// `invariant::reachable_inv`: the document is well formed, every id of
/// the parse state is a node of it, no two entries of the list of active
/// formatting elements are for the same element, and until parsing stops
/// the parser has `parser_wf`, its head element pointer names an HTML
/// `head` element (`invariant::head_ok`), and no two entries of the stack
/// of open elements are for the same element
/// (`independent::equivalence_foreign::open_distinct`); every entry of the
/// list is for an HTML element (`open_elements::fh`); and the insertion
/// target redirection map maps neither the Document nor a node to itself
/// ([`redirect_ok`]).
pub open spec fn reach_wf(p: Parser) -> bool {
    &&& reachable_inv(p)
    &&& dom::wf(p.doc)
    &&& ids_in_doc(p)
    &&& super::open_elements::fmt_unique(p)
    &&& !p.stopped ==> parser_wf(p) && head_ok(p)
    &&& !p.stopped ==> crate::independent::equivalence_foreign::open_distinct(p.open)
    &&& super::open_elements::fh(p)
    &&& redirect_ok(p)
}

/// The insertion target redirection map has no entry for the Document
/// (node 0) and does not map a node to itself: it is empty, or the
/// fragment case's entry from the root `html` element to the fragment.
pub open spec fn redirect_ok(p: Parser) -> bool {
    p.redirect is None || (p.redirect->Some_0.0 != 0 && p.redirect->Some_0.0 != p.redirect->Some_0.1)
}

/// A new parser has [`reach_wf`].
pub proof fn lemma_new_parser_wf(url: Seq<u32>, scripting: bool, tentative: bool)
    ensures
        reach_wf(new_parser(url, scripting, tentative)),
{
    crate::reachable::run::lemma_new_parser_reach(url, scripting, tentative);
    clazel_dom::lemmas::theorem_new_document_wf(url);
}

/// The fragment parser's arena is well formed and holds the context
/// element, root and the fragment (`exec::step::fragment_doc_ok`).
pub proof fn lemma_fragment_doc_ok(ctx: Context)
    ensures
        ({
            let (d, c, r, f) = crate::exec::step::fragment_doc(ctx);
            crate::exec::step::fragment_doc_ok(ctx, d, c, r, f)
        }),
{
    hide(dom::insert);
    hide(dom::wf);
    hide(tag_of);
    let dn = dom::new_document(seq![]);
    crate::exec::step::lemma_new_doc_extends(seq![], ctx.mode);
    clazel_dom::lemmas::theorem_set_mode_wf(dn, ctx.mode);
    let d0 = dom::set_mode(dn, ctx.mode);
    assert(d0.nodes.len() == 1);
    crate::exec::frame::lemma_create_extends(d0, crate::exec::step::context_kind(ctx));
    let (d1, ctx_id) = dom::create_node(d0, crate::exec::step::context_kind(ctx));
    crate::exec::frame::lemma_create_extends(d1, crate::exec::step::root_kind());
    let (d2, root) = dom::create_node(d1, crate::exec::step::root_kind());
    assert(ctx_id == 1 && root == 2 && d2.nodes.len() == 3);
    assert(d2.nodes[0] == d0.nodes[0]);
    assert(d2.nodes[root as int].kind == crate::exec::step::root_kind());
    assert(!dom::is_inclusive_ancestor(d2, root, 0)) by {
        assert(d2.nodes[0].parent is None);
    }
    crate::exec::frame::lemma_insert_extends(d2, root, 0, None);
    clazel_dom::lemmas::theorem_append_wf(d2, 0, root);
    let d3 = dom::append(d2, 0, root);
    assert(d3.nodes.len() == 3);
    crate::exec::frame::lemma_create_extends(d3, NodeKind::DocumentFragment { host: None });
    let (d4, fragment) = dom::create_node(d3, NodeKind::DocumentFragment { host: None });
    crate::exec::frame::lemma_doc_extends_trans(dn, d0, d1);
    crate::exec::frame::lemma_doc_extends_trans(dn, d1, d2);
    crate::exec::frame::lemma_doc_extends_trans(dn, d2, d3);
    crate::exec::frame::lemma_doc_extends_trans(dn, d3, d4);
    crate::exec::frame::lemma_doc_extends_trans(d1, d2, d3);
    crate::exec::frame::lemma_doc_extends_trans(d1, d3, d4);
    crate::exec::frame::lemma_doc_extends_trans(d2, d3, d4);
    crate::exec::step::lemma_templates_from_new(seq![], d4);
    assert(crate::exec::frame::kind_kept(d1.nodes[ctx_id as int].kind, d4.nodes[ctx_id as int].kind));
    assert(crate::exec::frame::kind_kept(d2.nodes[root as int].kind, d4.nodes[root as int].kind));
    assert(crate::exec::step::fragment_doc(ctx) == (d4, ctx_id, root, fragment));
}

/// The fragment parser has [`reach_wf`].
pub proof fn lemma_fragment_parser_wf(ctx: Context, scripting: bool)
    ensures
        reach_wf(fragment_parser(ctx, scripting).0),
{
    hide(reset_from);
    hide(annotation_html);
    crate::reachable::run::lemma_fragment_parser_reach(ctx, scripting);
    lemma_fragment_doc_ok(ctx);
    let (d4, ctx_id, root, fragment) = crate::exec::step::fragment_doc(ctx);
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
    assert(p1.open == seq![crate::exec::step::root_elem(root)]);
    crate::exec::step::lemma_fragment_start_inv(ctx, p1, ctx_id, root, fragment);
    let p2 = reset_insertion_mode(p1);
    assert(ids_in_doc(p2) && parser_wf(p2) && head_ok(p2));
    let p3 = if is_html(ctx_el, Tag::Form) {
        Parser { form: Some(ctx_id), ..p2 }
    } else {
        p2
    };
    assert(fragment_parser(ctx, scripting).0 == p3);
    assert(ids_in_doc(p3));
    assert(super::open_elements::fmt_unique(p3));
    assert(crate::independent::equivalence_foreign::open_distinct(p3.open));
}

/// One step keeps [`reach_wf`].
pub proof fn lemma_dispatch_wf(env: EncFns, p: Parser, token: Token)
    requires
        reach_wf(p),
    ensures
        reach_wf(dispatch(env, p, token).0),
{
    crate::reachable::run::lemma_dispatch_reach(env, p, token);
    if !p.stopped {
        super::open_elements::lemma_dispatch(env, p, token);
        super::open_elements::lemma_kpu(p, dispatch(env, p, token).0);
        super::open_elements::theorem_open_elements_in_doc(env, p, token);
        super::open_elements::theorem_doc_wf(env, p, token);
        super::nodes::theorem_nodes_per_token(env, p, token);
        super::open_elements::theorem_open_distinct(env, p, token);
        let q = dispatch(env, p, token).0;
        assert(!q.stopped ==> crate::termination::modes_ok(q));
    }
}

/// [`reach_wf`] survives every sequence of steps.
pub proof fn lemma_steps_wf(env: EncFns, p: Parser, tokens: Seq<Token>)
    requires
        reach_wf(p),
    ensures
        reach_wf(crate::reachable::run::dispatch_steps(env, p, tokens)),
    decreases tokens.len(),
{
    if tokens.len() > 0 {
        lemma_dispatch_wf(env, p, tokens[0]);
        lemma_steps_wf(env, dispatch(env, p, tokens[0]).0, tokens.drop_first());
    }
}

/// **Every reachable parser has a well-formed document** (Phase 4 item
/// 4.9): for every parser reached from `new_parser` or from
/// `fragment_parser` by `dispatch` steps (any tokens, any encoding
/// functions), [`reach_wf`] holds: `clazel_dom::spec::wf` of the document,
/// `invariant::ids_in_doc`, no element with two entries in the list of
/// active formatting elements (`open_elements::fmt_unique`), and until
/// parsing stops `invariant::parser_wf` and `invariant::head_ok`, with
/// `invariant::reachable_inv`. No hypotheses.
pub proof fn theorem_reachable_wf(
    env: EncFns,
    url: Seq<u32>,
    ctx: Context,
    scripting: bool,
    tentative: bool,
    tokens: Seq<Token>,
)
    ensures
        reach_wf(crate::reachable::run::dispatch_steps(env, new_parser(url, scripting, tentative), tokens)),
        reach_wf(crate::reachable::run::dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens)),
{
    lemma_new_parser_wf(url, scripting, tentative);
    lemma_fragment_parser_wf(ctx, scripting);
    lemma_steps_wf(env, new_parser(url, scripting, tentative), tokens);
    lemma_steps_wf(env, fragment_parser(ctx, scripting).0, tokens);
}

/// The step from a parser with [`reach_wf`] keeps the document well formed
/// and the ids of the parse state in it, and creates at most
/// `44 + 6 T + 2 F + P (F + 1)` nodes.
pub proof fn lemma_step_doc(env: EncFns, p: Parser, token: Token)
    requires
        reach_wf(p),
    ensures
        dom::wf(dispatch(env, p, token).0.doc),
        ids_in_doc(dispatch(env, p, token).0),
        dispatch(env, p, token).0.stopped || head_ok(dispatch(env, p, token).0),
        dispatch(env, p, token).0.doc.nodes.len() <= p.doc.nodes.len() + 44 + 6 * p.template_modes.len() + 2
            * p.formatting.len() + p.pending_table_text.len() * (p.formatting.len() + 1),
{
    lemma_dispatch_wf(env, p, token);
    if !p.stopped {
        crate::reachable::run::lemma_dispatch_reach(env, p, token);
        super::nodes::theorem_nodes_per_token(env, p, token);
    } else {
        let (pp, ff) = (p.pending_table_text.len() as int, p.formatting.len() as int);
        assert(0 <= pp * (ff + 1)) by (nonlinear_arith)
            requires
                pp >= 0,
                ff >= 0,
        ;
    }
}

/// **The document stays well formed, from every reachable parser**: the
/// corollary of `open_elements::theorem_doc_wf` for every parser reached
/// from `new_parser` or `fragment_parser` by `dispatch` steps, with no
/// hypotheses: the next step's document is well formed.
pub proof fn theorem_reachable_doc_wf(
    env: EncFns,
    url: Seq<u32>,
    ctx: Context,
    scripting: bool,
    tentative: bool,
    tokens: Seq<Token>,
    token: Token,
)
    ensures
        dom::wf(dispatch(env, crate::reachable::run::dispatch_steps(env, new_parser(url, scripting, tentative), tokens), token).0.doc),
        dom::wf(dispatch(env, crate::reachable::run::dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens), token).0.doc),
{
    theorem_reachable_wf(env, url, ctx, scripting, tentative, tokens);
    lemma_step_doc(env, crate::reachable::run::dispatch_steps(env, new_parser(url, scripting, tentative), tokens), token);
    lemma_step_doc(env, crate::reachable::run::dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens), token);
}

/// **The ids of the parse state stay in the document, from every reachable
/// parser**: the corollary of `open_elements::theorem_open_elements_in_doc`
/// for every parser reached from `new_parser` or `fragment_parser` by
/// `dispatch` steps, with no hypotheses: after the next step every id on
/// the stack of open elements and in the list of active formatting
/// elements is an element of the document with the record's namespace and
/// local name, the head and form element pointers, the context and the
/// redirection map name nodes of it, and until parsing stops the head
/// element pointer names an HTML `head` element.
pub proof fn theorem_reachable_open_elements_in_doc(
    env: EncFns,
    url: Seq<u32>,
    ctx: Context,
    scripting: bool,
    tentative: bool,
    tokens: Seq<Token>,
    token: Token,
)
    ensures
        ({
            let q = dispatch(env, crate::reachable::run::dispatch_steps(env, new_parser(url, scripting, tentative), tokens), token).0;
            ids_in_doc(q) && (q.stopped || head_ok(q))
        }),
        ({
            let q = dispatch(env, crate::reachable::run::dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens), token).0;
            ids_in_doc(q) && (q.stopped || head_ok(q))
        }),
{
    theorem_reachable_wf(env, url, ctx, scripting, tentative, tokens);
    lemma_step_doc(env, crate::reachable::run::dispatch_steps(env, new_parser(url, scripting, tentative), tokens), token);
    lemma_step_doc(env, crate::reachable::run::dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens), token);
}

/// **Nodes per token, from every reachable parser**: the corollary of
/// `nodes::theorem_nodes_per_token` for every parser `p` reached from
/// `new_parser` or `fragment_parser` by `dispatch` steps, with no
/// hypotheses (in particular not `open_elements::fmt_unique`, which
/// [`theorem_reachable_wf`] proves of every reachable parser): the next
/// step creates at most `44 + 6 T + 2 F + P (F + 1)` nodes, with T, F and
/// P the lengths of `p`'s stack of template insertion modes, list of
/// active formatting elements and pending table character tokens.
pub proof fn theorem_reachable_nodes_per_token(
    env: EncFns,
    url: Seq<u32>,
    ctx: Context,
    scripting: bool,
    tentative: bool,
    tokens: Seq<Token>,
    token: Token,
)
    ensures
        ({
            let p = crate::reachable::run::dispatch_steps(env, new_parser(url, scripting, tentative), tokens);
            dispatch(env, p, token).0.doc.nodes.len() <= p.doc.nodes.len() + 44 + 6 * p.template_modes.len() + 2
                * p.formatting.len() + p.pending_table_text.len() * (p.formatting.len() + 1)
        }),
        ({
            let p = crate::reachable::run::dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens);
            dispatch(env, p, token).0.doc.nodes.len() <= p.doc.nodes.len() + 44 + 6 * p.template_modes.len() + 2
                * p.formatting.len() + p.pending_table_text.len() * (p.formatting.len() + 1)
        }),
{
    theorem_reachable_wf(env, url, ctx, scripting, tentative, tokens);
    lemma_step_doc(env, crate::reachable::run::dispatch_steps(env, new_parser(url, scripting, tentative), tokens), token);
    lemma_step_doc(env, crate::reachable::run::dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens), token);
}

} // verus!
