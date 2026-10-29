//! The preconditions of the W3C equivalence lemmas
//! (`independent::equivalence`, `independent::equivalence_body`,
//! `independent::equivalence_foreign`) that are facts of every reachable
//! parser, proven from [`super::reachable::reach_wf`]; the foreign content
//! equivalence for reachable parsers without its stack hypothesis
//! ([`theorem_reachable_foreign_content`]); and the "in frameset" and "in
//! cell" equivalences for reachable parsers with no hypothesis
//! ([`theorem_reachable_frameset_cell`]).
//!
//! Discharged here, for every parser reached from `new_parser` or
//! `fragment_parser` by `dispatch` steps ([`theorem_reachable_w3c_facts`]):
//! `document_rooted` and `no_document_redirect` (always); `aa_wf` and
//! `tags_wf` (until parsing stops); `place_stable`, and `place_stable` of
//! the stack with the `head` element pushed, which "after head" needs,
//! `html_only_at_root`, which "in frameset" needs (until parsing stops,
//! once the `html` element exists: in every mode but "initial" and "before
//! html"); `open_distinct` (until parsing stops); in the "in cell" mode, a
//! `td` or `th` element in table scope, which "in cell" needs (from
//! `invariant::html_once` and `invariant::cell_scoped`, parts of
//! `invariant::reachable_inv`). For a token the tokenizer emits
//! (`classify`), `token_tagged`, `tok_tagged` and `attrs_plain` of its
//! attributes ([`lemma_classify_plain`]).
//!
//! Not discharged: the preconditions that exclude the inputs where the two
//! texts differ (they are not facts of states; `w3c_aa_agrees` and "in
//! table text"'s nonempty pending list among them), and `element_plain` of
//! the `html` and `body` elements ("in body"), which needs a fact about the
//! attributes of document nodes that no proof here carries.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What a well-formed arena gives: node 0 is the Document, every parent
/// and every child of the Document is a node of the arena.
pub proof fn lemma_wf_nodes(d: Document)
    requires
        dom::wf(d),
    ensures
        d.nodes.len() > 0,
        d.nodes[0].kind is Document,
        forall|i: int| 0 <= i < d.nodes.len() && (#[trigger] d.nodes[i]).parent is Some ==> dom::valid(d, d.nodes[i].parent->Some_0),
        forall|j: int| 0 <= j < d.nodes[0].children.len() ==> dom::valid(d, #[trigger] d.nodes[0].children[j]),
{
    let paths = clazel_dom::lemmas::lemma_wf_witness(d);
    assert forall|j: int| 0 <= j < d.nodes[0].children.len() implies dom::valid(d, #[trigger] d.nodes[0].children[j]) by {
        assert(0 <= 0 < d.nodes.len());
        let c = d.nodes[0].children[j];
        assert(c < d.nodes.len());
    }
}

/// Once the `html` element exists (every mode but "initial" and "before
/// html"), the stack of a running parser with [`reach_core`] is rooted at
/// it.
pub proof fn lemma_core_rooted(p: Parser)
    requires
        reach_core(p),
        p.mode != Mode::Initial,
        p.mode != Mode::BeforeHtml,
    ensures
        p.open.len() > 0,
        is_html(p.open[0], Tag::Html),
{
    if p.mode == Mode::Text {
        let o = p.open.drop_last();
        assert(o.len() >= 1);
        assert(o[0] == p.open[0]);
    }
}

/// [`reach_wf`](super::reachable::reach_wf) gives `document_rooted` and
/// `no_document_redirect`.
pub proof fn lemma_reach_doc(p: Parser)
    requires
        super::reachable::reach_wf(p),
    ensures
        crate::independent::equivalence::document_rooted(p),
        crate::independent::equivalence::no_document_redirect(p),
{
    lemma_wf_nodes(p.doc);
}

/// [`reach_wf`](super::reachable::reach_wf) of a running parser gives
/// `aa_wf` and `tags_wf`.
pub proof fn lemma_reach_aa_wf(p: Parser)
    requires
        super::reachable::reach_wf(p),
        !p.stopped,
    ensures
        crate::independent::equivalence_body::aa_wf(p),
        tags_wf(p),
{
    let n = p.doc.nodes.len();
    assert forall|j: int| 0 <= j < p.open.len() implies (#[trigger] p.open[j]).id < n && elem_tagged(p.open[j]) by {
        assert(elem_in_doc(p.doc, p.open[j]));
    }
    let f = p.formatting;
    assert forall|j: int| 0 <= j < f.len() implies crate::independent::equivalence_body::fmt_entry_ok(#[trigger] f[j], n) by {
        if f[j] is Entry {
            assert(elem_in_doc(p.doc, f[j]->Entry_elem));
        }
    }
    assert forall|j: int, k: int|
        #![trigger f[j], f[k]]
        0 <= j < f.len() && 0 <= k < f.len() && f[j] is Entry && f[k] is Entry && f[j]->Entry_elem.id == f[k]->Entry_elem.id
            implies f[j]->Entry_elem.tag == f[k]->Entry_elem.tag by {
        if j != k {
            assert(f[j]->Entry_elem.id != f[k]->Entry_elem.id);
        }
    }
}

/// [`reach_wf`](super::reachable::reach_wf) of a running parser in a mode
/// after "before html" gives `place_stable`, also of the stack with the
/// `head` element pushed ("after head").
pub proof fn lemma_reach_place_stable(p: Parser)
    requires
        super::reachable::reach_wf(p),
        !p.stopped,
        p.mode != Mode::Initial,
        p.mode != Mode::BeforeHtml,
    ensures
        crate::independent::equivalence::place_stable(p),
        p.head is Some ==> crate::independent::equivalence::place_stable(
            push(p, crate::independent::early::w3c_head_elem(p)),
        ),
{
    lemma_wf_nodes(p.doc);
    lemma_core_rooted(p);
    assert forall|i: int| 0 <= i < p.open.len() implies dom::valid(p.doc, (#[trigger] p.open[i]).id) && match p.doc.nodes[p.open[i].id as int].parent {
        Some(par) => dom::valid(p.doc, par),
        None => true,
    } by {
        assert(elem_in_doc(p.doc, p.open[i]));
    }
    if p.head is Some {
        let e = crate::independent::early::w3c_head_elem(p);
        let q = push(p, e);
        assert(elem_in_doc(p.doc, head_elem(p.head->Some_0)));
        assert forall|i: int| 0 <= i < q.open.len() implies dom::valid(q.doc, (#[trigger] q.open[i]).id) && match q.doc.nodes[q.open[i].id as int].parent {
            Some(par) => dom::valid(q.doc, par),
            None => true,
        } by {
            if i < p.open.len() {
                assert(q.open[i] == p.open[i]);
                assert(elem_in_doc(p.doc, p.open[i]));
            }
        }
        assert(q.open[0] == p.open[0]);
    }
}

/// A token's attributes as the tree builder sees them have no namespace
/// and no prefix, and its tag is the classification of its name.
pub proof fn lemma_classify_plain(token: Token)
    ensures
        crate::exec::modes::initial::tok_ok(classify(token)),
        crate::independent::equivalence::token_tagged(classify(token)),
        classify(token) is Start ==> crate::independent::equivalence_body::attrs_plain(classify(token)->Start_0.attrs),
        classify(token) is End ==> crate::independent::equivalence_body::attrs_plain(classify(token)->End_0.attrs),
{
    crate::reachable::run::lemma_classify_ok(token);
    match token {
        Token::StartTag { name, attrs, self_closing } => {
            let a = tok_attrs(attrs);
            assert forall|i: int| 0 <= i < a.len() implies (#[trigger] a[i]).namespace is None && a[i].prefix is None by {
                assert(a[i] == tok_attr(attrs[i]));
            }
        },
        Token::EndTag { name, attrs, self_closing } => {
            let a = tok_attrs(attrs);
            assert forall|i: int| 0 <= i < a.len() implies (#[trigger] a[i]).namespace is None && a[i].prefix is None by {
                assert(a[i] == tok_attr(attrs[i]));
            }
        },
        _ => {},
    }
}

/// The predicate of the "in cell" lemma's precondition: "a td element or a
/// th element".
pub open spec fn td_or_th() -> spec_fn(Elem) -> bool {
    |e: Elem| is_html(e, Tag::Td) || is_html(e, Tag::Th)
}

/// The stack of a parser in the "in cell" mode has a `td` or `th` element
/// in table scope (the "in cell" lemma's precondition).
pub open spec fn cell_in_table_scope(p: Parser) -> bool {
    in_scope_from(p.open, p.open.len() as int, td_or_th(), Scope::Table)
}

/// [`reach_core`] of a running parser in a mode after "before html" gives
/// `html_only_at_root`, and in the "in cell" mode a cell in table scope.
pub proof fn lemma_core_html_cell(p: Parser)
    requires
        reach_core(p),
        p.mode != Mode::Initial,
        p.mode != Mode::BeforeHtml,
    ensures
        crate::independent::equivalence::html_only_at_root(p),
        p.mode == Mode::InCell ==> cell_in_table_scope(p),
{
    lemma_core_rooted(p);
    if p.mode == Mode::InCell {
        crate::reachable::cells::lemma_cell_top(p.open);
        crate::reachable::walls::lemma_scoped_in_scope(p.open, p.open.len() as int);
        assert(cell_pred() =~= td_or_th());
    }
}

/// The facts of a reachable parser the W3C equivalence lemmas assume.
pub open spec fn w3c_facts(p: Parser) -> bool {
    &&& crate::independent::equivalence::document_rooted(p)
    &&& crate::independent::equivalence::no_document_redirect(p)
    &&& !p.stopped ==> {
        &&& crate::independent::equivalence_body::aa_wf(p)
        &&& tags_wf(p)
        &&& crate::independent::equivalence_foreign::open_distinct(p.open)
    }
    &&& !p.stopped && p.mode != Mode::Initial && p.mode != Mode::BeforeHtml ==> {
        &&& crate::independent::equivalence::place_stable(p)
        &&& p.head is Some ==> crate::independent::equivalence::place_stable(
            push(p, crate::independent::early::w3c_head_elem(p)),
        )
        &&& crate::independent::equivalence::html_only_at_root(p)
        &&& p.mode == Mode::InCell ==> cell_in_table_scope(p)
    }
}

/// [`reach_wf`](super::reachable::reach_wf) gives [`w3c_facts`].
pub proof fn lemma_reach_w3c_facts(p: Parser)
    requires
        super::reachable::reach_wf(p),
    ensures
        w3c_facts(p),
{
    lemma_reach_doc(p);
    if !p.stopped {
        lemma_reach_aa_wf(p);
        if p.mode != Mode::Initial && p.mode != Mode::BeforeHtml {
            lemma_reach_place_stable(p);
            lemma_core_html_cell(p);
        }
    }
}

/// **The W3C equivalence lemmas' state preconditions hold of every
/// reachable parser**: for every parser reached from `new_parser` or
/// `fragment_parser` by `dispatch` steps, [`w3c_facts`]: node 0 is the
/// Document with children in the arena, the redirection map has no entry
/// for it, and until parsing stops `aa_wf`, `tags_wf`, `open_distinct`,
/// and (in every mode after "before html") `place_stable`, also of the
/// stack with the `head` element pushed, `html_only_at_root` (the root is
/// the stack's only `html` element), and in the "in cell" mode a `td` or
/// `th` element in table scope. No hypotheses.
pub proof fn theorem_reachable_w3c_facts(
    env: EncFns,
    url: Seq<u32>,
    ctx: Context,
    scripting: bool,
    tentative: bool,
    tokens: Seq<Token>,
)
    ensures
        w3c_facts(crate::reachable::run::dispatch_steps(env, new_parser(url, scripting, tentative), tokens)),
        w3c_facts(crate::reachable::run::dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens)),
{
    super::reachable::theorem_reachable_wf(env, url, ctx, scripting, tentative, tokens);
    lemma_reach_w3c_facts(crate::reachable::run::dispatch_steps(env, new_parser(url, scripting, tentative), tokens));
    lemma_reach_w3c_facts(crate::reachable::run::dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens));
}

/// The inputs where the W3C and WHATWG rules for foreign content differ
/// (`independent::equivalence_foreign::lemma_foreign_content`): `menu`
/// start tags, `br` and `p` end tags, and the breakout tags in the fragment
/// case.
pub open spec fn foreign_texts_agree(p: Parser, t: Tok) -> bool {
    &&& !crate::independent::w3c_start(t, Tag::Menu)
    &&& !crate::independent::w3c_end(t, Tag::Br)
    &&& !crate::independent::w3c_end(t, Tag::P)
    &&& !(p.context is Some && crate::independent::foreign::w3c_foreign_breakout(t))
}

/// The foreign-content equivalence for a parser with
/// [`reach_wf`](super::reachable::reach_wf) and a token the tokenizer
/// emits.
pub proof fn lemma_reach_foreign_content(env: EncFns, p: Parser, token: Token)
    requires
        super::reachable::reach_wf(p),
        !(token is ProcessingInstruction),
        !p.stopped,
        dispatcher(p, classify(token)) == Rules::Foreign,
        foreign_texts_agree(p, classify(token)),
    ensures
        crate::independent::foreign::w3c_foreign_content(env, p, classify(token)) == foreign_content(env, p, classify(token)),
{
    lemma_classify_plain(token);
    assert(crate::independent::equivalence_foreign::foreign_agree(p, classify(token)));
    crate::independent::equivalence_foreign::lemma_foreign_content(env, p, classify(token));
}

/// **Foreign content, from every reachable parser**: the corollary of
/// `independent::equivalence_foreign::lemma_foreign_content` for every
/// parser `p` reached from `new_parser` or `fragment_parser` by `dispatch`
/// steps and every token the tokenizer emits (other than a processing
/// instruction, which the W3C does not have) that the dispatcher sends to
/// the rules for foreign content: the W3C and WHATWG rules give the same
/// outcome, except on the inputs where the texts differ
/// ([`foreign_texts_agree`]). Its hypothesis that the stack holds distinct
/// elements is discharged (`open_elements::theorem_open_distinct`), and so
/// are the token's (tagged, plain attributes).
pub proof fn theorem_reachable_foreign_content(
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
            let t = classify(token);
            !(token is ProcessingInstruction) && !p.stopped && dispatcher(p, t) == Rules::Foreign && foreign_texts_agree(p, t)
                ==> crate::independent::foreign::w3c_foreign_content(env, p, t) == foreign_content(env, p, t)
        }),
        ({
            let p = crate::reachable::run::dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens);
            let t = classify(token);
            !(token is ProcessingInstruction) && !p.stopped && dispatcher(p, t) == Rules::Foreign && foreign_texts_agree(p, t)
                ==> crate::independent::foreign::w3c_foreign_content(env, p, t) == foreign_content(env, p, t)
        }),
{
    super::reachable::theorem_reachable_wf(env, url, ctx, scripting, tentative, tokens);
    let p1 = crate::reachable::run::dispatch_steps(env, new_parser(url, scripting, tentative), tokens);
    let p2 = crate::reachable::run::dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens);
    let t = classify(token);
    if !(token is ProcessingInstruction) && !p1.stopped && dispatcher(p1, t) == Rules::Foreign && foreign_texts_agree(p1, t) {
        lemma_reach_foreign_content(env, p1, token);
    }
    if !(token is ProcessingInstruction) && !p2.stopped && dispatcher(p2, t) == Rules::Foreign && foreign_texts_agree(p2, t) {
        lemma_reach_foreign_content(env, p2, token);
    }
}

/// "In frameset" and "in cell", from a parser with
/// [`reach_wf`](super::reachable::reach_wf): the W3C and WHATWG rules give
/// the same outcome for every token the tokenizer emits (other than a
/// processing instruction).
pub proof fn lemma_reach_frameset_cell(env: EncFns, p: Parser, token: Token)
    requires
        super::reachable::reach_wf(p),
        !(token is ProcessingInstruction),
        !p.stopped,
    ensures
        p.mode == Mode::InFrameset ==> crate::independent::after::w3c_mode_in_frameset(env, p, classify(token))
            == mode_in_frameset(env, p, classify(token)),
        p.mode == Mode::InCell ==> crate::independent::tables::w3c_mode_in_cell(env, p, classify(token)) == mode_in_cell(
            env,
            p,
            classify(token),
        ),
{
    let t = classify(token);
    lemma_reach_w3c_facts(p);
    lemma_classify_plain(token);
    if p.mode == Mode::InFrameset {
        crate::independent::equivalence::lemma_in_frameset(env, p, t);
    }
    if p.mode == Mode::InCell {
        assert(td_or_th() == (|e: Elem| is_html(e, Tag::Td) || is_html(e, Tag::Th)));
        crate::independent::equivalence::lemma_in_cell(env, p, t);
    }
}

/// **"In frameset" and "in cell", from every reachable parser**: the
/// corollaries of `independent::equivalence::lemma_in_frameset` and
/// `lemma_in_cell` for every parser `p` reached from `new_parser` or
/// `fragment_parser` by `dispatch` steps and every token the tokenizer
/// emits (other than a processing instruction, which the W3C does not
/// have): in the "in frameset" mode the W3C and WHATWG rules give the same
/// outcome, and so in the "in cell" mode. No other hypothesis: their state
/// preconditions (the root is the stack's only `html` element; a `td` or
/// `th` element in table scope; tagged records and tokens) are discharged
/// ([`theorem_reachable_w3c_facts`]), and the texts do not differ on any
/// input a reachable parser meets.
pub proof fn theorem_reachable_frameset_cell(
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
            let t = classify(token);
            &&& !(token is ProcessingInstruction) && !p.stopped && p.mode == Mode::InFrameset
                ==> crate::independent::after::w3c_mode_in_frameset(env, p, t) == mode_in_frameset(env, p, t)
            &&& !(token is ProcessingInstruction) && !p.stopped && p.mode == Mode::InCell
                ==> crate::independent::tables::w3c_mode_in_cell(env, p, t) == mode_in_cell(env, p, t)
        }),
        ({
            let p = crate::reachable::run::dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens);
            let t = classify(token);
            &&& !(token is ProcessingInstruction) && !p.stopped && p.mode == Mode::InFrameset
                ==> crate::independent::after::w3c_mode_in_frameset(env, p, t) == mode_in_frameset(env, p, t)
            &&& !(token is ProcessingInstruction) && !p.stopped && p.mode == Mode::InCell
                ==> crate::independent::tables::w3c_mode_in_cell(env, p, t) == mode_in_cell(env, p, t)
        }),
{
    super::reachable::theorem_reachable_wf(env, url, ctx, scripting, tentative, tokens);
    let p1 = crate::reachable::run::dispatch_steps(env, new_parser(url, scripting, tentative), tokens);
    let p2 = crate::reachable::run::dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens);
    if !(token is ProcessingInstruction) && !p1.stopped {
        lemma_reach_frameset_cell(env, p1, token);
    }
    if !(token is ProcessingInstruction) && !p2.stopped {
        lemma_reach_frameset_cell(env, p2, token);
    }
}

} // verus!
