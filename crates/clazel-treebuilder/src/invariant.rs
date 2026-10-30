//! `parser_wf`, the invariant of every reachable parser state, which the
//! step's contract assumes and its theorems preserve (Phase 4 item 4.9:
//! `theorem_doc_wf`, `theorem_open_elements_in_doc`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `e` is an element of the arena whose namespace and local name are the
/// record's.
pub open spec fn elem_in_doc(doc: Document, e: Elem) -> bool {
    &&& dom::valid(doc, e.id)
    &&& doc.nodes[e.id as int].kind is Element
    &&& doc.nodes[e.id as int].kind->Element_namespace == Some(e.ns)
    &&& doc.nodes[e.id as int].kind->Element_local_name == e.name
}

/// An optional node of the arena.
pub open spec fn opt_valid(doc: Document, n: Option<NodeId>) -> bool {
    match n {
        None => true,
        Some(x) => dom::valid(doc, x),
    }
}

/// Every id the parse state holds names a node of the document: the stack
/// of open elements and the list of active formatting elements hold
/// elements of the arena (with their own namespace and name), and the
/// element pointers, the fragment context and the redirection map name
/// nodes of it.
pub open spec fn ids_in_doc(p: Parser) -> bool {
    &&& forall|i: int| 0 <= i < p.open.len() ==> elem_in_doc(p.doc, #[trigger] p.open[i])
    &&& forall|i: int|
        0 <= i < p.formatting.len() && (#[trigger] p.formatting[i]) is Entry ==> elem_in_doc(p.doc, p.formatting[i]->Entry_elem)
    &&& opt_valid(p.doc, p.head)
    &&& opt_valid(p.doc, p.form)
    &&& match p.context {
        None => true,
        Some(c) => elem_in_doc(p.doc, c),
    }
    &&& match p.redirect {
        None => true,
        Some((r, f)) => dom::valid(p.doc, r) && dom::valid(p.doc, f) && p.doc.nodes[f as int].kind is DocumentFragment,
    }
}

/// The invariant of every reachable parser state: the document is
/// well formed (`clazel_dom::spec::wf`), every id of the parse state is a
/// node of it, and the modes satisfy `termination::modes_ok` (the
/// hypothesis of `theorem_dispatch_total`).
pub open spec fn parser_wf(p: Parser) -> bool {
    dom::wf(p.doc) && ids_in_doc(p) && crate::termination::modes_ok(p)
}

// ---------------------------------------------------------------------
// Further invariants the executable helpers need (Phase 4 item 4.10).
// `parser_wf` is unchanged; these are separate, and the exec helpers
// require and keep them alongside it.

/// An element record's tag is the classification of its name (`Elem::tag`
/// is a cache of `tag_of(name)`; every record the rules make is built so).
pub open spec fn elem_tagged(e: Elem) -> bool {
    e.tag == tag_of(e.name)
}

/// A tag token's tag is the classification of its name.
pub open spec fn tok_tagged(t: TagTok) -> bool {
    t.tag == tag_of(t.name)
}

/// Every element record of the parse state, and every token of the list of
/// active formatting elements, is tagged by its name.
pub open spec fn tags_wf(p: Parser) -> bool {
    &&& forall|i: int| 0 <= i < p.open.len() ==> elem_tagged(#[trigger] p.open[i])
    &&& forall|i: int|
        0 <= i < p.formatting.len() && (#[trigger] p.formatting[i]) is Entry ==> elem_tagged(p.formatting[i]->Entry_elem)
            && tok_tagged(p.formatting[i]->Entry_token)
    &&& match p.context {
        None => true,
        Some(c) => elem_tagged(c),
    }
}

/// Node `n` is an element whose template contents exist.
pub open spec fn has_template_contents(doc: Document, n: NodeId) -> bool {
    &&& dom::valid(doc, n)
    &&& doc.nodes[n as int].kind is Element
    &&& doc.nodes[n as int].kind->Element_template_contents is Some
}

/// The template elements §13.2.6.1 "appropriate place for inserting a node"
/// can read the template contents of have them: every HTML `template` on
/// the stack of open elements, and every `template` element with a child
/// (a table's parent, step 3.4). (A template created when the node limit
/// stops the parser has none, but it is never pushed nor given a child.)
pub open spec fn templates_wf(p: Parser) -> bool {
    &&& forall|i: int|
        0 <= i < p.open.len() && is_html(#[trigger] p.open[i], Tag::Template) ==> has_template_contents(p.doc, p.open[i].id)
    &&& forall|n: NodeId|
        dom::valid(p.doc, n) && #[trigger] node_is_template(p.doc, n) && p.doc.nodes[n as int].children.len() > 0
            ==> has_template_contents(p.doc, n)
}

/// The head element pointer, if set, points to an HTML `head` element of
/// the document (it is only ever set to the `head` element the parser
/// created): what "after head" case 8 pushes back is a record of the
/// document. (A parser stopped while creating the `head` element may point
/// at node 0; a stopped parser takes no further step.)
pub open spec fn head_ok(p: Parser) -> bool {
    match p.head {
        Some(h) => elem_in_doc(p.doc, head_elem(h)),
        None => true,
    }
}

/// The invariant the executable helpers require and keep: `parser_wf`,
/// `tags_wf`, `templates_wf`, and (until parsing stops) [`head_ok`].
pub open spec fn parser_inv(p: Parser) -> bool {
    parser_wf(p) && tags_wf(p) && templates_wf(p) && (p.stopped || head_ok(p))
}

/// The stack of open elements is rooted at an HTML `html` element: what
/// "appropriate place for inserting a node" reads (the current node, and
/// step 3.2's first element). It holds from "before head" on until parsing
/// stops (and in the fragment case from the start).
pub open spec fn stack_rooted(p: Parser) -> bool {
    p.open.len() > 0 && is_html(p.open[0], Tag::Html)
}

// ---------------------------------------------------------------------
// The reachable-state invariant (Phase 4 item 4.10): what every parser
// state reachable from `new_parser` or `fragment_parser` by `dispatch`
// satisfies besides `parser_inv`. It relates each insertion mode to the
// stack's shape, so that the rules that pop the current node without
// looking at it ("in head", "in head noscript", "text") never pop the
// `html` element, and records the facts about node ids that keep the
// adoption agency algorithm and the `form` end tag from removing it.
// `reachable` proves `dispatch` keeps it (`reachable::run::theorem_reachable`).

/// The stack `o` is rooted at an HTML `html` element tagged by its name
/// ([`stack_rooted`], plus the tag).
pub open spec fn rooted_seq(o: Seq<Elem>) -> bool {
    o.len() > 0 && is_html(o[0], Tag::Html) && elem_tagged(o[0])
}

/// A mode whose only shape requirement is a rooted stack: every mode but
/// the two before the `html` element exists, the two whose rules pop the
/// current node blindly ("in head", "in head noscript"), and the two that
/// return to an original insertion mode ("text", "in table text").
pub open spec fn rooted_mode(m: Mode) -> bool {
    !(m == Mode::Initial || m == Mode::BeforeHtml || m == Mode::InHead || m == Mode::InHeadNoscript || m == Mode::Text || m
        == Mode::InTableText)
}

/// The stack `o` has an HTML element above the `html` element (the last
/// HTML element is not the first entry).
pub open spec fn html_above(o: Seq<Elem>) -> bool {
    last_index_where(o, o.len() as int, html_ns()) >= 1
}

/// The predicate "is an element in the HTML namespace".
pub open spec fn html_ns() -> spec_fn(Elem) -> bool {
    |e: Elem| e.ns == Namespace::Html
}

/// The shape of the stack `o` in insertion mode `m` (other than "text" and
/// "in table text"): empty before the `html` element exists; in "in head",
/// an HTML element (the `head` element) above `html`; in "in head
/// noscript", an HTML current node (`noscript`) above a stack of the "in
/// head" shape; otherwise rooted.
pub open spec fn shape0(m: Mode, o: Seq<Elem>) -> bool {
    match m {
        Mode::Initial | Mode::BeforeHtml => o.len() == 0,
        Mode::InHead => rooted_seq(o) && html_above(o),
        Mode::InHeadNoscript => rooted_seq(o) && o.len() >= 2 && o.last().ns == Namespace::Html && html_above(o.drop_last()),
        Mode::Text | Mode::InTableText => false,
        _ => rooted_seq(o),
    }
}

/// The stack's shape for the parser's insertion mode: in "text", an HTML
/// current node (the element whose text is parsed) above a stack of the
/// original insertion mode's shape; in "in table text", a rooted stack
/// with an HTML current node (a table element) above `html`, and an
/// original insertion mode of [`rooted_mode`]; before the `html` element
/// exists, no stack, no list of active formatting elements and no form
/// element pointer (and an arena holding the document); otherwise
/// [`shape0`].
pub open spec fn shape(p: Parser) -> bool {
    match p.mode {
        Mode::Text => p.open.len() >= 2 && p.open.last().ns == Namespace::Html && shape0(p.original_mode, p.open.drop_last()),
        Mode::InTableText => rooted_seq(p.open) && p.open.len() >= 2 && p.open.last().ns == Namespace::Html && rooted_mode(
            p.original_mode,
        ),
        Mode::Initial | Mode::BeforeHtml => p.open.len() == 0 && p.formatting.len() == 0 && p.form is None && p.doc.nodes.len()
            > 0,
        _ => shape0(p.mode, p.open),
    }
}

/// Facts about the `html` element's id: it is a node of the arena (so
/// every node created later has another id), no entry of the list of
/// active formatting elements is for it, and the form element pointer does
/// not point to it.
pub open spec fn root_ids(p: Parser) -> bool {
    rooted_seq(p.open) ==> {
        let r = p.open[0].id;
        &&& r < p.doc.nodes.len()
        &&& forall|i: int| 0 <= i < p.formatting.len() && (#[trigger] p.formatting[i]) is Entry ==> p.formatting[i]->Entry_elem.id != r
        &&& match p.form {
            Some(f) => f != r,
            None => true,
        }
    }
}

/// The predicate "is an HTML `td` or `th` element".
pub open spec fn cell_pred() -> spec_fn(Elem) -> bool {
    |e: Elem| is_html(e, Tag::Td) || is_html(e, Tag::Th)
}

/// The stack `o` holds a `td` or `th` element.
pub open spec fn has_cell(o: Seq<Elem>) -> bool {
    last_index_where(o, o.len() as int, cell_pred()) >= 0
}

/// The index of the last `td` or `th` element of the stack `o` (-1 if
/// none).
pub open spec fn last_cell(o: Seq<Elem>) -> int {
    last_index_where(o, o.len() as int, cell_pred())
}

/// An HTML `table` or `template` element: with the `html` element, what
/// ends a search in table scope (§13.2.4.2).
pub open spec fn table_wall(e: Elem) -> bool {
    is_html(e, Tag::Table) || is_html(e, Tag::Template)
}

/// The stack `o` holds a cell, and no `table` or `template` element is
/// above its last cell: with [`html_once`], the last cell is in table
/// scope.
pub open spec fn cell_scoped(o: Seq<Elem>) -> bool {
    &&& has_cell(o)
    &&& forall|j: int| last_cell(o) < j < o.len() ==> !table_wall(#[trigger] o[j])
}

/// The stack's only `html` element is its first entry (the parser creates
/// one `html` element, in "before html" or as the fragment case's root,
/// and an `html` start tag elsewhere only adds attributes to it).
pub open spec fn html_once(o: Seq<Elem>) -> bool {
    forall|i: int| 0 < i < o.len() ==> !is_html(#[trigger] o[i], Tag::Html)
}

/// In the "in cell" insertion mode the stack holds a cell in table scope
/// ([`cell_scoped`]; §13.2.6.4.15, "close the cell": "Assert: The stack of
/// open elements has a td or th element in table scope"; the start tags
/// and end tags that close the cell pop until one has been popped).
pub open spec fn in_cell_ok(p: Parser) -> bool {
    p.mode == Mode::InCell ==> cell_scoped(p.open)
}

/// [`in_cell_ok`], also for the "in cell" mode a parser returns to: in
/// "text" over "in cell" the stack below the current node holds a cell in
/// table scope,
/// and "in table text" never returns to "in cell" (the "in table" rules,
/// which switch to it, are never applied in the "in cell" mode).
pub open spec fn cell_ok(p: Parser) -> bool {
    &&& in_cell_ok(p)
    &&& p.mode == Mode::Text && p.original_mode == Mode::InCell ==> cell_scoped(p.open.drop_last())
    &&& p.mode == Mode::InTableText ==> p.original_mode != Mode::InCell
}

/// The id `id` of a cell on the stack names a node of the arena, and
/// neither the form element pointer nor an entry of the list of active
/// formatting elements is for it: the rules that remove an element by its
/// id ("a" start tag, "form" end tag) never remove a cell.
pub open spec fn cell_fresh(p: Parser, id: NodeId) -> bool {
    &&& id < p.doc.nodes.len()
    &&& p.form != Some(id)
    &&& forall|i: int| 0 <= i < p.formatting.len() && (#[trigger] p.formatting[i]) is Entry ==> p.formatting[i]->Entry_elem.id != id
}

/// Facts about cells and ids: every entry of the list of active formatting
/// elements is for a node of the arena, neither its element nor its token
/// is a cell, and its token is not `html` nor `table` (the parser pushes
/// entries only for the formatting tags, and the elements "reconstruct the
/// active formatting elements" and the adoption agency algorithm put on
/// the stack are created for these tokens); the form element pointer names a node of the arena; every cell
/// on the stack is [`cell_fresh`]. (So the elements the parser creates,
/// whose ids are new, are never in the list, the form pointer, or the
/// stack's cells.)
pub open spec fn cells_wf(p: Parser) -> bool {
    &&& forall|i: int|
        0 <= i < p.formatting.len() && (#[trigger] p.formatting[i]) is Entry ==> p.formatting[i]->Entry_elem.id
            < p.doc.nodes.len() && !cell_pred()(p.formatting[i]->Entry_elem) && p.formatting[i]->Entry_token.tag != Tag::Td
            && p.formatting[i]->Entry_token.tag != Tag::Th && p.formatting[i]->Entry_token.tag != Tag::Html
            && p.formatting[i]->Entry_token.tag != Tag::Table
    &&& match p.form {
        Some(f) => f < p.doc.nodes.len(),
        None => true,
    }
    &&& forall|j: int| 0 <= j < p.open.len() && cell_pred()(#[trigger] p.open[j]) ==> cell_fresh(p, p.open[j].id)
}

/// The reachable-state facts of a running parser: the stack's [`shape`],
/// [`root_ids`], [`tags_wf`], [`cells_wf`], [`cell_ok`], [`html_once`],
/// and the document facts `reachable::doc::dinv` (among them
/// [`templates_wf`]'s).
pub open spec fn reach_core(p: Parser) -> bool {
    shape(p) && root_ids(p) && tags_wf(p) && cells_wf(p) && cell_ok(p) && html_once(p.open)
        && crate::reachable::doc::dinv(p)
}

/// **The reachable-state invariant**: a stopped parser (which takes no
/// further step), or one whose modes satisfy `termination::modes_ok` (the
/// hypothesis of `termination::theorem_dispatch_total`) and
/// [`reach_core`].
pub open spec fn reachable_inv(p: Parser) -> bool {
    p.stopped || (crate::termination::modes_ok(p) && reach_core(p))
}

/// What a set of rules other than the current mode's needs (the rule
/// applications "using the rules for" another mode makes): the "in head"
/// rules get only the tokens [`crate::termination::headish`] lists; the
/// "in body" rules get a parser in a [`rooted_mode`] (in the "in cell"
/// mode, not a `td` or `th` end tag, which the "in cell" rules handle
/// themselves), or the `html` start tag; the "in template" rules a parser
/// in a [`rooted_mode`]; the "in table" rules one in a [`rooted_mode`]
/// other than "in cell" (they are used only by "in table body" and "in
/// row"); no other rules are used so; never before the `html` element
/// exists. Foreign content needs a parser in foreign content (as the
/// dispatcher chooses it).
pub open spec fn rules_need(r: Rules, p: Parser, t: Tok) -> bool {
    match r {
        Rules::Foreign => in_foreign_content(p),
        Rules::Html(m) => m == p.mode || (p.mode != Mode::Initial && p.mode != Mode::BeforeHtml && match m {
            Mode::InHead => crate::termination::headish(t),
            Mode::InBody => (rooted_mode(p.mode) && !(p.mode == Mode::InCell && (crate::termination::is_end(t, Tag::Td)
                || crate::termination::is_end(t, Tag::Th)))) || crate::termination::is_start(t, Tag::Html),
            Mode::InTable => rooted_mode(p.mode) && p.mode != Mode::InCell,
            Mode::InTemplate => rooted_mode(p.mode),
            _ => false,
        }),
    }
}

/// The invariant at every rule application of a token's run: a running
/// parser satisfying `termination::modes_ok`, [`reach_core`] and the
/// rules' [`rules_need`], a tagged token, and `termination::rules_ok`.
pub open spec fn rules_inv(r: Rules, p: Parser, t: Tok) -> bool {
    &&& !p.stopped
    &&& crate::exec::modes::initial::tok_ok(t)
    &&& crate::termination::modes_ok(p)
    &&& crate::termination::rules_ok(r, p)
    &&& reach_core(p)
    &&& rules_need(r, p, t)
}

// ---------------------------------------------------------------------
// What the executable step needs of the spec's run (Phase 4 item 4.10).
// The exec insertion modes need more than `parser_inv` of the parser they
// are applied to: most need the stack of open elements rooted at an HTML
// `html` element ([`stack_rooted`]). That does not follow from
// `parser_inv`, and the modes' contracts do not say they keep it; it
// follows from [`reachable_inv`] (`reachable::run::lemma_dispatch_reach`
// proves [`dispatch_needs`] from it).

/// What the exec rules `r` need of the parser beyond `parser_inv`, `!stopped`,
/// the token's tags and `termination::rules_ok`: the stack rooted at `html`
/// (every mode whose exec function requires it).
pub open spec fn rooted_needs(r: Rules, p: Parser) -> bool {
    match r {
        Rules::Foreign => stack_rooted(p),
        Rules::Html(m) => match m {
            Mode::Initial | Mode::BeforeHtml | Mode::InHeadNoscript | Mode::InCaption | Mode::InCell | Mode::InTemplate
            | Mode::AfterAfterBody | Mode::AfterAfterFrameset => true,
            _ => stack_rooted(p),
        },
    }
}

/// Every rule application of the spec's [`run`] (with at most `fuel`
/// applications) meets [`rooted_needs`].
pub open spec fn run_needs(env: EncFns, p: Parser, t: Tok, r: Rules, fuel: nat) -> bool
    decreases fuel,
{
    if fuel == 0 {
        true
    } else {
        rooted_needs(r, p) && match apply_rules(env, r, p, t) {
            Outcome::Done(_) => true,
            Outcome::Reprocess(q, t2) => q.stopped || run_needs(env, q, t2, Rules::Html(q.mode), (fuel - 1) as nat),
            Outcome::Using(m, q, t2) => q.stopped || run_needs(env, q, t2, Rules::Html(m), (fuel - 1) as nat),
        }
    }
}

/// [`run_needs`] of the run [`dispatch`] makes for `token`.
pub open spec fn dispatch_needs(env: EncFns, p: Parser, token: Token) -> bool {
    let p0 = Parser { actions: seq![], tokenizer: None, ..p };
    if p0.stopped {
        true
    } else if p0.skip_lf && token == (Token::Character { c: 0x0A }) {
        true
    } else {
        let p1 = Parser { skip_lf: false, ..p0 };
        let t = classify(token);
        run_needs(env, p1, t, dispatcher(p1, t), fuel_bound(p1))
    }
}

} // verus!
