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

/// The invariant the executable helpers require and keep: `parser_wf`,
/// `tags_wf` and `templates_wf`.
pub open spec fn parser_inv(p: Parser) -> bool {
    parser_wf(p) && tags_wf(p) && templates_wf(p)
}

/// The stack of open elements is rooted at an HTML `html` element: what
/// "appropriate place for inserting a node" reads (the current node, and
/// step 3.2's first element). It holds from "before head" on until parsing
/// stops (and in the fragment case from the start).
pub open spec fn stack_rooted(p: Parser) -> bool {
    p.open.len() > 0 && is_html(p.open[0], Tag::Html)
}

// ---------------------------------------------------------------------
// What the executable step needs of the spec's run (Phase 4 item 4.10).
// The exec insertion modes need more than `parser_inv` of the parser they
// are applied to: most need the stack of open elements rooted at an HTML
// `html` element ([`stack_rooted`]), and "after head" needs the head
// element pointer to name a `head` element. Neither follows from
// `parser_inv`, and the modes' contracts do not say they keep it; so the
// exec step takes it as a hypothesis on the spec's run, [`dispatch_needs`],
// not yet proven to hold for every reachable state (see `exec::step`).

/// What the exec rules `r` need of the parser beyond `parser_inv`, `!stopped`,
/// the token's tags and `termination::rules_ok`: the stack rooted at `html`
/// (every mode whose exec function requires it), and for "after head" the
/// head element pointer naming a `head` element.
pub open spec fn rooted_needs(r: Rules, p: Parser) -> bool {
    match r {
        Rules::Foreign => stack_rooted(p),
        Rules::Html(m) => match m {
            Mode::Initial | Mode::BeforeHtml | Mode::InHeadNoscript | Mode::InCaption | Mode::InCell | Mode::InTemplate
            | Mode::AfterAfterBody | Mode::AfterAfterFrameset => true,
            Mode::AfterHead => stack_rooted(p) && crate::exec::modes::after_head::head_ok(p),
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
