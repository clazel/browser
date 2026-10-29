//! The equivalence lemmas: for each insertion mode, the W3C transcription
//! ([`super`]) and [`crate::spec`]'s give the same outcome on every input
//! where the two documents prescribe the same thing. Each lemma's
//! precondition excludes exactly the inputs where they differ, and its doc
//! comment says what the difference is; the WHATWG text (which
//! [`crate::spec`] follows) is the one the parser implements.
//!
//! Common to every lemma: the W3C has no processing instruction tokens
//! (`Tok::Pi`), which the WHATWG modes insert as nodes.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// §8.2.5.4.1 to §8.2.5.4.3, §8.2.5.4.5

/// "initial" (W3C §8.2.5.4.1, WHATWG §13.2.6.4.1), every token but a
/// DOCTYPE: the same rules.
pub proof fn lemma_initial(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
        !(t is Doctype),
    ensures
        w3c_mode_initial(env, p, t) == mode_initial(env, p, t),
{
}

/// The W3C's lists of public and system identifiers for quirks and
/// limited-quirks mode classify the identifiers as the WHATWG
/// transcription's do. NOT PROVEN: see [`lemma_initial_doctype`].
pub open spec fn doctype_lists_agree(public_id: Option<Seq<u32>>, system_id: Option<Seq<u32>>) -> bool {
    &&& forall|name: Option<Seq<u32>>, force_quirks: bool|
        #[trigger] doctype_is_quirks(name, public_id, system_id, force_quirks) == (force_quirks || name != Some(w3c_name_html())
            || w3c_quirks_identifiers(public_id, system_id))
    &&& doctype_is_limited_quirks(public_id, system_id) == w3c_limited_quirks_identifiers(public_id, system_id)
}

/// Node 0 is the Document, and its children are nodes of the arena (facts
/// of every reachable state: `clazel_dom::spec::wf`).
pub open spec fn document_rooted(p: Parser) -> bool {
    &&& p.doc.nodes.len() > 0
    &&& p.doc.nodes[0].kind is Document
    &&& forall|i: int| 0 <= i < p.doc.nodes[0].children.len() ==> dom::valid(p.doc, #[trigger] p.doc.nodes[0].children[i])
}

/// "initial" for a DOCTYPE token (W3C §8.2.5.4.1, WHATWG §13.2.6.4.1): the
/// same rules (the W3C appends the DocumentType node with DOM's pre-insert,
/// which inserts nothing when the Document has a doctype or element child;
/// the WHATWG says so explicitly), given that the two documents' lists of
/// identifiers classify the token's identifiers alike
/// ([`doctype_lists_agree`]). That last fact is not proven: both
/// transcriptions compare ASCII case-insensitively (`ascii_lowercase`, a
/// `map_values`), which neither Z3 nor `compute_only` evaluates on the
/// lists' 65 strings within the resource limit. It is a precondition here,
/// and it is the part of "initial" this file does not check.
pub proof fn lemma_initial_doctype(env: EncFns, p: Parser, t: Tok)
    requires
        !p.stopped,
        document_rooted(p),
        t is Doctype,
        doctype_lists_agree(t->Doctype_public_id, t->Doctype_system_id),
    ensures
        w3c_mode_initial(env, p, t) == mode_initial(env, p, t),
{
    hide(doctype_is_quirks);
    hide(doctype_is_limited_quirks);
    hide(w3c_quirks_identifiers);
    hide(w3c_limited_quirks_identifiers);
    assert(doctype_is_quirks(t->Doctype_name, t->Doctype_public_id, t->Doctype_system_id, t->Doctype_force_quirks) == (
    t->Doctype_force_quirks || t->Doctype_name != Some(w3c_name_html()) || w3c_quirks_identifiers(
        t->Doctype_public_id,
        t->Doctype_system_id,
    )));
}

/// The insertion target redirection map has no entry for the Document
/// node: its only entry is the fragment case's `html` root (§13.4 step 15),
/// an element. (The WHATWG "before html" inserts the root "at the adjusted
/// insertion location", which consults the map; the W3C appends it.)
pub open spec fn no_document_redirect(p: Parser) -> bool {
    p.redirect is None || p.redirect->Some_0.0 != 0
}

/// A node `create_element_for_token` just created has no parent.
proof fn lemma_created_parentless(p: Parser, tt: TagTok, ns: Namespace, parent: NodeId)
    requires
        !p.stopped,
        !create_element_for_token(p, tt, ns, parent).0.stopped,
        !(ns == Namespace::Html && tt.tag == Tag::Template),
    ensures
        ({
            let (p1, e) = create_element_for_token(p, tt, ns, parent);
            p1.doc.nodes[e.id as int].parent is None
        }),
{
}

/// W3C "append" to the Document is the WHATWG "insert an element at the
/// adjusted insertion location" with the location (the Document, null), for
/// a node with no parent, when the map does not redirect the Document.
proof fn lemma_append_to_document(p: Parser, node: NodeId)
    requires
        no_document_redirect(p),
        p.stopped || p.doc.nodes[node as int].parent is None,
    ensures
        w3c_append_to_document(p, node) == insert_element_at(p, node, Some(document_location())),
{
}

/// "before html" (W3C §8.2.5.4.2, WHATWG §13.2.6.4.2): the same rules,
/// where the W3C's "append it to the Document object" (DOM pre-insert) and
/// the WHATWG's "insert an element at the adjusted insertion location" with
/// the Document as the location agree: when the insertion target
/// redirection map has no entry for the Document ([`no_document_redirect`]).
pub proof fn lemma_before_html(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
        no_document_redirect(p),
    ensures
        w3c_mode_before_html(env, p, t) == mode_before_html(env, p, t),
{
    let tt = if w3c_start(t, Tag::Html) {
        t->Start_0
    } else {
        start_tag_named(w3c_name_html())
    };
    assert(tag_of(w3c_name_html()) == Tag::Html) by (compute_only);
    let (p1, e) = create_element_for_token(p, tt, Namespace::Html, 0);
    if !p1.stopped {
        lemma_created_parentless(p, tt, Namespace::Html, 0);
    }
    lemma_append_to_document(p1, e.id);
}

/// "before head" (W3C §8.2.5.4.3, WHATWG §13.2.6.4.3): the same rules.
pub proof fn lemma_before_head(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_before_head(env, p, t) == mode_before_head(env, p, t),
{
}

/// The stack's elements and their parents are nodes of the arena, and the
/// insertion target redirection map does not map a node to itself (facts
/// of every reachable state: `crate::invariant::parser_wf`). Then a node
/// created in between does not move "the appropriate place for inserting a
/// node", and applying the map to an adjusted location changes nothing.
pub open spec fn place_stable(p: Parser) -> bool {
    &&& forall|i: int|
        0 <= i < p.open.len() ==> dom::valid(p.doc, (#[trigger] p.open[i]).id) && match p.doc.nodes[p.open[i].id as int].parent {
            Some(par) => dom::valid(p.doc, par),
            None => true,
        }
    &&& (p.redirect is None || p.redirect->Some_0.0 != p.redirect->Some_0.1)
    &&& p.open.len() > 0
    &&& is_html(p.open[0], Tag::Html)
}

/// `last_index_where` is -1 or the index of an entry satisfying `f`.
proof fn lemma_last_index_where(open: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool)
    requires
        0 <= i <= open.len(),
    ensures
        -1 <= last_index_where(open, i, f) < i,
        last_index_where(open, i, f) >= 0 ==> f(open[last_index_where(open, i, f)]),
    decreases i,
{
    if i > 0 && !f(open[i - 1]) {
        lemma_last_index_where(open, i - 1, f);
    }
}

/// "In head"'s `script` steps insert at the location computed before the
/// element is created (W3C, steps 1 and 5); the WHATWG transcription's
/// "insert an element at the adjusted insertion location" computes it after.
/// They are the same location ([`place_stable`]).
proof fn lemma_script_location(p: Parser, tt: TagTok)
    requires
        !p.stopped,
        place_stable(p),
        tt.tag == Tag::Script,
    ensures
        ({
            let loc = adjusted_location(p, None);
            let (p1, e) = create_element_for_token(p, tt, Namespace::Html, loc.parent);
            insert_element_at(p1, e.id, Some(loc)) == insert_element_at(p1, e.id, None)
        }),
{
    let loc = adjusted_location(p, None);
    let (p1, e) = create_element_for_token(p, tt, Namespace::Html, loc.parent);
    if !p1.stopped {
        assert(p1.open == p.open);
        assert(p1.doc.nodes.len() == p.doc.nodes.len() + 1);
        assert forall|j: int| 0 <= j < p.doc.nodes.len() implies p1.doc.nodes[j] == p.doc.nodes[j] by {}
        let f = |x: Elem| is_html(x, Tag::Template) || is_html(x, Tag::Table);
        lemma_last_index_where(p.open, p.open.len() as int, f);
        let k = last_index_where(p.open, p.open.len() as int, f);
        if k >= 0 {
            assert(f(p.open[k]));
            assert(k != 0);
            assert(dom::valid(p.doc, p.open[k].id));
            assert(dom::valid(p.doc, p.open[k - 1].id));
        }
        assert(dom::valid(p.doc, p.open[p.open.len() - 1].id));
        assert(dom::valid(p.doc, p.open[0].id));
        assert(appropriate_place(p1, None) == appropriate_place(p, None));
        assert(adjusted_location(p1, None) == loc);
        assert(adjusted_location(p1, Some(loc)) == loc);
    }
}

/// "in head" (W3C §8.2.5.4.4, WHATWG §13.2.6.4.4): the same rules.
pub proof fn lemma_in_head(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
        place_stable(p),
    ensures
        w3c_mode_in_head(env, p, t) == mode_in_head(env, p, t),
{
    if w3c_start(t, Tag::Script) {
        lemma_in_head_script(env, p, t);
    } else {
        lemma_in_head_other(env, p, t);
    }
}

/// [`lemma_in_head`] for a `script` start tag.
#[verifier::spinoff_prover]
proof fn lemma_in_head_script(env: EncFns, p: Parser, t: Tok)
    requires
        !p.stopped,
        place_stable(p),
        w3c_start(t, Tag::Script),
    ensures
        w3c_mode_in_head(env, p, t) == mode_in_head(env, p, t),
{
    lemma_script_location(p, t->Start_0);
}

/// [`lemma_in_head`] for every other token.
#[verifier::spinoff_prover]
proof fn lemma_in_head_other(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
        !w3c_start(t, Tag::Script),
    ensures
        w3c_mode_in_head(env, p, t) == mode_in_head(env, p, t),
{
}

/// "in head noscript" (W3C §8.2.5.4.5, WHATWG §13.2.6.4.5): the same rules.
pub proof fn lemma_in_head_noscript(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_in_head_noscript(env, p, t) == mode_in_head_noscript(env, p, t),
{
}

/// The token is one "after head"'s "anything else" entry handles (W3C
/// §8.2.5.4.6).
pub open spec fn after_head_anything_else(t: Tok) -> bool {
    let tag = w3c_tag(t);
    &&& !w3c_space_char(t)
    &&& !(t is Comment)
    &&& !(t is Doctype)
    &&& !(t is Start && (tag == Tag::Html || tag == Tag::Body || tag == Tag::Frameset || tag == Tag::Base || tag == Tag::Basefont
        || tag == Tag::Bgsound || tag == Tag::Link || tag == Tag::Meta || tag == Tag::Noframes || tag == Tag::Script || tag
        == Tag::Style || tag == Tag::Template || tag == Tag::Title || tag == Tag::Head))
    &&& !(t is End && !(tag == Tag::Body || tag == Tag::Html || tag == Tag::Br))
}

/// The tokens "after head" processes with the "in head" rules between
/// pushing and removing the head element.
pub open spec fn after_head_in_head_tag(t: Tok) -> bool {
    let tag = w3c_tag(t);
    t is Start && (tag == Tag::Base || tag == Tag::Basefont || tag == Tag::Bgsound || tag == Tag::Link || tag == Tag::Meta || tag
        == Tag::Noframes || tag == Tag::Script || tag == Tag::Style || tag == Tag::Template || tag == Tag::Title)
}

/// "after head" (W3C §8.2.5.4.6, WHATWG §13.2.6.4.6): the same rules, but
/// for two differences.
/// - The WHATWG's "anything else" entry also sets the frameset-ok flag to
///   "ok" (a change made after the W3C forked the text); the W3C leaves it.
///   They agree when the flag is already "ok": excluded otherwise.
/// - For the head-element entry (`base`, …, `title`), the W3C says "the
///   head element pointer cannot be null at this point" and the
///   WHATWG transcription ignores the token if it is: the pointer is
///   required to be set, and to point at an element of the arena whose
///   parent is one ([`place_stable`] of the stack with it pushed).
pub proof fn lemma_after_head(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
        place_stable(p),
        after_head_anything_else(t) ==> p.frameset_ok,
        after_head_in_head_tag(t) ==> p.head is Some && place_stable(push(p, w3c_head_elem(p))),
    ensures
        w3c_mode_after_head(env, p, t) == mode_after_head(env, p, t),
{
    assert(tag_of(w3c_name_body()) == Tag::Body) by (compute_only);
    if after_head_in_head_tag(t) {
        lemma_in_head(env, push(p, w3c_head_elem(p)), t);
    }
}

// ---------------------------------------------------------------------
// §8.2.5.4.8

/// "text" (W3C §8.2.5.4.8, WHATWG §13.2.6.4.8): the same rules.
pub proof fn lemma_text(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_text(env, p, t) == mode_text(env, p, t),
{
}

// ---------------------------------------------------------------------
// §8.2.5.4.11, §8.2.5.4.12

/// "in caption" (W3C §8.2.5.4.11, WHATWG §13.2.6.4.11): the same rules.
pub proof fn lemma_in_caption(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_in_caption(env, p, t) == mode_in_caption(env, p, t),
{
}

/// "in column group" (W3C §8.2.5.4.12, WHATWG §13.2.6.4.12): the same
/// rules.
pub proof fn lemma_in_column_group(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_in_column_group(env, p, t) == mode_in_column_group(env, p, t),
{
}

// ---------------------------------------------------------------------
// §8.2.5.4.19 to §8.2.5.4.23

/// "after body" (W3C §8.2.5.4.19, WHATWG §13.2.6.4.17): the same rules.
pub proof fn lemma_after_body(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_after_body(env, p, t) == mode_after_body(env, p, t),
{
}

/// The stack's only `html` element is its first entry, "the root html
/// element" (the parser creates one `html` element, in "before html", and
/// the fragment case puts its root first).
pub open spec fn html_only_at_root(p: Parser) -> bool {
    &&& p.open.len() > 0
    &&& is_html(p.open[0], Tag::Html)
    &&& forall|i: int| 0 < i < p.open.len() ==> !is_html(#[trigger] p.open[i], Tag::Html)
}

/// "in frameset" (W3C §8.2.5.4.20, WHATWG §13.2.6.4.18): the same rules,
/// where the W3C's "if the current node is the root html element" (read
/// here as: the current node is an `html` element) and the WHATWG
/// transcription's reading of the same words agree: when the root is the
/// stack's only `html` element ([`html_only_at_root`]).
pub proof fn lemma_in_frameset(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
        html_only_at_root(p),
    ensures
        w3c_mode_in_frameset(env, p, t) == mode_in_frameset(env, p, t),
{
}

/// "after frameset" (W3C §8.2.5.4.21, WHATWG §13.2.6.4.19): the same rules.
pub proof fn lemma_after_frameset(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_after_frameset(env, p, t) == mode_after_frameset(env, p, t),
{
}

/// "after after body" (W3C §8.2.5.4.22, WHATWG §13.2.6.4.20): the same
/// rules.
pub proof fn lemma_after_after_body(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_after_after_body(env, p, t) == mode_after_after_body(env, p, t),
{
}

/// "after after frameset" (W3C §8.2.5.4.23, WHATWG §13.2.6.4.21): the same
/// rules.
pub proof fn lemma_after_after_frameset(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_after_after_frameset(env, p, t) == mode_after_after_frameset(env, p, t),
{
}

// ---------------------------------------------------------------------
// §8.2.5.4.13 to §8.2.5.4.15, §8.2.5.4.18

/// `pop_while` depends only on the values of its predicate on the stack.
proof fn lemma_pop_while_ext(p: Parser, f: spec_fn(Elem) -> bool, g: spec_fn(Elem) -> bool)
    requires
        forall|j: int| 0 <= j < p.open.len() ==> #[trigger] f(p.open[j]) == g(p.open[j]),
    ensures
        pop_while(p, f) == pop_while(p, g),
    decreases p.open.len(),
{
    if p.open.len() > 0 {
        assert(f(p.open[p.open.len() - 1]) == g(p.open[p.open.len() - 1]));
        if f(current_node(p)) {
            let q = pop(p);
            assert forall|j: int| 0 <= j < q.open.len() implies #[trigger] f(q.open[j]) == g(q.open[j]) by {
                assert(q.open[j] == p.open[j]);
            }
            lemma_pop_while_ext(q, f, g);
        }
    }
}

/// `in_scope_from` depends only on the values of its target predicate on
/// the stack.
proof fn lemma_in_scope_ext(open: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool, g: spec_fn(Elem) -> bool, s: Scope)
    requires
        i <= open.len(),
        forall|j: int| 0 <= j < i ==> #[trigger] f(open[j]) == g(open[j]),
    ensures
        in_scope_from(open, i, f, s) == in_scope_from(open, i, g, s),
    decreases i,
{
    if i > 0 {
        assert(f(open[i - 1]) == g(open[i - 1]));
        lemma_in_scope_ext(open, i - 1, f, g, s);
    }
}

/// [`lemma_pop_while_ext`] and [`lemma_in_scope_ext`] for every predicate
/// pair, so that the transcriptions' own predicates (closures written
/// separately in each) can be matched.
pub proof fn lemma_closure_ext()
    ensures
        forall|p: Parser, f: spec_fn(Elem) -> bool, g: spec_fn(Elem) -> bool|
            (forall|j: int| 0 <= j < p.open.len() ==> #[trigger] f(p.open[j]) == g(p.open[j])) ==> #[trigger] pop_while(p, f)
                == #[trigger] pop_while(p, g),
        forall|open: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool, g: spec_fn(Elem) -> bool, s: Scope|
            i <= open.len() && (forall|j: int| 0 <= j < i ==> #[trigger] f(open[j]) == g(open[j])) ==> #[trigger] in_scope_from(
                open,
                i,
                f,
                s,
            ) == #[trigger] in_scope_from(open, i, g, s),
{
    assert forall|p: Parser, f: spec_fn(Elem) -> bool, g: spec_fn(Elem) -> bool|
        (forall|j: int| 0 <= j < p.open.len() ==> #[trigger] f(p.open[j]) == g(p.open[j])) implies #[trigger] pop_while(p, f)
        == #[trigger] pop_while(p, g) by {
        lemma_pop_while_ext(p, f, g);
    }
    assert forall|open: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool, g: spec_fn(Elem) -> bool, s: Scope|
        i <= open.len() && (forall|j: int| 0 <= j < i ==> #[trigger] f(open[j]) == g(open[j])) implies #[trigger] in_scope_from(
        open,
        i,
        f,
        s,
    ) == #[trigger] in_scope_from(open, i, g, s) by {
        lemma_in_scope_ext(open, i, f, g, s);
    }
}

/// Only the name "tbody" is the tag `tbody`, and so on for the table tags:
/// "an HTML element with the same tag name as the token" is one with the
/// same [`Tag`], for tagged records ([`crate::invariant::tags_wf`]).
pub proof fn lemma_table_tags_injective()
    ensures
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Tbody ==> n == seq![0x74u32, 0x62, 0x6f, 0x64, 0x79],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Tfoot ==> n == seq![0x74u32, 0x66, 0x6f, 0x6f, 0x74],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Thead ==> n == seq![0x74u32, 0x68, 0x65, 0x61, 0x64],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Td ==> n == seq![0x74u32, 0x64],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Th ==> n == seq![0x74u32, 0x68],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Tr ==> n == seq![0x74u32, 0x72],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Table ==> n == seq![0x74u32, 0x61, 0x62, 0x6c, 0x65],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Caption ==> n == seq![0x63u32, 0x61, 0x70, 0x74, 0x69, 0x6f, 0x6e],
{
}

/// The token's tag is the classification of its name (as
/// [`crate::spec::classify`] makes every tag token).
pub open spec fn token_tagged(t: Tok) -> bool {
    (t is Start || t is End) ==> tok_tagged(w3c_tag_tok(t))
}

/// "in table body" (W3C §8.2.5.4.13, WHATWG §13.2.6.4.13): the same rules.
/// ("An HTML element with the same tag name as the token" is read as the
/// same [`Tag`] here and as the same name in the WHATWG transcription; the
/// two agree for tagged records and tokens.)
pub proof fn lemma_in_table_body(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
        tags_wf(p),
        token_tagged(t),
    ensures
        w3c_mode_in_table_body(env, p, t) == mode_in_table_body(env, p, t),
{
    lemma_closure_ext();
    lemma_table_tags_injective();
}

/// "in row" (W3C §8.2.5.4.14, WHATWG §13.2.6.4.14): the same rules (with
/// the reading of "the same tag name" of [`lemma_in_table_body`]).
pub proof fn lemma_in_row(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
        tags_wf(p),
        token_tagged(t),
    ensures
        w3c_mode_in_row(env, p, t) == mode_in_row(env, p, t),
{
    lemma_closure_ext();
    lemma_table_tags_injective();
}

/// "Pop elements … until a td element or a th element has been popped":
/// the two transcriptions' loops are equal.
proof fn lemma_pop_until_cell_popped(p: Parser)
    ensures
        w3c_pop_until_cell_popped(p) == pop_until_cell_popped(p),
    decreases p.open.len(),
{
    if p.open.len() > 0 {
        lemma_pop_until_cell_popped(pop(p));
    }
}

/// A start tag "in cell" closes the cell for: "caption", "col", "colgroup",
/// "tbody", "td", "tfoot", "th", "thead", "tr".
pub open spec fn in_cell_closing_start(t: Tok) -> bool {
    let tag = w3c_tag(t);
    t is Start && (tag == Tag::Caption || tag == Tag::Col || tag == Tag::Colgroup || tag == Tag::Tbody || tag == Tag::Td || tag
        == Tag::Tfoot || tag == Tag::Th || tag == Tag::Thead || tag == Tag::Tr)
}

/// "in cell" (W3C §8.2.5.4.15, WHATWG §13.2.6.4.15): the same rules (with
/// the reading of "the same tag name" of [`lemma_in_table_body`]), but for
/// one difference: for a start tag `caption`, …, `tr` the W3C checks that
/// the stack has a `td` or `th` element in table scope and ignores the
/// token if not ("fragment case"); the WHATWG text *asserts* it ("Assert:
/// the stack of open elements has a td or th element in table scope") and
/// closes the cell. Excluded when the stack has none.
pub proof fn lemma_in_cell(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
        tags_wf(p),
        token_tagged(t),
        in_cell_closing_start(t) ==> in_scope_from(
            p.open,
            p.open.len() as int,
            |e: Elem| is_html(e, Tag::Td) || is_html(e, Tag::Th),
            Scope::Table,
        ),
    ensures
        w3c_mode_in_cell(env, p, t) == mode_in_cell(env, p, t),
{
    lemma_closure_ext();
    lemma_table_tags_injective();
    lemma_pop_until_cell_popped(generate_implied_end_tags(p, None));
}

/// "in template" (W3C §8.2.5.4.18, WHATWG §13.2.6.4.16): the same rules.
pub proof fn lemma_in_template(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
    ensures
        w3c_mode_in_template(env, p, t) == mode_in_template(env, p, t),
{
}

} // verus!
