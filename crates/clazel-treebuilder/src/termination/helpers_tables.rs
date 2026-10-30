//! Helper lemmas for the edge lemmas of the table modes ([`super::tables`]):
//! what the spec's stack helpers keep and change, where "reset the
//! insertion mode appropriately" lands, and which outcomes the "in table"
//! insertion mode's "anything else" entry (a direct call of the "in body"
//! rules) can return.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The stack of open elements

/// `a` is a prefix of `b`.
pub open spec fn is_prefix(a: Seq<Elem>, b: Seq<Elem>) -> bool {
    a.len() <= b.len() && forall|j: int| 0 <= j < a.len() ==> #[trigger] a[j] == b[j]
}

/// Popping a non-empty stack shortens it by one and changes nothing else.
pub proof fn lemma_pop(p: Parser)
    requires
        p.open.len() > 0,
    ensures
        pop(p) == (Parser { open: pop(p).open, ..p }),
        pop(p).open.len() == p.open.len() - 1,
        is_prefix(pop(p).open, p.open),
{
}

/// `pop_while` keeps every field but `open`, leaves a prefix of the stack,
/// and stops at (keeps) any entry that does not satisfy its predicate.
pub proof fn lemma_pop_while(p: Parser, f: spec_fn(Elem) -> bool)
    ensures
        pop_while(p, f) == (Parser { open: pop_while(p, f).open, ..p }),
        is_prefix(pop_while(p, f).open, p.open),
        forall|i: int| 0 <= i < p.open.len() && !f(#[trigger] p.open[i]) ==> pop_while(p, f).open.len() > i,
    decreases p.open.len(),
{
    if p.open.len() > 0 && f(current_node(p)) {
        lemma_pop(p);
        lemma_pop_while(pop(p), f);
        assert forall|i: int| 0 <= i < p.open.len() && !f(#[trigger] p.open[i]) implies pop_while(p, f).open.len() > i by {
            assert(i != p.open.len() - 1);
            assert(pop(p).open[i] == p.open[i]);
        }
    }
}

/// [`lemma_pop_while`] for every predicate (so that it applies to the
/// closures of the spec's "clear the stack back to …" algorithms).
pub proof fn lemma_pop_while_all(p: Parser)
    ensures
        forall|f: spec_fn(Elem) -> bool|
            {
                &&& #[trigger] pop_while(p, f) == (Parser { open: pop_while(p, f).open, ..p })
                &&& is_prefix(pop_while(p, f).open, p.open)
                &&& forall|i: int| 0 <= i < p.open.len() && !f(#[trigger] p.open[i]) ==> pop_while(p, f).open.len() > i
            },
{
    assert forall|f: spec_fn(Elem) -> bool|
        {
            &&& #[trigger] pop_while(p, f) == (Parser { open: pop_while(p, f).open, ..p })
            &&& is_prefix(pop_while(p, f).open, p.open)
            &&& forall|i: int| 0 <= i < p.open.len() && !f(#[trigger] p.open[i]) ==> pop_while(p, f).open.len() > i
        } by {
        lemma_pop_while(p, f);
    }
}

/// `pop_until_popped` keeps every field but `open`, leaves a prefix of the
/// stack, and pops at least one entry off a non-empty stack.
pub proof fn lemma_pop_until_popped(p: Parser, tag: Tag)
    ensures
        pop_until_popped(p, tag) == (Parser { open: pop_until_popped(p, tag).open, ..p }),
        is_prefix(pop_until_popped(p, tag).open, p.open),
        p.open.len() > 0 ==> pop_until_popped(p, tag).open.len() < p.open.len(),
    decreases p.open.len(),
{
    if p.open.len() > 0 {
        lemma_pop(p);
        if !is_html(current_node(p), tag) {
            lemma_pop_until_popped(pop(p), tag);
        }
    }
}

/// `pop_until_cell_popped` keeps every field but `open` and leaves a prefix
/// of the stack.
pub proof fn lemma_pop_until_cell_popped(p: Parser)
    ensures
        pop_until_cell_popped(p) == (Parser { open: pop_until_cell_popped(p).open, ..p }),
        pop_until_cell_popped(p).open.len() <= p.open.len(),
        is_prefix(pop_until_cell_popped(p).open, p.open),
    decreases p.open.len(),
{
    if p.open.len() > 0 {
        lemma_pop(p);
        if !(is_html(current_node(p), Tag::Td) || is_html(current_node(p), Tag::Th)) {
            lemma_pop_until_cell_popped(pop(p));
        }
    }
}

/// `clear_to_last_marker` changes only the list of active formatting
/// elements.
pub proof fn lemma_clear_to_last_marker(p: Parser)
    ensures
        clear_to_last_marker(p) == (Parser { formatting: clear_to_last_marker(p).formatting, ..p }),
    decreases p.formatting.len(),
{
    if p.formatting.len() > 0 {
        let q = Parser { formatting: p.formatting.drop_last(), ..p };
        if !(p.formatting.last() is Marker) {
            lemma_clear_to_last_marker(q);
        }
    }
}

/// "close the cell" keeps the template modes and the original insertion
/// mode, never lengthens the stack, adds no `template` element, keeps the
/// list of active formatting elements fine, and switches to "in row".
pub proof fn lemma_close_the_cell(p: Parser)
    ensures
        close_the_cell(p).template_modes == p.template_modes,
        close_the_cell(p).original_mode == p.original_mode,
        close_the_cell(p).mode == Mode::InRow,
        close_the_cell(p).open.len() <= p.open.len(),
        close_the_cell(p).pending_table_text == p.pending_table_text,
        template_count(close_the_cell(p)) <= template_count(p),
        formatting_ok(p) ==> formatting_ok(close_the_cell(p)),
{
    lemma_pop_while_all(p);
    let p1 = generate_implied_end_tags(p, None);
    lemma_pop_until_cell_popped(p1);
    let p2 = pop_until_cell_popped(p1);
    super::helpers_ranking::lemma_clear_to_last_marker(p2);
    super::helpers_ranking::lemma_template_count_prefix(p, p1);
    super::helpers_ranking::lemma_template_count_prefix(p1, p2);
}

/// The stack has an entry satisfying `target` below index `i` when
/// `in_scope_from` holds (the witness).
pub open spec fn scope_witness(open: Seq<Elem>, i: int, target: spec_fn(Elem) -> bool, s: Scope) -> int
    decreases i,
{
    if i <= 0 {
        -1
    } else if target(open[i - 1]) {
        i - 1
    } else {
        scope_witness(open, i - 1, target, s)
    }
}

/// [`scope_witness`] is an index of an entry satisfying the target.
pub proof fn lemma_scope_witness(open: Seq<Elem>, i: int, target: spec_fn(Elem) -> bool, s: Scope)
    requires
        i <= open.len(),
        in_scope_from(open, i, target, s),
    ensures
        0 <= scope_witness(open, i, target, s) < i,
        target(open[scope_witness(open, i, target, s)]),
    decreases i,
{
    if i > 0 && !target(open[i - 1]) {
        lemma_scope_witness(open, i - 1, target, s);
    }
}

/// [`lemma_scope_witness`] for every target and scope, from the top of the
/// stack.
pub proof fn lemma_scope_witness_all(open: Seq<Elem>)
    ensures
        forall|target: spec_fn(Elem) -> bool, s: Scope|
            #[trigger] in_scope_from(open, open.len() as int, target, s) ==> 0 <= scope_witness(open, open.len() as int, target, s)
                < open.len() && target(open[scope_witness(open, open.len() as int, target, s)]),
{
    assert forall|target: spec_fn(Elem) -> bool, s: Scope|
        #[trigger] in_scope_from(open, open.len() as int, target, s) implies 0 <= scope_witness(open, open.len() as int, target, s)
            < open.len() && target(open[scope_witness(open, open.len() as int, target, s)]) by {
        lemma_scope_witness(open, open.len() as int, target, s);
    }
}

// ---------------------------------------------------------------------
// Inserting

/// `create` keeps the modes and never lengthens the stack.
pub proof fn lemma_create(p: Parser, k: NodeKind)
    ensures
        create(p, k).0.template_modes == p.template_modes,
        create(p, k).0.mode == p.mode,
        create(p, k).0.original_mode == p.original_mode,
        create(p, k).0.open.len() <= p.open.len(),
{
}

/// "Insert an HTML element" keeps the modes and lengthens the stack by at
/// most one.
pub proof fn lemma_insert_html_element(p: Parser, t: TagTok)
    ensures
        insert_html_element(p, t).0.template_modes == p.template_modes,
        insert_html_element(p, t).0.mode == p.mode,
        insert_html_element(p, t).0.original_mode == p.original_mode,
        insert_html_element(p, t).0.open.len() <= p.open.len() + 1,
{
    let ns = Namespace::Html;
    let parent = appropriate_place(p, None).parent;
    let owner = if is_form_associated(ns, t.tag) && p.form is Some && !parsing_template_contents(p) && p.context is None && (
    !is_listed(ns, t.tag) || !has_attr(t, name_form())) && same_tree(p.doc, parent, p.form->Some_0) {
        p.form
    } else {
        None
    };
    let k = NodeKind::Element {
        namespace: Some(ns),
        prefix: None,
        local_name: t.name,
        attributes: t.attrs,
        template_contents: None,
        form_owner: owner,
    };
    lemma_create(p, k);
    let (p2, e) = create_element_for_token(p, t, ns, parent);
    assert(p2.template_modes == p.template_modes && p2.mode == p.mode && p2.original_mode == p.original_mode
        && p2.open.len() <= p.open.len());
    let p3 = insert_element_at(p2, e.id, None);
    assert(p3.template_modes == p.template_modes && p3.mode == p.mode && p3.original_mode == p.original_mode
        && p3.open.len() <= p.open.len());
}

/// "Insert a character" keeps the modes and never lengthens the stack.
pub proof fn lemma_insert_characters(p: Parser, data: Seq<u32>)
    ensures
        insert_characters(p, data).template_modes == p.template_modes,
        insert_characters(p, data).mode == p.mode,
        insert_characters(p, data).original_mode == p.original_mode,
        insert_characters(p, data).open.len() <= p.open.len(),
{
    lemma_create(p, NodeKind::Text { data });
}

// ---------------------------------------------------------------------
// Reset the insertion mode appropriately

/// The modes "reset the insertion mode appropriately" can land on.
pub open spec fn reset_mode_ok(m: Mode) -> bool {
    m != Mode::Text && m != Mode::InTableText && m != Mode::Initial && m != Mode::BeforeHtml && m != Mode::InHeadNoscript
}

/// A mode "reset the insertion mode appropriately" lands on gives a `table`
/// start tag a growth budget of at most 2.
pub proof fn lemma_reset_mode_growth_table(m: Mode, t: Tok)
    requires
        reset_mode_ok(m),
        is_start(t, Tag::Table),
    ensures
        growth(Rules::Html(m), t) <= 2,
{
}

/// Every mode but "text" and "in table text" gives a growth budget of at
/// most 4.
pub proof fn lemma_growth_le_4(m: Mode, t: Tok)
    requires
        m != Mode::Text,
        m != Mode::InTableText,
    ensures
        growth(Rules::Html(m), t) <= 4,
{
}

// ---------------------------------------------------------------------
// The "in table" insertion mode's "anything else" entry

/// The tokens that reach the "in table" insertion mode's "anything else"
/// entry (case 17) or its "input" case's fallthrough to it.
pub open spec fn in_table_else_tok(t: Tok) -> bool {
    match t {
        Tok::Char(_) => true,
        Tok::Start(tt) => match tt.tag {
            Tag::Caption | Tag::Colgroup | Tag::Col | Tag::Tbody | Tag::Tfoot | Tag::Thead | Tag::Td | Tag::Th | Tag::Tr
            | Tag::Table | Tag::Style | Tag::Script | Tag::Template | Tag::Form => false,
            _ => true,
        },
        Tok::End(tt) => match tt.tag {
            Tag::Table | Tag::Body | Tag::Caption | Tag::Col | Tag::Colgroup | Tag::Html | Tag::Tbody | Tag::Td
            | Tag::Tfoot | Tag::Th | Tag::Thead | Tag::Tr | Tag::Template => false,
            _ => true,
        },
        _ => false,
    }
}

/// For the tokens that reach it, the "in body" rules called by the "in
/// table" insertion mode's "anything else" entry finish the token
/// themselves, send it to the "in head" rules (which finish it), or turn an
/// `image` start tag into `img` and reprocess it (which lowers `img`).
#[verifier::spinoff_prover]
pub proof fn lemma_in_table_anything_else_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        p.mode != Mode::Text,
        p.mode != Mode::InTableText,
        in_table_else_tok(t),
    ensures
        edge_ok(Rules::Html(Mode::InTable), p, t, in_table_anything_else(env, p, t)),
{
    hide(in_body_start_tag);
    hide(in_body_end_tag);
    hide(in_body_char);
    hide(in_body_eof);
    hide(mode_in_head);
    let pf = Parser { foster: true, ..p };
    match t {
        Tok::Start(tt) => {
            super::helpers_in_body::lemma_in_body_start_tag_outcome(pf, t, tt);
            match in_body_start_tag(pf, t, tt) {
                Outcome::Using(_, _, _) => {
                    lemma_in_head_start_done(env, pf, t);
                },
                Outcome::Reprocess(q0, t2) => {
                    let q = Parser { foster: false, ..pf };
                    assert(in_table_anything_else(env, p, t) == Outcome::Reprocess(q, t2));
                    lemma_components_bounded(Rules::Html(q.mode), t2);
                    assert(img(t) == 1);
                    assert(img(t2) == 0);
                    super::helpers_ranking::lemma_modes_ok_from(p, q);
                    lemma_growth_le_4(q.mode, t2);
                },
                Outcome::Done(_) => {},
            }
        },
        Tok::End(tt) => {
            super::helpers_in_body::lemma_in_body_end_tag_outcome(pf, t, tt);
        },
        _ => {},
    }
}

/// The "in head" rules finish the "in head" start tags the "in body" rules
/// send them from the "in table" insertion mode's "anything else" entry.
#[verifier::spinoff_prover]
pub proof fn lemma_in_head_start_done(env: EncFns, p: Parser, t: Tok)
    requires
        t is Start,
        is_in_head_start_tag(t->Start_0.tag),
        in_table_else_tok(t),
    ensures
        mode_in_head(env, p, t) is Done,
{
    hide(insert_html_element);
    hide(pop);
    hide(in_head_meta);
    hide(generic_text_parsing);
    hide(in_head_script);
    hide(in_head_template_start);
    hide(in_head_template_end);
    hide(in_head_anything_else);
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
}

} // verus!
