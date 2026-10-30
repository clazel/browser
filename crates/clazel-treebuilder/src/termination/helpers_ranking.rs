//! Helper lemmas shared by the edge lemmas (see [`super`]): how the spec's
//! stack helpers change the number of `template` elements on the stack
//! ([`templates_in`]), where "reset the insertion mode appropriately"
//! lands under [`modes_ok`], how far "reconstruct the active formatting
//! elements" and the "in table text" mode's reprocessing of the pending
//! characters can grow the stack, and when [`modes_ok`] carries over.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {


// ---------------------------------------------------------------------
// Counting template elements

/// The number of `template` elements on the whole stack.
pub open spec fn tcount(open: Seq<Elem>) -> nat {
    templates_in(open, open.len() as int)
}

/// Equal entries below `i` give equal counts.
pub proof fn lemma_templates_in_same(a: Seq<Elem>, b: Seq<Elem>, i: int)
    requires
        i <= a.len(),
        i <= b.len(),
        forall|j: int| 0 <= j < i ==> a[j] == b[j],
    ensures
        templates_in(a, i) == templates_in(b, i),
    decreases i,
{
    if i > 0 {
        lemma_templates_in_same(a, b, i - 1);
    }
}

/// The count only grows with `i`.
pub proof fn lemma_templates_in_mono(s: Seq<Elem>, i: int, j: int)
    requires
        i <= j,
    ensures
        templates_in(s, i) <= templates_in(s, j),
    decreases j - i,
{
    if j > i {
        lemma_templates_in_mono(s, i, j - 1);
    }
}

/// A prefix has no more `template` elements.
pub proof fn lemma_tcount_prefix(a: Seq<Elem>, b: Seq<Elem>)
    requires
        super::helpers_tables::is_prefix(a, b),
    ensures
        tcount(a) <= tcount(b),
{
    lemma_templates_in_same(a, b, a.len() as int);
    lemma_templates_in_mono(b, a.len() as int, b.len() as int);
}

/// Pushing an element that is not a `template` keeps the count.
pub proof fn lemma_tcount_push(a: Seq<Elem>, e: Elem)
    requires
        !is_html(e, Tag::Template),
    ensures
        tcount(a.push(e)) == tcount(a),
{
    let b = a.push(e);
    assert(templates_in(b, b.len() as int) == templates_in(b, a.len() as int));
    lemma_templates_in_same(a, b, a.len() as int);
}

/// A `template` element below `i` makes the count positive.
pub proof fn lemma_templates_in_pos(s: Seq<Elem>, i: int, j: int)
    requires
        0 <= j < i,
        is_html(s[j], Tag::Template),
    ensures
        templates_in(s, i) >= 1,
    decreases i,
{
    if j < i - 1 {
        lemma_templates_in_pos(s, i - 1, j);
    }
}

/// [`last_index_where`] is -1 or an index below `i` satisfying `f`.
pub proof fn lemma_last_index_where(open: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool)
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

/// The count of the whole parser: [`template_count`].
pub proof fn lemma_template_count(p: Parser)
    ensures
        template_count(p) == tcount(p.open) + if p.context is Some && is_html(p.context->Some_0, Tag::Template) {
            1nat
        } else {
            0nat
        },
{
}

// ---------------------------------------------------------------------
// Popping

/// "Pop the current node": a prefix, every other field kept.
pub proof fn lemma_pop(p: Parser)
    ensures
        pop(p) == (Parser { open: pop(p).open, ..p }),
        super::helpers_tables::is_prefix(pop(p).open, p.open),
        p.open.len() > 0 ==> pop(p).open.len() == p.open.len() - 1,
        tcount(pop(p).open) <= tcount(p.open),
        template_count(pop(p)) <= template_count(p),
{
    if p.open.len() > 0 {
        super::helpers_tables::lemma_pop(p);
    }
    lemma_tcount_prefix(pop(p).open, p.open);
}

/// A parser whose stack is a prefix and whose context is the same has no
/// more `template` elements.
pub proof fn lemma_template_count_prefix(p: Parser, q: Parser)
    requires
        super::helpers_tables::is_prefix(q.open, p.open),
        q.context == p.context,
    ensures
        template_count(q) <= template_count(p),
{
    lemma_tcount_prefix(q.open, p.open);
}

/// `pop_until_popped` of a stack holding a `template` element, for the tag
/// `template`, pops at least one `template` element.
pub proof fn lemma_pop_until_template(p: Parser, j: int)
    requires
        0 <= j < p.open.len(),
        is_html(p.open[j], Tag::Template),
    ensures
        tcount(pop_until_popped(p, Tag::Template).open) + 1 <= tcount(p.open),
    decreases p.open.len(),
{
    let n = p.open.len() as int;
    let q = pop(p);
    super::helpers_tables::lemma_pop(p);
    lemma_templates_in_same(q.open, p.open, n - 1);
    if is_html(current_node(p), Tag::Template) {
        assert(templates_in(p.open, n) == templates_in(p.open, n - 1) + 1);
    } else {
        assert(j < n - 1);
        assert(templates_in(p.open, n) == templates_in(p.open, n - 1));
        assert(q.open[j] == p.open[j]);
        lemma_pop_until_template(q, j);
    }
}

/// [`open_has_html`] gives an index.
pub proof fn lemma_open_has_html(p: Parser, tag: Tag) -> (j: int)
    requires
        open_has_html(p, tag),
    ensures
        0 <= j < p.open.len(),
        is_html(p.open[j], tag),
{
    lemma_last_index_where(p.open, p.open.len() as int, |e: Elem| is_html(e, tag));
    last_index_where(p.open, p.open.len() as int, |e: Elem| is_html(e, tag))
}

/// `clear_to_last_marker` keeps a prefix of the list and every other field.
pub proof fn lemma_clear_to_last_marker(p: Parser)
    ensures
        clear_to_last_marker(p) == (Parser { formatting: clear_to_last_marker(p).formatting, ..p }),
        clear_to_last_marker(p).formatting.len() <= p.formatting.len(),
        forall|i: int| 0 <= i < clear_to_last_marker(p).formatting.len() ==> #[trigger] clear_to_last_marker(p).formatting[i] == p.formatting[i],
        formatting_ok(p) ==> formatting_ok(clear_to_last_marker(p)),
    decreases p.formatting.len(),
{
    if p.formatting.len() > 0 {
        let q = Parser { formatting: p.formatting.drop_last(), ..p };
        if !(p.formatting.last() is Marker) {
            lemma_clear_to_last_marker(q);
        }
    }
    let r = clear_to_last_marker(p);
    if formatting_ok(p) {
        assert forall|i: int| 0 <= i < r.formatting.len() && #[trigger] r.formatting[i] is Entry implies r.formatting[i]->Entry_token.tag
            != Tag::Template by {
            assert(r.formatting[i] == p.formatting[i]);
        }
    }
}

// ---------------------------------------------------------------------
// Reset the insertion mode appropriately

/// The count bound of [`modes_ok`] with the template modes it constrains.
pub open spec fn count_ok(p: Parser) -> bool {
    &&& forall|i: int| 0 <= i < p.template_modes.len() ==> template_mode_ok(#[trigger] p.template_modes[i])
    &&& template_count(p) <= p.template_modes.len()
}

/// Where [`reset_from`] lands: a mode with a known budget, and "in
/// template" only with a non-empty stack of template insertion modes
/// (reaching a `template` element, or a `template` context, means the
/// count, hence the stack of template modes, is positive).
pub proof fn lemma_reset_from(p: Parser, i: int)
    requires
        count_ok(p),
        i < p.open.len(),
    ensures
        super::helpers_tables::reset_mode_ok(reset_from(p, i)),
        reset_from(p, i) == Mode::InTemplate ==> p.template_modes.len() > 0,
        template_mode_ok(reset_from(p, i)) || reset_from(p, i) != Mode::InTemplate,
    decreases i,
{
    if i >= 0 {
        let last = i == 0;
        let node = if last && p.context is Some {
            p.context->Some_0
        } else {
            p.open[i]
        };
        if is_html(node, Tag::Template) {
            if last && p.context is Some {
                assert(template_count(p) >= 1);
            } else {
                lemma_templates_in_pos(p.open, p.open.len() as int, i);
                assert(template_count(p) >= 1);
            }
            assert(p.template_modes.len() > 0);
            assert(template_mode_ok(p.template_modes[p.template_modes.len() - 1]));
        }
        if i >= 1 {
            lemma_reset_from(p, i - 1);
        }
    }
}

/// "Reset the insertion mode appropriately" with the count bound gives a
/// parser satisfying [`modes_ok`] when everything else does.
pub proof fn lemma_reset_modes_ok(p: Parser)
    requires
        count_ok(p),
        formatting_ok(p),
    ensures
        modes_ok(reset_insertion_mode(p)),
        super::helpers_tables::reset_mode_ok(reset_insertion_mode(p).mode),
{
    lemma_reset_from(p, p.open.len() - 1);
}

// ---------------------------------------------------------------------
// Carrying modes_ok over

/// [`modes_ok`] of a parser with the same template modes, no more
/// `template` elements, a list of active formatting elements that is fine,
/// and a mode (and original mode) that is fine.
pub proof fn lemma_modes_ok_from(p: Parser, q: Parser)
    requires
        modes_ok(p),
        q.template_modes == p.template_modes,
        template_count(q) <= template_count(p),
        formatting_ok(q),
        q.mode == Mode::InTableText ==> q.original_mode != Mode::Text && q.original_mode != Mode::InTableText,
        q.mode == Mode::Text ==> q.original_mode != Mode::Text && q.original_mode != Mode::InTableText,
        q.mode == Mode::InTemplate ==> p.template_modes.len() > 0,
        (q.mode == Mode::Text || q.mode == Mode::InTableText) && q.original_mode == Mode::InTemplate ==> p.template_modes.len() > 0,
    ensures
        modes_ok(q),
{
}

/// The same with the list of active formatting elements a prefix.
pub proof fn lemma_formatting_ok_prefix(p: Parser, q: Parser)
    requires
        formatting_ok(p),
        q.formatting.len() <= p.formatting.len(),
        forall|i: int| 0 <= i < q.formatting.len() ==> #[trigger] q.formatting[i] == p.formatting[i],
    ensures
        formatting_ok(q),
{
    assert forall|i: int| 0 <= i < q.formatting.len() && #[trigger] q.formatting[i] is Entry implies q.formatting[i]->Entry_token.tag
        != Tag::Template by {
        assert(q.formatting[i] == p.formatting[i]);
    }
}

// ---------------------------------------------------------------------
// Inserting

/// The fields the insertion algorithms keep.
pub open spec fn frame(p: Parser, q: Parser) -> bool {
    &&& q.template_modes == p.template_modes
    &&& q.mode == p.mode
    &&& q.original_mode == p.original_mode
    &&& q.context == p.context
    &&& q.pending_table_text == p.pending_table_text
    &&& q.formatting == p.formatting
}

/// `stop_parsing` empties the stack and keeps the frame.
pub proof fn lemma_stop_parsing(p: Parser)
    ensures
        frame(p, stop_parsing(p)),
        stop_parsing(p).open == p.open || stop_parsing(p).open.len() == 0,
{
}

/// `create` keeps the frame and the stack, or empties it.
pub proof fn lemma_create(p: Parser, k: NodeKind)
    ensures
        frame(p, create(p, k).0),
        create(p, k).0.open == p.open || create(p, k).0.open.len() == 0,
{
}

/// "Create an element for a token" keeps the frame and the stack, or
/// empties it, and makes an HTML element of the token's tag.
pub proof fn lemma_create_element_for_token(p: Parser, t: TagTok, intended_parent: NodeId)
    ensures
        frame(p, create_element_for_token(p, t, Namespace::Html, intended_parent).0),
        create_element_for_token(p, t, Namespace::Html, intended_parent).0.open == p.open || create_element_for_token(
            p,
            t,
            Namespace::Html,
            intended_parent,
        ).0.open.len() == 0,
        create_element_for_token(p, t, Namespace::Html, intended_parent).1.ns == Namespace::Html,
        create_element_for_token(p, t, Namespace::Html, intended_parent).1.tag == t.tag,
{
    let ns = Namespace::Html;
    let owner = if is_form_associated(ns, t.tag) && p.form is Some && !parsing_template_contents(p) && p.context is None && (
    !is_listed(ns, t.tag) || !has_attr(t, name_form())) && same_tree(p.doc, intended_parent, p.form->Some_0) {
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
    let p1 = create(p, k).0;
    lemma_stop_parsing(p1);
}

/// "Insert an element at the adjusted insertion location" changes only the
/// document.
pub proof fn lemma_insert_element_at(p: Parser, el: NodeId, loc: Option<Location>)
    ensures
        frame(p, insert_element_at(p, el, loc)),
        insert_element_at(p, el, loc).open == p.open,
{
}

/// Pushing a created element: the stack is kept, emptied, or gains one
/// element that is not a `template`, and the count does not grow.
pub proof fn lemma_push_counts(p: Parser, q: Parser)
    requires
        q.open == p.open || q.open.len() == 0,
    ensures
        q.open.len() <= p.open.len(),
        tcount(q.open) <= tcount(p.open),
{
    if q.open.len() == 0 {
    }
}

/// Pushing an element that is not a `template` onto a parser whose stack is
/// that of `p` or empty.
pub proof fn lemma_push_created(p: Parser, p2: Parser, e: Elem)
    requires
        frame(p, p2),
        p2.open == p.open || p2.open.len() == 0,
        !is_html(e, Tag::Template),
    ensures
        frame(p, push(p2, e)),
        push(p2, e).open.len() <= p.open.len() + 1,
        tcount(push(p2, e).open) <= tcount(p.open),
        template_count(push(p2, e)) <= template_count(p),
{
    let p3 = push(p2, e);
    if p2.stopped {
        lemma_push_counts(p, p3);
    } else if p2.open == p.open {
        assert(p3.open == p.open.push(e));
        lemma_tcount_push(p.open, e);
    } else {
        assert(p3.open == p2.open.push(e));
        assert(p3.open.len() == 1);
        assert(templates_in(p3.open, 1) == templates_in(p3.open, 0));
    }
}

/// "Insert an HTML element" for a token other than `template`: the frame is
/// kept, the stack grows by at most one, and the count does not grow.
pub proof fn lemma_insert_html_element(p: Parser, tt: TagTok)
    requires
        tt.tag != Tag::Template,
    ensures
        frame(p, insert_html_element(p, tt).0),
        insert_html_element(p, tt).0.open.len() <= p.open.len() + 1,
        tcount(insert_html_element(p, tt).0.open) <= tcount(p.open),
        template_count(insert_html_element(p, tt).0) <= template_count(p),
{
    let parent = appropriate_place(p, None).parent;
    lemma_create_element_for_token(p, tt, parent);
    let (p1, e) = create_element_for_token(p, tt, Namespace::Html, parent);
    lemma_insert_element_at(p1, e.id, None);
    let p2 = insert_element_at(p1, e.id, None);
    lemma_push_created(p, p2, e);
}

/// "template"
pub open spec fn name_template() -> Seq<u32> {
    seq![0x74u32, 0x65u32, 0x6du32, 0x70u32, 0x6cu32, 0x61u32, 0x74u32, 0x65u32]
}

/// Only the name "template" is the tag `template`.
pub proof fn lemma_tag_of_template(name: Seq<u32>)
    ensures
        tag_of(name) == Tag::Template ==> name == name_template(),
{
}

/// A name that is not "template" (another length, or another first code
/// point) is not the tag `template`.
pub proof fn lemma_not_template(name: Seq<u32>)
    requires
        name.len() != 8 || (name.len() > 0 && name[0] != 0x74u32),
    ensures
        tag_of(name) != Tag::Template,
{
    lemma_tag_of_template(name);
    if tag_of(name) == Tag::Template {
        assert(name_template().len() == 8);
        assert(name_template()[0] == 0x74u32);
    }
}

/// "Insert a character" keeps the frame and the stack, or empties it.
pub proof fn lemma_insert_characters(p: Parser, data: Seq<u32>)
    ensures
        frame(p, insert_characters(p, data)),
        insert_characters(p, data).open == p.open || insert_characters(p, data).open.len() == 0,
{
    lemma_create(p, NodeKind::Text { data });
}

/// [`lemma_insert_characters`]'s stack in numbers.
pub proof fn lemma_insert_characters_counts(p: Parser, data: Seq<u32>)
    ensures
        frame(p, insert_characters(p, data)),
        insert_characters(p, data).open.len() <= p.open.len(),
        tcount(insert_characters(p, data).open) <= tcount(p.open),
{
    lemma_insert_characters(p, data);
    lemma_push_counts(p, insert_characters(p, data));
}

// ---------------------------------------------------------------------
// Reconstructing the active formatting elements

/// Steps 7 to 10 from entry `i`: at most one element per remaining entry,
/// none a `template`, and the list keeps its length and stays fine.
pub proof fn lemma_reconstruct_create(p: Parser, i: int)
    requires
        0 <= i <= p.formatting.len(),
        formatting_ok(p),
    ensures
        ({
            let q = reconstruct_create(p, i);
            &&& q.template_modes == p.template_modes
            &&& q.mode == p.mode
            &&& q.original_mode == p.original_mode
            &&& q.context == p.context
            &&& q.pending_table_text == p.pending_table_text
            &&& q.formatting.len() == p.formatting.len()
            &&& formatting_ok(q)
            &&& q.open.len() <= p.open.len() + (p.formatting.len() - i)
            &&& tcount(q.open) <= tcount(p.open)
        }),
    decreases p.formatting.len() - i,
{
    if i < 0 || i >= p.formatting.len() || p.stopped || !(p.formatting[i] is Entry) {
    } else {
        let token = p.formatting[i]->Entry_token;
        assert(token.tag != Tag::Template);
        lemma_insert_html_element(p, token);
        let (p1, new_element) = insert_html_element(p, token);
        let p2 = if p1.stopped {
            p1
        } else {
            Parser { formatting: p1.formatting.update(i, Fmt::Entry { elem: new_element, token }), ..p1 }
        };
        assert(p2.formatting.len() == p.formatting.len());
        assert(formatting_ok(p2)) by {
            assert forall|k: int| 0 <= k < p2.formatting.len() && #[trigger] p2.formatting[k] is Entry implies p2.formatting[k]->Entry_token.tag
                != Tag::Template by {
                if k != i {
                    assert(p2.formatting[k] == p.formatting[k]);
                }
            }
        }
        if i + 1 < p2.formatting.len() && p2.formatting.len() == p.formatting.len() {
            lemma_reconstruct_create(p2, i + 1);
            assert(p2.open.len() <= p.open.len() + 1);
        }
    }
}

/// [`reconstruct_rewind`] is not negative.
pub proof fn lemma_reconstruct_rewind(p: Parser, i: int)
    requires
        i >= 0,
    ensures
        0 <= reconstruct_rewind(p, i) <= i,
    decreases i,
{
    if i > 0 {
        let e = p.formatting[i - 1];
        if !(e is Marker) && !fmt_on_stack(p, e) {
            lemma_reconstruct_rewind(p, i - 1);
        }
    }
}

/// "Reconstruct the active formatting elements" pushes at most one element
/// per entry of the list, none a `template`, and keeps the list's length.
pub proof fn lemma_reconstruct_formatting(p: Parser)
    requires
        formatting_ok(p),
    ensures
        ({
            let q = reconstruct_formatting(p);
            &&& q.template_modes == p.template_modes
            &&& q.mode == p.mode
            &&& q.original_mode == p.original_mode
            &&& q.context == p.context
            &&& q.pending_table_text == p.pending_table_text
            &&& q.formatting.len() == p.formatting.len()
            &&& formatting_ok(q)
            &&& q.open.len() <= p.open.len() + p.formatting.len()
            &&& tcount(q.open) <= tcount(p.open)
        }),
{
    let n = p.formatting.len();
    if n == 0 {
    } else if p.formatting[n - 1] is Marker || fmt_on_stack(p, p.formatting[n - 1]) {
    } else {
        lemma_reconstruct_rewind(p, n - 1);
        lemma_reconstruct_create(p, reconstruct_rewind(p, n - 1));
    }
}

/// The "in body" rules for a character token (cases 1 to 3), as the "in
/// table" insertion mode's "anything else" entry applies them.
pub proof fn lemma_in_table_char(env: EncFns, p: Parser, c: u32)
    requires
        formatting_ok(p),
    ensures
        ({
            let q = outcome_parser(in_table_anything_else(env, p, Tok::Char(c)));
            &&& q.template_modes == p.template_modes
            &&& q.mode == p.mode
            &&& q.original_mode == p.original_mode
            &&& q.context == p.context
            &&& q.pending_table_text == p.pending_table_text
            &&& q.formatting.len() == p.formatting.len()
            &&& formatting_ok(q)
            &&& q.open.len() <= p.open.len() + p.formatting.len()
            &&& tcount(q.open) <= tcount(p.open)
        }),
{
    let pf = Parser { foster: true, ..p };
    assert(formatting_ok(pf));
    lemma_reconstruct_formatting(pf);
    let r = reconstruct_formatting(pf);
    lemma_insert_characters_counts(r, seq![c]);
    assert(in_table_anything_else(env, p, Tok::Char(c)) == outcome_without_foster(Outcome::Done(in_body_char(pf, c))));
}

/// Reprocessing the pending characters from index `i` pushes at most one
/// element per entry of the list for each.
pub proof fn lemma_reprocess_pending(env: EncFns, p: Parser, s: Seq<u32>, i: int)
    requires
        0 <= i <= s.len(),
        formatting_ok(p),
    ensures
        ({
            let q = reprocess_pending(env, p, s, i);
            &&& q.template_modes == p.template_modes
            &&& q.mode == p.mode
            &&& q.original_mode == p.original_mode
            &&& q.context == p.context
            &&& q.pending_table_text == p.pending_table_text
            &&& q.formatting.len() == p.formatting.len()
            &&& formatting_ok(q)
            &&& q.open.len() <= p.open.len() + p.formatting.len() * (s.len() - i)
            &&& tcount(q.open) <= tcount(p.open)
        }),
    decreases s.len() - i,
{
    hide(in_table_anything_else);
    if i < s.len() {
        lemma_in_table_char(env, p, s[i]);
        let q = outcome_parser(in_table_anything_else(env, p, Tok::Char(s[i])));
        lemma_reprocess_pending(env, q, s, i + 1);
        let r = reprocess_pending(env, q, s, i + 1);
        assert(r == reprocess_pending(env, p, s, i));
        let f = p.formatting.len() as int;
        let k = s.len() - i;
        assert(f + f * (k - 1) == f * k) by (nonlinear_arith);
    } else {
        let k = s.len() - i;
        assert(k == 0);
        assert(p.formatting.len() * k == 0) by (nonlinear_arith) requires k == 0;
    }
}

} // verus!
