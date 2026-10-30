//! The helpers of the list of active formatting elements, "reconstruct the
//! active formatting elements", "reset the insertion mode appropriately"
//! and the "in body" loops [`keeps`] a live parser (see [`super`]).

#[cfg(verus_only)]
use super::cells::*;
#[cfg(verus_only)]
use super::helpers::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// An entry that may join the list of a [`good`] parser: a marker, or an
/// element other than `html`'s, tagged, not a cell, with an id of the
/// arena that no cell on the stack has ([`id_new`]), for a tagged token
/// with plain attributes other than `template`, `td`, `th`, `html` and
/// `table`.
pub open spec fn fmt_fresh(p: Parser, x: Fmt) -> bool {
    match x {
        Fmt::Marker => true,
        Fmt::Entry { elem, token } => elem.id != p.open[0].id && elem_tagged(elem) && tok_tagged(token) && token.tag
            != Tag::Template && !cell_pred()(elem) && token.tag != Tag::Td && token.tag != Tag::Th && token.tag != Tag::Html
            && token.tag != Tag::Table && id_new(p, elem.id) && crate::independent::equivalence_body::attrs_plain(token.attrs),
    }
}

/// Every entry of a [`good`] parser's list is [`fmt_fresh`].
pub proof fn lemma_fmt_entries_fresh(p: Parser, i: int)
    requires
        good(p),
        0 <= i < p.formatting.len(),
    ensures
        fmt_fresh(p, p.formatting[i]),
{
    if p.formatting[i] is Entry {
        reveal(fmt_plain);
        assert(p.formatting[i]->Entry_elem.id != p.open[0].id);
        let id = p.formatting[i]->Entry_elem.id;
        assert forall|j: int| 0 <= j < p.open.len() && cell_pred()(#[trigger] p.open[j]) implies p.open[j].id != id by {
            assert(cell_fresh(p, p.open[j].id));
        }
    }
}

/// A list whose entries are all [`fmt_fresh`] keeps a live parser.
pub proof fn lemma_fmt_list_keeps(p: Parser, q: Parser)
    requires
        live(p),
        q == (Parser { formatting: q.formatting, ..p }),
        !p.stopped ==> forall|i: int| 0 <= i < q.formatting.len() ==> fmt_fresh(p, #[trigger] q.formatting[i]),
    ensures
        keeps(p, q),
{
    if !p.stopped {
        assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies q.formatting[i]->Entry_elem.id
            != q.open[0].id by {
            assert(fmt_fresh(p, q.formatting[i]));
        }
        assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies elem_tagged(
            q.formatting[i]->Entry_elem,
        ) && tok_tagged(q.formatting[i]->Entry_token) by {
            assert(fmt_fresh(p, q.formatting[i]));
        }
        assert forall|i: int| 0 <= i < q.formatting.len() && #[trigger] q.formatting[i] is Entry implies q.formatting[i]->Entry_token.tag
            != Tag::Template by {
            assert(fmt_fresh(p, q.formatting[i]));
        }
        assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies q.formatting[i]->Entry_elem.id
            < q.doc.nodes.len() && !cell_pred()(q.formatting[i]->Entry_elem) && q.formatting[i]->Entry_token.tag != Tag::Td
            && q.formatting[i]->Entry_token.tag != Tag::Th && q.formatting[i]->Entry_token.tag != Tag::Html
            && q.formatting[i]->Entry_token.tag != Tag::Table by {
            assert(fmt_fresh(p, q.formatting[i]));
        }
        assert(fmt_plain(q.formatting)) by {
            reveal(fmt_plain);
            assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies crate::independent::equivalence_body::attrs_plain(
                q.formatting[i]->Entry_token.attrs,
            ) by {
                assert(fmt_fresh(p, q.formatting[i]));
            }
        }
        assert forall|j: int| 0 <= j < q.open.len() && cell_pred()(#[trigger] q.open[j]) implies cell_fresh(q, q.open[j].id) by {
            assert(cell_fresh(p, p.open[j].id));
            assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies q.formatting[i]->Entry_elem.id
                != q.open[j].id by {
                assert(fmt_fresh(p, q.formatting[i]));
            }
        }
    }
}

/// Remove entry `i` of the list.
pub proof fn lemma_fmt_remove_keeps(p: Parser, i: int)
    requires
        live(p),
        0 <= i < p.formatting.len(),
    ensures
        keeps(p, Parser { formatting: p.formatting.remove(i), ..p }),
{
    let q = Parser { formatting: p.formatting.remove(i), ..p };
    if !p.stopped {
        assert forall|j: int| 0 <= j < q.formatting.len() implies fmt_fresh(p, #[trigger] q.formatting[j]) by {
            if j < i {
                lemma_fmt_entries_fresh(p, j);
            } else {
                lemma_fmt_entries_fresh(p, j + 1);
            }
        }
    }
    lemma_fmt_list_keeps(p, q);
}

/// Replace entry `i` of the list with a [`fmt_fresh`] one.
pub proof fn lemma_fmt_update_keeps(p: Parser, i: int, x: Fmt)
    requires
        live(p),
        0 <= i < p.formatting.len(),
        !p.stopped ==> fmt_fresh(p, x),
    ensures
        keeps(p, Parser { formatting: p.formatting.update(i, x), ..p }),
{
    let q = Parser { formatting: p.formatting.update(i, x), ..p };
    if !p.stopped {
        assert forall|j: int| 0 <= j < q.formatting.len() implies fmt_fresh(p, #[trigger] q.formatting[j]) by {
            if j != i {
                lemma_fmt_entries_fresh(p, j);
            }
        }
    }
    lemma_fmt_list_keeps(p, q);
}

/// Insert a [`fmt_fresh`] entry at index `i` of the list.
pub proof fn lemma_fmt_insert_keeps(p: Parser, i: int, x: Fmt)
    requires
        live(p),
        0 <= i <= p.formatting.len(),
        !p.stopped ==> fmt_fresh(p, x),
    ensures
        keeps(p, Parser { formatting: p.formatting.insert(i, x), ..p }),
{
    let q = Parser { formatting: p.formatting.insert(i, x), ..p };
    if !p.stopped {
        assert forall|j: int| 0 <= j < q.formatting.len() implies fmt_fresh(p, #[trigger] q.formatting[j]) by {
            if j < i {
                lemma_fmt_entries_fresh(p, j);
            } else if j > i {
                lemma_fmt_entries_fresh(p, j - 1);
            }
        }
    }
    lemma_fmt_list_keeps(p, q);
}

/// Push a [`fmt_fresh`] entry onto the list.
pub proof fn lemma_fmt_push_keeps(p: Parser, x: Fmt)
    requires
        live(p),
        !p.stopped ==> fmt_fresh(p, x),
    ensures
        keeps(p, Parser { formatting: p.formatting.push(x), ..p }),
{
    let q = Parser { formatting: p.formatting.push(x), ..p };
    if !p.stopped {
        assert forall|j: int| 0 <= j < q.formatting.len() implies fmt_fresh(p, #[trigger] q.formatting[j]) by {
            if j < p.formatting.len() {
                lemma_fmt_entries_fresh(p, j);
            }
        }
    }
    lemma_fmt_list_keeps(p, q);
}

/// The family indices lie in `from..i`.
pub proof fn lemma_family_range(f: Seq<Fmt>, from: int, i: int, e: Elem, t: TagTok)
    ensures
        forall|k: int|
            0 <= k < family_indices(f, from, i, e, t).len() ==> from <= #[trigger] family_indices(f, from, i, e, t)[k] < i,
    decreases i - from,
{
    if i > from {
        lemma_family_range(f, from, i - 1, e, t);
        let rest = family_indices(f, from, i - 1, e, t);
        let fam = family_indices(f, from, i, e, t);
        assert forall|k: int| 0 <= k < fam.len() implies from <= #[trigger] fam[k] < i by {
            if k < rest.len() {
                assert(fam[k] == rest[k]);
            }
        }
    }
}

/// "Push onto the list of active formatting elements" a fresh, tagged
/// element created for a tagged token other than `template`, `td`, `th`,
/// `html` and `table`.
pub proof fn lemma_push_formatting_keeps(p: Parser, e: Elem, t: TagTok)
    requires
        live(p),
        !p.stopped ==> e.id != p.open[0].id && elem_tagged(e) && tok_tagged(t) && t.tag != Tag::Template && !cell_pred()(e)
            && t.tag != Tag::Td && t.tag != Tag::Th && t.tag != Tag::Html && t.tag != Tag::Table && id_new(p, e.id)
            && crate::independent::equivalence_body::attrs_plain(t.attrs),
    ensures
        keeps(p, push_formatting(p, e, t)),
{
    if !p.stopped {
        let f = p.formatting;
        crate::exec::modes::in_body_start_lemmas::lemma_after_last_marker_nonneg(f, f.len() as int);
        let from = after_last_marker(f, f.len() as int);
        let fam = family_indices(f, from, f.len() as int, e, t);
        lemma_family_range(f, from, f.len() as int, e, t);
        let x = Fmt::Entry { elem: e, token: t };
        if fam.len() >= 3 {
            assert(0 <= fam[0] < f.len());
            lemma_fmt_remove_keeps(p, fam[0]);
            let p1 = Parser { formatting: f.remove(fam[0]), ..p };
            lemma_fmt_push_keeps(p1, x);
            lemma_keeps_trans(p, p1, Parser { formatting: p1.formatting.push(x), ..p1 });
        } else {
            lemma_fmt_push_keeps(p, x);
        }
    }
}

/// Steps 7 to 10 of "reconstruct the active formatting elements".
pub proof fn lemma_reconstruct_create_keeps(p: Parser, i: int)
    requires
        live(p),
    ensures
        keeps(p, reconstruct_create(p, i)),
    decreases p.formatting.len() - i,
{
    if i < 0 || i >= p.formatting.len() || p.stopped || !(p.formatting[i] is Entry) {
        lemma_keeps_refl(p);
    } else {
        let token = p.formatting[i]->Entry_token;
        lemma_fmt_entries_fresh(p, i);
        lemma_insert_html_keeps(p, token);
        let (p1, new_element) = insert_html_element(p, token);
        let x = Fmt::Entry { elem: new_element, token };
        let p2 = if p1.stopped {
            p1
        } else {
            Parser { formatting: p1.formatting.update(i, x), ..p1 }
        };
        if !p1.stopped {
            assert(fmt_fresh(p1, x));
            lemma_fmt_update_keeps(p1, i, x);
            lemma_keeps_trans(p, p1, p2);
        }
        if i + 1 < p2.formatting.len() && p2.formatting.len() == p.formatting.len() {
            lemma_reconstruct_create_keeps(p2, i + 1);
            lemma_keeps_trans(p, p2, reconstruct_create(p2, i + 1));
        }
    }
}

/// "Reconstruct the active formatting elements".
pub proof fn lemma_reconstruct_keeps(p: Parser)
    requires
        live(p),
    ensures
        keeps(p, reconstruct_formatting(p)),
{
    let n = p.formatting.len();
    if n == 0 || p.formatting[n - 1] is Marker || fmt_on_stack(p, p.formatting[n - 1]) {
        lemma_keeps_refl(p);
    } else {
        lemma_reconstruct_create_keeps(p, reconstruct_rewind(p, n - 1));
    }
}

/// "Add attribute … to element" for the missing attributes, of an element
/// of the document.
pub proof fn lemma_add_missing_keeps(p: Parser, el: NodeId, attrs: Seq<Attr>, i: int)
    requires
        live(p),
        !p.stopped ==> dom::valid(p.doc, el) && p.doc.nodes[el as int].kind is Element,
        crate::independent::equivalence_body::attrs_plain(attrs),
    ensures
        keeps(p, add_missing_attributes(p, el, attrs, i)),
        add_missing_attributes(p, el, attrs, i) == (Parser { doc: add_missing_attributes(p, el, attrs, i).doc, ..p }),
{
    super::body::lemma_add_missing_frame(p, el, attrs, i);
    if !p.stopped {
        super::doc::lemma_dinv(p);
    }
    lemma_doc_keeps(p, add_missing_attributes(p, el, attrs, i));
}

// ---------------------------------------------------------------------
// Reset the insertion mode appropriately

/// Where [`reset_from`] lands from entry `i` of a rooted stack whose
/// template modes are fine: a mode the stack has the shape of, other than
/// "in head noscript" (so "in head" only when a `head` element above `html`
/// was found).
pub proof fn lemma_reset_shape(p: Parser, i: int)
    requires
        rooted_seq(p.open),
        crate::termination::helpers_ranking::count_ok(p),
        0 <= i < p.open.len(),
    ensures
        shape0(reset_from(p, i), p.open),
        reset_from(p, i) != Mode::InHeadNoscript,
        reset_from(p, i) == Mode::InTemplate ==> p.template_modes.len() > 0,
    decreases i,
{
    crate::termination::helpers_ranking::lemma_reset_from(p, i);
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
            crate::termination::helpers_ranking::lemma_templates_in_pos(p.open, p.open.len() as int, i);
            assert(template_count(p) >= 1);
        }
        assert(p.template_modes.len() > 0);
        assert(crate::termination::template_mode_ok(p.template_modes[p.template_modes.len() - 1]));
    }
    if is_html(node, Tag::Head) && !last {
        crate::exec::stack::lemma_last_index_where_found(p.open, p.open.len() as int, html_ns(), i);
    }
    if i >= 1 {
        lemma_reset_shape(p, i - 1);
    }
}

/// [`reset_from`] chooses "in cell" only on a cell (step 4), never as a
/// template insertion mode.
pub proof fn lemma_reset_cell(p: Parser, i: int)
    requires
        rooted_seq(p.open),
        crate::termination::helpers_ranking::count_ok(p),
        0 <= i < p.open.len(),
    ensures
        reset_from(p, i) == Mode::InCell ==> last_index_where(p.open, i + 1, cell_pred()) >= 0,
    decreases i,
{
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
            crate::termination::helpers_ranking::lemma_templates_in_pos(p.open, p.open.len() as int, i);
            assert(template_count(p) >= 1);
        }
        assert(p.template_modes.len() > 0);
        assert(crate::termination::template_mode_ok(p.template_modes[p.template_modes.len() - 1]));
    }
    if i >= 1 {
        lemma_reset_cell(p, i - 1);
    }
}

/// "Reset the insertion mode appropriately" (only the mode changes).
pub proof fn lemma_reset_keeps(p: Parser)
    requires
        good(p),
        crate::termination::helpers_ranking::count_ok(p),
    ensures
        shape0(reset_insertion_mode(p).mode, p.open),
        reset_insertion_mode(p).mode != Mode::InHeadNoscript,
        reset_insertion_mode(p).mode == Mode::InTemplate ==> p.template_modes.len() > 0,
        reset_insertion_mode(p) == (Parser { mode: reset_insertion_mode(p).mode, ..p }),
        reset_insertion_mode(p).mode == Mode::InCell ==> cell_scoped(p.open),
{
    lemma_reset_shape(p, p.open.len() - 1);
    lemma_reset_cell(p, p.open.len() - 1);
    super::walls::lemma_reset_scoped(p);
}

// ---------------------------------------------------------------------
// The "in body" loops

/// Steps of the `li` start tag's loop.
pub proof fn lemma_li_loop_keeps(p: Parser, i: int)
    requires
        live(p),
        !p.stopped ==> i < p.open.len(),
        in_cell(p) ==> last_cell(p.open) <= i || i == p.open.len() - 1,
    ensures
        keeps(p, li_loop(p, i)),
    decreases i + 1,
{
    if i < 0 || p.stopped {
        if p.stopped {
            crate::theorems::frame_body::lemma_li_loop(p, i);
        } else {
            lemma_keeps_refl(p);
        }
    } else {
        let node = p.open[i];
        lemma_cell_top(p.open);
        if is_html(node, Tag::Li) {
            let f = |e: Elem| is_html(e, Tag::Li);
            assert(i != 0);
            let q = generate_implied_end_tags(p, Some(Tag::Li));
            crate::exec::stack::lemma_pop_until_popped(q, Tag::Li);
            lemma_close_keeps(p, Some(Tag::Li), f, i);
        } else if is_special(node) && !is_html(node, Tag::Address) && !is_html(node, Tag::Div) && !is_html(node, Tag::P) {
            lemma_keeps_refl(p);
        } else {
            lemma_li_loop_keeps(p, i - 1);
        }
    }
}

/// Steps of the `dd`/`dt` start tag's loop.
pub proof fn lemma_dd_dt_loop_keeps(p: Parser, i: int)
    requires
        live(p),
        !p.stopped ==> i < p.open.len(),
        in_cell(p) ==> last_cell(p.open) <= i || i == p.open.len() - 1,
    ensures
        keeps(p, dd_dt_loop(p, i)),
    decreases i + 1,
{
    if i < 0 || p.stopped {
        if p.stopped {
            crate::theorems::frame_body::lemma_dd_dt_loop(p, i);
        } else {
            lemma_keeps_refl(p);
        }
    } else {
        let node = p.open[i];
        lemma_cell_top(p.open);
        if is_html(node, Tag::Dd) {
            let f = |e: Elem| is_html(e, Tag::Dd);
            assert(i != 0);
            let q = generate_implied_end_tags(p, Some(Tag::Dd));
            crate::exec::stack::lemma_pop_until_popped(q, Tag::Dd);
            lemma_close_keeps(p, Some(Tag::Dd), f, i);
        } else if is_html(node, Tag::Dt) {
            let f = |e: Elem| is_html(e, Tag::Dt);
            assert(i != 0);
            let q = generate_implied_end_tags(p, Some(Tag::Dt));
            crate::exec::stack::lemma_pop_until_popped(q, Tag::Dt);
            lemma_close_keeps(p, Some(Tag::Dt), f, i);
        } else if is_special(node) && !is_html(node, Tag::Address) && !is_html(node, Tag::Div) && !is_html(node, Tag::P) {
            lemma_keeps_refl(p);
        } else {
            lemma_dd_dt_loop_keeps(p, i - 1);
        }
    }
}

/// The "any other end tag" loop, for a tagged token that is not `html`
/// (nor, in the "in cell" mode, `td` or `th`).
pub proof fn lemma_any_other_loop_keeps(p: Parser, tt: TagTok, i: int)
    requires
        live(p),
        tok_tagged(tt),
        crate::independent::equivalence_body::attrs_plain(tt.attrs),
        tt.tag != Tag::Html,
        in_cell(p) ==> tt.tag != Tag::Td && tt.tag != Tag::Th,
        !p.stopped ==> i < p.open.len(),
        in_cell(p) ==> last_cell(p.open) <= i || i == p.open.len() - 1,
    ensures
        keeps(p, any_other_end_tag_loop(p, tt, i)),
    decreases i + 1,
{
    if i < 0 || p.stopped {
        if p.stopped {
            crate::theorems::frame_body::lemma_any_other_end_tag_loop(p, tt, i);
        } else {
            lemma_keeps_refl(p);
        }
    } else {
        let node = p.open[i];
        lemma_cell_top(p.open);
        if is_html_named(node, tt.name) {
            assert(i != 0) by {
                if i == 0 {
                    assert(elem_tagged(p.open[0]));
                }
            }
            assert(node.tag == tt.tag) by {
                assert(elem_tagged(p.open[i]));
            }
            let f = |e: Elem| e.id == node.id;
            let q = generate_implied_end_tags(p, Some(tt.tag));
            crate::exec::stack::lemma_pop_until_node_popped(q, node.id);
            lemma_close_keeps(p, Some(tt.tag), f, i);
        } else if is_special(node) {
            lemma_keeps_refl(p);
        } else {
            lemma_any_other_loop_keeps(p, tt, i - 1);
        }
    }
}

/// "Any other end tag" for a tagged token that is not `html` (nor, in the
/// "in cell" mode, `td` or `th`).
pub proof fn lemma_any_other_keeps(p: Parser, tt: TagTok)
    requires
        in_cell(p) ==> tt.tag != Tag::Td && tt.tag != Tag::Th,
        live(p),
        tok_tagged(tt),
        crate::independent::equivalence_body::attrs_plain(tt.attrs),
        tt.tag != Tag::Html,
    ensures
        keeps(p, in_body_any_other_end_tag(p, tt)),
{
    lemma_any_other_loop_keeps(p, tt, p.open.len() - 1);
}

} // verus!
