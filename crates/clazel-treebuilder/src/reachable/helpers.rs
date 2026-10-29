//! Each helper of the transcription [`keeps`] a live parser, under the
//! condition its callers check (see [`super`]).

#[cfg(verus_only)]
use super::cells::*;
#[cfg(verus_only)]
use super::doc::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The stack of open elements

/// The parser is in the "in cell" mode (with a cell).
pub open spec fn in_cell(p: Parser) -> bool {
    !p.stopped && p.mode == Mode::InCell && has_cell(p.open)
}

/// A non-empty prefix of the stack (holding the last cell in the "in cell"
/// mode), nothing else changed.
pub proof fn lemma_prefix_keeps(p: Parser, q: Parser)
    requires
        live(p),
        q == (Parser { open: q.open, ..p }),
        !p.stopped ==> 1 <= q.open.len() <= p.open.len(),
        forall|j: int| 0 <= j < q.open.len() ==> #[trigger] q.open[j] == p.open[j],
        in_cell(p) ==> q.open.len() > last_cell(p.open),
    ensures
        keeps(p, q),
        in_cell(p) ==> last_cell(q.open) == last_cell(p.open),
{
    if !p.stopped {
        assert forall|j: int| 0 <= j < q.open.len() && cell_pred()(#[trigger] q.open[j]) implies exists|k: int|
            0 <= k < p.open.len() && (#[trigger] p.open[k]) == q.open[j] by {
            assert(p.open[j] == q.open[j]);
        }
        lemma_cells_wf_open(p, q);
        if in_cell(p) {
            lemma_cell_prefix(p.open, q.open);
        }
        assert(q.open[0] == p.open[0]);
        assert forall|i: int| 0 <= i < q.open.len() implies elem_tagged(#[trigger] q.open[i]) by {
            assert(q.open[i] == p.open[i]);
        }
        assert(crate::termination::helpers_tables::is_prefix(q.open, p.open));
        assert forall|j: int| 0 <= j < q.open.len() implies p.open.contains(#[trigger] q.open[j]) by {
            assert(p.open[j] == q.open[j]);
        }
        lemma_dinv_sub(p, q.open);
        crate::termination::helpers_ranking::lemma_tcount_prefix(q.open, p.open);
        crate::termination::helpers_ranking::lemma_template_count(p);
        crate::termination::helpers_ranking::lemma_template_count(q);
    }
}

/// "Pop the current node" when it is not the only one (nor, in the "in
/// cell" mode, a cell).
pub proof fn lemma_pop_keeps(p: Parser)
    requires
        live(p),
        !p.stopped ==> p.open.len() >= 2,
        in_cell(p) ==> !cell_pred()(current_node(p)),
    ensures
        keeps(p, pop(p)),
{
    if !p.stopped {
        let q = pop(p);
        assert forall|j: int| 0 <= j < q.open.len() implies #[trigger] q.open[j] == p.open[j] by {}
        if in_cell(p) {
            lemma_cell_top(p.open);
        }
        lemma_prefix_keeps(p, q);
    }
}

/// Pop while the current node satisfies `f`, which the `html` element does
/// not (nor, in the "in cell" mode, the last cell).
pub proof fn lemma_pop_while_keeps(p: Parser, f: spec_fn(Elem) -> bool)
    requires
        live(p),
        !p.stopped ==> !f(p.open[0]),
        in_cell(p) ==> !f(p.open[last_cell(p.open)]),
    ensures
        keeps(p, pop_while(p, f)),
        in_cell(p) ==> last_cell(pop_while(p, f).open) == last_cell(p.open),
{
    crate::termination::helpers_tables::lemma_pop_while(p, f);
    let q = pop_while(p, f);
    if !p.stopped {
        assert(p.open.len() > 0);
        assert(!f(p.open[0]));
        assert(q.open.len() > 0);
    }
    if in_cell(p) {
        lemma_cell_top(p.open);
        assert(q.open.len() > last_cell(p.open));
    }
    lemma_prefix_keeps(p, q);
}

/// Pop until an entry satisfying `f` has been popped, when one is at index
/// `k >= 1` (above the last cell in the "in cell" mode).
pub proof fn lemma_pop_until_where_keeps(p: Parser, f: spec_fn(Elem) -> bool, k: int)
    requires
        live(p),
        !p.stopped ==> 1 <= k < p.open.len() && f(p.open[k]),
        in_cell(p) ==> k > last_cell(p.open),
    ensures
        keeps(p, crate::exec::stack::pop_until_where(p, f)),
        crate::exec::stack::pop_until_where(p, f) == (Parser { open: crate::exec::stack::pop_until_where(p, f).open, ..p }),
{
    crate::exec::modes::in_body_start_lemmas::lemma_pop_until_where_prefix(p, f);
    let q = crate::exec::stack::pop_until_where(p, f);
    if !p.stopped {
        crate::exec::stack::lemma_last_index_where_found(p.open, p.open.len() as int, f, k);
    }
    lemma_prefix_keeps(p, q);
}

/// An entry in scope that the `html` element is not is at an index
/// `k >= 1`, above the last cell if it is not a cell and the scope is not
/// table scope.
pub proof fn lemma_scope_k(o: Seq<Elem>, f: spec_fn(Elem) -> bool, s: Scope) -> (k: int)
    requires
        o.len() > 0,
        in_scope_from(o, o.len() as int, f, s),
        !f(o[0]),
    ensures
        1 <= k < o.len(),
        f(o[k]),
        k == last_index_where(o, o.len() as int, f),
        s != Scope::Table && !cell_pred()(o[k]) ==> last_cell(o) < k,
{
    crate::exec::modes::in_body_start_lemmas::lemma_scope_liw(o, o.len() as int, f, s);
    crate::termination::helpers_ranking::lemma_last_index_where(o, o.len() as int, f);
    let k = last_index_where(o, o.len() as int, f);
    if s != Scope::Table && !cell_pred()(o[k]) {
        lemma_scope_cell(o, f, s);
    }
    k
}

/// An entry on the stack that the `html` element is not is at an index
/// `k >= 1`.
pub proof fn lemma_has_k(o: Seq<Elem>, f: spec_fn(Elem) -> bool) -> (k: int)
    requires
        o.len() > 0,
        last_index_where(o, o.len() as int, f) >= 0,
        !f(o[0]),
    ensures
        1 <= k < o.len(),
        f(o[k]),
        k == last_index_where(o, o.len() as int, f),
{
    crate::termination::helpers_ranking::lemma_last_index_where(o, o.len() as int, f);
    last_index_where(o, o.len() as int, f)
}

/// "Pop until an HTML `tag` element has been popped" with one at `k >= 1`.
pub proof fn lemma_pop_until_popped_keeps(p: Parser, tag: Tag, k: int)
    requires
        live(p),
        !p.stopped ==> 1 <= k < p.open.len() && is_html(p.open[k], tag),
        in_cell(p) ==> k > last_cell(p.open),
    ensures
        keeps(p, pop_until_popped(p, tag)),
        pop_until_popped(p, tag) == (Parser { open: pop_until_popped(p, tag).open, ..p }),
{
    let f = |e: Elem| is_html(e, tag);
    crate::exec::stack::lemma_pop_until_popped(p, tag);
    lemma_pop_until_where_keeps(p, f, k);
}

/// "Pop until an HTML h1 to h6 element has been popped" with one at
/// `k >= 1`.
pub proof fn lemma_pop_until_heading_popped_keeps(p: Parser, k: int)
    requires
        live(p),
        !p.stopped ==> 1 <= k < p.open.len() && is_heading(p.open[k]),
        in_cell(p) ==> k > last_cell(p.open),
    ensures
        keeps(p, pop_until_heading_popped(p)),
        pop_until_heading_popped(p) == (Parser { open: pop_until_heading_popped(p).open, ..p }),
{
    let f = |e: Elem| is_heading(e);
    crate::exec::stack::lemma_pop_until_heading_popped(p);
    lemma_pop_until_where_keeps(p, f, k);
}

/// "Pop until `id` has been popped" with it at `k >= 1`.
pub proof fn lemma_pop_until_node_popped_keeps(p: Parser, id: NodeId, k: int)
    requires
        live(p),
        !p.stopped ==> 1 <= k < p.open.len() && p.open[k].id == id,
        in_cell(p) ==> k > last_cell(p.open),
    ensures
        keeps(p, pop_until_node_popped(p, id)),
        pop_until_node_popped(p, id) == (Parser { open: pop_until_node_popped(p, id).open, ..p }),
{
    let f = |e: Elem| e.id == id;
    crate::exec::stack::lemma_pop_until_node_popped(p, id);
    lemma_pop_until_where_keeps(p, f, k);
}

/// [`pop_until_named_popped`] is a [`crate::exec::stack::pop_until_where`].
pub proof fn lemma_pop_until_named_is(p: Parser, name: Seq<u32>)
    ensures
        pop_until_named_popped(p, name) == crate::exec::stack::pop_until_where(p, |e: Elem| is_html_named(e, name)),
    decreases p.open.len(),
{
    if p.open.len() > 0 && !is_html_named(current_node(p), name) {
        lemma_pop_until_named_is(pop(p), name);
    }
}

/// "Pop until an HTML element named `name` has been popped" with one at
/// `k >= 1`.
pub proof fn lemma_pop_until_named_popped_keeps(p: Parser, name: Seq<u32>, k: int)
    requires
        live(p),
        !p.stopped ==> 1 <= k < p.open.len() && is_html_named(p.open[k], name),
        in_cell(p) ==> k > last_cell(p.open),
    ensures
        keeps(p, pop_until_named_popped(p, name)),
        pop_until_named_popped(p, name) == (Parser { open: pop_until_named_popped(p, name).open, ..p }),
{
    let f = |e: Elem| is_html_named(e, name);
    lemma_pop_until_named_is(p, name);
    lemma_pop_until_where_keeps(p, f, k);
}

/// Remove the entry at index `i >= 1` (not the last cell in the "in cell"
/// mode).
pub proof fn lemma_remove_open_keeps(p: Parser, i: int)
    requires
        live(p),
        !p.stopped ==> 1 <= i < p.open.len(),
        in_cell(p) ==> i != last_cell(p.open),
    ensures
        keeps(p, remove_open_at(p, i)),
{
    let q = remove_open_at(p, i);
    if !p.stopped {
        assert forall|j: int| 0 <= j < q.open.len() && cell_pred()(#[trigger] q.open[j]) implies exists|k: int|
            0 <= k < p.open.len() && (#[trigger] p.open[k]) == q.open[j] by {
            if j < i {
                assert(p.open[j] == q.open[j]);
            } else {
                assert(p.open[j + 1] == q.open[j]);
            }
        }
        lemma_cells_wf_open(p, q);
        if in_cell(p) {
            lemma_cell_remove(p.open, i);
        }
        assert(q.open[0] == p.open[0]);
        assert forall|j: int| 0 <= j < q.open.len() implies elem_tagged(#[trigger] q.open[j]) by {
            if j < i {
                assert(q.open[j] == p.open[j]);
            } else {
                assert(q.open[j] == p.open[j + 1]);
            }
        }
        lemma_tcount_remove(p.open, i);
        crate::termination::helpers_ranking::lemma_template_count(p);
        crate::termination::helpers_ranking::lemma_template_count(q);
        assert forall|j: int| 0 <= j < q.open.len() implies p.open.contains(#[trigger] q.open[j]) by {
            if j < i {
                assert(p.open[j] == q.open[j]);
            } else {
                assert(p.open[j + 1] == q.open[j]);
            }
        }
        lemma_dinv_sub(p, q.open);
    }
}

/// Removing an entry does not add a `template` element.
pub proof fn lemma_tcount_remove(o: Seq<Elem>, i: int)
    requires
        0 <= i < o.len(),
    ensures
        crate::termination::helpers_ranking::tcount(o.remove(i)) <= crate::termination::helpers_ranking::tcount(o),
{
    lemma_templates_in_remove(o, i, o.len() as int);
}

/// [`templates_in`] of a stack with entry `i` removed, up to `j`.
pub proof fn lemma_templates_in_remove(o: Seq<Elem>, i: int, j: int)
    requires
        0 <= i < o.len(),
        i < j <= o.len(),
    ensures
        templates_in(o.remove(i), j - 1) <= templates_in(o, j),
    decreases j,
{
    let r = o.remove(i);
    if j - 1 == i {
        crate::termination::helpers_ranking::lemma_templates_in_same(r, o, i);
        crate::termination::helpers_ranking::lemma_templates_in_mono(o, i, j);
    } else {
        lemma_templates_in_remove(o, i, j - 1);
        assert(r[j - 2] == o[j - 1]);
    }
}

/// Push a tagged element that is not a `template`, nor a cell unless the
/// mode is not "in cell" and its id is fresh.
pub proof fn lemma_push_keeps(p: Parser, e: Elem)
    requires
        live(p),
        elem_tagged(e),
        !is_html(e, Tag::Template),
        !p.stopped && cell_pred()(e) ==> p.mode != Mode::InCell && cell_fresh(p, e.id),
        !p.stopped ==> crate::exec::frame::elem_ok(p.doc, e),
    ensures
        keeps(p, push(p, e)),
        !p.stopped ==> push(p, e).open == p.open.push(e),
{
    if !p.stopped {
        let q = push(p, e);
        lemma_dinv(p);
        crate::exec::frame::lemma_open_push(p.doc, p.open, e);
        lemma_dinv_open(p, p.open.push(e));
        assert forall|j: int| 0 <= j < q.open.len() && cell_pred()(#[trigger] q.open[j]) implies cell_fresh(q, q.open[j].id) by {
            if j < p.open.len() {
                assert(q.open[j] == p.open[j]);
                assert(cell_fresh(p, p.open[j].id));
            } else {
                assert(q.open[j] == e);
                assert(cell_fresh(p, e.id));
            }
        }
        assert(cells_wf(q));
        if in_cell(p) {
            lemma_cell_push(p.open, e);
            lemma_cell_top(p.open);
            assert(q.open[last_cell(p.open)] == p.open[last_cell(p.open)]);
            assert(q.open[last_cell(q.open)] == p.open[last_cell(p.open)]);
        }
        assert(in_cell_ok(q));
        assert(q.open[0] == p.open[0]);
        assert forall|i: int| 0 <= i < q.open.len() implies elem_tagged(#[trigger] q.open[i]) by {
            if i < p.open.len() {
                assert(q.open[i] == p.open[i]);
            }
        }
        crate::termination::helpers_ranking::lemma_tcount_push(p.open, e);
        crate::termination::helpers_ranking::lemma_template_count(p);
        crate::termination::helpers_ranking::lemma_template_count(q);
    }
}

/// "Generate implied end tags".
pub proof fn lemma_implied_keeps(p: Parser, except: Option<Tag>)
    requires
        live(p),
    ensures
        keeps(p, generate_implied_end_tags(p, except)),
        generate_implied_end_tags(p, except) == (Parser { open: generate_implied_end_tags(p, except).open, ..p }),
        in_cell(p) ==> last_cell(generate_implied_end_tags(p, except).open) == last_cell(p.open),
        crate::termination::helpers_tables::is_prefix(generate_implied_end_tags(p, except).open, p.open),
        forall|i: int|
            0 <= i < p.open.len() && !crate::exec::modes::in_body_start_lemmas::implied_pred(except)(#[trigger] p.open[i])
                ==> generate_implied_end_tags(p, except).open.len() > i,
{
    let f = crate::exec::modes::in_body_start_lemmas::implied_pred(except);
    assert(generate_implied_end_tags(p, except) == pop_while(p, f));
    crate::termination::helpers_tables::lemma_pop_while(p, f);
    if in_cell(p) {
        lemma_cell_top(p.open);
    }
    lemma_pop_while_keeps(p, f);
}

/// "Generate all implied end tags thoroughly" (not in the "in cell" mode,
/// where it may pop the cell).
pub proof fn lemma_thorough_keeps(p: Parser)
    requires
        live(p),
        !in_cell(p),
    ensures
        keeps(p, generate_all_implied_end_tags_thoroughly(p)),
        generate_all_implied_end_tags_thoroughly(p) == (Parser { open: generate_all_implied_end_tags_thoroughly(p).open, ..p }),
{
    let f = |e: Elem|
        e.ns == Namespace::Html && match e.tag {
            Tag::Caption | Tag::Colgroup | Tag::Dd | Tag::Dt | Tag::Li | Tag::Optgroup | Tag::Option | Tag::P | Tag::Rb
            | Tag::Rp | Tag::Rt | Tag::Rtc | Tag::Tbody | Tag::Td | Tag::Tfoot | Tag::Th | Tag::Thead | Tag::Tr => true,
            _ => false,
        };
    assert(generate_all_implied_end_tags_thoroughly(p) == pop_while(p, f));
    crate::termination::helpers_tables::lemma_pop_while(p, f);
    lemma_pop_while_keeps(p, f);
}

/// "Generate implied end tags, except for `except`", then pop until an
/// entry satisfying `f` has been popped, when one at `k >= 1` is not an
/// implied end tag (except `except`).
pub proof fn lemma_close_keeps(p: Parser, except: Option<Tag>, f: spec_fn(Elem) -> bool, k: int)
    requires
        live(p),
        !p.stopped ==> 1 <= k < p.open.len() && f(p.open[k]) && !crate::exec::modes::in_body_start_lemmas::implied_pred(
            except,
        )(p.open[k]),
        in_cell(p) ==> k > last_cell(p.open),
    ensures
        keeps(p, crate::exec::stack::pop_until_where(generate_implied_end_tags(p, except), f)),
{
    lemma_implied_keeps(p, except);
    let q = generate_implied_end_tags(p, except);
    if !p.stopped {
        assert(q.open[k] == p.open[k]);
    }
    lemma_pop_until_where_keeps(q, f, k);
    lemma_keeps_trans(p, q, crate::exec::stack::pop_until_where(q, f));
}

/// "Close a p element" with a `p` element in button scope.
pub proof fn lemma_close_p_keeps(p: Parser)
    requires
        live(p),
        !p.stopped ==> has_in_scope(p, Tag::P, Scope::Button),
    ensures
        keeps(p, close_p_element(p)),
{
    let f = |e: Elem| is_html(e, Tag::P);
    let k = if !p.stopped {
        lemma_scope_k(p.open, f, Scope::Button)
    } else {
        0
    };
    let q = generate_implied_end_tags(p, Some(Tag::P));
    crate::exec::stack::lemma_pop_until_popped(q, Tag::P);
    lemma_close_keeps(p, Some(Tag::P), f, k);
}

/// "If the stack of open elements has a p element in button scope, then
/// close a p element."
pub proof fn lemma_close_p_if_keeps(p: Parser)
    requires
        live(p),
    ensures
        keeps(p, close_p_if_in_button_scope(p)),
{
    if has_in_scope(p, Tag::P, Scope::Button) {
        lemma_close_p_keeps(p);
    }
}

// ---------------------------------------------------------------------
// The document

/// A change of the document that does not shrink the arena and (while
/// parsing) extends it (`exec::frame::doc_extends`).
pub proof fn lemma_doc_keeps(p: Parser, q: Parser)
    requires
        live(p),
        q == (Parser { doc: q.doc, ..p }),
        q.doc.nodes.len() >= p.doc.nodes.len(),
        !p.stopped ==> crate::exec::frame::doc_extends(p.doc, q.doc),
    ensures
        keeps(p, q),
{
    if !p.stopped {
        lemma_dinv_doc(p, q.doc);
    }
}

/// Stop parsing.
pub proof fn lemma_stop_keeps(p: Parser)
    ensures
        keeps(p, stop_parsing(p)),
{
}

/// DOM "insert" keeps the arena's size.
pub proof fn lemma_insert_len(d: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    ensures
        dom::insert(d, node, parent, child).nodes.len() == d.nodes.len(),
{
    let d1 = dom::adopt(d, node);
    assert(d1.nodes.len() == d.nodes.len());
}

/// [`dom_insert`], into a parent that may receive a child.
pub proof fn lemma_dom_insert_keeps(p: Parser, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        live(p),
        !p.stopped ==> pok(p.doc, parent),
    ensures
        keeps(p, dom_insert(p, node, parent, child)),
        dom_insert(p, node, parent, child) == (Parser { doc: dom_insert(p, node, parent, child).doc, ..p }),
        dom_insert(p, node, parent, child).doc.nodes.len() == p.doc.nodes.len(),
        !p.stopped ==> crate::exec::frame::doc_extends(p.doc, dom_insert(p, node, parent, child).doc),
{
    lemma_insert_len(p.doc, node, parent, child);
    if !p.stopped {
        lemma_dinv(p);
        if insert_valid(p.doc, node, parent, child) {
            crate::exec::frame::lemma_insert_extends(p.doc, node, parent, child);
            lemma_dinv_doc(p, dom::insert(p.doc, node, parent, child));
        } else {
            crate::exec::modes::in_body_start_lemmas::lemma_doc_extends_refl(p.doc);
        }
    }
}

/// [`dom_remove`].
pub proof fn lemma_dom_remove_keeps(p: Parser, node: NodeId)
    requires
        live(p),
    ensures
        keeps(p, dom_remove(p, node)),
        dom_remove(p, node) == (Parser { doc: dom_remove(p, node).doc, ..p }),
        dom_remove(p, node).doc.nodes.len() == p.doc.nodes.len(),
        !p.stopped ==> crate::exec::frame::doc_extends(p.doc, dom_remove(p, node).doc),
{
    if !p.stopped {
        lemma_dinv(p);
        if dom::valid(p.doc, node) && p.doc.nodes[node as int].parent is Some {
            crate::exec::frame::lemma_remove_extends(p.doc, node);
            lemma_dinv_doc(p, dom::remove(p.doc, node));
        } else {
            crate::exec::modes::in_body_start_lemmas::lemma_doc_extends_refl(p.doc);
        }
    }
}

/// Create a node of a kind the arena accepts: the new id is the arena's
/// old size.
pub proof fn lemma_create_keeps(p: Parser, k: NodeKind)
    requires
        live(p),
        !p.stopped ==> dom::creatable(p.doc, k),
    ensures
        keeps(p, create(p, k).0),
        !create(p, k).0.stopped ==> {
            &&& create(p, k).0 == (Parser { doc: create(p, k).0.doc, ..p })
            &&& create(p, k).1 as int == p.doc.nodes.len()
            &&& create(p, k).0.doc.nodes.len() == p.doc.nodes.len() + 1
            &&& create(p, k).0.doc.nodes[create(p, k).1 as int].kind == k
            &&& crate::exec::frame::doc_extends(p.doc, create(p, k).0.doc)
        },
{
    if !p.stopped && dom::can_create(p.doc, 1) {
        lemma_dinv(p);
        crate::exec::frame::lemma_create_extends(p.doc, k);
        lemma_dinv_doc(p, dom::create_node(p.doc, k).0);
    }
}

/// "Create an element for a token": a fresh element of the token's name,
/// with template contents if it is an HTML `template`.
pub proof fn lemma_ceft_keeps(p: Parser, t: TagTok, ns: Namespace, ip: NodeId)
    requires
        live(p),
    ensures
        keeps(p, create_element_for_token(p, t, ns, ip).0),
        !create_element_for_token(p, t, ns, ip).0.stopped ==> {
            let (q, e) = create_element_for_token(p, t, ns, ip);
            &&& q == (Parser { doc: q.doc, ..p })
            &&& e.id as int == p.doc.nodes.len()
            &&& e.id < q.doc.nodes.len()
            &&& id_new(q, e.id)
            &&& elem_in_doc(q.doc, e)
            &&& (is_html(e, Tag::Template) ==> has_template_contents(q.doc, e.id))
            &&& crate::exec::frame::doc_extends(p.doc, q.doc)
        },
        create_element_for_token(p, t, ns, ip).1.ns == ns,
        create_element_for_token(p, t, ns, ip).1.tag == t.tag,
        create_element_for_token(p, t, ns, ip).1.name == t.name,
{
    hide(create);
    let owner = if is_form_associated(ns, t.tag) && p.form is Some && !parsing_template_contents(p) && p.context is None && (
    !is_listed(ns, t.tag) || !has_attr(t, name_form())) && same_tree(p.doc, ip, p.form->Some_0) {
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
    lemma_create_keeps(p, k);
    let (p1, id) = create(p, k);
    if ns == Namespace::Html && t.tag == Tag::Template && !p1.stopped {
        if dom::can_create(p1.doc, 1) {
            let d = dom::create_template_contents(p1.doc, id).0;
            assert(d.nodes.len() == p1.doc.nodes.len() + 1);
            crate::exec::frame::lemma_create_template_contents_extends(p1.doc, id);
            lemma_doc_keeps(p1, Parser { doc: d, ..p1 });
            crate::exec::frame::lemma_doc_extends_trans(p.doc, p1.doc, d);
        }
    }
    let (q, e) = create_element_for_token(p, t, ns, ip);
    if !q.stopped {
        assert forall|j: int| 0 <= j < q.open.len() && cell_pred()(#[trigger] q.open[j]) implies q.open[j].id != e.id by {
            assert(q.open[j] == p.open[j]);
            assert(cell_fresh(p, p.open[j].id));
        }
    }
}

/// "Insert an element at the adjusted insertion location", at a given
/// location whose parent may receive a child, or the appropriate place.
pub proof fn lemma_insert_element_at_keeps(p: Parser, el: NodeId, loc: Option<Location>)
    requires
        live(p),
        !p.stopped ==> match loc {
            Some(l) => pok(p.doc, l.parent),
            None => true,
        },
    ensures
        keeps(p, insert_element_at(p, el, loc)),
        insert_element_at(p, el, loc) == (Parser { doc: insert_element_at(p, el, loc).doc, ..p }),
        insert_element_at(p, el, loc).doc.nodes.len() == p.doc.nodes.len(),
        !p.stopped ==> crate::exec::frame::doc_extends(p.doc, insert_element_at(p, el, loc).doc),
{
    let l = adjusted_location(p, loc);
    if !p.stopped {
        lemma_adjusted_pok(p, loc);
        lemma_dinv(p);
        crate::exec::modes::in_body_start_lemmas::lemma_doc_extends_refl(p.doc);
    }
    lemma_dom_insert_keeps(p, el, l.parent, l.child);
}

/// "Insert a foreign element" for a tagged token, not an HTML `template`
/// (nor a cell in the "in cell" mode): the stack gains the new, fresh,
/// tagged element.
pub proof fn lemma_insert_foreign_keeps(p: Parser, t: TagTok, ns: Namespace)
    requires
        live(p),
        tok_tagged(t),
        !(ns == Namespace::Html && t.tag == Tag::Template),
        !p.stopped && ns == Namespace::Html && (t.tag == Tag::Td || t.tag == Tag::Th) ==> p.mode != Mode::InCell,
    ensures
        keeps(p, insert_foreign_element(p, t, ns).0),
        !insert_foreign_element(p, t, ns).0.stopped ==> {
            let (q, e) = insert_foreign_element(p, t, ns);
            &&& q == (Parser { doc: q.doc, open: p.open.push(e), ..p })
            &&& e.id as int >= p.doc.nodes.len()
            &&& e.id < q.doc.nodes.len()
            &&& !cell_pred()(e) ==> id_new(q, e.id)
            &&& crate::exec::frame::doc_extends(p.doc, q.doc)
        },
        insert_foreign_element(p, t, ns).1.ns == ns,
        insert_foreign_element(p, t, ns).1.tag == t.tag,
        insert_foreign_element(p, t, ns).1.name == t.name,
        elem_tagged(insert_foreign_element(p, t, ns).1),
{
    let ip = appropriate_place(p, None).parent;
    lemma_ceft_keeps(p, t, ns, ip);
    let (p1, e) = create_element_for_token(p, t, ns, ip);
    lemma_insert_element_at_keeps(p1, e.id, None);
    let p2 = insert_element_at(p1, e.id, None);
    lemma_keeps_trans(p, p1, p2);
    if !p2.stopped {
        assert(p2.form == p.form && p2.formatting == p.formatting && p2.mode == p.mode);
        assert(e.id as int == p.doc.nodes.len());
        assert(e.id < p2.doc.nodes.len());
        assert(p2.form != Some(e.id));
        assert forall|i: int| 0 <= i < p2.formatting.len() && (#[trigger] p2.formatting[i]) is Entry implies p2.formatting[i]->Entry_elem.id
            != e.id by {
            assert(p.formatting[i] == p2.formatting[i]);
        }
        assert(cell_fresh(p2, e.id));
        assert(crate::exec::frame::elem_ok(p1.doc, e));
        crate::exec::frame::lemma_elem_ok_extends(p1.doc, p2.doc, e);
        crate::exec::frame::lemma_doc_extends_trans(p.doc, p1.doc, p2.doc);
    }
    lemma_push_keeps(p2, e);
    lemma_keeps_trans(p, p2, push(p2, e));
    let q = push(p2, e);
    if !q.stopped && !cell_pred()(e) {
        assert forall|j: int| 0 <= j < q.open.len() && cell_pred()(#[trigger] q.open[j]) implies q.open[j].id != e.id by {
            assert(q.open[j] == p.open[j]);
            assert(cell_fresh(p, p.open[j].id));
        }
    }
}

/// "Insert an HTML element" for a tagged token other than `template` (nor
/// a cell in the "in cell" mode).
pub proof fn lemma_insert_html_keeps(p: Parser, t: TagTok)
    requires
        live(p),
        tok_tagged(t),
        t.tag != Tag::Template,
        !p.stopped && (t.tag == Tag::Td || t.tag == Tag::Th) ==> p.mode != Mode::InCell,
    ensures
        keeps(p, insert_html_element(p, t).0),
        !insert_html_element(p, t).0.stopped ==> {
            let (q, e) = insert_html_element(p, t);
            &&& q == (Parser { doc: q.doc, open: p.open.push(e), ..p })
            &&& e.id as int >= p.doc.nodes.len()
            &&& e.id < q.doc.nodes.len()
            &&& t.tag != Tag::Td && t.tag != Tag::Th ==> id_new(q, e.id)
            &&& crate::exec::frame::doc_extends(p.doc, q.doc)
        },
        insert_html_element(p, t).1.ns == Namespace::Html,
        insert_html_element(p, t).1.tag == t.tag,
        insert_html_element(p, t).1.name == t.name,
        elem_tagged(insert_html_element(p, t).1),
{
    lemma_insert_foreign_keeps(p, t, Namespace::Html);
}

/// "Insert a character" (the stack is kept).
pub proof fn lemma_insert_characters_keeps(p: Parser, data: Seq<u32>)
    requires
        live(p),
    ensures
        keeps(p, insert_characters(p, data)),
        !insert_characters(p, data).stopped ==> insert_characters(p, data) == (Parser {
            doc: insert_characters(p, data).doc,
            ..p
        }),
        !insert_characters(p, data).stopped ==> crate::exec::frame::doc_extends(p.doc, insert_characters(p, data).doc),
{
    let loc = adjusted_location(p, None);
    let doc = p.doc;
    if !p.stopped {
        lemma_dinv(p);
        crate::exec::modes::in_body_start_lemmas::lemma_doc_extends_refl(p.doc);
    }
    if !(p.stopped || doc.nodes[loc.parent as int].kind is Document) {
        lemma_adjusted_pok(p, None);
        let prev = match loc.child {
            Some(c) => dom::previous_sibling(doc, c),
            None => dom::last_child(doc, loc.parent),
        };
        match prev {
            Some(s) if dom::valid(doc, s) && doc.nodes[s as int].kind is Text => {
                assert(dom::append_data(doc, s, data).nodes.len() == doc.nodes.len());
                crate::exec::frame::lemma_append_data_extends(doc, s, data);
                lemma_doc_keeps(p, Parser { doc: dom::append_data(doc, s, data), ..p });
            },
            _ => {
                lemma_create_keeps(p, NodeKind::Text { data });
                let (p1, text) = create(p, NodeKind::Text { data });
                if !p1.stopped {
                    lemma_pok_extends(p.doc, p1.doc, loc.parent);
                }
                lemma_dom_insert_keeps(p1, text, loc.parent, loc.child);
                lemma_keeps_trans(p, p1, dom_insert(p1, text, loc.parent, loc.child));
                if !p1.stopped {
                    crate::exec::frame::lemma_doc_extends_trans(p.doc, p1.doc, dom_insert(p1, text, loc.parent, loc.child).doc);
                }
            },
        }
    }
}

/// "Insert a character".
pub proof fn lemma_insert_char_keeps(p: Parser, c: u32)
    requires
        live(p),
    ensures
        keeps(p, insert_char(p, c)),
        !insert_char(p, c).stopped ==> insert_char(p, c) == (Parser { doc: insert_char(p, c).doc, ..p }),
        !insert_char(p, c).stopped ==> crate::exec::frame::doc_extends(p.doc, insert_char(p, c).doc),
{
    lemma_insert_characters_keeps(p, seq![c]);
}

/// The location is the appropriate place, or one whose parent may receive
/// a child.
pub open spec fn loc_pok(p: Parser, loc: Option<Location>) -> bool {
    match loc {
        Some(l) => pok(p.doc, l.parent),
        None => true,
    }
}

/// "Insert a comment".
pub proof fn lemma_insert_comment_keeps(p: Parser, data: Seq<u32>, loc: Option<Location>)
    requires
        live(p),
        !p.stopped ==> loc_pok(p, loc),
    ensures
        keeps(p, insert_comment(p, data, loc)),
        !insert_comment(p, data, loc).stopped ==> insert_comment(p, data, loc) == (Parser {
            doc: insert_comment(p, data, loc).doc,
            ..p
        }),
        !insert_comment(p, data, loc).stopped ==> crate::exec::frame::doc_extends(p.doc, insert_comment(p, data, loc).doc),
{
    let l = adjusted_location(p, loc);
    lemma_create_keeps(p, NodeKind::Comment { data });
    let (p1, c) = create(p, NodeKind::Comment { data });
    if !p1.stopped {
        lemma_adjusted_pok(p, loc);
        lemma_pok_extends(p.doc, p1.doc, l.parent);
    }
    lemma_dom_insert_keeps(p1, c, l.parent, l.child);
    lemma_keeps_trans(p, p1, dom_insert(p1, c, l.parent, l.child));
    if !p1.stopped {
        crate::exec::frame::lemma_doc_extends_trans(p.doc, p1.doc, dom_insert(p1, c, l.parent, l.child).doc);
    }
}

/// "Insert a processing instruction".
pub proof fn lemma_insert_pi_keeps(p: Parser, target: Seq<u32>, data: Seq<u32>, loc: Option<Location>)
    requires
        live(p),
        !p.stopped ==> loc_pok(p, loc),
    ensures
        keeps(p, insert_pi(p, target, data, loc)),
        !insert_pi(p, target, data, loc).stopped ==> insert_pi(p, target, data, loc) == (Parser {
            doc: insert_pi(p, target, data, loc).doc,
            ..p
        }),
        !insert_pi(p, target, data, loc).stopped ==> crate::exec::frame::doc_extends(p.doc, insert_pi(p, target, data, loc).doc),
{
    let l = adjusted_location(p, loc);
    lemma_create_keeps(p, NodeKind::ProcessingInstruction { target, data });
    let (p1, n) = create(p, NodeKind::ProcessingInstruction { target, data });
    if !p1.stopped {
        lemma_adjusted_pok(p, loc);
        lemma_pok_extends(p.doc, p1.doc, l.parent);
    }
    lemma_dom_insert_keeps(p1, n, l.parent, l.child);
    lemma_keeps_trans(p, p1, dom_insert(p1, n, l.parent, l.child));
    if !p1.stopped {
        crate::exec::frame::lemma_doc_extends_trans(p.doc, p1.doc, dom_insert(p1, n, l.parent, l.child).doc);
    }
}

// ---------------------------------------------------------------------
// The list of active formatting elements

/// Insert a marker.
pub proof fn lemma_push_marker_keeps(p: Parser)
    requires
        live(p),
    ensures
        keeps(p, push_marker(p)),
{
    let q = push_marker(p);
    if !p.stopped {
        assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies q.formatting[i]
            == p.formatting[i] by {}
    }
}

/// Dropping entries from the end of the list keeps [`good`].
pub proof fn lemma_formatting_prefix_keeps(p: Parser, q: Parser)
    requires
        live(p),
        q == (Parser { formatting: q.formatting, ..p }),
        q.formatting.len() <= p.formatting.len(),
        forall|i: int| 0 <= i < q.formatting.len() ==> #[trigger] q.formatting[i] == p.formatting[i],
    ensures
        keeps(p, q),
{
    if !p.stopped {
        assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies q.formatting[i]
            == p.formatting[i] by {}
    }
}

/// "Clear the list of active formatting elements up to the last marker".
pub proof fn lemma_clear_keeps(p: Parser)
    requires
        live(p),
    ensures
        keeps(p, clear_to_last_marker(p)),
        clear_to_last_marker(p) == (Parser { formatting: clear_to_last_marker(p).formatting, ..p }),
    decreases p.formatting.len(),
{
    if p.formatting.len() > 0 {
        let q = Parser { formatting: p.formatting.drop_last(), ..p };
        lemma_formatting_prefix_keeps(p, q);
        if !(p.formatting.last() is Marker) {
            lemma_clear_keeps(q);
            lemma_keeps_trans(p, q, clear_to_last_marker(q));
        }
    } else {
        lemma_keeps_refl(p);
    }
}

} // verus!
