//! Lemmas for the "in body" start tag cases (HTML §13.2.6.4.7): popping
//! keeps a prefix of the stack of open elements, so the stack stays rooted
//! at the `html` element ([`stack_rooted`]) when the element popped to is
//! above it; and appending an attribute extends the document.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::exec::frame::*;
#[cfg(verus_only)]
use crate::exec::stack::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`last_index_where`] reads only the first `i` entries.
pub proof fn lemma_liw_prefix(a: Seq<Elem>, b: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool)
    requires
        0 <= i <= a.len(),
        i <= b.len(),
        forall|j: int| 0 <= j < i ==> a[j] == b[j],
    ensures
        last_index_where(a, i, f) == last_index_where(b, i, f),
    decreases i,
{
    if i > 0 {
        assert(a[i - 1] == b[i - 1]);
        lemma_liw_prefix(a, b, i - 1, f);
    }
}

/// A target in scope is on the stack: [`in_scope_from`] implies
/// [`last_index_where`] finds it.
pub proof fn lemma_scope_liw(o: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool, s: Scope)
    requires
        0 <= i <= o.len(),
        in_scope_from(o, i, f, s),
    ensures
        last_index_where(o, i, f) >= 0,
    decreases i,
{
    if i > 0 && !f(o[i - 1]) {
        lemma_scope_liw(o, i - 1, f, s);
    }
}

/// [`pop_while`] keeps a prefix of the stack, and every entry below one
/// that does not satisfy `f`; it changes nothing else.
pub proof fn lemma_pop_while_prefix(p: Parser, f: spec_fn(Elem) -> bool)
    ensures
        pop_while(p, f) == with_open(p, pop_while(p, f).open),
        pop_while(p, f).open.len() <= p.open.len(),
        forall|j: int| 0 <= j < pop_while(p, f).open.len() ==> #[trigger] pop_while(p, f).open[j] == p.open[j],
        forall|k: int| 0 <= k < p.open.len() && !f(#[trigger] p.open[k]) ==> pop_while(p, f).open.len() > k,
    decreases p.open.len(),
{
    if p.open.len() > 0 && f(current_node(p)) {
        let q = pop(p);
        lemma_pop_while_prefix(q, f);
        assert forall|j: int| 0 <= j < pop_while(p, f).open.len() implies #[trigger] pop_while(p, f).open[j] == p.open[j] by {
            assert(q.open[j] == p.open[j]);
        }
        assert forall|k: int| 0 <= k < p.open.len() && !f(#[trigger] p.open[k]) implies pop_while(p, f).open.len() > k by {
            assert(k != p.open.len() - 1);
            assert(q.open[k] == p.open[k]);
        }
    }
}

/// [`pop_until_where`] keeps a prefix of the stack, down to the last entry
/// satisfying `f` if there is one; it changes nothing else.
pub proof fn lemma_pop_until_where_prefix(p: Parser, f: spec_fn(Elem) -> bool)
    ensures
        pop_until_where(p, f) == with_open(p, pop_until_where(p, f).open),
        pop_until_where(p, f).open.len() <= p.open.len(),
        forall|j: int| 0 <= j < pop_until_where(p, f).open.len() ==> #[trigger] pop_until_where(p, f).open[j] == p.open[j],
        last_index_where(p.open, p.open.len() as int, f) >= 0 ==> pop_until_where(p, f).open.len() == last_index_where(
            p.open,
            p.open.len() as int,
            f,
        ),
    decreases p.open.len(),
{
    if p.open.len() > 0 {
        let q = pop(p);
        let n = p.open.len() as int;
        if !f(current_node(p)) {
            lemma_pop_until_where_prefix(q, f);
            assert forall|j: int| 0 <= j < pop_until_where(p, f).open.len() implies #[trigger] pop_until_where(p, f).open[j]
                == p.open[j] by {
                assert(q.open[j] == p.open[j]);
            }
            assert forall|j: int| 0 <= j < n - 1 implies q.open[j] == p.open[j] by {}
            lemma_liw_prefix(q.open, p.open, n - 1, f);
        }
    }
}

/// The predicate of [`pop_until_popped`] for `tag`.
pub open spec fn html_pred(tag: Tag) -> spec_fn(Elem) -> bool {
    |e: Elem| is_html(e, tag)
}

/// The predicate of [`generate_implied_end_tags`] with `except`.
pub open spec fn implied_pred(except: Option<Tag>) -> spec_fn(Elem) -> bool {
    |e: Elem| implied_end_tag(e) && !(except is Some && e.tag == except->Some_0)
}

/// "Generate implied end tags" keeps the stack rooted, the first entry
/// and everything but the stack.
pub proof fn lemma_implied_rooted(p: Parser, except: Option<Tag>)
    requires
        stack_rooted(p),
    ensures
        stack_rooted(generate_implied_end_tags(p, except)),
        generate_implied_end_tags(p, except) == with_open(p, generate_implied_end_tags(p, except).open),
        generate_implied_end_tags(p, except).open[0] == p.open[0],
{
    let f = implied_pred(except);
    assert(generate_implied_end_tags(p, except) == pop_while(p, f));
    lemma_pop_while_prefix(p, f);
    assert(!f(p.open[0]));
}

/// Popping until an HTML `tag` element has been popped, when one is at
/// index `k >= 1`, keeps the stack rooted (and changes nothing but the
/// stack).
pub proof fn lemma_pop_until_rooted(p: Parser, tag: Tag, k: int)
    requires
        stack_rooted(p),
        1 <= k < p.open.len(),
        is_html(p.open[k], tag),
    ensures
        stack_rooted(pop_until_popped(p, tag)),
        pop_until_popped(p, tag) == with_open(p, pop_until_popped(p, tag).open),
{
    let f = html_pred(tag);
    lemma_pop_until_popped(p, tag);
    assert(pop_until_popped(p, tag) == pop_until_where(p, f)) by {
        assert(f =~= (|e: Elem| is_html(e, tag)));
    }
    lemma_pop_until_where_prefix(p, f);
    lemma_last_index_where_found(p.open, p.open.len() as int, f, k);
    let q = pop_until_popped(p, tag);
    assert(q.open[0] == p.open[0]);
}

/// "Generate implied end tags, except for `except`", then pop until an
/// HTML `tag` element has been popped, when one that the first step does
/// not pop is at index `k >= 1`: the stack stays rooted.
pub proof fn lemma_close_rooted(p: Parser, except: Option<Tag>, tag: Tag, k: int)
    requires
        stack_rooted(p),
        1 <= k < p.open.len(),
        is_html(p.open[k], tag),
        !(implied_end_tag(p.open[k]) && !(except is Some && p.open[k].tag == except->Some_0)),
    ensures
        stack_rooted(pop_until_popped(generate_implied_end_tags(p, except), tag)),
        pop_until_popped(generate_implied_end_tags(p, except), tag) == with_open(
            p,
            pop_until_popped(generate_implied_end_tags(p, except), tag).open,
        ),
{
    let f = implied_pred(except);
    let q = generate_implied_end_tags(p, except);
    assert(q == pop_while(p, f));
    lemma_pop_while_prefix(p, f);
    lemma_implied_rooted(p, except);
    assert(q.open.len() > k);
    assert(q.open[k] == p.open[k]);
    lemma_pop_until_rooted(q, tag, k);
}

/// A tag in scope other than `html`, on a rooted stack, is at an index
/// `k >= 1`: the last such index.
pub proof fn lemma_scope_index(p: Parser, tag: Tag, s: Scope) -> (k: int)
    requires
        stack_rooted(p),
        has_in_scope(p, tag, s),
        tag != Tag::Html,
    ensures
        1 <= k < p.open.len(),
        is_html(p.open[k], tag),
        k == last_index_where(p.open, p.open.len() as int, html_pred(tag)),
{
    let f = html_pred(tag);
    assert(has_in_scope(p, tag, s) == in_scope_from(p.open, p.open.len() as int, f, s)) by {
        assert(f =~= (|e: Elem| is_html(e, tag)));
    }
    lemma_scope_liw(p.open, p.open.len() as int, f, s);
    lemma_last_index_where(p.open, p.open.len() as int, f);
    let k = last_index_where(p.open, p.open.len() as int, f);
    assert(k != 0);
    k
}

/// [`close_p_element`] when a `p` is in button scope keeps the stack
/// rooted.
pub proof fn lemma_close_p_rooted(p: Parser)
    requires
        stack_rooted(p),
        has_in_scope(p, Tag::P, Scope::Button),
    ensures
        stack_rooted(close_p_element(p)),
        close_p_element(p) == with_open(p, close_p_element(p).open),
{
    let k = lemma_scope_index(p, Tag::P, Scope::Button);
    lemma_close_rooted(p, Some(Tag::P), Tag::P, k);
}

/// Popping a current node that is not the `html` element keeps the stack
/// rooted.
pub proof fn lemma_pop_rooted(p: Parser)
    requires
        stack_rooted(p),
        !is_html(current_node(p), Tag::Html),
    ensures
        stack_rooted(pop(p)),
        pop(p) == with_open(p, pop(p).open),
{
    assert(p.open.len() >= 2);
    assert(pop(p).open[0] == p.open[0]);
}

/// [`fmt_last_where`] is -1 or the index of an element entry in `from..i`
/// whose element satisfies `pred`.
pub proof fn lemma_fmt_last_where(f: Seq<Fmt>, from: int, i: int, pred: spec_fn(Elem) -> bool)
    requires
        0 <= from,
        i <= f.len(),
    ensures
        fmt_last_where(f, from, i, pred) >= 0 ==> from <= fmt_last_where(f, from, i, pred) < i && f[fmt_last_where(
            f,
            from,
            i,
            pred,
        )] is Entry && pred(f[fmt_last_where(f, from, i, pred)]->Entry_elem),
    decreases i - from,
{
    if i > from && !(f[i - 1] is Entry && pred(f[i - 1]->Entry_elem)) {
        lemma_fmt_last_where(f, from, i - 1, pred);
    }
}

/// [`after_last_marker`] is not negative.
pub proof fn lemma_after_last_marker_nonneg(f: Seq<Fmt>, i: int)
    ensures
        after_last_marker(f, i) >= 0,
    decreases i,
{
    if i > 0 && !(f[i - 1] is Marker) {
        lemma_after_last_marker_nonneg(f, i - 1);
    }
}

/// Case 29's entry: the last `a` element entry after the last marker is an
/// element entry of the list, whose element is an HTML `a` element of the
/// document, tagged by its name.
pub proof fn lemma_a_entry(p: Parser, i: int)
    requires
        parser_inv(p),
        i >= 0,
        i == fmt_last_where(
            p.formatting,
            after_last_marker(p.formatting, p.formatting.len() as int),
            p.formatting.len() as int,
            |e: Elem| is_html(e, Tag::A),
        ),
    ensures
        i < p.formatting.len(),
        p.formatting[i] is Entry,
        elem_in_doc(p.doc, p.formatting[i]->Entry_elem),
        elem_tagged(p.formatting[i]->Entry_elem),
        is_html(p.formatting[i]->Entry_elem, Tag::A),
{
    let f = p.formatting;
    let pred = |e: Elem| is_html(e, Tag::A);
    lemma_after_last_marker_nonneg(f, f.len() as int);
    lemma_fmt_last_where(f, after_last_marker(f, f.len() as int), f.len() as int, pred);
    lemma_inv_iff(p);
    assert(fmt_ok(p.doc, f[i]));
}

/// Appending an attribute to an element extends the document.
pub proof fn lemma_append_attribute_extends(doc: Document, e: NodeId, a: Attr)
    requires
        clazel_dom::contract::append_attribute_requires(doc, e),
    ensures
        doc_extends(doc, dom::append_attribute(doc, e, a)),
{
    clazel_dom::lemmas::theorem_append_attribute_wf(doc, e, a);
    let d = dom::append_attribute(doc, e, a);
    assert forall|i: int| 0 <= i < doc.nodes.len() implies kind_kept(doc.nodes[i].kind, #[trigger] d.nodes[i].kind) by {
        if i != e {
            assert(d.nodes[i] == doc.nodes[i]);
        }
    }
    assert forall|m: NodeId|
        dom::valid(d, m) && #[trigger] node_is_template(d, m) && d.nodes[m as int].children.len() > 0 implies has_template_contents(
        d,
        m,
    ) || (m < doc.nodes.len() && doc.nodes[m as int].children.len() > 0) by {
        if m != e {
            assert(d.nodes[m as int] == doc.nodes[m as int]);
        } else {
            assert(d.nodes[m as int].children == doc.nodes[m as int].children);
        }
    }
}

/// A document extends itself.
pub proof fn lemma_doc_extends_refl(doc: Document)
    requires
        dom::wf(doc),
    ensures
        doc_extends(doc, doc),
{
}

} // verus!
