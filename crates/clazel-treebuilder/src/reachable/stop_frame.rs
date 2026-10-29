//! The helpers of the transcription keep the modes ([`mk`]), whether or
//! not they stop parsing: they keep the insertion mode, the original
//! insertion mode, the context and the stack of template insertion modes,
//! keep the list of active formatting elements free of `template` entries
//! (`termination::formatting_ok`), and leave a stopped parser's stack of
//! open elements empty ([`emptied`]: "stop parsing" pops it, and nothing
//! pushes onto a stopped parser's).
//!
//! These are the facts [`super::stopped`] needs to prove
//! `termination::modes_ok` of a parser a rule application stops part-way.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A stopped parser's stack of open elements is empty.
pub open spec fn emptied(p: Parser) -> bool {
    p.stopped ==> p.open.len() == 0
}

/// `q` has `p`'s insertion mode, original insertion mode, context and stack
/// of template insertion modes; its list of active formatting elements has
/// no `template` entry if `p`'s has none, and its stack is empty if it has
/// stopped and `p`'s stack is empty if `p` has stopped.
pub open spec fn mk(p: Parser, q: Parser) -> bool {
    &&& q.mode == p.mode
    &&& q.original_mode == p.original_mode
    &&& q.context == p.context
    &&& q.template_modes == p.template_modes
    &&& formatting_ok(p) ==> formatting_ok(q)
    &&& emptied(p) ==> emptied(q)
}

/// [`mk`] is transitive.
pub proof fn lemma_mk_trans(p: Parser, q: Parser, r: Parser)
    requires
        mk(p, q),
        mk(q, r),
    ensures
        mk(p, r),
{
}

// ---------------------------------------------------------------------
// The stack of open elements and the arena

/// "Pop the current node".
pub broadcast proof fn lemma_pop(p: Parser)
    ensures
        mk(p, #[trigger] pop(p)),
{
}

/// Push onto the stack of open elements.
pub broadcast proof fn lemma_push(p: Parser, e: Elem)
    ensures
        mk(p, #[trigger] push(p, e)),
{
}

/// Stop parsing.
pub broadcast proof fn lemma_stop_parsing(p: Parser)
    ensures
        mk(p, #[trigger] stop_parsing(p)),
{
}

/// Insert a node in the arena.
pub broadcast proof fn lemma_dom_insert(p: Parser, node: NodeId, parent: NodeId, child: Option<NodeId>)
    ensures
        mk(p, #[trigger] dom_insert(p, node, parent, child)),
{
}

/// Remove a node from its parent.
pub broadcast proof fn lemma_dom_remove(p: Parser, node: NodeId)
    ensures
        mk(p, #[trigger] dom_remove(p, node)),
{
}

/// Create a node, or stop parsing.
pub broadcast proof fn lemma_create(p: Parser, k: NodeKind)
    ensures
        mk(p, (#[trigger] create(p, k)).0),
        create(p, k).0.formatting == p.formatting,
{
}

/// Create an element for a token.
pub broadcast proof fn lemma_create_element_for_token(p: Parser, t: TagTok, ns: Namespace, ip: NodeId)
    ensures
        mk(p, (#[trigger] create_element_for_token(p, t, ns, ip)).0),
        create_element_for_token(p, t, ns, ip).0.formatting == p.formatting,
{
    hide(create);
    let owner = if is_form_associated(ns, t.tag) && p.form is Some && !parsing_template_contents(p) && p.context is None && (
    !is_listed(ns, t.tag) || !has_attr(t, name_form())) && same_tree(p.doc, ip, p.form->Some_0) {
        p.form
    } else {
        None
    };
    lemma_create(
        p,
        NodeKind::Element {
            namespace: Some(ns),
            prefix: None,
            local_name: t.name,
            attributes: t.attrs,
            template_contents: None,
            form_owner: owner,
        },
    );
}

/// Insert an element at a location.
pub broadcast proof fn lemma_insert_element_at(p: Parser, el: NodeId, loc: Option<Location>)
    ensures
        mk(p, #[trigger] insert_element_at(p, el, loc)),
{
}

/// Insert a foreign element.
pub broadcast proof fn lemma_insert_foreign_element(p: Parser, t: TagTok, ns: Namespace)
    ensures
        mk(p, (#[trigger] insert_foreign_element(p, t, ns)).0),
{
    hide(create_element_for_token);
    hide(insert_element_at);
    hide(push);
    let (p1, e) = create_element_for_token(p, t, ns, appropriate_place(p, None).parent);
    lemma_create_element_for_token(p, t, ns, appropriate_place(p, None).parent);
    lemma_insert_element_at(p1, e.id, None);
    let p2 = insert_element_at(p1, e.id, None);
    lemma_push(p2, e);
}

/// Insert an HTML element.
pub broadcast proof fn lemma_insert_html_element(p: Parser, t: TagTok)
    ensures
        mk(p, (#[trigger] insert_html_element(p, t)).0),
{
    hide(insert_foreign_element);
    lemma_insert_foreign_element(p, t, Namespace::Html);
}

/// Insert characters.
pub broadcast proof fn lemma_insert_characters(p: Parser, data: Seq<u32>)
    ensures
        mk(p, #[trigger] insert_characters(p, data)),
{
    hide(create);
    hide(dom_insert);
    hide(adjusted_location);
    lemma_create(p, NodeKind::Text { data });
    let (p1, text) = create(p, NodeKind::Text { data });
    let loc = adjusted_location(p, None);
    lemma_dom_insert(p1, text, loc.parent, loc.child);
}

/// Insert a character.
pub broadcast proof fn lemma_insert_char(p: Parser, c: u32)
    ensures
        mk(p, #[trigger] insert_char(p, c)),
{
    hide(insert_characters);
    lemma_insert_characters(p, seq![c]);
}

/// Insert a comment.
pub broadcast proof fn lemma_insert_comment(p: Parser, data: Seq<u32>, loc: Option<Location>)
    ensures
        mk(p, #[trigger] insert_comment(p, data, loc)),
{
    hide(create);
    hide(dom_insert);
    hide(adjusted_location);
    lemma_create(p, NodeKind::Comment { data });
    let (p1, c) = create(p, NodeKind::Comment { data });
    let l = adjusted_location(p, loc);
    lemma_dom_insert(p1, c, l.parent, l.child);
}

/// Insert a processing instruction.
pub broadcast proof fn lemma_insert_pi(p: Parser, target: Seq<u32>, data: Seq<u32>, loc: Option<Location>)
    ensures
        mk(p, #[trigger] insert_pi(p, target, data, loc)),
{
    hide(create);
    hide(dom_insert);
    hide(adjusted_location);
    lemma_create(p, NodeKind::ProcessingInstruction { target, data });
    let (p1, n) = create(p, NodeKind::ProcessingInstruction { target, data });
    let l = adjusted_location(p, loc);
    lemma_dom_insert(p1, n, l.parent, l.child);
}

/// The generic raw text and RCDATA element parsing algorithms keep
/// everything [`mk`] says but the modes, which they set.
pub broadcast proof fn lemma_generic_text_parsing(p: Parser, t: TagTok, rawtext: bool)
    ensures
        ({
            let q = #[trigger] generic_text_parsing(p, t, rawtext);
            &&& mk(p, Parser { mode: p.mode, original_mode: p.original_mode, ..q })
            &&& q.mode == Mode::Text
            &&& q.original_mode == p.mode
        }),
{
    hide(insert_html_element);
    lemma_insert_html_element(p, t);
}

/// Pop while the current node satisfies `f`.
pub broadcast proof fn lemma_pop_while(p: Parser, f: spec_fn(Elem) -> bool)
    ensures
        mk(p, #[trigger] pop_while(p, f)),
    decreases p.open.len(),
{
    if p.open.len() > 0 && f(current_node(p)) {
        lemma_pop_while(pop(p), f);
    }
}

/// Generate implied end tags.
pub broadcast proof fn lemma_generate_implied_end_tags(p: Parser, except: Option<Tag>)
    ensures
        mk(p, #[trigger] generate_implied_end_tags(p, except)),
{
    hide(pop_while);
    lemma_pop_while(p, |e: Elem| implied_end_tag(e) && !(except is Some && e.tag == except->Some_0));
}

/// Generate all implied end tags thoroughly.
pub broadcast proof fn lemma_generate_all_implied_end_tags_thoroughly(p: Parser)
    ensures
        mk(p, #[trigger] generate_all_implied_end_tags_thoroughly(p)),
{
    hide(pop_while);
    lemma_pop_while(
        p,
        |e: Elem|
            e.ns == Namespace::Html && match e.tag {
                Tag::Caption | Tag::Colgroup | Tag::Dd | Tag::Dt | Tag::Li | Tag::Optgroup | Tag::Option | Tag::P | Tag::Rb
                | Tag::Rp | Tag::Rt | Tag::Rtc | Tag::Tbody | Tag::Td | Tag::Tfoot | Tag::Th | Tag::Thead | Tag::Tr => true,
                _ => false,
            },
    );
}

/// Pop until an HTML element named `tag` has been popped.
pub broadcast proof fn lemma_pop_until_popped(p: Parser, tag: Tag)
    ensures
        mk(p, #[trigger] pop_until_popped(p, tag)),
    decreases p.open.len(),
{
    if p.open.len() > 0 && !is_html(current_node(p), tag) {
        lemma_pop_until_popped(pop(p), tag);
    }
}

/// Pop until a heading has been popped.
pub broadcast proof fn lemma_pop_until_heading_popped(p: Parser)
    ensures
        mk(p, #[trigger] pop_until_heading_popped(p)),
    decreases p.open.len(),
{
    if p.open.len() > 0 && !is_heading(current_node(p)) {
        lemma_pop_until_heading_popped(pop(p));
    }
}

/// Pop until a node has been popped.
pub broadcast proof fn lemma_pop_until_node_popped(p: Parser, id: NodeId)
    ensures
        mk(p, #[trigger] pop_until_node_popped(p, id)),
        pop_until_node_popped(p, id).formatting == p.formatting,
    decreases p.open.len(),
{
    if p.open.len() > 0 && current_node(p).id != id {
        lemma_pop_until_node_popped(pop(p), id);
    }
}

/// Pop until a `td` or `th` has been popped.
pub broadcast proof fn lemma_pop_until_cell_popped(p: Parser)
    ensures
        mk(p, #[trigger] pop_until_cell_popped(p)),
    decreases p.open.len(),
{
    if p.open.len() > 0 {
        lemma_pop_until_cell_popped(pop(p));
    }
}

/// Remove an entry of a running parser's stack of open elements.
pub broadcast proof fn lemma_remove_open_at(p: Parser, i: int)
    ensures
        !p.stopped ==> mk(p, #[trigger] remove_open_at(p, i)),
{
}

/// "Reset the insertion mode appropriately" keeps everything [`mk`] says
/// but the mode; on a stopped parser with an empty stack it lands on "in
/// body".
pub broadcast proof fn lemma_reset_insertion_mode(p: Parser)
    ensures
        mk(p, Parser { mode: p.mode, ..#[trigger] reset_insertion_mode(p) }),
        p.open.len() == 0 ==> reset_insertion_mode(p).mode == Mode::InBody,
{
}

// ---------------------------------------------------------------------
// The list of active formatting elements

/// Push onto the list of active formatting elements an entry for a token
/// other than `template`.
pub broadcast proof fn lemma_push_formatting(p: Parser, e: Elem, t: TagTok)
    ensures
        t.tag != Tag::Template ==> mk(p, #[trigger] push_formatting(p, e, t)),
{
    if !p.stopped && t.tag != Tag::Template && formatting_ok(p) {
        let f = p.formatting;
        crate::exec::modes::in_body_start_lemmas::lemma_after_last_marker_nonneg(f, f.len() as int);
        let from = after_last_marker(f, f.len() as int);
        let fam = family_indices(f, from, f.len() as int, e, t);
        super::lists::lemma_family_range(f, from, f.len() as int, e, t);
        if fam.len() >= 3 {
            assert(0 <= fam[0] < f.len());
        }
        let f1 = if fam.len() >= 3 {
            f.remove(fam[0])
        } else {
            f
        };
        let q = push_formatting(p, e, t);
        assert(q.formatting == f1.push(Fmt::Entry { elem: e, token: t }));
        assert forall|i: int| 0 <= i < f1.len() && #[trigger] f1[i] is Entry implies f1[i]->Entry_token.tag != Tag::Template by {
            if fam.len() >= 3 {
                assert(f1[i] == f[i] || f1[i] == f[i + 1]);
            }
        }
        assert forall|i: int| 0 <= i < q.formatting.len() && #[trigger] q.formatting[i] is Entry implies q.formatting[i]->Entry_token.tag
            != Tag::Template by {
            if i < f1.len() {
                assert(q.formatting[i] == f1[i]);
            }
        }
    }
}

/// Insert a marker.
pub broadcast proof fn lemma_push_marker(p: Parser)
    ensures
        mk(p, #[trigger] push_marker(p)),
{
    let q = push_marker(p);
    if formatting_ok(p) {
        assert forall|i: int| 0 <= i < q.formatting.len() && #[trigger] q.formatting[i] is Entry implies q.formatting[i]->Entry_token.tag
            != Tag::Template by {
            assert(q.formatting[i] == p.formatting[i]);
        }
    }
}

/// Clear the list of active formatting elements up to the last marker.
pub broadcast proof fn lemma_clear_to_last_marker(p: Parser)
    ensures
        mk(p, #[trigger] clear_to_last_marker(p)),
{
    crate::termination::helpers_ranking::lemma_clear_to_last_marker(p);
}

/// Reconstruct the active formatting elements, from entry `i`.
pub broadcast proof fn lemma_reconstruct_create(p: Parser, i: int)
    ensures
        mk(p, #[trigger] reconstruct_create(p, i)),
    decreases p.formatting.len() - i,
{
    hide(insert_html_element);
    if !(i < 0 || i >= p.formatting.len() || p.stopped || !(p.formatting[i] is Entry)) {
        let token = p.formatting[i]->Entry_token;
        let (p1, new_element) = insert_html_element(p, token);
        lemma_insert_html_element(p, token);
        let p2 = if p1.stopped {
            p1
        } else {
            Parser { formatting: p1.formatting.update(i, Fmt::Entry { elem: new_element, token }), ..p1 }
        };
        if formatting_ok(p) {
            assert forall|k: int| 0 <= k < p2.formatting.len() && #[trigger] p2.formatting[k] is Entry implies p2.formatting[k]->Entry_token.tag
                != Tag::Template by {
                if k != i && !p1.stopped {
                    assert(p2.formatting[k] == p1.formatting[k]);
                }
            }
        }
        assert(mk(p, p2));
        if i + 1 < p2.formatting.len() && p2.formatting.len() == p.formatting.len() {
            lemma_reconstruct_create(p2, i + 1);
        }
    }
}

/// Reconstruct the active formatting elements.
pub broadcast proof fn lemma_reconstruct_formatting(p: Parser)
    ensures
        mk(p, #[trigger] reconstruct_formatting(p)),
{
    hide(reconstruct_create);
    let n = p.formatting.len();
    if n > 0 {
        lemma_reconstruct_create(p, reconstruct_rewind(p, n - 1));
    }
}

} // verus!
