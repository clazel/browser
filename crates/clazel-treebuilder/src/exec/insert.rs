//! HTML §13.2.6.1 "creating and inserting nodes", §13.2.6.2, §13.2.6.3
//! and §13.2.4.3 "reconstruct the active formatting elements" over
//! [`ParserBuf`], with the guarded DOM calls. Each function is proven equal
//! to the spec function of `spec/base/insert.rs` it names, and to keep
//! [`parser_inv`].
//!
//! Every function that computes "the appropriate place for inserting a
//! node" needs the stack rooted at an `html` element ([`stack_rooted`]) or
//! the parser stopped; a given insertion location must be [`loc_ok`].

use super::formatting::fmt_on_stack_exec;
#[cfg(verus_only)]
use super::frame::*;
use super::names::*;
#[allow(unused_imports)]
use super::spec::*;
use super::stack::*;
use super::types::*;
use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Facts of a well-formed arena

/// A node's parent is a node that lists it as a child.
pub proof fn lemma_wf_parent(doc: Document, n: NodeId)
    requires
        dom::wf(doc),
        dom::valid(doc, n),
        doc.nodes[n as int].parent is Some,
    ensures
        dom::valid(doc, doc.nodes[n as int].parent->Some_0),
        doc.nodes[doc.nodes[n as int].parent->Some_0 as int].children.contains(n),
        doc.nodes[doc.nodes[n as int].parent->Some_0 as int].children.len() > 0,
{
    let paths = clazel_dom::lemmas::lemma_wf_witness(doc);
    assert(doc.nodes[n as int].parent is Some);
}

/// A node's children are nodes.
pub proof fn lemma_wf_child(doc: Document, n: NodeId, j: int)
    requires
        dom::wf(doc),
        dom::valid(doc, n),
        0 <= j < doc.nodes[n as int].children.len(),
    ensures
        dom::valid(doc, doc.nodes[n as int].children[j]),
{
    let paths = clazel_dom::lemmas::lemma_wf_witness(doc);
    let c = doc.nodes[n as int].children[j];
}

/// A template's contents is a fragment of the arena.
pub proof fn lemma_wf_contents(doc: Document, n: NodeId)
    requires
        dom::wf(doc),
        has_template_contents(doc, n),
    ensures
        dom::valid(doc, template_contents(doc, n)),
        doc.nodes[template_contents(doc, n) as int].kind is DocumentFragment,
{
    let paths = clazel_dom::lemmas::lemma_wf_witness(doc);
    assert(doc.nodes[n as int].kind is Element);
}

/// The arena is not empty.
pub proof fn lemma_wf_nonempty(doc: Document)
    requires
        dom::wf(doc),
    ensures
        dom::valid(doc, 0),
        doc.nodes[0].kind is Document,
{
    let paths = clazel_dom::lemmas::lemma_wf_witness(doc);
}

// ---------------------------------------------------------------------
// The parts of the state the insertions keep

/// `q` is `p` with only the document, the stack of open elements, the
/// stopped flag and the actions changed.
pub open spec fn same_but_tree(p: Parser, q: Parser) -> bool {
    &&& q.mode == p.mode
    &&& q.original_mode == p.original_mode
    &&& q.template_modes == p.template_modes
    &&& q.formatting == p.formatting
    &&& q.head == p.head
    &&& q.form == p.form
    &&& q.context == p.context
    &&& q.scripting == p.scripting
    &&& q.frameset_ok == p.frameset_ok
    &&& q.foster == p.foster
    &&& q.pending_table_text == p.pending_table_text
    &&& q.skip_lf == p.skip_lf
    &&& q.tokenizer == p.tokenizer
    &&& q.tentative == p.tentative
    &&& q.redirect == p.redirect
}

/// An insertion location the DOM calls accept: its parent and child are
/// nodes, and the parent is no template without template contents.
pub open spec fn loc_ok(doc: Document, l: Location) -> bool {
    &&& dom::valid(doc, l.parent)
    &&& (node_is_template(doc, l.parent) ==> has_template_contents(doc, l.parent))
    &&& match l.child {
        Some(c) => dom::valid(doc, c),
        None => true,
    }
}

/// [`loc_ok`] survives [`doc_extends`].
pub proof fn lemma_loc_ok_extends(d0: Document, d1: Document, l: Location)
    requires
        loc_ok(d0, l),
        doc_extends(d0, d1),
    ensures
        loc_ok(d1, l),
{
    assert(kind_kept(d0.nodes[l.parent as int].kind, d1.nodes[l.parent as int].kind));
}

/// The view of an optional borrowed element record.
pub open spec fn opt_ref_view(e: Option<&ExecElem>) -> Option<Elem> {
    match e {
        Some(x) => Some(x@),
        None => None,
    }
}

// ---------------------------------------------------------------------
// Guarded DOM calls and stopping

/// [`dom_insert`]: the DOM's "insert" when [`insert_valid`] holds,
/// nothing otherwise. A new parent that is a `template` must have template
/// contents.
pub fn dom_insert_exec(p: &mut ParserBuf, node: usize, parent: usize, child: Option<usize>)
    requires
        parser_inv(old(p)@),
        node_is_template(old(p)@.doc, parent) ==> has_template_contents(old(p)@.doc, parent),
    ensures
        final(p)@ == dom_insert(old(p)@, node, parent, child),
        parser_inv(final(p)@),
        doc_extends(old(p)@.doc, final(p)@.doc),
        final(p)@ == (Parser { doc: final(p)@.doc, ..old(p)@ }),
{
    proof {
        lemma_inv_iff(old(p)@);
        assert(doc_extends(p@.doc, p@.doc)) by {
            assert forall|i: int| 0 <= i < p@.doc.nodes.len() implies kind_kept(
                p@.doc.nodes[i].kind,
                #[trigger] p@.doc.nodes[i].kind,
            ) by {}
        }
    }
    if p.stopped {
        return ;
    }
    let len = p.arena.len();
    if node >= len || parent >= len {
        return ;
    }
    let ok_node = !matches!(p.arena.kind(node), ExecKind::Document { .. } | ExecKind::DocumentFragment { .. });
    let ok_parent = matches!(
        p.arena.kind(parent),
        ExecKind::Document { .. } | ExecKind::Element { .. } | ExecKind::DocumentFragment { .. }
    );
    if !ok_node || !ok_parent || p.arena.is_inclusive_ancestor(node, parent) {
        return ;
    }
    match child {
        None => {
            proof {
                lemma_insert_extends(old(p)@.doc, node, parent, None);
            }
            p.arena.append(parent, node);
        },
        Some(c) => {
            if c >= len || c == node || p.arena.parent(c) != Some(parent) {
                return ;
            }
            proof {
                lemma_insert_extends(old(p)@.doc, node, parent, Some(c));
            }
            p.arena.insert_before(parent, node, c);
        },
    }
    proof {
        lemma_inv_doc(old(p)@, p@.doc);
    }
}

/// [`dom_remove`]: the DOM's "remove" of a node with a parent.
pub fn dom_remove_exec(p: &mut ParserBuf, node: usize)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == dom_remove(old(p)@, node),
        parser_inv(final(p)@),
{
    if p.stopped || node >= p.arena.len() || p.arena.parent(node).is_none() {
        return ;
    }
    proof {
        lemma_inv_iff(old(p)@);
        lemma_remove_extends(old(p)@.doc, node);
    }
    p.arena.remove(node);
    proof {
        lemma_inv_doc(old(p)@, p@.doc);
    }
}

/// §13.2.7 "stop parsing" ([`stop_parsing`]).
pub fn stop_parsing_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == stop_parsing(old(p)@),
        parser_inv(final(p)@),
        same_but_tree(old(p)@, final(p)@),
        final(p)@.doc == old(p)@.doc,
{
    if p.stopped {
        return ;
    }
    let ghost a = p.actions@;
    p.open = Vec::new();
    p.stopped = true;
    p.actions.push(ExecAction::StopParsing);
    proof {
        assert(elems_view(p.open@) =~= Seq::<Elem>::empty());
        assert(actions_view(p.actions@) =~= actions_view(a).push(Action::StopParsing));
        lemma_inv_iff(old(p)@);
        lemma_inv_iff(p@);
        assert(crate::termination::templates_in(p@.open, 0) == 0);
    }
}

/// [`create`]: a new node of kind `k`, or "stop parsing" at the node limit;
/// the node's id (0 if none was created).
pub fn create_exec(p: &mut ParserBuf, k: ExecKind) -> (r: usize)
    requires
        parser_inv(old(p)@),
        dom::creatable(old(p)@.doc, k@),
    ensures
        (final(p)@, r) == create(old(p)@, k@),
        parser_inv(final(p)@),
        doc_extends(old(p)@.doc, final(p)@.doc),
        !final(p)@.stopped ==> r == old(p)@.doc.nodes.len() && final(p)@.doc == dom::create_node(old(p)@.doc, k@).0
            && final(p)@ == (Parser { doc: final(p)@.doc, ..old(p)@ }),
        same_but_tree(old(p)@, final(p)@),
{
    proof {
        lemma_inv_iff(old(p)@);
        assert(doc_extends(p@.doc, p@.doc)) by {
            assert forall|i: int| 0 <= i < p@.doc.nodes.len() implies kind_kept(
                p@.doc.nodes[i].kind,
                #[trigger] p@.doc.nodes[i].kind,
            ) by {}
        }
    }
    if p.stopped {
        return 0;
    }
    let ghost kv = k@;
    match p.arena.create(k) {
        Some(id) => {
            proof {
                lemma_create_extends(old(p)@.doc, kv);
                lemma_inv_doc(old(p)@, p@.doc);
            }
            id
        },
        None => {
            stop_parsing_exec(p);
            0
        },
    }
}

// ---------------------------------------------------------------------
// The appropriate place for inserting a node

/// [`is_table_like`].
pub fn is_table_like_exec(e: &ExecElem) -> (r: bool)
    ensures
        r == is_table_like(e@),
{
    is_html_ns(e) && matches!(e.tag, Tag::Table | Tag::Tbody | Tag::Tfoot | Tag::Thead | Tag::Tr)
}

/// [`node_is_template`].
pub fn node_is_template_exec(a: &Arena, n: usize) -> (r: bool)
    ensures
        r == node_is_template(a@, n),
{
    if n >= a.len() {
        return false;
    }
    match a.kind(n) {
        ExecKind::Element { namespace: Some(Namespace::Html), local_name, .. } => matches!(
            tag_of_exec(local_name.as_slice()),
            Tag::Template
        ),
        _ => false,
    }
}

/// [`template_contents`].
pub fn template_contents_exec(a: &Arena, n: usize) -> (r: usize)
    requires
        has_template_contents(a@, n),
    ensures
        r == template_contents(a@, n),
{
    match a.kind(n) {
        ExecKind::Element { template_contents: Some(f), .. } => *f,
        _ => vstd::pervasive::unreached(),
    }
}

/// The record at index `i` of the stack.
fn open_at(p: &ParserBuf, i: usize) -> (r: &ExecElem)
    requires
        i < p@.open.len(),
    ensures
        r@ == p@.open[i as int],
{
    match p.open.get(i) {
        Some(e) => e,
        None => vstd::pervasive::unreached(),
    }
}

/// An element record that is [`elem_ok`] and not a `template` names a node
/// that is no template.
proof fn lemma_not_template_node(doc: Document, e: Elem)
    requires
        elem_ok(doc, e),
        !is_html(e, Tag::Template),
    ensures
        !node_is_template(doc, e.id),
{
}

/// §13.2.6.1 "appropriate place for inserting a node"
/// ([`appropriate_place`]), with an optional override target.
#[verifier::rlimit(60)]
pub fn appropriate_place_exec(p: &ParserBuf, ov: Option<&ExecElem>) -> (r: Location)
    requires
        parser_inv(p@),
        stack_rooted(p@),
        match ov {
            Some(e) => elem_ok(p@.doc, e@),
            None => true,
        },
    ensures
        r == appropriate_place(p@, opt_ref_view(ov)),
        loc_ok(p@.doc, r),
{
    proof {
        lemma_inv_iff(p@);
    }
    // 1.
    let target: &ExecElem = match ov {
        Some(e) => e,
        None => current_node_exec(p),
    };
    proof {
        assert(elem_ok(p@.doc, target@));
    }
    // 3.
    let (tp, rc, tpt) = if p.foster && is_table_like_exec(target) {
        let ghost f = |e: Elem| is_html(e, Tag::Template) || is_html(e, Tag::Table);
        // 3.1
        match last_index_where_exec(p.open.as_slice(), p.open.len(), &ElemPred::TemplateOrTable, Ghost(f)) {
            None => {
                // 3.2
                let first = open_at(p, 0);
                proof {
                    assert(elem_ok(p@.doc, first@));
                }
                (first.id, None, false)
            },
            Some(i) => {
                let last = open_at(p, i);
                proof {
                    lemma_last_index_where(p@.open, p@.open.len() as int, f);
                    assert(elem_ok(p@.doc, last@));
                }
                if is_html_ns(last) && matches!(last.tag, Tag::Template) {
                    // 3.3
                    (last.id, None, true)
                } else {
                    let t = last.id;
                    match p.arena.parent(t) {
                        // 3.4
                        Some(par) => {
                            proof {
                                lemma_wf_parent(p@.doc, t);
                            }
                            (par, Some(t), node_is_template_exec(&p.arena, par))
                        },
                        // 3.5
                        None => {
                            let above = open_at(p, i.saturating_sub(1));
                            proof {
                                assert(i > 0);
                                assert(elem_ok(p@.doc, above@));
                            }
                            (above.id, None, is_html_ns(above) && matches!(above.tag, Tag::Template))
                        },
                    }
                }
            },
        }
    } else {
        (target.id, None, is_html_ns(target) && matches!(target.tag, Tag::Template))
    };
    if !tpt {
        // 4.
        Location { parent: tp, child: rc }
    } else {
        // 5., 6.
        proof {
            lemma_wf_contents(p@.doc, tp);
        }
        Location { parent: template_contents_exec(&p.arena, tp), child: None }
    }
}

/// §13.2.6.1 "adjusted insertion location" ([`adjusted_location`]).
pub fn adjusted_location_exec(p: &ParserBuf, loc: Option<Location>) -> (r: Location)
    requires
        parser_inv(p@),
        match loc {
            Some(l) => loc_ok(p@.doc, l),
            None => stack_rooted(p@),
        },
    ensures
        r == adjusted_location(p@, loc),
        loc_ok(p@.doc, r),
{
    // 1.
    let location = match loc {
        Some(l) => l,
        None => appropriate_place_exec(p, None),
    };
    match p.redirect {
        // 5.
        Some((key, frag)) if key == location.parent => {
            proof {
                lemma_inv_iff(p@);
            }
            Location { parent: frag, child: None }
        },
        // 3.
        _ => location,
    }
}

// ---------------------------------------------------------------------
// Creating an element for a token

/// [`is_form_associated`].
pub fn is_form_associated_exec(ns: &Namespace, t: &Tag) -> (r: bool)
    ensures
        r == is_form_associated(*ns, *t),
{
    matches!(ns, Namespace::Html) && matches!(
        t,
        Tag::Button | Tag::Fieldset | Tag::Input | Tag::Object | Tag::Output | Tag::Select | Tag::Textarea | Tag::Img
    )
}

/// [`is_listed`].
pub fn is_listed_exec(ns: &Namespace, t: &Tag) -> (r: bool)
    ensures
        r == is_listed(*ns, *t),
{
    matches!(ns, Namespace::Html) && matches!(
        t,
        Tag::Button | Tag::Fieldset | Tag::Input | Tag::Object | Tag::Output | Tag::Select | Tag::Textarea
    )
}

/// The root of `n` ([`root_within`] with the arena's length as fuel),
/// walking parents in a loop.
pub fn root_exec(a: &Arena, n: usize) -> (r: usize)
    requires
        dom::wf(a@),
        dom::valid(a@, n),
    ensures
        r == root_within(a@, n, a@.nodes.len()),
{
    let fuel = a.len();
    let mut cur = n;
    let mut steps: usize = 0;
    while steps < fuel
        invariant
            dom::wf(a@),
            fuel == a@.nodes.len(),
            dom::valid(a@, cur),
            steps <= fuel,
            root_within(a@, n, fuel as nat) == root_within(a@, cur, (fuel - steps) as nat),
        decreases fuel - steps,
    {
        match a.parent(cur) {
            None => return cur,
            Some(par) => {
                proof {
                    lemma_wf_parent(a@, cur);
                }
                cur = par;
            },
        }
        // Never saturates: steps < fuel.
        steps = steps.saturating_add(1);
    }
    cur
}

/// [`same_tree`].
pub fn same_tree_exec(a: &Arena, x: usize, y: usize) -> (r: bool)
    requires
        dom::wf(a@),
        dom::valid(a@, x),
        dom::valid(a@, y),
    ensures
        r == same_tree(a@, x, y),
{
    root_exec(a, x) == root_exec(a, y)
}

/// [`attr_value`]: the value of the first attribute with no namespace named
/// `name`.
pub fn attr_value_exec<'a>(attrs: &'a [ExecAttr], name: &[u32]) -> (r: Option<&'a Vec<u32>>)
    ensures
        match r {
            Some(v) => attr_value(clazel_dom::exec::attrs_view(attrs@), name@) == Some(v@),
            None => attr_value(clazel_dom::exec::attrs_view(attrs@), name@) is None,
        },
{
    let ghost av = clazel_dom::exec::attrs_view(attrs@);
    let n = attrs.len();
    let mut i: usize = 0;
    proof {
        assert(av.subrange(0, n as int) =~= av);
    }
    while i < n
        invariant
            n == attrs@.len(),
            av == clazel_dom::exec::attrs_view(attrs@),
            i <= n,
            attr_value(av, name@) == attr_value(av.subrange(i as int, n as int), name@),
        decreases n - i,
    {
        let a = match attrs.get(i) {
            Some(a) => a,
            None => vstd::pervasive::unreached(),
        };
        proof {
            let s = av.subrange(i as int, n as int);
            assert(s[0] == a@);
            assert(s.drop_first() =~= av.subrange(i as int + 1, n as int));
        }
        if a.namespace.is_none() && u32s_eq(a.local_name.as_slice(), name) {
            return Some(&a.value);
        }
        // Never saturates: i < n.
        i = i.saturating_add(1);
    }
    proof {
        assert(av.subrange(n as int, n as int).len() == 0);
    }
    None
}

/// [`ascii_lower`].
pub fn ascii_lower_exec(c: u32) -> (r: u32)
    ensures
        r == ascii_lower(c),
{
    match c {
        // Never saturates: c <= 0x5A.
        0x41..=0x5A => c.saturating_add(0x20),
        _ => c,
    }
}

/// [`ascii_ci_eq`].
pub fn ascii_ci_eq_exec(a: &[u32], b: &[u32]) -> (r: bool)
    ensures
        r == ascii_ci_eq(a@, b@),
{
    if a.len() != b.len() {
        proof {
            assert(ascii_lowercase(a@).len() != ascii_lowercase(b@).len());
        }
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> ascii_lower(#[trigger] a@[j]) == ascii_lower(b@[j]),
        decreases a.len() - i,
    {
        let (x, y) = match (a.get(i), b.get(i)) {
            (Some(x), Some(y)) => (*x, *y),
            _ => vstd::pervasive::unreached(),
        };
        if ascii_lower_exec(x) != ascii_lower_exec(y) {
            proof {
                assert(ascii_lowercase(a@)[i as int] != ascii_lowercase(b@)[i as int]);
            }
            return false;
        }
        // Never saturates: i < a.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(ascii_lowercase(a@) =~= ascii_lowercase(b@));
    }
    true
}

/// [`annotation_html`].
pub fn annotation_html_exec(ns: &Namespace, t: &ExecTagTok) -> (r: bool)
    ensures
        r == annotation_html(*ns, t@),
{
    if !(matches!(ns, Namespace::MathMl) && matches!(t.tag, Tag::AnnotationXml)) {
        return false;
    }
    let encoding: &[u32] = &[0x65u32, 0x6e, 0x63, 0x6f, 0x64, 0x69, 0x6e, 0x67];
    let text_html: &[u32] = &[0x74u32, 0x65, 0x78, 0x74, 0x2f, 0x68, 0x74, 0x6d, 0x6c];
    let xhtml: &[u32] = &[
        0x61u32,
        0x70,
        0x70,
        0x6c,
        0x69,
        0x63,
        0x61,
        0x74,
        0x69,
        0x6f,
        0x6e,
        0x2f,
        0x78,
        0x68,
        0x74,
        0x6d,
        0x6c,
        0x2b,
        0x78,
        0x6d,
        0x6c,
    ];
    proof {
        assert(encoding@ =~= seq![0x65u32, 0x6e, 0x63, 0x6f, 0x64, 0x69, 0x6e, 0x67]);
        assert(text_html@ =~= seq![0x74u32, 0x65, 0x78, 0x74, 0x2f, 0x68, 0x74, 0x6d, 0x6c]);
        assert(xhtml@ =~= seq![
            0x61u32,
            0x70,
            0x70,
            0x6c,
            0x69,
            0x63,
            0x61,
            0x74,
            0x69,
            0x6f,
            0x6e,
            0x2f,
            0x78,
            0x68,
            0x74,
            0x6d,
            0x6c,
            0x2b,
            0x78,
            0x6d,
            0x6c,
        ]);
    }
    match attr_value_exec(t.attrs.as_slice(), encoding) {
        Some(v) => ascii_ci_eq_exec(v.as_slice(), text_html) || ascii_ci_eq_exec(v.as_slice(), xhtml),
        None => false,
    }
}

/// [`has_attr`].
pub fn has_attr_exec(t: &ExecTagTok, name: &[u32]) -> (r: bool)
    ensures
        r == has_attr(t@, name@),
{
    attr_value_exec(t.attrs.as_slice(), name).is_some()
}

/// The form owner step 21 of "create an element for a token" computes.
fn form_owner_exec(p: &ParserBuf, t: &ExecTagTok, ns: &Namespace, intended_parent: usize) -> (r: Option<usize>)
    requires
        parser_inv(p@),
        dom::valid(p@.doc, intended_parent),
    ensures
        r == (if is_form_associated(*ns, t@.tag) && p@.form is Some && !parsing_template_contents(p@) && p@.context is None
            && (!is_listed(*ns, t@.tag) || !has_attr(t@, name_form())) && same_tree(p@.doc, intended_parent, p@.form->Some_0) {
            p@.form
        } else {
            None
        }),
{
    let form = p.form?;
    if !is_form_associated_exec(ns, &t.tag) || parsing_template_contents_exec(p) || p.context.is_some() {
        return None;
    }
    let form_name: &[u32] = &[0x66u32, 0x6f, 0x72, 0x6d];
    proof {
        assert(form_name@ =~= name_form());
    }
    if is_listed_exec(ns, &t.tag) && has_attr_exec(t, form_name) {
        return None;
    }
    proof {
        lemma_inv_iff(p@);
    }
    if same_tree_exec(&p.arena, intended_parent, form) {
        Some(form)
    } else {
        None
    }
}

/// §13.2.6.1 "create an element for a token" ([`create_element_for_token`]).
#[verifier::rlimit(60)]
pub fn create_element_for_token_exec(p: &mut ParserBuf, t: &ExecTagTok, ns: Namespace, intended_parent: usize) -> (r:
    ExecElem)
    requires
        parser_inv(old(p)@),
        tok_tagged(t@),
        dom::valid(old(p)@.doc, intended_parent),
    ensures
        (final(p)@, r@) == create_element_for_token(old(p)@, t@, ns, intended_parent),
        parser_inv(final(p)@),
        !final(p)@.stopped ==> elem_ok(final(p)@.doc, r@),
        same_but_tree(old(p)@, final(p)@),
        !final(p)@.stopped ==> final(p)@.open == old(p)@.open,
        r@.tag == t@.tag && r@.ns == ns,
{
    let ghost p0 = p@;
    let annotation = annotation_html_exec(&ns, t);
    if p.stopped {
        return ExecElem { id: 0, ns, tag: copy_tag(&t.tag), name: copy_str(t.name.as_slice()), annotation_html: annotation };
    }
    // 21.
    let owner = form_owner_exec(p, t, &ns, intended_parent);
    // 15., 17.
    let kind = ExecKind::Element {
        namespace: Some(copy_ns(&ns)),
        prefix: None,
        local_name: copy_str(t.name.as_slice()),
        attributes: copy_attrs(t.attrs.as_slice()),
        template_contents: None,
        form_owner: owner,
    };
    proof {
        lemma_inv_iff(p0);
    }
    let id = create_exec(p, kind);
    let ghost p1 = p@;
    let template = matches!(ns, Namespace::Html) && matches!(t.tag, Tag::Template);
    if template && !p.stopped {
        proof {
            lemma_inv_iff(p1);
        }
        let ghost d1 = p@.doc;
        match p.arena.create_template_contents(id) {
            Some(_) => {
                proof {
                    lemma_create_template_contents_extends(d1, id);
                    lemma_inv_doc(p1, p@.doc);
                    clazel_dom::lemmas::theorem_create_template_contents_wf(d1, id);
                }
            },
            None => {
                stop_parsing_exec(p);
            },
        }
    }
    ExecElem { id, ns, tag: copy_tag(&t.tag), name: copy_str(t.name.as_slice()), annotation_html: annotation }
}

// ---------------------------------------------------------------------
// Inserting elements

/// [`has_element_child`].
pub fn has_element_child_exec(a: &Arena, n: usize) -> (r: bool)
    requires
        dom::wf(a@),
        dom::valid(a@, n),
    ensures
        r == has_element_child(a@, n),
{
    let kids = a.children(n);
    let mut j: usize = 0;
    while j < kids.len()
        invariant
            dom::wf(a@),
            dom::valid(a@, n),
            kids@ == a@.nodes[n as int].children,
            j <= kids@.len(),
            forall|q: int|
                0 <= q < j ==> !(dom::valid(a@, #[trigger] kids@[q]) && a@.nodes[kids@[q] as int].kind is Element),
        decreases kids@.len() - j,
    {
        let c = match kids.get(j) {
            Some(c) => *c,
            None => vstd::pervasive::unreached(),
        };
        proof {
            lemma_wf_child(a@, n, j as int);
        }
        if matches!(a.kind(c), ExecKind::Element { .. }) {
            return true;
        }
        // Never saturates: j < kids.len().
        j = j.saturating_add(1);
    }
    false
}

/// §13.2.6.1 "insert an element at the adjusted insertion location"
/// ([`insert_element_at`]).
pub fn insert_element_at_exec(p: &mut ParserBuf, el: usize, override_loc: Option<Location>)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped ==> dom::valid(old(p)@.doc, el),
        !old(p)@.stopped ==> match override_loc {
            Some(l) => loc_ok(old(p)@.doc, l),
            None => stack_rooted(old(p)@),
        },
    ensures
        final(p)@ == insert_element_at(old(p)@, el, override_loc),
        parser_inv(final(p)@),
        doc_extends(old(p)@.doc, final(p)@.doc),
        final(p)@ == (Parser { doc: final(p)@.doc, ..old(p)@ }),
{
    proof {
        lemma_inv_iff(old(p)@);
        assert(doc_extends(p@.doc, p@.doc)) by {
            assert forall|i: int| 0 <= i < p@.doc.nodes.len() implies kind_kept(
                p@.doc.nodes[i].kind,
                #[trigger] p@.doc.nodes[i].kind,
            ) by {}
        }
    }
    if p.stopped {
        return ;
    }
    // 1.
    let loc = adjusted_location_exec(p, override_loc);
    // 2.
    if p.arena.parent(el).is_some() || p.arena.is_inclusive_ancestor(el, loc.parent) || (matches!(
        p.arena.kind(loc.parent),
        ExecKind::Document { .. }
    ) && has_element_child_exec(&p.arena, loc.parent)) {
        return ;
    }
    // 6.
    dom_insert_exec(p, el, loc.parent, loc.child);
}

/// §13.2.6.1 "insert a foreign element" ([`insert_foreign_element`]): a
/// `template` element needs a spare template insertion mode (push the
/// mode first; `insert_foreign_element` does not read the stack of template
/// insertion modes).
pub fn insert_foreign_element_exec(p: &mut ParserBuf, t: &ExecTagTok, ns: Namespace) -> (r: ExecElem)
    requires
        parser_inv(old(p)@),
        tok_tagged(t@),
        old(p)@.stopped || stack_rooted(old(p)@),
        ns == Namespace::Html && t@.tag == Tag::Template ==> crate::termination::template_count(old(p)@)
            < old(p)@.template_modes.len(),
    ensures
        (final(p)@, r@) == insert_foreign_element(old(p)@, t@, ns),
        parser_inv(final(p)@),
        same_but_tree(old(p)@, final(p)@),
        !final(p)@.stopped ==> final(p)@.open == old(p)@.open.push(r@),
{
    proof {
        lemma_wf_nonempty(old(p)@.doc);
    }
    if p.stopped {
        return create_element_for_token_exec(p, t, ns, 0);
    }
    // 1.
    let place = appropriate_place_exec(p, None);
    let ghost p0 = p@;
    let e = create_element_for_token_exec(p, t, ns, place.parent);
    // 2.
    let ghost p1 = p@;
    insert_element_at_exec(p, e.id, None);
    // 3.
    let ghost p2 = p@;
    let r = copy_elem(&e);
    proof {
        if !p2.stopped {
            lemma_elem_ok_extends(p1.doc, p2.doc, e@);
        }
    }
    push_exec(p, e);
    r
}

/// §13.2.6.1 "insert an HTML element" ([`insert_html_element`]).
pub fn insert_html_element_exec(p: &mut ParserBuf, t: &ExecTagTok) -> (r: ExecElem)
    requires
        parser_inv(old(p)@),
        tok_tagged(t@),
        old(p)@.stopped || stack_rooted(old(p)@),
        t@.tag == Tag::Template ==> crate::termination::template_count(old(p)@) < old(p)@.template_modes.len(),
    ensures
        (final(p)@, r@) == insert_html_element(old(p)@, t@),
        parser_inv(final(p)@),
        same_but_tree(old(p)@, final(p)@),
        !final(p)@.stopped ==> final(p)@.open == old(p)@.open.push(r@),
{
    insert_foreign_element_exec(p, t, Namespace::Html)
}

// ---------------------------------------------------------------------
// Attribute adjustments (§13.2.6.1), in place

/// A placeholder attribute (no allocation), to swap one out of a list.
fn placeholder_attr() -> (r: ExecAttr) {
    ExecAttr { namespace: None, prefix: None, local_name: Vec::new(), value: Vec::new() }
}

/// "adjust MathML attributes for a token" ([`adjust_mathml_attributes`]).
pub fn adjust_mathml_attributes_exec(t: &mut ExecTagTok)
    ensures
        final(t)@ == adjust_mathml_attributes(old(t)@),
{
    let ghost t0 = t@;
    let ghost a0 = t.attrs@;
    let from: &[u32] = &[0x64u32, 0x65, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x69, 0x6f, 0x6e, 0x75, 0x72, 0x6c];
    proof {
        assert(from@ =~= name_definitionurl());
    }
    let n = t.attrs.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == t.attrs@.len(),
            n == a0.len(),
            i <= n,
            from@ == name_definitionurl(),
            t.name@ == t0.name,
            t.tag == t0.tag,
            t.self_closing == t0.self_closing,
            t0 == old(t)@,
            t0.attrs == clazel_dom::exec::attrs_view(a0),
            forall|j: int| 0 <= j < i ==> (#[trigger] t.attrs@[j])@ == adjust_mathml_attributes(t0).attrs[j],
            forall|j: int| i <= j < n ==> #[trigger] t.attrs@[j] == a0[j],
        decreases n - i,
    {
        let mut a = placeholder_attr();
        t.attrs.set_and_swap(i, &mut a);
        if a.namespace.is_none() && u32s_eq(a.local_name.as_slice(), from) {
            let v = vec![0x64u32, 0x65, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x69, 0x6f, 0x6e, 0x55, 0x52, 0x4c];
            proof {
                assert(v@ =~= name_definition_url());
            }
            a.local_name = v;
        }
        t.attrs.set(i, a);
        // Never saturates: i < n.
        i = i.saturating_add(1);
    }
    proof {
        assert(clazel_dom::exec::attrs_view(t.attrs@) =~= adjust_mathml_attributes(t0).attrs);
    }
}

/// "adjust SVG attributes for a token" ([`adjust_svg_attributes`]).
pub fn adjust_svg_attributes_exec(t: &mut ExecTagTok)
    ensures
        final(t)@ == adjust_svg_attributes(old(t)@),
{
    let ghost t0 = t@;
    let ghost a0 = t.attrs@;
    let n = t.attrs.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == t.attrs@.len(),
            n == a0.len(),
            i <= n,
            t.name@ == t0.name,
            t.tag == t0.tag,
            t.self_closing == t0.self_closing,
            t0 == old(t)@,
            t0.attrs == clazel_dom::exec::attrs_view(a0),
            forall|j: int| 0 <= j < i ==> (#[trigger] t.attrs@[j])@ == adjust_svg_attributes(t0).attrs[j],
            forall|j: int| i <= j < n ==> #[trigger] t.attrs@[j] == a0[j],
        decreases n - i,
    {
        let mut a = placeholder_attr();
        t.attrs.set_and_swap(i, &mut a);
        let mapped = if a.namespace.is_none() {
            svg_attribute_name_exec(a.local_name.as_slice())
        } else {
            None
        };
        if let Some(v) = mapped {
            a.local_name = v;
        }
        t.attrs.set(i, a);
        // Never saturates: i < n.
        i = i.saturating_add(1);
    }
    proof {
        assert(clazel_dom::exec::attrs_view(t.attrs@) =~= adjust_svg_attributes(t0).attrs);
    }
}

/// "adjust foreign attributes for a token" ([`adjust_foreign_attributes`]).
pub fn adjust_foreign_attributes_exec(t: &mut ExecTagTok)
    ensures
        final(t)@ == adjust_foreign_attributes(old(t)@),
{
    let ghost t0 = t@;
    let ghost a0 = t.attrs@;
    let n = t.attrs.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == t.attrs@.len(),
            n == a0.len(),
            i <= n,
            t.name@ == t0.name,
            t.tag == t0.tag,
            t.self_closing == t0.self_closing,
            t0 == old(t)@,
            t0.attrs == clazel_dom::exec::attrs_view(a0),
            forall|j: int| 0 <= j < i ==> (#[trigger] t.attrs@[j])@ == adjust_foreign_attributes(t0).attrs[j],
            forall|j: int| i <= j < n ==> #[trigger] t.attrs@[j] == a0[j],
        decreases n - i,
    {
        let mut a = placeholder_attr();
        t.attrs.set_and_swap(i, &mut a);
        let row = if a.namespace.is_none() {
            foreign_attribute_exec(a.local_name.as_slice())
        } else {
            None
        };
        if let Some((prefix, local, ns)) = row {
            a = ExecAttr { namespace: Some(ns), prefix, local_name: local, value: a.value };
        }
        t.attrs.set(i, a);
        // Never saturates: i < n.
        i = i.saturating_add(1);
    }
    proof {
        assert(clazel_dom::exec::attrs_view(t.attrs@) =~= adjust_foreign_attributes(t0).attrs);
    }
}

// ---------------------------------------------------------------------
// Inserting characters, comments and processing instructions

/// The insertion location (the Document object, null)
/// ([`document_location`]).
pub fn document_location_exec() -> (r: Location)
    ensures
        r == document_location(),
{
    Location { parent: 0, child: None }
}

/// (The Document object, null) is [`loc_ok`].
pub proof fn lemma_document_location_ok(p: Parser)
    requires
        parser_inv(p),
    ensures
        loc_ok(p.doc, document_location()),
{
    lemma_inv_iff(p);
    lemma_wf_nonempty(p.doc);
}

/// Create a node of kind `k` and insert it at `l` (the last two steps of
/// "insert a character", "insert a comment" and "insert a processing
/// instruction").
pub open spec fn create_insert(p: Parser, k: NodeKind, l: Location) -> Parser {
    let (p1, n) = create(p, k);
    dom_insert(p1, n, l.parent, l.child)
}

/// [`create_insert`].
pub fn create_insert_exec(p: &mut ParserBuf, k: ExecKind, l: Location)
    requires
        parser_inv(old(p)@),
        dom::creatable(old(p)@.doc, k@),
        loc_ok(old(p)@.doc, l),
    ensures
        final(p)@ == create_insert(old(p)@, k@, l),
        parser_inv(final(p)@),
        same_but_tree(old(p)@, final(p)@),
{
    let ghost p0 = p@;
    let n = create_exec(p, k);
    proof {
        lemma_loc_ok_extends(p0.doc, p@.doc, l);
    }
    dom_insert_exec(p, n, l.parent, l.child);
}

/// "insert a character" from step 3, at the location `loc` step 2 gave.
pub open spec fn chars_at(p: Parser, data: Seq<u32>, loc: Location) -> Parser {
    let doc = p.doc;
    if p.stopped || doc.nodes[loc.parent as int].kind is Document {
        p
    } else {
        let prev = match loc.child {
            Some(c) => dom::previous_sibling(doc, c),
            None => dom::last_child(doc, loc.parent),
        };
        match prev {
            Some(s) if dom::valid(doc, s) && doc.nodes[s as int].kind is Text => Parser { doc: dom::append_data(doc, s, data), ..p },
            _ => create_insert(p, NodeKind::Text { data }, loc),
        }
    }
}

/// [`insert_characters`] is [`chars_at`] the adjusted insertion location.
proof fn lemma_chars_at(p: Parser, data: Seq<u32>)
    ensures
        insert_characters(p, data) == chars_at(p, data, adjusted_location(p, None)),
{
}

/// [`chars_at`].
fn chars_at_exec(p: &mut ParserBuf, data: &[u32], loc: Location)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        loc_ok(old(p)@.doc, loc),
    ensures
        final(p)@ == chars_at(old(p)@, data@, loc),
        parser_inv(final(p)@),
        same_but_tree(old(p)@, final(p)@),
{
    // 3.
    if matches!(p.arena.kind(loc.parent), ExecKind::Document { .. }) {
        return ;
    }
    proof {
        lemma_inv_iff(old(p)@);
    }
    // 4.
    let prev = match loc.child {
        Some(c) => p.arena.previous_sibling(c),
        None => p.arena.last_child(loc.parent),
    };
    // 5.
    let text_prev = match prev {
        Some(s) if s < p.arena.len() && matches!(p.arena.kind(s), ExecKind::Text { .. }) => Some(s),
        _ => None,
    };
    if let Some(s) = text_prev {
        proof {
            lemma_append_data_extends(old(p)@.doc, s, data@);
        }
        p.arena.append_data(s, data);
        proof {
            lemma_inv_doc(old(p)@, p@.doc);
        }
        return ;
    }
    create_insert_exec(p, ExecKind::Text { data: copy_str(data) }, loc);
}

/// §13.2.6.1 "insert a character" with the characters `data`
/// ([`insert_characters`]).
pub fn insert_characters_exec(p: &mut ParserBuf, data: &[u32])
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
    ensures
        final(p)@ == insert_characters(old(p)@, data@),
        parser_inv(final(p)@),
        same_but_tree(old(p)@, final(p)@),
{
    proof {
        lemma_chars_at(old(p)@, data@);
    }
    if p.stopped {
        return ;
    }
    // 2.
    let loc = adjusted_location_exec(p, None);
    chars_at_exec(p, data, loc);
}

/// "insert a character" for one character ([`insert_char`]).
pub fn insert_char_exec(p: &mut ParserBuf, c: u32)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
    ensures
        final(p)@ == insert_char(old(p)@, c),
        parser_inv(final(p)@),
        same_but_tree(old(p)@, final(p)@),
{
    let a = [c];
    proof {
        assert(a@ =~= seq![c]);
    }
    insert_characters_exec(p, a.as_slice());
}

/// §13.2.6.1 "insert a comment" ([`insert_comment`]), moving `data`.
pub fn insert_comment_exec(p: &mut ParserBuf, data: Vec<u32>, loc: Option<Location>)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || match loc {
            Some(l) => loc_ok(old(p)@.doc, l),
            None => stack_rooted(old(p)@),
        },
    ensures
        final(p)@ == insert_comment(old(p)@, data@, loc),
        parser_inv(final(p)@),
        same_but_tree(old(p)@, final(p)@),
{
    if p.stopped {
        return ;
    }
    // 3.
    let l = adjusted_location_exec(p, loc);
    let ghost p0 = p@;
    // 4.
    let c = create_exec(p, ExecKind::Comment { data });
    proof {
        lemma_loc_ok_extends(p0.doc, p@.doc, l);
    }
    // 5.
    dom_insert_exec(p, c, l.parent, l.child);
}

/// §13.2.6.1 "insert a processing instruction" ([`insert_pi`]), moving
/// `target` and `data`.
pub fn insert_pi_exec(p: &mut ParserBuf, target: Vec<u32>, data: Vec<u32>, loc: Option<Location>)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || match loc {
            Some(l) => loc_ok(old(p)@.doc, l),
            None => stack_rooted(old(p)@),
        },
    ensures
        final(p)@ == insert_pi(old(p)@, target@, data@, loc),
        parser_inv(final(p)@),
        same_but_tree(old(p)@, final(p)@),
{
    if p.stopped {
        return ;
    }
    // 4.
    let l = adjusted_location_exec(p, loc);
    let ghost p0 = p@;
    // 5.
    let n = create_exec(p, ExecKind::ProcessingInstruction { target, data });
    proof {
        lemma_loc_ok_extends(p0.doc, p@.doc, l);
    }
    // 6.
    dom_insert_exec(p, n, l.parent, l.child);
}

// ---------------------------------------------------------------------
// §13.2.6.2 and §13.2.6.3

/// §13.2.6.2 the generic raw text (`rawtext`) or RCDATA element parsing
/// algorithm ([`generic_text_parsing`]). The current mode must not be
/// "text" or "in table text" (it becomes the original insertion mode).
pub fn generic_text_parsing_exec(p: &mut ParserBuf, t: &ExecTagTok, rawtext: bool)
    requires
        parser_inv(old(p)@),
        tok_tagged(t@),
        old(p)@.stopped || stack_rooted(old(p)@),
        t@.tag == Tag::Template ==> crate::termination::template_count(old(p)@) < old(p)@.template_modes.len(),
        old(p)@.mode != Mode::Text && old(p)@.mode != Mode::InTableText,
    ensures
        final(p)@ == generic_text_parsing(old(p)@, t@, rawtext),
        parser_inv(final(p)@),
{
    // 1.
    let _ = insert_html_element_exec(p, t);
    proof {
        lemma_inv_iff(old(p)@);
        lemma_inv_iff(p@);
    }
    // 2.
    p.tokenizer = Some(
        if rawtext {
            TokenizerState::Rawtext
        } else {
            TokenizerState::Rcdata
        },
    );
    // 3., 4.
    p.original_mode = copy_mode(&p.mode);
    p.mode = Mode::Text;
    proof {
        lemma_inv_iff(p@);
    }
}

/// "generate implied end tags", except for HTML elements named `except`
/// ([`generate_implied_end_tags`]).
pub fn generate_implied_end_tags_exec(p: &mut ParserBuf, except: Option<Tag>)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == generate_implied_end_tags(old(p)@, except),
        parser_inv(final(p)@),
{
    let ghost f = |e: Elem| implied_end_tag(e) && !(except is Some && e.tag == except->Some_0);
    let pr = ElemPred::ImpliedEnd(except);
    pop_while_exec(p, &pr, Ghost(f));
}

/// "generate all implied end tags thoroughly"
/// ([`generate_all_implied_end_tags_thoroughly`]).
pub fn generate_all_implied_end_tags_thoroughly_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == generate_all_implied_end_tags_thoroughly(old(p)@),
        parser_inv(final(p)@),
{
    let ghost f = |e: Elem|
        e.ns == Namespace::Html && match e.tag {
            Tag::Caption | Tag::Colgroup | Tag::Dd | Tag::Dt | Tag::Li | Tag::Optgroup | Tag::Option | Tag::P | Tag::Rb | Tag::Rp
            | Tag::Rt | Tag::Rtc | Tag::Tbody | Tag::Td | Tag::Tfoot | Tag::Th | Tag::Thead | Tag::Tr => true,
            _ => false,
        };
    pop_while_exec(p, &ElemPred::Thoroughly, Ghost(f));
}

// ---------------------------------------------------------------------
// §13.2.4.3 reconstruct the active formatting elements

/// The first entry to create ([`reconstruct_rewind`] from `n - 1`).
fn reconstruct_rewind_exec(p: &ParserBuf, n: usize) -> (r: usize)
    requires
        0 < n <= p@.formatting.len(),
    ensures
        r as int == reconstruct_rewind(p@, n - 1),
        r < n,
{
    let mut i: usize = n.saturating_sub(1);
    loop
        invariant
            0 < n <= p@.formatting.len(),
            i < n,
            reconstruct_rewind(p@, n - 1) == reconstruct_rewind(p@, i as int),
        decreases i,
    {
        // 4.
        if i == 0 {
            return 0;
        }
        // 5.
        let e = match p.formatting.get(i.saturating_sub(1)) {
            Some(e) => e,
            None => vstd::pervasive::unreached(),
        };
        // 6.
        if !matches!(e, ExecFmt::Marker) && !fmt_on_stack_exec(p, e) {
            i = i.saturating_sub(1);
        } else {
            return i;
        }
    }
}

/// [`reconstruct_create`], hidden so that the loop's context stays small.
#[verifier::opaque]
pub open spec fn rc(p: Parser, i: int) -> Parser {
    reconstruct_create(p, i)
}

/// One round of steps 8 to 10 of "reconstruct the active formatting
/// elements" at entry `i`: `true` to go on with entry `i + 1`.
fn reconstruct_step_exec(p: &mut ParserBuf, i: usize, n: usize) -> (cont: bool)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        n == old(p)@.formatting.len(),
        i < n,
    ensures
        parser_inv(final(p)@),
        final(p)@.stopped || stack_rooted(final(p)@),
        n == final(p)@.formatting.len(),
        cont ==> i + 1 < n && rc(final(p)@, i + 1) == rc(old(p)@, i as int),
        !cont ==> final(p)@ == rc(old(p)@, i as int),
{
    reveal(rc);
    if p.stopped {
        return false;
    }
    let token = match p.formatting.get(i) {
        Some(ExecFmt::Entry { token, .. }) => copy_tagtok(token),
        _ => return false,
    };
    let ghost p0 = p@;
    proof {
        lemma_inv_iff(p0);
        assert(fmt_ok(p0.doc, p0.formatting[i as int]));
    }
    // 8.
    let ne = insert_html_element_exec(p, &token);
    // 9.
    if !p.stopped {
        let ghost p1 = p@;
        let ghost v = p.formatting@;
        let ghost x = Fmt::Entry { elem: ne@, token: token@ };
        p.formatting.set(i, ExecFmt::Entry { elem: ne, token });
        proof {
            assert(fmts_view(p.formatting@) =~= fmts_view(v).update(i as int, x));
            lemma_inv_iff(p1);
            assert(elem_ok(p1.doc, p1.open[p1.open.len() - 1]));
            lemma_fmts_update(p1.doc, fmts_view(v), i as int, x);
            lemma_inv_iff(p@);
        }
    }
    // 10., 7.
    i.saturating_add(1) < n
}

/// §13.2.4.3 "reconstruct the active formatting elements"
/// ([`reconstruct_formatting`]).
pub fn reconstruct_formatting_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
    ensures
        final(p)@ == reconstruct_formatting(old(p)@),
        parser_inv(final(p)@),
{
    if p.stopped {
        return ;
    }
    let n = p.formatting.len();
    // 1.
    if n == 0 {
        return ;
    }
    // 2.
    let last = match p.formatting.get(n.saturating_sub(1)) {
        Some(e) => e,
        None => vstd::pervasive::unreached(),
    };
    if matches!(last, ExecFmt::Marker) || fmt_on_stack_exec(p, last) {
        return ;
    }
    // 3. to 6.
    let start = reconstruct_rewind_exec(p, n);
    // 7. to 10.
    reconstruct_loop_exec(p, start, n);
    proof {
        reveal(rc);
    }
}

/// Steps 7 to 10 from entry `start` ([`rc`]).
fn reconstruct_loop_exec(p: &mut ParserBuf, start: usize, n: usize)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        n == old(p)@.formatting.len(),
        start < n,
    ensures
        final(p)@ == rc(old(p)@, start as int),
        parser_inv(final(p)@),
{
    let mut i = start;
    loop
        invariant
            parser_inv(p@),
            p@.stopped || stack_rooted(p@),
            n == p@.formatting.len(),
            i < n,
            rc(p@, i as int) == rc(old(p)@, start as int),
        decreases n - i,
    {
        if !reconstruct_step_exec(p, i, n) {
            return ;
        }
        // Never saturates: i + 1 < n.
        i = i.saturating_add(1);
    }
}
} // verus!
