//! The equivalence lemmas for "in body" (W3C §8.2.5.4.7, WHATWG
//! §13.2.6.4.7), with the adoption agency algorithm, "in table"
//! (§8.2.5.4.9, §13.2.6.4.9) and "in table text" (§8.2.5.4.10,
//! §13.2.6.4.10). As in [`super::equivalence`], each lemma's precondition
//! excludes exactly the inputs where the two documents differ, says why,
//! and states the facts of reachable states it relies on; the WHATWG text
//! (which [`crate::spec`] follows) is the one the parser implements.

#[cfg(verus_only)]
use super::equivalence::{lemma_in_head, place_stable};
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

broadcast use super::equivalence::group_w3c_state;

// ---------------------------------------------------------------------
// Tags and names

/// The tags whose entries the WHATWG transcription matches by name and the
/// W3C one by [`Tag`]: the end tags "address", …, "ul", "dd", "dt",
/// "applet", "marquee", "object", the formatting tags (the adoption agency
/// algorithm's subject) and "br".
pub open spec fn named_tag(g: Tag) -> bool {
    w3c_block_end_tag(g) || g == Tag::Dd || g == Tag::Dt || g == Tag::Applet || g == Tag::Marquee || g == Tag::Object
        || w3c_formatting_end_tag(g) || g == Tag::Br
}

/// Only one name has each [`named_tag`] (first part).
proof fn lemma_named_tags_injective_1()
    ensures
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Address ==> n == seq![0x61u32, 0x64, 0x64, 0x72, 0x65, 0x73, 0x73],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Article ==> n == seq![0x61u32, 0x72, 0x74, 0x69, 0x63, 0x6c, 0x65],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Aside ==> n == seq![0x61u32, 0x73, 0x69, 0x64, 0x65],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Blockquote ==> n == seq![0x62u32, 0x6c, 0x6f, 0x63, 0x6b, 0x71, 0x75, 0x6f, 0x74, 0x65],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Button ==> n == seq![0x62u32, 0x75, 0x74, 0x74, 0x6f, 0x6e],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Center ==> n == seq![0x63u32, 0x65, 0x6e, 0x74, 0x65, 0x72],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Details ==> n == seq![0x64u32, 0x65, 0x74, 0x61, 0x69, 0x6c, 0x73],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Dialog ==> n == seq![0x64u32, 0x69, 0x61, 0x6c, 0x6f, 0x67],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Dir ==> n == seq![0x64u32, 0x69, 0x72],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Div ==> n == seq![0x64u32, 0x69, 0x76],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Dl ==> n == seq![0x64u32, 0x6c],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Fieldset ==> n == seq![0x66u32, 0x69, 0x65, 0x6c, 0x64, 0x73, 0x65, 0x74],
{
}

/// Only one name has each [`named_tag`] (second part).
proof fn lemma_named_tags_injective_2()
    ensures
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Figcaption ==> n == seq![0x66u32, 0x69, 0x67, 0x63, 0x61, 0x70, 0x74, 0x69, 0x6f, 0x6e],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Figure ==> n == seq![0x66u32, 0x69, 0x67, 0x75, 0x72, 0x65],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Footer ==> n == seq![0x66u32, 0x6f, 0x6f, 0x74, 0x65, 0x72],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Header ==> n == seq![0x68u32, 0x65, 0x61, 0x64, 0x65, 0x72],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Listing ==> n == seq![0x6cu32, 0x69, 0x73, 0x74, 0x69, 0x6e, 0x67],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Main ==> n == seq![0x6du32, 0x61, 0x69, 0x6e],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Nav ==> n == seq![0x6eu32, 0x61, 0x76],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Ol ==> n == seq![0x6fu32, 0x6c],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Pre ==> n == seq![0x70u32, 0x72, 0x65],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Section ==> n == seq![0x73u32, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Summary ==> n == seq![0x73u32, 0x75, 0x6d, 0x6d, 0x61, 0x72, 0x79],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Ul ==> n == seq![0x75u32, 0x6c],
{
}

/// Only one name has each [`named_tag`] (third part).
proof fn lemma_named_tags_injective_3()
    ensures
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Dd ==> n == seq![0x64u32, 0x64],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Dt ==> n == seq![0x64u32, 0x74],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Applet ==> n == seq![0x61u32, 0x70, 0x70, 0x6c, 0x65, 0x74],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Marquee ==> n == seq![0x6du32, 0x61, 0x72, 0x71, 0x75, 0x65, 0x65],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Object ==> n == seq![0x6fu32, 0x62, 0x6a, 0x65, 0x63, 0x74],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Br ==> n == seq![0x62u32, 0x72],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::A ==> n == seq![0x61u32],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::B ==> n == seq![0x62u32],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Big ==> n == seq![0x62u32, 0x69, 0x67],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Code ==> n == seq![0x63u32, 0x6f, 0x64, 0x65],
{
}

/// Only one name has each [`named_tag`] (fourth part).
proof fn lemma_named_tags_injective_4()
    ensures
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Em ==> n == seq![0x65u32, 0x6d],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Font ==> n == seq![0x66u32, 0x6f, 0x6e, 0x74],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::I ==> n == seq![0x69u32],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Nobr ==> n == seq![0x6eu32, 0x6f, 0x62, 0x72],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::S ==> n == seq![0x73u32],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Small ==> n == seq![0x73u32, 0x6d, 0x61, 0x6c, 0x6c],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Strike ==> n == seq![0x73u32, 0x74, 0x72, 0x69, 0x6b, 0x65],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Strong ==> n == seq![0x73u32, 0x74, 0x72, 0x6f, 0x6e, 0x67],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::Tt ==> n == seq![0x74u32, 0x74],
        forall|n: Seq<u32>| #[trigger] tag_of(n) == Tag::U ==> n == seq![0x75u32],
{
}

/// Two names with the same [`named_tag`] are the same name.
pub proof fn lemma_named_tag_names(a: Seq<u32>, b: Seq<u32>)
    requires
        named_tag(tag_of(a)),
        tag_of(a) == tag_of(b),
    ensures
        a == b,
{
    lemma_named_tags_injective_1();
    lemma_named_tags_injective_2();
    lemma_named_tags_injective_3();
    lemma_named_tags_injective_4();
}

/// For a tagged record and a tagged token with a [`named_tag`], "an HTML
/// element with the same tag name as the token" is the same whether names
/// (the WHATWG transcription) or tags (the W3C one) are compared.
pub proof fn lemma_same_name_same_tag(e: Elem, tt: TagTok)
    requires
        elem_tagged(e),
        tok_tagged(tt),
        named_tag(tt.tag),
    ensures
        is_html_named(e, tt.name) == is_html(e, tt.tag),
        (e.name == tt.name) == (e.tag == tt.tag),
{
    if e.tag == tt.tag {
        lemma_named_tag_names(tt.name, e.name);
    }
}

// ---------------------------------------------------------------------
// The stack

/// Every record of `o` is tagged by its name.
pub open spec fn all_tagged(o: Seq<Elem>) -> bool {
    forall|j: int| 0 <= j < o.len() ==> elem_tagged(#[trigger] o[j])
}

/// `pop_while` keeps a prefix of the stack and every other field.
pub proof fn lemma_pop_while_prefix(p: Parser, f: spec_fn(Elem) -> bool)
    ensures
        pop_while(p, f) == (Parser { open: pop_while(p, f).open, ..p }),
        pop_while(p, f).open.len() <= p.open.len(),
        forall|j: int| 0 <= j < pop_while(p, f).open.len() ==> #[trigger] pop_while(p, f).open[j] == p.open[j],
    decreases p.open.len(),
{
    if p.open.len() > 0 && f(current_node(p)) {
        lemma_pop_while_prefix(pop(p), f);
    }
}

/// [`all_tagged`] of the stack after "generate implied end tags".
pub proof fn lemma_implied_tagged(p: Parser, except: Option<Tag>)
    requires
        all_tagged(p.open),
    ensures
        all_tagged(generate_implied_end_tags(p, except).open),
        generate_implied_end_tags(p, except) == (Parser { open: generate_implied_end_tags(p, except).open, ..p }),
{
    lemma_pop_while_prefix(p, |e: Elem| implied_end_tag(e) && !(except is Some && e.tag == except->Some_0));
    let q = generate_implied_end_tags(p, except);
    assert forall|j: int| 0 <= j < q.open.len() implies elem_tagged(#[trigger] q.open[j]) by {
        assert(q.open[j] == p.open[j]);
    }
}

/// "Pop elements … until an HTML element with the same tag name as the
/// token has been popped": by name (WHATWG transcription) and by tag (W3C)
/// alike, on a tagged stack.
pub proof fn lemma_pop_until_named(q: Parser, tt: TagTok)
    requires
        tok_tagged(tt),
        named_tag(tt.tag),
        all_tagged(q.open),
    ensures
        pop_until_named_popped(q, tt.name) == pop_until_popped(q, tt.tag),
    decreases q.open.len(),
{
    if q.open.len() > 0 {
        lemma_same_name_same_tag(current_node(q), tt);
        if !is_html(current_node(q), tt.tag) {
            let r = pop(q);
            assert forall|j: int| 0 <= j < r.open.len() implies elem_tagged(#[trigger] r.open[j]) by {
                assert(r.open[j] == q.open[j]);
            }
            lemma_pop_until_named(r, tt);
        }
    }
}

/// "Has an element in scope that is an HTML element with the same tag
/// name as that of the token": by name and by tag alike, on a tagged
/// stack.
pub proof fn lemma_same_name_in_scope(p: Parser, tt: TagTok)
    requires
        tok_tagged(tt),
        named_tag(tt.tag),
        all_tagged(p.open),
    ensures
        has_same_name_in_scope(p, tt) == has_in_scope(p, tt.tag, Scope::Default),
{
    super::equivalence::lemma_closure_ext();
    let f = |e: Elem| is_html_named(e, tt.name);
    let g = |e: Elem| is_html(e, tt.tag);
    assert forall|j: int| 0 <= j < p.open.len() implies #[trigger] f(p.open[j]) == g(p.open[j]) by {
        lemma_same_name_same_tag(p.open[j], tt);
    }
}

/// The "li" loops.
proof fn lemma_li_loop(p: Parser, i: int)
    requires
        i < p.open.len(),
    ensures
        w3c_li_loop(p, i) == li_loop(p, i),
    decreases i + 1,
{
    if i >= 0 {
        lemma_li_loop(p, i - 1);
    }
}

/// The "dd", "dt" loops.
proof fn lemma_dd_dt_loop(p: Parser, i: int)
    requires
        i < p.open.len(),
    ensures
        w3c_dd_dt_loop(p, i) == dd_dt_loop(p, i),
    decreases i + 1,
{
    if i >= 0 {
        lemma_dd_dt_loop(p, i - 1);
    }
}

/// The "any other end tag" loops.
proof fn lemma_any_other_end_tag_loop(p: Parser, tt: TagTok, i: int)
    requires
        i < p.open.len(),
    ensures
        w3c_any_other_end_tag_loop(p, tt, i) == any_other_end_tag_loop(p, tt, i),
    decreases i + 1,
{
    if i >= 0 {
        lemma_any_other_end_tag_loop(p, tt, i - 1);
    }
}

/// "Any other end tag".
pub proof fn lemma_any_other_end_tag(p: Parser, tt: TagTok)
    ensures
        w3c_any_other_end_tag(p, tt) == in_body_any_other_end_tag(p, tt),
{
    lemma_any_other_end_tag_loop(p, tt, p.open.len() - 1);
}

/// "Pop all the nodes … up to, but not including, the root html element"
/// leaves the first entry.
proof fn lemma_pop_to_root(q: Parser)
    requires
        q.open.len() >= 1,
    ensures
        w3c_pop_to_root(q) == (Parser { open: q.open.take(1), ..q }),
    decreases q.open.len(),
{
    if q.open.len() > 1 {
        lemma_pop_to_root(pop(q));
        assert(pop(q).open.take(1) =~= q.open.take(1));
    } else {
        assert(q.open.take(1) =~= q.open);
    }
}

/// Inserting an element that stops parsing leaves the stack empty
/// ([`stop_parsing`] empties it), so popping it changes nothing.
pub proof fn lemma_insert_foreign_stopped(p: Parser, tt: TagTok, ns: Namespace)
    requires
        !p.stopped,
    ensures
        insert_foreign_element(p, tt, ns).0.stopped ==> insert_foreign_element(p, tt, ns).0.open.len() == 0,
{
}

// ---------------------------------------------------------------------
// Attributes

/// Every attribute has no namespace and no prefix (the token's attributes,
/// and those of an element the parser created for a token in the HTML
/// namespace).
pub open spec fn attrs_plain(attrs: Seq<Attr>) -> bool {
    forall|i: int| 0 <= i < attrs.len() ==> (#[trigger] attrs[i]).namespace is None && attrs[i].prefix is None
}

/// Node `el` is an element of the arena whose attributes are
/// [`attrs_plain`].
pub open spec fn element_plain(doc: Document, el: NodeId) -> bool {
    &&& dom::valid(doc, el)
    &&& doc.nodes[el as int].kind is Element
    &&& attrs_plain(doc.nodes[el as int].kind->Element_attributes)
}

/// "Already present": for attributes without namespace or prefix, the
/// W3C transcription's test (an attribute with no namespace and the local
/// name) and the WHATWG one's (an attribute with the qualified name) agree.
proof fn lemma_attr_present(attrs: Seq<Attr>, name: Seq<u32>)
    requires
        attrs_plain(attrs),
    ensures
        (attr_value(attrs, name) is Some) == attrs_have_name(attrs, name),
    decreases attrs.len(),
{
    if attrs.len() > 0 {
        assert(attrs[0].namespace is None && attrs[0].prefix is None);
        let r = attrs.drop_first();
        assert forall|i: int| 0 <= i < r.len() implies (#[trigger] r[i]).namespace is None && r[i].prefix is None by {
            assert(r[i] == attrs[i + 1]);
        }
        lemma_attr_present(r, name);
    }
}

/// The `html` and `body` start tags' attribute loops.
proof fn lemma_add_missing(p: Parser, el: NodeId, attrs: Seq<Attr>, i: int)
    requires
        element_plain(p.doc, el),
        attrs_plain(attrs),
    ensures
        w3c_add_missing_attributes(p, el, attrs, i) == add_missing_attributes(p, el, attrs, i),
    decreases attrs.len() - i,
{
    if 0 <= i < attrs.len() {
        let old = p.doc.nodes[el as int].kind->Element_attributes;
        lemma_attr_present(old, attrs[i].local_name);
        let a = attrs[i];
        let q = if !p.stopped && !element_has_attribute_named(p.doc, el, a.local_name) {
            Parser { doc: dom::append_attribute(p.doc, el, a), ..p }
        } else {
            p
        };
        if q != p {
            let new = q.doc.nodes[el as int].kind->Element_attributes;
            assert(new == old.push(a));
            assert forall|j: int| 0 <= j < new.len() implies (#[trigger] new[j]).namespace is None && new[j].prefix is None by {
                if j < old.len() {
                    assert(new[j] == old[j]);
                }
            }
        }
        lemma_add_missing(q, el, attrs, i + 1);
    }
}

// ---------------------------------------------------------------------
// The adoption agency algorithm: the state

/// An entry of the list of active formatting elements is for an HTML
/// element whose id is below `n`, tagged by its name, with a tagged token.
pub open spec fn fmt_entry_ok(x: Fmt, n: nat) -> bool {
    x is Entry ==> {
        &&& x->Entry_elem.id < n
        &&& x->Entry_elem.ns == Namespace::Html
        &&& elem_tagged(x->Entry_elem)
        &&& tok_tagged(x->Entry_token)
    }
}

/// Every entry of `f` is [`fmt_entry_ok`], and two entries for the same
/// element have the same tag.
pub open spec fn fmt_list_ok(f: Seq<Fmt>, n: nat) -> bool {
    &&& forall|j: int| 0 <= j < f.len() ==> fmt_entry_ok(#[trigger] f[j], n)
    &&& forall|j: int, k: int|
        #![trigger f[j], f[k]]
        0 <= j < f.len() && 0 <= k < f.len() && f[j] is Entry && f[k] is Entry && f[j]->Entry_elem.id == f[k]->Entry_elem.id
            ==> f[j]->Entry_elem.tag == f[k]->Entry_elem.tag
}

/// Every record of the stack `o` has an id below `n` and is tagged.
pub open spec fn stack_ok(o: Seq<Elem>, n: nat) -> bool {
    forall|j: int| 0 <= j < o.len() ==> (#[trigger] o[j]).id < n && elem_tagged(o[j])
}

/// The facts of reachable states the adoption agency algorithm's lemma
/// uses: every record on the stack and in the list of active formatting
/// elements names a node of the arena (`invariant::ids_in_doc`) and is
/// tagged (`invariant::tags_wf`); the list's entries are HTML elements (the
/// parser pushes only the elements "in body" creates for formatting tags);
/// and two entries for the same element agree on its tag (both name the
/// element's node, and `ids_in_doc` ties a record's name to its node's).
pub open spec fn aa_wf(p: Parser) -> bool {
    stack_ok(p.open, p.doc.nodes.len()) && fmt_list_ok(p.formatting, p.doc.nodes.len())
}

/// The entry is for the element `id`.
pub open spec fn has_id(x: Fmt, id: NodeId) -> bool {
    x is Entry && x->Entry_elem.id == id
}

// ---------------------------------------------------------------------
// The adoption agency algorithm: where the two texts differ

/// Steps 15 to 18 (WHATWG steps 4.17 to 4.27) of one outer loop iteration
/// make the same insertions in both texts, for the parser `p` the inner
/// loop hands over, formatting element's token `fe_token`, common
/// ancestor `ca`, furthest block `fb` and last node `last`. The texts
/// differ there in three ways, each excluded here:
/// - Step 15 inserts last node "at the appropriate place for inserting a
///   node" with common ancestor as the override target; the WHATWG takes
///   the *adjusted* insertion location (4.18), which the insertion target
///   redirection map (the fragment case's root, a WHATWG addition) can
///   redirect: excluded when it does.
/// - The W3C's DOM insertion "first removing it from its previous parent"
///   inserts only if DOM's checks pass and otherwise leaves last node
///   where it is; the WHATWG removes last node (4.20) and then inserts it
///   only if its own checks pass (4.21): both checks are required to pass.
/// - Step 18 appends the new element to furthest block; the WHATWG inserts
///   it at the adjusted insertion location given (furthest block, null)
///   (4.27.2): excluded when the redirection map redirects furthest block;
///   and the WHATWG makes 4.27.1's reparenting only when its guard holds
///   (`dom_reparent_children`): required to hold.
pub open spec fn w3c_aa_step_agrees(p: Parser, fe_token: TagTok, ca: Elem, fb: Elem, last: Elem) -> bool {
    let loc = appropriate_place(p, Some(ca));
    let d1 = dom_remove(p, last.id).doc;
    let p2 = dom_insert(p, last.id, loc.parent, loc.child);
    let (p3, new_el) = create_element_for_token(p2, fe_token, Namespace::Html, fb.id);
    let d3 = p3.doc;
    &&& adjusted_location(p, Some(loc)) == loc
    &&& insert_valid(p.doc, last.id, loc.parent, loc.child)
    &&& insert_valid(d1, last.id, loc.parent, loc.child)
    &&& !(d1.nodes[loc.parent as int].kind is Document && has_element_child(d1, loc.parent))
    &&& (p3.stopped || (dom::valid(d3, fb.id) && dom::valid(d3, new_el.id) && fb.id != new_el.id && dom::may_have_children(
        d3.nodes[fb.id as int].kind,
    ) && dom::may_have_children(d3.nodes[new_el.id as int].kind) && !dom::is_inclusive_ancestor(d3, fb.id, new_el.id)))
    &&& (p.redirect is None || p.redirect->Some_0.0 != fb.id)
}

/// [`w3c_aa_step_agrees`] at every iteration of the outer loop of the
/// W3C's adoption agency algorithm run from `p` with outer loop counter
/// `counter` (the iterations [`w3c_aa_outer`] makes).
pub open spec fn w3c_aa_agrees(p: Parser, tt: TagTok, counter: nat) -> bool
    decreases 8 - counter,
{
    if counter >= 8 || p.stopped {
        true
    } else {
        let k = w3c_aa_find(p.formatting, p.formatting.len() as int, tt.tag);
        if k < 0 {
            true
        } else {
            let fe = p.formatting[k]->Entry_elem;
            let fe_token = p.formatting[k]->Entry_token;
            let fi = open_index_of(p, fe.id);
            if fi < 0 || !has_node_in_scope(p, fe.id, Scope::Default) {
                true
            } else {
                let b = w3c_furthest_block(p.open, fi + 1);
                if b < 0 {
                    true
                } else {
                    let fb = p.open[b];
                    let ca = p.open[fi - 1];
                    let (p1, last, bm1) = w3c_aa_inner(p, fe, ca, fb, b, fb, 0, k);
                    &&& p1.stopped || w3c_aa_step_agrees(p1, fe_token, ca, fb, last)
                    &&& w3c_aa_agrees(w3c_aa_after_inner(p1, fe, fe_token, ca, fb, last, bm1), tt, counter + 1)
                }
            }
        }
    }
}

// ---------------------------------------------------------------------
// The adoption agency algorithm: the list of active formatting elements

/// [`fmt_index_of`] is -1 or the index of the last entry for `id` among
/// the first `i`.
proof fn lemma_fmt_index(f: Seq<Fmt>, i: int, id: NodeId)
    requires
        0 <= i <= f.len(),
    ensures
        -1 <= fmt_index_of(f, i, id) < i,
        fmt_index_of(f, i, id) >= 0 ==> has_id(f[fmt_index_of(f, i, id)], id),
        forall|m: int| fmt_index_of(f, i, id) < m < i ==> !has_id(#[trigger] f[m], id),
    decreases i,
{
    if i > 0 && !has_id(f[i - 1], id) {
        lemma_fmt_index(f, i - 1, id);
    }
}

/// [`fmt_index_of`] is the index `j` of an entry for `id` (or -1) when no
/// later entry among the first `i` is for `id`.
proof fn lemma_fmt_index_is(f: Seq<Fmt>, i: int, id: NodeId, j: int)
    requires
        0 <= i <= f.len(),
        -1 <= j < i,
        j >= 0 ==> has_id(f[j], id),
        forall|m: int| j < m < i ==> !has_id(#[trigger] f[m], id),
    ensures
        fmt_index_of(f, i, id) == j,
    decreases i,
{
    if i > 0 && i - 1 != j {
        assert(!has_id(f[i - 1], id));
        lemma_fmt_index_is(f, i - 1, id, j);
    }
}

/// The index `j` once the entry at `k` (another one) is removed.
pub open spec fn shift_after_remove(j: int, k: int) -> int {
    if j < 0 {
        -1
    } else if k < j {
        j - 1
    } else {
        j
    }
}

/// Removing an entry not for `id` moves `id`'s entry down past it.
proof fn lemma_fmt_remove(f: Seq<Fmt>, k: int, id: NodeId)
    requires
        0 <= k < f.len(),
        !has_id(f[k], id),
    ensures
        fmt_index_of(f.remove(k), f.len() - 1, id) == shift_after_remove(fmt_index_of(f, f.len() as int, id), k),
        fmt_index_of(f, f.len() as int, id) >= 0 ==> f.remove(k)[shift_after_remove(fmt_index_of(f, f.len() as int, id), k)]
            == f[fmt_index_of(f, f.len() as int, id)],
{
    let g = f.remove(k);
    let j = fmt_index_of(f, f.len() as int, id);
    lemma_fmt_index(f, f.len() as int, id);
    let j2 = shift_after_remove(j, k);
    assert forall|m: int| j2 < m < g.len() implies !has_id(#[trigger] g[m], id) by {
        if m < k {
            assert(g[m] == f[m]);
        } else {
            assert(g[m] == f[m + 1]);
        }
    }
    if j >= 0 {
        assert(g[j2] == f[j]);
    }
    lemma_fmt_index_is(g, g.len() as int, id, j2);
}

/// Replacing an entry not for `id` by another not for `id` keeps `id`'s
/// entry.
proof fn lemma_fmt_update(f: Seq<Fmt>, k: int, x: Fmt, id: NodeId)
    requires
        0 <= k < f.len(),
        !has_id(f[k], id),
        !has_id(x, id),
    ensures
        fmt_index_of(f.update(k, x), f.len() as int, id) == fmt_index_of(f, f.len() as int, id),
        fmt_index_of(f, f.len() as int, id) >= 0 ==> f.update(k, x)[fmt_index_of(f, f.len() as int, id)] == f[fmt_index_of(
            f,
            f.len() as int,
            id,
        )],
{
    let g = f.update(k, x);
    let j = fmt_index_of(f, f.len() as int, id);
    lemma_fmt_index(f, f.len() as int, id);
    assert forall|m: int| j < m < g.len() implies !has_id(#[trigger] g[m], id) by {
        if m != k {
            assert(g[m] == f[m]);
        }
    }
    lemma_fmt_index_is(g, g.len() as int, id, j);
}

/// An entry for a new element `id` (no other entry is for it) is found
/// where it was put.
proof fn lemma_fmt_fresh(f: Seq<Fmt>, k: int, x: Fmt, id: NodeId)
    requires
        0 <= k < f.len(),
        has_id(x, id),
        forall|m: int| 0 <= m < f.len() && m != k ==> !has_id(#[trigger] f[m], id),
    ensures
        fmt_index_of(f.update(k, x), f.len() as int, id) == k,
{
    let g = f.update(k, x);
    assert forall|m: int| k < m < g.len() implies !has_id(#[trigger] g[m], id) by {
        assert(g[m] == f[m]);
    }
    lemma_fmt_index_is(g, g.len() as int, id, k);
}

/// [`fmt_list_ok`] after removing an entry.
proof fn lemma_list_ok_remove(f: Seq<Fmt>, k: int, n: nat)
    requires
        fmt_list_ok(f, n),
        0 <= k < f.len(),
    ensures
        fmt_list_ok(f.remove(k), n),
{
    let g = f.remove(k);
    assert forall|j: int| 0 <= j < g.len() implies fmt_entry_ok(#[trigger] g[j], n) by {
        if j < k {
            assert(g[j] == f[j]);
        } else {
            assert(g[j] == f[j + 1]);
        }
    }
    assert forall|j: int, m: int|
        #![trigger g[j], g[m]]
        0 <= j < g.len() && 0 <= m < g.len() && g[j] is Entry && g[m] is Entry && g[j]->Entry_elem.id
            == g[m]->Entry_elem.id implies g[j]->Entry_elem.tag == g[m]->Entry_elem.tag by {
        let j1 = if j < k {
            j
        } else {
            j + 1
        };
        let m1 = if m < k {
            m
        } else {
            m + 1
        };
        assert(g[j] == f[j1]);
        assert(g[m] == f[m1]);
    }
}

/// A list entry is new: its element's id is at least `n` (every entry of
/// the list has a smaller one), and it is [`fmt_entry_ok`] for `n2`.
pub open spec fn fresh_entry(x: Fmt, n: nat, n2: nat) -> bool {
    &&& x is Entry
    &&& x->Entry_elem.id >= n
    &&& fmt_entry_ok(x, n2)
}

/// [`fmt_list_ok`] for a larger arena.
proof fn lemma_list_ok_grow(f: Seq<Fmt>, n: nat, n2: nat)
    requires
        fmt_list_ok(f, n),
        n <= n2,
    ensures
        fmt_list_ok(f, n2),
{
    assert forall|j: int| 0 <= j < f.len() implies fmt_entry_ok(#[trigger] f[j], n2) by {
        assert(fmt_entry_ok(f[j], n));
    }
}

/// [`fmt_list_ok`] after replacing an entry by a new one, with the arena
/// grown from `n` to `n2` nodes.
proof fn lemma_list_ok_update(f: Seq<Fmt>, k: int, x: Fmt, n: nat, n2: nat)
    requires
        fmt_list_ok(f, n),
        n <= n2,
        fresh_entry(x, n, n2),
        0 <= k < f.len(),
    ensures
        fmt_list_ok(f.update(k, x), n2),
{
    lemma_list_ok_grow(f, n, n2);
    let g = f.update(k, x);
    assert forall|j: int| 0 <= j < g.len() implies fmt_entry_ok(#[trigger] g[j], n2) by {
        if j != k {
            assert(g[j] == f[j]);
        }
    }
    assert forall|j: int, m: int|
        #![trigger g[j], g[m]]
        0 <= j < g.len() && 0 <= m < g.len() && g[j] is Entry && g[m] is Entry && g[j]->Entry_elem.id
            == g[m]->Entry_elem.id implies g[j]->Entry_elem.tag == g[m]->Entry_elem.tag by {
        if j != k {
            assert(g[j] == f[j]);
            assert(fmt_entry_ok(f[j], n));
        }
        if m != k {
            assert(g[m] == f[m]);
            assert(fmt_entry_ok(f[m], n));
        }
    }
}

/// [`fmt_list_ok`] after inserting a new entry, with the arena grown from
/// `n` to `n2` nodes.
proof fn lemma_list_ok_insert(f: Seq<Fmt>, k: int, x: Fmt, n: nat, n2: nat)
    requires
        fmt_list_ok(f, n),
        n <= n2,
        fresh_entry(x, n, n2),
        0 <= k <= f.len(),
    ensures
        fmt_list_ok(f.insert(k, x), n2),
{
    lemma_list_ok_grow(f, n, n2);
    let h = f.insert(k, x);
    assert forall|j: int| 0 <= j < h.len() implies fmt_entry_ok(#[trigger] h[j], n2) by {
        if j < k {
            assert(h[j] == f[j]);
        } else if j > k {
            assert(h[j] == f[j - 1]);
        }
    }
    assert forall|j: int, m: int|
        #![trigger h[j], h[m]]
        0 <= j < h.len() && 0 <= m < h.len() && h[j] is Entry && h[m] is Entry && h[j]->Entry_elem.id
            == h[m]->Entry_elem.id implies h[j]->Entry_elem.tag == h[m]->Entry_elem.tag by {
        if j != k {
            let j1 = if j < k {
                j
            } else {
                j - 1
            };
            assert(h[j] == f[j1]);
            assert(fmt_entry_ok(f[j1], n));
        }
        if m != k {
            let m1 = if m < k {
                m
            } else {
                m - 1
            };
            assert(h[m] == f[m1]);
            assert(fmt_entry_ok(f[m1], n));
        }
        if j != k && m != k {
            let j1 = if j < k {
                j
            } else {
                j - 1
            };
            let m1 = if m < k {
                m
            } else {
                m - 1
            };
            assert(f[j1] is Entry && f[m1] is Entry);
        }
    }
}

// ---------------------------------------------------------------------
// The adoption agency algorithm: the searches

/// [`after_last_marker`] is the index after the last marker among the
/// first `i` entries (0 if none).
proof fn lemma_after_last_marker(f: Seq<Fmt>, i: int)
    requires
        0 <= i <= f.len(),
    ensures
        0 <= after_last_marker(f, i) <= i,
        after_last_marker(f, i) > 0 ==> f[after_last_marker(f, i) - 1] is Marker,
        forall|j: int| after_last_marker(f, i) <= j < i ==> !(#[trigger] f[j] is Marker),
    decreases i,
{
    if i > 0 && !(f[i - 1] is Marker) {
        lemma_after_last_marker(f, i - 1);
    }
}

/// Step 6's search (W3C: by tag, stopping at a marker) and the WHATWG
/// transcription's (by `pred`, from the index after the last marker)
/// agree when `pred` is the tag test on the entries after the last
/// marker.
proof fn lemma_aa_find_eq(f: Seq<Fmt>, i: int, subject: Tag, pred: spec_fn(Elem) -> bool)
    requires
        after_last_marker(f, f.len() as int) <= i <= f.len(),
        forall|j: int|
            after_last_marker(f, f.len() as int) <= j < f.len() && #[trigger] f[j] is Entry ==> pred(f[j]->Entry_elem) == (
            f[j]->Entry_elem.tag == subject),
    ensures
        w3c_aa_find(f, i, subject) == fmt_last_where(f, after_last_marker(f, f.len() as int), i, pred),
    decreases i,
{
    lemma_after_last_marker(f, f.len() as int);
    let m = after_last_marker(f, f.len() as int);
    if i > m {
        assert(!(f[i - 1] is Marker));
        lemma_aa_find_eq(f, i - 1, subject, pred);
    }
}

/// What step 6's search finds: an entry with the tag, after which no entry
/// has it.
proof fn lemma_aa_find_facts(f: Seq<Fmt>, i: int, subject: Tag)
    requires
        0 <= i <= f.len(),
    ensures
        -1 <= w3c_aa_find(f, i, subject) < i,
        w3c_aa_find(f, i, subject) >= 0 ==> f[w3c_aa_find(f, i, subject)] is Entry && f[w3c_aa_find(
            f,
            i,
            subject,
        )]->Entry_elem.tag == subject,
        w3c_aa_find(f, i, subject) >= 0 ==> forall|m: int|
            w3c_aa_find(f, i, subject) < m < i ==> (#[trigger] f[m]) is Entry && f[m]->Entry_elem.tag != subject,
    decreases i,
{
    if i > 0 && !(f[i - 1] is Marker) && f[i - 1]->Entry_elem.tag != subject {
        lemma_aa_find_facts(f, i - 1, subject);
    }
}

/// The entry step 6 finds is the last entry for its element (another
/// entry for it would have the same tag, and be found instead).
proof fn lemma_aa_find_last_id(f: Seq<Fmt>, subject: Tag, n: nat)
    requires
        fmt_list_ok(f, n),
        w3c_aa_find(f, f.len() as int, subject) >= 0,
    ensures
        fmt_index_of(f, f.len() as int, f[w3c_aa_find(f, f.len() as int, subject)]->Entry_elem.id) == w3c_aa_find(
            f,
            f.len() as int,
            subject,
        ),
{
    let k = w3c_aa_find(f, f.len() as int, subject);
    lemma_aa_find_facts(f, f.len() as int, subject);
    let id = f[k]->Entry_elem.id;
    assert forall|m: int| k < m < f.len() implies !has_id(#[trigger] f[m], id) by {
        assert(f[m] is Entry && f[m]->Entry_elem.tag != subject);
        if f[m]->Entry_elem.id == id {
            assert(f[m]->Entry_elem.tag == f[k]->Entry_elem.tag);
        }
    }
    lemma_fmt_index_is(f, f.len() as int, id, k);
}

/// Step 10's searches.
proof fn lemma_furthest_block(open: Seq<Elem>, i: int)
    ensures
        w3c_furthest_block(open, i) == first_special_from(open, i),
    decreases open.len() - i,
{
    if 0 <= i < open.len() && !is_special(open[i]) {
        lemma_furthest_block(open, i + 1);
    }
}

/// `last_index_where` depends only on the values of its predicate.
proof fn lemma_liw_ext(o: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool, g: spec_fn(Elem) -> bool)
    requires
        i <= o.len(),
        forall|j: int| 0 <= j < i ==> #[trigger] f(o[j]) == g(o[j]),
    ensures
        last_index_where(o, i, f) == last_index_where(o, i, g),
    decreases i,
{
    if i > 0 {
        assert(f(o[i - 1]) == g(o[i - 1]));
        lemma_liw_ext(o, i - 1, f, g);
    }
}

/// [`lemma_aa_find_eq`] for every predicate, so that the WHATWG
/// transcription's own closure can be matched.
proof fn lemma_aa_find_eq_all(f: Seq<Fmt>, subject: Tag)
    ensures
        forall|pred: spec_fn(Elem) -> bool|
            (forall|j: int|
                after_last_marker(f, f.len() as int) <= j < f.len() && #[trigger] f[j] is Entry ==> pred(f[j]->Entry_elem) == (
                f[j]->Entry_elem.tag == subject)) ==> #[trigger] fmt_last_where(
                f,
                after_last_marker(f, f.len() as int),
                f.len() as int,
                pred,
            ) == w3c_aa_find(f, f.len() as int, subject),
{
    lemma_after_last_marker(f, f.len() as int);
    assert forall|pred: spec_fn(Elem) -> bool|
        (forall|j: int|
            after_last_marker(f, f.len() as int) <= j < f.len() && #[trigger] f[j] is Entry ==> pred(f[j]->Entry_elem) == (
            f[j]->Entry_elem.tag == subject)) implies #[trigger] fmt_last_where(
        f,
        after_last_marker(f, f.len() as int),
        f.len() as int,
        pred,
    ) == w3c_aa_find(f, f.len() as int, subject) by {
        lemma_aa_find_eq(f, f.len() as int, subject, pred);
    }
}

/// [`lemma_liw_ext`] for every pair of predicates.
proof fn lemma_liw_ext_all()
    ensures
        forall|o: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool, g: spec_fn(Elem) -> bool|
            i <= o.len() && (forall|j: int| 0 <= j < i ==> #[trigger] f(o[j]) == g(o[j])) ==> #[trigger] last_index_where(o, i, f)
                == #[trigger] last_index_where(o, i, g),
{
    assert forall|o: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool, g: spec_fn(Elem) -> bool|
        i <= o.len() && (forall|j: int| 0 <= j < i ==> #[trigger] f(o[j]) == g(o[j])) implies #[trigger] last_index_where(o, i, f)
        == #[trigger] last_index_where(o, i, g) by {
        lemma_liw_ext(o, i, f, g);
    }
}

/// `last_index_where` is -1 or an index below `i` satisfying `f`, and is
/// not -1 if some entry below `i` satisfies `f`.
proof fn lemma_liw(o: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool)
    requires
        0 <= i <= o.len(),
    ensures
        -1 <= last_index_where(o, i, f) < i,
        last_index_where(o, i, f) >= 0 ==> f(o[last_index_where(o, i, f)]),
        (exists|j: int| 0 <= j < i && #[trigger] f(o[j])) ==> last_index_where(o, i, f) >= 0,
    decreases i,
{
    if i > 0 && !f(o[i - 1]) {
        lemma_liw(o, i - 1, f);
        if exists|j: int| 0 <= j < i && #[trigger] f(o[j]) {
            let j = choose|j: int| 0 <= j < i && #[trigger] f(o[j]);
            assert(j < i - 1);
        }
    }
}

// ---------------------------------------------------------------------
// The adoption agency algorithm: the DOM

/// What creating an element for a token changes in a running parser: the
/// document, which gets the new node (its id is the arena's length), or,
/// at the node limit, parsing stops.
proof fn lemma_create_new(p: Parser, t: TagTok, ns: Namespace, ip: NodeId)
    requires
        !p.stopped,
    ensures
        ({
            let (q, e) = create_element_for_token(p, t, ns, ip);
            &&& e.ns == ns && e.tag == t.tag && e.name == t.name
            &&& !q.stopped ==> q == (Parser { doc: q.doc, ..p }) && e.id == p.doc.nodes.len() && e.id < q.doc.nodes.len()
        }),
{
}

/// A DOM insertion changes only the document, and not its number of nodes.
proof fn lemma_dom_insert_len(p: Parser, n: NodeId, par: NodeId, c: Option<NodeId>)
    ensures
        dom_insert(p, n, par, c) == (Parser { doc: dom_insert(p, n, par, c).doc, ..p }),
        dom_insert(p, n, par, c).doc.nodes.len() == p.doc.nodes.len(),
{
}

/// Moving children does not change the number of nodes.
proof fn lemma_reparent_len(d: Document, from: NodeId, to: NodeId, n: nat)
    ensures
        dom::reparent_children_n(d, from, to, n).nodes.len() == d.nodes.len(),
    decreases n,
{
    if !(n == 0 || d.nodes[from as int].children.len() == 0) {
        let d1 = dom::append(d, to, d.nodes[from as int].children[0]);
        assert(d1.nodes.len() == d.nodes.len());
        lemma_reparent_len(d1, from, to, (n - 1) as nat);
    }
}

/// Step 15's insertion: the WHATWG removes last node and then inserts it
/// (4.20, 4.21); the W3C's DOM insertion removes it from its parent itself.
/// When both insertions are made, the documents are the same.
proof fn lemma_insert_after_remove(p: Parser, n: NodeId, par: NodeId, c: Option<NodeId>)
    requires
        !p.stopped,
        insert_valid(p.doc, n, par, c),
        insert_valid(dom_remove(p, n).doc, n, par, c),
    ensures
        dom_insert(dom_remove(p, n), n, par, c) == dom_insert(p, n, par, c),
        dom_remove(p, n).doc.nodes[n as int].parent is None,
{
    let d = p.doc;
    if d.nodes[n as int].parent is Some {
        let d1 = dom::remove(d, n);
        assert(d1.nodes[n as int].parent is None);
        assert(dom::adopt(d1, n) == d1);
        assert(dom::adopt(d, n) == d1);
    }
}

// ---------------------------------------------------------------------
// The adoption agency algorithm: the loops

/// An entry of the stack `o` is for the element `id`.
pub open spec fn on_stack(o: Seq<Elem>, id: NodeId) -> bool {
    exists|j: int| 0 <= j < o.len() && (#[trigger] o[j]).id == id
}

/// The inner loop's state in both transcriptions, at node index `ni`, for
/// formatting element `fe` (created for `fe_token`) and furthest block
/// `fb`, with last node `last`, the W3C's bookmark `bm` (an index) and the
/// WHATWG's `bk`: [`aa_wf`]; formatting element on the stack and the last
/// entry for it in the list; the bookmarks at the same place (still at
/// formatting element, while last node is furthest block; otherwise after
/// the first new element `b`, which is not on the stack above node).
pub open spec fn aa_inner_ok(p: Parser, fe: Elem, fe_token: TagTok, fb: Elem, ni: int, last: Elem, bm: int, bk: Bookmark) -> bool {
    let f = p.formatting;
    let n = f.len() as int;
    &&& aa_wf(p)
    &&& ni <= p.open.len()
    &&& fb.id < p.doc.nodes.len()
    &&& on_stack(p.open, fe.id)
    &&& fmt_index_of(f, n, fe.id) >= 0
    &&& f[fmt_index_of(f, n, fe.id)] == (Fmt::Entry { elem: fe, token: fe_token })
    &&& match bk {
        Bookmark::FormattingElement => last.id == fb.id && bm == fmt_index_of(f, n, fe.id),
        Bookmark::After(b) => {
            &&& last.id != fb.id
            &&& b != fe.id
            &&& fmt_index_of(f, n, b) >= 0
            &&& bm == fmt_index_of(f, n, b) + 1
            &&& forall|j: int| 0 <= j < ni ==> (#[trigger] p.open[j]).id != b
        },
    }
}

/// Step 14.5's removal from the list keeps [`aa_inner_ok`].
proof fn lemma_aa_inner_remove(p: Parser, fe: Elem, fe_token: TagTok, fb: Elem, ni: int, last: Elem, bm: int, bk: Bookmark, k: int)
    requires
        aa_inner_ok(p, fe, fe_token, fb, ni, last, bm, bk),
        0 <= ni - 1 < p.open.len(),
        0 <= k < p.formatting.len(),
        has_id(p.formatting[k], p.open[ni - 1].id),
        p.open[ni - 1].id != fe.id,
    ensures
        aa_inner_ok(w3c_fmt_remove(p, k), fe, fe_token, fb, ni, last, w3c_bookmark_after_remove(bm, k), bk),
{
    let f = p.formatting;
    let id = p.open[ni - 1].id;
    lemma_fmt_remove(f, k, fe.id);
    lemma_list_ok_remove(f, k, p.doc.nodes.len());
    match bk {
        Bookmark::After(b) => {
            assert(p.open[ni - 1].id != b);
            lemma_fmt_remove(f, k, b);
            lemma_fmt_index(f, f.len() as int, b);
        },
        Bookmark::FormattingElement => {
            lemma_fmt_index(f, f.len() as int, fe.id);
        },
    }
}

/// Step 14.6's removal from the stack keeps [`aa_inner_ok`] at the node
/// above.
proof fn lemma_aa_inner_pop(p: Parser, fe: Elem, fe_token: TagTok, fb: Elem, ni: int, last: Elem, bm: int, bk: Bookmark)
    requires
        aa_inner_ok(p, fe, fe_token, fb, ni, last, bm, bk),
        0 <= ni - 1 < p.open.len(),
        p.open[ni - 1].id != fe.id,
    ensures
        aa_inner_ok(remove_open_at(p, ni - 1), fe, fe_token, fb, ni - 1, last, bm, bk),
{
    let i = ni - 1;
    let q = remove_open_at(p, i);
    assert forall|j: int| 0 <= j < q.open.len() implies (#[trigger] q.open[j]).id < q.doc.nodes.len() && elem_tagged(
        q.open[j],
    ) by {
        if j < i {
            assert(q.open[j] == p.open[j]);
        } else {
            assert(q.open[j] == p.open[j + 1]);
        }
    }
    let w = choose|j: int| 0 <= j < p.open.len() && (#[trigger] p.open[j]).id == fe.id;
    if w < i {
        assert(q.open[w] == p.open[w]);
    } else {
        assert(w > i);
        assert(q.open[w - 1] == p.open[w]);
    }
    match bk {
        Bookmark::After(b) => {
            assert forall|j: int| 0 <= j < i implies (#[trigger] q.open[j]).id != b by {
                assert(q.open[j] == p.open[j]);
            }
        },
        Bookmark::FormattingElement => {},
    }
}

/// Step 14.7 to 14.9 keep [`aa_inner_ok`] at the node above, with the new
/// element as last node.
proof fn lemma_aa_inner_replace(
    p: Parser,
    fe: Elem,
    fe_token: TagTok,
    fb: Elem,
    ni: int,
    last: Elem,
    bm: int,
    bk: Bookmark,
    k1: int,
    p2: Parser,
    new_el: Elem,
)
    requires
        aa_inner_ok(p, fe, fe_token, fb, ni, last, bm, bk),
        0 <= ni - 1 < p.open.len(),
        p.open[ni - 1].id != fe.id,
        0 <= k1 < p.formatting.len(),
        has_id(p.formatting[k1], p.open[ni - 1].id),
        k1 == fmt_index_of(p.formatting, p.formatting.len() as int, p.open[ni - 1].id),
        !p2.stopped,
        p2 == (Parser { doc: p2.doc, ..p }),
        new_el.id == p.doc.nodes.len(),
        new_el.id < p2.doc.nodes.len(),
        new_el.ns == Namespace::Html,
        new_el.tag == p.formatting[k1]->Entry_token.tag,
        new_el.name == p.formatting[k1]->Entry_token.name,
    ensures
        ({
            let token = p.formatting[k1]->Entry_token;
            let i = ni - 1;
            let p3 = Parser {
                formatting: p2.formatting.update(k1, Fmt::Entry { elem: new_el, token }),
                open: p2.open.update(i, new_el),
                ..p2
            };
            let bm2 = if last.id == fb.id {
                k1 + 1
            } else {
                bm
            };
            let bk2 = match bk {
                Bookmark::FormattingElement => Bookmark::After(new_el.id),
                Bookmark::After(b) => Bookmark::After(b),
            };
            aa_inner_ok(dom_insert(p3, last.id, new_el.id, None), fe, fe_token, fb, i, new_el, bm2, bk2)
        }),
{
    let f = p.formatting;
    let n0 = p.doc.nodes.len();
    let n2 = p2.doc.nodes.len();
    let token = f[k1]->Entry_token;
    let i = ni - 1;
    let x = Fmt::Entry { elem: new_el, token };
    assert(fmt_entry_ok(f[k1], n0));
    assert(elem_tagged(new_el));
    assert(fresh_entry(x, n0, n2));
    lemma_list_ok_update(f, k1, x, n0, n2);
    let p3 = Parser { formatting: p2.formatting.update(k1, x), open: p2.open.update(i, new_el), ..p2 };
    lemma_dom_insert_len(p3, last.id, new_el.id, None);
    let p4 = dom_insert(p3, last.id, new_el.id, None);
    // The stack.
    assert forall|j: int| 0 <= j < p4.open.len() implies (#[trigger] p4.open[j]).id < p4.doc.nodes.len() && elem_tagged(
        p4.open[j],
    ) by {
        if j != i {
            assert(p4.open[j] == p.open[j]);
        }
    }
    let w = choose|j: int| 0 <= j < p.open.len() && (#[trigger] p.open[j]).id == fe.id;
    assert(w != i);
    assert(p4.open[w] == p.open[w]);
    // Formatting element's entry.
    lemma_fmt_index(f, f.len() as int, fe.id);
    assert(fmt_entry_ok(f[fmt_index_of(f, f.len() as int, fe.id)], n0));
    lemma_fmt_update(f, k1, x, fe.id);
    // The bookmarks.
    match bk {
        Bookmark::FormattingElement => {
            assert forall|m: int| 0 <= m < f.len() && m != k1 implies !has_id(#[trigger] f[m], new_el.id) by {
                assert(fmt_entry_ok(f[m], n0));
            }
            lemma_fmt_fresh(f, k1, x, new_el.id);
            assert forall|j: int| 0 <= j < i implies (#[trigger] p4.open[j]).id != new_el.id by {
                assert(p4.open[j] == p.open[j]);
            }
        },
        Bookmark::After(b) => {
            assert(p.open[i].id != b);
            lemma_fmt_index(f, f.len() as int, b);
            assert(fmt_entry_ok(f[fmt_index_of(f, f.len() as int, b)], n0));
            lemma_fmt_update(f, k1, x, b);
            assert forall|j: int| 0 <= j < i implies (#[trigger] p4.open[j]).id != b by {
                assert(p4.open[j] == p.open[j]);
            }
        },
    }
}

/// What [`aa_inner_ok`] says of the index and of the bookmarks, and that
/// it holds at node index 0 once it holds at any.
proof fn lemma_aa_inner_ok_facts(p: Parser, fe: Elem, fe_token: TagTok, fb: Elem, ni: int, last: Elem, bm: int, bk: Bookmark)
    requires
        aa_inner_ok(p, fe, fe_token, fb, ni, last, bm, bk),
    ensures
        ni <= p.open.len(),
        (bk is FormattingElement) == (last.id == fb.id),
        aa_inner_ok(p, fe, fe_token, fb, 0, last, bm, bk),
{
}

/// Step 14, the inner loop: the two transcriptions agree, and keep
/// [`aa_inner_ok`].
proof fn lemma_aa_inner(
    p: Parser,
    fe: Elem,
    fe_token: TagTok,
    ca: Elem,
    fb: Elem,
    ni: int,
    last: Elem,
    counter: nat,
    bm: int,
    bk: Bookmark,
)
    requires
        aa_inner_ok(p, fe, fe_token, fb, ni, last, bm, bk),
    ensures
        aa_inner_agree(p, fe, fe_token, ca, fb, ni, last, counter, bm, bk),
    decreases ni, 2nat,
{
    hide(aa_inner_ok);
    hide(w3c_aa_inner);
    hide(aa_inner);
    lemma_aa_inner_ok_facts(p, fe, fe_token, fb, ni, last, bm, bk);
    if p.stopped || ni <= 0 || p.open[ni - 1].id == fe.id {
        reveal_with_fuel(w3c_aa_inner, 1);
        reveal_with_fuel(aa_inner, 1);
    } else {
        let c = counter + 1;
        let id = p.open[ni - 1].id;
        let p1 = aa_inner_p1(p, id, c);
        let bm1 = aa_inner_bm1(p, id, c, bm);
        lemma_aa_inner_first(p, fe, fe_token, fb, ni, last, c, bm, bk);
        if w3c_fmt_index(p1, id) < 0 {
            lemma_aa_inner_case_pop(p, fe, fe_token, ca, fb, ni, last, counter, bm, bk);
        } else {
            lemma_aa_inner_case_new(p, fe, fe_token, ca, fb, ni, last, counter, bm, bk);
        }
    }
}

/// The conclusion of [`lemma_aa_inner`]: the inner loops of both
/// transcriptions end in the same parser and last node, with
/// [`aa_inner_ok`] at node index 0 unless parsing stopped.
pub open spec fn aa_inner_agree(
    p: Parser,
    fe: Elem,
    fe_token: TagTok,
    ca: Elem,
    fb: Elem,
    ni: int,
    last: Elem,
    counter: nat,
    bm: int,
    bk: Bookmark,
) -> bool {
    let (q, l, b) = w3c_aa_inner(p, fe, ca, fb, ni, last, counter, bm);
    let (q2, l2, b2) = aa_inner(p, fe, ca, ni, last, counter, bk);
    &&& q == q2
    &&& l == l2
    &&& !q.stopped ==> aa_inner_ok(q, fe, fe_token, fb, 0, l, b, b2)
}

/// Step 14.5 in both transcriptions: the parser after it.
pub open spec fn aa_inner_p1(p: Parser, id: NodeId, c: nat) -> Parser {
    let k = w3c_fmt_index(p, id);
    if c > 3 && k >= 0 {
        w3c_fmt_remove(p, k)
    } else {
        p
    }
}

/// Step 14.5: the W3C's bookmark after it.
pub open spec fn aa_inner_bm1(p: Parser, id: NodeId, c: nat, bm: int) -> int {
    let k = w3c_fmt_index(p, id);
    if c > 3 && k >= 0 {
        w3c_bookmark_after_remove(bm, k)
    } else {
        bm
    }
}

/// Step 14.5 keeps [`aa_inner_ok`].
proof fn lemma_aa_inner_first(p: Parser, fe: Elem, fe_token: TagTok, fb: Elem, ni: int, last: Elem, c: nat, bm: int, bk: Bookmark)
    requires
        aa_inner_ok(p, fe, fe_token, fb, ni, last, bm, bk),
        !p.stopped,
        0 < ni <= p.open.len(),
        p.open[ni - 1].id != fe.id,
    ensures
        aa_inner_ok(
            aa_inner_p1(p, p.open[ni - 1].id, c),
            fe,
            fe_token,
            fb,
            ni,
            last,
            aa_inner_bm1(p, p.open[ni - 1].id, c, bm),
            bk,
        ),
        aa_inner_p1(p, p.open[ni - 1].id, c) == (Parser {
            formatting: aa_inner_p1(p, p.open[ni - 1].id, c).formatting,
            ..p
        }),
{
    let f = p.formatting;
    let id = p.open[ni - 1].id;
    lemma_fmt_index(f, f.len() as int, id);
    let k = w3c_fmt_index(p, id);
    if c > 3 && k >= 0 {
        lemma_aa_inner_remove(p, fe, fe_token, fb, ni, last, bm, bk, k);
    }
}

/// The inner loop when node is not in the list after step 14.5: step 14.6
/// removes it from the stack, in both transcriptions.
proof fn lemma_aa_inner_case_pop(
    p: Parser,
    fe: Elem,
    fe_token: TagTok,
    ca: Elem,
    fb: Elem,
    ni: int,
    last: Elem,
    counter: nat,
    bm: int,
    bk: Bookmark,
)
    requires
        aa_inner_ok(p, fe, fe_token, fb, ni, last, bm, bk),
        !p.stopped,
        0 < ni <= p.open.len(),
        p.open[ni - 1].id != fe.id,
        w3c_fmt_index(aa_inner_p1(p, p.open[ni - 1].id, counter + 1), p.open[ni - 1].id) < 0,
        aa_inner_ok(
            aa_inner_p1(p, p.open[ni - 1].id, counter + 1),
            fe,
            fe_token,
            fb,
            ni,
            last,
            aa_inner_bm1(p, p.open[ni - 1].id, counter + 1, bm),
            bk,
        ),
        aa_inner_p1(p, p.open[ni - 1].id, counter + 1) == (Parser {
            formatting: aa_inner_p1(p, p.open[ni - 1].id, counter + 1).formatting,
            ..p
        }),
    ensures
        aa_inner_agree(p, fe, fe_token, ca, fb, ni, last, counter, bm, bk),
    decreases ni, 1nat,
{
    hide(aa_inner_ok);
    hide(create_element_for_token);
    hide(dom_insert);
    let c = counter + 1;
    let i = ni - 1;
    let id = p.open[i].id;
    let p1 = aa_inner_p1(p, id, c);
    let bm1 = aa_inner_bm1(p, id, c, bm);
    lemma_aa_inner_pop(p1, fe, fe_token, fb, ni, last, bm1, bk);
    lemma_aa_inner(remove_open_at(p1, i), fe, fe_token, ca, fb, i, last, c, bm1, bk);
    reveal_with_fuel(w3c_aa_inner, 1);
    reveal_with_fuel(aa_inner, 1);
}

/// The inner loop when node is in the list after step 14.5: steps 14.7 to
/// 14.9 replace it by a new element, in both transcriptions.
proof fn lemma_aa_inner_case_new(
    p: Parser,
    fe: Elem,
    fe_token: TagTok,
    ca: Elem,
    fb: Elem,
    ni: int,
    last: Elem,
    counter: nat,
    bm: int,
    bk: Bookmark,
)
    requires
        aa_inner_ok(p, fe, fe_token, fb, ni, last, bm, bk),
        !p.stopped,
        0 < ni <= p.open.len(),
        p.open[ni - 1].id != fe.id,
        w3c_fmt_index(aa_inner_p1(p, p.open[ni - 1].id, counter + 1), p.open[ni - 1].id) >= 0,
        aa_inner_ok(
            aa_inner_p1(p, p.open[ni - 1].id, counter + 1),
            fe,
            fe_token,
            fb,
            ni,
            last,
            aa_inner_bm1(p, p.open[ni - 1].id, counter + 1, bm),
            bk,
        ),
        aa_inner_p1(p, p.open[ni - 1].id, counter + 1) == (Parser {
            formatting: aa_inner_p1(p, p.open[ni - 1].id, counter + 1).formatting,
            ..p
        }),
    ensures
        aa_inner_agree(p, fe, fe_token, ca, fb, ni, last, counter, bm, bk),
    decreases ni, 1nat,
{
    hide(aa_inner_ok);
    hide(create_element_for_token);
    hide(dom_insert);
    let c = counter + 1;
    let i = ni - 1;
    let id = p.open[i].id;
    let p1 = aa_inner_p1(p, id, c);
    let bm1 = aa_inner_bm1(p, id, c, bm);
    let f1 = p1.formatting;
    lemma_fmt_index(f1, f1.len() as int, id);
    let k1 = w3c_fmt_index(p1, id);
    let token = f1[k1]->Entry_token;
    lemma_create_new(p1, token, Namespace::Html, ca.id);
    let (p2, new_el) = create_element_for_token(p1, token, Namespace::Html, ca.id);
    lemma_aa_inner_ok_facts(p1, fe, fe_token, fb, ni, last, bm1, bk);
    if !p2.stopped {
        lemma_aa_inner_replace(p1, fe, fe_token, fb, ni, last, bm1, bk, k1, p2, new_el);
        let p3 = Parser {
            formatting: p2.formatting.update(k1, Fmt::Entry { elem: new_el, token }),
            open: p2.open.update(i, new_el),
            ..p2
        };
        let bm2 = if last.id == fb.id {
            k1 + 1
        } else {
            bm1
        };
        let bk2 = match bk {
            Bookmark::FormattingElement => Bookmark::After(new_el.id),
            Bookmark::After(b) => Bookmark::After(b),
        };
        lemma_aa_inner(dom_insert(p3, last.id, new_el.id, None), fe, fe_token, ca, fb, i, new_el, c, bm2, bk2);
    }
    reveal_with_fuel(w3c_aa_inner, 1);
    reveal_with_fuel(aa_inner, 1);
}

/// The parser an adoption agency outcome leaves, once "in body" acts as
/// "any other end tag" says when the algorithm says so.
pub open spec fn aa_result(o: AdoptionOutcome, tt: TagTok) -> Parser {
    match o {
        AdoptionOutcome::Done(q) => q,
        AdoptionOutcome::AnyOtherEndTag(q) => in_body_any_other_end_tag(q, tt),
    }
}

/// Steps 15 to 20 (WHATWG 4.17 to 4.24, 4.27): the two transcriptions
/// agree where [`w3c_aa_step_agrees`], and keep [`aa_wf`].
proof fn lemma_aa_after_inner(p: Parser, fe: Elem, fe_token: TagTok, ca: Elem, fb: Elem, last: Elem, bm: int, bk: Bookmark)
    requires
        !p.stopped,
        aa_inner_ok(p, fe, fe_token, fb, 0, last, bm, bk),
        w3c_aa_step_agrees(p, fe_token, ca, fb, last),
    ensures
        w3c_aa_after_inner(p, fe, fe_token, ca, fb, last, bm) == aa_finish(p, fe, fb, ca, last, bk),
        !w3c_aa_after_inner(p, fe, fe_token, ca, fb, last, bm).stopped ==> aa_wf(w3c_aa_after_inner(p, fe, fe_token, ca, fb, last, bm)),
{
    let f = p.formatting;
    let n0 = p.doc.nodes.len();
    let loc = appropriate_place(p, Some(ca));
    // Step 15 (4.17 to 4.21).
    lemma_insert_after_remove(p, last.id, loc.parent, loc.child);
    lemma_dom_insert_len(p, last.id, loc.parent, loc.child);
    let p1 = dom_insert(p, last.id, loc.parent, loc.child);
    // Step 16 (4.22).
    lemma_fmt_index(f, f.len() as int, fe.id);
    let fi = fmt_index_of(f, f.len() as int, fe.id);
    lemma_create_new(p1, fe_token, Namespace::Html, fb.id);
    let (p2, new_el) = create_element_for_token(p1, fe_token, Namespace::Html, fb.id);
    if !p2.stopped {
        let n2 = p2.doc.nodes.len();
        // Step 17 (4.27.1).
        let p3 = Parser { doc: dom::reparent_children(p2.doc, fb.id, new_el.id), ..p2 };
        lemma_reparent_len(p2.doc, fb.id, new_el.id, p2.doc.nodes[fb.id as int].children.len());
        // Step 18 (4.27.2, 4.27.3).
        lemma_dom_insert_len(p3, new_el.id, fb.id, None);
        let p4 = dom_insert(p3, new_el.id, fb.id, None);
        // Step 19 (4.23).
        let x = Fmt::Entry { elem: new_el, token: fe_token };
        assert(fmt_entry_ok(f[fi], n0));
        assert(elem_tagged(new_el));
        assert(fresh_entry(x, n0, n2));
        let bm1 = w3c_bookmark_after_remove(bm, fi);
        let f1 = f.remove(fi);
        lemma_list_ok_remove(f, fi, n0);
        match bk {
            Bookmark::After(b) => {
                lemma_fmt_index(f, f.len() as int, b);
                lemma_fmt_remove(f, fi, b);
            },
            Bookmark::FormattingElement => {},
        }
        assert(0 <= bm1 <= f1.len());
        lemma_list_ok_insert(f1, bm1, x, n0, n2);
        // Step 20 (4.24).
        let fe_pred = |e: Elem| e.id == fe.id;
        let w = choose|j: int| 0 <= j < p.open.len() && (#[trigger] p.open[j]).id == fe.id;
        assert(fe_pred(p.open[w]));
        lemma_liw(p.open, p.open.len() as int, |e: Elem| e.id == fe.id);
        let fei = open_index_of(p, fe.id);
        assert(0 <= fei < p.open.len());
        let o1 = p.open.remove(fei);
        assert forall|j: int| 0 <= j < o1.len() implies (#[trigger] o1[j]).id < n2 && elem_tagged(o1[j]) by {
            if j < fei {
                assert(o1[j] == p.open[j]);
            } else {
                assert(o1[j] == p.open[j + 1]);
            }
        }
        lemma_liw(o1, o1.len() as int, |e: Elem| e.id == fb.id);
        lemma_liw_ext_all();
        let fbi = last_index_where(o1, o1.len() as int, |e: Elem| e.id == fb.id);
        let o2 = o1.insert(fbi + 1, new_el);
        assert forall|j: int| 0 <= j < o2.len() implies (#[trigger] o2[j]).id < n2 && elem_tagged(o2[j]) by {
            if j < fbi + 1 {
                assert(o2[j] == o1[j]);
            } else if j > fbi + 1 {
                assert(o2[j] == o1[j - 1]);
            }
        }
    }
}

/// Once the inner loop has stopped parsing, the steps after it change
/// nothing, in both transcriptions.
proof fn lemma_aa_after_inner_stopped(p: Parser, fe: Elem, fe_token: TagTok, ca: Elem, fb: Elem, last: Elem, bm: int, bk: Bookmark)
    requires
        p.stopped,
    ensures
        w3c_aa_after_inner(p, fe, fe_token, ca, fb, last, bm) == p,
        aa_finish(p, fe, fb, ca, last, bk) == p,
{
}

/// The inner loop's state at its start (step 14: node and last node are
/// furthest block; the bookmark is at formatting element).
proof fn lemma_aa_inner_start(p: Parser, k: int, fi: int, b: int)
    requires
        aa_wf(p),
        0 <= k < p.formatting.len(),
        p.formatting[k] is Entry,
        fmt_index_of(p.formatting, p.formatting.len() as int, p.formatting[k]->Entry_elem.id) == k,
        0 <= fi < p.open.len(),
        p.open[fi].id == p.formatting[k]->Entry_elem.id,
        0 <= b < p.open.len(),
    ensures
        aa_inner_ok(
            p,
            p.formatting[k]->Entry_elem,
            p.formatting[k]->Entry_token,
            p.open[b],
            b,
            p.open[b],
            k,
            Bookmark::FormattingElement,
        ),
{
    assert(on_stack(p.open, p.formatting[k]->Entry_elem.id));
}

/// One iteration of the outer loop that reaches the inner loop: the two
/// transcriptions agree on it and on the rest of the loop.
proof fn lemma_aa_iteration(p: Parser, tt: TagTok, counter: nat, k: int, fi: int, b: int)
    requires
        aa_wf(p),
        tok_tagged(tt),
        w3c_formatting_end_tag(tt.tag),
        counter < 8,
        !p.stopped,
        0 <= k < p.formatting.len(),
        p.formatting[k] is Entry,
        fmt_index_of(p.formatting, p.formatting.len() as int, p.formatting[k]->Entry_elem.id) == k,
        0 <= fi < p.open.len(),
        p.open[fi].id == p.formatting[k]->Entry_elem.id,
        0 <= b < p.open.len(),
        ({
            let fe = p.formatting[k]->Entry_elem;
            let fe_token = p.formatting[k]->Entry_token;
            let fb = p.open[b];
            let ca = p.open[fi - 1];
            let (p1, last, bm1) = w3c_aa_inner(p, fe, ca, fb, b, fb, 0, k);
            &&& p1.stopped || w3c_aa_step_agrees(p1, fe_token, ca, fb, last)
            &&& w3c_aa_agrees(w3c_aa_after_inner(p1, fe, fe_token, ca, fb, last, bm1), tt, counter + 1)
        }),
    ensures
        ({
            let fe = p.formatting[k]->Entry_elem;
            let fe_token = p.formatting[k]->Entry_token;
            let fb = p.open[b];
            let ca = p.open[fi - 1];
            let (p1, last, bm1) = w3c_aa_inner(p, fe, ca, fb, b, fb, 0, k);
            let (q1, l1, bk1) = aa_inner(p, fe, ca, b, fb, 0, Bookmark::FormattingElement);
            w3c_aa_outer(w3c_aa_after_inner(p1, fe, fe_token, ca, fb, last, bm1), tt, counter + 1) == aa_result(
                aa_outer(aa_finish(q1, fe, fb, ca, l1, bk1), tt, counter + 1),
                tt,
            )
        }),
    decreases 8 - counter, 0nat,
{
    hide(w3c_aa_inner);
    hide(aa_inner);
    hide(w3c_aa_after_inner);
    hide(aa_finish);
    hide(aa_inner_ok);
    let fe = p.formatting[k]->Entry_elem;
    let fe_token = p.formatting[k]->Entry_token;
    let fb = p.open[b];
    let ca = p.open[fi - 1];
    lemma_aa_inner_start(p, k, fi, b);
    lemma_aa_inner(p, fe, fe_token, ca, fb, b, fb, 0, k, Bookmark::FormattingElement);
    let (p1, last, bm1) = w3c_aa_inner(p, fe, ca, fb, b, fb, 0, k);
    let (q1, l1, bk1) = aa_inner(p, fe, ca, b, fb, 0, Bookmark::FormattingElement);
    if p1.stopped {
        lemma_aa_after_inner_stopped(p1, fe, fe_token, ca, fb, last, bm1, bk1);
        reveal_with_fuel(w3c_aa_outer, 1);
        reveal_with_fuel(aa_outer, 1);
    } else {
        lemma_aa_after_inner(p1, fe, fe_token, ca, fb, last, bm1, bk1);
        lemma_aa_outer(w3c_aa_after_inner(p1, fe, fe_token, ca, fb, last, bm1), tt, (counter + 1) as nat);
    }
}

/// The outer loop: the two transcriptions agree where
/// [`w3c_aa_agrees`].
proof fn lemma_aa_outer(p: Parser, tt: TagTok, counter: nat)
    requires
        p.stopped || aa_wf(p),
        tok_tagged(tt),
        w3c_formatting_end_tag(tt.tag),
        w3c_aa_agrees(p, tt, counter),
    ensures
        w3c_aa_outer(p, tt, counter) == aa_result(aa_outer(p, tt, counter), tt),
    decreases 8 - counter, 1nat,
{
    hide(w3c_aa_inner);
    hide(aa_inner);
    hide(w3c_aa_after_inner);
    hide(aa_finish);
    hide(in_body_any_other_end_tag);
    hide(w3c_any_other_end_tag);
    if !(counter >= 8 || p.stopped) {
        let f = p.formatting;
        let n = f.len() as int;
        lemma_after_last_marker(f, n);
        assert forall|j: int| after_last_marker(f, n) <= j < f.len() && #[trigger] f[j] is Entry implies (f[j]->Entry_elem.name
            == tt.name) == (f[j]->Entry_elem.tag == tt.tag) by {
            assert(fmt_entry_ok(f[j], p.doc.nodes.len()));
            lemma_same_name_same_tag(f[j]->Entry_elem, tt);
        }
        lemma_aa_find_eq_all(f, tt.tag);
        let k = w3c_aa_find(f, n, tt.tag);
        lemma_aa_find_facts(f, n, tt.tag);
        assert(fmt_last_where(f, after_last_marker(f, n), n, |e: Elem| e.name == tt.name) == k);
        if k < 0 {
            lemma_any_other_end_tag(p, tt);
            assert(w3c_aa_outer(p, tt, counter) == aa_result(aa_outer(p, tt, counter), tt));
        } else {
            lemma_aa_find_last_id(f, tt.tag, p.doc.nodes.len());
            let fe = f[k]->Entry_elem;
            let fi = open_index_of(p, fe.id);
            lemma_liw(p.open, p.open.len() as int, |e: Elem| e.id == fe.id);
            lemma_pop_until_node_frame(p, fe.id);
            if fi < 0 || !has_node_in_scope(p, fe.id, Scope::Default) {
                assert(w3c_aa_outer(p, tt, counter) == aa_result(aa_outer(p, tt, counter), tt));
            }
            if fi >= 0 && has_node_in_scope(p, fe.id, Scope::Default) {
                lemma_furthest_block(p.open, fi + 1);
                let b = w3c_furthest_block(p.open, fi + 1);
                if b < 0 {
                    assert(w3c_aa_outer(p, tt, counter) == aa_result(aa_outer(p, tt, counter), tt));
                }
                if b >= 0 {
                    assert(p.open[fi].id == fe.id);
                    assert(b < p.open.len()) by {
                        reveal_with_fuel(w3c_furthest_block, 1);
                        lemma_furthest_block_range(p.open, fi + 1);
                    }
                    lemma_aa_iteration(p, tt, counter, k, fi, b);
                }
            }
        }
    }
}

/// "Pop all the nodes … up to and including" an element changes only the
/// stack.
proof fn lemma_pop_until_node_frame(p: Parser, id: NodeId)
    ensures
        pop_until_node_popped(p, id) == (Parser { open: pop_until_node_popped(p, id).open, ..p }),
    decreases p.open.len(),
{
    if p.open.len() > 0 && current_node(p).id != id {
        lemma_pop_until_node_frame(pop(p), id);
    }
}

/// Step 10's search finds -1 or an index of the stack.
proof fn lemma_furthest_block_range(open: Seq<Elem>, i: int)
    ensures
        -1 <= w3c_furthest_block(open, i) < open.len(),
    decreases open.len() - i,
{
    if 0 <= i < open.len() && !is_special(open[i]) {
        lemma_furthest_block_range(open, i + 1);
    }
}

/// The adoption agency algorithm (W3C §8.2.5.4.7, WHATWG §13.2.6.4.7, with
/// "any other end tag" where step 6 (4.3) says to act as it): the two
/// transcriptions agree where the insertions of every iteration do
/// ([`w3c_aa_agrees`]), on a parser with the facts [`aa_wf`] and a
/// nonempty stack, for a tagged token with a formatting tag. (Step 6's
/// "has the tag name subject" is read as the same tag here and as the same
/// name in the WHATWG transcription; they agree on tagged records.)
pub proof fn lemma_adoption(p: Parser, tt: TagTok)
    requires
        aa_wf(p),
        p.open.len() > 0,
        tok_tagged(tt),
        w3c_formatting_end_tag(tt.tag),
        w3c_aa_agrees(p, tt, 0),
    ensures
        w3c_adoption_agency(p, tt) == in_body_adoption(p, tt),
{
    assert(elem_tagged(p.open[p.open.len() - 1]));
    lemma_same_name_same_tag(current_node(p), tt);
    lemma_aa_outer(p, tt, 0);
}

// ---------------------------------------------------------------------
// §8.2.5.4.7 "in body"

/// "Pop elements … until an HTML element whose name is `tag` has been
/// popped" changes only the stack.
proof fn lemma_pop_until_frame(p: Parser, tag: Tag)
    ensures
        pop_until_popped(p, tag) == (Parser { open: pop_until_popped(p, tag).open, ..p }),
    decreases p.open.len(),
{
    if p.open.len() > 0 && !is_html(current_node(p), tag) {
        lemma_pop_until_frame(pop(p), tag);
    }
}

/// A parser that stopped has an empty stack ([`stop_parsing`] empties it):
/// so the WHATWG transcription's "no pop if the insertion stopped parsing"
/// and the W3C's pop agree.
pub open spec fn stopped_empty(p: Parser) -> bool {
    p.stopped ==> p.open.len() == 0
}

/// Inserting an element keeps [`stopped_empty`].
proof fn lemma_insert_stopped_empty(p: Parser, tt: TagTok, ns: Namespace)
    requires
        stopped_empty(p),
    ensures
        stopped_empty(insert_foreign_element(p, tt, ns).0),
        ns == Namespace::Html ==> stopped_empty(insert_html_element(p, tt).0),
{
}

/// Steps 7 to 10 of "reconstruct the active formatting elements" keep
/// [`stopped_empty`].
proof fn lemma_reconstruct_create_stopped_empty(p: Parser, i: int)
    requires
        stopped_empty(p),
    ensures
        stopped_empty(reconstruct_create(p, i)),
    decreases p.formatting.len() - i,
{
    if !(i < 0 || i >= p.formatting.len() || p.stopped || !(p.formatting[i] is Entry)) {
        let token = p.formatting[i]->Entry_token;
        lemma_insert_stopped_empty(p, token, Namespace::Html);
        let (p1, new_element) = insert_html_element(p, token);
        let p2 = if p1.stopped {
            p1
        } else {
            Parser { formatting: p1.formatting.update(i, Fmt::Entry { elem: new_element, token }), ..p1 }
        };
        if i + 1 < p2.formatting.len() && p2.formatting.len() == p.formatting.len() {
            lemma_reconstruct_create_stopped_empty(p2, i + 1);
        }
    }
}

/// "Reconstruct the active formatting elements" keeps [`stopped_empty`].
proof fn lemma_reconstruct_stopped_empty(p: Parser)
    requires
        stopped_empty(p),
    ensures
        stopped_empty(reconstruct_formatting(p)),
{
    let n = p.formatting.len();
    if n > 0 {
        lemma_reconstruct_create_stopped_empty(p, reconstruct_rewind(p, n - 1));
    }
}

/// Inserting an element for two tokens that differ only in their
/// self-closing flag gives the same parser.
proof fn lemma_insert_same_token(p: Parser, a: TagTok, b: TagTok)
    requires
        a.name == b.name,
        a.tag == b.tag,
        a.attrs == b.attrs,
    ensures
        insert_html_element(p, a).0 == insert_html_element(p, b).0,
{
    assert(a == TagTok { self_closing: a.self_closing, ..b });
}

/// Where the W3C "in body" text differs from the WHATWG one (each
/// excluded):
/// - The WHATWG adds `hgroup`, `menu` and `search` to the block start
///   tags (closing a `p` element) and end tags, and `select` to the block
///   end tags; for the W3C they are "any other" start or end tags.
/// - The WHATWG's `area`, … entry also lists `keygen`; for the W3C it is
///   "any other start tag".
/// - `select`: the W3C switches to "in select" or "in select in table"
///   (not WHATWG modes); the WHATWG parses its content "in body". The
///   WHATWG's `input`, `hr`, `option` and `optgroup` entries have steps
///   for a `select` element in scope (or a `select` fragment context) the
///   W3C does not: excluded when there is one.
/// - `form` start and end tags: the WHATWG tests "parsing template
///   contents", which is also true when the fragment context is a
///   `template`; the W3C tests for a `template` element on the stack:
///   excluded for a `template` context.
pub open spec fn in_body_texts_agree(p: Parser, t: Tok) -> bool {
    let g = w3c_tag(t);
    let select_context = p.context is Some && is_html(p.context->Some_0, Tag::Select);
    &&& !(t is Pi)
    &&& !(t is Start && (g == Tag::Hgroup || g == Tag::Menu || g == Tag::Search || g == Tag::Keygen || g == Tag::Select))
    &&& !(t is End && (g == Tag::Hgroup || g == Tag::Menu || g == Tag::Search || g == Tag::Select))
    &&& (t is Start && g == Tag::Input) ==> !select_context && !has_in_scope(p, Tag::Select, Scope::Default)
    &&& (t is Start && g == Tag::Hr) ==> !has_in_scope(w3c_close_p_in_button_scope(p), Tag::Select, Scope::Default)
    &&& (t is Start && (g == Tag::Option || g == Tag::Optgroup)) ==> !has_in_scope(p, Tag::Select, Scope::Default)
    &&& ((t is Start || t is End) && g == Tag::Form) ==> !(p.context is Some && is_html(p.context->Some_0, Tag::Template))
}

/// Where the token runs the adoption agency algorithm, its insertions are
/// ones both texts make ([`w3c_aa_agrees`]) on the parser it runs on,
/// which has the facts [`aa_wf`] (the `nobr` start tag runs it after
/// reconstructing the active formatting elements).
pub open spec fn in_body_aa_agrees(p: Parser, t: Tok) -> bool {
    let g = w3c_tag(t);
    &&& (t is End && w3c_formatting_end_tag(g)) ==> w3c_aa_agrees(p, t->End_0, 0)
    &&& (t is Start && g == Tag::A && w3c_aa_find(p.formatting, p.formatting.len() as int, Tag::A) >= 0) ==> w3c_aa_agrees(
        p,
        t->Start_0,
        0,
    )
    &&& (t is Start && g == Tag::Nobr && has_in_scope(reconstruct_formatting(p), Tag::Nobr, Scope::Default)) ==> {
        let q = reconstruct_formatting(p);
        aa_wf(q) && q.open.len() > 0 && w3c_aa_agrees(q, t->Start_0, 0)
    }
}

/// The facts of reachable states the "in body" lemma uses: a stack (with
/// the `html` element), node 0 is the Document, [`aa_wf`], a tagged token;
/// and the `html` element (for an `html` start tag) and the `body`
/// element (for a `body` start tag) are elements whose attributes, like
/// the token's, have no namespace or prefix (they are HTML elements the
/// parser created for tokens).
pub open spec fn in_body_facts(p: Parser, t: Tok) -> bool {
    &&& p.open.len() > 0
    &&& p.doc.nodes.len() > 0
    &&& p.doc.nodes[0].kind is Document
    &&& aa_wf(p)
    &&& super::equivalence::token_tagged(t)
    &&& w3c_start(t, Tag::Html) ==> element_plain(p.doc, p.open[0].id) && attrs_plain(t->Start_0.attrs)
    &&& (w3c_start(t, Tag::Body) && p.open.len() >= 2 && is_html(p.open[1], Tag::Body)) ==> element_plain(p.doc, p.open[1].id)
        && attrs_plain(t->Start_0.attrs)
}

/// "In body"'s start tags.
proof fn lemma_in_body_start(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    let g = tt.tag;
    if g == Tag::Html || g == Tag::Body || g == Tag::Frameset {
        lemma_in_body_start_1(env, p, tt);
    } else if g == Tag::Form || g == Tag::Li || g == Tag::Dd || g == Tag::Dt {
        lemma_in_body_start_2(env, p, tt);
    } else if g == Tag::A || g == Tag::Nobr {
        lemma_in_body_start_3(env, p, tt);
    } else if g == Tag::Area || g == Tag::Br || g == Tag::Embed || g == Tag::Img || g == Tag::Wbr || g == Tag::Input || g
        == Tag::Math || g == Tag::Svg || g == Tag::Param || g == Tag::Source || g == Tag::Track || g == Tag::Hr {
        lemma_in_body_start_4(env, p, tt);
    } else {
        lemma_in_body_start_5(env, p, tt);
    }
}

/// "In body"'s start tags: `html`, `body`, `frameset`.
#[verifier::spinoff_prover]
proof fn lemma_in_body_start_1(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        tt.tag == Tag::Html || tt.tag == Tag::Body || tt.tag == Tag::Frameset,
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(reconstruct_formatting);
    hide(generic_text_parsing);
    hide(pop_until_popped);
    hide(generate_implied_end_tags);
    hide(w3c_adoption_agency);
    hide(in_body_adoption);
    hide(w3c_add_missing_attributes);
    hide(add_missing_attributes);
    hide(w3c_li_loop);
    hide(li_loop);
    hide(w3c_dd_dt_loop);
    hide(dd_dt_loop);
    hide(push_formatting);
    hide(w3c_push_formatting);
    hide(dom_remove);
    hide(w3c_pop_to_root);
    hide(in_body_start_a);
    let g = tt.tag;
    if g == Tag::Html {
        if !open_has_html(p, Tag::Template) {
            lemma_add_missing(p, p.open[0].id, tt.attrs, 0);
        }
    } else if g == Tag::Body {
        if !(p.open.len() < 2 || !is_html(p.open[1], Tag::Body) || open_has_html(p, Tag::Template)) {
            lemma_add_missing(w3c_frameset_not_ok(p), p.open[1].id, tt.attrs, 0);
        }
    } else {
        if p.open.len() >= 2 {
            reveal(dom_remove);
            lemma_pop_to_root(dom_remove(p, p.open[1].id));
        }
    }
}

/// "In body"'s start tags: `form`, `li`, `dd`, `dt`.
#[verifier::spinoff_prover]
proof fn lemma_in_body_start_2(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        tt.tag == Tag::Form || tt.tag == Tag::Li || tt.tag == Tag::Dd || tt.tag == Tag::Dt,
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(reconstruct_formatting);
    hide(generic_text_parsing);
    hide(pop_until_popped);
    hide(generate_implied_end_tags);
    hide(w3c_adoption_agency);
    hide(in_body_adoption);
    hide(w3c_add_missing_attributes);
    hide(add_missing_attributes);
    hide(w3c_li_loop);
    hide(li_loop);
    hide(w3c_dd_dt_loop);
    hide(dd_dt_loop);
    hide(push_formatting);
    hide(w3c_push_formatting);
    hide(dom_remove);
    hide(w3c_pop_to_root);
    hide(in_body_start_a);
    let g = tt.tag;
    if g == Tag::Form {
        if has_in_scope(p, Tag::P, Scope::Button) {
            reveal(generate_implied_end_tags);
            lemma_implied_tagged(p, Some(Tag::P));
            lemma_pop_until_frame(generate_implied_end_tags(p, Some(Tag::P)), Tag::P);
        }
    } else if g == Tag::Li {
        lemma_li_loop(w3c_frameset_not_ok(p), p.open.len() - 1);
    } else {
        lemma_dd_dt_loop(w3c_frameset_not_ok(p), p.open.len() - 1);
    }
}

/// "In body"'s start tags: `a`, `nobr`.
#[verifier::spinoff_prover]
proof fn lemma_in_body_start_3(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        tt.tag == Tag::A || tt.tag == Tag::Nobr,
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(reconstruct_formatting);
    hide(generic_text_parsing);
    hide(pop_until_popped);
    hide(generate_implied_end_tags);
    hide(w3c_adoption_agency);
    hide(in_body_adoption);
    hide(w3c_add_missing_attributes);
    hide(add_missing_attributes);
    hide(w3c_li_loop);
    hide(li_loop);
    hide(w3c_dd_dt_loop);
    hide(dd_dt_loop);
    hide(push_formatting);
    hide(w3c_push_formatting);
    hide(dom_remove);
    hide(w3c_pop_to_root);
    hide(in_body_start_a);
    let g = tt.tag;
    if g == Tag::A {
        reveal(in_body_start_a);
        lemma_in_body_start_a(p, tt);
    } else {
        let q = reconstruct_formatting(p);
        if has_in_scope(q, Tag::Nobr, Scope::Default) {
            lemma_adoption(q, tt);
        }
    }
}

/// "In body"'s start tags: the void elements, `input`, `math`, `svg`, `hr`.
proof fn lemma_in_body_start_4(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        tt.tag == Tag::Area || tt.tag == Tag::Br || tt.tag == Tag::Embed || tt.tag == Tag::Img || tt.tag == Tag::Wbr || tt.tag == Tag::Input || tt.tag == Tag::Math || tt.tag == Tag::Svg || tt.tag == Tag::Param || tt.tag == Tag::Source || tt.tag == Tag::Track || tt.tag == Tag::Hr,
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    let g = tt.tag;
    if g == Tag::Hr {
        lemma_in_body_start_4a(env, p, tt);
    } else if g == Tag::Math || g == Tag::Svg {
        lemma_in_body_start_4b(env, p, tt);
    } else if g == Tag::Param || g == Tag::Source || g == Tag::Track {
        lemma_in_body_start_4c(env, p, tt);
    } else {
        lemma_in_body_start_4d(env, p, tt);
    }
}

/// "In body"'s start tags: `hr`.
#[verifier::spinoff_prover]
proof fn lemma_in_body_start_4a(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        tt.tag == Tag::Hr,
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(reconstruct_formatting);
    hide(generic_text_parsing);
    hide(pop_until_popped);
    hide(generate_implied_end_tags);
    hide(w3c_adoption_agency);
    hide(in_body_adoption);
    hide(w3c_add_missing_attributes);
    hide(add_missing_attributes);
    hide(w3c_li_loop);
    hide(li_loop);
    hide(w3c_dd_dt_loop);
    hide(dd_dt_loop);
    hide(push_formatting);
    hide(w3c_push_formatting);
    hide(dom_remove);
    hide(w3c_pop_to_root);
    hide(in_body_start_a);
    let g = tt.tag;
    let q2 = w3c_close_p_in_button_scope(p);
    if has_in_scope(p, Tag::P, Scope::Button) {
        reveal(generate_implied_end_tags);
        lemma_implied_tagged(p, Some(Tag::P));
        lemma_pop_until_frame(generate_implied_end_tags(p, Some(Tag::P)), Tag::P);
    }
    lemma_insert_stopped_empty(q2, tt, Namespace::Html);
}

/// "In body"'s start tags: `math`, `svg`.
#[verifier::spinoff_prover]
proof fn lemma_in_body_start_4b(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        tt.tag == Tag::Math || tt.tag == Tag::Svg,
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(reconstruct_formatting);
    hide(generic_text_parsing);
    hide(pop_until_popped);
    hide(generate_implied_end_tags);
    hide(w3c_adoption_agency);
    hide(in_body_adoption);
    hide(w3c_add_missing_attributes);
    hide(add_missing_attributes);
    hide(w3c_li_loop);
    hide(li_loop);
    hide(w3c_dd_dt_loop);
    hide(dd_dt_loop);
    hide(push_formatting);
    hide(w3c_push_formatting);
    hide(dom_remove);
    hide(w3c_pop_to_root);
    hide(in_body_start_a);
    let g = tt.tag;
    lemma_reconstruct_stopped_empty(p);
    let q = reconstruct_formatting(p);
    if g == Tag::Math {
        lemma_insert_stopped_empty(q, adjust_foreign_attributes(adjust_mathml_attributes(tt)), Namespace::MathMl);
    } else {
        lemma_insert_stopped_empty(q, adjust_foreign_attributes(adjust_svg_attributes(tt)), Namespace::Svg);
    }
}

/// "In body"'s start tags: `param`, `source`, `track`.
proof fn lemma_in_body_start_4c(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        tt.tag == Tag::Param || tt.tag == Tag::Source || tt.tag == Tag::Track,
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    let g = tt.tag;
    if g == Tag::Param {
        lemma_in_body_start_4c_param(env, p, tt);
    } else if g == Tag::Source {
        lemma_in_body_start_4c_source(env, p, tt);
    } else {
        lemma_in_body_start_4c_track(env, p, tt);
    }
}

/// "In body"'s `param` start tag.
#[verifier::spinoff_prover]
proof fn lemma_in_body_start_4c_param(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        tt.tag == Tag::Param,
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(reconstruct_formatting);
    hide(generic_text_parsing);
    hide(pop_until_popped);
    hide(generate_implied_end_tags);
    hide(w3c_adoption_agency);
    hide(in_body_adoption);
    hide(w3c_add_missing_attributes);
    hide(add_missing_attributes);
    hide(w3c_li_loop);
    hide(li_loop);
    hide(w3c_dd_dt_loop);
    hide(dd_dt_loop);
    hide(push_formatting);
    hide(w3c_push_formatting);
    hide(dom_remove);
    hide(w3c_pop_to_root);
    hide(in_body_start_a);
    let g = tt.tag;
    lemma_insert_stopped_empty(p, tt, Namespace::Html);
}

/// "In body"'s `source` start tag.
#[verifier::spinoff_prover]
proof fn lemma_in_body_start_4c_source(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        tt.tag == Tag::Source,
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(reconstruct_formatting);
    hide(generic_text_parsing);
    hide(pop_until_popped);
    hide(generate_implied_end_tags);
    hide(w3c_adoption_agency);
    hide(in_body_adoption);
    hide(w3c_add_missing_attributes);
    hide(add_missing_attributes);
    hide(w3c_li_loop);
    hide(li_loop);
    hide(w3c_dd_dt_loop);
    hide(dd_dt_loop);
    hide(push_formatting);
    hide(w3c_push_formatting);
    hide(dom_remove);
    hide(w3c_pop_to_root);
    hide(in_body_start_a);
    let g = tt.tag;
    lemma_insert_stopped_empty(p, tt, Namespace::Html);
}

/// "In body"'s `track` start tag.
#[verifier::spinoff_prover]
proof fn lemma_in_body_start_4c_track(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        tt.tag == Tag::Track,
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(reconstruct_formatting);
    hide(generic_text_parsing);
    hide(pop_until_popped);
    hide(generate_implied_end_tags);
    hide(w3c_adoption_agency);
    hide(in_body_adoption);
    hide(w3c_add_missing_attributes);
    hide(add_missing_attributes);
    hide(w3c_li_loop);
    hide(li_loop);
    hide(w3c_dd_dt_loop);
    hide(dd_dt_loop);
    hide(push_formatting);
    hide(w3c_push_formatting);
    hide(dom_remove);
    hide(w3c_pop_to_root);
    hide(in_body_start_a);
    let g = tt.tag;
    lemma_insert_stopped_empty(p, tt, Namespace::Html);
}


/// "In body"'s start tags: `area`, `br`, `embed`, `img`, `wbr`, `input`.
proof fn lemma_in_body_start_4d(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        tt.tag == Tag::Area || tt.tag == Tag::Br || tt.tag == Tag::Embed || tt.tag == Tag::Img || tt.tag == Tag::Wbr || tt.tag == Tag::Input,
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    let g = tt.tag;
    if g == Tag::Area {
        lemma_in_body_start_4d_area(env, p, tt);
    } else if g == Tag::Br {
        lemma_in_body_start_4d_br(env, p, tt);
    } else if g == Tag::Embed {
        lemma_in_body_start_4d_embed(env, p, tt);
    } else if g == Tag::Img {
        lemma_in_body_start_4d_img(env, p, tt);
    } else if g == Tag::Wbr {
        lemma_in_body_start_4d_wbr(env, p, tt);
    } else {
        lemma_in_body_start_4d_input(env, p, tt);
    }
}

/// "In body"'s `area` start tag.
#[verifier::spinoff_prover]
proof fn lemma_in_body_start_4d_area(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        tt.tag == Tag::Area,
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(reconstruct_formatting);
    hide(generic_text_parsing);
    hide(pop_until_popped);
    hide(generate_implied_end_tags);
    hide(w3c_adoption_agency);
    hide(in_body_adoption);
    hide(w3c_add_missing_attributes);
    hide(add_missing_attributes);
    hide(w3c_li_loop);
    hide(li_loop);
    hide(w3c_dd_dt_loop);
    hide(dd_dt_loop);
    hide(push_formatting);
    hide(w3c_push_formatting);
    hide(dom_remove);
    hide(w3c_pop_to_root);
    hide(in_body_start_a);
    let g = tt.tag;
    lemma_reconstruct_stopped_empty(p);
    let q = reconstruct_formatting(p);
    lemma_insert_stopped_empty(q, tt, Namespace::Html);
}

/// "In body"'s `br` start tag.
#[verifier::spinoff_prover]
proof fn lemma_in_body_start_4d_br(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        tt.tag == Tag::Br,
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(reconstruct_formatting);
    hide(generic_text_parsing);
    hide(pop_until_popped);
    hide(generate_implied_end_tags);
    hide(w3c_adoption_agency);
    hide(in_body_adoption);
    hide(w3c_add_missing_attributes);
    hide(add_missing_attributes);
    hide(w3c_li_loop);
    hide(li_loop);
    hide(w3c_dd_dt_loop);
    hide(dd_dt_loop);
    hide(push_formatting);
    hide(w3c_push_formatting);
    hide(dom_remove);
    hide(w3c_pop_to_root);
    hide(in_body_start_a);
    let g = tt.tag;
    lemma_reconstruct_stopped_empty(p);
    let q = reconstruct_formatting(p);
    lemma_insert_stopped_empty(q, tt, Namespace::Html);
}

/// "In body"'s `embed` start tag.
#[verifier::spinoff_prover]
proof fn lemma_in_body_start_4d_embed(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        tt.tag == Tag::Embed,
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(reconstruct_formatting);
    hide(generic_text_parsing);
    hide(pop_until_popped);
    hide(generate_implied_end_tags);
    hide(w3c_adoption_agency);
    hide(in_body_adoption);
    hide(w3c_add_missing_attributes);
    hide(add_missing_attributes);
    hide(w3c_li_loop);
    hide(li_loop);
    hide(w3c_dd_dt_loop);
    hide(dd_dt_loop);
    hide(push_formatting);
    hide(w3c_push_formatting);
    hide(dom_remove);
    hide(w3c_pop_to_root);
    hide(in_body_start_a);
    let g = tt.tag;
    lemma_reconstruct_stopped_empty(p);
    let q = reconstruct_formatting(p);
    lemma_insert_stopped_empty(q, tt, Namespace::Html);
}

/// "In body"'s `img` start tag.
#[verifier::spinoff_prover]
proof fn lemma_in_body_start_4d_img(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        tt.tag == Tag::Img,
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(reconstruct_formatting);
    hide(generic_text_parsing);
    hide(pop_until_popped);
    hide(generate_implied_end_tags);
    hide(w3c_adoption_agency);
    hide(in_body_adoption);
    hide(w3c_add_missing_attributes);
    hide(add_missing_attributes);
    hide(w3c_li_loop);
    hide(li_loop);
    hide(w3c_dd_dt_loop);
    hide(dd_dt_loop);
    hide(push_formatting);
    hide(w3c_push_formatting);
    hide(dom_remove);
    hide(w3c_pop_to_root);
    hide(in_body_start_a);
    let g = tt.tag;
    lemma_reconstruct_stopped_empty(p);
    let q = reconstruct_formatting(p);
    lemma_insert_stopped_empty(q, tt, Namespace::Html);
}

/// "In body"'s `wbr` start tag.
#[verifier::spinoff_prover]
proof fn lemma_in_body_start_4d_wbr(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        tt.tag == Tag::Wbr,
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(reconstruct_formatting);
    hide(generic_text_parsing);
    hide(pop_until_popped);
    hide(generate_implied_end_tags);
    hide(w3c_adoption_agency);
    hide(in_body_adoption);
    hide(w3c_add_missing_attributes);
    hide(add_missing_attributes);
    hide(w3c_li_loop);
    hide(li_loop);
    hide(w3c_dd_dt_loop);
    hide(dd_dt_loop);
    hide(push_formatting);
    hide(w3c_push_formatting);
    hide(dom_remove);
    hide(w3c_pop_to_root);
    hide(in_body_start_a);
    let g = tt.tag;
    lemma_reconstruct_stopped_empty(p);
    let q = reconstruct_formatting(p);
    lemma_insert_stopped_empty(q, tt, Namespace::Html);
}

/// "In body"'s `input` start tag.
#[verifier::spinoff_prover]
proof fn lemma_in_body_start_4d_input(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        tt.tag == Tag::Input,
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(reconstruct_formatting);
    hide(generic_text_parsing);
    hide(pop_until_popped);
    hide(generate_implied_end_tags);
    hide(w3c_adoption_agency);
    hide(in_body_adoption);
    hide(w3c_add_missing_attributes);
    hide(add_missing_attributes);
    hide(w3c_li_loop);
    hide(li_loop);
    hide(w3c_dd_dt_loop);
    hide(dd_dt_loop);
    hide(push_formatting);
    hide(w3c_push_formatting);
    hide(dom_remove);
    hide(w3c_pop_to_root);
    hide(in_body_start_a);
    let g = tt.tag;
    lemma_reconstruct_stopped_empty(p);
    let q = reconstruct_formatting(p);
    lemma_insert_stopped_empty(q, tt, Namespace::Html);
}


/// "In body"'s start tags: the others.
#[verifier::spinoff_prover]
proof fn lemma_in_body_start_5(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::Start(tt)),
        in_body_texts_agree(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
        !(tt.tag == Tag::Html || tt.tag == Tag::Body || tt.tag == Tag::Frameset || tt.tag == Tag::Form || tt.tag == Tag::Li || tt.tag == Tag::Dd || tt.tag == Tag::Dt || tt.tag == Tag::A || tt.tag == Tag::Nobr || tt.tag == Tag::Area || tt.tag == Tag::Br || tt.tag == Tag::Embed || tt.tag == Tag::Img || tt.tag == Tag::Wbr || tt.tag == Tag::Input || tt.tag == Tag::Math || tt.tag == Tag::Svg || tt.tag == Tag::Param || tt.tag == Tag::Source || tt.tag == Tag::Track || tt.tag == Tag::Hr),
    ensures
        w3c_in_body_start(env, p, tt) == in_body_start_tag(p, Tok::Start(tt), tt),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(reconstruct_formatting);
    hide(generic_text_parsing);
    hide(pop_until_popped);
    hide(generate_implied_end_tags);
    hide(w3c_adoption_agency);
    hide(in_body_adoption);
    hide(w3c_add_missing_attributes);
    hide(add_missing_attributes);
    hide(w3c_li_loop);
    hide(li_loop);
    hide(w3c_dd_dt_loop);
    hide(dd_dt_loop);
    hide(push_formatting);
    hide(w3c_push_formatting);
    hide(dom_remove);
    hide(w3c_pop_to_root);
    hide(in_body_start_a);
    let g = tt.tag;
    if g == Tag::Image {
        assert(tag_of(w3c_name_img()) == Tag::Img) by (compute_only);
    }
}

/// "In body"'s `a` start tag.
proof fn lemma_in_body_start_a(p: Parser, tt: TagTok)
    requires
        !p.stopped,
        tt.tag == Tag::A,
        in_body_facts(p, Tok::Start(tt)),
        in_body_aa_agrees(p, Tok::Start(tt)),
    ensures
        ({
            let k = w3c_aa_find(p.formatting, p.formatting.len() as int, Tag::A);
            let p1 = if k >= 0 {
                let a = p.formatting[k]->Entry_elem;
                let q = w3c_adoption_agency(p, tt);
                if q.stopped {
                    q
                } else {
                    let kq = w3c_fmt_index(q, a.id);
                    let q1 = if kq >= 0 {
                        w3c_fmt_remove(q, kq)
                    } else {
                        q
                    };
                    let iq = open_index_of(q1, a.id);
                    if iq >= 0 {
                        remove_open_at(q1, iq)
                    } else {
                        q1
                    }
                }
            } else {
                p
            };
            w3c_insert_formatting(reconstruct_formatting(p1), tt) == in_body_start_a(p, tt)
        }),
{
    let f = p.formatting;
    let n = f.len() as int;
    lemma_after_last_marker(f, n);
    assert forall|j: int| after_last_marker(f, n) <= j < f.len() && #[trigger] f[j] is Entry implies is_html(
        f[j]->Entry_elem,
        Tag::A,
    ) == (f[j]->Entry_elem.tag == Tag::A) by {
        assert(fmt_entry_ok(f[j], p.doc.nodes.len()));
    }
    lemma_aa_find_eq_all(f, Tag::A);
    assert(fmt_last_where(f, after_last_marker(f, n), n, |e: Elem| is_html(e, Tag::A)) == w3c_aa_find(f, n, Tag::A));
    if w3c_aa_find(f, n, Tag::A) >= 0 {
        lemma_adoption(p, tt);
    }
}

/// "In body"'s end tags.
proof fn lemma_in_body_end(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        in_body_facts(p, Tok::End(tt)),
        in_body_texts_agree(p, Tok::End(tt)),
        in_body_aa_agrees(p, Tok::End(tt)),
    ensures
        w3c_in_body_end(env, p, tt) == in_body_end_tag(p, Tok::End(tt), tt),
{
    hide(insert_html_element);
    hide(reconstruct_formatting);
    hide(pop_until_popped);
    hide(pop_until_named_popped);
    hide(generate_implied_end_tags);
    hide(w3c_adoption_agency);
    hide(in_body_adoption);
    hide(w3c_any_other_end_tag);
    hide(in_body_any_other_end_tag);
    hide(clear_to_last_marker);
    hide(w3c_in_body_start);
    let g = tt.tag;
    assert(tag_of(name_sarcasm()) == Tag::Other) by (compute_only);
    assert(all_tagged(p.open));
    if w3c_block_end_tag(g) || g == Tag::Applet || g == Tag::Marquee || g == Tag::Object {
        lemma_same_name_in_scope(p, tt);
        lemma_implied_tagged(p, None);
        lemma_pop_until_named(generate_implied_end_tags(p, None), tt);
    } else if g == Tag::Dd || g == Tag::Dt {
        lemma_same_name_in_scope(p, tt);
        lemma_implied_tagged(p, Some(g));
        lemma_pop_until_named(generate_implied_end_tags(p, Some(g)), tt);
    } else if w3c_formatting_end_tag(g) {
        lemma_adoption(p, tt);
    } else if g == Tag::Br {
        lemma_named_tag_names(tt.name, w3c_name_br());
        assert(tag_of(w3c_name_br()) == Tag::Br) by (compute_only);
        lemma_in_body_br_end(env, p, tt);
    }
    lemma_any_other_end_tag(p, tt);
}

/// "In body"'s `br` end tag: as a `br` start tag with no attributes.
proof fn lemma_in_body_br_end(env: EncFns, p: Parser, tt: TagTok)
    requires
        !p.stopped,
        tt.tag == Tag::Br,
        tt.name == w3c_name_br(),
        tag_of(w3c_name_br()) == Tag::Br,
        aa_wf(p),
    ensures
        w3c_in_body_start(env, p, start_tag_named(w3c_name_br())) == Outcome::Done(
            in_body_void_start_tag(p, TagTok { attrs: seq![], ..tt }),
        ),
{
    hide(reconstruct_formatting);
    hide(insert_foreign_element);
    lemma_reconstruct_stopped_empty(p);
    let q = reconstruct_formatting(p);
    lemma_insert_stopped_empty(q, start_tag_named(w3c_name_br()), Namespace::Html);
    lemma_insert_same_token(q, start_tag_named(w3c_name_br()), TagTok { attrs: seq![], ..tt });
}

/// "in body" (W3C §8.2.5.4.7, WHATWG §13.2.6.4.7): the same rules but where
/// the texts differ ([`in_body_texts_agree`]) and where the adoption
/// agency algorithm's insertions differ ([`in_body_aa_agrees`]), given the
/// facts of reachable states [`in_body_facts`]. ("An HTML element with the
/// same tag name as the token" is read as the same [`Tag`] for the entries
/// listing their tags, as in [`super::equivalence::lemma_in_table_body`].)
pub proof fn lemma_in_body(env: EncFns, p: Parser, t: Tok)
    requires
        !p.stopped,
        in_body_facts(p, t),
        in_body_texts_agree(p, t),
        in_body_aa_agrees(p, t),
    ensures
        w3c_mode_in_body(env, p, t) == mode_in_body(env, p, t),
{
    hide(w3c_in_body_start);
    hide(in_body_start_tag);
    hide(w3c_in_body_end);
    hide(in_body_end_tag);
    match t {
        Tok::Start(tt) => lemma_in_body_start(env, p, tt),
        Tok::End(tt) => lemma_in_body_end(env, p, tt),
        _ => {},
    }
}

// ---------------------------------------------------------------------
// §8.2.5.4.9 "in table", §8.2.5.4.10 "in table text"

/// "In body" for a character token: the same rules (no precondition).
pub proof fn lemma_in_body_char(env: EncFns, p: Parser, c: u32)
    ensures
        w3c_mode_in_body(env, p, Tok::Char(c)) == mode_in_body(env, p, Tok::Char(c)),
{
}

/// The stack after inserting an element for a token other than `template`
/// has a `template` element only if it had one.
proof fn lemma_insert_no_template(p: Parser, tt: TagTok)
    requires
        !p.stopped,
        tt.tag != Tag::Template,
        !open_has_html(p, Tag::Template),
    ensures
        !open_has_html(insert_html_element(p, tt).0, Tag::Template),
        insert_html_element(p, tt).0.context == p.context,
{
    let q = insert_html_element(p, tt).0;
    let f = |e: Elem| is_html(e, Tag::Template);
    if !q.stopped {
        let (p1, e) = create_element_for_token(p, tt, Namespace::Html, appropriate_place(p, None).parent);
        assert(q.open == p.open.push(e));
        lemma_liw(q.open, q.open.len() as int, f);
        lemma_liw(p.open, p.open.len() as int, f);
        let r = last_index_where(q.open, q.open.len() as int, f);
        if r >= 0 {
            assert(r != p.open.len());
            assert(q.open[r] == p.open[r]);
            assert(f(p.open[r]));
        }
    } else {
        assert(q.open.len() == 0);
    }
}

/// The "in body" lemma's precondition for a parser with foster parenting
/// enabled: what "in table"'s "anything else" entry needs.
pub open spec fn in_table_body_ok(p: Parser, t: Tok) -> bool {
    let pf = Parser { foster: true, ..p };
    &&& in_body_facts(pf, t)
    &&& in_body_texts_agree(pf, t)
    &&& in_body_aa_agrees(pf, t)
}

/// "In table"'s "anything else" entry (and "in table text"'s use of it).
proof fn lemma_in_table_anything_else(env: EncFns, p: Parser, t: Tok)
    requires
        !p.stopped,
        !(t is Pi),
        in_table_body_ok(p, t),
        place_stable(p),
    ensures
        w3c_in_table_anything_else(env, p, t) == in_table_anything_else(env, p, t),
{
    let pf = Parser { foster: true, ..p };
    lemma_in_body(env, pf, t);
    match mode_in_body(env, pf, t) {
        Outcome::Using(m, q, t2) => {
            if m == Mode::InHead && !q.stopped && !(t2 is Pi) && place_stable(q) {
                lemma_in_head(env, q, t2);
            }
        },
        _ => {},
    }
    lemma_in_table_anything_else_using(env, p, t);
}

/// "In body" hands the "in head" rules the token unchanged, on the parser
/// it was given (its `base`, …, `title` entry).
proof fn lemma_in_table_anything_else_using(env: EncFns, p: Parser, t: Tok)
    requires
        !p.stopped,
        !(t is Pi),
        place_stable(p),
    ensures
        match mode_in_body(env, Parser { foster: true, ..p }, t) {
            Outcome::Using(m, q, t2) => m == Mode::InHead ==> q == (Parser { foster: true, ..p }) && t2 == t && !(t2 is Pi)
                && place_stable(q),
            _ => true,
        },
{
    hide(in_body_end_tag);
    hide(in_body_char);
    hide(in_body_eof);
    hide(in_body_start_html);
    hide(in_body_start_body);
    hide(in_body_start_frameset);
    hide(in_body_start_heading);
    hide(in_body_start_pre);
    hide(in_body_start_form);
    hide(in_body_start_li);
    hide(in_body_start_dd_dt);
    hide(in_body_start_button);
    hide(in_body_start_a);
    hide(in_body_start_nobr);
    hide(in_body_void_start_tag);
    hide(in_body_start_input);
    hide(in_body_start_hr);
    hide(in_body_start_textarea);
    hide(in_body_start_select);
    hide(in_body_start_option);
    hide(in_body_start_optgroup);
    hide(in_body_start_math);
    hide(in_body_start_svg);
    hide(insert_html_element);
    hide(reconstruct_formatting);
    hide(generic_text_parsing);
    if t is End {
        reveal(in_body_end_tag);
    } else if t is Eof {
        reveal(in_body_eof);
    }
}

/// The current node is not a `template` element (the WHATWG "in table"
/// also sends characters to "in table text" when it is; the W3C does not).
pub open spec fn in_table_texts_agree(p: Parser, t: Tok) -> bool {
    &&& !(t is Pi)
    &&& t is Char ==> !is_html(current_node(p), Tag::Template)
    &&& w3c_start(t, Tag::Form) ==> !parsing_template_contents(p)
}

/// "in table" (W3C §8.2.5.4.9, WHATWG §13.2.6.4.9): the same rules, but
/// for two differences ([`in_table_texts_agree`]):
/// - The WHATWG sends a character token to "in table text" also when the
///   current node is a `template` element; the W3C applies "anything
///   else". Excluded.
/// - For a `form` start tag, the WHATWG ignores the token when the form
///   element pointer is set and the parser is not parsing template
///   contents, and otherwise inserts the form; the W3C ignores it when
///   there is a `template` element on the stack or the pointer is set.
///   They agree when the parser is not parsing template contents:
///   excluded otherwise.
/// "Anything else" runs the "in body" rules with foster parenting enabled,
/// so their lemma's precondition is required for that parser
/// ([`in_table_body_ok`]), with [`place_stable`] for the "in head" rules
/// they hand some tokens to.
pub proof fn lemma_in_table(env: EncFns, p: Parser, t: Tok)
    requires
        !p.stopped,
        in_table_texts_agree(p, t),
        place_stable(p),
        in_table_body_ok(p, t),
    ensures
        w3c_mode_in_table(env, p, t) == mode_in_table(env, p, t),
{
    hide(w3c_in_table_anything_else);
    hide(in_table_anything_else);
    hide(insert_html_element);
    hide(pop_until_popped);
    hide(reset_insertion_mode);
    hide(pop_while);
    lemma_in_table_anything_else(env, p, t);
    super::equivalence::lemma_closure_ext();
    if w3c_start(t, Tag::Input) {
        lemma_insert_stopped_empty(p, t->Start_0, Namespace::Html);
    }
    if w3c_start(t, Tag::Form) && p.form is None {
        lemma_insert_no_template(p, t->Start_0);
    }
}

/// The WHATWG transcription's test for a non-whitespace character and
/// the W3C's (not all space characters) agree.
proof fn lemma_all_space(s: Seq<u32>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        w3c_all_space(s, i) == !(exists|j: int| i <= j < s.len() && !is_ascii_whitespace(#[trigger] s[j])),
    decreases s.len() - i,
{
    if i < s.len() {
        lemma_all_space(s, i + 1);
        if exists|j: int| i <= j < s.len() && !is_ascii_whitespace(#[trigger] s[j]) {
            let j = choose|j: int| i <= j < s.len() && !is_ascii_whitespace(#[trigger] s[j]);
            if j > i {
                assert(i + 1 <= j);
            }
        }
    }
}

/// "Reprocess the character tokens in the pending table character tokens
/// list using the rules given in the "anything else" entry in the "in
/// table" insertion mode": the same in both.
proof fn lemma_reprocess_table_text(env: EncFns, p: Parser, s: Seq<u32>, i: int)
    ensures
        w3c_reprocess_table_text(env, p, s, i) == reprocess_pending(env, p, s, i),
    decreases s.len() - i,
{
    if 0 <= i < s.len() {
        let pf = Parser { foster: true, ..p };
        lemma_in_body_char(env, pf, s[i]);
        let q = outcome_parser(in_table_anything_else(env, p, Tok::Char(s[i])));
        lemma_reprocess_table_text(env, q, s, i + 1);
    }
}

/// "in table text" (W3C §8.2.5.4.10, WHATWG §13.2.6.4.10): the same rules,
/// but for one difference: when the pending table character tokens list
/// is empty (every character since "in table" was U+0000), "insert the
/// characters" of the empty list, read literally, creates an empty `Text`
/// node; the WHATWG transcription inserts nothing (docs/ERRATA.md). The
/// W3C text is taken literally here: excluded.
pub proof fn lemma_in_table_text(env: EncFns, p: Parser, t: Tok)
    requires
        !(t is Pi),
        !p.stopped,
        !(t is Char) ==> p.pending_table_text.len() > 0,
    ensures
        w3c_mode_in_table_text(env, p, t) == mode_in_table_text(env, p, t),
{
    let s = p.pending_table_text;
    lemma_all_space(s, 0);
    lemma_reprocess_table_text(env, p, s, 0);
}

} // verus!
