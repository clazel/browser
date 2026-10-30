//! HTML §13.2.6.4.7 the "in body" insertion mode: the end tag cases
//! (`spec/modes/in_body.rs`, [`in_body_end_tag`] and its case functions)
//! and "close a p element", over [`ParserBuf`], each proven equal to its
//! spec function and to keep [`parser_inv`].

use super::super::formatting::*;
#[cfg(verus_only)]
use super::super::frame::*;
use super::super::insert::*;
use super::super::names::*;
use super::super::stack::*;
use super::super::types::*;
use super::in_body_start_cases::*;
#[cfg(verus_only)]
use super::in_body_start_lemmas::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use clazel_dom::exec::attrs_view;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Helpers

/// [`pop_until_named_popped`] is [`pop_until_where`].
proof fn lemma_pop_until_named_popped(p: Parser, name: Seq<u32>)
    ensures
        pop_until_named_popped(p, name) == pop_until_where(p, |e: Elem| e.ns == Namespace::Html && e.name == name),
    decreases p.open.len(),
{
    if p.open.len() > 0 && !is_html_named(current_node(p), name) {
        lemma_pop_until_named_popped(pop(p), name);
    }
}

/// [`pop_until_named_popped`].
pub fn pop_until_named_popped_exec(p: &mut ParserBuf, name: &[u32])
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == pop_until_named_popped(old(p)@, name@),
        parser_inv(final(p)@),
{
    let ghost f = |e: Elem| e.ns == Namespace::Html && e.name == name@;
    proof {
        lemma_pop_until_named_popped(old(p)@, name@);
    }
    pop_until_where_exec(p, &ElemPred::HtmlName(name), Ghost(f));
}

/// [`has_same_name_in_scope`].
pub fn has_same_name_in_scope_exec(p: &ParserBuf, tt: &ExecTagTok) -> (r: bool)
    ensures
        r == has_same_name_in_scope(p@, tt@),
{
    let ghost f = |e: Elem| is_html_named(e, tt@.name);
    in_scope_exec(p, &ElemPred::HtmlName(tt.name.as_slice()), Ghost(f), &Scope::Default)
}

/// Only "template" is classified as `template`.
proof fn lemma_tag_of_template(n: Seq<u32>)
    requires
        tag_of(n) == Tag::Template,
    ensures
        n.len() == 8,
{
}

// ---------------------------------------------------------------------
// The cases

/// Case 22 ([`in_body_end_same_name`]).
pub fn in_body_end_same_name_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == in_body_end_same_name(old(p)@, tt@),
        parser_inv(final(p)@),
{
    if !has_same_name_in_scope_exec(p, tt) {
        return ;
    }
    // 1. "Generate implied end tags."
    generate_implied_end_tags_exec(p, None);
    // 3. "Pop elements … until an HTML element with the same tag name as the
    // token has been popped from the stack."
    pop_until_named_popped_exec(p, tt.name.as_slice());
}

/// Case 23, "An end tag whose tag name is "form"" ([`in_body_end_form`]).
pub fn in_body_end_form_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == in_body_end_form(old(p)@),
        parser_inv(final(p)@),
{
    if !parsing_template_contents_exec(p) {
        // 1. "Let node be the element that the form element pointer is set
        // to."
        let node = p.form;
        // 2. "Set the form element pointer to null."
        p.form = None;
        proof {
            lemma_inv_iff(old(p)@);
            lemma_inv_iff(p@);
        }
        if let Some(n) = node {
            if !has_node_in_scope_exec(p, n, &Scope::Default) {
                // 3. "return and ignore the token."
                return ;
            }
            // 4. "Generate implied end tags."
            generate_implied_end_tags_exec(p, None);
            // 6. "Remove node from the stack of open elements."
            if let Some(j) = open_index_of_exec(p, n) {
                remove_open_at_exec(p, j);
            }
        }
    } else if !has_in_scope_exec(p, Tag::Form, &Scope::Default) {
        // "Otherwise:" 1. "return and ignore the token."
    } else {
        // 2. "Generate implied end tags." 4. "Pop elements … until a form
        // element has been popped from the stack."
        generate_implied_end_tags_exec(p, None);
        pop_until_popped_exec(p, Tag::Form);
    }
}

/// Case 55's step 2 for node at index `i`, an HTML element with the
/// token's tag name: 2.1 "Generate implied end tags, except for HTML
/// elements with the same tag name as the token." 2.3 "Pop all the nodes
/// from the current node up to node, including node, then stop these
/// steps."
fn any_other_hit_exec(p: &mut ParserBuf, tt: &ExecTagTok, i: usize)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Html,
        i < old(p)@.open.len(),
        is_html_named(old(p)@.open[i as int], tt@.name),
    ensures
        final(p)@ == pop_until_node_popped(generate_implied_end_tags(old(p)@, Some(tt@.tag)), old(p)@.open[i as int].id),
        parser_inv(final(p)@),
        final(p)@.stopped || stack_rooted(final(p)@),
        final(p)@.doc == old(p)@.doc,
{
    hide(tag_of);
    hide(dom::wf);
    let ghost p0 = p@;
    let id = match p.open.get(i) {
        Some(e) => e.id,
        None => vstd::pervasive::unreached(),
    };
    proof {
        lemma_inv_iff(p0);
        assert(elem_ok(p0.doc, p0.open[i as int]));
        if i == 0 && !p0.stopped {
            assert(is_html(p0.open[0], Tag::Html));
        }
        let f = implied_pred(Some(tt@.tag));
        assert(generate_implied_end_tags(p0, Some(tt@.tag)) == pop_while(p0, f));
        lemma_pop_while_prefix(p0, f);
        assert(!f(p0.open[i as int]));
    }
    generate_implied_end_tags_exec(p, Some(copy_tag(&tt.tag)));
    let ghost q = p@;
    let ghost g = |e: Elem| e.id == id;
    proof {
        assert(q.open[i as int] == p0.open[i as int]);
        lemma_pop_until_node_popped(q, id);
        lemma_pop_until_where_prefix(q, g);
        lemma_last_index_where_found(q.open, q.open.len() as int, g, i as int);
    }
    pop_until_node_popped_exec(p, id);
    proof {
        if !p0.stopped {
            assert(p@.open[0] == q.open[0]);
            assert(q.open[0] == p0.open[0]);
        }
    }
}

/// Case 55, "Any other end tag" ([`in_body_any_other_end_tag`], with
/// [`any_other_end_tag_loop`] as a loop over the stack index).
pub fn in_body_any_other_end_tag_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Html,
    ensures
        final(p)@ == in_body_any_other_end_tag(old(p)@, tt@),
        parser_inv(final(p)@),
        final(p)@.stopped || stack_rooted(final(p)@),
        final(p)@.doc == old(p)@.doc,
{
    hide(tag_of);
    hide(parser_inv);
    hide(generate_implied_end_tags);
    hide(pop_until_node_popped);
    let ghost p0 = p@;
    // 1. "Initialize node to be the current node."
    let n = p.open.len();
    if n == 0 {
        return ;
    }
    let mut i: usize = n.saturating_sub(1);
    loop
        invariant
            p@ == p0,
            p0 == old(p)@,
            parser_inv(p0),
            p0.stopped || stack_rooted(p0),
            tok_tagged(tt@),
            tt@.tag != Tag::Html,
            i < p0.open.len(),
            any_other_end_tag_loop(p0, tt@, p0.open.len() - 1) == any_other_end_tag_loop(p0, tt@, i as int),
        decreases i,
    {
        let node = match p.open.get(i) {
            Some(e) => e,
            None => vstd::pervasive::unreached(),
        };
        proof {
            assert(node@ == p0.open[i as int]);
        }
        if is_html_ns(node) && u32s_eq(node.name.as_slice(), tt.name.as_slice()) {
            // 2.
            any_other_hit_exec(p, tt, i);
            return ;
        }
        if is_special_exec(node) {
            // 3. "Otherwise, if node is in the special category, then this is
            // a parse error; ignore the token, and return."
            return ;
        }
        // 4. "Set node to the previous entry in the stack of open elements."
        if i == 0 {
            proof {
                assert(any_other_end_tag_loop(p0, tt@, -1) == p0);
            }
            return ;
        }
        i = i.saturating_sub(1);
    }
}

/// Case 24's "insert an HTML element for a "p" start tag token with no
/// attributes".
fn insert_p_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
    ensures
        final(p)@ == insert_html_element(old(p)@, start_tag_named(name_p())).0,
        parser_inv(final(p)@),
{
    let l: &[u32] = &[0x70u32];
    proof {
        assert(l@ =~= name_p());
    }
    let name = copy_str(l);
    let tag = tag_of_exec(name.as_slice());
    let tok = ExecTagTok { name, tag, attrs: Vec::new(), self_closing: false };
    proof {
        assert(tok.name@ =~= name_p());
        if tag == Tag::Template {
            lemma_tag_of_template(name_p());
        }
        assert(attrs_view(tok.attrs@) =~= Seq::<Attr>::empty());
        assert(tok@ == start_tag_named(name_p()));
    }
    let _ = insert_html_element_exec(p, &tok);
}

/// "Switch the insertion mode to "after body"."
fn to_after_body_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == (Parser { mode: Mode::AfterBody, ..old(p)@ }),
        parser_inv(final(p)@),
{
    p.mode = Mode::AfterBody;
    proof {
        lemma_inv_iff(old(p)@);
        lemma_inv_iff(p@);
    }
}

/// The end tag cases, in the standard's order ([`in_body_end_tag`]); `tt`
/// is the end tag token (the spec's `t` is `Tok::End(tt)`).
pub fn in_body_end_tag_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, tt: ExecTagTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        tok_tagged(tt@),
    ensures
        outcome_view(o, final(p)@) == in_body_end_tag(old(p)@, Tok::End(tt@), tt@),
        parser_inv(final(p)@),
{
    hide(tag_of);
    hide(parser_inv);
    hide(insert_html_element);
    hide(generate_implied_end_tags);
    hide(in_body_adoption);
    hide(in_body_any_other_end_tag);
    hide(in_body_void_start_tag);
    hide(in_body_end_same_name);
    hide(in_body_end_form);
    hide(close_p_element);
    hide(has_in_scope);
    hide(has_same_name_in_scope);
    hide(has_heading_in_scope);
    hide(pop_until_popped);
    hide(pop_until_named_popped);
    hide(pop_until_heading_popped);
    hide(clear_to_last_marker);
    hide(dom::wf);
    match tt.tag {
        Tag::Template => {
            // 8. "Process the token using the rules for the "in head"
            // insertion mode."
            return ExecOutcome::Using(Mode::InHead, ExecTok::End(tt));
        },
        Tag::Body => {
            // 12.
            if has_in_scope_exec(p, Tag::Body, &Scope::Default) {
                // "Switch the insertion mode to "after body"."
                to_after_body_exec(p);
            }
            return ExecOutcome::Done;
        },
        Tag::Html => {
            // 13.
            if has_in_scope_exec(p, Tag::Body, &Scope::Default) {
                // "Switch the insertion mode to "after body"." "Reprocess the
                // token."
                to_after_body_exec(p);
                return ExecOutcome::Reprocess(ExecTok::End(tt));
            }
            return ExecOutcome::Done;
        },
        Tag::Address | Tag::Article | Tag::Aside | Tag::Blockquote | Tag::Button | Tag::Center | Tag::Details | Tag::Dialog
        | Tag::Dir | Tag::Div | Tag::Dl | Tag::Fieldset | Tag::Figcaption | Tag::Figure | Tag::Footer | Tag::Header
        | Tag::Hgroup | Tag::Listing | Tag::Main | Tag::Menu | Tag::Nav | Tag::Ol | Tag::Pre | Tag::Search | Tag::Section
        | Tag::Select | Tag::Summary | Tag::Ul => {
            // 22.
            in_body_end_same_name_exec(p, &tt);
            return ExecOutcome::Done;
        },
        Tag::Form => {
            // 23.
            in_body_end_form_exec(p);
            return ExecOutcome::Done;
        },
        Tag::P => {
            // 24. "If the stack of open elements does not have a p element in
            // button scope, then this is a parse error; insert an HTML element
            // for a "p" start tag token with no attributes. Close a p element."
            if !has_in_scope_exec(p, Tag::P, &Scope::Button) {
                insert_p_exec(p);
            }
            close_p_element_exec(p);
            return ExecOutcome::Done;
        },
        Tag::Li => {
            // 25.
            if has_in_scope_exec(p, Tag::Li, &Scope::ListItem) {
                // 1. "Generate implied end tags, except for li elements." 3.
                // "Pop elements … until an li element has been popped."
                generate_implied_end_tags_exec(p, Some(Tag::Li));
                pop_until_popped_exec(p, Tag::Li);
            }
            return ExecOutcome::Done;
        },
        Tag::Dd | Tag::Dt => {
            // 26.
            if has_same_name_in_scope_exec(p, &tt) {
                // 1. "Generate implied end tags, except for HTML elements with
                // the same tag name as the token." 3. "Pop elements … until an
                // HTML element with the same tag name as the token has been
                // popped from the stack."
                generate_implied_end_tags_exec(p, Some(copy_tag(&tt.tag)));
                pop_until_named_popped_exec(p, tt.name.as_slice());
            }
            return ExecOutcome::Done;
        },
        Tag::H1 | Tag::H2 | Tag::H3 | Tag::H4 | Tag::H5 | Tag::H6 => {
            // 27.
            if has_heading_in_scope_exec(p) {
                // 1. "Generate implied end tags." 3. "Pop elements … until an
                // HTML element whose tag name is one of "h1", …, "h6" has been
                // popped from the stack."
                generate_implied_end_tags_exec(p, None);
                pop_until_heading_popped_exec(p);
            }
            return ExecOutcome::Done;
        },
        _ => {},
    }
    let sarcasm: &[u32] = &[0x73u32, 0x61, 0x72, 0x63, 0x61, 0x73, 0x6d];
    proof {
        assert(sarcasm@ =~= name_sarcasm());
    }
    if u32s_eq(tt.name.as_slice(), sarcasm) {
        // 28. "Take a deep breath, then act as described in the "any other
        // end tag" entry below."
        in_body_any_other_end_tag_exec(p, &tt);
        return ExecOutcome::Done;
    }
    match tt.tag {
        Tag::A | Tag::B | Tag::Big | Tag::Code | Tag::Em | Tag::Font | Tag::I | Tag::Nobr | Tag::S | Tag::Small
        | Tag::Strike | Tag::Strong | Tag::Tt | Tag::U => {
            // 32. "Run the adoption agency algorithm for the token."
            in_body_adoption_exec(env, p, &tt);
            ExecOutcome::Done
        },
        Tag::Applet | Tag::Marquee | Tag::Object => {
            // 34.
            if has_same_name_in_scope_exec(p, &tt) {
                // 1. "Generate implied end tags." 3. "Pop elements … until an
                // HTML element with the same tag name as the token has been
                // popped from the stack." 4. "Clear the list of active
                // formatting elements up to the last marker."
                generate_implied_end_tags_exec(p, None);
                pop_until_named_popped_exec(p, tt.name.as_slice());
                clear_to_last_marker_exec(p);
            }
            ExecOutcome::Done
        },
        Tag::Br => {
            // 36. "Drop the attributes from the token, and act as described in
            // the next entry."
            let tok = ExecTagTok { name: tt.name, tag: Tag::Br, attrs: Vec::new(), self_closing: tt.self_closing };
            proof {
                assert(attrs_view(tok.attrs@) =~= Seq::<Attr>::empty());
                assert(tok@ == (TagTok { attrs: seq![], ..tt@ }));
            }
            in_body_void_start_tag_exec(p, &tok);
            ExecOutcome::Done
        },
        _ => {
            // 55. "Any other end tag"
            in_body_any_other_end_tag_exec(p, &tt);
            ExecOutcome::Done
        },
    }
}

} // verus!
