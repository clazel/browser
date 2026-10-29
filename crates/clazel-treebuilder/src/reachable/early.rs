//! The rules of "initial", "before html", "before head", "in head", "in
//! head noscript", "after head" and "text" keep the reachable-state facts
//! ([`next_core`], see [`super`]).

#[cfg(verus_only)]
use super::cells::*;
#[cfg(verus_only)]
use super::helpers::*;
#[cfg(verus_only)]
use super::lists::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Changes of the document only

/// "Insert a comment" changes only the document (growing it), or stops.
pub proof fn lemma_comment_frame(p: Parser, data: Seq<u32>, loc: Option<Location>)
    ensures
        insert_comment(p, data, loc).stopped || (insert_comment(p, data, loc) == (Parser {
            doc: insert_comment(p, data, loc).doc,
            ..p
        }) && insert_comment(p, data, loc).doc.nodes.len() >= p.doc.nodes.len()),
{
    let l = adjusted_location(p, loc);
    let (p1, c) = create(p, NodeKind::Comment { data });
    lemma_insert_len(p1.doc, c, l.parent, l.child);
}

/// "Insert a processing instruction" changes only the document, or stops.
pub proof fn lemma_pi_frame(p: Parser, target: Seq<u32>, data: Seq<u32>, loc: Option<Location>)
    ensures
        insert_pi(p, target, data, loc).stopped || (insert_pi(p, target, data, loc) == (Parser {
            doc: insert_pi(p, target, data, loc).doc,
            ..p
        }) && insert_pi(p, target, data, loc).doc.nodes.len() >= p.doc.nodes.len()),
{
    let l = adjusted_location(p, loc);
    let (p1, n) = create(p, NodeKind::ProcessingInstruction { target, data });
    lemma_insert_len(p1.doc, n, l.parent, l.child);
}

/// The DOCTYPE of the "initial" mode changes only the document, or stops.
pub proof fn lemma_initial_doctype_frame(
    p: Parser,
    name: Option<Seq<u32>>,
    public_id: Option<Seq<u32>>,
    system_id: Option<Seq<u32>>,
    force_quirks: bool,
)
    ensures
        ({
            let q = initial_doctype(p, name, public_id, system_id, force_quirks);
            p.doc.nodes.len() > 0 ==> q.stopped || (q == (Parser { doc: q.doc, mode: Mode::BeforeHtml, ..p })
                && q.doc.nodes.len() >= p.doc.nodes.len())
        }),
{
    let k = NodeKind::DocumentType { name: or_empty(name), public_id: or_empty(public_id), system_id: or_empty(system_id) };
    let (p1, doctype) = create(p, k);
    lemma_insert_len(p1.doc, doctype, 0, None);
}

/// A parser whose document changed (growing), or that stopped, keeps
/// [`reach_core`] and `modes_ok`.
pub proof fn lemma_doc_only(p: Parser, q: Parser)
    requires
        reach_core(p),
        modes_ok(p),
        q.stopped || (q == (Parser { doc: q.doc, ..p }) && q.doc.nodes.len() >= p.doc.nodes.len()),
    ensures
        q.stopped || (reach_core(q) && modes_ok(q)),
{
    if !q.stopped {
        lemma_core_frame(p, q);
    }
}

// ---------------------------------------------------------------------
// "initial" and "before html"

/// The "initial" rules.
pub proof fn lemma_initial_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::Initial), p, t),
    ensures
        next_core(mode_initial(env, p, t)),
{
    if t is Comment {
        lemma_comment_frame(p, t->Comment_0, Some(document_location()));
        lemma_doc_only(p, insert_comment(p, t->Comment_0, Some(document_location())));
    } else if t is Pi {
        lemma_pi_frame(p, t->Pi_0, t->Pi_1, Some(document_location()));
        lemma_doc_only(p, insert_pi(p, t->Pi_0, t->Pi_1, Some(document_location())));
    } else if t is Doctype {
        lemma_initial_doctype_frame(p, t->Doctype_name, t->Doctype_public_id, t->Doctype_system_id, t->Doctype_force_quirks);
        let p1 = Parser { mode: Mode::BeforeHtml, ..p };
        lemma_doc_only(
            p1,
            initial_doctype(p, t->Doctype_name, t->Doctype_public_id, t->Doctype_system_id, t->Doctype_force_quirks),
        );
    }
}

/// The `html` element "before html" creates and pushes.
pub proof fn lemma_before_html_push(p: Parser, tt: TagTok)
    requires
        reach_core(p),
        modes_ok(p),
        p.mode == Mode::BeforeHtml,
        !p.stopped,
        tok_tagged(tt),
        tt.tag == Tag::Html,
    ensures
        ({
            let (p1, e) = create_element_for_token(p, tt, Namespace::Html, 0);
            let p2 = insert_element_at(p1, e.id, Some(document_location()));
            let q = Parser { mode: Mode::BeforeHead, ..push(p2, e) };
            q.stopped || (reach_core(q) && modes_ok(q))
        }),
{
    let (p1, e) = create_element_for_token(p, tt, Namespace::Html, 0);
    let p2 = insert_element_at(p1, e.id, Some(document_location()));
    let l = adjusted_location(p1, Some(document_location()));
    lemma_insert_len(p1.doc, e.id, l.parent, l.child);
    let q = Parser { mode: Mode::BeforeHead, ..push(p2, e) };
    if !q.stopped {
        let k = NodeKind::Element {
            namespace: Some(Namespace::Html),
            prefix: None,
            local_name: tt.name,
            attributes: tt.attrs,
            template_contents: None,
            form_owner: None,
        };
        assert(!is_form_associated(Namespace::Html, Tag::Html));
        assert(q.open == seq![e]);
        assert(e.id as int == p.doc.nodes.len());
        assert(q.open[0] == e);
        assert(crate::termination::templates_in(q.open, 1) == crate::termination::templates_in(q.open, 0));
        assert(rooted_seq(q.open));
        assert(root_ids(q));
        assert(tags_wf(q));
    }
}

/// The "before html" rules.
pub proof fn lemma_before_html_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::BeforeHtml), p, t),
    ensures
        next_core(mode_before_html(env, p, t)),
{
    if t is Comment {
        lemma_comment_frame(p, t->Comment_0, Some(document_location()));
        lemma_doc_only(p, insert_comment(p, t->Comment_0, Some(document_location())));
    } else if t is Pi {
        lemma_pi_frame(p, t->Pi_0, t->Pi_1, Some(document_location()));
        lemma_doc_only(p, insert_pi(p, t->Pi_0, t->Pi_1, Some(document_location())));
    } else if t is Doctype || (t is Char && is_ascii_whitespace(t->Char_0)) {
    } else if t is Start && t->Start_0.tag == Tag::Html {
        lemma_before_html_push(p, t->Start_0);
    } else if t is End && !(t->End_0.tag == Tag::Head || t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Html
        || t->End_0.tag == Tag::Br) {
    } else {
        let tt = start_tag_named(seq![0x68u32, 0x74, 0x6d, 0x6c]);
        assert(tag_of(seq![0x68u32, 0x74, 0x6d, 0x6c]) == Tag::Html) by (compute);
        lemma_before_html_push(p, tt);
    }
}

// ---------------------------------------------------------------------
// "before head"

/// Insert the `head` element and switch to "in head".
pub proof fn lemma_insert_head(p: Parser, tt: TagTok)
    requires
        reach_core(p),
        modes_ok(p),
        p.mode == Mode::BeforeHead,
        !p.stopped,
        tok_tagged(tt),
        tt.tag == Tag::Head,
    ensures
        ({
            let (p1, e) = insert_html_element(p, tt);
            let q = Parser { head: Some(e.id), mode: Mode::InHead, ..p1 };
            q.stopped || (reach_core(q) && modes_ok(q))
        }),
{
    lemma_insert_html_keeps(p, tt);
    let (p1, e) = insert_html_element(p, tt);
    let q = Parser { head: Some(e.id), mode: Mode::InHead, ..p1 };
    if !q.stopped {
        lemma_html_above_push(p.open, e);
        crate::termination::helpers_ranking::lemma_modes_ok_from(p, q);
    }
}

/// The "before head" rules.
pub proof fn lemma_before_head_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::BeforeHead), p, t),
    ensures
        next_core(mode_before_head(env, p, t)),
{
    assert(good(p));
    if t is Char && is_ascii_whitespace(t->Char_0) {
    } else if t is Comment {
        lemma_insert_comment_keeps(p, t->Comment_0, None);
        let q = insert_comment(p, t->Comment_0, None);
        if !q.stopped {
            lemma_core_frame(p, q);
        }
    } else if t is Pi {
        lemma_insert_pi_keeps(p, t->Pi_0, t->Pi_1, None);
        let q = insert_pi(p, t->Pi_0, t->Pi_1, None);
        if !q.stopped {
            lemma_core_frame(p, q);
        }
    } else if t is Doctype {
    } else if t is Start && t->Start_0.tag == Tag::Html {
    } else if t is Start && t->Start_0.tag == Tag::Head {
        lemma_insert_head(p, t->Start_0);
    } else if t is End && !(t->End_0.tag == Tag::Head || t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Html
        || t->End_0.tag == Tag::Br) {
    } else {
        let tt = start_tag_named(seq![0x68u32, 0x65, 0x61, 0x64]);
        assert(tag_of(seq![0x68u32, 0x65, 0x61, 0x64]) == Tag::Head) by (compute);
        lemma_insert_head(p, tt);
    }
}

// ---------------------------------------------------------------------
// "in head"

/// A parser whose rules are not before the `html` element, nor "text" or
/// "in table text", has a stack of its mode's [`shape0`].
pub proof fn lemma_shape_mode(p: Parser)
    requires
        shape(p),
        p.mode != Mode::Text,
        p.mode != Mode::InTableText,
    ensures
        shape0(p.mode, p.open),
{
}

/// The generic text parsing algorithms: "text" over the current mode,
/// with an HTML element pushed onto a stack of the mode's shape.
pub proof fn lemma_generic_text_reach(p: Parser, tt: TagTok, rawtext: bool)
    requires
        good(p),
        !p.stopped,
        modes_ok(p),
        shape0(p.mode, p.open),
        p.mode != Mode::Text && p.mode != Mode::InTableText,
        tok_tagged(tt),
        tt.tag != Tag::Template,
        tt.tag != Tag::Td && tt.tag != Tag::Th,
        tt.tag != Tag::Html && tt.tag != Tag::Table,
    ensures
        next_core(Outcome::Done(generic_text_parsing(p, tt, rawtext))),
{
    lemma_insert_html_keeps(p, tt);
    let (p1, e) = insert_html_element(p, tt);
    let q = generic_text_parsing(p, tt, rawtext);
    if !q.stopped {
        assert(q.open == p.open.push(e));
        assert(q.open.drop_last() == p.open);
        crate::termination::helpers_ranking::lemma_modes_ok_from(p, q);
    }
}

/// The "in head" `script` start tag: as the generic text parsing
/// algorithms, in the script data state.
pub proof fn lemma_in_head_script_reach(p: Parser, tt: TagTok)
    requires
        good(p),
        !p.stopped,
        modes_ok(p),
        shape0(p.mode, p.open),
        p.mode != Mode::Text && p.mode != Mode::InTableText,
        tok_tagged(tt),
        tt.tag == Tag::Script,
    ensures
        next_core(Outcome::Done(in_head_script(p, tt))),
{
    lemma_insert_html_keeps(p, tt);
    let (p1, e) = insert_html_element(p, tt);
    assert(in_head_script(p, tt) == Parser {
        tokenizer: Some(TokenizerState::ScriptData),
        original_mode: p1.mode,
        mode: Mode::Text,
        ..p1
    });
    let q = in_head_script(p, tt);
    if !q.stopped {
        assert(q.open == p.open.push(e));
        assert(q.open.drop_last() == p.open);
        crate::termination::helpers_ranking::lemma_modes_ok_from(p, q);
    }
}

/// Pushing an HTML `template` element counts one more `template`.
pub proof fn lemma_tcount_push_template(o: Seq<Elem>, e: Elem)
    ensures
        crate::termination::helpers_ranking::tcount(o.push(e)) <= crate::termination::helpers_ranking::tcount(o) + 1,
{
    let b = o.push(e);
    crate::termination::helpers_ranking::lemma_templates_in_same(o, b, o.len() as int);
}

/// The "in head" `template` start tag.
pub proof fn lemma_in_head_template_start_reach(p: Parser, tt: TagTok)
    requires
        good(p),
        !p.stopped,
        modes_ok(p),
        shape0(p.mode, p.open),
        p.mode != Mode::Initial && p.mode != Mode::BeforeHtml,
        tok_tagged(tt),
        tt.tag == Tag::Template,
    ensures
        next_core(Outcome::Done(in_head_template_start(p, tt))),
{
    hide(create_element_for_token);
    hide(insert_element_at);
    let p1 = push_marker(p);
    lemma_push_marker_keeps(p);
    let p2 = Parser { frameset_ok: false, mode: Mode::InTemplate, template_modes: p1.template_modes.push(Mode::InTemplate), ..p1 };
    assert(good(p2));
    lemma_ceft_keeps(p2, tt, Namespace::Html, appropriate_place(p2, None).parent);
    let (p3, template) = create_element_for_token(p2, tt, Namespace::Html, appropriate_place(p2, None).parent);
    let insertion_location = appropriate_place(p3, None);
    let p4 = push(p3, template);
    let q = insert_element_at(p4, template.id, Some(insertion_location));
    lemma_insert_element_at_keeps(p4, template.id, Some(insertion_location));
    if !q.stopped {
        assert(!p4.stopped);
        assert(p4.open == p.open.push(template));
        assert(q.open == p4.open);
        assert(q.open[0] == p.open[0]);
        assert(elem_tagged(template));
        assert forall|i: int| 0 <= i < q.open.len() implies elem_tagged(#[trigger] q.open[i]) by {
            if i < p.open.len() {
                assert(q.open[i] == p.open[i]);
            }
        }
        assert(good(q));
        lemma_tcount_push_template(p.open, template);
        crate::termination::helpers_ranking::lemma_template_count(p);
        crate::termination::helpers_ranking::lemma_template_count(q);
        assert(q.template_modes == p.template_modes.push(Mode::InTemplate));
        assert forall|i: int| 0 <= i < q.template_modes.len() implies crate::termination::template_mode_ok(#[trigger] q.template_modes[i]) by {
            if i < p.template_modes.len() {
                assert(q.template_modes[i] == p.template_modes[i]);
            }
        }
        assert(modes_ok(q));
    }
}

/// The "in head" `template` end tag (proven on the parser put in the "in
/// body" mode: in the "in cell" mode it pops the cell, and the mode is
/// reset).
pub proof fn lemma_in_head_template_end_reach(p: Parser)
    requires
        reach_core(p),
        good(p),
        !p.stopped,
        modes_ok(p),
    ensures
        next_core(Outcome::Done(in_head_template_end(p))),
{
    if !open_has_html(p, Tag::Template) {
        return;
    }
    let p0 = mode_as(p, Mode::InBody);
    assert(good(p0));
    lemma_in_head_template_end_reach0(p0);
    let ft = |e: Elem|
        e.ns == Namespace::Html && match e.tag {
            Tag::Caption | Tag::Colgroup | Tag::Dd | Tag::Dt | Tag::Li | Tag::Optgroup | Tag::Option | Tag::P | Tag::Rb
            | Tag::Rp | Tag::Rt | Tag::Rtc | Tag::Tbody | Tag::Td | Tag::Tfoot | Tag::Th | Tag::Thead | Tag::Tr => true,
            _ => false,
        };
    let p1 = generate_all_implied_end_tags_thoroughly(p);
    assert(p1 == pop_while(p, ft));
    assert(generate_all_implied_end_tags_thoroughly(p0) == pop_while(p0, ft));
    lemma_pop_while_mode(p, ft, Mode::InBody);
    let f = |e: Elem| is_html(e, Tag::Template);
    crate::exec::stack::lemma_pop_until_popped(p1, Tag::Template);
    crate::exec::stack::lemma_pop_until_popped(mode_as(p1, Mode::InBody), Tag::Template);
    lemma_pop_until_where_mode(p1, f, Mode::InBody);
    let p2 = pop_until_popped(p1, Tag::Template);
    lemma_clear_mode(p2, Mode::InBody);
    let p3 = clear_to_last_marker(p2);
    let p4 = Parser { template_modes: p3.template_modes.drop_last(), ..p3 };
    assert(Parser { template_modes: p3.template_modes.drop_last(), ..mode_as(p3, Mode::InBody) } == mode_as(p4, Mode::InBody));
    lemma_reset_from_mode(p4, Mode::InBody, p4.open.len() - 1);
    assert(reset_insertion_mode(mode_as(p4, Mode::InBody)) == reset_insertion_mode(p4));
    assert(in_head_template_end(p0) == in_head_template_end(p));
}

/// [`lemma_in_head_template_end_reach`] outside the "in cell" mode.
pub proof fn lemma_in_head_template_end_reach0(p: Parser)
    requires
        good(p),
        !p.stopped,
        modes_ok(p),
        p.mode != Mode::InCell,
        open_has_html(p, Tag::Template),
    ensures
        next_core(Outcome::Done(in_head_template_end(p))),
{
    if !open_has_html(p, Tag::Template) {
        return;
    }
    let j = crate::termination::helpers_ranking::lemma_open_has_html(p, Tag::Template);
    let p1 = generate_all_implied_end_tags_thoroughly(p);
    lemma_thorough_keeps(p);
    let f = |e: Elem|
        e.ns == Namespace::Html && match e.tag {
            Tag::Caption | Tag::Colgroup | Tag::Dd | Tag::Dt | Tag::Li | Tag::Optgroup | Tag::Option | Tag::P | Tag::Rb
            | Tag::Rp | Tag::Rt | Tag::Rtc | Tag::Tbody | Tag::Td | Tag::Tfoot | Tag::Th | Tag::Thead | Tag::Tr => true,
            _ => false,
        };
    assert(p1 == pop_while(p, f));
    crate::termination::helpers_tables::lemma_pop_while(p, f);
    assert(p1.open.len() > j);
    assert(p1.open[j] == p.open[j]);
    assert(j >= 1);
    let p2 = pop_until_popped(p1, Tag::Template);
    lemma_pop_until_popped_keeps(p1, Tag::Template, j);
    crate::termination::helpers_ranking::lemma_pop_until_template(p1, j);
    let p3 = clear_to_last_marker(p2);
    lemma_clear_keeps(p2);
    lemma_keeps_trans(p, p1, p2);
    lemma_keeps_trans(p, p2, p3);
    let p4 = Parser { template_modes: p3.template_modes.drop_last(), ..p3 };
    if !p4.stopped {
        crate::termination::helpers_ranking::lemma_template_count(p1);
        crate::termination::helpers_ranking::lemma_template_count(p2);
        crate::termination::helpers_ranking::lemma_template_count(p4);
        assert(crate::termination::template_count(p4) + 1 <= crate::termination::template_count(p));
        assert(p.template_modes.len() > 0);
        assert forall|i: int| 0 <= i < p4.template_modes.len() implies crate::termination::template_mode_ok(#[trigger] p4.template_modes[i]) by {
            assert(p4.template_modes[i] == p.template_modes[i]);
        }
        assert(crate::termination::helpers_ranking::count_ok(p4));
        assert(good(p4));
        lemma_reset_keeps(p4);
        crate::termination::helpers_ranking::lemma_reset_modes_ok(p4);
    }
}

/// The "in head" start tags that insert and pop an element (`base`,
/// `basefont`, `bgsound`, `link`, `meta`) keep the stack.
pub proof fn lemma_insert_pop_frame(p: Parser, tt: TagTok)
    requires
        good(p),
        !p.stopped,
        modes_ok(p),
        reach_core(p),
        tok_tagged(tt),
        tt.tag != Tag::Template,
        tt.tag != Tag::Td && tt.tag != Tag::Th,
        tt.tag != Tag::Html && tt.tag != Tag::Table,
    ensures
        ({
            let q = pop(insert_html_element(p, tt).0);
            q.stopped || (q == (Parser { doc: q.doc, ..p }) && reach_core(q) && modes_ok(q))
        }),
{
    lemma_insert_html_keeps(p, tt);
    let (p1, e) = insert_html_element(p, tt);
    let q = pop(p1);
    if !q.stopped {
        assert(q.open == p.open);
        lemma_core_frame(p, q);
    }
}

/// The "in head" rules.
pub proof fn lemma_in_head_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InHead), p, t),
    ensures
        next_core(mode_in_head(env, p, t)),
{
    hide(generic_text_parsing);
    hide(in_head_script);
    hide(in_head_template_start);
    hide(in_head_template_end);
    hide(insert_html_element);
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(in_head_meta);
    assert(good(p));
    assert(shape0(p.mode, p.open));
    let in_mode = p.mode == Mode::InHead;
    assert(in_mode || headish(t));
    if t is Char && is_ascii_whitespace(t->Char_0) {
        lemma_insert_char_keeps(p, t->Char_0);
        let q = insert_char(p, t->Char_0);
        if !q.stopped {
            lemma_core_frame(p, q);
        }
    } else if t is Comment {
        lemma_insert_comment_keeps(p, t->Comment_0, None);
        let q = insert_comment(p, t->Comment_0, None);
        if !q.stopped {
            lemma_core_frame(p, q);
        }
    } else if t is Pi {
        lemma_insert_pi_keeps(p, t->Pi_0, t->Pi_1, None);
        let q = insert_pi(p, t->Pi_0, t->Pi_1, None);
        if !q.stopped {
            lemma_core_frame(p, q);
        }
    } else if t is Doctype {
    } else if t is Start && t->Start_0.tag == Tag::Html {
    } else if t is Start && (t->Start_0.tag == Tag::Base || t->Start_0.tag == Tag::Basefont || t->Start_0.tag == Tag::Bgsound
        || t->Start_0.tag == Tag::Link) {
        lemma_insert_pop_frame(p, t->Start_0);
    } else if t is Start && t->Start_0.tag == Tag::Meta {
        let tt = t->Start_0;
        lemma_insert_pop_frame(p, tt);
        let p1 = pop(insert_html_element(p, tt).0);
        reveal(in_head_meta);
        let q = in_head_meta(env, p, tt);
        if !q.stopped {
            assert(!p1.stopped);
            lemma_core_frame(p1, q);
        }
    } else if t is Start && t->Start_0.tag == Tag::Title {
        lemma_generic_text_reach(p, t->Start_0, false);
    } else if t is Start && ((t->Start_0.tag == Tag::Noscript && p.scripting) || t->Start_0.tag == Tag::Noframes
        || t->Start_0.tag == Tag::Style) {
        lemma_generic_text_reach(p, t->Start_0, true);
    } else if t is Start && t->Start_0.tag == Tag::Noscript {
        assert(in_mode);
        reveal(insert_html_element);
        lemma_insert_html_keeps(p, t->Start_0);
        let (p1, e) = insert_html_element(p, t->Start_0);
        let q = Parser { mode: Mode::InHeadNoscript, ..p1 };
        if !q.stopped {
            assert(q.open == p.open.push(e));
            assert(q.open.drop_last() == p.open);
            crate::termination::helpers_ranking::lemma_modes_ok_from(p, q);
        }
    } else if t is Start && t->Start_0.tag == Tag::Script {
        lemma_in_head_script_reach(p, t->Start_0);
    } else if t is End && t->End_0.tag == Tag::Head {
        assert(in_mode);
        lemma_html_above_len(p.open);
        lemma_pop_keeps(p);
        let q = Parser { mode: Mode::AfterHead, ..pop(p) };
        lemma_finish(p, pop(p), q);
    } else if t is End && (t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Br) {
        assert(in_mode);
        lemma_html_above_len(p.open);
        lemma_pop_keeps(p);
        let q = Parser { mode: Mode::AfterHead, ..pop(p) };
        lemma_finish(p, pop(p), q);
    } else if t is Start && t->Start_0.tag == Tag::Template {
        lemma_in_head_template_start_reach(p, t->Start_0);
    } else if t is End && t->End_0.tag == Tag::Template {
        lemma_in_head_template_end_reach(p);
    } else if (t is Start && t->Start_0.tag == Tag::Head) || t is End {
    } else {
        assert(in_mode);
        lemma_html_above_len(p.open);
        lemma_pop_keeps(p);
        let q = Parser { mode: Mode::AfterHead, ..pop(p) };
        lemma_finish(p, pop(p), q);
    }
}

// ---------------------------------------------------------------------
// "in head noscript"

/// The "in head noscript" rules.
pub proof fn lemma_in_head_noscript_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InHeadNoscript), p, t),
    ensures
        next_core(mode_in_head_noscript(env, p, t)),
{
    assert(p.mode == Mode::InHeadNoscript);
    let o = mode_in_head_noscript(env, p, t);
    if (t is End && t->End_0.tag == Tag::Noscript) || o is Reprocess {
        let q0 = pop(p);
        assert(q0.open == p.open.drop_last());
        assert(q0.open[0] == p.open[0]);
        lemma_pop_keeps(p);
        let q = Parser { mode: Mode::InHead, ..q0 };
        crate::termination::helpers_ranking::lemma_modes_ok_from(p, q);
        assert(reach_core(q));
    }
}

// ---------------------------------------------------------------------
// "after head"

/// The `head` element record is tagged.
pub proof fn lemma_head_elem_tagged(h: NodeId)
    ensures
        elem_tagged(head_elem(h)),
        !is_html(head_elem(h), Tag::Template),
{
    assert(tag_of(seq![0x68u32, 0x65, 0x61, 0x64]) == Tag::Head) by (compute);
}

/// Case 8 of "after head": the "in head" rules with the `head` element
/// pushed back, then removed.
pub proof fn lemma_after_head_using_in_head_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::AfterHead), p, t),
        t is Start && after_head_in_head_tag(t->Start_0.tag),
    ensures
        next_core(after_head_using_in_head(env, p, t)),
{
    if p.head is None {
        return;
    }
    let h = p.head->Some_0;
    lemma_head_elem_tagged(h);
    let p1 = push(p, head_elem(h));
    lemma_push_keeps(p, head_elem(h));
    lemma_html_above_push(p.open, head_elem(h));
    crate::termination::helpers_ranking::lemma_tcount_push(p.open, head_elem(h));
    crate::termination::helpers_ranking::lemma_template_count(p);
    crate::termination::helpers_ranking::lemma_template_count(p1);
    crate::termination::helpers_ranking::lemma_modes_ok_from(p, p1);
    assert(headish(t));
    assert(rules_inv(Rules::Html(Mode::InHead), p1, t));
    crate::termination::helpers_early::lemma_in_head_start_done(env, p1, t);
    lemma_in_head_open(env, p1, t);
    lemma_in_head_reach(env, p1, t);
    let o = mode_in_head(env, p1, t);
    if let Outcome::Done(p2) = o {
        lemma_after_head_tail(p, p2, h);
    }
}

/// Case 8 of "after head": removing the `head` element after the "in head"
/// rules.
pub proof fn lemma_after_head_tail(p: Parser, p2: Parser, h: NodeId)
    requires
        reach_core(p),
        good(p),
        !p.stopped,
        modes_ok(p),
        p.mode == Mode::AfterHead,
        !p2.stopped ==> reach_core(p2) && modes_ok(p2),
        !p2.stopped ==> p2.mode == Mode::AfterHead || p2.mode == Mode::InTemplate || (p2.mode == Mode::Text
            && p2.original_mode == Mode::AfterHead),
        !p2.stopped ==> p2.open == p.open.push(head_elem(h)) || (p2.open.len() == p.open.len() + 2 && p2.open.drop_last()
            == p.open.push(head_elem(h)) && p2.open.last().ns == Namespace::Html),
        !p2.stopped && p2.mode == Mode::Text ==> p2.open.len() == p.open.len() + 2,
    ensures
        ({
            let i = open_index_of(p2, h);
            next_core(
                Outcome::Done(
                    if p2.stopped || i < 0 {
                        p2
                    } else {
                        remove_open_at(p2, i)
                    },
                ),
            )
        }),
{
    {
        let i = open_index_of(p2, h);
        if !(p2.stopped || i < 0) {
            let f = |e: Elem| e.id == h;
            let n = p.open.len() as int;
            if p2.open == p.open.push(head_elem(h)) {
                assert(p2.open[n] == head_elem(h));
            } else {
                assert(p2.open.drop_last()[n] == head_elem(h));
                assert(p2.open[n] == p2.open.drop_last()[n]);
            }
            crate::exec::stack::lemma_last_index_where_found(p2.open, p2.open.len() as int, f, n);
            assert(i >= n);
            let q = remove_open_at(p2, i);
            lemma_remove_open_keeps(p2, i);
            assert(q.open.len() == p2.open.len() - 1);
            assert forall|j: int| 0 <= j < n implies #[trigger] q.open[j] == p.open[j] by {
                assert(q.open[j] == p2.open[j]);
            }
            assert(q.open.subrange(0, n) == p.open);
            if p2.mode == Mode::Text {
                assert(q.open.len() == n + 1);
                assert(q.open.drop_last() =~= p.open);
                assert(q.open.last().ns == Namespace::Html) by {
                    if i == n {
                        assert(q.open.last() == p2.open.last());
                    } else {
                        assert(q.open.last() == p2.open[n]);
                    }
                }
            }
            crate::termination::helpers_ranking::lemma_template_count(p2);
            crate::termination::helpers_ranking::lemma_template_count(q);
        }
    }
}

/// The stack after the "in head" rules for the start tags of "after head"
/// case 8: kept, or one HTML element pushed.
pub proof fn lemma_in_head_open(env: EncFns, p: Parser, t: Tok)
    requires
        !p.stopped,
        t is Start && after_head_in_head_tag(t->Start_0.tag),
        crate::exec::modes::initial::tok_ok(t),
    ensures
        match mode_in_head(env, p, t) {
            Outcome::Done(q) => q.stopped || q.open == p.open || (q.open.len() == p.open.len() + 1 && q.open.drop_last()
                == p.open && q.open.last().ns == Namespace::Html),
            _ => true,
        },
        match mode_in_head(env, p, t) {
            Outcome::Done(q) => q.stopped || q.mode == p.mode || q.mode == Mode::InTemplate || (q.mode == Mode::Text
                && q.original_mode == p.mode && q.open.len() == p.open.len() + 1),
            _ => true,
        },
{
    let tt = t->Start_0;
    lemma_insert_html_keeps_frame(p, tt);
    if tt.tag == Tag::Script {
        assert(in_head_script(p, tt) == Parser {
            tokenizer: Some(TokenizerState::ScriptData),
            original_mode: insert_html_element(p, tt).0.mode,
            mode: Mode::Text,
            ..insert_html_element(p, tt).0
        });
    }
    if tt.tag == Tag::Template {
        let p1 = push_marker(p);
        let p2 = Parser { frameset_ok: false, mode: Mode::InTemplate, template_modes: p1.template_modes.push(Mode::InTemplate), ..p1 };
        let (p3, template) = create_element_for_token(p2, tt, Namespace::Html, appropriate_place(p2, None).parent);
        lemma_ceft_frame(p2, tt, Namespace::Html, appropriate_place(p2, None).parent);
        let insertion_location = appropriate_place(p3, None);
        let p4 = push(p3, template);
        lemma_insert_len(p4.doc, template.id, adjusted_location(p4, Some(insertion_location)).parent, adjusted_location(p4, Some(insertion_location)).child);
        if !p4.stopped {
            assert(p4.open.drop_last() == p.open);
        }
    }
    if tt.tag == Tag::Meta {
        let p1 = pop(insert_html_element(p, tt).0);
        if !p1.stopped {
            assert(p1.open == p.open);
        }
    }
}

/// "Insert an HTML element", as a frame (no requirement on the parser).
pub proof fn lemma_insert_html_keeps_frame(p: Parser, tt: TagTok)
    ensures
        !insert_html_element(p, tt).0.stopped ==> insert_html_element(p, tt).0.open == p.open.push(insert_html_element(p, tt).1),
        !insert_html_element(p, tt).0.stopped ==> insert_html_element(p, tt).0.mode == p.mode
            && insert_html_element(p, tt).0.original_mode == p.original_mode,
        insert_html_element(p, tt).1.ns == Namespace::Html,
{
    let ip = appropriate_place(p, None).parent;
    lemma_ceft_frame(p, tt, Namespace::Html, ip);
}

/// "Create an element for a token", as a frame.
pub proof fn lemma_ceft_frame(p: Parser, t: TagTok, ns: Namespace, ip: NodeId)
    ensures
        !create_element_for_token(p, t, ns, ip).0.stopped ==> create_element_for_token(p, t, ns, ip).0.open == p.open,
        !create_element_for_token(p, t, ns, ip).0.stopped ==> create_element_for_token(p, t, ns, ip).0.mode == p.mode
            && create_element_for_token(p, t, ns, ip).0.original_mode == p.original_mode,
        create_element_for_token(p, t, ns, ip).1.ns == ns,
{
}

/// The "after head" rules.
pub proof fn lemma_after_head_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::AfterHead), p, t),
    ensures
        next_core(mode_after_head(env, p, t)),
{
    hide(after_head_using_in_head);
    hide(insert_html_element);
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    assert(p.mode == Mode::AfterHead);
    assert(good(p));
    if t is Char && is_ascii_whitespace(t->Char_0) {
        lemma_insert_char_keeps(p, t->Char_0);
        let q = insert_char(p, t->Char_0);
        if !q.stopped {
            lemma_core_frame(p, q);
        }
    } else if t is Comment {
        lemma_insert_comment_keeps(p, t->Comment_0, None);
        let q = insert_comment(p, t->Comment_0, None);
        if !q.stopped {
            lemma_core_frame(p, q);
        }
    } else if t is Pi {
        lemma_insert_pi_keeps(p, t->Pi_0, t->Pi_1, None);
        let q = insert_pi(p, t->Pi_0, t->Pi_1, None);
        if !q.stopped {
            lemma_core_frame(p, q);
        }
    } else if t is Doctype {
    } else if t is Start && t->Start_0.tag == Tag::Html {
    } else if t is Start && (t->Start_0.tag == Tag::Body || t->Start_0.tag == Tag::Frameset) {
        lemma_insert_html_keeps(p, t->Start_0);
        let p1 = insert_html_element(p, t->Start_0).0;
        if t->Start_0.tag == Tag::Body {
            lemma_finish(p, p1, Parser { frameset_ok: false, mode: Mode::InBody, ..p1 });
        } else {
            lemma_finish(p, p1, Parser { mode: Mode::InFrameset, ..p1 });
        }
    } else if t is Start && after_head_in_head_tag(t->Start_0.tag) {
        lemma_after_head_using_in_head_reach(env, p, t);
    } else if t is End && t->End_0.tag == Tag::Template {
    } else if (t is End && (t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Br)) || !((t is Start
        && t->Start_0.tag == Tag::Head) || t is End) {
        let tt = start_tag_named(seq![0x62u32, 0x6f, 0x64, 0x79]);
        assert(tag_of(seq![0x62u32, 0x6f, 0x64, 0x79]) == Tag::Body) by (compute);
        lemma_insert_html_keeps(p, tt);
        let p1 = insert_html_element(p, tt).0;
        lemma_finish(p, p1, Parser { frameset_ok: true, mode: Mode::InBody, ..p1 });
    }
}

// ---------------------------------------------------------------------
// "text"

/// The "text" rules.
pub proof fn lemma_text_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::Text), p, t),
    ensures
        next_core(mode_text(env, p, t)),
{
    hide(insert_char);
    assert(p.mode == Mode::Text);
    let o = mode_text(env, p, t);
    if t is Char {
        assert(good(p)) by {
            assert(p.open.drop_last()[0] == p.open[0]);
        }
        lemma_insert_char_keeps(p, t->Char_0);
        let q = insert_char(p, t->Char_0);
        if !q.stopped {
            lemma_core_frame(p, q);
        }
    } else if t is Eof || t is End {
        let q0 = pop(p);
        assert(q0.open == p.open.drop_last());
        assert(q0.open[0] == p.open[0]);
        assert(good(p));
        lemma_pop_keeps(p);
        let q = Parser { mode: p.original_mode, ..q0 };
        crate::termination::helpers_ranking::lemma_modes_ok_from(p, q);
        assert(reach_core(q));
        if t is End && t->End_0.tag == Tag::Script {
            assert(text_script_end(p) == Parser { actions: text_script_end(p).actions, ..q });
        }
    }
}

} // verus!
