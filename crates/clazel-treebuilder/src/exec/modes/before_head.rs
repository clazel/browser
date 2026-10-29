//! HTML §13.2.6.4.3 the "before head" insertion mode ([`mode_before_head`])
//! over [`ParserBuf`].

#[cfg(verus_only)]
use super::super::frame::*;
use super::super::insert::*;
use super::super::stack::*;
use super::super::types::*;
use super::initial::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §13.2.6.4.3 the "before head" insertion mode ([`mode_before_head`]).
pub fn mode_before_head_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        tok_ok(t@),
        old(p)@.stopped || stack_rooted(old(p)@),
    ensures
        outcome_view(o, final(p)@) == mode_before_head(_env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    hide(before_head_anything_else);
    if is_whitespace_tok(&t) {
        // 1.
        return ExecOutcome::Done;
    }
    match t {
        ExecTok::Comment(d) => {
            // 2.
            insert_comment_exec(p, d, None);
            ExecOutcome::Done
        },
        ExecTok::Pi(target, d) => {
            // 3.
            insert_pi_exec(p, target, d, None);
            ExecOutcome::Done
        },
        // 4.
        ExecTok::Doctype { .. } => ExecOutcome::Done,
        ExecTok::Start(tt) => {
            if matches!(tt.tag, Tag::Html) {
                // 5.
                ExecOutcome::Using(Mode::InBody, ExecTok::Start(tt))
            } else if matches!(tt.tag, Tag::Head) {
                // 6.
                proof {
                    lemma_tag_of_head(tt@.name);
                }
                insert_head(p, &tt);
                ExecOutcome::Done
            } else {
                // 9.
                before_head_anything_else_exec(p, ExecTok::Start(tt))
            }
        },
        ExecTok::End(tt) => {
            if matches!(tt.tag, Tag::Head | Tag::Body | Tag::Html | Tag::Br) {
                // 7.
                before_head_anything_else_exec(p, ExecTok::End(tt))
            } else {
                // 8.
                ExecOutcome::Done
            }
        },
        // 9.
        t => before_head_anything_else_exec(p, t),
    }
}

/// Every element "create an element for a token" returns is a node of the
/// document, or 0 (when parsing has stopped).
proof fn lemma_created_id(p: Parser, t: TagTok, ns: Namespace, ip: NodeId)
    requires
        parser_inv(p),
    ensures
        create_element_for_token(p, t, ns, ip).1.id == 0 || dom::valid(
            create_element_for_token(p, t, ns, ip).0.doc,
            create_element_for_token(p, t, ns, ip).1.id,
        ),
{
}

/// [`insert_html_element`] for a token other than `template`, with the
/// element's id a node of the document (the head element pointer is set to
/// it).
fn insert_html_element_id(p: &mut ParserBuf, t: &ExecTagTok) -> (r: ExecElem)
    requires
        parser_inv(old(p)@),
        tok_tagged(t@),
        old(p)@.stopped || stack_rooted(old(p)@),
        t@.tag != Tag::Template,
    ensures
        (final(p)@, r@) == insert_html_element(old(p)@, t@),
        parser_inv(final(p)@),
        dom::valid(final(p)@.doc, r.id),
{
    proof {
        lemma_inv_iff(old(p)@);
        lemma_wf_nonempty(old(p)@.doc);
    }
    let ghost p0 = p@;
    if p.stopped {
        let e = create_element_for_token_exec(p, t, Namespace::Html, 0);
        proof {
            lemma_created_id(p0, t@, Namespace::Html, 0);
        }
        return e;
    }
    // 1.
    let place = appropriate_place_exec(p, None);
    let e = create_element_for_token_exec(p, t, Namespace::Html, place.parent);
    proof {
        lemma_created_id(p0, t@, Namespace::Html, place.parent);
    }
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

/// Only the name "head" is the tag `head`.
pub proof fn lemma_tag_of_head(name: Seq<u32>)
    ensures
        tag_of(name) == Tag::Head ==> name == seq![0x68u32, 0x65, 0x61, 0x64],
{
}

/// Setting the head element pointer to a node keeps [`parser_inv`].
pub proof fn lemma_inv_head(p: Parser, h: NodeId)
    requires
        parser_inv(p),
        dom::valid(p.doc, h),
        p.stopped || elem_in_doc(p.doc, head_elem(h)),
    ensures
        parser_inv(Parser { head: Some(h), ..p }),
{
    lemma_inv_iff(p);
    lemma_inv_iff(Parser { head: Some(h), ..p });
}

/// "Insert an HTML element for the token", "set the head element pointer
/// to the newly created head element" and "switch the insertion mode to
/// "in head"": case 6 and the "anything else" entry.
fn insert_head(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        tok_tagged(tt@),
        old(p)@.stopped || stack_rooted(old(p)@),
        tt@.tag != Tag::Template,
        tt@.name == seq![0x68u32, 0x65, 0x61, 0x64],
    ensures
        final(p)@ == ({
            let (p1, e) = insert_html_element(old(p)@, tt@);
            Parser { head: Some(e.id), mode: Mode::InHead, ..p1 }
        }),
        parser_inv(final(p)@),
{
    let ghost p0 = p@;
    let e = insert_html_element_id(p, tt);
    proof {
        if !p@.stopped {
            let q = p@;
            assert(q.open == insert_html_element(p0, tt@).0.open);
            assert(q.open[q.open.len() - 1] == e@);
            lemma_inv_iff(q);
            assert(elem_ok(q.doc, q.open[q.open.len() - 1]));
            assert(elem_in_doc(q.doc, head_elem(e.id)));
        }
        lemma_inv_head(p@, e.id);
    }
    p.head = Some(e.id);
    proof {
        lemma_inv_mode(p@, Mode::InHead);
    }
    p.mode = Mode::InHead;
}

/// The "anything else" entry of the "before head" insertion mode
/// ([`before_head_anything_else`]).
pub fn before_head_anything_else_exec(p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
    ensures
        outcome_view(o, final(p)@) == before_head_anything_else(old(p)@, t@),
        parser_inv(final(p)@),
{
    // "head"
    let tt = start_tag_named_exec(vec![0x68u32, 0x65, 0x61, 0x64]);
    proof {
        assert(tt@.name =~= seq![0x68u32, 0x65, 0x61, 0x64]);
        crate::termination::helpers_ranking::lemma_not_template(tt@.name);
    }
    insert_head(p, &tt);
    ExecOutcome::Reprocess(t)
}

} // verus!
