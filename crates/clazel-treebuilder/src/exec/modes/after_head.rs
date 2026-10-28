//! HTML §13.2.6.4.6 the "after head" insertion mode ([`mode_after_head`])
//! over [`ParserBuf`]. Case 8 runs the "in head" rules
//! ([`mode_in_head_exec`]) with the head element pushed back on the stack.

#[cfg(verus_only)]
use super::super::frame::*;
use super::super::insert::*;
use super::super::stack::*;
use super::super::types::*;
use super::in_head::*;
use super::initial::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The head element pointer, if set, points to an HTML `head` element of
/// the document (it is only ever set to the `head` element the parser
/// created): what case 8 pushes back is a record of the document.
pub open spec fn head_ok(p: Parser) -> bool {
    match p.head {
        Some(h) => elem_in_doc(p.doc, head_elem(h)),
        None => true,
    }
}

/// §13.2.6.4.6 the "after head" insertion mode ([`mode_after_head`]). The
/// rules are never applied in the "text" or "in table text" modes
/// (`termination::rules_ok` for "after head").
pub fn mode_after_head_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        tok_ok(t@),
        old(p)@.stopped || stack_rooted(old(p)@),
        old(p)@.stopped || head_ok(old(p)@),
        old(p)@.mode != Mode::Text && old(p)@.mode != Mode::InTableText,
    ensures
        outcome_view(o, final(p)@) == mode_after_head(env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    hide(after_head_using_in_head);
    hide(after_head_anything_else);
    hide(insert_html_element);
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    match t {
        ExecTok::Char(c) => {
            if is_ascii_whitespace_exec(c) {
                // 1.
                insert_char_exec(p, c);
                ExecOutcome::Done
            } else {
                // 12.
                after_head_anything_else_exec(p, ExecTok::Char(c))
            }
        },
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
            } else if matches!(tt.tag, Tag::Body) {
                // 6.
                let _ = insert_html_element_exec(p, &tt);
                proof {
                    lemma_inv_frameset_mode(p@, false, Mode::InBody);
                }
                p.frameset_ok = false;
                p.mode = Mode::InBody;
                ExecOutcome::Done
            } else if matches!(tt.tag, Tag::Frameset) {
                // 7.
                let _ = insert_html_element_exec(p, &tt);
                proof {
                    lemma_inv_mode(p@, Mode::InFrameset);
                }
                p.mode = Mode::InFrameset;
                ExecOutcome::Done
            } else if after_head_in_head_tag_exec(&tt.tag) {
                // 8.
                after_head_using_in_head_exec(env, p, tt)
            } else if matches!(tt.tag, Tag::Head) {
                // 11.
                ExecOutcome::Done
            } else {
                // 12.
                after_head_anything_else_exec(p, ExecTok::Start(tt))
            }
        },
        ExecTok::End(tt) => {
            if matches!(tt.tag, Tag::Template) {
                // 9.
                ExecOutcome::Using(Mode::InHead, ExecTok::End(tt))
            } else if matches!(tt.tag, Tag::Body | Tag::Html | Tag::Br) {
                // 10.
                after_head_anything_else_exec(p, ExecTok::End(tt))
            } else {
                // 11.
                ExecOutcome::Done
            }
        },
        // 12.
        t => after_head_anything_else_exec(p, t),
    }
}

/// Setting the frameset-ok flag and switching to a mode keeps
/// [`parser_inv`].
proof fn lemma_inv_frameset_mode(p: Parser, b: bool, m: Mode)
    requires
        parser_inv(p),
        m != Mode::Text,
        m != Mode::InTableText,
        m != Mode::InTemplate,
    ensures
        parser_inv(Parser { frameset_ok: b, mode: m, ..p }),
{
    lemma_inv_iff(p);
    lemma_inv_iff(Parser { frameset_ok: b, mode: m, ..p });
}

/// [`after_head_in_head_tag`].
pub fn after_head_in_head_tag_exec(tag: &Tag) -> (r: bool)
    ensures
        r == after_head_in_head_tag(*tag),
{
    matches!(
        tag,
        Tag::Base | Tag::Basefont | Tag::Bgsound | Tag::Link | Tag::Meta | Tag::Noframes | Tag::Script | Tag::Style
            | Tag::Template | Tag::Title
    )
}

/// The record [`head_elem`] of the head element `h`.
fn head_elem_exec(h: usize) -> (r: ExecElem)
    ensures
        r@ == head_elem(h),
        elem_tagged(r@),
{
    let name = vec![0x68u32, 0x65, 0x61, 0x64];
    proof {
        assert(name@ =~= seq![0x68u32, 0x65, 0x61, 0x64]);
        assert(tag_of(seq![0x68u32, 0x65, 0x61, 0x64]) == Tag::Head);
    }
    ExecElem { id: h, ns: Namespace::Html, tag: Tag::Head, name, annotation_html: false }
}

/// Case 8 of the "after head" insertion mode ([`after_head_using_in_head`]).
pub fn after_head_using_in_head_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, tt: ExecTagTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        tok_tagged(tt@),
        old(p)@.stopped || stack_rooted(old(p)@),
        old(p)@.stopped || head_ok(old(p)@),
        old(p)@.mode != Mode::Text && old(p)@.mode != Mode::InTableText,
    ensures
        outcome_view(o, final(p)@) == after_head_using_in_head(env.enc(), old(p)@, Tok::Start(tt@)),
        parser_inv(final(p)@),
{
    hide(mode_in_head);
    let h = match p.head {
        // "The head element pointer cannot be null at this point."
        None => return ExecOutcome::Done,
        Some(h) => h,
    };
    // "Push the node pointed to by the head element pointer onto the stack
    // of open elements."
    let e = head_elem_exec(h);
    proof {
        assert(old(p)@.head == Some(h));
        if !p@.stopped {
            assert(elem_in_doc(p@.doc, e@));
        }
        assert(!is_html(e@, Tag::Template));
    }
    push_exec(p, e);
    // "Process the token using the rules for the "in head" insertion
    // mode."
    let o = mode_in_head_exec(env, p, ExecTok::Start(tt));
    match o {
        ExecOutcome::Done => {
            // "Remove the node pointed to by the head element pointer from
            // the stack of open elements."
            let i = if p.stopped {
                None
            } else {
                open_index_of_exec(p, h)
            };
            if let Some(i) = i {
                remove_open_at_exec(p, i);
            }
            ExecOutcome::Done
        },
        other => other,
    }
}

/// The "anything else" entry of the "after head" insertion mode
/// ([`after_head_anything_else`]).
pub fn after_head_anything_else_exec(p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
    ensures
        outcome_view(o, final(p)@) == after_head_anything_else(old(p)@, t@),
        parser_inv(final(p)@),
{
    // "body"
    let tt = start_tag_named_exec(vec![0x62u32, 0x6f, 0x64, 0x79]);
    proof {
        assert(tt@.name =~= seq![0x62u32, 0x6f, 0x64, 0x79]);
        crate::termination::helpers_ranking::lemma_not_template(tt@.name);
    }
    let _ = insert_html_element_exec(p, &tt);
    proof {
        lemma_inv_frameset_mode(p@, true, Mode::InBody);
    }
    p.frameset_ok = true;
    p.mode = Mode::InBody;
    ExecOutcome::Reprocess(t)
}

} // verus!
