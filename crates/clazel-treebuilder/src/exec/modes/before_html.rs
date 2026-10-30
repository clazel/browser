//! HTML §13.2.6.4.2 the "before html" insertion mode ([`mode_before_html`])
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

/// §13.2.6.4.2 the "before html" insertion mode ([`mode_before_html`]).
pub fn mode_before_html_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        tok_ok(t@),
    ensures
        outcome_view(o, final(p)@) == mode_before_html(_env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    hide(before_html_anything_else);
    if is_whitespace_tok(&t) {
        // 4.
        return ExecOutcome::Done;
    }
    proof {
        lemma_document_location_ok(p@);
    }
    match t {
        // 1.
        ExecTok::Doctype { .. } => ExecOutcome::Done,
        ExecTok::Comment(d) => {
            // 2.
            insert_comment_exec(p, d, Some(document_location_exec()));
            ExecOutcome::Done
        },
        ExecTok::Pi(target, d) => {
            // 3.
            insert_pi_exec(p, target, d, Some(document_location_exec()));
            ExecOutcome::Done
        },
        ExecTok::Start(tt) => {
            if matches!(tt.tag, Tag::Html) {
                // 5.
                insert_html_root(p, &tt);
                proof {
                    lemma_inv_mode(p@, Mode::BeforeHead);
                }
                p.mode = Mode::BeforeHead;
                ExecOutcome::Done
            } else {
                // 8.
                before_html_anything_else_exec(p, ExecTok::Start(tt))
            }
        },
        ExecTok::End(tt) => {
            if matches!(tt.tag, Tag::Head | Tag::Body | Tag::Html | Tag::Br) {
                // 6.
                before_html_anything_else_exec(p, ExecTok::End(tt))
            } else {
                // 7.
                ExecOutcome::Done
            }
        },
        // 8.
        t => before_html_anything_else_exec(p, t),
    }
}

/// "Create an element for the token in the HTML namespace, with the
/// Document as the intended parent", "insert an element at the adjusted
/// insertion location with that element and (the Document, null)" and
/// "put this element in the stack of open elements": the steps cases 5 and
/// 8 share.
fn insert_html_root(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == ({
            let (p1, e) = create_element_for_token(old(p)@, tt@, Namespace::Html, 0);
            push(insert_element_at(p1, e.id, Some(document_location())), e)
        }),
        parser_inv(final(p)@),
{
    proof {
        lemma_inv_iff(old(p)@);
        lemma_wf_nonempty(old(p)@.doc);
    }
    let e = create_element_for_token_exec(p, tt, Namespace::Html, 0);
    let ghost p1 = p@;
    proof {
        lemma_document_location_ok(p1);
    }
    insert_element_at_exec(p, e.id, Some(document_location_exec()));
    proof {
        if !p1.stopped {
            lemma_elem_ok_extends(p1.doc, p@.doc, e@);
        }
    }
    push_exec(p, e);
}

/// The "anything else" entry of the "before html" insertion mode
/// ([`before_html_anything_else`]).
pub fn before_html_anything_else_exec(p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
    ensures
        outcome_view(o, final(p)@) == before_html_anything_else(old(p)@, t@),
        parser_inv(final(p)@),
{
    // "html"
    let tt = start_tag_named_exec(vec![0x68u32, 0x74, 0x6d, 0x6c]);
    proof {
        assert(tt@.name =~= seq![0x68u32, 0x74, 0x6d, 0x6c]);
        crate::termination::helpers_ranking::lemma_not_template(tt@.name);
    }
    insert_html_root(p, &tt);
    proof {
        lemma_inv_mode(p@, Mode::BeforeHead);
    }
    p.mode = Mode::BeforeHead;
    ExecOutcome::Reprocess(t)
}

} // verus!
