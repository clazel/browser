//! HTML §13.2.6.4.4 the "in head" insertion mode ([`mode_in_head`]) over
//! [`ParserBuf`]: the `meta` rule with "change the encoding" through
//! [`EncFnsExec`], the `script` rule, and the `template` start and end tag
//! rules.

use super::super::formatting::*;
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

/// §13.2.6.4.4 the "in head" insertion mode ([`mode_in_head`]). The rules
/// are never applied in the "text" or "in table text" modes
/// (`termination::rules_ok` for "in head").
pub fn mode_in_head_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        tok_ok(t@),
        old(p)@.stopped || stack_rooted(old(p)@),
        old(p)@.mode != Mode::Text && old(p)@.mode != Mode::InTableText,
    ensures
        outcome_view(o, final(p)@) == mode_in_head(env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    hide(in_head_meta);
    hide(in_head_script);
    hide(in_head_template_start);
    hide(in_head_template_end);
    hide(in_head_anything_else);
    hide(insert_html_element);
    hide(generic_text_parsing);
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
                // 17.
                in_head_anything_else_exec(p, ExecTok::Char(c))
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
        ExecTok::Start(tt) => in_head_start_exec(env, p, tt),
        ExecTok::End(tt) => {
            if matches!(tt.tag, Tag::Head) {
                // 12.
                pop_exec(p);
                proof {
                    lemma_inv_mode(p@, Mode::AfterHead);
                }
                p.mode = Mode::AfterHead;
                ExecOutcome::Done
            } else if matches!(tt.tag, Tag::Body | Tag::Html | Tag::Br) {
                // 13.
                in_head_anything_else_exec(p, ExecTok::End(tt))
            } else if matches!(tt.tag, Tag::Template) {
                // 15.
                in_head_template_end_exec(p);
                ExecOutcome::Done
            } else {
                // 16.
                ExecOutcome::Done
            }
        },
        // 17.
        t => in_head_anything_else_exec(p, t),
    }
}

/// The start tag cases of [`mode_in_head`].
fn in_head_start_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, tt: ExecTagTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        tok_tagged(tt@),
        old(p)@.stopped || stack_rooted(old(p)@),
        old(p)@.mode != Mode::Text && old(p)@.mode != Mode::InTableText,
    ensures
        outcome_view(o, final(p)@) == mode_in_head(env.enc(), old(p)@, Tok::Start(tt@)),
        parser_inv(final(p)@),
{
    hide(in_head_meta);
    hide(in_head_script);
    hide(in_head_template_start);
    hide(in_head_template_end);
    hide(in_head_anything_else);
    hide(generic_text_parsing);
    if matches!(tt.tag, Tag::Html) {
        // 5.
        ExecOutcome::Using(Mode::InBody, ExecTok::Start(tt))
    } else if matches!(tt.tag, Tag::Base | Tag::Basefont | Tag::Bgsound | Tag::Link) {
        // 6.
        let _ = insert_html_element_exec(p, &tt);
        pop_exec(p);
        ExecOutcome::Done
    } else if matches!(tt.tag, Tag::Meta) {
        // 7.
        in_head_meta_exec(env, p, &tt);
        ExecOutcome::Done
    } else if matches!(tt.tag, Tag::Title) {
        // 8.
        generic_text_parsing_exec(p, &tt, false);
        ExecOutcome::Done
    } else if (matches!(tt.tag, Tag::Noscript) && p.scripting) || matches!(tt.tag, Tag::Noframes | Tag::Style) {
        // 9.
        generic_text_parsing_exec(p, &tt, true);
        ExecOutcome::Done
    } else if matches!(tt.tag, Tag::Noscript) {
        // 10.
        let _ = insert_html_element_exec(p, &tt);
        proof {
            lemma_inv_mode(p@, Mode::InHeadNoscript);
        }
        p.mode = Mode::InHeadNoscript;
        ExecOutcome::Done
    } else if matches!(tt.tag, Tag::Script) {
        // 11.
        in_head_script_exec(p, &tt);
        ExecOutcome::Done
    } else if matches!(tt.tag, Tag::Template) {
        // 14.
        in_head_template_start_exec(p, &tt);
        ExecOutcome::Done
    } else if matches!(tt.tag, Tag::Head) {
        // 16.
        ExecOutcome::Done
    } else {
        // 17.
        in_head_anything_else_exec(p, ExecTok::Start(tt))
    }
}

/// §13.2.3.4 "change the encoding" ([`change_the_encoding`]).
pub fn change_the_encoding_exec(p: &mut ParserBuf, enc: u64)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == change_the_encoding(old(p)@, enc as nat),
        parser_inv(final(p)@),
{
    if p.stopped {
        return ;
    }
    let ghost a = p.actions@;
    p.actions.push(ExecAction::ChangeEncoding(enc));
    p.tentative = false;
    proof {
        assert(actions_view(p.actions@) =~= actions_view(a).push(Action::ChangeEncoding(enc as nat)));
    }
}

/// The encoding a `meta` element's `content` value declares
/// ([`meta_extracted_encoding`]).
pub fn meta_extracted_encoding_exec<E: EncFnsExec>(env: &E, content: &[u32]) -> (r: Option<u64>)
    ensures
        opt_enc_view(r) == meta_extracted_encoding(env.enc(), content@),
{
    match env.extract_from_meta(content) {
        Some(label) => env.get_an_encoding(label.as_slice()),
        None => None,
    }
}

/// Case 7 of the "in head" insertion mode ([`in_head_meta`]).
pub fn in_head_meta_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        tok_tagged(tt@),
        old(p)@.stopped || stack_rooted(old(p)@),
        tt@.tag == Tag::Meta,
    ensures
        final(p)@ == in_head_meta(env.enc(), old(p)@, tt@),
        parser_inv(final(p)@),
{
    let _ = insert_html_element_exec(p, tt);
    pop_exec(p);
    let charset: &[u32] = &[0x63u32, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74];
    let http_equiv: &[u32] = &[0x68u32, 0x74, 0x74, 0x70, 0x2d, 0x65, 0x71, 0x75, 0x69, 0x76];
    let content: &[u32] = &[0x63u32, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74];
    let content_type: &[u32] = &[0x43u32, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x2d, 0x54, 0x79, 0x70, 0x65];
    proof {
        assert(charset@ =~= in_head_name_charset());
        assert(http_equiv@ =~= in_head_name_http_equiv());
        assert(content@ =~= in_head_name_content());
        assert(content_type@ =~= in_head_content_type());
    }
    // 1.
    let from_charset = match attr_value_exec(tt.attrs.as_slice(), charset) {
        Some(v) => env.get_an_encoding(v.as_slice()),
        None => None,
    };
    match from_charset {
        Some(enc) if p.tentative => {
            change_the_encoding_exec(p, enc);
            return ;
        },
        _ => {},
    }
    // 2.
    let is_content_type = match attr_value_exec(tt.attrs.as_slice(), http_equiv) {
        Some(h) => ascii_ci_eq_exec(h.as_slice(), content_type),
        None => false,
    };
    if !is_content_type || !p.tentative {
        return ;
    }
    let extracted = match attr_value_exec(tt.attrs.as_slice(), content) {
        Some(c) => meta_extracted_encoding_exec(env, c.as_slice()),
        None => None,
    };
    if let Some(enc) = extracted {
        change_the_encoding_exec(p, enc);
    }
}

/// Switching to the "text" mode with the current mode as the original
/// insertion mode keeps [`parser_inv`].
proof fn lemma_inv_text(p: Parser, ts: Option<TokenizerState>)
    requires
        parser_inv(p),
        p.mode != Mode::Text && p.mode != Mode::InTableText,
    ensures
        parser_inv(Parser { tokenizer: ts, original_mode: p.mode, mode: Mode::Text, ..p }),
{
    lemma_inv_iff(p);
    lemma_inv_iff(Parser { tokenizer: ts, original_mode: p.mode, mode: Mode::Text, ..p });
}

/// Case 11 of the "in head" insertion mode ([`in_head_script`]).
pub fn in_head_script_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        tok_tagged(tt@),
        old(p)@.stopped || stack_rooted(old(p)@),
        old(p)@.mode != Mode::Text && old(p)@.mode != Mode::InTableText,
        tt@.tag == Tag::Script,
    ensures
        final(p)@ == in_head_script(old(p)@, tt@),
        parser_inv(final(p)@),
{
    proof {
        lemma_inv_iff(old(p)@);
        lemma_wf_nonempty(old(p)@.doc);
    }
    // 1.
    let parent = if p.stopped {
        0
    } else {
        appropriate_place_exec(p, None).parent
    };
    let e = create_element_for_token_exec(p, tt, Namespace::Html, parent);
    // 5.
    let ghost p1 = p@;
    insert_element_at_exec(p, e.id, None);
    proof {
        if !p1.stopped {
            lemma_elem_ok_extends(p1.doc, p@.doc, e@);
        }
    }
    // 6.
    push_exec(p, e);
    // 7., 8., 9.
    proof {
        lemma_inv_text(p@, Some(TokenizerState::ScriptData));
    }
    p.tokenizer = Some(TokenizerState::ScriptData);
    p.original_mode = copy_mode(&p.mode);
    p.mode = Mode::Text;
}

/// Pushing "in template" onto the stack of template insertion modes and
/// switching to it keeps [`parser_inv`].
proof fn lemma_inv_template_mode(p: Parser)
    requires
        parser_inv(p),
    ensures
        parser_inv(Parser { frameset_ok: false, mode: Mode::InTemplate, template_modes: p.template_modes.push(Mode::InTemplate), ..p }),
{
    let q = Parser { frameset_ok: false, mode: Mode::InTemplate, template_modes: p.template_modes.push(Mode::InTemplate), ..p };
    lemma_inv_iff(p);
    lemma_inv_iff(q);
    assert forall|i: int| 0 <= i < q.template_modes.len() implies crate::termination::template_mode_ok(
        #[trigger] q.template_modes[i],
    ) by {
        if i < p.template_modes.len() {
            assert(q.template_modes[i] == p.template_modes[i]);
        }
    }
}

/// Case 14 of the "in head" insertion mode ([`in_head_template_start`]).
pub fn in_head_template_start_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        tok_tagged(tt@),
        old(p)@.stopped || stack_rooted(old(p)@),
        tt@.tag == Tag::Template,
    ensures
        final(p)@ == in_head_template_start(old(p)@, tt@),
        parser_inv(final(p)@),
{
    // 2.
    push_marker_exec(p);
    // 3., 4., 5.
    proof {
        lemma_inv_template_mode(p@);
    }
    p.frameset_ok = false;
    p.mode = Mode::InTemplate;
    p.template_modes.push(Mode::InTemplate);
    let ghost p2 = p@;
    proof {
        lemma_inv_iff(p2);
        lemma_wf_nonempty(p2.doc);
    }
    // 8.
    let parent = if p.stopped {
        0
    } else {
        appropriate_place_exec(p, None).parent
    };
    let template = create_element_for_token_exec(p, tt, Namespace::Html, parent);
    let ghost p3 = p@;
    // 9.
    let location = if p.stopped {
        document_location_exec()
    } else {
        appropriate_place_exec(p, None)
    };
    // 10.
    let id = template.id;
    push_exec(p, template);
    // 13.3
    insert_element_at_exec(p, id, Some(location));
}

/// `reset_from` does not read the insertion mode.
proof fn lemma_reset_from_mode(p: Parser, m: Mode, i: int)
    ensures
        reset_from(Parser { mode: m, ..p }, i) == reset_from(p, i),
    decreases i + 1,
{
    if i >= 0 {
        lemma_reset_from_mode(p, m, i - 1);
    }
}

/// "Pop elements … until an HTML element named `tag` has been popped"
/// changes only the stack.
proof fn lemma_pop_until_popped_frame(p: Parser, tag: Tag)
    ensures
        pop_until_popped(p, tag) == (Parser { open: pop_until_popped(p, tag).open, ..p }),
    decreases p.open.len(),
{
    if p.open.len() > 0 && !is_html(current_node(p), tag) {
        lemma_pop_until_popped_frame(pop(p), tag);
    }
}

/// Steps 1, 5 and 6 of case 15 pop one `template` element at least, and
/// change neither the template insertion modes nor the context.
proof fn lemma_template_end_count(p0: Parser)
    requires
        open_has_html(p0, Tag::Template),
    ensures
        ({
            let p3 = clear_to_last_marker(pop_until_popped(generate_all_implied_end_tags_thoroughly(p0), Tag::Template));
            &&& crate::termination::template_count(p3) + 1 <= crate::termination::template_count(p0)
            &&& p3.template_modes == p0.template_modes
            &&& p3.open == pop_until_popped(generate_all_implied_end_tags_thoroughly(p0), Tag::Template).open
        }),
{
    let f = |e: Elem|
        e.ns == Namespace::Html && match e.tag {
            Tag::Caption | Tag::Colgroup | Tag::Dd | Tag::Dt | Tag::Li | Tag::Optgroup | Tag::Option | Tag::P | Tag::Rb | Tag::Rp
            | Tag::Rt | Tag::Rtc | Tag::Tbody | Tag::Td | Tag::Tfoot | Tag::Th | Tag::Thead | Tag::Tr => true,
            _ => false,
        };
    let p1 = generate_all_implied_end_tags_thoroughly(p0);
    let p2 = pop_until_popped(p1, Tag::Template);
    let p3 = clear_to_last_marker(p2);
    assert(p1 == pop_while(p0, f));
    crate::termination::helpers_tables::lemma_pop_while(p0, f);
    let j = crate::termination::helpers_ranking::lemma_open_has_html(p0, Tag::Template);
    assert(!f(p0.open[j]));
    assert(p1.open[j] == p0.open[j]);
    crate::termination::helpers_ranking::lemma_pop_until_template(p1, j);
    crate::termination::helpers_ranking::lemma_tcount_prefix(p1.open, p0.open);
    lemma_pop_until_popped_frame(p1, Tag::Template);
    crate::termination::helpers_ranking::lemma_clear_to_last_marker(p2);
    crate::termination::helpers_ranking::lemma_template_count(p0);
    crate::termination::helpers_ranking::lemma_template_count(p3);
}

/// Step 7 of case 15, with the mode "in head" until step 8 resets it,
/// keeps [`parser_inv`], and step 8 does not read the mode.
proof fn lemma_template_end_modes(p0: Parser, p3: Parser)
    requires
        parser_inv(p0),
        parser_inv(p3),
        crate::termination::template_count(p3) + 1 <= crate::termination::template_count(p0),
        p3.template_modes == p0.template_modes,
    ensures
        parser_inv(Parser { mode: Mode::InHead, template_modes: p3.template_modes.drop_last(), ..p3 }),
        reset_insertion_mode(Parser { mode: Mode::InHead, template_modes: p3.template_modes.drop_last(), ..p3 })
            == reset_insertion_mode(Parser { template_modes: p3.template_modes.drop_last(), ..p3 }),
{
    let q = Parser { mode: Mode::InHead, template_modes: p3.template_modes.drop_last(), ..p3 };
    lemma_inv_iff(p0);
    lemma_inv_iff(p3);
    lemma_inv_iff(q);
    assert forall|i: int| 0 <= i < q.template_modes.len() implies crate::termination::template_mode_ok(
        #[trigger] q.template_modes[i],
    ) by {
        assert(q.template_modes[i] == p3.template_modes[i]);
    }
    lemma_reset_from_mode(Parser { template_modes: p3.template_modes.drop_last(), ..p3 }, Mode::InHead, q.open.len() - 1);
}

/// Case 15 of the "in head" insertion mode ([`in_head_template_end`]).
pub fn in_head_template_end_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == in_head_template_end(old(p)@),
        parser_inv(final(p)@),
{
    if !open_has_html_exec(p, Tag::Template) {
        return ;
    }
    let ghost p0 = p@;
    proof {
        lemma_template_end_count(p0);
    }
    // 1.
    generate_all_implied_end_tags_thoroughly_exec(p);
    // 5.
    pop_until_popped_exec(p, Tag::Template);
    // 6.
    clear_to_last_marker_exec(p);
    let ghost p3 = p@;
    proof {
        lemma_template_end_modes(p0, p3);
    }
    // 7.
    p.mode = Mode::InHead;
    let ghost tm = p.template_modes@;
    let _ = p.template_modes.pop();
    proof {
        assert(p.template_modes@ == tm.drop_last());
        assert(p@ == (Parser { mode: Mode::InHead, template_modes: p3.template_modes.drop_last(), ..p3 }));
    }
    // 8.
    reset_insertion_mode_exec(p);
}

/// The "anything else" entry of the "in head" insertion mode
/// ([`in_head_anything_else`]).
pub fn in_head_anything_else_exec(p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
    ensures
        outcome_view(o, final(p)@) == in_head_anything_else(old(p)@, t@),
        parser_inv(final(p)@),
{
    pop_exec(p);
    proof {
        lemma_inv_mode(p@, Mode::AfterHead);
    }
    p.mode = Mode::AfterHead;
    ExecOutcome::Reprocess(t)
}

} // verus!
