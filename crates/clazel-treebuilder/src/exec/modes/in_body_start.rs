//! HTML §13.2.6.4.7 the "in body" insertion mode, its start tag cases
//! ([`in_body_start_tag_exec`], the exec form of [`in_body_start_tag`]),
//! tested in the standard's order like the spec function. The cases that
//! are their own spec functions are in [`super::in_body_start_cases`].

use super::in_body_start_cases::*;
#[allow(unused_imports)]
use super::spec::*;
use crate::exec::formatting::*;
#[cfg(verus_only)]
use crate::exec::frame::*;
use crate::exec::insert::*;
use crate::exec::stack::*;
use crate::exec::types::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Tag groups

/// [`is_in_head_start_tag`].
pub fn is_in_head_start_tag_exec(t: &Tag) -> (r: bool)
    ensures
        r == is_in_head_start_tag(*t),
{
    matches!(
        t,
        Tag::Base | Tag::Basefont | Tag::Bgsound | Tag::Link | Tag::Meta | Tag::Noframes | Tag::Script | Tag::Style
            | Tag::Template | Tag::Title
    )
}

/// [`is_block_start_tag`].
pub fn is_block_start_tag_exec(t: &Tag) -> (r: bool)
    ensures
        r == is_block_start_tag(*t),
{
    matches!(
        t,
        Tag::Address | Tag::Article | Tag::Aside | Tag::Blockquote | Tag::Center | Tag::Details | Tag::Dialog | Tag::Dir
            | Tag::Div | Tag::Dl | Tag::Fieldset | Tag::Figcaption | Tag::Figure | Tag::Footer | Tag::Header | Tag::Hgroup
            | Tag::Main | Tag::Menu | Tag::Nav | Tag::Ol | Tag::P | Tag::Search | Tag::Section | Tag::Summary | Tag::Ul
    )
}

/// [`is_heading_tag`].
pub fn is_heading_tag_exec(t: &Tag) -> (r: bool)
    ensures
        r == is_heading_tag(*t),
{
    matches!(t, Tag::H1 | Tag::H2 | Tag::H3 | Tag::H4 | Tag::H5 | Tag::H6)
}

/// [`is_formatting_start_tag`].
pub fn is_formatting_start_tag_exec(t: &Tag) -> (r: bool)
    ensures
        r == is_formatting_start_tag(*t),
{
    matches!(
        t,
        Tag::B | Tag::Big | Tag::Code | Tag::Em | Tag::Font | Tag::I | Tag::S | Tag::Small | Tag::Strike | Tag::Strong
            | Tag::Tt | Tag::U
    )
}

/// [`is_applet_like`].
pub fn is_applet_like_exec(t: &Tag) -> (r: bool)
    ensures
        r == is_applet_like(*t),
{
    matches!(t, Tag::Applet | Tag::Marquee | Tag::Object)
}

/// [`is_void_start_tag`].
pub fn is_void_start_tag_exec(t: &Tag) -> (r: bool)
    ensures
        r == is_void_start_tag(*t),
{
    matches!(t, Tag::Area | Tag::Br | Tag::Embed | Tag::Img | Tag::Keygen | Tag::Wbr)
}

/// [`is_ignored_start_tag`].
pub fn is_ignored_start_tag_exec(t: &Tag) -> (r: bool)
    ensures
        r == is_ignored_start_tag(*t),
{
    matches!(
        t,
        Tag::Caption | Tag::Col | Tag::Colgroup | Tag::Frame | Tag::Head | Tag::Tbody | Tag::Td | Tag::Tfoot | Tag::Th
            | Tag::Thead | Tag::Tr
    )
}

// ---------------------------------------------------------------------
// The cases written in place in the spec function

/// Case 20, "plaintext".
fn start_plaintext_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag == Tag::Plaintext,
    ensures
        final(p)@ == (Parser {
            tokenizer: Some(TokenizerState::Plaintext),
            ..insert_html_element(close_p_if_in_button_scope(old(p)@), tt@).0
        }),
        parser_inv(final(p)@),
{
    close_p_insert_exec(p, tt);
    proof {
        lemma_inv_iff(p@);
    }
    p.tokenizer = Some(TokenizerState::Plaintext);
    proof {
        lemma_inv_iff(p@);
    }
}

/// Case 30, "b", "big", … "u".
fn start_formatting_exec(p: &mut ParserBuf, tt: ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        is_formatting_start_tag(tt@.tag),
    ensures
        final(p)@ == push_formatting(
            insert_html_element(reconstruct_formatting(old(p)@), tt@).0,
            insert_html_element(reconstruct_formatting(old(p)@), tt@).1,
            tt@,
        ),
        parser_inv(final(p)@),
{
    reconstruct_formatting_exec(p);
    insert_push_formatting_exec(p, tt);
}

/// Case 33, "applet", "marquee", "object".
fn start_applet_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        is_applet_like(tt@.tag),
    ensures
        final(p)@ == frameset_not_ok(push_marker(insert_html_element(reconstruct_formatting(old(p)@), tt@).0)),
        parser_inv(final(p)@),
{
    reconstruct_formatting_exec(p);
    let _ = insert_html_element_exec(p, tt);
    push_marker_exec(p);
    frameset_not_ok_exec(p);
}

/// Case 35, "table".
fn start_table_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag == Tag::Table,
    ensures
        final(p)@ == (Parser {
            frameset_ok: false,
            mode: Mode::InTable,
            ..insert_html_element(
                if !doc_is_quirks(old(p)@) && has_in_scope(old(p)@, Tag::P, Scope::Button) {
                    close_p_element(old(p)@)
                } else {
                    old(p)@
                },
                tt@,
            ).0
        }),
        parser_inv(final(p)@),
{
    hide(insert_html_element);
    hide(close_p_element);
    if !doc_is_quirks_exec(p) && has_in_scope_exec(p, Tag::P, &Scope::Button) {
        close_p_element_exec(p);
    }
    let _ = insert_html_element_exec(p, tt);
    proof {
        lemma_inv_iff(p@);
    }
    p.frameset_ok = false;
    p.mode = Mode::InTable;
    proof {
        lemma_inv_iff(p@);
    }
}

/// Case 39, "param", "source", "track".
fn start_param_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == insert_and_pop(old(p)@, tt@),
        parser_inv(final(p)@),
{
    insert_and_pop_exec(p, tt);
}

/// Case 43, "xmp".
fn start_xmp_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag == Tag::Xmp,
        old(p)@.mode != Mode::Text && old(p)@.mode != Mode::InTableText,
    ensures
        final(p)@ == generic_text_parsing(
            frameset_not_ok(reconstruct_formatting(close_p_if_in_button_scope(old(p)@))),
            tt@,
            true,
        ),
        parser_inv(final(p)@),
{
    close_p_if_in_button_scope_exec(p);
    reconstruct_formatting_exec(p);
    frameset_not_ok_exec(p);
    generic_text_parsing_exec(p, tt, true);
}

/// Case 44, "iframe".
fn start_iframe_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag == Tag::Iframe,
        old(p)@.mode != Mode::Text && old(p)@.mode != Mode::InTableText,
    ensures
        final(p)@ == generic_text_parsing(frameset_not_ok(old(p)@), tt@, true),
        parser_inv(final(p)@),
{
    frameset_not_ok_exec(p);
    generic_text_parsing_exec(p, tt, true);
}

/// Cases 54 (and the rest of 30, 33): "Reconstruct the active formatting
/// elements, if any. Insert an HTML element for the token."
fn start_reconstruct_insert_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == insert_html_element(reconstruct_formatting(old(p)@), tt@).0,
        parser_inv(final(p)@),
{
    reconstruct_formatting_exec(p);
    let _ = insert_html_element_exec(p, tt);
}

/// "img"
fn name_img_exec() -> (r: Vec<u32>)
    ensures
        r@ == name_img(),
{
    let l: &[u32] = &[0x69u32, 0x6du32, 0x67u32];
    proof {
        assert(l@ =~= name_img());
    }
    copy_str(l)
}

// ---------------------------------------------------------------------
// The start tags

/// The start tag cases of §13.2.6.4.7 the "in body" insertion mode
/// ([`in_body_start_tag`] for the token `Tok::Start(tt)`), on a parser that
/// has not stopped, whose stack of open elements is rooted at the `html`
/// element, and whose insertion mode is neither "text" nor "in table text"
/// (`termination::rules_ok` for the "in body" rules gives the last).
pub fn in_body_start_tag_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, tt: ExecTagTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        old(p)@.mode != Mode::Text && old(p)@.mode != Mode::InTableText,
    ensures
        outcome_view(o, final(p)@) == in_body_start_tag(old(p)@, Tok::Start(tt@), tt@),
        parser_inv(final(p)@),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(close_p_if_in_button_scope);
    hide(close_p_element);
    hide(reconstruct_formatting);
    hide(push_formatting);
    hide(push_marker);
    hide(generic_text_parsing);
    hide(generate_implied_end_tags);
    hide(insert_and_pop);
    hide(has_in_scope);
    hide(doc_is_quirks);
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
    let g = &tt.tag;
    if matches!(g, Tag::Html) {
        // 7.
        in_body_start_html_exec(p, &tt);
        ExecOutcome::Done
    } else if is_in_head_start_tag_exec(g) {
        // 8.
        ExecOutcome::Using(Mode::InHead, ExecTok::Start(tt))
    } else if matches!(g, Tag::Body) {
        // 9.
        in_body_start_body_exec(p, &tt);
        ExecOutcome::Done
    } else if matches!(g, Tag::Frameset) {
        // 10.
        in_body_start_frameset_exec(p, &tt);
        ExecOutcome::Done
    } else if is_block_start_tag_exec(g) {
        // 14.
        close_p_insert_exec(p, &tt);
        ExecOutcome::Done
    } else if is_heading_tag_exec(g) {
        // 15.
        in_body_start_heading_exec(p, &tt);
        ExecOutcome::Done
    } else if matches!(g, Tag::Pre | Tag::Listing) {
        // 16.
        in_body_start_pre_exec(p, &tt);
        ExecOutcome::Done
    } else if matches!(g, Tag::Form) {
        // 17.
        in_body_start_form_exec(p, &tt);
        ExecOutcome::Done
    } else if matches!(g, Tag::Li) {
        // 18.
        in_body_start_li_exec(p, &tt);
        ExecOutcome::Done
    } else if matches!(g, Tag::Dd | Tag::Dt) {
        // 19.
        in_body_start_dd_dt_exec(p, &tt);
        ExecOutcome::Done
    } else if matches!(g, Tag::Plaintext) {
        // 20.
        start_plaintext_exec(p, &tt);
        ExecOutcome::Done
    } else if matches!(g, Tag::Button) {
        // 21.
        in_body_start_button_exec(p, &tt);
        ExecOutcome::Done
    } else if matches!(g, Tag::A) {
        // 29.
        in_body_start_a_exec(env, p, tt);
        ExecOutcome::Done
    } else if is_formatting_start_tag_exec(g) {
        // 30.
        start_formatting_exec(p, tt);
        ExecOutcome::Done
    } else if matches!(g, Tag::Nobr) {
        // 31.
        in_body_start_nobr_exec(env, p, tt);
        ExecOutcome::Done
    } else {
        in_body_start_tag_rest_exec(p, tt)
    }
}

/// [`in_body_start_tag`] from case 33 on.
fn in_body_start_tag_rest_exec(p: &mut ParserBuf, tt: ExecTagTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        old(p)@.mode != Mode::Text && old(p)@.mode != Mode::InTableText,
        !(tt@.tag == Tag::Html || is_in_head_start_tag(tt@.tag) || tt@.tag == Tag::Body || tt@.tag == Tag::Frameset
            || is_block_start_tag(tt@.tag) || is_heading_tag(tt@.tag) || tt@.tag == Tag::Pre || tt@.tag == Tag::Listing
            || tt@.tag == Tag::Form || tt@.tag == Tag::Li || tt@.tag == Tag::Dd || tt@.tag == Tag::Dt || tt@.tag
            == Tag::Plaintext || tt@.tag == Tag::Button || tt@.tag == Tag::A || is_formatting_start_tag(tt@.tag)
            || tt@.tag == Tag::Nobr),
    ensures
        outcome_view(o, final(p)@) == in_body_start_tag(old(p)@, Tok::Start(tt@), tt@),
        parser_inv(final(p)@),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(close_p_if_in_button_scope);
    hide(close_p_element);
    hide(reconstruct_formatting);
    hide(push_formatting);
    hide(push_marker);
    hide(generic_text_parsing);
    hide(generate_implied_end_tags);
    hide(insert_and_pop);
    hide(has_in_scope);
    hide(doc_is_quirks);
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
    let g = &tt.tag;
    if is_applet_like_exec(g) {
        // 33.
        start_applet_exec(p, &tt);
    } else if matches!(g, Tag::Table) {
        // 35.
        start_table_exec(p, &tt);
    } else if is_void_start_tag_exec(g) {
        // 37.
        in_body_void_start_tag_exec(p, &tt);
    } else if matches!(g, Tag::Input) {
        // 38.
        in_body_start_input_exec(p, &tt);
    } else if matches!(g, Tag::Param | Tag::Source | Tag::Track) {
        // 39.
        start_param_exec(p, &tt);
    } else if matches!(g, Tag::Hr) {
        // 40.
        in_body_start_hr_exec(p, &tt);
    } else if matches!(g, Tag::Image) {
        // 41.
        let name = name_img_exec();
        return ExecOutcome::Reprocess(
            ExecTok::Start(ExecTagTok { name, tag: Tag::Img, attrs: tt.attrs, self_closing: tt.self_closing }),
        );
    } else if matches!(g, Tag::Textarea) {
        // 42.
        in_body_start_textarea_exec(p, &tt);
    } else if matches!(g, Tag::Xmp) {
        // 43.
        start_xmp_exec(p, &tt);
    } else if matches!(g, Tag::Iframe) {
        // 44.
        start_iframe_exec(p, &tt);
    } else if matches!(g, Tag::Noembed) || (matches!(g, Tag::Noscript) && p.scripting) {
        // 45.
        generic_text_parsing_exec(p, &tt, true);
    } else if matches!(g, Tag::Select) {
        // 46.
        in_body_start_select_exec(p, &tt);
    } else if matches!(g, Tag::Option) {
        // 47.
        in_body_start_option_exec(p, &tt);
    } else if matches!(g, Tag::Optgroup) {
        // 48.
        in_body_start_optgroup_exec(p, &tt);
    } else if matches!(g, Tag::Rb | Tag::Rtc) {
        // 49.
        in_body_start_ruby_exec(p, &tt, None);
    } else if matches!(g, Tag::Rp | Tag::Rt) {
        // 50.
        in_body_start_ruby_exec(p, &tt, Some(Tag::Rtc));
    } else if matches!(g, Tag::Math) {
        // 51.
        in_body_start_math_exec(p, tt);
    } else if matches!(g, Tag::Svg) {
        // 52.
        in_body_start_svg_exec(p, tt);
    } else if is_ignored_start_tag_exec(g) {
        // 53.
    } else {
        // 54.
        start_reconstruct_insert_exec(p, &tt);
    }
    ExecOutcome::Done
}

} // verus!
