//! HTML §13.2.6.5 "The rules for parsing tokens in foreign content"
//! ([`foreign_content`]), with the exec counterparts of its helpers
//! ([`is_breakout_tag`], [`has_font_breakout_attr`],
//! [`adjust_foreign_start_tag`], [`foreign_end_tag_loop`] as a loop).

use super::super::insert::*;
use super::super::names::*;
use super::super::stack::*;
use super::super::types::*;
use super::after_body::is_ascii_whitespace_exec;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`is_breakout_tag`].
pub fn is_breakout_tag_exec(t: &Tag) -> (r: bool)
    ensures
        r == is_breakout_tag(*t),
{
    matches!(
        t,
        Tag::B | Tag::Big | Tag::Blockquote | Tag::Body | Tag::Br | Tag::Center | Tag::Code | Tag::Dd | Tag::Div | Tag::Dl
            | Tag::Dt | Tag::Em | Tag::Embed | Tag::H1 | Tag::H2 | Tag::H3 | Tag::H4 | Tag::H5 | Tag::H6 | Tag::Head
            | Tag::Hr | Tag::I | Tag::Img | Tag::Li | Tag::Listing | Tag::Menu | Tag::Meta | Tag::Nobr | Tag::Ol | Tag::P
            | Tag::Pre | Tag::Ruby | Tag::S | Tag::Small | Tag::Span | Tag::Strong | Tag::Strike | Tag::Sub | Tag::Sup
            | Tag::Table | Tag::Tt | Tag::U | Tag::Ul | Tag::Var
    )
}

/// [`has_font_breakout_attr`]: the token has an attribute named "color",
/// "face" or "size".
pub fn has_font_breakout_attr_exec(t: &ExecTagTok) -> (r: bool)
    ensures
        r == has_font_breakout_attr(t@),
{
    let color: &[u32] = &[0x63u32, 0x6f, 0x6c, 0x6f, 0x72];
    let face: &[u32] = &[0x66u32, 0x61, 0x63, 0x65];
    let size: &[u32] = &[0x73u32, 0x69, 0x7a, 0x65];
    proof {
        assert(color@ =~= seq![0x63u32, 0x6f, 0x6c, 0x6f, 0x72]);
        assert(face@ =~= seq![0x66u32, 0x61, 0x63, 0x65]);
        assert(size@ =~= seq![0x73u32, 0x69, 0x7a, 0x65]);
    }
    has_attr_exec(t, color) || has_attr_exec(t, face) || has_attr_exec(t, size)
}

/// Whether the ASCII lowercase of `a` is `b` (`ascii_lowercase(a) == b`).
pub fn lowercase_is_exec(a: &[u32], b: &[u32]) -> (r: bool)
    ensures
        r == (ascii_lowercase(a@) == b@),
{
    if a.len() != b.len() {
        proof {
            assert(ascii_lowercase(a@).len() != b@.len());
        }
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> ascii_lower(#[trigger] a@[j]) == b@[j],
        decreases a.len() - i,
    {
        let (x, y) = match (a.get(i), b.get(i)) {
            (Some(x), Some(y)) => (*x, *y),
            _ => vstd::pervasive::unreached(),
        };
        if ascii_lower_exec(x) != y {
            proof {
                assert(ascii_lowercase(a@)[i as int] != b@[i as int]);
            }
            return false;
        }
        // Never saturates: i < a.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(ascii_lowercase(a@) =~= b@);
    }
    true
}

/// "Any other start tag": the adjustments of the token for the adjusted
/// current node's namespace `ns` ([`adjust_foreign_start_tag`]), in place.
pub fn adjust_foreign_start_tag_exec(ns: &Namespace, t: &mut ExecTagTok)
    requires
        tok_tagged(old(t)@),
    ensures
        forall|a: Elem| a.ns == *ns ==> final(t)@ == #[trigger] adjust_foreign_start_tag(a, old(t)@),
        tok_tagged(final(t)@),
{
    // "If the adjusted current node is an element in the MathML namespace,
    // adjust MathML attributes for the token."
    if matches!(ns, Namespace::MathMl) {
        adjust_mathml_attributes_exec(t);
    }
    // "If the adjusted current node is an element in the SVG namespace, and
    // the token's tag name is one of the ones in the first column of the
    // following table, change the tag name to the name given in the
    // corresponding cell in the second column."
    if matches!(ns, Namespace::Svg) {
        if let Some(v) = svg_tag_name_exec(t.name.as_slice()) {
            t.tag = tag_of_exec(v.as_slice());
            t.name = v;
        }
        // "If the adjusted current node is an element in the SVG namespace,
        // adjust SVG attributes for the token."
        adjust_svg_attributes_exec(t);
    }
    // "Adjust foreign attributes for the token."
    adjust_foreign_attributes_exec(t);
}

/// "Any other end tag", steps 3 to 7 ([`foreign_end_tag_loop`]) from the
/// current node, as a loop.
pub fn foreign_end_tag_loop_exec(p: &mut ParserBuf, t: ExecTagTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
    ensures
        outcome_view(o, final(p)@) == foreign_end_tag_loop(
            old(p)@,
            Tok::End(t@),
            old(p)@.open.len() - 1,
        ),
        parser_inv(final(p)@),
{
    let ghost tok = Tok::End(t@);
    let n = p.open.len();
    if n == 0 {
        return ExecOutcome::Done;
    }
    // 1. "Initialize node to be the current node (the bottommost node of the
    // stack)."
    let mut i: usize = n.saturating_sub(1);
    loop
        invariant
            p@ == old(p)@,
            parser_inv(p@),
            n == p.open@.len(),
            i < n,
            foreign_end_tag_loop(p@, tok, i as int) == foreign_end_tag_loop(p@, tok, n - 1),
            tok == Tok::End(t@),
        decreases i,
    {
        // 3. "Loop: If node is the topmost element in the stack of open
        // elements, then return. (fragment case)"
        if i == 0 {
            return ExecOutcome::Done;
        }
        let (hit, id) = match p.open.get(i) {
            Some(e) => (lowercase_is_exec(e.name.as_slice(), t.name.as_slice()), e.id),
            None => vstd::pervasive::unreached(),
        };
        // 4. "If node's tag name, converted to ASCII lowercase, is the same
        // as the tag name of the token, pop elements from the stack of open
        // elements until node has been popped from the stack, and then
        // return."
        if hit {
            pop_until_node_popped_exec(p, id);
            return ExecOutcome::Done;
        }
        // 5. "Set node to the previous entry in the stack of open elements."
        let html = match p.open.get(i.saturating_sub(1)) {
            Some(e) => is_html_ns(e),
            None => vstd::pervasive::unreached(),
        };
        // 7. "Otherwise, process the token according to the rules given in
        // the section corresponding to the current insertion mode in HTML
        // content."
        if html {
            return ExecOutcome::Reprocess(ExecTok::End(t));
        }
        // 6. "If node is not an element in the HTML namespace, return to the
        // step labeled loop."
        i = i.saturating_sub(1);
    }
}

/// §13.2.6.5 "The rules for parsing tokens in foreign content"
/// ([`foreign_content`]). The dispatcher applies them only in foreign
/// content (the adjusted current node is not an HTML element).
pub fn foreign_content_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        in_foreign_content(old(p)@),
        t@ is Start ==> tok_tagged(t@->Start_0),
    ensures
        outcome_view(o, final(p)@) == foreign_content(_env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    match t {
        ExecTok::Char(c) => {
            if c == 0 {
                // 1. "Parse error. Insert a U+FFFD REPLACEMENT CHARACTER
                // character."
                insert_char_exec(p, 0xFFFD);
            } else if is_ascii_whitespace_exec(c) {
                // 2. "Insert the token's character."
                insert_char_exec(p, c);
            } else {
                // 3. "Insert the token's character. Set the frameset-ok flag
                // to "not ok"."
                insert_char_exec(p, c);
                p.frameset_ok = false;
            }
            ExecOutcome::Done
        },
        ExecTok::Comment(data) => {
            // 4. "Insert a comment."
            insert_comment_exec(p, data, None);
            ExecOutcome::Done
        },
        ExecTok::Pi(target, data) => {
            // 5. "Insert a processing instruction."
            insert_pi_exec(p, target, data, None);
            ExecOutcome::Done
        },
        // 6. "A DOCTYPE token": "Parse error. Ignore the token."
        ExecTok::Doctype { .. } => ExecOutcome::Done,
        ExecTok::Start(tt) => foreign_start_exec(_env, p, tt),
        ExecTok::End(tt) => foreign_end_exec(_env, p, tt),
        // An end-of-file token: never here.
        ExecTok::Eof => ExecOutcome::Done,
    }
}

/// [`foreign_content`] for a start tag (split from [`foreign_content_exec`]
/// to keep each proof small).
fn foreign_start_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, tt: ExecTagTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        in_foreign_content(old(p)@),
        tok_tagged(tt@),
    ensures
        outcome_view(o, final(p)@) == foreign_content(_env.enc(), old(p)@, Tok::Start(tt@)),
        parser_inv(final(p)@),
{
        if is_breakout_tag_exec(&tt.tag) || (matches!(tt.tag, Tag::Font) && has_font_breakout_attr_exec(&tt)) {
            // 7.
            breakout_exec(p);
            return ExecOutcome::Reprocess(ExecTok::Start(tt));
        }
        // 8. "Any other start tag"
        let ns = copy_ns(&adjusted_current_node_exec(p).ns);
        let mut tt = tt;
        adjust_foreign_start_tag_exec(&ns, &mut tt);
        // "Insert a foreign element for the token, with the adjusted
        // current node's namespace."
        let _ = insert_foreign_element_exec(p, &tt, ns);
        // "If the token has its self-closing flag set": for an SVG
        // "script", the steps for a "script" end tag (as modelled, "pop
        // the current node"); otherwise "pop the current node off the
        // stack of open elements". (A parser stopped by the insertion
        // changes nothing more.)
        if !p.stopped && tt.self_closing {
            pop_exec(p);
        }
        ExecOutcome::Done
}

/// [`foreign_content`] for an end tag (split from [`foreign_content_exec`]).
fn foreign_end_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, tt: ExecTagTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        in_foreign_content(old(p)@),
    ensures
        outcome_view(o, final(p)@) == foreign_content(_env.enc(), old(p)@, Tok::End(tt@)),
        parser_inv(final(p)@),
{
        if matches!(tt.tag, Tag::Br | Tag::P) {
            // 7.
            breakout_exec(p);
            return ExecOutcome::Reprocess(ExecTok::End(tt));
        }
        if matches!(tt.tag, Tag::Script) && !p.open.is_empty() {
            let e = current_node_exec(p);
            if matches!(e.ns, Namespace::Svg) && matches!(e.tag, Tag::Script) {
                // 9. "An end tag whose tag name is "script", if the current
                // node is an SVG script element": the steps, as modelled
                // ([`svg_script_end`]).
                pop_exec(p);
                return ExecOutcome::Done;
            }
        }
        // 10. "Any other end tag"
        foreign_end_tag_loop_exec(p, tt)
}

/// Step 7's popping: "While the current node is not a MathML text
/// integration point, an HTML integration point, or an element in the HTML
/// namespace, pop elements from the stack of open elements."
fn breakout_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == pop_while(
            old(p)@,
            |e: Elem|
                !(is_mathml_text_integration_point(e) || is_html_integration_point(e) || e.ns
                    == clazel_dom::spec::Namespace::Html),
        ),
        parser_inv(final(p)@),
{
    let ghost f = |e: Elem|
        !(is_mathml_text_integration_point(e) || is_html_integration_point(e) || e.ns == clazel_dom::spec::Namespace::Html);
    pop_while_exec(p, &ElemPred::NotHtmlContent, Ghost(f));
}

} // verus!
