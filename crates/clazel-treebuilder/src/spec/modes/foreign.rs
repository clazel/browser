//! HTML §13.2.6.5 "The rules for parsing tokens in foreign content".
//!
//! Modelling choices (besides those of [`super::super`]):
//! - **SVG `script`.** Scripts are not modelled, so the steps for a
//!   `script` end tag (in SVG) reduce to "pop the current node off the stack
//!   of open elements": the insertion point is not modelled, the script
//!   nesting level is restored by the same steps that raise it, the parser
//!   pause flag ends false as it started (nothing runs between), and "process
//!   the SVG script element according to the SVG rules" is not run (Phase 7;
//!   no action is returned for it).
//! - **Tag name comparison.** "node's tag name, converted to ASCII
//!   lowercase" uses the element's local name (`Elem::name`): the parser
//!   creates every element with a null prefix, so its qualified name is its
//!   local name, and an HTML element's uppercased tag name lowercases to the
//!   same string.
//! - **Adjusted SVG names.** An element created with an adjusted SVG tag
//!   name (e.g. `clipPath`) has that name as its `Elem::name` and
//!   `tag_of(name)` as its `Elem::tag` (`foreignObject` classifies as
//!   [`Tag::Foreignobject`]).

#[allow(unused_imports)]
use super::super::dispatch::*;
#[allow(unused_imports)]
use super::super::insert::*;
#[allow(unused_imports)]
use super::super::state::*;
#[allow(unused_imports)]
use super::super::tags::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The start tag names of the first "breakout" case: "b", "big",
/// "blockquote", "body", "br", "center", "code", "dd", "div", "dl", "dt",
/// "em", "embed", "h1", "h2", "h3", "h4", "h5", "h6", "head", "hr", "i",
/// "img", "li", "listing", "menu", "meta", "nobr", "ol", "p", "pre", "ruby",
/// "s", "small", "span", "strong", "strike", "sub", "sup", "table", "tt",
/// "u", "ul", "var".
pub open spec fn is_breakout_tag(t: Tag) -> bool {
    match t {
        Tag::B | Tag::Big | Tag::Blockquote | Tag::Body | Tag::Br | Tag::Center | Tag::Code | Tag::Dd | Tag::Div | Tag::Dl
        | Tag::Dt | Tag::Em | Tag::Embed | Tag::H1 | Tag::H2 | Tag::H3 | Tag::H4 | Tag::H5 | Tag::H6 | Tag::Head | Tag::Hr
        | Tag::I | Tag::Img | Tag::Li | Tag::Listing | Tag::Menu | Tag::Meta | Tag::Nobr | Tag::Ol | Tag::P | Tag::Pre
        | Tag::Ruby | Tag::S | Tag::Small | Tag::Span | Tag::Strong | Tag::Strike | Tag::Sub | Tag::Sup | Tag::Table
        | Tag::Tt | Tag::U | Tag::Ul | Tag::Var => true,
        _ => false,
    }
}

/// The token has "any attributes named "color", "face", or "size"".
pub open spec fn has_font_breakout_attr(t: TagTok) -> bool {
    has_attr(t, seq![0x63u32, 0x6f, 0x6c, 0x6f, 0x72])  // "color"
    || has_attr(t, seq![0x66u32, 0x61, 0x63, 0x65])  // "face"
    || has_attr(t, seq![0x73u32, 0x69, 0x7a, 0x65])  // "size"
}

/// The token is one of the three "breakout" cases.
pub open spec fn is_foreign_breakout(t: Tok) -> bool {
    // "A start tag whose tag name is one of: "b", … "var""
    (t is Start && is_breakout_tag(t->Start_0.tag))
    // "A start tag whose tag name is "font", if the token has any attributes
    // named "color", "face", or "size""
    || (t is Start && t->Start_0.tag == Tag::Font && has_font_breakout_attr(t->Start_0))
    // "An end tag whose tag name is "br", "p""
    || (t is End && (t->End_0.tag == Tag::Br || t->End_0.tag == Tag::P))
}

/// The steps for "an end tag whose tag name is "script", if the current
/// node is an SVG script element", as modelled (see the module comment).
pub open spec fn svg_script_end(p: Parser) -> Parser {
    // 1. "Pop the current node off the stack of open elements."
    // 2. "Let the old insertion point have the same value as the current
    // insertion point. Let the insertion point be just before the next input
    // character." (Not modelled.)
    // 3. "Increment the parser's script nesting level by one. Set the parser
    // pause flag to true." 4. "If the active speculative HTML parser is null
    // and the user agent supports SVG, then Process the SVG script element
    // according to the SVG rules." (Scripts are not run.) 5. "Decrement the
    // parser's script nesting level by one. If the parser's script nesting
    // level is zero, then set the parser pause flag to false." 6. "Let the
    // insertion point have the value of the old insertion point." (Steps 2
    // to 6 leave the modelled state as it was.)
    pop(p)
}

/// "Any other start tag": the token after the adjustments for the adjusted
/// current node `a`.
pub open spec fn adjust_foreign_start_tag(a: Elem, t: TagTok) -> TagTok {
    // "If the adjusted current node is an element in the MathML namespace,
    // adjust MathML attributes for the token."
    let t1 = if a.ns == clazel_dom::spec::Namespace::MathMl {
        adjust_mathml_attributes(t)
    } else {
        t
    };
    // "If the adjusted current node is an element in the SVG namespace, and
    // the token's tag name is one of the ones in the first column of the
    // following table, change the tag name to the name given in the
    // corresponding cell in the second column." (The name's `Tag` follows
    // the name.)
    let t2 = if a.ns == clazel_dom::spec::Namespace::Svg {
        let n = super::super::tables::svg_tag_name(t1.name);
        TagTok { name: n, tag: tag_of(n), ..t1 }
    } else {
        t1
    };
    // "If the adjusted current node is an element in the SVG namespace,
    // adjust SVG attributes for the token."
    let t3 = if a.ns == clazel_dom::spec::Namespace::Svg {
        adjust_svg_attributes(t2)
    } else {
        t2
    };
    // "Adjust foreign attributes for the token."
    adjust_foreign_attributes(t3)
}

/// "Any other end tag", steps 3 to 7 with `node` the entry at index `i` of
/// the stack of open elements.
pub open spec fn foreign_end_tag_loop(p: Parser, t: Tok, i: int) -> Outcome
    decreases i,
{
    if i <= 0 || i >= p.open.len() {
        // 3. "Loop: If node is the topmost element in the stack of open
        // elements, then return. (fragment case)"
        Outcome::Done(p)
    } else if ascii_lowercase(p.open[i].name) == t->End_0.name {
        // 4. "If node's tag name, converted to ASCII lowercase, is the same as
        // the tag name of the token, pop elements from the stack of open
        // elements until node has been popped from the stack, and then
        // return."
        Outcome::Done(pop_until_node_popped(p, p.open[i].id))
    } else if p.open[i - 1].ns != clazel_dom::spec::Namespace::Html {
        // 5. "Set node to the previous entry in the stack of open elements."
        // 6. "If node is not an element in the HTML namespace, return to the
        // step labeled loop."
        foreign_end_tag_loop(p, t, i - 1)
    } else {
        // 7. "Otherwise, process the token according to the rules given in
        // the section corresponding to the current insertion mode in HTML
        // content." (The stack is unchanged.)
        Outcome::Reprocess(p, t)
    }
}

/// §13.2.6.5 "The rules for parsing tokens in foreign content".
pub open spec fn foreign_content(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is Char && t->Char_0 == 0 {
        // 1. "A character token that is U+0000 NULL": "Parse error. Insert a
        // U+FFFD REPLACEMENT CHARACTER character."
        Outcome::Done(insert_char(p, 0xFFFD))
    } else if t is Char && is_ascii_whitespace(t->Char_0) {
        // 2. "A character token that is one of U+0009 CHARACTER TABULATION,
        // U+000A LINE FEED (LF), U+000C FORM FEED (FF), U+000D CARRIAGE
        // RETURN (CR), or U+0020 SPACE": "Insert the token's character."
        Outcome::Done(insert_char(p, t->Char_0))
    } else if t is Char {
        // 3. "Any other character token": "Insert the token's character. Set
        // the frameset-ok flag to "not ok"."
        Outcome::Done(Parser { frameset_ok: false, ..insert_char(p, t->Char_0) })
    } else if t is Comment {
        // 4. "A comment token": "Insert a comment."
        Outcome::Done(insert_comment(p, t->Comment_0, None))
    } else if t is Pi {
        // 5. "A processing instruction token": "Insert a processing
        // instruction."
        Outcome::Done(insert_pi(p, t->Pi_0, t->Pi_1, None))
    } else if t is Doctype {
        // 6. "A DOCTYPE token": "Parse error. Ignore the token."
        Outcome::Done(p)
    } else if is_foreign_breakout(t) {
        // 7. "A start tag whose tag name is one of: "b", "big", … "var"", "A
        // start tag whose tag name is "font", if the token has any attributes
        // named "color", "face", or "size"", "An end tag whose tag name is
        // "br", "p"": "Parse error."
        // "While the current node is not a MathML text integration point, an
        // HTML integration point, or an element in the HTML namespace, pop
        // elements from the stack of open elements."
        let q = pop_while(
            p,
            |e: Elem|
                !(is_mathml_text_integration_point(e) || is_html_integration_point(e) || e.ns
                    == clazel_dom::spec::Namespace::Html),
        );
        // "Reprocess the token according to the rules given in the section
        // corresponding to the current insertion mode in HTML content."
        Outcome::Reprocess(q, t)
    } else if t is Start {
        // 8. "Any other start tag"
        let a = adjusted_current_node(p);
        // The MathML and SVG adjustments and "adjust foreign attributes for
        // the token".
        let tt = adjust_foreign_start_tag(a, t->Start_0);
        // "Insert a foreign element for the token, with the adjusted current
        // node's namespace."
        let (p1, e) = insert_foreign_element(p, tt, a.ns);
        if p1.stopped || !tt.self_closing {
            // A parser stopped by the insertion changes nothing more.
            Outcome::Done(p1)
        } else if tt.tag == Tag::Script && e.ns == clazel_dom::spec::Namespace::Svg {
            // "If the token has its self-closing flag set, then run the
            // appropriate steps from the following list:"
            // "If the token's tag name is "script", and the new current node is
            // in the SVG namespace": "Acknowledge the token's self-closing flag
            // (nothing to model), and then act as described in the steps for a
            // "script" end tag below."
            Outcome::Done(svg_script_end(p1))
        } else {
            // "Otherwise": "Pop the current node off the stack of open elements
            // and acknowledge the token's self-closing flag."
            Outcome::Done(pop(p1))
        }
    } else if t is End && t->End_0.tag == Tag::Script && p.open.len() > 0 && is_svg(current_node(p), Tag::Script) {
        // 9. "An end tag whose tag name is "script", if the current node is an
        // SVG script element" (the stack is never empty in foreign content).
        Outcome::Done(svg_script_end(p))
    } else if t is End {
        // 10. "Any other end tag": "Run these steps:"
        // 1. "Initialize node to be the current node (the bottommost node of
        // the stack)." 2. "If node's tag name, converted to ASCII lowercase,
        // is not the same as the tag name of the token, then this is a parse
        // error." Steps 3 to 7: the loop.
        foreign_end_tag_loop(p, t, p.open.len() - 1)
    } else {
        // An end-of-file token: never here (the dispatcher sends it to the
        // rules of the current insertion mode in HTML content).
        Outcome::Done(p)
    }
}

} // verus!
