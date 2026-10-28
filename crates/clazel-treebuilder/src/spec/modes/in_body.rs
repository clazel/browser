//! HTML §13.2.6.4.7 the "in body" insertion mode, with "close a p
//! element"; the adoption agency algorithm is in [`super::adoption`].
//!
//! Modelling choices (see also [`super::super`]):
//! - **Split by token kind.** [`mode_in_body`] sends each token kind to a
//!   function: characters, start tags ([`in_body_start_tag`]), end tags
//!   ([`in_body_end_tag`]); the other kinds are handled in place. The cases
//!   are numbered 1 to 55 in the standard's order, and each function tests
//!   its cases in that order. Only cases of one token kind can match the
//!   same token, so testing a start tag against the start tag cases only
//!   changes nothing; "any other start tag" and "any other end tag" are the
//!   last cases of their kinds. Long cases are their own functions.
//! - **The sanitizer is null**, so the `html` and `body` start tag cases'
//!   steps 2.1 and 3.1 never "continue", and the parser's own steps after
//!   "run the adoption agency algorithm" see no redirection map changes.
//! - **"Act as described in the "any other end tag" entry"** (the
//!   `sarcasm` case, and the adoption agency's step 4.3) is
//!   [`in_body_any_other_end_tag`] for the token.
//! - **The `br` end tag case** applies the next entry's steps
//!   ([`in_body_void_start_tag`]) to a `br` start tag token with no
//!   attributes: the token "with no attributes" is the end tag's name, tag,
//!   no attributes and its self-closing flag (which those steps only
//!   acknowledge).
//! - **"If the next token is a U+000A LINE FEED (LF) character token, then
//!   ignore that token"** sets `Parser::skip_lf`, which the step applies to
//!   the next token (`dispatch`).
//! - **The node limit.** Where a case stores the element it just inserted
//!   (the form element pointer) or pops it, it does so only if the insertion
//!   did not stop parsing.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Names

/// "p"
pub open spec fn name_p() -> Seq<u32> {
    seq![0x70u32]
}

/// "img"
pub open spec fn name_img() -> Seq<u32> {
    seq![0x69u32, 0x6d, 0x67]
}

/// "sarcasm"
pub open spec fn name_sarcasm() -> Seq<u32> {
    seq![0x73u32, 0x61, 0x72, 0x63, 0x61, 0x73, 0x6d]
}

/// "type"
pub open spec fn name_type() -> Seq<u32> {
    seq![0x74u32, 0x79, 0x70, 0x65]
}

/// "hidden"
pub open spec fn name_hidden() -> Seq<u32> {
    seq![0x68u32, 0x69, 0x64, 0x64, 0x65, 0x6e]
}

// ---------------------------------------------------------------------
// Helpers

/// DOM "qualified name" of an attribute: its local name if its prefix is
/// null, otherwise its prefix, ":", and its local name.
pub open spec fn qualified_name(a: Attr) -> Seq<u32> {
    match a.prefix {
        None => a.local_name,
        Some(px) => px + seq![0x3au32] + a.local_name,
    }
}

/// One of `attrs` has the (qualified) name `name`.
pub open spec fn attrs_have_name(attrs: Seq<Attr>, name: Seq<u32>) -> bool
    decreases attrs.len(),
{
    if attrs.len() == 0 {
        false
    } else if qualified_name(attrs[0]) == name {
        true
    } else {
        attrs_have_name(attrs.drop_first(), name)
    }
}

/// Element `el` "has an attribute whose name is" `name`.
pub open spec fn element_has_attribute_named(doc: dom::Document, el: NodeId, name: Seq<u32>) -> bool {
    dom::valid(doc, el) && match doc.nodes[el as int].kind {
        dom::NodeKind::Element { attributes, .. } => attrs_have_name(attributes, name),
        _ => false,
    }
}

/// The `html` and `body` start tag cases' attribute loop, from the token's
/// attribute at index `i`: "For each attribute on the token: … If
/// element does not have an attribute whose name is attribute's name, then
/// add attribute's name and its corresponding value to element." (The
/// sanitizer step before it never continues: the sanitizer is null.)
pub open spec fn add_missing_attributes(p: Parser, el: NodeId, attrs: Seq<Attr>, i: int) -> Parser
    decreases attrs.len() - i,
{
    if i < 0 || i >= attrs.len() {
        p
    } else {
        let a = attrs[i];
        let q = if !p.stopped && !element_has_attribute_named(p.doc, el, a.local_name) {
            Parser { doc: dom::append_attribute(p.doc, el, a), ..p }
        } else {
            p
        };
        add_missing_attributes(q, el, attrs, i + 1)
    }
}

/// The element is an HTML element with the token's tag name.
pub open spec fn is_html_named(e: Elem, name: Seq<u32>) -> bool {
    e.ns == Namespace::Html && e.name == name
}

/// "The stack of open elements has an element in scope that is an HTML
/// element with the same tag name as that of the token."
pub open spec fn has_same_name_in_scope(p: Parser, tt: TagTok) -> bool {
    in_scope_from(p.open, p.open.len() as int, |e: Elem| is_html_named(e, tt.name), Scope::Default)
}

/// "Pop elements from the stack of open elements until an HTML element with
/// the same tag name as the token has been popped from the stack."
pub open spec fn pop_until_named_popped(p: Parser, name: Seq<u32>) -> Parser
    decreases p.open.len(),
{
    if p.open.len() == 0 {
        p
    } else if is_html_named(current_node(p), name) {
        pop(p)
    } else {
        pop_until_named_popped(pop(p), name)
    }
}

/// "Insert an HTML element for the token. Immediately pop the current node
/// off the stack of open elements." (No pop if the insertion stopped
/// parsing.)
pub open spec fn insert_and_pop(p: Parser, tt: TagTok) -> Parser {
    let q = insert_html_element(p, tt).0;
    if q.stopped {
        q
    } else {
        pop(q)
    }
}

/// "Set the frameset-ok flag to "not ok"."
pub open spec fn frameset_not_ok(p: Parser) -> Parser {
    Parser { frameset_ok: false, ..p }
}

/// "If the stack of open elements has a p element in button scope, then
/// close a p element."
pub open spec fn close_p_if_in_button_scope(p: Parser) -> Parser {
    if has_in_scope(p, Tag::P, Scope::Button) {
        close_p_element(p)
    } else {
        p
    }
}

/// The document is in quirks mode.
pub open spec fn doc_is_quirks(p: Parser) -> bool {
    p.doc.nodes[0].kind is Document && p.doc.nodes[0].kind->Document_mode == DocumentMode::Quirks
}

// ---------------------------------------------------------------------
// Close a p element

/// "When the steps above say the user agent is to close a p element, it
/// means that the user agent must run the following steps:"
pub open spec fn close_p_element(p: Parser) -> Parser {
    // 1. "Generate implied end tags, except for p elements."
    let q = generate_implied_end_tags(p, Some(Tag::P));
    // 2. "If the current node is not a p element, then this is a parse
    // error."
    // 3. "Pop elements from the stack of open elements until a p element has
    // been popped from the stack."
    pop_until_popped(q, Tag::P)
}

// ---------------------------------------------------------------------
// Tag groups

/// Case 8's start tags: "base", "basefont", "bgsound", "link", "meta",
/// "noframes", "script", "style", "template", "title".
pub open spec fn is_in_head_start_tag(t: Tag) -> bool {
    match t {
        Tag::Base | Tag::Basefont | Tag::Bgsound | Tag::Link | Tag::Meta | Tag::Noframes | Tag::Script | Tag::Style
        | Tag::Template | Tag::Title => true,
        _ => false,
    }
}

/// Case 14: "address", "article", "aside", "blockquote", "center",
/// "details", "dialog", "dir", "div", "dl", "fieldset", "figcaption",
/// "figure", "footer", "header", "hgroup", "main", "menu", "nav", "ol",
/// "p", "search", "section", "summary", "ul".
pub open spec fn is_block_start_tag(t: Tag) -> bool {
    match t {
        Tag::Address | Tag::Article | Tag::Aside | Tag::Blockquote | Tag::Center | Tag::Details | Tag::Dialog | Tag::Dir
        | Tag::Div | Tag::Dl | Tag::Fieldset | Tag::Figcaption | Tag::Figure | Tag::Footer | Tag::Header | Tag::Hgroup
        | Tag::Main | Tag::Menu | Tag::Nav | Tag::Ol | Tag::P | Tag::Search | Tag::Section | Tag::Summary | Tag::Ul => true,
        _ => false,
    }
}

/// "h1", "h2", "h3", "h4", "h5", "h6".
pub open spec fn is_heading_tag(t: Tag) -> bool {
    match t {
        Tag::H1 | Tag::H2 | Tag::H3 | Tag::H4 | Tag::H5 | Tag::H6 => true,
        _ => false,
    }
}

/// Case 22: "address", "article", "aside", "blockquote", "button",
/// "center", "details", "dialog", "dir", "div", "dl", "fieldset",
/// "figcaption", "figure", "footer", "header", "hgroup", "listing", "main",
/// "menu", "nav", "ol", "pre", "search", "section", "select", "summary",
/// "ul".
pub open spec fn is_block_end_tag(t: Tag) -> bool {
    match t {
        Tag::Address | Tag::Article | Tag::Aside | Tag::Blockquote | Tag::Button | Tag::Center | Tag::Details | Tag::Dialog
        | Tag::Dir | Tag::Div | Tag::Dl | Tag::Fieldset | Tag::Figcaption | Tag::Figure | Tag::Footer | Tag::Header
        | Tag::Hgroup | Tag::Listing | Tag::Main | Tag::Menu | Tag::Nav | Tag::Ol | Tag::Pre | Tag::Search | Tag::Section
        | Tag::Select | Tag::Summary | Tag::Ul => true,
        _ => false,
    }
}

/// Case 30: "b", "big", "code", "em", "font", "i", "s", "small", "strike",
/// "strong", "tt", "u".
pub open spec fn is_formatting_start_tag(t: Tag) -> bool {
    match t {
        Tag::B | Tag::Big | Tag::Code | Tag::Em | Tag::Font | Tag::I | Tag::S | Tag::Small | Tag::Strike | Tag::Strong
        | Tag::Tt | Tag::U => true,
        _ => false,
    }
}

/// Case 32: "a", "b", "big", "code", "em", "font", "i", "nobr", "s",
/// "small", "strike", "strong", "tt", "u".
pub open spec fn is_formatting_end_tag(t: Tag) -> bool {
    match t {
        Tag::A | Tag::B | Tag::Big | Tag::Code | Tag::Em | Tag::Font | Tag::I | Tag::Nobr | Tag::S | Tag::Small
        | Tag::Strike | Tag::Strong | Tag::Tt | Tag::U => true,
        _ => false,
    }
}

/// Cases 33 and 34: "applet", "marquee", "object".
pub open spec fn is_applet_like(t: Tag) -> bool {
    match t {
        Tag::Applet | Tag::Marquee | Tag::Object => true,
        _ => false,
    }
}

/// Case 37: "area", "br", "embed", "img", "keygen", "wbr".
pub open spec fn is_void_start_tag(t: Tag) -> bool {
    match t {
        Tag::Area | Tag::Br | Tag::Embed | Tag::Img | Tag::Keygen | Tag::Wbr => true,
        _ => false,
    }
}

/// Case 53: "caption", "col", "colgroup", "frame", "head", "tbody", "td",
/// "tfoot", "th", "thead", "tr".
pub open spec fn is_ignored_start_tag(t: Tag) -> bool {
    match t {
        Tag::Caption | Tag::Col | Tag::Colgroup | Tag::Frame | Tag::Head | Tag::Tbody | Tag::Td | Tag::Tfoot | Tag::Th
        | Tag::Thead | Tag::Tr => true,
        _ => false,
    }
}

// ---------------------------------------------------------------------
// The mode

/// §13.2.6.4.7 the "in body" insertion mode.
pub open spec fn mode_in_body(env: EncFns, p: Parser, t: Tok) -> Outcome {
    match t {
        // 1. to 3.: character tokens.
        Tok::Char(c) => Outcome::Done(in_body_char(p, c)),
        // 4. "A comment token": "Insert a comment."
        Tok::Comment(data) => Outcome::Done(insert_comment(p, data, None)),
        // 5. "A processing instruction token": "Insert a processing
        // instruction."
        Tok::Pi(target, data) => Outcome::Done(insert_pi(p, target, data, None)),
        // 6. "A DOCTYPE token": "Parse error. Ignore the token."
        Tok::Doctype { .. } => Outcome::Done(p),
        // 7. to 10., 14. to 21., 29. to 31., 33., 35., 37. to 54.: start tags.
        Tok::Start(tt) => in_body_start_tag(p, t, tt),
        // 11. "An end-of-file token"
        Tok::Eof => in_body_eof(p, t),
        // 8. (the "template" end tag), 12., 13., 22. to 28., 32., 34., 36.,
        // 55.: end tags.
        Tok::End(tt) => in_body_end_tag(p, t, tt),
    }
}

/// Cases 1 to 3, character tokens.
pub open spec fn in_body_char(p: Parser, c: u32) -> Parser {
    if c == 0 {
        // 1. "A character token that is U+0000 NULL": "Parse error. Ignore the
        // token."
        p
    } else if is_ascii_whitespace(c) {
        // 2. "A character token that is one of U+0009 CHARACTER TABULATION,
        // U+000A LINE FEED (LF), U+000C FORM FEED (FF), U+000D CARRIAGE RETURN
        // (CR), or U+0020 SPACE": "Reconstruct the active formatting elements,
        // if any. Insert the token's character."
        insert_char(reconstruct_formatting(p), c)
    } else {
        // 3. "Any other character token": "Reconstruct the active formatting
        // elements, if any. Insert the token's character. Set the frameset-ok
        // flag to "not ok"."
        frameset_not_ok(insert_char(reconstruct_formatting(p), c))
    }
}

/// Case 11, "An end-of-file token".
pub open spec fn in_body_eof(p: Parser, t: Tok) -> Outcome {
    if p.template_modes.len() > 0 {
        // "If the stack of template insertion modes is not empty, then process
        // the token using the rules for the "in template" insertion mode."
        Outcome::Using(Mode::InTemplate, p, t)
    } else {
        // "Otherwise, follow these steps:" 1. "If there is a node in the stack
        // of open elements that is not either a dd element, … or the html
        // element, then this is a parse error."
        // 2. "Stop parsing."
        Outcome::Done(stop_parsing(p))
    }
}

// ---------------------------------------------------------------------
// Start tags

/// The start tag cases, in the standard's order.
pub open spec fn in_body_start_tag(p: Parser, t: Tok, tt: TagTok) -> Outcome {
    let g = tt.tag;
    if g == Tag::Html {
        // 7. "A start tag whose tag name is "html""
        Outcome::Done(in_body_start_html(p, tt))
    } else if is_in_head_start_tag(g) {
        // 8. "A start tag whose tag name is one of: "base", "basefont",
        // "bgsound", "link", "meta", "noframes", "script", "style",
        // "template", "title"": "Process the token using the rules for the
        // "in head" insertion mode."
        Outcome::Using(Mode::InHead, p, t)
    } else if g == Tag::Body {
        // 9. "A start tag whose tag name is "body""
        Outcome::Done(in_body_start_body(p, tt))
    } else if g == Tag::Frameset {
        // 10. "A start tag whose tag name is "frameset""
        Outcome::Done(in_body_start_frameset(p, tt))
    } else if is_block_start_tag(g) {
        // 14. "A start tag whose tag name is one of: "address", "article",
        // "aside", "blockquote", "center", "details", "dialog", "dir", "div",
        // "dl", "fieldset", "figcaption", "figure", "footer", "header",
        // "hgroup", "main", "menu", "nav", "ol", "p", "search", "section",
        // "summary", "ul"": "If the stack of open elements has a p element in
        // button scope, then close a p element. Insert an HTML element for the
        // token."
        Outcome::Done(insert_html_element(close_p_if_in_button_scope(p), tt).0)
    } else if is_heading_tag(g) {
        // 15. "A start tag whose tag name is one of: "h1", "h2", "h3", "h4",
        // "h5", "h6""
        Outcome::Done(in_body_start_heading(p, tt))
    } else if g == Tag::Pre || g == Tag::Listing {
        // 16. "A start tag whose tag name is one of: "pre", "listing""
        Outcome::Done(in_body_start_pre(p, tt))
    } else if g == Tag::Form {
        // 17. "A start tag whose tag name is "form""
        Outcome::Done(in_body_start_form(p, tt))
    } else if g == Tag::Li {
        // 18. "A start tag whose tag name is "li""
        Outcome::Done(in_body_start_li(p, tt))
    } else if g == Tag::Dd || g == Tag::Dt {
        // 19. "A start tag whose tag name is one of: "dd", "dt""
        Outcome::Done(in_body_start_dd_dt(p, tt))
    } else if g == Tag::Plaintext {
        // 20. "A start tag whose tag name is "plaintext"": "If the stack of
        // open elements has a p element in button scope, then close a p
        // element. Insert an HTML element for the token. Switch the tokenizer
        // to the PLAINTEXT state."
        let q = insert_html_element(close_p_if_in_button_scope(p), tt).0;
        Outcome::Done(Parser { tokenizer: Some(TokenizerState::Plaintext), ..q })
    } else if g == Tag::Button {
        // 21. "A start tag whose tag name is "button""
        Outcome::Done(in_body_start_button(p, tt))
    } else if g == Tag::A {
        // 29. "A start tag whose tag name is "a""
        Outcome::Done(in_body_start_a(p, tt))
    } else if is_formatting_start_tag(g) {
        // 30. "A start tag whose tag name is one of: "b", "big", "code", "em",
        // "font", "i", "s", "small", "strike", "strong", "tt", "u"":
        // "Reconstruct the active formatting elements, if any. Insert an HTML
        // element for the token. Push onto the list of active formatting
        // elements that element."
        let (q, e) = insert_html_element(reconstruct_formatting(p), tt);
        Outcome::Done(push_formatting(q, e, tt))
    } else if g == Tag::Nobr {
        // 31. "A start tag whose tag name is "nobr""
        Outcome::Done(in_body_start_nobr(p, tt))
    } else if is_applet_like(g) {
        // 33. "A start tag whose tag name is one of: "applet", "marquee",
        // "object"": "Reconstruct the active formatting elements, if any.
        // Insert an HTML element for the token. Insert a marker at the end of
        // the list of active formatting elements. Set the frameset-ok flag to
        // "not ok"."
        let q = insert_html_element(reconstruct_formatting(p), tt).0;
        Outcome::Done(frameset_not_ok(push_marker(q)))
    } else if g == Tag::Table {
        // 35. "A start tag whose tag name is "table"": "If the Document is not
        // set to quirks mode, and the stack of open elements has a p element in
        // button scope, then close a p element. Insert an HTML element for the
        // token. Set the frameset-ok flag to "not ok". Switch the insertion
        // mode to "in table"."
        let q = if !doc_is_quirks(p) && has_in_scope(p, Tag::P, Scope::Button) {
            close_p_element(p)
        } else {
            p
        };
        let q1 = insert_html_element(q, tt).0;
        Outcome::Done(Parser { frameset_ok: false, mode: Mode::InTable, ..q1 })
    } else if is_void_start_tag(g) {
        // 37. "A start tag whose tag name is one of: "area", "br", "embed",
        // "img", "keygen", "wbr""
        Outcome::Done(in_body_void_start_tag(p, tt))
    } else if g == Tag::Input {
        // 38. "A start tag whose tag name is "input""
        Outcome::Done(in_body_start_input(p, tt))
    } else if g == Tag::Param || g == Tag::Source || g == Tag::Track {
        // 39. "A start tag whose tag name is one of: "param", "source",
        // "track"": "Insert an HTML element for the token. Immediately pop the
        // current node off the stack of open elements. Acknowledge the token's
        // self-closing flag, if it is set." (Nothing to model.)
        Outcome::Done(insert_and_pop(p, tt))
    } else if g == Tag::Hr {
        // 40. "A start tag whose tag name is "hr""
        Outcome::Done(in_body_start_hr(p, tt))
    } else if g == Tag::Image {
        // 41. "A start tag whose tag name is "image"": "Parse error. Change the
        // token's tag name to "img" and reprocess it. (Don't ask.)"
        Outcome::Reprocess(p, Tok::Start(TagTok { name: name_img(), tag: Tag::Img, ..tt }))
    } else if g == Tag::Textarea {
        // 42. "A start tag whose tag name is "textarea""
        Outcome::Done(in_body_start_textarea(p, tt))
    } else if g == Tag::Xmp {
        // 43. "A start tag whose tag name is "xmp"": "If the stack of open
        // elements has a p element in button scope, then close a p element.
        // Reconstruct the active formatting elements, if any. Set the
        // frameset-ok flag to "not ok". Follow the generic raw text element
        // parsing algorithm."
        let q = frameset_not_ok(reconstruct_formatting(close_p_if_in_button_scope(p)));
        Outcome::Done(generic_text_parsing(q, tt, true))
    } else if g == Tag::Iframe {
        // 44. "A start tag whose tag name is "iframe"": "Set the frameset-ok
        // flag to "not ok". Follow the generic raw text element parsing
        // algorithm."
        Outcome::Done(generic_text_parsing(frameset_not_ok(p), tt, true))
    } else if g == Tag::Noembed || (g == Tag::Noscript && p.scripting) {
        // 45. "A start tag whose tag name is "noembed"", "A start tag whose
        // tag name is "noscript", if scripting mode is not Disabled": "Follow
        // the generic raw text element parsing algorithm."
        Outcome::Done(generic_text_parsing(p, tt, true))
    } else if g == Tag::Select {
        // 46. "A start tag whose tag name is "select""
        Outcome::Done(in_body_start_select(p, tt))
    } else if g == Tag::Option {
        // 47. "A start tag whose tag name is "option""
        Outcome::Done(in_body_start_option(p, tt))
    } else if g == Tag::Optgroup {
        // 48. "A start tag whose tag name is "optgroup""
        Outcome::Done(in_body_start_optgroup(p, tt))
    } else if g == Tag::Rb || g == Tag::Rtc {
        // 49. "A start tag whose tag name is one of: "rb", "rtc"": "If the
        // stack of open elements has a ruby element in scope, then generate
        // implied end tags. If the current node is not now a ruby element,
        // this is a parse error. Insert an HTML element for the token."
        let q = if has_in_scope(p, Tag::Ruby, Scope::Default) {
            generate_implied_end_tags(p, None)
        } else {
            p
        };
        Outcome::Done(insert_html_element(q, tt).0)
    } else if g == Tag::Rp || g == Tag::Rt {
        // 50. "A start tag whose tag name is one of: "rp", "rt"": "If the
        // stack of open elements has a ruby element in scope, then generate
        // implied end tags, except for rtc elements. If the current node is
        // not now a rtc element or a ruby element, this is a parse error.
        // Insert an HTML element for the token."
        let q = if has_in_scope(p, Tag::Ruby, Scope::Default) {
            generate_implied_end_tags(p, Some(Tag::Rtc))
        } else {
            p
        };
        Outcome::Done(insert_html_element(q, tt).0)
    } else if g == Tag::Math {
        // 51. "A start tag whose tag name is "math""
        Outcome::Done(in_body_start_math(p, tt))
    } else if g == Tag::Svg {
        // 52. "A start tag whose tag name is "svg""
        Outcome::Done(in_body_start_svg(p, tt))
    } else if is_ignored_start_tag(g) {
        // 53. "A start tag whose tag name is one of: "caption", "col",
        // "colgroup", "frame", "head", "tbody", "td", "tfoot", "th", "thead",
        // "tr"": "Parse error. Ignore the token."
        Outcome::Done(p)
    } else {
        // 54. "Any other start tag": "Reconstruct the active formatting
        // elements, if any. Insert an HTML element for the token."
        Outcome::Done(insert_html_element(reconstruct_formatting(p), tt).0)
    }
}

/// Case 7, "A start tag whose tag name is "html"".
pub open spec fn in_body_start_html(p: Parser, tt: TagTok) -> Parser {
    // "Parse error."
    if open_has_html(p, Tag::Template) {
        // "If there is a template element on the stack of open elements, then
        // ignore the token."
        p
    } else {
        // "Otherwise:" 1. "Let htmlElement be the top element of the stack of
        // open elements."
        let html_element = p.open[0];
        // 2. "For each attribute on the token:" 2.1 (the sanitizer is null)
        // 2.2 "If htmlElement does not have an attribute whose name is
        // attribute's name, then add attribute's name and its corresponding
        // value to htmlElement."
        add_missing_attributes(p, html_element.id, tt.attrs, 0)
    }
}

/// Case 9, "A start tag whose tag name is "body"".
pub open spec fn in_body_start_body(p: Parser, tt: TagTok) -> Parser {
    // "Parse error."
    if p.open.len() == 1 || !is_html(p.open[1], Tag::Body) || open_has_html(p, Tag::Template) {
        // "If the stack of open elements has only one node on it, or if the
        // second element on the stack of open elements is not a body element,
        // or if there is a template element on the stack of open elements,
        // then ignore the token."
        p
    } else {
        // "Otherwise:" 1. "Set the frameset-ok flag to "not ok"."
        let q = frameset_not_ok(p);
        // 2. "Let bodyElement be the body element (the second element) on the
        // stack of open elements."
        let body_element = q.open[1];
        // 3. "For each attribute on the token:" 3.1 (the sanitizer is null)
        // 3.2 "If bodyElement does not have an attribute whose name is
        // attribute's name, then add attribute's name and its corresponding
        // value to bodyElement."
        add_missing_attributes(q, body_element.id, tt.attrs, 0)
    }
}

/// Case 10, "A start tag whose tag name is "frameset"".
pub open spec fn in_body_start_frameset(p: Parser, tt: TagTok) -> Parser {
    // "Parse error."
    if p.open.len() == 1 || !is_html(p.open[1], Tag::Body) {
        // "If the stack of open elements has only one node on it, or if the
        // second element on the stack of open elements is not a body element,
        // then ignore the token."
        p
    } else if !p.frameset_ok {
        // "If the frameset-ok flag is set to "not ok", ignore the token."
        p
    } else {
        // "Otherwise, run the following steps:" 1. "Remove the second element
        // on the stack of open elements from its parent node, if it has one."
        let q1 = dom_remove(p, p.open[1].id);
        // 2. "Pop all the nodes from the bottom of the stack of open elements,
        // from the current node up to, but not including, the root html
        // element."
        let q2 = Parser { open: q1.open.take(1), ..q1 };
        // 3. "Insert an HTML element for the token."
        let q3 = insert_html_element(q2, tt).0;
        // 4. "Switch the insertion mode to "in frameset"."
        Parser { mode: Mode::InFrameset, ..q3 }
    }
}

/// Case 15, "A start tag whose tag name is one of: "h1", "h2", "h3", "h4",
/// "h5", "h6"".
pub open spec fn in_body_start_heading(p: Parser, tt: TagTok) -> Parser {
    // "If the stack of open elements has a p element in button scope, then
    // close a p element."
    let q = close_p_if_in_button_scope(p);
    // "If the current node is an HTML element whose tag name is one of "h1",
    // "h2", "h3", "h4", "h5", or "h6", then this is a parse error; pop the
    // current node off the stack of open elements."
    let q1 = if q.open.len() > 0 && is_heading(current_node(q)) {
        pop(q)
    } else {
        q
    };
    // "Insert an HTML element for the token."
    insert_html_element(q1, tt).0
}

/// Case 16, "A start tag whose tag name is one of: "pre", "listing"".
pub open spec fn in_body_start_pre(p: Parser, tt: TagTok) -> Parser {
    // "If the stack of open elements has a p element in button scope, then
    // close a p element."
    // "Insert an HTML element for the token."
    let q = insert_html_element(close_p_if_in_button_scope(p), tt).0;
    // "If the next token is a U+000A LINE FEED (LF) character token, then
    // ignore that token and move on to the next one."
    // "Set the frameset-ok flag to "not ok"."
    Parser { skip_lf: true, frameset_ok: false, ..q }
}

/// Case 17, "A start tag whose tag name is "form"".
pub open spec fn in_body_start_form(p: Parser, tt: TagTok) -> Parser {
    if p.form is Some && !parsing_template_contents(p) {
        // "If the form element pointer is not null, and the parser is not
        // parsing template contents, then this is a parse error; ignore the
        // token."
        p
    } else {
        // "Otherwise:" 1. "If the stack of open elements has a p element in
        // button scope, then close a p element."
        let q = close_p_if_in_button_scope(p);
        // 2. "Insert an HTML element for the token, and, if the parser is not
        // parsing template contents, set the form element pointer to point to
        // the element created."
        let (q1, e) = insert_html_element(q, tt);
        if !q1.stopped && !parsing_template_contents(q) {
            Parser { form: Some(e.id), ..q1 }
        } else {
            q1
        }
    }
}

/// Case 18's steps 3 to 5 ("Loop") with node the entry at index `i`; the
/// parser at the step labeled "done".
pub open spec fn li_loop(p: Parser, i: int) -> Parser
    decreases i + 1,
{
    if i < 0 {
        // Unreachable: the html element at the top is special (step 4).
        p
    } else {
        let node = p.open[i];
        if is_html(node, Tag::Li) {
            // 3. "Loop: If node is an li element, then run these substeps:"
            // 3.1 "Generate implied end tags, except for li elements."
            let q = generate_implied_end_tags(p, Some(Tag::Li));
            // 3.2 "If the current node is not an li element, then this is a
            // parse error."
            // 3.3 "Pop elements from the stack of open elements until an li
            // element has been popped from the stack."
            // 3.4 "Jump to the step labeled done below."
            pop_until_popped(q, Tag::Li)
        } else if is_special(node) && !is_html(node, Tag::Address) && !is_html(node, Tag::Div) && !is_html(node, Tag::P) {
            // 4. "If node is in the special category, but is not an address,
            // div, or p element, then jump to the step labeled done below."
            p
        } else {
            // 5. "Otherwise, set node to the previous entry in the stack of open
            // elements and return to the step labeled loop."
            li_loop(p, i - 1)
        }
    }
}

/// Case 18, "A start tag whose tag name is "li"".
pub open spec fn in_body_start_li(p: Parser, tt: TagTok) -> Parser {
    // "Run these steps:" 1. "Set the frameset-ok flag to "not ok"."
    let q = frameset_not_ok(p);
    // 2. "Initialize node to be the current node (the bottommost node of the
    // stack)." 3. to 5.
    let q1 = li_loop(q, q.open.len() - 1);
    // 6. "Done: If the stack of open elements has a p element in button
    // scope, then close a p element."
    // 7. "Finally, insert an HTML element for the token."
    insert_html_element(close_p_if_in_button_scope(q1), tt).0
}

/// Case 19's steps 3 to 6 ("Loop") with node the entry at index `i`; the
/// parser at the step labeled "done".
pub open spec fn dd_dt_loop(p: Parser, i: int) -> Parser
    decreases i + 1,
{
    if i < 0 {
        // Unreachable: the html element at the top is special (step 5).
        p
    } else {
        let node = p.open[i];
        if is_html(node, Tag::Dd) {
            // 3. "Loop: If node is a dd element, then run these substeps:" 3.1
            // "Generate implied end tags, except for dd elements." 3.2 "If the
            // current node is not a dd element, then this is a parse error."
            // 3.3 "Pop elements from the stack of open elements until a dd
            // element has been popped from the stack." 3.4 "Jump to the step
            // labeled done below."
            pop_until_popped(generate_implied_end_tags(p, Some(Tag::Dd)), Tag::Dd)
        } else if is_html(node, Tag::Dt) {
            // 4. "If node is a dt element, then run these substeps:" 4.1
            // "Generate implied end tags, except for dt elements." 4.2 "If the
            // current node is not a dt element, then this is a parse error."
            // 4.3 "Pop elements from the stack of open elements until a dt
            // element has been popped from the stack." 4.4 "Jump to the step
            // labeled done below."
            pop_until_popped(generate_implied_end_tags(p, Some(Tag::Dt)), Tag::Dt)
        } else if is_special(node) && !is_html(node, Tag::Address) && !is_html(node, Tag::Div) && !is_html(node, Tag::P) {
            // 5. "If node is in the special category, but is not an address,
            // div, or p element, then jump to the step labeled done below."
            p
        } else {
            // 6. "Otherwise, set node to the previous entry in the stack of open
            // elements and return to the step labeled loop."
            dd_dt_loop(p, i - 1)
        }
    }
}

/// Case 19, "A start tag whose tag name is one of: "dd", "dt"".
pub open spec fn in_body_start_dd_dt(p: Parser, tt: TagTok) -> Parser {
    // "Run these steps:" 1. "Set the frameset-ok flag to "not ok"."
    let q = frameset_not_ok(p);
    // 2. "Initialize node to be the current node (the bottommost node of the
    // stack)." 3. to 6.
    let q1 = dd_dt_loop(q, q.open.len() - 1);
    // 7. "Done: If the stack of open elements has a p element in button
    // scope, then close a p element."
    // 8. "Finally, insert an HTML element for the token."
    insert_html_element(close_p_if_in_button_scope(q1), tt).0
}

/// Case 21, "A start tag whose tag name is "button"".
pub open spec fn in_body_start_button(p: Parser, tt: TagTok) -> Parser {
    // 1. "If the stack of open elements has a button element in scope, then
    // run these substeps:" 1.1 "Parse error." 1.2 "Generate implied end
    // tags." 1.3 "Pop elements from the stack of open elements until a button
    // element has been popped from the stack."
    let q = if has_in_scope(p, Tag::Button, Scope::Default) {
        pop_until_popped(generate_implied_end_tags(p, None), Tag::Button)
    } else {
        p
    };
    // 2. "Reconstruct the active formatting elements, if any."
    // 3. "Insert an HTML element for the token."
    let q1 = insert_html_element(reconstruct_formatting(q), tt).0;
    // 4. "Set the frameset-ok flag to "not ok"."
    frameset_not_ok(q1)
}

/// "Run the adoption agency algorithm for the token", acting as the "any
/// other end tag" entry describes when its step 4.3 says so.
pub open spec fn in_body_adoption(p: Parser, tt: TagTok) -> Parser {
    match adoption_agency(p, tt) {
        AdoptionOutcome::Done(q) => q,
        AdoptionOutcome::AnyOtherEndTag(q) => in_body_any_other_end_tag(q, tt),
    }
}

/// Case 29, "A start tag whose tag name is "a"".
pub open spec fn in_body_start_a(p: Parser, tt: TagTok) -> Parser {
    let f = p.formatting;
    let i = fmt_last_where(f, after_last_marker(f, f.len() as int), f.len() as int, |e: Elem| is_html(e, Tag::A));
    // "If the list of active formatting elements contains an a element
    // between the end of the list and the last marker on the list (or the
    // start of the list if there is no marker on the list), then this is a
    // parse error; run the adoption agency algorithm for the token, then
    // remove that element from the list of active formatting elements and the
    // stack of open elements if the adoption agency algorithm didn't already
    // remove it (it might not have if the element is not in table scope)."
    let q = if i >= 0 {
        let a = f[i]->Entry_elem;
        let q1 = in_body_adoption(p, tt);
        if q1.stopped {
            q1
        } else {
            let k = fmt_index_of(q1.formatting, q1.formatting.len() as int, a.id);
            let q2 = if k >= 0 {
                Parser { formatting: q1.formatting.remove(k), ..q1 }
            } else {
                q1
            };
            let j = open_index_of(q2, a.id);
            if j >= 0 {
                remove_open_at(q2, j)
            } else {
                q2
            }
        }
    } else {
        p
    };
    // "Reconstruct the active formatting elements, if any."
    // "Insert an HTML element for the token. Push onto the list of active
    // formatting elements that element."
    let (q3, e) = insert_html_element(reconstruct_formatting(q), tt);
    push_formatting(q3, e, tt)
}

/// Case 31, "A start tag whose tag name is "nobr"".
pub open spec fn in_body_start_nobr(p: Parser, tt: TagTok) -> Parser {
    // "Reconstruct the active formatting elements, if any."
    let q = reconstruct_formatting(p);
    // "If the stack of open elements has a nobr element in scope, then this is
    // a parse error; run the adoption agency algorithm for the token, then
    // once again reconstruct the active formatting elements, if any."
    let q1 = if has_in_scope(q, Tag::Nobr, Scope::Default) {
        reconstruct_formatting(in_body_adoption(q, tt))
    } else {
        q
    };
    // "Insert an HTML element for the token. Push onto the list of active
    // formatting elements that element."
    let (q2, e) = insert_html_element(q1, tt);
    push_formatting(q2, e, tt)
}

/// Case 37, "A start tag whose tag name is one of: "area", "br", "embed",
/// "img", "keygen", "wbr"" (and case 36's `br`).
pub open spec fn in_body_void_start_tag(p: Parser, tt: TagTok) -> Parser {
    // "Reconstruct the active formatting elements, if any."
    // "Insert an HTML element for the token. Immediately pop the current node
    // off the stack of open elements."
    let q = insert_and_pop(reconstruct_formatting(p), tt);
    // "Acknowledge the token's self-closing flag, if it is set." (Nothing to
    // model.)
    // "Set the frameset-ok flag to "not ok"."
    frameset_not_ok(q)
}

/// Case 38, "A start tag whose tag name is "input"".
pub open spec fn in_body_start_input(p: Parser, tt: TagTok) -> Parser {
    if p.context is Some && is_html(p.context->Some_0, Tag::Select) {
        // "If the parser's fragment context element is a select element
        // (fragment case):" 1. "Parse error." 2. "Ignore the token." 3.
        // "Return."
        p
    } else {
        // "If the stack of open elements has a select element in scope:" 1.
        // "Parse error." 2. "Pop elements from the stack of open elements until
        // a select element has been popped from the stack."
        let q = if has_in_scope(p, Tag::Select, Scope::Default) {
            pop_until_popped(p, Tag::Select)
        } else {
            p
        };
        // "Reconstruct the active formatting elements, if any."
        // "Insert an HTML element for the token. Immediately pop the current
        // node off the stack of open elements."
        let q1 = insert_and_pop(reconstruct_formatting(q), tt);
        // "Acknowledge the token's self-closing flag, if it is set." (Nothing
        // to model.)
        // "If the token does not have an attribute with the name "type", or if
        // it does, but that attribute's value is not an ASCII
        // case-insensitive match for "hidden", then set the frameset-ok flag
        // to "not ok"."
        match attr_value(tt.attrs, name_type()) {
            Some(v) if ascii_ci_eq(v, name_hidden()) => q1,
            _ => frameset_not_ok(q1),
        }
    }
}

/// Case 40, "A start tag whose tag name is "hr"".
pub open spec fn in_body_start_hr(p: Parser, tt: TagTok) -> Parser {
    // "If the stack of open elements has a p element in button scope, then
    // close a p element."
    let q = close_p_if_in_button_scope(p);
    // "If the stack of open elements has a select element in scope:" 1.
    // "Generate implied end tags." 2. "If the stack of open elements has an
    // option element in scope or has an optgroup element in scope, then this
    // is a parse error."
    let q1 = if has_in_scope(q, Tag::Select, Scope::Default) {
        generate_implied_end_tags(q, None)
    } else {
        q
    };
    // "Insert an HTML element for the token. Immediately pop the current node
    // off the stack of open elements."
    // "Acknowledge the token's self-closing flag, if it is set." (Nothing to
    // model.)
    // "Set the frameset-ok flag to "not ok"."
    frameset_not_ok(insert_and_pop(q1, tt))
}

/// Case 42, "A start tag whose tag name is "textarea"".
pub open spec fn in_body_start_textarea(p: Parser, tt: TagTok) -> Parser {
    // "Run these steps:" 1. "Insert an HTML element for the token."
    let q = insert_html_element(p, tt).0;
    Parser {
        // 2. "If the next token is a U+000A LINE FEED (LF) character token,
        // then ignore that token and move on to the next one."
        skip_lf: true,
        // 3. "Switch the tokenizer to the RCDATA state."
        tokenizer: Some(TokenizerState::Rcdata),
        // 4. "Set the original insertion mode to the current insertion mode."
        original_mode: q.mode,
        // 5. "Set the frameset-ok flag to "not ok"."
        frameset_ok: false,
        // 6. "Switch the insertion mode to "text"."
        mode: Mode::Text,
        ..q
    }
}

/// Case 46, "A start tag whose tag name is "select"".
pub open spec fn in_body_start_select(p: Parser, tt: TagTok) -> Parser {
    if p.context is Some && is_html(p.context->Some_0, Tag::Select) {
        // "If the parser's fragment context element is a select element
        // (fragment case):" 1. "Parse error." 2. "Ignore the token."
        p
    } else if has_in_scope(p, Tag::Select, Scope::Default) {
        // "Otherwise, if the stack of open elements has a select element in
        // scope:" 1. "Parse error." 2. "Ignore the token." 3. "Pop elements
        // from the stack of open elements until a select element has been
        // popped from the stack."
        pop_until_popped(p, Tag::Select)
    } else {
        // "Otherwise:" 1. "Reconstruct the active formatting elements, if
        // any." 2. "Insert an HTML element for the token."
        let q = insert_html_element(reconstruct_formatting(p), tt).0;
        // 3. "Set the frameset-ok flag to "not ok"."
        frameset_not_ok(q)
    }
}

/// Case 47, "A start tag whose tag name is "option"".
pub open spec fn in_body_start_option(p: Parser, tt: TagTok) -> Parser {
    let q = if has_in_scope(p, Tag::Select, Scope::Default) {
        // "If the stack of open elements has a select element in scope:" 1.
        // "Generate implied end tags except for optgroup elements." 2. "If the
        // stack of open elements has an option element in scope, then this is
        // a parse error."
        generate_implied_end_tags(p, Some(Tag::Optgroup))
    } else if p.open.len() > 0 && is_html(current_node(p), Tag::Option) {
        // "Otherwise:" 1. "If the current node is an option element, then pop
        // the current node off the stack of open elements."
        pop(p)
    } else {
        p
    };
    // "Reconstruct the active formatting elements, if any."
    // "Insert an HTML element for the token."
    insert_html_element(reconstruct_formatting(q), tt).0
}

/// Case 48, "A start tag whose tag name is "optgroup"".
pub open spec fn in_body_start_optgroup(p: Parser, tt: TagTok) -> Parser {
    let q = if has_in_scope(p, Tag::Select, Scope::Default) {
        // "If the stack of open elements has a select element in scope:" 1.
        // "Generate implied end tags." 2. "If the stack of open elements has
        // an option element in scope or has an optgroup element in scope, then
        // this is a parse error."
        generate_implied_end_tags(p, None)
    } else if p.open.len() > 0 && is_html(current_node(p), Tag::Option) {
        // "Otherwise, if the current node is an option element, then pop the
        // current node from the stack of open elements."
        pop(p)
    } else {
        p
    };
    // "Reconstruct the active formatting elements, if any."
    // "Insert an HTML element for the token."
    insert_html_element(reconstruct_formatting(q), tt).0
}

/// Case 51, "A start tag whose tag name is "math"".
pub open spec fn in_body_start_math(p: Parser, tt: TagTok) -> Parser {
    // "Reconstruct the active formatting elements, if any."
    let q = reconstruct_formatting(p);
    // "Adjust MathML attributes for the token." "Adjust foreign attributes
    // for the token."
    let t2 = adjust_foreign_attributes(adjust_mathml_attributes(tt));
    // "Insert a foreign element for the token, with MathML namespace."
    let q1 = insert_foreign_element(q, t2, Namespace::MathMl).0;
    // "If the token has its self-closing flag set, pop the current node off
    // the stack of open elements and acknowledge the token's self-closing
    // flag."
    if tt.self_closing && !q1.stopped {
        pop(q1)
    } else {
        q1
    }
}

/// Case 52, "A start tag whose tag name is "svg"".
pub open spec fn in_body_start_svg(p: Parser, tt: TagTok) -> Parser {
    // "Reconstruct the active formatting elements, if any."
    let q = reconstruct_formatting(p);
    // "Adjust SVG attributes for the token." "Adjust foreign attributes for
    // the token."
    let t2 = adjust_foreign_attributes(adjust_svg_attributes(tt));
    // "Insert a foreign element for the token, with SVG namespace."
    let q1 = insert_foreign_element(q, t2, Namespace::Svg).0;
    // "If the token has its self-closing flag set, pop the current node off
    // the stack of open elements and acknowledge the token's self-closing
    // flag."
    if tt.self_closing && !q1.stopped {
        pop(q1)
    } else {
        q1
    }
}

// ---------------------------------------------------------------------
// End tags

/// The end tag cases, in the standard's order.
pub open spec fn in_body_end_tag(p: Parser, t: Tok, tt: TagTok) -> Outcome {
    let g = tt.tag;
    if g == Tag::Template {
        // 8. "An end tag whose tag name is "template"": "Process the token
        // using the rules for the "in head" insertion mode."
        Outcome::Using(Mode::InHead, p, t)
    } else if g == Tag::Body {
        // 12. "An end tag whose tag name is "body""
        if !has_in_scope(p, Tag::Body, Scope::Default) {
            // "If the stack of open elements does not have a body element in
            // scope, this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, if there is a node in the stack of open elements that
            // is not either a dd element, … or the html element, then this is a
            // parse error." "Switch the insertion mode to "after body"."
            Outcome::Done(Parser { mode: Mode::AfterBody, ..p })
        }
    } else if g == Tag::Html {
        // 13. "An end tag whose tag name is "html""
        if !has_in_scope(p, Tag::Body, Scope::Default) {
            // "If the stack of open elements does not have a body element in
            // scope, this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, if there is a node … then this is a parse error."
            // "Switch the insertion mode to "after body"." "Reprocess the
            // token."
            Outcome::Reprocess(Parser { mode: Mode::AfterBody, ..p }, t)
        }
    } else if is_block_end_tag(g) {
        // 22. "An end tag whose tag name is one of: "address", "article",
        // "aside", "blockquote", "button", "center", "details", "dialog",
        // "dir", "div", "dl", "fieldset", "figcaption", "figure", "footer",
        // "header", "hgroup", "listing", "main", "menu", "nav", "ol", "pre",
        // "search", "section", "select", "summary", "ul""
        Outcome::Done(in_body_end_same_name(p, tt))
    } else if g == Tag::Form {
        // 23. "An end tag whose tag name is "form""
        Outcome::Done(in_body_end_form(p))
    } else if g == Tag::P {
        // 24. "An end tag whose tag name is "p"": "If the stack of open
        // elements does not have a p element in button scope, then this is a
        // parse error; insert an HTML element for a "p" start tag token with no
        // attributes. Close a p element."
        let q = if !has_in_scope(p, Tag::P, Scope::Button) {
            insert_html_element(p, start_tag_named(name_p())).0
        } else {
            p
        };
        Outcome::Done(close_p_element(q))
    } else if g == Tag::Li {
        // 25. "An end tag whose tag name is "li""
        if !has_in_scope(p, Tag::Li, Scope::ListItem) {
            // "If the stack of open elements does not have an li element in
            // list item scope, then this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, run these steps:" 1. "Generate implied end tags,
            // except for li elements." 2. "If the current node is not an li
            // element, then this is a parse error." 3. "Pop elements from the
            // stack of open elements until an li element has been popped from
            // the stack."
            Outcome::Done(pop_until_popped(generate_implied_end_tags(p, Some(Tag::Li)), Tag::Li))
        }
    } else if g == Tag::Dd || g == Tag::Dt {
        // 26. "An end tag whose tag name is one of: "dd", "dt""
        if !has_same_name_in_scope(p, tt) {
            // "If the stack of open elements does not have an element in scope
            // that is an HTML element with the same tag name as that of the
            // token, then this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, run these steps:" 1. "Generate implied end tags,
            // except for HTML elements with the same tag name as the token." 2.
            // "If the current node is not an HTML element with the same tag
            // name as that of the token, then this is a parse error." 3. "Pop
            // elements from the stack of open elements until an HTML element
            // with the same tag name as the token has been popped from the
            // stack."
            Outcome::Done(pop_until_named_popped(generate_implied_end_tags(p, Some(g)), tt.name))
        }
    } else if is_heading_tag(g) {
        // 27. "An end tag whose tag name is one of: "h1", "h2", "h3", "h4",
        // "h5", "h6""
        if !has_heading_in_scope(p) {
            // "If the stack of open elements does not have an element in scope
            // that is an HTML element and whose tag name is one of "h1", "h2",
            // "h3", "h4", "h5", or "h6", then this is a parse error; ignore the
            // token."
            Outcome::Done(p)
        } else {
            // "Otherwise, run these steps:" 1. "Generate implied end tags." 2.
            // "If the current node is not an HTML element with the same tag
            // name as that of the token, then this is a parse error." 3. "Pop
            // elements from the stack of open elements until an HTML element
            // whose tag name is one of "h1", "h2", "h3", "h4", "h5", or "h6"
            // has been popped from the stack."
            Outcome::Done(pop_until_heading_popped(generate_implied_end_tags(p, None)))
        }
    } else if tt.name == name_sarcasm() {
        // 28. "An end tag whose tag name is "sarcasm"": "Take a deep breath,
        // then act as described in the "any other end tag" entry below."
        Outcome::Done(in_body_any_other_end_tag(p, tt))
    } else if is_formatting_end_tag(g) {
        // 32. "An end tag whose tag name is one of: "a", "b", "big", "code",
        // "em", "font", "i", "nobr", "s", "small", "strike", "strong", "tt",
        // "u"": "Run the adoption agency algorithm for the token."
        Outcome::Done(in_body_adoption(p, tt))
    } else if is_applet_like(g) {
        // 34. "An end tag token whose tag name is one of: "applet",
        // "marquee", "object""
        if !has_same_name_in_scope(p, tt) {
            // "If the stack of open elements does not have an element in scope
            // that is an HTML element with the same tag name as that of the
            // token, then this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, run these steps:" 1. "Generate implied end tags." 2.
            // "If the current node is not an HTML element with the same tag
            // name as that of the token, then this is a parse error." 3. "Pop
            // elements from the stack of open elements until an HTML element
            // with the same tag name as the token has been popped from the
            // stack."
            let q = pop_until_named_popped(generate_implied_end_tags(p, None), tt.name);
            // 4. "Clear the list of active formatting elements up to the last
            // marker."
            Outcome::Done(clear_to_last_marker(q))
        }
    } else if g == Tag::Br {
        // 36. "An end tag whose tag name is "br"": "Parse error. Drop the
        // attributes from the token, and act as described in the next entry;
        // i.e. act as if this was a "br" start tag token with no attributes,
        // rather than the end tag token that it actually is."
        Outcome::Done(in_body_void_start_tag(p, TagTok { attrs: seq![], ..tt }))
    } else {
        // 55. "Any other end tag"
        Outcome::Done(in_body_any_other_end_tag(p, tt))
    }
}

/// Case 22: "If the stack of open elements does not have an element in
/// scope that is an HTML element with the same tag name as that of the
/// token, then this is a parse error; ignore the token."
pub open spec fn in_body_end_same_name(p: Parser, tt: TagTok) -> Parser {
    if !has_same_name_in_scope(p, tt) {
        p
    } else {
        // "Otherwise, run these steps:" 1. "Generate implied end tags."
        let q = generate_implied_end_tags(p, None);
        // 2. "If the current node is not an HTML element with the same tag name
        // as that of the token, then this is a parse error."
        // 3. "Pop elements from the stack of open elements until an HTML
        // element with the same tag name as the token has been popped from the
        // stack."
        pop_until_named_popped(q, tt.name)
    }
}

/// Case 23, "An end tag whose tag name is "form"".
pub open spec fn in_body_end_form(p: Parser) -> Parser {
    if !parsing_template_contents(p) {
        // "If the parser is not parsing template contents:" 1. "Let node be the
        // element that the form element pointer is set to, or null if it is
        // not set to an element."
        let node = p.form;
        // 2. "Set the form element pointer to null."
        let q = Parser { form: None, ..p };
        match node {
            Some(n) if has_node_in_scope(q, n, Scope::Default) => {
                // 4. "Generate implied end tags."
                let q1 = generate_implied_end_tags(q, None);
                // 5. "If the current node is not node, then this is a parse
                // error."
                // 6. "Remove node from the stack of open elements."
                let j = open_index_of(q1, n);
                if j >= 0 {
                    remove_open_at(q1, j)
                } else {
                    q1
                }
            },
            // 3. "If node is null or if the stack of open elements does not
            // have node in scope, then this is a parse error; return and ignore
            // the token."
            _ => q,
        }
    } else if !has_in_scope(p, Tag::Form, Scope::Default) {
        // "Otherwise:" 1. "If the stack of open elements does not have a form
        // element in scope, then this is a parse error; return and ignore the
        // token."
        p
    } else {
        // 2. "Generate implied end tags." 3. "If the current node is not a form
        // element, then this is a parse error." 4. "Pop elements from the
        // stack of open elements until a form element has been popped from the
        // stack."
        pop_until_popped(generate_implied_end_tags(p, None), Tag::Form)
    }
}

/// Case 55's steps 2 to 5 ("Loop") with node the entry at index `i`.
pub open spec fn any_other_end_tag_loop(p: Parser, tt: TagTok, i: int) -> Parser
    decreases i + 1,
{
    if i < 0 {
        // Unreachable: the html element at the top is special (step 3).
        p
    } else {
        let node = p.open[i];
        if is_html_named(node, tt.name) {
            // 2. "Loop: If node is an HTML element with the same tag name as the
            // token:" 2.1 "Generate implied end tags, except for HTML elements
            // with the same tag name as the token." (An element generate
            // implied end tags pops has a name `tag_of` classifies, so
            // comparing the tags is comparing the names.)
            let q = generate_implied_end_tags(p, Some(tt.tag));
            // 2.2 "If node is not the current node, then this is a parse
            // error."
            // 2.3 "Pop all the nodes from the current node up to node,
            // including node, then stop these steps."
            pop_until_node_popped(q, node.id)
        } else if is_special(node) {
            // 3. "Otherwise, if node is in the special category, then this is a
            // parse error; ignore the token, and return."
            p
        } else {
            // 4. "Set node to the previous entry in the stack of open
            // elements." 5. "Return to the step labeled loop."
            any_other_end_tag_loop(p, tt, i - 1)
        }
    }
}

/// Case 55, "Any other end tag": "Run these steps:" 1. "Initialize node to
/// be the current node (the bottommost node of the stack)." 2. to 5.
pub open spec fn in_body_any_other_end_tag(p: Parser, tt: TagTok) -> Parser {
    any_other_end_tag_loop(p, tt, p.open.len() - 1)
}

} // verus!
