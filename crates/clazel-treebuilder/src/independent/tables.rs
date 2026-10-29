//! W3C HTML 5.2 §8.2.5.4.9 to §8.2.5.4.15: the "in table", "in table
//! text", "in caption", "in column group", "in table body", "in row" and
//! "in cell" insertion modes. Source and modelling choices: [`super`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The steps "in caption" runs for an end tag `caption` (and, then
/// reprocessing, for the second entry): "Generate implied end tags. Now, if
/// the current node is not a caption element, then this is a parse error.
/// Pop elements from this stack until a caption element has been popped
/// from the stack. Clear the list of active formatting elements up to the
/// last marker. Switch the insertion mode to "in table"."
pub open spec fn w3c_close_caption(p: Parser) -> Parser {
    let q = clear_to_last_marker(pop_until_popped(generate_implied_end_tags(p, None), Tag::Caption));
    Parser { mode: Mode::InTable, ..q }
}

/// W3C HTML 5.2 §8.2.5.4.11 the "in caption" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-in-caption-insertion-mode>).
pub open spec fn w3c_mode_in_caption(env: EncFns, p: Parser, t: Tok) -> Outcome {
    let tag = w3c_tag(t);
    if w3c_end(t, Tag::Caption) {
        // "An end tag whose tag name is "caption"":
        if !has_in_scope(p, Tag::Caption, Scope::Table) {
            // "If the stack of open elements does not have a caption element
            // in table scope, this is a parse error; ignore the token.
            // (fragment case)"
            Outcome::Done(p)
        } else {
            // "Otherwise: …"
            Outcome::Done(w3c_close_caption(p))
        }
    } else if (t is Start && (tag == Tag::Caption || tag == Tag::Col || tag == Tag::Colgroup || tag == Tag::Tbody || tag
        == Tag::Td || tag == Tag::Tfoot || tag == Tag::Th || tag == Tag::Thead || tag == Tag::Tr)) || w3c_end(t, Tag::Table) {
        // "A start tag whose tag name is one of: "caption", "col",
        // "colgroup", "tbody", "td", "tfoot", "th", "thead", "tr"", "An end
        // tag whose tag name is "table"":
        if !has_in_scope(p, Tag::Caption, Scope::Table) {
            // "If the stack of open elements does not have a caption element
            // in table scope, this is a parse error; ignore the token.
            // (fragment case)"
            Outcome::Done(p)
        } else {
            // "Otherwise: …" and "Reprocess the token."
            Outcome::Reprocess(w3c_close_caption(p), t)
        }
    } else if t is End && (tag == Tag::Body || tag == Tag::Col || tag == Tag::Colgroup || tag == Tag::Html || tag
        == Tag::Tbody || tag == Tag::Td || tag == Tag::Tfoot || tag == Tag::Th || tag == Tag::Thead || tag == Tag::Tr) {
        // "An end tag whose tag name is one of: "body", "col", "colgroup",
        // "html", "tbody", "td", "tfoot", "th", "thead", "tr"": "Parse
        // error."
        Outcome::Done(p)
    } else {
        // "Anything else": "Process the token using the rules for the "in
        // body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    }
}

/// W3C HTML 5.2 §8.2.5.4.12 the "in column group" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-in-column-group-insertion-mode>).
pub open spec fn w3c_mode_in_column_group(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if w3c_space_char(t) {
        // "Insert the character."
        Outcome::Done(insert_char(p, t->Char_0))
    } else if t is Comment {
        // "A comment token": "Insert a comment."
        Outcome::Done(insert_comment(p, t->Comment_0, None))
    } else if t is Doctype {
        // "A DOCTYPE token": "Parse error."
        Outcome::Done(p)
    } else if w3c_start(t, Tag::Html) {
        // "A start tag whose tag name is "html"": "Process the token using
        // the rules for the "in body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    } else if w3c_start(t, Tag::Col) {
        // "A start tag whose tag name is "col"": "Insert an HTML element for
        // the token. Immediately pop the current node off the stack of open
        // elements. Acknowledge the token's self-closing flag, if it is set."
        Outcome::Done(pop(insert_html_element(p, t->Start_0).0))
    } else if w3c_end(t, Tag::Colgroup) {
        // "An end tag whose tag name is "colgroup"":
        if !w3c_current_is(p, Tag::Colgroup) {
            // "If the current node is not a colgroup element, then this is a
            // parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, pop the current node from the stack of open
            // elements. Switch the insertion mode to "in table"."
            Outcome::Done(Parser { mode: Mode::InTable, ..pop(p) })
        }
    } else if w3c_end(t, Tag::Col) {
        // "An end tag whose tag name is "col"": "Parse error."
        Outcome::Done(p)
    } else if w3c_start(t, Tag::Template) || w3c_end(t, Tag::Template) {
        // "A start tag whose tag name is "template"", "An end tag whose tag
        // name is "template"": "Process the token using the rules for the "in
        // head" insertion mode."
        Outcome::Using(Mode::InHead, p, t)
    } else if t is Eof {
        // "An end-of-file token": "Process the token using the rules for the
        // "in body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    } else {
        // "Anything else":
        if !w3c_current_is(p, Tag::Colgroup) {
            // "If the current node is not a colgroup element, then this is a
            // parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, pop the current node from the stack of open
            // elements. Switch the insertion mode to "in table". Reprocess
            // the token."
            Outcome::Reprocess(Parser { mode: Mode::InTable, ..pop(p) }, t)
        }
    }
}

} // verus!
