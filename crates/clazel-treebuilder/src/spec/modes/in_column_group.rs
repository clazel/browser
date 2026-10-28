//! HTML §13.2.6.4.12 the "in column group" insertion mode.

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

/// §13.2.6.4.12 the "in column group" insertion mode.
/// <https://html.spec.whatwg.org/multipage/parsing.html#parsing-main-incolgroup>
pub open spec fn mode_in_column_group(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is Char && is_ascii_whitespace(t->Char_0) {
        // 1. "A character token that is one of U+0009 CHARACTER TABULATION,
        // U+000A LINE FEED (LF), U+000C FORM FEED (FF), U+000D CARRIAGE RETURN
        // (CR), or U+0020 SPACE"
        // "Insert the character."
        Outcome::Done(insert_char(p, t->Char_0))
    } else if t is Comment {
        // 2. "A comment token"
        // "Insert a comment."
        Outcome::Done(insert_comment(p, t->Comment_0, None))
    } else if t is Pi {
        // 3. "A processing instruction token"
        // "Insert a processing instruction."
        Outcome::Done(insert_pi(p, t->Pi_0, t->Pi_1, None))
    } else if t is Doctype {
        // 4. "A DOCTYPE token"
        // "Parse error. Ignore the token."
        Outcome::Done(p)
    } else if t is Start && t->Start_0.tag == Tag::Html {
        // 5. "A start tag whose tag name is "html""
        // "Process the token using the rules for the "in body" insertion
        // mode."
        Outcome::Using(Mode::InBody, p, t)
    } else if t is Start && t->Start_0.tag == Tag::Col {
        // 6. "A start tag whose tag name is "col""
        // "Insert an HTML element for the token."
        let p1 = insert_html_element(p, t->Start_0).0;
        // "Immediately pop the current node off the stack of open elements."
        // (A stopped parser changes nothing.)
        let p2 = if p1.stopped {
            p1
        } else {
            pop(p1)
        };
        // "Acknowledge the token's self-closing flag, if it is set."
        // (Nothing to model: it only decides a parse error.)
        Outcome::Done(p2)
    } else if t is End && t->End_0.tag == Tag::Colgroup {
        // 7. "An end tag whose tag name is "colgroup""
        if !is_html(current_node(p), Tag::Colgroup) {
            // "If the current node is not a colgroup element, then this is a
            // parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, pop the current node from the stack of open
            // elements. Switch the insertion mode to "in table"."
            Outcome::Done(Parser { mode: Mode::InTable, ..pop(p) })
        }
    } else if t is End && t->End_0.tag == Tag::Col {
        // 8. "An end tag whose tag name is "col""
        // "Parse error. Ignore the token."
        Outcome::Done(p)
    } else if (t is Start && t->Start_0.tag == Tag::Template) || (t is End && t->End_0.tag == Tag::Template) {
        // 9. "A start tag whose tag name is "template"", "An end tag whose
        // tag name is "template""
        // "Process the token using the rules for the "in head" insertion
        // mode."
        Outcome::Using(Mode::InHead, p, t)
    } else if t is Eof {
        // 10. "An end-of-file token"
        // "Process the token using the rules for the "in body" insertion
        // mode."
        Outcome::Using(Mode::InBody, p, t)
    } else {
        // 11. "Anything else"
        if !is_html(current_node(p), Tag::Colgroup) {
            // "If the current node is not a colgroup element, then this is a
            // parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, pop the current node from the stack of open
            // elements." "Switch the insertion mode to "in table"."
            // "Reprocess the token."
            Outcome::Reprocess(Parser { mode: Mode::InTable, ..pop(p) }, t)
        }
    }
}

} // verus!
