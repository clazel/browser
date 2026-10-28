//! HTML §13.2.6.4.18 the "in frameset" insertion mode.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §13.2.6.4.18 the "in frameset" insertion mode.
pub open spec fn mode_in_frameset(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is Char && is_ascii_whitespace(t->Char_0) {
        // 1. "A character token that is one of U+0009 CHARACTER TABULATION,
        // U+000A LINE FEED (LF), U+000C FORM FEED (FF), U+000D CARRIAGE
        // RETURN (CR), or U+0020 SPACE": "Insert the character."
        Outcome::Done(insert_char(p, t->Char_0))
    } else if t is Comment {
        // 2. "A comment token": "Insert a comment."
        Outcome::Done(insert_comment(p, t->Comment_0, None))
    } else if t is Pi {
        // 3. "A processing instruction token": "Insert a processing
        // instruction."
        Outcome::Done(insert_pi(p, t->Pi_0, t->Pi_1, None))
    } else if t is Doctype {
        // 4. "A DOCTYPE token": "Parse error. Ignore the token."
        Outcome::Done(p)
    } else if t is Start && t->Start_0.tag == Tag::Html {
        // 5. "A start tag whose tag name is "html"": "Process the token using
        // the rules for the "in body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    } else if t is Start && t->Start_0.tag == Tag::Frameset {
        // 6. "A start tag whose tag name is "frameset"": "Insert an HTML
        // element for the token."
        Outcome::Done(insert_html_element(p, t->Start_0).0)
    } else if t is End && t->End_0.tag == Tag::Frameset {
        // 7. "An end tag whose tag name is "frameset""
        // "If the current node is the root html element, then this is a parse
        // error; ignore the token. (fragment case)" The root html element is
        // the first entry of the stack, so the current node is it exactly
        // when the stack has one entry. (The stack is never empty in this
        // mode; the test includes that case so that `pop` is never applied
        // to an empty stack.)
        if p.open.len() <= 1 {
            Outcome::Done(p)
        } else {
            // "Otherwise, pop the current node from the stack of open
            // elements."
            let q = pop(p);
            // "If the parser's fragment context element is null and the
            // current node is no longer a frameset element, then switch the
            // insertion mode to "after frameset"."
            if q.context is None && !is_html(current_node(q), Tag::Frameset) {
                Outcome::Done(Parser { mode: Mode::AfterFrameset, ..q })
            } else {
                Outcome::Done(q)
            }
        }
    } else if t is Start && t->Start_0.tag == Tag::Frame {
        // 8. "A start tag whose tag name is "frame"": "Insert an HTML element
        // for the token. Immediately pop the current node off the stack of
        // open elements." (A parser stopped by the insertion has an empty
        // stack and changes nothing more.) "Acknowledge the token's
        // self-closing flag, if it is set": nothing to model (parse errors
        // only).
        let p1 = insert_html_element(p, t->Start_0).0;
        if p1.stopped {
            Outcome::Done(p1)
        } else {
            Outcome::Done(pop(p1))
        }
    } else if t is Start && t->Start_0.tag == Tag::Noframes {
        // 9. "A start tag whose tag name is "noframes"": "Process the token
        // using the rules for the "in head" insertion mode."
        Outcome::Using(Mode::InHead, p, t)
    } else if t is Eof {
        // 10. "An end-of-file token": "If the current node is not the root
        // html element, then this is a parse error." (Parse errors are not
        // modelled.) "Stop parsing."
        Outcome::Done(stop_parsing(p))
    } else {
        // 11. "Anything else": "Parse error. Ignore the token."
        Outcome::Done(p)
    }
}

} // verus!
