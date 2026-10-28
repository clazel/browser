//! HTML §13.2.6.4.17 the "after body" insertion mode.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §13.2.6.4.17 the "after body" insertion mode.
pub open spec fn mode_after_body(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is Char && is_ascii_whitespace(t->Char_0) {
        // 1. "A character token that is one of U+0009 CHARACTER TABULATION,
        // U+000A LINE FEED (LF), U+000C FORM FEED (FF), U+000D CARRIAGE
        // RETURN (CR), or U+0020 SPACE": "Process the token using the rules
        // for the "in body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    } else if t is Comment {
        // 2. "A comment token": "Insert a comment given (the first element in
        // the stack of open elements (the html element), null)."
        Outcome::Done(insert_comment(p, t->Comment_0, Some(Location { parent: p.open[0].id, child: None })))
    } else if t is Pi {
        // 3. "A processing instruction token": "Insert a processing
        // instruction given (the first element in the stack of open elements
        // (the html element), null)."
        Outcome::Done(insert_pi(p, t->Pi_0, t->Pi_1, Some(Location { parent: p.open[0].id, child: None })))
    } else if t is Doctype {
        // 4. "A DOCTYPE token": "Parse error. Ignore the token."
        Outcome::Done(p)
    } else if t is Start && t->Start_0.tag == Tag::Html {
        // 5. "A start tag whose tag name is "html"": "Process the token using
        // the rules for the "in body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    } else if t is End && t->End_0.tag == Tag::Html {
        // 6. "An end tag whose tag name is "html""
        if p.context is Some {
            // "If the parser's fragment context element is non-null, this is a
            // parse error; ignore the token. (fragment case)"
            Outcome::Done(p)
        } else {
            // "Otherwise, switch the insertion mode to "after after body"."
            Outcome::Done(Parser { mode: Mode::AfterAfterBody, ..p })
        }
    } else if t is Eof {
        // 7. "An end-of-file token": "Stop parsing."
        Outcome::Done(stop_parsing(p))
    } else {
        // 8. "Anything else": "Parse error. Switch the insertion mode to "in
        // body" and reprocess the token."
        Outcome::Reprocess(Parser { mode: Mode::InBody, ..p }, t)
    }
}

} // verus!
