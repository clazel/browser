//! HTML §13.2.6.4.19 the "after frameset" insertion mode.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §13.2.6.4.19 the "after frameset" insertion mode.
pub open spec fn mode_after_frameset(env: EncFns, p: Parser, t: Tok) -> Outcome {
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
    } else if t is End && t->End_0.tag == Tag::Html {
        // 6. "An end tag whose tag name is "html"": "Switch the insertion mode
        // to "after after frameset"."
        Outcome::Done(Parser { mode: Mode::AfterAfterFrameset, ..p })
    } else if t is Start && t->Start_0.tag == Tag::Noframes {
        // 7. "A start tag whose tag name is "noframes"": "Process the token
        // using the rules for the "in head" insertion mode."
        Outcome::Using(Mode::InHead, p, t)
    } else if t is Eof {
        // 8. "An end-of-file token": "Stop parsing."
        Outcome::Done(stop_parsing(p))
    } else {
        // 9. "Anything else": "Parse error. Ignore the token."
        Outcome::Done(p)
    }
}

} // verus!
