//! HTML §13.2.6.4.21 the "after after frameset" insertion mode.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §13.2.6.4.21 the "after after frameset" insertion mode.
pub open spec fn mode_after_after_frameset(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is Comment {
        // 1. "A comment token": "Insert a comment given (the Document object,
        // null)."
        Outcome::Done(insert_comment(p, t->Comment_0, Some(document_location())))
    } else if t is Pi {
        // 2. "A processing instruction token": "Insert a processing
        // instruction given (the Document object, null)."
        Outcome::Done(insert_pi(p, t->Pi_0, t->Pi_1, Some(document_location())))
    } else if t is Doctype || (t is Char && is_ascii_whitespace(t->Char_0)) || (t is Start && t->Start_0.tag == Tag::Html) {
        // 3. "A DOCTYPE token", "A character token that is one of U+0009
        // CHARACTER TABULATION, U+000A LINE FEED (LF), U+000C FORM FEED (FF),
        // U+000D CARRIAGE RETURN (CR), or U+0020 SPACE", "A start tag whose
        // tag name is "html"": "Process the token using the rules for the "in
        // body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    } else if t is Eof {
        // 4. "An end-of-file token": "Stop parsing."
        Outcome::Done(stop_parsing(p))
    } else if t is Start && t->Start_0.tag == Tag::Noframes {
        // 5. "A start tag whose tag name is "noframes"": "Process the token
        // using the rules for the "in head" insertion mode."
        Outcome::Using(Mode::InHead, p, t)
    } else {
        // 6. "Anything else": "Parse error. Ignore the token."
        Outcome::Done(p)
    }
}

} // verus!
