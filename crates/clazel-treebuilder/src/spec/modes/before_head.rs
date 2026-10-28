//! HTML §13.2.6.4.3 the "before head" insertion mode. The modelling choices
//! are listed in [`super::super`].

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

/// §13.2.6.4.3 the "before head" insertion mode.
pub open spec fn mode_before_head(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is Char && is_ascii_whitespace(t->Char_0) {
        // 1. "A character token that is one of U+0009 CHARACTER TABULATION,
        // U+000A LINE FEED (LF), U+000C FORM FEED (FF), U+000D CARRIAGE
        // RETURN (CR), or U+0020 SPACE": "Ignore the token."
        Outcome::Done(p)
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
    } else if t is Start && t->Start_0.tag == Tag::Head {
        // 6. "A start tag whose tag name is "head""
        // "Insert an HTML element for the token."
        let (p1, e) = insert_html_element(p, t->Start_0);
        // "Set the head element pointer to the newly created head element."
        // "Switch the insertion mode to "in head"."
        Outcome::Done(Parser { head: Some(e.id), mode: Mode::InHead, ..p1 })
    } else if t is End && (t->End_0.tag == Tag::Head || t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Br) {
        // 7. "An end tag whose tag name is one of: "head", "body", "html",
        // "br"": "Act as described in the "anything else" entry below."
        before_head_anything_else(p, t)
    } else if t is End {
        // 8. "Any other end tag": "Parse error. Ignore the token."
        Outcome::Done(p)
    } else {
        // 9. "Anything else"
        before_head_anything_else(p, t)
    }
}

/// The "anything else" entry of the "before head" insertion mode.
pub open spec fn before_head_anything_else(p: Parser, t: Tok) -> Outcome {
    // "Insert an HTML element for a "head" start tag token with no
    // attributes."
    let (p1, e) = insert_html_element(p, start_tag_named(seq![0x68u32, 0x65, 0x61, 0x64]));  // "head"
    // "Set the head element pointer to the newly created head element."
    // "Switch the insertion mode to "in head"."
    // "Reprocess the current token."
    Outcome::Reprocess(Parser { head: Some(e.id), mode: Mode::InHead, ..p1 }, t)
}

} // verus!
