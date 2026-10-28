//! HTML §13.2.6.4.2 the "before html" insertion mode. The modelling choices
//! are listed in [`super::super`].

#[allow(unused_imports)]
use super::super::dispatch::*;
#[allow(unused_imports)]
use super::super::insert::*;
#[allow(unused_imports)]
use super::super::state::*;
#[allow(unused_imports)]
use super::super::tags::*;
use clazel_dom::spec::Namespace;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §13.2.6.4.2 the "before html" insertion mode.
pub open spec fn mode_before_html(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is Doctype {
        // 1. "A DOCTYPE token": "Parse error. Ignore the token."
        Outcome::Done(p)
    } else if t is Comment {
        // 2. "A comment token": "Insert a comment given (the Document object,
        // null)."
        Outcome::Done(insert_comment(p, t->Comment_0, Some(document_location())))
    } else if t is Pi {
        // 3. "A processing instruction token": "Insert a processing
        // instruction given (the Document object, null)."
        Outcome::Done(insert_pi(p, t->Pi_0, t->Pi_1, Some(document_location())))
    } else if t is Char && is_ascii_whitespace(t->Char_0) {
        // 4. "A character token that is one of U+0009 CHARACTER TABULATION,
        // U+000A LINE FEED (LF), U+000C FORM FEED (FF), U+000D CARRIAGE
        // RETURN (CR), or U+0020 SPACE": "Ignore the token."
        Outcome::Done(p)
    } else if t is Start && t->Start_0.tag == Tag::Html {
        // 5. "A start tag whose tag name is "html""
        // "Create an element for the token in the HTML namespace, with the
        // Document as the intended parent."
        let (p1, e) = create_element_for_token(p, t->Start_0, Namespace::Html, 0);
        // "Insert an element at the adjusted insertion location with that
        // element and (the Document, null)."
        let p2 = insert_element_at(p1, e.id, Some(document_location()));
        // "Put this element in the stack of open elements."
        let p3 = push(p2, e);
        // "Switch the insertion mode to "before head"."
        Outcome::Done(Parser { mode: Mode::BeforeHead, ..p3 })
    } else if t is End && (t->End_0.tag == Tag::Head || t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Br) {
        // 6. "An end tag whose tag name is one of: "head", "body", "html",
        // "br"": "Act as described in the "anything else" entry below."
        before_html_anything_else(p, t)
    } else if t is End {
        // 7. "Any other end tag": "Parse error. Ignore the token."
        Outcome::Done(p)
    } else {
        // 8. "Anything else"
        before_html_anything_else(p, t)
    }
}

/// The "anything else" entry of the "before html" insertion mode.
pub open spec fn before_html_anything_else(p: Parser, t: Tok) -> Outcome {
    // "Create an html element whose node document is the Document object."
    // Created as "create an element for the token" for an `html` start tag
    // with no attributes: the same element (an `html` element is neither a
    // template nor form-associated, so nothing else of that algorithm
    // applies), and the intended parent the Document, where it goes.
    let (p1, e) = create_element_for_token(p, start_tag_named(seq![0x68u32, 0x74, 0x6d, 0x6c]), Namespace::Html, 0);  // "html"
    // "Insert an element at the adjusted insertion location with that
    // element and (the Document, null)."
    let p2 = insert_element_at(p1, e.id, Some(document_location()));
    // "Put this element in the stack of open elements."
    let p3 = push(p2, e);
    // "Switch the insertion mode to "before head", then reprocess the token."
    Outcome::Reprocess(Parser { mode: Mode::BeforeHead, ..p3 }, t)
}

} // verus!
