//! HTML §13.2.6.4.6 the "after head" insertion mode. The modelling choices
//! are listed in [`super::super`]; the one this mode adds: case 7 processes
//! the token using the "in head" rules in the middle of its own steps, so
//! it calls [`mode_in_head`] directly (that function never refers back to
//! this mode, so there is no recursion), and for the tags of case 7 the "in
//! head" rules always handle the token (`Outcome::Done`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §13.2.6.4.6 the "after head" insertion mode.
pub open spec fn mode_after_head(env: EncFns, p: Parser, t: Tok) -> Outcome {
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
    } else if t is Start && t->Start_0.tag == Tag::Body {
        // 6. "A start tag whose tag name is "body""
        // "Insert an HTML element for the token."
        let p1 = insert_html_element(p, t->Start_0).0;
        // "Set the frameset-ok flag to "not ok"."
        // "Switch the insertion mode to "in body"."
        Outcome::Done(Parser { frameset_ok: false, mode: Mode::InBody, ..p1 })
    } else if t is Start && t->Start_0.tag == Tag::Frameset {
        // 7. "A start tag whose tag name is "frameset""
        // "Insert an HTML element for the token."
        let p1 = insert_html_element(p, t->Start_0).0;
        // "Switch the insertion mode to "in frameset"."
        Outcome::Done(Parser { mode: Mode::InFrameset, ..p1 })
    } else if t is Start && after_head_in_head_tag(t->Start_0.tag) {
        // 8. "A start tag whose tag name is one of: "base", "basefont",
        // "bgsound", "link", "meta", "noframes", "script", "style",
        // "template", "title""
        after_head_using_in_head(env, p, t)
    } else if t is End && t->End_0.tag == Tag::Template {
        // 9. "An end tag whose tag name is "template"": "Process the token
        // using the rules for the "in head" insertion mode."
        Outcome::Using(Mode::InHead, p, t)
    } else if t is End && (t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Br) {
        // 10. "An end tag whose tag name is one of: "body", "html", "br"":
        // "Act as described in the "anything else" entry below."
        after_head_anything_else(p, t)
    } else if (t is Start && t->Start_0.tag == Tag::Head) || t is End {
        // 11. "A start tag whose tag name is "head"" and "Any other end tag":
        // "Parse error. Ignore the token."
        Outcome::Done(p)
    } else {
        // 12. "Anything else"
        after_head_anything_else(p, t)
    }
}

/// The tag names of case 8: "base", "basefont", "bgsound", "link", "meta",
/// "noframes", "script", "style", "template", "title".
pub open spec fn after_head_in_head_tag(tag: Tag) -> bool {
    match tag {
        Tag::Base | Tag::Basefont | Tag::Bgsound | Tag::Link | Tag::Meta | Tag::Noframes | Tag::Script | Tag::Style
        | Tag::Template | Tag::Title => true,
        _ => false,
    }
}

/// The head element as the stack of open elements holds it: the node the
/// head element pointer points to, an HTML `head` element (the pointer is
/// only ever set to a `head` element the parser created for a `head` start
/// tag).
pub open spec fn head_elem(h: NodeId) -> Elem {
    Elem { id: h, ns: Namespace::Html, tag: Tag::Head, name: seq![0x68u32, 0x65, 0x61, 0x64], annotation_html: false }  // "head"
}

/// Case 8 of the "after head" insertion mode.
pub open spec fn after_head_using_in_head(env: EncFns, p: Parser, t: Tok) -> Outcome {
    // "Parse error."
    match p.head {
        // "The head element pointer cannot be null at this point." (If it
        // were, the token would be ignored.)
        None => Outcome::Done(p),
        Some(h) => {
            // "Push the node pointed to by the head element pointer onto the
            // stack of open elements."
            let p1 = push(p, head_elem(h));
            // "Process the token using the rules for the "in head" insertion
            // mode."
            match mode_in_head(env, p1, t) {
                Outcome::Done(p2) => {
                    // "Remove the node pointed to by the head element pointer
                    // from the stack of open elements. (It might not be the
                    // current node at this point.)"
                    let i = open_index_of(p2, h);
                    if p2.stopped || i < 0 {
                        Outcome::Done(p2)
                    } else {
                        Outcome::Done(remove_open_at(p2, i))
                    }
                },
                // Never: the "in head" rules handle each of these start tags
                // (cases 6 to 11 and 14 there).
                other => other,
            }
        },
    }
}

/// The "anything else" entry of the "after head" insertion mode.
pub open spec fn after_head_anything_else(p: Parser, t: Tok) -> Outcome {
    // "Insert an HTML element for a "body" start tag token with no
    // attributes."
    let p1 = insert_html_element(p, start_tag_named(seq![0x62u32, 0x6f, 0x64, 0x79])).0;  // "body"
    // "Set the frameset-ok flag to "ok"."
    // "Switch the insertion mode to "in body"."
    // "Reprocess the current token."
    Outcome::Reprocess(Parser { frameset_ok: true, mode: Mode::InBody, ..p1 }, t)
}

} // verus!
