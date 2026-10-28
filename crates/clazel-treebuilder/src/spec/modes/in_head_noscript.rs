//! HTML §13.2.6.4.5 the "in head noscript" insertion mode. The modelling
//! choices are listed in [`super::super`].

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

/// §13.2.6.4.5 the "in head noscript" insertion mode.
pub open spec fn mode_in_head_noscript(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is Doctype {
        // 1. "A DOCTYPE token": "Parse error. Ignore the token."
        Outcome::Done(p)
    } else if t is Start && t->Start_0.tag == Tag::Html {
        // 2. "A start tag whose tag name is "html"": "Process the token using
        // the rules for the "in body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    } else if t is End && t->End_0.tag == Tag::Noscript {
        // 3. "An end tag whose tag name is "noscript""
        // "Pop the current node (which will be a noscript element) from the
        // stack of open elements; the new current node will be a head
        // element."
        // "Switch the insertion mode to "in head"."
        Outcome::Done(Parser { mode: Mode::InHead, ..pop(p) })
    } else if (t is Char && is_ascii_whitespace(t->Char_0)) || t is Comment || t is Pi || (t is Start && (t->Start_0.tag
        == Tag::Basefont || t->Start_0.tag == Tag::Bgsound || t->Start_0.tag == Tag::Link || t->Start_0.tag == Tag::Meta
        || t->Start_0.tag == Tag::Noframes || t->Start_0.tag == Tag::Style)) {
        // 4. "A character token that is one of U+0009 CHARACTER TABULATION,
        // U+000A LINE FEED (LF), U+000C FORM FEED (FF), U+000D CARRIAGE
        // RETURN (CR), or U+0020 SPACE", "A comment token", "A processing
        // instruction token" and "A start tag whose tag name is one of:
        // "basefont", "bgsound", "link", "meta", "noframes", "style"":
        // "Process the token using the rules for the "in head" insertion
        // mode."
        Outcome::Using(Mode::InHead, p, t)
    } else if t is End && t->End_0.tag == Tag::Br {
        // 5. "An end tag whose tag name is "br"": "Act as described in the
        // "anything else" entry below."
        in_head_noscript_anything_else(p, t)
    } else if (t is Start && (t->Start_0.tag == Tag::Head || t->Start_0.tag == Tag::Noscript)) || t is End {
        // 6. "A start tag whose tag name is one of: "head", "noscript"" and
        // "Any other end tag": "Parse error. Ignore the token."
        Outcome::Done(p)
    } else {
        // 7. "Anything else"
        in_head_noscript_anything_else(p, t)
    }
}

/// The "anything else" entry of the "in head noscript" insertion mode.
pub open spec fn in_head_noscript_anything_else(p: Parser, t: Tok) -> Outcome {
    // "Parse error."
    // "Pop the current node (which will be a noscript element) from the stack
    // of open elements; the new current node will be a head element."
    // "Switch the insertion mode to "in head"."
    // "Reprocess the token."
    Outcome::Reprocess(Parser { mode: Mode::InHead, ..pop(p) }, t)
}

} // verus!
