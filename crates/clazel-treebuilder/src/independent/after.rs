//! W3C HTML 5.2 §8.2.5.4.19 to §8.2.5.4.23: the "after body", "in
//! frameset", "after frameset", "after after body" and "after after
//! frameset" insertion modes. Source and modelling choices: [`super`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// W3C HTML 5.2 §8.2.5.4.19 the "after body" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-after-body-insertion-mode>).
pub open spec fn w3c_mode_after_body(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if w3c_space_char(t) {
        // "A character token that is one of U+0009 …": "Process the token
        // using the rules for the "in body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    } else if t is Comment {
        // "A comment token": "Insert a comment as the last child of the first
        // element in the stack of open elements (the html element)."
        Outcome::Done(insert_comment(p, t->Comment_0, Some(Location { parent: p.open[0].id, child: None })))
    } else if t is Doctype {
        // "A DOCTYPE token": "Parse error."
        Outcome::Done(p)
    } else if w3c_start(t, Tag::Html) {
        // "A start tag whose tag name is "html"": "Process the token using
        // the rules for the "in body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    } else if w3c_end(t, Tag::Html) {
        // "An end tag whose tag name is "html"":
        if p.context is Some {
            // "If the parser was originally created as part of the HTML
            // fragment parsing algorithm, this is a parse error; ignore the
            // token. (fragment case)"
            Outcome::Done(p)
        } else {
            // "Otherwise, switch the insertion mode to "after after body"."
            Outcome::Done(Parser { mode: Mode::AfterAfterBody, ..p })
        }
    } else if t is Eof {
        // "An end-of-file token": "Stop parsing."
        Outcome::Done(stop_parsing(p))
    } else {
        // "Anything else": "Parse error. Switch the insertion mode to "in
        // body" and reprocess the token."
        Outcome::Reprocess(Parser { mode: Mode::InBody, ..p }, t)
    }
}

/// W3C HTML 5.2 §8.2.5.4.20 the "in frameset" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-in-frameset-insertion-mode>).
pub open spec fn w3c_mode_in_frameset(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if w3c_space_char(t) {
        // "A character token that is one of U+0009 …": "Insert the
        // character."
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
    } else if w3c_start(t, Tag::Frameset) {
        // "A start tag whose tag name is "frameset"": "Insert an HTML element
        // for the token."
        Outcome::Done(insert_html_element(p, t->Start_0).0)
    } else if w3c_end(t, Tag::Frameset) {
        // "An end tag whose tag name is "frameset"":
        if w3c_current_is(p, Tag::Html) {
            // "If the current node is the root html element, then this is a
            // parse error; ignore the token. (fragment case)"
            Outcome::Done(p)
        } else {
            // "Otherwise, pop the current node from the stack of open
            // elements."
            let q = pop(p);
            // "If the parser was not originally created as part of the HTML
            // fragment parsing algorithm (fragment case), and the current
            // node is no longer a frameset element, then switch the insertion
            // mode to "after frameset"."
            if p.context is None && !w3c_current_is(q, Tag::Frameset) {
                Outcome::Done(Parser { mode: Mode::AfterFrameset, ..q })
            } else {
                Outcome::Done(q)
            }
        }
    } else if w3c_start(t, Tag::Frame) {
        // "A start tag whose tag name is "frame"": "Insert an HTML element for
        // the token. Immediately pop the current node off the stack of open
        // elements. Acknowledge the token's self-closing flag, if it is set."
        Outcome::Done(pop(insert_html_element(p, t->Start_0).0))
    } else if w3c_start(t, Tag::Noframes) {
        // "A start tag whose tag name is "noframes"": "Process the token
        // using the rules for the "in head" insertion mode."
        Outcome::Using(Mode::InHead, p, t)
    } else if t is Eof {
        // "An end-of-file token": "If the current node is not the root html
        // element, then this is a parse error. … Stop parsing."
        Outcome::Done(stop_parsing(p))
    } else {
        // "Anything else": "Parse error."
        Outcome::Done(p)
    }
}

/// W3C HTML 5.2 §8.2.5.4.21 the "after frameset" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-after-frameset-insertion-mode>).
pub open spec fn w3c_mode_after_frameset(env: EncFns, p: Parser, t: Tok) -> Outcome {
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
    } else if w3c_end(t, Tag::Html) {
        // "An end tag whose tag name is "html"": "Switch the insertion mode
        // to "after after frameset"."
        Outcome::Done(Parser { mode: Mode::AfterAfterFrameset, ..p })
    } else if w3c_start(t, Tag::Noframes) {
        // "A start tag whose tag name is "noframes"": "Process the token
        // using the rules for the "in head" insertion mode."
        Outcome::Using(Mode::InHead, p, t)
    } else if t is Eof {
        // "An end-of-file token": "Stop parsing."
        Outcome::Done(stop_parsing(p))
    } else {
        // "Anything else": "Parse error."
        Outcome::Done(p)
    }
}

/// W3C HTML 5.2 §8.2.5.4.22 the "after after body" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-after-after-body-insertion-mode>).
pub open spec fn w3c_mode_after_after_body(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is Comment {
        // "A comment token": "Insert a comment as the last child of the
        // Document object."
        Outcome::Done(insert_comment(p, t->Comment_0, Some(document_location())))
    } else if t is Doctype || w3c_space_char(t) || w3c_start(t, Tag::Html) {
        // "A DOCTYPE token", "A character token that is one of U+0009 …", "A
        // start tag whose tag name is "html"": "Process the token using the
        // rules for the "in body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    } else if t is Eof {
        // "An end-of-file token": "Stop parsing."
        Outcome::Done(stop_parsing(p))
    } else {
        // "Anything else": "Parse error. Switch the insertion mode to "in
        // body" and reprocess the token."
        Outcome::Reprocess(Parser { mode: Mode::InBody, ..p }, t)
    }
}

/// W3C HTML 5.2 §8.2.5.4.23 the "after after frameset" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-after-after-frameset-insertion-mode>).
pub open spec fn w3c_mode_after_after_frameset(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is Comment {
        // "A comment token": "Insert a comment as the last child of the
        // Document object."
        Outcome::Done(insert_comment(p, t->Comment_0, Some(document_location())))
    } else if t is Doctype || w3c_space_char(t) || w3c_start(t, Tag::Html) {
        // "A DOCTYPE token", "A character token that is one of U+0009 …", "A
        // start tag whose tag name is "html"": "Process the token using the
        // rules for the "in body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    } else if t is Eof {
        // "An end-of-file token": "Stop parsing."
        Outcome::Done(stop_parsing(p))
    } else if w3c_start(t, Tag::Noframes) {
        // "A start tag whose tag name is "noframes"": "Process the token
        // using the rules for the "in head" insertion mode."
        Outcome::Using(Mode::InHead, p, t)
    } else {
        // "Anything else": "Parse error."
        Outcome::Done(p)
    }
}

} // verus!
