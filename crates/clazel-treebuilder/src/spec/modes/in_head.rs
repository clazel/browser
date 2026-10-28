//! HTML §13.2.6.4.4 the "in head" insertion mode. The modelling choices are
//! listed in [`super::super`]; the ones this mode reads:
//! - the active speculative HTML parser is always null, so the `meta`
//!   rule's encoding steps always run;
//! - "change the encoding" pushes `Action::ChangeEncoding` and makes the
//!   confidence certain (`tentative: false`);
//! - the `script` element's "parser document", "force async" and "already
//!   started" (its steps 2 to 4) are script-processing state that is not
//!   part of the DOM model (Phase 7), so those steps change nothing here;
//! - the sanitizer configuration is null (sanitizerAction is "Keep"),
//!   "allow declarative shadow roots" is false, and template content
//!   patching is not modelled, so the `template` start tag always inserts a
//!   plain template, and a template's "insertion target" is always null.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §13.2.6.4.4 the "in head" insertion mode.
pub open spec fn mode_in_head(env: EncFns, p: Parser, t: Tok) -> Outcome {
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
    } else if t is Start && (t->Start_0.tag == Tag::Base || t->Start_0.tag == Tag::Basefont || t->Start_0.tag == Tag::Bgsound
        || t->Start_0.tag == Tag::Link) {
        // 6. "A start tag whose tag name is one of: "base", "basefont",
        // "bgsound", "link""
        // "Insert an HTML element for the token. Immediately pop the current
        // node off the stack of open elements."
        // "Acknowledge the token's self-closing flag, if it is set." (Only
        // whether a parse error occurs depends on it: nothing to model.)
        Outcome::Done(pop(insert_html_element(p, t->Start_0).0))
    } else if t is Start && t->Start_0.tag == Tag::Meta {
        // 7. "A start tag whose tag name is "meta""
        Outcome::Done(in_head_meta(env, p, t->Start_0))
    } else if t is Start && t->Start_0.tag == Tag::Title {
        // 8. "A start tag whose tag name is "title"": "Follow the generic
        // RCDATA element parsing algorithm."
        Outcome::Done(generic_text_parsing(p, t->Start_0, false))
    } else if t is Start && ((t->Start_0.tag == Tag::Noscript && p.scripting) || t->Start_0.tag == Tag::Noframes
        || t->Start_0.tag == Tag::Style) {
        // 9. "A start tag whose tag name is "noscript", if scripting mode is
        // not Disabled" and "A start tag whose tag name is one of:
        // "noframes", "style"": "Follow the generic raw text element parsing
        // algorithm."
        Outcome::Done(generic_text_parsing(p, t->Start_0, true))
    } else if t is Start && t->Start_0.tag == Tag::Noscript {
        // 10. "A start tag whose tag name is "noscript", if scripting mode is
        // Disabled" (case 9 took the others)
        // "Insert an HTML element for the token."
        let p1 = insert_html_element(p, t->Start_0).0;
        // "Switch the insertion mode to "in head noscript"."
        Outcome::Done(Parser { mode: Mode::InHeadNoscript, ..p1 })
    } else if t is Start && t->Start_0.tag == Tag::Script {
        // 11. "A start tag whose tag name is "script""
        Outcome::Done(in_head_script(p, t->Start_0))
    } else if t is End && t->End_0.tag == Tag::Head {
        // 12. "An end tag whose tag name is "head""
        // "Pop the current node (which will be the head element) off the
        // stack of open elements."
        // "Switch the insertion mode to "after head"."
        Outcome::Done(Parser { mode: Mode::AfterHead, ..pop(p) })
    } else if t is End && (t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Br) {
        // 13. "An end tag whose tag name is one of: "body", "html", "br"":
        // "Act as described in the "anything else" entry below."
        in_head_anything_else(p, t)
    } else if t is Start && t->Start_0.tag == Tag::Template {
        // 14. "A start tag whose tag name is "template""
        Outcome::Done(in_head_template_start(p, t->Start_0))
    } else if t is End && t->End_0.tag == Tag::Template {
        // 15. "An end tag whose tag name is "template""
        Outcome::Done(in_head_template_end(p))
    } else if (t is Start && t->Start_0.tag == Tag::Head) || t is End {
        // 16. "A start tag whose tag name is "head"" and "Any other end tag":
        // "Parse error. Ignore the token."
        Outcome::Done(p)
    } else {
        // 17. "Anything else"
        in_head_anything_else(p, t)
    }
}

/// "charset"
pub open spec fn in_head_name_charset() -> Seq<u32> {
    seq![0x63u32, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74]
}

/// "http-equiv"
pub open spec fn in_head_name_http_equiv() -> Seq<u32> {
    seq![0x68u32, 0x74, 0x74, 0x70, 0x2d, 0x65, 0x71, 0x75, 0x69, 0x76]
}

/// "content"
pub open spec fn in_head_name_content() -> Seq<u32> {
    seq![0x63u32, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74]
}

/// "Content-Type"
pub open spec fn in_head_content_type() -> Seq<u32> {
    seq![0x43u32, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x2d, 0x54, 0x79, 0x70, 0x65]
}

/// §13.2.3.4 "change the encoding" as the parser hands it on: the action,
/// and the confidence certain (see [`super::super`]). A stopped parser
/// changes nothing.
pub open spec fn change_the_encoding(p: Parser, enc: nat) -> Parser {
    if p.stopped {
        p
    } else {
        Parser { actions: p.actions.push(Action::ChangeEncoding(enc)), tentative: false, ..p }
    }
}

/// The encoding the `meta` element's `http-equiv`/`content` pair declares:
/// "applying the algorithm for extracting a character encoding from a meta
/// element to that attribute's value returns an encoding". The extraction
/// algorithm's last step is "Return the result of getting an encoding from
/// the string …"; the parameter [`EncFns::extract_from_meta`] returns that
/// string (the label), so the encoding is "get an encoding" of it.
pub open spec fn meta_extracted_encoding(env: EncFns, content: Seq<u32>) -> Option<nat> {
    match (env.extract_from_meta)(content) {
        Some(label) => (env.get_an_encoding)(label),
        None => None,
    }
}

/// Case 7 of the "in head" insertion mode, "A start tag whose tag name is
/// "meta"". The element's attributes are the token's (create an element
/// for the token, step 17), so they are read from the token.
pub open spec fn in_head_meta(env: EncFns, p: Parser, tt: TagTok) -> Parser {
    // "Insert an HTML element for the token. Immediately pop the current
    // node off the stack of open elements."
    let p1 = pop(insert_html_element(p, tt).0);
    // "Acknowledge the token's self-closing flag, if it is set." (Nothing to
    // model.)
    // "If the active speculative HTML parser is null:" (it always is)
    let charset = attr_value(tt.attrs, in_head_name_charset());
    let http_equiv = attr_value(tt.attrs, in_head_name_http_equiv());
    let content = attr_value(tt.attrs, in_head_name_content());
    if charset is Some && (env.get_an_encoding)(charset->Some_0) is Some && p1.tentative {
        // 1. "If the element has a charset attribute, and getting an encoding
        // from its value results in an encoding, and the confidence is
        // currently tentative, then change the encoding to the resulting
        // encoding."
        change_the_encoding(p1, (env.get_an_encoding)(charset->Some_0)->Some_0)
    } else if http_equiv is Some && ascii_ci_eq(http_equiv->Some_0, in_head_content_type()) && content is Some
        && meta_extracted_encoding(env, content->Some_0) is Some && p1.tentative {
        // 2. "Otherwise, if the element has an http-equiv attribute whose
        // value is an ASCII case-insensitive match for "Content-Type", and
        // the element has a content attribute, and applying the algorithm
        // for extracting a character encoding from a meta element to that
        // attribute's value returns an encoding, and the confidence is
        // currently tentative, then change the encoding to the extracted
        // encoding."
        change_the_encoding(p1, meta_extracted_encoding(env, content->Some_0)->Some_0)
    } else {
        p1
    }
}

/// Case 11 of the "in head" insertion mode, "A start tag whose tag name is
/// "script"": "Run these steps:"
pub open spec fn in_head_script(p: Parser, tt: TagTok) -> Parser {
    // 1. "Create an element for the token in the HTML namespace, with the
    // intended parent being the target parent of the appropriate place for
    // inserting a node."
    let (p1, e) = create_element_for_token(p, tt, Namespace::Html, appropriate_place(p, None).parent);
    // 2. "If the scripting mode is not Fragment, then set the element's
    // parser document to the Document and set its force async to false."
    // 3. "If the parser's scripting mode is Inert, then set the script
    // element's already started to true." 4. (document.write: not
    // modelled.) The script element's processing state is not part of the
    // DOM model (Phase 7): nothing to model.
    // 5. "Insert an element at the adjusted insertion location with the newly
    // created element."
    let p2 = insert_element_at(p1, e.id, None);
    // 6. "Push the newly created element onto the stack of open elements so
    // that it is the new current node."
    let p3 = push(p2, e);
    // 7. "Switch the tokenizer to the script data state."
    // 8. "Set the original insertion mode to the current insertion mode."
    // 9. "Switch the insertion mode to "text"."
    Parser { tokenizer: Some(TokenizerState::ScriptData), original_mode: p3.mode, mode: Mode::Text, ..p3 }
}

/// Case 14 of the "in head" insertion mode, "A start tag whose tag name is
/// "template"": "Run these steps:"
pub open spec fn in_head_template_start(p: Parser, tt: TagTok) -> Parser {
    // 1. "Let templateStartTag be the start tag." (`tt`)
    // 2. "Insert a marker at the end of the list of active formatting
    // elements."
    let p1 = push_marker(p);
    // 3. "Set the frameset-ok flag to "not ok"."
    // 4. "Switch the insertion mode to "in template"."
    // 5. "Push "in template" onto the stack of template insertion modes so
    // that it is the new current template insertion mode."
    let p2 = Parser { frameset_ok: false, mode: Mode::InTemplate, template_modes: p1.template_modes.push(Mode::InTemplate), ..p1 };
    // 6. "Let declarativeShadowHostElement be the current node." 7. "Let
    // hostIsRoot be …" (Read only by step 13.1, which never applies.)
    // 8. "Let template be the result of creating an element for the token
    // given templateStartTag, the HTML namespace, and the target parent of
    // the appropriate place for inserting a node."
    let (p3, template) = create_element_for_token(p2, tt, Namespace::Html, appropriate_place(p2, None).parent);
    // 9. "Let insertionLocation be the appropriate place for inserting a
    // node."
    let insertion_location = appropriate_place(p3, None);
    // 10. "Push template onto the stack of open elements so that it is the
    // new current node."
    let p4 = push(p3, template);
    // 11. "Let sanitizerAction be "Keep"." 12. The sanitizer configuration
    // is null.
    // 13. "Switch on sanitizerAction:" "Keep":
    // 13.1 "If template's shadowrootmode attribute is not in the None
    // state:" 13.1.1 "If any of the following are true: the parser's allow
    // declarative shadow roots is false; … then insert an element at the
    // adjusted insertion location with template, insertionLocation, and
    // true, and return." (Allow declarative shadow roots is false.)
    // 13.2 "Otherwise, if template has a for attribute:" content patching is
    // not modelled (see [`super::super`]): the template is inserted as at
    // 13.2.4 when patching fails.
    // 13.3 "Otherwise, insert an element at the adjusted insertion location
    // with template, insertionLocation, and true."
    // (Every branch is the same insertion.)
    insert_element_at(p4, template.id, Some(insertion_location))
}

/// Case 15 of the "in head" insertion mode, "An end tag whose tag name is
/// "template"".
pub open spec fn in_head_template_end(p: Parser) -> Parser {
    if !open_has_html(p, Tag::Template) {
        // "If there is no template element on the stack of open elements,
        // then this is a parse error; ignore the token."
        p
    } else {
        // "Otherwise, run these steps:"
        // 1. "Generate all implied end tags thoroughly."
        let p1 = generate_all_implied_end_tags_thoroughly(p);
        // 2. "If the current node is not a template element, then this is a
        // parse error."
        // 3. "Let template be the last template element in the stack of open
        // elements." 4. "If template's insertion target is not null: …" (It is
        // always null: content patching is not modelled.)
        // 5. "Pop elements from the stack of open elements until a template
        // element has been popped from the stack."
        let p2 = pop_until_popped(p1, Tag::Template);
        // 6. "Clear the list of active formatting elements up to the last
        // marker."
        let p3 = clear_to_last_marker(p2);
        // 7. "Pop the current template insertion mode off the stack of
        // template insertion modes."
        let p4 = Parser { template_modes: p3.template_modes.drop_last(), ..p3 };
        // 8. "Reset the insertion mode appropriately."
        reset_insertion_mode(p4)
    }
}

/// The "anything else" entry of the "in head" insertion mode.
pub open spec fn in_head_anything_else(p: Parser, t: Tok) -> Outcome {
    // "Pop the current node (which will be the head element) off the stack
    // of open elements."
    // "Switch the insertion mode to "after head"."
    // "Reprocess the token."
    Outcome::Reprocess(Parser { mode: Mode::AfterHead, ..pop(p) }, t)
}

} // verus!
