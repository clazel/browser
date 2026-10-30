//! W3C HTML 5.2 §8.2.5.4.1 to §8.2.5.4.6: the "initial", "before html",
//! "before head", "in head", "in head noscript" and "after head" insertion
//! modes. Source and modelling choices: [`super`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "html"
pub open spec fn w3c_name_html() -> Seq<u32> {
    seq![0x68u32, 0x74, 0x6d, 0x6c]
}

/// "head"
pub open spec fn w3c_name_head() -> Seq<u32> {
    seq![0x68u32, 0x65, 0x61, 0x64]
}

/// "body"
pub open spec fn w3c_name_body() -> Seq<u32> {
    seq![0x62u32, 0x6f, 0x64, 0x79]
}

/// DOM "append" `node` to the Document object: "pre-insert" `node` into
/// the Document before null. Pre-insert first "ensures pre-insert
/// validity", which throws (and so inserts nothing) "if parent is a
/// Document, and … node is an Element and parent has an element child";
/// its other checks are [`dom_insert`]'s guard.
pub open spec fn w3c_append_to_document(p: Parser, node: NodeId) -> Parser {
    if p.stopped || (p.doc.nodes[0].kind is Document && has_element_child(p.doc, 0)) {
        p
    } else {
        dom_insert(p, node, 0, None)
    }
}

/// W3C HTML 5.2 §8.2.5.4.2 the "before html" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-before-html-insertion-mode>).
pub open spec fn w3c_mode_before_html(env: EncFns, p: Parser, t: Tok) -> Outcome {
    let tag = w3c_tag(t);
    if t is Doctype {
        // "A DOCTYPE token": "Parse error."
        Outcome::Done(p)
    } else if t is Comment {
        // "A comment token": "Insert a comment as the last child of the
        // Document object."
        Outcome::Done(insert_comment(p, t->Comment_0, Some(document_location())))
    } else if w3c_space_char(t) {
        // "Ignore the token."
        Outcome::Done(p)
    } else if w3c_start(t, Tag::Html) {
        // "A start tag whose tag name is "html"": "Create an element for the
        // token in the HTML namespace, with the Document as the intended
        // parent."
        let (p1, e) = create_element_for_token(p, t->Start_0, Namespace::Html, 0);
        // "Append it to the Document object."
        let p2 = w3c_append_to_document(p1, e.id);
        // "Put this element in the stack of open elements."
        let p3 = push(p2, e);
        // "Switch the insertion mode to "before head"."
        Outcome::Done(Parser { mode: Mode::BeforeHead, ..p3 })
    } else if t is End && !(tag == Tag::Head || tag == Tag::Body || tag == Tag::Html || tag == Tag::Br) {
        // "Any other end tag": "Parse error." (An end tag whose tag name is
        // one of: "head", "body", "html", "br": "Act as described in the
        // "anything else" entry below.")
        Outcome::Done(p)
    } else {
        // "Anything else": "Create an html element whose node document is
        // the Document object." (An element created for no token: no
        // attributes, and no form owner; "create an element for the token"
        // with an `html` start tag token with no attributes does exactly
        // that.)
        let (p1, e) = create_element_for_token(p, start_tag_named(w3c_name_html()), Namespace::Html, 0);
        // "Append it to the Document object."
        let p2 = w3c_append_to_document(p1, e.id);
        // "Put this element in the stack of open elements."
        let p3 = push(p2, e);
        // "Switch the insertion mode to "before head", then reprocess the
        // token."
        Outcome::Reprocess(Parser { mode: Mode::BeforeHead, ..p3 }, t)
    }
}

/// W3C HTML 5.2 §8.2.5.4.3 the "before head" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-before-head-insertion-mode>).
pub open spec fn w3c_mode_before_head(env: EncFns, p: Parser, t: Tok) -> Outcome {
    let tag = w3c_tag(t);
    if w3c_space_char(t) {
        // "Ignore the token."
        Outcome::Done(p)
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
    } else if w3c_start(t, Tag::Head) {
        // "A start tag whose tag name is "head"": "Insert an HTML element for
        // the token. Set the head element pointer to the newly created head
        // element. Switch the insertion mode to "in head"."
        let (p1, e) = insert_html_element(p, t->Start_0);
        Outcome::Done(Parser { head: Some(e.id), mode: Mode::InHead, ..p1 })
    } else if t is End && !(tag == Tag::Head || tag == Tag::Body || tag == Tag::Html || tag == Tag::Br) {
        // "Any other end tag": "Parse error." (An end tag whose tag name is
        // one of: "head", "body", "html", "br": "Act as described in the
        // "anything else" entry below.")
        Outcome::Done(p)
    } else {
        // "Anything else": "Insert an HTML element for a "head" start tag
        // token with no attributes. Set the head element pointer to the newly
        // created head element. Switch the insertion mode to "in head".
        // Reprocess the current token."
        let (p1, e) = insert_html_element(p, start_tag_named(w3c_name_head()));
        Outcome::Reprocess(Parser { head: Some(e.id), mode: Mode::InHead, ..p1 }, t)
    }
}

/// W3C HTML 5.2 §8.2.5.4.5 the "in head noscript" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-in-head-noscript-insertion-mode>).
pub open spec fn w3c_mode_in_head_noscript(env: EncFns, p: Parser, t: Tok) -> Outcome {
    let tag = w3c_tag(t);
    if t is Doctype {
        // "A DOCTYPE token": "Parse error."
        Outcome::Done(p)
    } else if w3c_start(t, Tag::Html) {
        // "A start tag whose tag name is "html"": "Process the token using
        // the rules for the "in body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    } else if w3c_end(t, Tag::Noscript) {
        // "An end tag whose tag name is "noscript"": "Pop the current node
        // (which will be a noscript element) from the stack of open elements;
        // the new current node will be a head element. Switch the insertion
        // mode to "in head"."
        Outcome::Done(Parser { mode: Mode::InHead, ..pop(p) })
    } else if w3c_space_char(t) || t is Comment || (t is Start && (tag == Tag::Basefont || tag == Tag::Bgsound || tag
        == Tag::Link || tag == Tag::Meta || tag == Tag::Noframes || tag == Tag::Style)) {
        // "A character token that is one of U+0009 …", "A comment token", "A
        // start tag whose tag name is one of: "basefont", "bgsound", "link",
        // "meta", "noframes", "style"": "Process the token using the rules
        // for the "in head" insertion mode."
        Outcome::Using(Mode::InHead, p, t)
    } else if (t is Start && (tag == Tag::Head || tag == Tag::Noscript)) || (t is End && tag != Tag::Br) {
        // "A start tag whose tag name is one of: "head", "noscript"", "Any
        // other end tag": "Parse error." (An end tag whose tag name is "br":
        // "Act as described in the "anything else" entry below.")
        Outcome::Done(p)
    } else {
        // "Anything else": "Parse error. Pop the current node (which will be
        // a noscript element) from the stack of open elements; the new
        // current node will be a head element. Switch the insertion mode to
        // "in head". Reprocess the token."
        Outcome::Reprocess(Parser { mode: Mode::InHead, ..pop(p) }, t)
    }
}

/// "charset"
pub open spec fn w3c_name_charset() -> Seq<u32> {
    seq![0x63u32, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74]
}

/// "http-equiv"
pub open spec fn w3c_name_http_equiv() -> Seq<u32> {
    seq![0x68u32, 0x74, 0x74, 0x70, 0x2d, 0x65, 0x71, 0x75, 0x69, 0x76]
}

/// "content"
pub open spec fn w3c_name_content() -> Seq<u32> {
    seq![0x63u32, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74]
}

/// "Content-Type"
pub open spec fn w3c_content_type() -> Seq<u32> {
    seq![0x43u32, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x2d, 0x54, 0x79, 0x70, 0x65]
}

/// "Change the encoding to" `enc` (the driver's action; see [`super`]: the
/// confidence becomes certain). Nothing, once parsing has stopped (the node
/// limit; see [`super`]).
pub open spec fn w3c_change_encoding(p: Parser, enc: nat) -> Parser {
    if p.stopped {
        p
    } else {
        Parser { actions: p.actions.push(Action::ChangeEncoding(enc)), tentative: false, ..p }
    }
}

/// The `meta` entry's encoding steps, for the element created for `tt`,
/// after it is inserted and popped (`p`).
pub open spec fn w3c_meta_encoding(env: EncFns, p: Parser, tt: TagTok) -> Parser {
    let charset = attr_value(tt.attrs, w3c_name_charset());
    let http_equiv = attr_value(tt.attrs, w3c_name_http_equiv());
    let content = attr_value(tt.attrs, w3c_name_content());
    if charset is Some && (env.get_an_encoding)(charset->Some_0) is Some && p.tentative {
        // "If the element has a charset attribute, and getting an encoding
        // from its value results in an encoding, and the confidence is
        // currently tentative, then change the encoding to the resulting
        // encoding."
        w3c_change_encoding(p, (env.get_an_encoding)(charset->Some_0)->Some_0)
    } else if http_equiv is Some && ascii_ci_eq(http_equiv->Some_0, w3c_content_type()) && content is Some && (
    env.extract_from_meta)(content->Some_0) is Some && (env.get_an_encoding)((env.extract_from_meta)(content->Some_0)->Some_0)
        is Some && p.tentative {
        // "Otherwise, if the element has an http-equiv attribute whose value
        // is an ASCII case-insensitive match for the string "Content-Type",
        // and the element has a content attribute, and applying the
        // algorithm for extracting a character encoding from a meta element
        // to that attribute's value returns an encoding, and the confidence
        // is currently tentative, then change the encoding to the extracted
        // encoding." (The extraction algorithm returns a label,
        // `env.extract_from_meta`; its encoding is the one "get an encoding"
        // gives for it.)
        w3c_change_encoding(p, (env.get_an_encoding)((env.extract_from_meta)(content->Some_0)->Some_0)->Some_0)
    } else {
        p
    }
}

/// The steps of "in head" for a `script` start tag.
pub open spec fn w3c_in_head_script(p: Parser, tt: TagTok) -> Parser {
    // 1. "Let the adjusted insertion location be the appropriate place for
    // inserting a node."
    let loc = adjusted_location(p, None);
    // 2. "Create an element for the token in the HTML namespace, with the
    // intended parent being the element in which the adjusted insertion
    // location finds itself."
    let (p1, e) = create_element_for_token(p, tt, Namespace::Html, loc.parent);
    // 3. "Mark the element as being "parser-inserted" and unset the
    // element's "non-blocking" flag." 4. "If the parser was originally
    // created for the HTML fragment parsing algorithm, then mark the script
    // element as "already started"." (Not modelled: see [`super`].)
    // 5. "Insert the newly created element at the adjusted insertion
    // location."
    let p2 = insert_element_at(p1, e.id, Some(loc));
    // 6. "Push the element onto the stack of open elements so that it is
    // the new current node."
    let p3 = push(p2, e);
    // 7. "Switch the tokenizer to the script data state."
    // 8. "Let the original insertion mode be the current insertion mode."
    // 9. "Switch the insertion mode to "text"."
    Parser { tokenizer: Some(TokenizerState::ScriptData), original_mode: p3.mode, mode: Mode::Text, ..p3 }
}

/// W3C HTML 5.2 §8.2.5.4.4 the "in head" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-in-head-insertion-mode>).
pub open spec fn w3c_mode_in_head(env: EncFns, p: Parser, t: Tok) -> Outcome {
    let tag = w3c_tag(t);
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
    } else if t is Start && (tag == Tag::Base || tag == Tag::Basefont || tag == Tag::Bgsound || tag == Tag::Link) {
        // "A start tag whose tag name is one of: "base", "basefont",
        // "bgsound", "link"": "Insert an HTML element for the token.
        // Immediately pop the current node off the stack of open elements.
        // Acknowledge the token's self-closing flag, if it is set."
        Outcome::Done(pop(insert_html_element(p, t->Start_0).0))
    } else if w3c_start(t, Tag::Meta) {
        // "A start tag whose tag name is "meta"": "Insert an HTML element for
        // the token. Immediately pop the current node off the stack of open
        // elements. Acknowledge the token's self-closing flag, if it is set."
        // Then the encoding steps.
        Outcome::Done(w3c_meta_encoding(env, pop(insert_html_element(p, t->Start_0).0), t->Start_0))
    } else if w3c_start(t, Tag::Title) {
        // "A start tag whose tag name is "title"": "Follow the generic RCDATA
        // element parsing algorithm."
        Outcome::Done(generic_text_parsing(p, t->Start_0, false))
    } else if (w3c_start(t, Tag::Noscript) && p.scripting) || w3c_start(t, Tag::Noframes) || w3c_start(t, Tag::Style) {
        // "A start tag whose tag name is "noscript", if the scripting flag is
        // enabled", "A start tag whose tag name is one of: "noframes",
        // "style"": "Follow the generic raw text element parsing algorithm."
        Outcome::Done(generic_text_parsing(p, t->Start_0, true))
    } else if w3c_start(t, Tag::Noscript) && !p.scripting {
        // "A start tag whose tag name is "noscript", if the scripting flag is
        // disabled": "Insert an HTML element for the token. Switch the
        // insertion mode to "in head noscript"."
        Outcome::Done(Parser { mode: Mode::InHeadNoscript, ..insert_html_element(p, t->Start_0).0 })
    } else if w3c_start(t, Tag::Script) {
        // "A start tag whose tag name is "script"": "Run these steps: …"
        Outcome::Done(w3c_in_head_script(p, t->Start_0))
    } else if w3c_end(t, Tag::Head) {
        // "An end tag whose tag name is "head"": "Pop the current node (which
        // will be the head element) off the stack of open elements. Switch
        // the insertion mode to "after head"."
        Outcome::Done(Parser { mode: Mode::AfterHead, ..pop(p) })
    } else if w3c_start(t, Tag::Template) {
        // "A start tag whose tag name is "template"": "Insert an HTML element
        // for the token."
        let p1 = insert_html_element(p, t->Start_0).0;
        // "Insert a marker at the end of the list of active formatting
        // elements."
        let p2 = push_marker(p1);
        // "Set the frameset-ok flag to "not ok". Switch the insertion mode to
        // "in template". Push "in template" onto the stack of template
        // insertion modes so that it is the new current template insertion
        // mode."
        Outcome::Done(
            Parser { frameset_ok: false, mode: Mode::InTemplate, template_modes: p2.template_modes.push(Mode::InTemplate), ..p2 },
        )
    } else if w3c_end(t, Tag::Template) {
        // "An end tag whose tag name is "template"":
        if !open_has_html(p, Tag::Template) {
            // "If there is no template element on the stack of open elements,
            // then this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, run these steps:" "Generate all implied end tags
            // thoroughly." "If the current node is not a template element,
            // then this is a parse error." "Pop elements from the stack of open
            // elements until a template element has been popped from the
            // stack."
            let p1 = pop_until_popped(generate_all_implied_end_tags_thoroughly(p), Tag::Template);
            // "Clear the list of active formatting elements up to the last
            // marker."
            let p2 = clear_to_last_marker(p1);
            // "Pop the current template insertion mode off the stack of
            // template insertion modes."
            let p3 = Parser { template_modes: p2.template_modes.drop_last(), ..p2 };
            // "Reset the insertion mode appropriately."
            Outcome::Done(reset_insertion_mode(p3))
        }
    } else if w3c_start(t, Tag::Head) || (t is End && !(tag == Tag::Body || tag == Tag::Html || tag == Tag::Br)) {
        // "A start tag whose tag name is "head"", "Any other end tag": "Parse
        // error." (An end tag whose tag name is one of: "body", "html", "br":
        // "Act as described in the "anything else" entry below.")
        Outcome::Done(p)
    } else {
        // "Anything else": "Pop the current node (which will be the head
        // element) off the stack of open elements. Switch the insertion mode
        // to "after head". Reprocess the token."
        Outcome::Reprocess(Parser { mode: Mode::AfterHead, ..pop(p) }, t)
    }
}

/// The node the head element pointer points to, as an entry of the stack of
/// open elements: an HTML `head` element (the pointer is set only to
/// elements "in head" and "before head" create for a `head` start tag).
pub open spec fn w3c_head_elem(p: Parser) -> Elem {
    Elem { id: p.head->Some_0, ns: Namespace::Html, tag: Tag::Head, name: w3c_name_head(), annotation_html: false }
}

/// "Remove the node pointed to by the head element pointer from the stack of
/// open elements. (It might not be the current node at this point.)"
pub open spec fn w3c_remove_head(q: Parser, head: NodeId) -> Parser {
    let i = open_index_of(q, head);
    if i >= 0 {
        remove_open_at(q, i)
    } else {
        q
    }
}

/// W3C HTML 5.2 §8.2.5.4.6 the "after head" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-after-head-insertion-mode>).
pub open spec fn w3c_mode_after_head(env: EncFns, p: Parser, t: Tok) -> Outcome {
    let tag = w3c_tag(t);
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
    } else if w3c_start(t, Tag::Body) {
        // "A start tag whose tag name is "body"": "Insert an HTML element for
        // the token. Set the frameset-ok flag to "not ok". Switch the
        // insertion mode to "in body"."
        Outcome::Done(Parser { frameset_ok: false, mode: Mode::InBody, ..insert_html_element(p, t->Start_0).0 })
    } else if w3c_start(t, Tag::Frameset) {
        // "A start tag whose tag name is "frameset"": "Insert an HTML element
        // for the token. Switch the insertion mode to "in frameset"."
        Outcome::Done(Parser { mode: Mode::InFrameset, ..insert_html_element(p, t->Start_0).0 })
    } else if t is Start && (tag == Tag::Base || tag == Tag::Basefont || tag == Tag::Bgsound || tag == Tag::Link || tag
        == Tag::Meta || tag == Tag::Noframes || tag == Tag::Script || tag == Tag::Style || tag == Tag::Template || tag
        == Tag::Title) {
        // "A start tag whose tag name is one of: "base", "basefont",
        // "bgsound", "link", "meta", "noframes", "script", "style",
        // "template", "title"": "Parse error. Push the node pointed to by the
        // head element pointer onto the stack of open elements."
        let p1 = push(p, w3c_head_elem(p));
        // "Process the token using the rules for the "in head" insertion
        // mode."
        match w3c_mode_in_head(env, p1, t) {
            // "Remove the node pointed to by the head element pointer from
            // the stack of open elements."
            Outcome::Done(q) => Outcome::Done(w3c_remove_head(q, p.head->Some_0)),
            // Never: "in head" handles each of these tags itself.
            other => other,
        }
    } else if w3c_end(t, Tag::Template) {
        // "An end tag whose tag name is "template"": "Process the token using
        // the rules for the "in head" insertion mode."
        Outcome::Using(Mode::InHead, p, t)
    } else if w3c_start(t, Tag::Head) || (t is End && !(tag == Tag::Body || tag == Tag::Html || tag == Tag::Br)) {
        // "A start tag whose tag name is "head"", "Any other end tag": "Parse
        // error." (An end tag whose tag name is one of: "body", "html", "br":
        // "Act as described in the "anything else" entry below.")
        Outcome::Done(p)
    } else {
        // "Anything else": "Insert an HTML element for a "body" start tag
        // token with no attributes. Switch the insertion mode to "in body".
        // Reprocess the current token."
        Outcome::Reprocess(Parser { mode: Mode::InBody, ..insert_html_element(p, start_tag_named(w3c_name_body())).0 }, t)
    }
}

} // verus!
