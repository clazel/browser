//! W3C HTML 5.2 §8.2.5.4.9 to §8.2.5.4.15: the "in table", "in table
//! text", "in caption", "in column group", "in table body", "in row" and
//! "in cell" insertion modes. Source and modelling choices: [`super`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "colgroup"
pub open spec fn w3c_name_colgroup() -> Seq<u32> {
    seq![0x63u32, 0x6f, 0x6c, 0x67, 0x72, 0x6f, 0x75, 0x70]
}

/// "tbody"
pub open spec fn w3c_name_tbody() -> Seq<u32> {
    seq![0x74u32, 0x62, 0x6f, 0x64, 0x79]
}

/// "Clear the stack back to a table context": "while the current node is
/// not a table, template, or html element, pop elements from the stack of
/// open elements."
pub open spec fn w3c_clear_to_table_context(p: Parser) -> Parser {
    pop_while(p, |e: Elem| !(is_html(e, Tag::Table) || is_html(e, Tag::Template) || is_html(e, Tag::Html)))
}

/// "In table"'s "anything else" entry: "Parse error. Enable foster
/// parenting, process the token using the rules for the "in body"
/// insertion mode, and then disable foster parenting." The "in body" rules
/// are applied here (see [`super`]), and so are the "in head" rules when
/// "in body" says to process the token with them (its `base`, …, `title`
/// entry), so that they too run with foster parenting enabled.
pub open spec fn w3c_in_table_anything_else(env: EncFns, p: Parser, t: Tok) -> Outcome {
    match w3c_mode_in_body(env, Parser { foster: true, ..p }, t) {
        Outcome::Done(q) => Outcome::Done(Parser { foster: false, ..q }),
        Outcome::Using(m, q, t2) => if m == Mode::InHead {
            match w3c_mode_in_head(env, q, t2) {
                Outcome::Done(q2) => Outcome::Done(Parser { foster: false, ..q2 }),
                Outcome::Reprocess(q2, t3) => Outcome::Reprocess(Parser { foster: false, ..q2 }, t3),
                Outcome::Using(m2, q2, t3) => Outcome::Using(m2, Parser { foster: false, ..q2 }, t3),
            }
        } else {
            Outcome::Using(m, Parser { foster: false, ..q }, t2)
        },
        Outcome::Reprocess(q, t2) => Outcome::Reprocess(Parser { foster: false, ..q }, t2),
    }
}

/// The token is a start tag `input` with "an attribute with the name
/// "type"" whose value is "an ASCII case-insensitive match for the string
/// "hidden"".
pub open spec fn w3c_hidden_input(t: Tok) -> bool {
    w3c_start(t, Tag::Input) && w3c_input_hidden(t->Start_0)
}

/// W3C HTML 5.2 §8.2.5.4.9 the "in table" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-in-table-insertion-mode>).
pub open spec fn w3c_mode_in_table(env: EncFns, p: Parser, t: Tok) -> Outcome {
    let tag = w3c_tag(t);
    let cur = current_node(p);
    if t is Char && (is_html(cur, Tag::Table) || is_html(cur, Tag::Tbody) || is_html(cur, Tag::Tfoot) || is_html(cur, Tag::Thead)
        || is_html(cur, Tag::Tr)) {
        // "A character token, if the current node is table, tbody, tfoot,
        // thead, or tr element": "Let the pending table character tokens be
        // an empty list of tokens. Let the original insertion mode be the
        // current insertion mode. Switch the insertion mode to "in table
        // text" and reprocess the token."
        Outcome::Reprocess(Parser { pending_table_text: seq![], original_mode: p.mode, mode: Mode::InTableText, ..p }, t)
    } else if t is Comment {
        // "A comment token": "Insert a comment."
        Outcome::Done(insert_comment(p, t->Comment_0, None))
    } else if t is Doctype {
        // "A DOCTYPE token": "Parse error."
        Outcome::Done(p)
    } else if w3c_start(t, Tag::Caption) {
        // "A start tag whose tag name is "caption"": "Clear the stack back to
        // a table context. Insert a marker at the end of the list of active
        // formatting elements. Insert an HTML element for the token, then
        // switch the insertion mode to "in caption"."
        let q = insert_html_element(push_marker(w3c_clear_to_table_context(p)), t->Start_0).0;
        Outcome::Done(Parser { mode: Mode::InCaption, ..q })
    } else if w3c_start(t, Tag::Colgroup) {
        // "A start tag whose tag name is "colgroup"": "Clear the stack back to
        // a table context. Insert an HTML element for the token, then switch
        // the insertion mode to "in column group"."
        let q = insert_html_element(w3c_clear_to_table_context(p), t->Start_0).0;
        Outcome::Done(Parser { mode: Mode::InColumnGroup, ..q })
    } else if w3c_start(t, Tag::Col) {
        // "A start tag whose tag name is "col"": "Clear the stack back to a
        // table context. Insert an HTML element for a "colgroup" start tag
        // token with no attributes, then switch the insertion mode to "in
        // column group". Reprocess the current token."
        let q = insert_html_element(w3c_clear_to_table_context(p), start_tag_named(w3c_name_colgroup())).0;
        Outcome::Reprocess(Parser { mode: Mode::InColumnGroup, ..q }, t)
    } else if t is Start && (tag == Tag::Tbody || tag == Tag::Tfoot || tag == Tag::Thead) {
        // "A start tag whose tag name is one of: "tbody", "tfoot", "thead"":
        // "Clear the stack back to a table context. Insert an HTML element
        // for the token, then switch the insertion mode to "in table body"."
        let q = insert_html_element(w3c_clear_to_table_context(p), t->Start_0).0;
        Outcome::Done(Parser { mode: Mode::InTableBody, ..q })
    } else if t is Start && (tag == Tag::Td || tag == Tag::Th || tag == Tag::Tr) {
        // "A start tag whose tag name is one of: "td", "th", "tr"": "Clear
        // the stack back to a table context. Insert an HTML element for a
        // "tbody" start tag token with no attributes, then switch the
        // insertion mode to "in table body". Reprocess the current token."
        let q = insert_html_element(w3c_clear_to_table_context(p), start_tag_named(w3c_name_tbody())).0;
        Outcome::Reprocess(Parser { mode: Mode::InTableBody, ..q }, t)
    } else if w3c_start(t, Tag::Table) {
        // "A start tag whose tag name is "table"": "Parse error."
        if !has_in_scope(p, Tag::Table, Scope::Table) {
            // "If the stack of open elements does not have a table element in
            // table scope, ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise: Pop elements from this stack until a table element
            // has been popped from the stack. Reset the insertion mode
            // appropriately. Reprocess the token."
            Outcome::Reprocess(reset_insertion_mode(pop_until_popped(p, Tag::Table)), t)
        }
    } else if w3c_end(t, Tag::Table) {
        // "An end tag whose tag name is "table"":
        if !has_in_scope(p, Tag::Table, Scope::Table) {
            // "If the stack of open elements does not have a table element in
            // table scope, this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise: Pop elements from this stack until a table element
            // has been popped from the stack. Reset the insertion mode
            // appropriately."
            Outcome::Done(reset_insertion_mode(pop_until_popped(p, Tag::Table)))
        }
    } else if t is End && (tag == Tag::Body || tag == Tag::Caption || tag == Tag::Col || tag == Tag::Colgroup || tag == Tag::Html
        || tag == Tag::Tbody || tag == Tag::Td || tag == Tag::Tfoot || tag == Tag::Th || tag == Tag::Thead || tag == Tag::Tr) {
        // "An end tag whose tag name is one of: "body", "caption", "col",
        // "colgroup", "html", "tbody", "td", "tfoot", "th", "thead", "tr"":
        // "Parse error."
        Outcome::Done(p)
    } else if (t is Start && (tag == Tag::Style || tag == Tag::Script || tag == Tag::Template)) || w3c_end(t, Tag::Template) {
        // "A start tag whose tag name is one of: "style", "script",
        // "template"", "An end tag whose tag name is "template"": "Process the
        // token using the rules for the "in head" insertion mode."
        Outcome::Using(Mode::InHead, p, t)
    } else if w3c_start(t, Tag::Input) && w3c_input_hidden(t->Start_0) {
        // "A start tag whose tag name is "input"": (a hidden one; any other
        // "act as described in the "anything else" entry below") "Parse
        // error. Insert an HTML element for the token. Pop that input element
        // off the stack of open elements. Acknowledge the token's
        // self-closing flag, if it is set."
        Outcome::Done(pop(insert_html_element(p, t->Start_0).0))
    } else if w3c_start(t, Tag::Form) {
        // "A start tag whose tag name is "form"": "Parse error."
        if open_has_html(p, Tag::Template) || p.form is Some {
            // "If there is a template element on the stack of open elements,
            // or if the form element pointer is not null, ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise: Insert an HTML element for the token, and set the
            // form element pointer to point to the element created. Pop that
            // form element off the stack of open elements."
            // (A stopped parser changes nothing: see [`super`].)
            let (q, e) = insert_html_element(p, t->Start_0);
            if q.stopped {
                Outcome::Done(q)
            } else {
                Outcome::Done(pop(Parser { form: Some(e.id), ..q }))
            }
        }
    } else if t is Eof {
        // "An end-of-file token": "Process the token using the rules for the
        // "in body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    } else {
        // "Anything else":
        w3c_in_table_anything_else(env, p, t)
    }
}

/// Every character of `s` from index `i` on is one of the space
/// characters (U+0009, U+000A, U+000C, U+000D, U+0020).
pub open spec fn w3c_all_space(s: Seq<u32>, i: int) -> bool
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        true
    } else {
        w3c_space_char(Tok::Char(s[i])) && w3c_all_space(s, i + 1)
    }
}

/// "Reprocess the character tokens in the pending table character tokens
/// list using the rules given in the "anything else" entry in the "in
/// table" insertion mode", from the `i`th on. (The "in body" rules handle a
/// character token themselves: the outcome is always `Done`.)
pub open spec fn w3c_reprocess_table_text(env: EncFns, p: Parser, s: Seq<u32>, i: int) -> Parser
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        p
    } else {
        let q = match w3c_in_table_anything_else(env, p, Tok::Char(s[i])) {
            Outcome::Done(q) => q,
            Outcome::Reprocess(q, _) => q,
            Outcome::Using(_, q, _) => q,
        };
        w3c_reprocess_table_text(env, q, s, i + 1)
    }
}

/// W3C HTML 5.2 §8.2.5.4.10 the "in table text" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-in-table-text-insertion-mode>).
pub open spec fn w3c_mode_in_table_text(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is Char && t->Char_0 == 0 {
        // "A character token that is U+0000 NULL": "Parse error."
        Outcome::Done(p)
    } else if t is Char {
        // "Any other character token": "Append the character token to the
        // pending table character tokens list."
        Outcome::Done(Parser { pending_table_text: p.pending_table_text.push(t->Char_0), ..p })
    } else {
        // "Anything else":
        let pending = p.pending_table_text;
        let q = if !w3c_all_space(pending, 0) {
            // "If any of the tokens in the pending table character tokens list
            // are character tokens that are not space characters, then this is
            // a parse error: reprocess the character tokens in the pending
            // table character tokens list using the rules given in the
            // "anything else" entry in the "in table" insertion mode."
            w3c_reprocess_table_text(env, p, pending, 0)
        } else {
            // "Otherwise, insert the characters given by the pending table
            // character tokens list."
            insert_characters(p, pending)
        };
        // "Switch the insertion mode to the original insertion mode and
        // reprocess the token."
        Outcome::Reprocess(Parser { mode: q.original_mode, ..q }, t)
    }
}

/// The steps "in caption" runs for an end tag `caption` (and, then
/// reprocessing, for the second entry): "Generate implied end tags. Now, if
/// the current node is not a caption element, then this is a parse error.
/// Pop elements from this stack until a caption element has been popped
/// from the stack. Clear the list of active formatting elements up to the
/// last marker. Switch the insertion mode to "in table"."
pub open spec fn w3c_close_caption(p: Parser) -> Parser {
    let q = clear_to_last_marker(pop_until_popped(generate_implied_end_tags(p, None), Tag::Caption));
    Parser { mode: Mode::InTable, ..q }
}

/// W3C HTML 5.2 §8.2.5.4.11 the "in caption" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-in-caption-insertion-mode>).
pub open spec fn w3c_mode_in_caption(env: EncFns, p: Parser, t: Tok) -> Outcome {
    let tag = w3c_tag(t);
    if w3c_end(t, Tag::Caption) {
        // "An end tag whose tag name is "caption"":
        if !has_in_scope(p, Tag::Caption, Scope::Table) {
            // "If the stack of open elements does not have a caption element
            // in table scope, this is a parse error; ignore the token.
            // (fragment case)"
            Outcome::Done(p)
        } else {
            // "Otherwise: …"
            Outcome::Done(w3c_close_caption(p))
        }
    } else if (t is Start && (tag == Tag::Caption || tag == Tag::Col || tag == Tag::Colgroup || tag == Tag::Tbody || tag
        == Tag::Td || tag == Tag::Tfoot || tag == Tag::Th || tag == Tag::Thead || tag == Tag::Tr)) || w3c_end(t, Tag::Table) {
        // "A start tag whose tag name is one of: "caption", "col",
        // "colgroup", "tbody", "td", "tfoot", "th", "thead", "tr"", "An end
        // tag whose tag name is "table"":
        if !has_in_scope(p, Tag::Caption, Scope::Table) {
            // "If the stack of open elements does not have a caption element
            // in table scope, this is a parse error; ignore the token.
            // (fragment case)"
            Outcome::Done(p)
        } else {
            // "Otherwise: …" and "Reprocess the token."
            Outcome::Reprocess(w3c_close_caption(p), t)
        }
    } else if t is End && (tag == Tag::Body || tag == Tag::Col || tag == Tag::Colgroup || tag == Tag::Html || tag
        == Tag::Tbody || tag == Tag::Td || tag == Tag::Tfoot || tag == Tag::Th || tag == Tag::Thead || tag == Tag::Tr) {
        // "An end tag whose tag name is one of: "body", "col", "colgroup",
        // "html", "tbody", "td", "tfoot", "th", "thead", "tr"": "Parse
        // error."
        Outcome::Done(p)
    } else {
        // "Anything else": "Process the token using the rules for the "in
        // body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    }
}

/// W3C HTML 5.2 §8.2.5.4.12 the "in column group" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-in-column-group-insertion-mode>).
pub open spec fn w3c_mode_in_column_group(env: EncFns, p: Parser, t: Tok) -> Outcome {
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
    } else if w3c_start(t, Tag::Col) {
        // "A start tag whose tag name is "col"": "Insert an HTML element for
        // the token. Immediately pop the current node off the stack of open
        // elements. Acknowledge the token's self-closing flag, if it is set."
        Outcome::Done(pop(insert_html_element(p, t->Start_0).0))
    } else if w3c_end(t, Tag::Colgroup) {
        // "An end tag whose tag name is "colgroup"":
        if !w3c_current_is(p, Tag::Colgroup) {
            // "If the current node is not a colgroup element, then this is a
            // parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, pop the current node from the stack of open
            // elements. Switch the insertion mode to "in table"."
            Outcome::Done(Parser { mode: Mode::InTable, ..pop(p) })
        }
    } else if w3c_end(t, Tag::Col) {
        // "An end tag whose tag name is "col"": "Parse error."
        Outcome::Done(p)
    } else if w3c_start(t, Tag::Template) || w3c_end(t, Tag::Template) {
        // "A start tag whose tag name is "template"", "An end tag whose tag
        // name is "template"": "Process the token using the rules for the "in
        // head" insertion mode."
        Outcome::Using(Mode::InHead, p, t)
    } else if t is Eof {
        // "An end-of-file token": "Process the token using the rules for the
        // "in body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    } else {
        // "Anything else":
        if !w3c_current_is(p, Tag::Colgroup) {
            // "If the current node is not a colgroup element, then this is a
            // parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, pop the current node from the stack of open
            // elements. Switch the insertion mode to "in table". Reprocess
            // the token."
            Outcome::Reprocess(Parser { mode: Mode::InTable, ..pop(p) }, t)
        }
    }
}

/// "Clear the stack back to a table body context": "while the current node
/// is not a tbody, tfoot, thead, template, or html element, pop elements
/// from the stack of open elements."
pub open spec fn w3c_clear_to_table_body_context(p: Parser) -> Parser {
    pop_while(
        p,
        |e: Elem|
            !(is_html(e, Tag::Tbody) || is_html(e, Tag::Tfoot) || is_html(e, Tag::Thead) || is_html(e, Tag::Template) || is_html(
                e,
                Tag::Html,
            )),
    )
}

/// "Clear the stack back to a table row context": "while the current node
/// is not a tr, template, or html element, pop elements from the stack of
/// open elements."
pub open spec fn w3c_clear_to_table_row_context(p: Parser) -> Parser {
    pop_while(p, |e: Elem| !(is_html(e, Tag::Tr) || is_html(e, Tag::Template) || is_html(e, Tag::Html)))
}

/// "The stack of open elements has a tbody, thead, or tfoot element in
/// table scope."
pub open spec fn w3c_has_table_section_in_table_scope(p: Parser) -> bool {
    in_scope_from(
        p.open,
        p.open.len() as int,
        |e: Elem| is_html(e, Tag::Tbody) || is_html(e, Tag::Thead) || is_html(e, Tag::Tfoot),
        Scope::Table,
    )
}

/// "tr"
pub open spec fn w3c_name_tr() -> Seq<u32> {
    seq![0x74u32, 0x72]
}

/// W3C HTML 5.2 §8.2.5.4.13 the "in table body" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-in-table-body-insertion-mode>).
pub open spec fn w3c_mode_in_table_body(env: EncFns, p: Parser, t: Tok) -> Outcome {
    let tag = w3c_tag(t);
    if w3c_start(t, Tag::Tr) {
        // "A start tag whose tag name is "tr"": "Clear the stack back to a
        // table body context. Insert an HTML element for the token, then
        // switch the insertion mode to "in row"."
        let q = insert_html_element(w3c_clear_to_table_body_context(p), t->Start_0).0;
        Outcome::Done(Parser { mode: Mode::InRow, ..q })
    } else if w3c_start(t, Tag::Th) || w3c_start(t, Tag::Td) {
        // "A start tag whose tag name is one of: "th", "td"": "Parse error.
        // Clear the stack back to a table body context. Insert an HTML
        // element for a "tr" start tag token with no attributes, then switch
        // the insertion mode to "in row". Reprocess the current token."
        let q = insert_html_element(w3c_clear_to_table_body_context(p), start_tag_named(w3c_name_tr())).0;
        Outcome::Reprocess(Parser { mode: Mode::InRow, ..q }, t)
    } else if t is End && (tag == Tag::Tbody || tag == Tag::Tfoot || tag == Tag::Thead) {
        // "An end tag whose tag name is one of: "tbody", "tfoot", "thead"":
        if !has_in_scope(p, tag, Scope::Table) {
            // "If the stack of open elements does not have an element in
            // table scope that is an HTML element with the same tag name as
            // the token, this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise: Clear the stack back to a table body context. Pop
            // the current node from the stack of open elements. Switch the
            // insertion mode to "in table"."
            Outcome::Done(Parser { mode: Mode::InTable, ..pop(w3c_clear_to_table_body_context(p)) })
        }
    } else if (t is Start && (tag == Tag::Caption || tag == Tag::Col || tag == Tag::Colgroup || tag == Tag::Tbody || tag
        == Tag::Tfoot || tag == Tag::Thead)) || w3c_end(t, Tag::Table) {
        // "A start tag whose tag name is one of: "caption", "col",
        // "colgroup", "tbody", "tfoot", "thead"", "An end tag whose tag name
        // is "table"":
        if !w3c_has_table_section_in_table_scope(p) {
            // "If the stack of open elements does not have a tbody, thead, or
            // tfoot element in table scope, this is a parse error; ignore the
            // token."
            Outcome::Done(p)
        } else {
            // "Otherwise: Clear the stack back to a table body context. Pop
            // the current node from the stack of open elements. Switch the
            // insertion mode to "in table". Reprocess the token."
            Outcome::Reprocess(Parser { mode: Mode::InTable, ..pop(w3c_clear_to_table_body_context(p)) }, t)
        }
    } else if t is End && (tag == Tag::Body || tag == Tag::Caption || tag == Tag::Col || tag == Tag::Colgroup || tag
        == Tag::Html || tag == Tag::Td || tag == Tag::Th || tag == Tag::Tr) {
        // "An end tag whose tag name is one of: "body", "caption", "col",
        // "colgroup", "html", "td", "th", "tr"": "Parse error."
        Outcome::Done(p)
    } else {
        // "Anything else": "Process the token using the rules for the "in
        // table" insertion mode."
        Outcome::Using(Mode::InTable, p, t)
    }
}

/// W3C HTML 5.2 §8.2.5.4.14 the "in row" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-in-row-insertion-mode>).
pub open spec fn w3c_mode_in_row(env: EncFns, p: Parser, t: Tok) -> Outcome {
    let tag = w3c_tag(t);
    if w3c_start(t, Tag::Th) || w3c_start(t, Tag::Td) {
        // "A start tag whose tag name is one of: "th", "td"": "Clear the
        // stack back to a table row context. Insert an HTML element for the
        // token, then switch the insertion mode to "in cell". Insert a marker
        // at the end of the list of active formatting elements."
        let q = insert_html_element(w3c_clear_to_table_row_context(p), t->Start_0).0;
        Outcome::Done(push_marker(Parser { mode: Mode::InCell, ..q }))
    } else if w3c_end(t, Tag::Tr) {
        // "An end tag whose tag name is "tr"":
        if !has_in_scope(p, Tag::Tr, Scope::Table) {
            // "If the stack of open elements does not have a tr element in
            // table scope, this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise: Clear the stack back to a table row context. Pop the
            // current node (which will be a tr element) from the stack of
            // open elements. Switch the insertion mode to "in table body"."
            Outcome::Done(Parser { mode: Mode::InTableBody, ..pop(w3c_clear_to_table_row_context(p)) })
        }
    } else if (t is Start && (tag == Tag::Caption || tag == Tag::Col || tag == Tag::Colgroup || tag == Tag::Tbody || tag
        == Tag::Tfoot || tag == Tag::Thead || tag == Tag::Tr)) || w3c_end(t, Tag::Table) {
        // "A start tag whose tag name is one of: "caption", "col",
        // "colgroup", "tbody", "tfoot", "thead", "tr"", "An end tag whose tag
        // name is "table"":
        if !has_in_scope(p, Tag::Tr, Scope::Table) {
            // "If the stack of open elements does not have a tr element in
            // table scope, this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise: Clear the stack back to a table row context. Pop the
            // current node (which will be a tr element) from the stack of
            // open elements. Switch the insertion mode to "in table body".
            // Reprocess the token."
            Outcome::Reprocess(Parser { mode: Mode::InTableBody, ..pop(w3c_clear_to_table_row_context(p)) }, t)
        }
    } else if t is End && (tag == Tag::Tbody || tag == Tag::Tfoot || tag == Tag::Thead) {
        // "An end tag whose tag name is one of: "tbody", "tfoot", "thead"":
        if !has_in_scope(p, tag, Scope::Table) {
            // "If the stack of open elements does not have an element in table
            // scope that is an HTML element with the same tag name as the
            // token, this is a parse error; ignore the token."
            Outcome::Done(p)
        } else if !has_in_scope(p, Tag::Tr, Scope::Table) {
            // "If the stack of open elements does not have a tr element in
            // table scope, ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise: Clear the stack back to a table row context. Pop the
            // current node (which will be a tr element) from the stack of
            // open elements. Switch the insertion mode to "in table body".
            // Reprocess the token."
            Outcome::Reprocess(Parser { mode: Mode::InTableBody, ..pop(w3c_clear_to_table_row_context(p)) }, t)
        }
    } else if t is End && (tag == Tag::Body || tag == Tag::Caption || tag == Tag::Col || tag == Tag::Colgroup || tag
        == Tag::Html || tag == Tag::Td || tag == Tag::Th) {
        // "An end tag whose tag name is one of: "body", "caption", "col",
        // "colgroup", "html", "td", "th"": "Parse error."
        Outcome::Done(p)
    } else {
        // "Anything else": "Process the token using the rules for the "in
        // table" insertion mode."
        Outcome::Using(Mode::InTable, p, t)
    }
}

/// "Pop elements from the stack of open elements stack until a td element
/// or a th element has been popped from the stack."
pub open spec fn w3c_pop_until_cell_popped(p: Parser) -> Parser
    decreases p.open.len(),
{
    if p.open.len() == 0 {
        p
    } else if is_html(current_node(p), Tag::Td) || is_html(current_node(p), Tag::Th) {
        pop(p)
    } else {
        w3c_pop_until_cell_popped(pop(p))
    }
}

/// "Close the cell": "Generate implied end tags. If the current node is not
/// now a td element or a th element, then this is a parse error. Pop
/// elements from the stack of open elements stack until a td element or a
/// th element has been popped from the stack. Clear the list of active
/// formatting elements up to the last marker. Switch the insertion mode to
/// "in row"."
pub open spec fn w3c_close_the_cell(p: Parser) -> Parser {
    let q = clear_to_last_marker(w3c_pop_until_cell_popped(generate_implied_end_tags(p, None)));
    Parser { mode: Mode::InRow, ..q }
}

/// W3C HTML 5.2 §8.2.5.4.15 the "in cell" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-in-cell-insertion-mode>).
pub open spec fn w3c_mode_in_cell(env: EncFns, p: Parser, t: Tok) -> Outcome {
    let tag = w3c_tag(t);
    if t is End && (tag == Tag::Td || tag == Tag::Th) {
        // "An end tag whose tag name is one of: "td", "th"":
        if !has_in_scope(p, tag, Scope::Table) {
            // "If the stack of open elements does not have an element in table
            // scope that is an HTML element with the same tag name as that of
            // the token, then this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise: Generate implied end tags. Now, if the current node
            // is not an HTML element with the same tag name as the token, then
            // this is a parse error. Pop elements from the stack of open
            // elements stack until an HTML element with the same tag name as
            // the token has been popped from the stack. Clear the list of
            // active formatting elements up to the last marker. Switch the
            // insertion mode to "in row"."
            let q = clear_to_last_marker(pop_until_popped(generate_implied_end_tags(p, None), tag));
            Outcome::Done(Parser { mode: Mode::InRow, ..q })
        }
    } else if t is Start && (tag == Tag::Caption || tag == Tag::Col || tag == Tag::Colgroup || tag == Tag::Tbody || tag
        == Tag::Td || tag == Tag::Tfoot || tag == Tag::Th || tag == Tag::Thead || tag == Tag::Tr) {
        // "A start tag whose tag name is one of: "caption", "col",
        // "colgroup", "tbody", "td", "tfoot", "th", "thead", "tr"":
        if !in_scope_from(p.open, p.open.len() as int, |e: Elem| is_html(e, Tag::Td) || is_html(e, Tag::Th), Scope::Table) {
            // "If the stack of open elements does not have a td or th element
            // in table scope, then this is a parse error; ignore the token.
            // (fragment case)"
            Outcome::Done(p)
        } else {
            // "Otherwise, close the cell (see below) and reprocess the
            // token."
            Outcome::Reprocess(w3c_close_the_cell(p), t)
        }
    } else if t is End && (tag == Tag::Body || tag == Tag::Caption || tag == Tag::Col || tag == Tag::Colgroup || tag
        == Tag::Html) {
        // "An end tag whose tag name is one of: "body", "caption", "col",
        // "colgroup", "html"": "Parse error."
        Outcome::Done(p)
    } else if t is End && (tag == Tag::Table || tag == Tag::Tbody || tag == Tag::Tfoot || tag == Tag::Thead || tag
        == Tag::Tr) {
        // "An end tag whose tag name is one of: "table", "tbody", "tfoot",
        // "thead", "tr"":
        if !has_in_scope(p, tag, Scope::Table) {
            // "If the stack of open elements does not have an element in table
            // scope that is an HTML element with the same tag name as that of
            // the token, then this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, close the cell (see below) and reprocess the
            // token."
            Outcome::Reprocess(w3c_close_the_cell(p), t)
        }
    } else {
        // "Anything else": "Process the token using the rules for the "in
        // body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    }
}

} // verus!
