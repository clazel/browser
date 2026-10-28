//! HTML §13.2.6.4.9 the "in table" insertion mode, and "clear the stack back
//! to a table context".
//!
//! Modelling choice: the "anything else" case ("Enable foster parenting,
//! process the token using the rules for the "in body" insertion mode, and
//! then disable foster parenting") cannot be an `Outcome::Using`, since the
//! reprocessing loop could not disable foster parenting afterwards. It is
//! [`in_table_anything_else`]: a direct call of [`mode_in_body`] on the parser
//! with `foster: true`, then `foster: false` on the result. There is no
//! recursion cycle: the "in body" rules never apply the "in table" rules
//! directly (only through the loop, by switching the insertion mode). When
//! the "in body" rules do not finish the token themselves, the outcome is
//! handled as follows (see [`in_table_anything_else`] for why each is the
//! standard's meaning):
//! - `Using(InHead, …)` (the `base`, `basefont`, `bgsound`, `link`, `meta`,
//!   `noframes` and `title` start tags): the "in head" rules are applied
//!   directly, still with foster parenting enabled, and foster parenting is
//!   disabled on their result;
//! - any other outcome is returned with foster parenting disabled.

#[allow(unused_imports)]
use super::super::dispatch::*;
#[allow(unused_imports)]
use super::super::insert::*;
#[allow(unused_imports)]
use super::super::state::*;
#[allow(unused_imports)]
use super::super::tags::*;
#[allow(unused_imports)]
use super::in_body::*;
#[allow(unused_imports)]
use super::in_head::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "clear the stack back to a table context": "while the current node is not
/// a table, template, or html element, pop elements from the stack of open
/// elements."
pub open spec fn clear_stack_back_to_table_context(p: Parser) -> Parser {
    pop_while(p, |e: Elem| !(is_html(e, Tag::Table) || is_html(e, Tag::Template) || is_html(e, Tag::Html)))
}

/// The parser an outcome carries.
pub open spec fn outcome_parser(o: Outcome) -> Parser {
    match o {
        Outcome::Done(q) => q,
        Outcome::Reprocess(q, _) => q,
        Outcome::Using(_, q, _) => q,
    }
}

/// The outcome with foster parenting disabled in its parser.
pub open spec fn outcome_without_foster(o: Outcome) -> Outcome {
    match o {
        Outcome::Done(q) => Outcome::Done(Parser { foster: false, ..q }),
        Outcome::Reprocess(q, t2) => Outcome::Reprocess(Parser { foster: false, ..q }, t2),
        Outcome::Using(m, q, t2) => Outcome::Using(m, Parser { foster: false, ..q }, t2),
    }
}

/// "colgroup"
pub open spec fn name_colgroup() -> Seq<u32> {
    seq![0x63u32, 0x6f, 0x6c, 0x67, 0x72, 0x6f, 0x75, 0x70]
}

/// "tbody"
pub open spec fn name_tbody() -> Seq<u32> {
    seq![0x74u32, 0x62, 0x6f, 0x64, 0x79]
}

/// The "in table" `input` case's test: "the token does not have an attribute
/// with the name "type", or … it does, but that attribute's value is not an
/// ASCII case-insensitive match for "hidden"" (`false`), or it does
/// (`true`).
pub open spec fn in_table_input_is_hidden(tt: TagTok) -> bool {
    // "type"
    match attr_value(tt.attrs, seq![0x74u32, 0x79, 0x70, 0x65]) {
        // "hidden"
        Some(v) => ascii_ci_eq(v, seq![0x68u32, 0x69, 0x64, 0x64, 0x65, 0x6e]),
        None => false,
    }
}

/// The "in table" insertion mode's "anything else" entry: "Parse error.
/// Enable foster parenting, process the token using the rules for the "in
/// body" insertion mode, and then disable foster parenting." (Also used by
/// the "in table text" mode, which reprocesses characters "using the rules
/// given in the "anything else" entry in the "in table" insertion mode".)
pub open spec fn in_table_anything_else(env: EncFns, p: Parser, t: Tok) -> Outcome {
    // "Enable foster parenting, process the token using the rules for the
    // "in body" insertion mode"
    let o = mode_in_body(env, Parser { foster: true, ..p }, t);
    // "and then disable foster parenting."
    match o {
        // The "in body" rules handled the token.
        Outcome::Done(_) => outcome_without_foster(o),
        // The "in body" rules process the token using the "in head" rules
        // (its `base`, `basefont`, `bgsound`, `link`, `meta`, `noframes` and
        // `title` start tags reach here; this mode handles `style`,
        // `script` and `template` itself): that processing is part of
        // processing the token using the "in body" rules, so it happens with
        // foster parenting enabled (a `meta` after `<table>` is fostered),
        // and foster parenting is disabled after it. The "in head" rules
        // never apply the "in table" rules directly, so the call is not
        // recursive.
        Outcome::Using(Mode::InHead, q, t2) => outcome_without_foster(mode_in_head(env, q, t2)),
        // Any other outcome is the loop's, with foster parenting disabled.
        // Only one is reachable from this entry: a start tag "image", which
        // the "in body" rules change to "img" and reprocess. The insertion
        // mode is still "in table", so the reprocessing applies these rules
        // again and reaches this entry, which enables foster parenting for
        // it as the standard's nested reprocessing does. (The others are not
        // reachable here: the "in body" `html` end tag case, which this mode
        // ignores before "anything else", and its end-of-file case, which
        // this mode handles itself.)
        _ => outcome_without_foster(o),
    }
}

/// §13.2.6.4.9 the "in table" insertion mode.
/// <https://html.spec.whatwg.org/multipage/parsing.html#parsing-main-intable>
pub open spec fn mode_in_table(env: EncFns, p: Parser, t: Tok) -> Outcome {
    let cur = current_node(p);
    if t is Char && (is_html(cur, Tag::Table) || is_html(cur, Tag::Tbody) || is_html(cur, Tag::Template) || is_html(
        cur,
        Tag::Tfoot,
    ) || is_html(cur, Tag::Thead) || is_html(cur, Tag::Tr)) {
        // 1. "A character token, if the current node is table, tbody,
        // template, tfoot, thead, or tr element"
        // "Let the pending table character tokens be an empty list of
        // tokens." "Set the original insertion mode to the current insertion
        // mode." "Switch the insertion mode to "in table text" and reprocess
        // the token."
        Outcome::Reprocess(Parser { pending_table_text: seq![], original_mode: p.mode, mode: Mode::InTableText, ..p }, t)
    } else if t is Comment {
        // 2. "A comment token"
        // "Insert a comment."
        Outcome::Done(insert_comment(p, t->Comment_0, None))
    } else if t is Pi {
        // 3. "A processing instruction token"
        // "Insert a processing instruction."
        Outcome::Done(insert_pi(p, t->Pi_0, t->Pi_1, None))
    } else if t is Doctype {
        // 4. "A DOCTYPE token"
        // "Parse error. Ignore the token."
        Outcome::Done(p)
    } else if t is Start && t->Start_0.tag == Tag::Caption {
        // 5. "A start tag whose tag name is "caption""
        // "Clear the stack back to a table context."
        let p1 = clear_stack_back_to_table_context(p);
        // "Insert a marker at the end of the list of active formatting
        // elements."
        let p2 = push_marker(p1);
        // "Insert an HTML element for the token, then switch the insertion
        // mode to "in caption"."
        let p3 = insert_html_element(p2, t->Start_0).0;
        Outcome::Done(Parser { mode: Mode::InCaption, ..p3 })
    } else if t is Start && t->Start_0.tag == Tag::Colgroup {
        // 6. "A start tag whose tag name is "colgroup""
        // "Clear the stack back to a table context."
        let p1 = clear_stack_back_to_table_context(p);
        // "Insert an HTML element for the token, then switch the insertion
        // mode to "in column group"."
        let p2 = insert_html_element(p1, t->Start_0).0;
        Outcome::Done(Parser { mode: Mode::InColumnGroup, ..p2 })
    } else if t is Start && t->Start_0.tag == Tag::Col {
        // 7. "A start tag whose tag name is "col""
        // "Clear the stack back to a table context."
        let p1 = clear_stack_back_to_table_context(p);
        // "Insert an HTML element for a "colgroup" start tag token with no
        // attributes, then switch the insertion mode to "in column group"."
        let p2 = insert_html_element(p1, start_tag_named(name_colgroup())).0;
        // "Reprocess the current token."
        Outcome::Reprocess(Parser { mode: Mode::InColumnGroup, ..p2 }, t)
    } else if t is Start && (t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead) {
        // 8. "A start tag whose tag name is one of: "tbody", "tfoot",
        // "thead""
        // "Clear the stack back to a table context."
        let p1 = clear_stack_back_to_table_context(p);
        // "Insert an HTML element for the token, then switch the insertion
        // mode to "in table body"."
        let p2 = insert_html_element(p1, t->Start_0).0;
        Outcome::Done(Parser { mode: Mode::InTableBody, ..p2 })
    } else if t is Start && (t->Start_0.tag == Tag::Td || t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Tr) {
        // 9. "A start tag whose tag name is one of: "td", "th", "tr""
        // "Clear the stack back to a table context."
        let p1 = clear_stack_back_to_table_context(p);
        // "Insert an HTML element for a "tbody" start tag token with no
        // attributes, then switch the insertion mode to "in table body"."
        let p2 = insert_html_element(p1, start_tag_named(name_tbody())).0;
        // "Reprocess the current token."
        Outcome::Reprocess(Parser { mode: Mode::InTableBody, ..p2 }, t)
    } else if t is Start && t->Start_0.tag == Tag::Table {
        // 10. "A start tag whose tag name is "table""
        // "Parse error."
        if !has_in_scope(p, Tag::Table, Scope::Table) {
            // "If the stack of open elements does not have a table element in
            // table scope, ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise:"
            // 1. "Pop elements from this stack until a table element has been
            // popped from the stack."
            let p1 = pop_until_popped(p, Tag::Table);
            // 2. "Reset the insertion mode appropriately."
            let p2 = reset_insertion_mode(p1);
            // 3. "Reprocess the token."
            Outcome::Reprocess(p2, t)
        }
    } else if t is End && t->End_0.tag == Tag::Table {
        // 11. "An end tag whose tag name is "table""
        if !has_in_scope(p, Tag::Table, Scope::Table) {
            // "If the stack of open elements does not have a table element in
            // table scope, this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise:"
            // 1. "Pop elements from this stack until a table element has been
            // popped from the stack."
            let p1 = pop_until_popped(p, Tag::Table);
            // 2. "Reset the insertion mode appropriately."
            Outcome::Done(reset_insertion_mode(p1))
        }
    } else if t is End && (t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Caption || t->End_0.tag == Tag::Col
        || t->End_0.tag == Tag::Colgroup || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Tbody || t->End_0.tag
        == Tag::Td || t->End_0.tag == Tag::Tfoot || t->End_0.tag == Tag::Th || t->End_0.tag == Tag::Thead
        || t->End_0.tag == Tag::Tr) {
        // 12. "An end tag whose tag name is one of: "body", "caption", "col",
        // "colgroup", "html", "tbody", "td", "tfoot", "th", "thead", "tr""
        // "Parse error. Ignore the token."
        Outcome::Done(p)
    } else if (t is Start && (t->Start_0.tag == Tag::Style || t->Start_0.tag == Tag::Script || t->Start_0.tag
        == Tag::Template)) || (t is End && t->End_0.tag == Tag::Template) {
        // 13. "A start tag whose tag name is one of: "style", "script",
        // "template"", "An end tag whose tag name is "template""
        // "Process the token using the rules for the "in head" insertion
        // mode."
        Outcome::Using(Mode::InHead, p, t)
    } else if t is Start && t->Start_0.tag == Tag::Input && in_table_input_is_hidden(t->Start_0) {
        // 14. "A start tag whose tag name is "input""
        // "If the token does not have an attribute with the name "type", or
        // if it does, but that attribute's value is not an ASCII
        // case-insensitive match for "hidden", then act as described in the
        // "anything else" entry below." (Those tokens fall through to case
        // 17.)
        // "Otherwise:"
        // 1. "Parse error."
        // 2. "Insert an HTML element for the token."
        let p1 = insert_html_element(p, t->Start_0).0;
        // 3. "Pop that input element off the stack of open elements." (It is
        // the current node; a stopped parser changes nothing.)
        let p2 = if p1.stopped {
            p1
        } else {
            pop(p1)
        };
        // 4. "Acknowledge the token's self-closing flag, if it is set."
        // (Nothing to model: it only decides a parse error.)
        Outcome::Done(p2)
    } else if t is Start && t->Start_0.tag == Tag::Form {
        // 15. "A start tag whose tag name is "form""
        // "Parse error."
        if p.form is Some && !parsing_template_contents(p) {
            // "If the form element pointer is not null, and the parser is not
            // parsing template contents, then ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise:"
            // 1. "Insert an HTML element for the token, and, if the parser is
            // not parsing template contents, set the form element pointer to
            // point to the element created." (A stopped parser changes
            // nothing.)
            let (p1, e) = insert_html_element(p, t->Start_0);
            let p2 = if !parsing_template_contents(p1) && !p1.stopped {
                Parser { form: Some(e.id), ..p1 }
            } else {
                p1
            };
            // 2. "Pop that form element off the stack of open elements." (It
            // is the current node.)
            let p3 = if p2.stopped {
                p2
            } else {
                pop(p2)
            };
            Outcome::Done(p3)
        }
    } else if t is Eof {
        // 16. "An end-of-file token"
        // "Process the token using the rules for the "in body" insertion
        // mode."
        Outcome::Using(Mode::InBody, p, t)
    } else {
        // 17. "Anything else"
        // "Parse error. Enable foster parenting, process the token using the
        // rules for the "in body" insertion mode, and then disable foster
        // parenting."
        in_table_anything_else(env, p, t)
    }
}

} // verus!
