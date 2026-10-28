//! HTML §13.2.6.4.14 the "in row" insertion mode, and "clear the stack back
//! to a table row context".

#[allow(unused_imports)]
use super::super::dispatch::*;
#[allow(unused_imports)]
use super::super::insert::*;
#[allow(unused_imports)]
use super::super::state::*;
#[allow(unused_imports)]
use super::super::tags::*;
#[allow(unused_imports)]
use super::in_table_body::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "clear the stack back to a table row context": "while the current node is
/// not a tr, template, or html element, pop elements from the stack of open
/// elements."
pub open spec fn clear_stack_back_to_table_row_context(p: Parser) -> Parser {
    pop_while(p, |e: Elem| !(is_html(e, Tag::Tr) || is_html(e, Tag::Template) || is_html(e, Tag::Html)))
}

/// §13.2.6.4.14 the "in row" insertion mode.
/// <https://html.spec.whatwg.org/multipage/parsing.html#parsing-main-intr>
pub open spec fn mode_in_row(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is Start && (t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Td) {
        // 1. "A start tag whose tag name is one of: "th", "td""
        // "Clear the stack back to a table row context."
        let p1 = clear_stack_back_to_table_row_context(p);
        // "Insert an HTML element for the token, then switch the insertion
        // mode to "in cell"."
        let p2 = insert_html_element(p1, t->Start_0).0;
        let p3 = Parser { mode: Mode::InCell, ..p2 };
        // "Insert a marker at the end of the list of active formatting
        // elements."
        Outcome::Done(push_marker(p3))
    } else if t is End && t->End_0.tag == Tag::Tr {
        // 2. "An end tag whose tag name is "tr""
        if !has_in_scope(p, Tag::Tr, Scope::Table) {
            // "If the stack of open elements does not have a tr element in
            // table scope, this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise:"
            // 1. "Clear the stack back to a table row context."
            let p1 = clear_stack_back_to_table_row_context(p);
            // 2. "Pop the current node (which will be a tr element) from the
            // stack of open elements. Switch the insertion mode to "in table
            // body"."
            Outcome::Done(Parser { mode: Mode::InTableBody, ..pop(p1) })
        }
    } else if (t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Col || t->Start_0.tag == Tag::Colgroup
        || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead || t->Start_0.tag
        == Tag::Tr)) || (t is End && t->End_0.tag == Tag::Table) {
        // 3. "A start tag whose tag name is one of: "caption", "col",
        // "colgroup", "tbody", "tfoot", "thead", "tr"", "An end tag whose tag
        // name is "table""
        if !has_in_scope(p, Tag::Tr, Scope::Table) {
            // "If the stack of open elements does not have a tr element in
            // table scope, this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise:"
            // 1. "Clear the stack back to a table row context."
            let p1 = clear_stack_back_to_table_row_context(p);
            // 2. "Pop the current node (which will be a tr element) from the
            // stack of open elements. Switch the insertion mode to "in table
            // body"."
            // 3. "Reprocess the token."
            Outcome::Reprocess(Parser { mode: Mode::InTableBody, ..pop(p1) }, t)
        }
    } else if t is End && (t->End_0.tag == Tag::Tbody || t->End_0.tag == Tag::Tfoot || t->End_0.tag == Tag::Thead) {
        // 4. "An end tag whose tag name is one of: "tbody", "tfoot", "thead""
        if !has_same_name_in_table_scope(p, t->End_0) {
            // "If the stack of open elements does not have an element in table
            // scope that is an HTML element with the same tag name as the
            // token, this is a parse error; ignore the token."
            Outcome::Done(p)
        } else if !has_in_scope(p, Tag::Tr, Scope::Table) {
            // "If the stack of open elements does not have a tr element in
            // table scope, ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise:"
            // 1. "Clear the stack back to a table row context."
            let p1 = clear_stack_back_to_table_row_context(p);
            // 2. "Pop the current node (which will be a tr element) from the
            // stack of open elements. Switch the insertion mode to "in table
            // body"."
            // 3. "Reprocess the token."
            Outcome::Reprocess(Parser { mode: Mode::InTableBody, ..pop(p1) }, t)
        }
    } else if t is End && (t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Caption || t->End_0.tag == Tag::Col
        || t->End_0.tag == Tag::Colgroup || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Td || t->End_0.tag
        == Tag::Th) {
        // 5. "An end tag whose tag name is one of: "body", "caption", "col",
        // "colgroup", "html", "td", "th""
        // "Parse error. Ignore the token."
        Outcome::Done(p)
    } else {
        // 6. "Anything else"
        // "Process the token using the rules for the "in table" insertion
        // mode."
        Outcome::Using(Mode::InTable, p, t)
    }
}

} // verus!
