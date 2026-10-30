//! HTML §13.2.6.4.13 the "in table body" insertion mode, and "clear the
//! stack back to a table body context".

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "clear the stack back to a table body context": "while the current node
/// is not a tbody, tfoot, thead, template, or html element, pop elements from
/// the stack of open elements."
pub open spec fn clear_stack_back_to_table_body_context(p: Parser) -> Parser {
    pop_while(
        p,
        |e: Elem|
            !(is_html(e, Tag::Tbody) || is_html(e, Tag::Tfoot) || is_html(e, Tag::Thead) || is_html(e, Tag::Template)
                || is_html(e, Tag::Html)),
    )
}

/// "The stack of open elements has an element in table scope that is an
/// HTML element with the same tag name as the token".
pub open spec fn has_same_name_in_table_scope(p: Parser, tt: TagTok) -> bool {
    in_scope_from(p.open, p.open.len() as int, |e: Elem| e.ns == clazel_dom::spec::Namespace::Html && e.name == tt.name, Scope::Table)
}

/// "The stack of open elements has a tbody, thead, or tfoot element in table
/// scope".
pub open spec fn has_table_section_in_table_scope(p: Parser) -> bool {
    in_scope_from(
        p.open,
        p.open.len() as int,
        |e: Elem| is_html(e, Tag::Tbody) || is_html(e, Tag::Thead) || is_html(e, Tag::Tfoot),
        Scope::Table,
    )
}

/// "tr"
pub open spec fn name_tr() -> Seq<u32> {
    seq![0x74u32, 0x72]
}

/// §13.2.6.4.13 the "in table body" insertion mode.
/// <https://html.spec.whatwg.org/multipage/parsing.html#parsing-main-intbody>
pub open spec fn mode_in_table_body(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is Start && t->Start_0.tag == Tag::Tr {
        // 1. "A start tag whose tag name is "tr""
        // "Clear the stack back to a table body context."
        let p1 = clear_stack_back_to_table_body_context(p);
        // "Insert an HTML element for the token, then switch the insertion
        // mode to "in row"."
        let p2 = insert_html_element(p1, t->Start_0).0;
        Outcome::Done(Parser { mode: Mode::InRow, ..p2 })
    } else if t is Start && (t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Td) {
        // 2. "A start tag whose tag name is one of: "th", "td""
        // "Parse error."
        // "Clear the stack back to a table body context."
        let p1 = clear_stack_back_to_table_body_context(p);
        // "Insert an HTML element for a "tr" start tag token with no
        // attributes, then switch the insertion mode to "in row"."
        let p2 = insert_html_element(p1, start_tag_named(name_tr())).0;
        // "Reprocess the current token."
        Outcome::Reprocess(Parser { mode: Mode::InRow, ..p2 }, t)
    } else if t is End && (t->End_0.tag == Tag::Tbody || t->End_0.tag == Tag::Tfoot || t->End_0.tag == Tag::Thead) {
        // 3. "An end tag whose tag name is one of: "tbody", "tfoot", "thead""
        if !has_same_name_in_table_scope(p, t->End_0) {
            // "If the stack of open elements does not have an element in table
            // scope that is an HTML element with the same tag name as the
            // token, this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise:"
            // 1. "Clear the stack back to a table body context."
            let p1 = clear_stack_back_to_table_body_context(p);
            // 2. "Pop the current node from the stack of open elements. Switch
            // the insertion mode to "in table"."
            Outcome::Done(Parser { mode: Mode::InTable, ..pop(p1) })
        }
    } else if (t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Col || t->Start_0.tag == Tag::Colgroup
        || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead)) || (t is End
        && t->End_0.tag == Tag::Table) {
        // 4. "A start tag whose tag name is one of: "caption", "col",
        // "colgroup", "tbody", "tfoot", "thead"", "An end tag whose tag name
        // is "table""
        if !has_table_section_in_table_scope(p) {
            // "If the stack of open elements does not have a tbody, thead, or
            // tfoot element in table scope, this is a parse error; ignore the
            // token."
            Outcome::Done(p)
        } else {
            // "Otherwise:"
            // 1. "Clear the stack back to a table body context."
            let p1 = clear_stack_back_to_table_body_context(p);
            // 2. "Pop the current node from the stack of open elements. Switch
            // the insertion mode to "in table"."
            // 3. "Reprocess the token."
            Outcome::Reprocess(Parser { mode: Mode::InTable, ..pop(p1) }, t)
        }
    } else if t is End && (t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Caption || t->End_0.tag == Tag::Col
        || t->End_0.tag == Tag::Colgroup || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Td || t->End_0.tag
        == Tag::Th || t->End_0.tag == Tag::Tr) {
        // 5. "An end tag whose tag name is one of: "body", "caption", "col",
        // "colgroup", "html", "td", "th", "tr""
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
