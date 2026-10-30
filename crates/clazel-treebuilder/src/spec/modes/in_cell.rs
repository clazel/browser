//! HTML §13.2.6.4.15 the "in cell" insertion mode, and "close the cell".

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "Pop elements from the stack of open elements until a td element or a th
/// element has been popped from the stack." (Pops everything if there is
/// none; "close the cell" is only invoked with one in table scope.)
pub open spec fn pop_until_cell_popped(p: Parser) -> Parser
    decreases p.open.len(),
{
    if p.open.len() == 0 {
        p
    } else if is_html(current_node(p), Tag::Td) || is_html(current_node(p), Tag::Th) {
        pop(p)
    } else {
        pop_until_cell_popped(pop(p))
    }
}

/// "close the cell".
/// <https://html.spec.whatwg.org/multipage/parsing.html#close-the-cell>
pub open spec fn close_the_cell(p: Parser) -> Parser {
    // 1. "Generate implied end tags."
    let p1 = generate_implied_end_tags(p, None);
    // 2. "If the current node is not now a td element or a th element, then
    // this is a parse error."
    // 3. "Pop elements from the stack of open elements until a td element or a
    // th element has been popped from the stack."
    let p2 = pop_until_cell_popped(p1);
    // 4. "Clear the list of active formatting elements up to the last
    // marker."
    let p3 = clear_to_last_marker(p2);
    // 5. "Switch the insertion mode to "in row"."
    Parser { mode: Mode::InRow, ..p3 }
}

/// §13.2.6.4.15 the "in cell" insertion mode.
/// <https://html.spec.whatwg.org/multipage/parsing.html#parsing-main-intd>
pub open spec fn mode_in_cell(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is End && (t->End_0.tag == Tag::Td || t->End_0.tag == Tag::Th) {
        // 1. "An end tag whose tag name is one of: "td", "th""
        if !has_same_name_in_table_scope(p, t->End_0) {
            // "If the stack of open elements does not have an element in table
            // scope that is an HTML element with the same tag name as that of
            // the token, then this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise:"
            // 1. "Generate implied end tags."
            let p1 = generate_implied_end_tags(p, None);
            // 2. "Now, if the current node is not an HTML element with the same
            // tag name as the token, then this is a parse error."
            // 3. "Pop elements from the stack of open elements until an HTML
            // element with the same tag name as the token has been popped from
            // the stack." (The token's name is "td" or "th", so its `Tag`
            // names it.)
            let p2 = pop_until_popped(p1, t->End_0.tag);
            // 4. "Clear the list of active formatting elements up to the last
            // marker."
            let p3 = clear_to_last_marker(p2);
            // 5. "Switch the insertion mode to "in row"."
            Outcome::Done(Parser { mode: Mode::InRow, ..p3 })
        }
    } else if t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Col || t->Start_0.tag == Tag::Colgroup
        || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Td || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag
        == Tag::Th || t->Start_0.tag == Tag::Thead || t->Start_0.tag == Tag::Tr) {
        // 2. "A start tag whose tag name is one of: "caption", "col",
        // "colgroup", "tbody", "td", "tfoot", "th", "thead", "tr""
        // "Assert: the stack of open elements has a td or th element in table
        // scope." (An assertion of the standard; nothing to model.)
        // "Close the cell (see below) and reprocess the token."
        Outcome::Reprocess(close_the_cell(p), t)
    } else if t is End && (t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Caption || t->End_0.tag == Tag::Col
        || t->End_0.tag == Tag::Colgroup || t->End_0.tag == Tag::Html) {
        // 3. "An end tag whose tag name is one of: "body", "caption", "col",
        // "colgroup", "html""
        // "Parse error. Ignore the token."
        Outcome::Done(p)
    } else if t is End && (t->End_0.tag == Tag::Table || t->End_0.tag == Tag::Tbody || t->End_0.tag == Tag::Tfoot
        || t->End_0.tag == Tag::Thead || t->End_0.tag == Tag::Tr) {
        // 4. "An end tag whose tag name is one of: "table", "tbody", "tfoot",
        // "thead", "tr""
        if !has_same_name_in_table_scope(p, t->End_0) {
            // "If the stack of open elements does not have an element in table
            // scope that is an HTML element with the same tag name as that of
            // the token, then this is a parse error; ignore the token."
            Outcome::Done(p)
        } else {
            // "Otherwise, close the cell (see below) and reprocess the
            // token."
            Outcome::Reprocess(close_the_cell(p), t)
        }
    } else {
        // 5. "Anything else"
        // "Process the token using the rules for the "in body" insertion
        // mode."
        Outcome::Using(Mode::InBody, p, t)
    }
}

} // verus!
