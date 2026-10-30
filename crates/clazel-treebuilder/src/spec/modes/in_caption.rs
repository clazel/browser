//! HTML §13.2.6.4.11 the "in caption" insertion mode.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §13.2.6.4.11 the "in caption" insertion mode.
/// <https://html.spec.whatwg.org/multipage/parsing.html#parsing-main-incaption>
pub open spec fn mode_in_caption(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is End && t->End_0.tag == Tag::Caption {
        // 1. "An end tag whose tag name is "caption""
        if !has_in_scope(p, Tag::Caption, Scope::Table) {
            // "If the stack of open elements does not have a caption element
            // in table scope, this is a parse error; ignore the token.
            // (fragment case)"
            Outcome::Done(p)
        } else {
            // "Otherwise:"
            // 1. "Generate implied end tags."
            let p1 = generate_implied_end_tags(p, None);
            // 2. "Now, if the current node is not a caption element, then this
            // is a parse error."
            // 3. "Pop elements from this stack until a caption element has
            // been popped from the stack."
            let p2 = pop_until_popped(p1, Tag::Caption);
            // 4. "Clear the list of active formatting elements up to the last
            // marker."
            let p3 = clear_to_last_marker(p2);
            // 5. "Switch the insertion mode to "in table"."
            Outcome::Done(Parser { mode: Mode::InTable, ..p3 })
        }
    } else if (t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Col || t->Start_0.tag == Tag::Colgroup
        || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Td || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag
        == Tag::Th || t->Start_0.tag == Tag::Thead || t->Start_0.tag == Tag::Tr)) || (t is End && t->End_0.tag
        == Tag::Table) {
        // 2. "A start tag whose tag name is one of: "caption", "col",
        // "colgroup", "tbody", "td", "tfoot", "th", "thead", "tr"", "An end tag
        // whose tag name is "table""
        if !has_in_scope(p, Tag::Caption, Scope::Table) {
            // "If the stack of open elements does not have a caption element
            // in table scope, this is a parse error; ignore the token.
            // (fragment case)"
            Outcome::Done(p)
        } else {
            // "Otherwise:"
            // 1. "Generate implied end tags."
            let p1 = generate_implied_end_tags(p, None);
            // 2. "Now, if the current node is not a caption element, then this
            // is a parse error."
            // 3. "Pop elements from this stack until a caption element has
            // been popped from the stack."
            let p2 = pop_until_popped(p1, Tag::Caption);
            // 4. "Clear the list of active formatting elements up to the last
            // marker."
            let p3 = clear_to_last_marker(p2);
            // 5. "Switch the insertion mode to "in table"."
            // 6. "Reprocess the token."
            Outcome::Reprocess(Parser { mode: Mode::InTable, ..p3 }, t)
        }
    } else if t is End && (t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Col || t->End_0.tag == Tag::Colgroup
        || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Tbody || t->End_0.tag == Tag::Td || t->End_0.tag
        == Tag::Tfoot || t->End_0.tag == Tag::Th || t->End_0.tag == Tag::Thead || t->End_0.tag == Tag::Tr) {
        // 3. "An end tag whose tag name is one of: "body", "col", "colgroup",
        // "html", "tbody", "td", "tfoot", "th", "thead", "tr""
        // "Parse error. Ignore the token."
        Outcome::Done(p)
    } else {
        // 4. "Anything else"
        // "Process the token using the rules for the "in body" insertion
        // mode."
        Outcome::Using(Mode::InBody, p, t)
    }
}

} // verus!
