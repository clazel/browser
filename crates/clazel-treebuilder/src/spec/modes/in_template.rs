//! HTML §13.2.6.4.16 the "in template" insertion mode.

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

/// "Pop the current template insertion mode off the stack of template
/// insertion modes. Push `m` onto the stack of template insertion modes so
/// that it is the new current template insertion mode. Switch the insertion
/// mode to `m`, and reprocess the token." (Cases 3 to 7 of the "in template"
/// insertion mode.)
pub open spec fn in_template_switch(p: Parser, t: Tok, m: Mode) -> Outcome {
    Outcome::Reprocess(Parser { template_modes: p.template_modes.drop_last().push(m), mode: m, ..p }, t)
}

/// §13.2.6.4.16 the "in template" insertion mode.
/// <https://html.spec.whatwg.org/multipage/parsing.html#parsing-main-intemplate>
pub open spec fn mode_in_template(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is Char || t is Comment || t is Pi || t is Doctype {
        // 1. "A character token", "A comment token", "A processing
        // instruction token", "A DOCTYPE token"
        // "Process the token using the rules for the "in body" insertion
        // mode."
        Outcome::Using(Mode::InBody, p, t)
    } else if (t is Start && (t->Start_0.tag == Tag::Base || t->Start_0.tag == Tag::Basefont || t->Start_0.tag
        == Tag::Bgsound || t->Start_0.tag == Tag::Link || t->Start_0.tag == Tag::Meta || t->Start_0.tag == Tag::Noframes
        || t->Start_0.tag == Tag::Script || t->Start_0.tag == Tag::Style || t->Start_0.tag == Tag::Template
        || t->Start_0.tag == Tag::Title)) || (t is End && t->End_0.tag == Tag::Template) {
        // 2. "A start tag whose tag name is one of: "base", "basefont",
        // "bgsound", "link", "meta", "noframes", "script", "style",
        // "template", "title"", "An end tag whose tag name is "template""
        // "Process the token using the rules for the "in head" insertion
        // mode."
        Outcome::Using(Mode::InHead, p, t)
    } else if t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Colgroup || t->Start_0.tag
        == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead) {
        // 3. "A start tag whose tag name is one of: "caption", "colgroup",
        // "tbody", "tfoot", "thead""
        // "Pop the current template insertion mode off the stack of template
        // insertion modes." "Push "in table" onto the stack of template
        // insertion modes so that it is the new current template insertion
        // mode." "Switch the insertion mode to "in table", and reprocess the
        // token."
        in_template_switch(p, t, Mode::InTable)
    } else if t is Start && t->Start_0.tag == Tag::Col {
        // 4. "A start tag whose tag name is "col""
        // "Pop the current template insertion mode …" "Push "in column
        // group" …" "Switch the insertion mode to "in column group", and
        // reprocess the token."
        in_template_switch(p, t, Mode::InColumnGroup)
    } else if t is Start && t->Start_0.tag == Tag::Tr {
        // 5. "A start tag whose tag name is "tr""
        // "Pop the current template insertion mode …" "Push "in table body"
        // …" "Switch the insertion mode to "in table body", and reprocess the
        // token."
        in_template_switch(p, t, Mode::InTableBody)
    } else if t is Start && (t->Start_0.tag == Tag::Td || t->Start_0.tag == Tag::Th) {
        // 6. "A start tag whose tag name is one of: "td", "th""
        // "Pop the current template insertion mode …" "Push "in row" …"
        // "Switch the insertion mode to "in row", and reprocess the token."
        in_template_switch(p, t, Mode::InRow)
    } else if t is Start {
        // 7. "Any other start tag"
        // "Pop the current template insertion mode …" "Push "in body" …"
        // "Switch the insertion mode to "in body", and reprocess the token."
        in_template_switch(p, t, Mode::InBody)
    } else if t is End {
        // 8. "Any other end tag"
        // "Parse error. Ignore the token."
        Outcome::Done(p)
    } else {
        // 9. "An end-of-file token" (the only token kind left)
        if !open_has_html(p, Tag::Template) {
            // "If there is no template element on the stack of open elements,
            // then stop parsing. (fragment case)"
            Outcome::Done(stop_parsing(p))
        } else {
            // "Otherwise, this is a parse error."
            // "Pop elements from the stack of open elements until a template
            // element has been popped from the stack."
            let p1 = pop_until_popped(p, Tag::Template);
            // "Clear the list of active formatting elements up to the last
            // marker."
            let p2 = clear_to_last_marker(p1);
            // "Pop the current template insertion mode off the stack of
            // template insertion modes."
            let p3 = Parser { template_modes: p2.template_modes.drop_last(), ..p2 };
            // "Reset the insertion mode appropriately."
            let p4 = reset_insertion_mode(p3);
            // "Reprocess the token."
            Outcome::Reprocess(p4, t)
        }
    }
}

} // verus!
