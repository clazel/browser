//! W3C HTML 5.2 §8.2.5.4.18: the "in template" insertion mode. Source and
//! modelling choices: [`super`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "Pop the current template insertion mode off the stack of template
/// insertion modes. Push `m` onto the stack of template insertion modes so
/// that it is the new current template insertion mode. Switch the insertion
/// mode to `m`, and reprocess the token."
pub open spec fn w3c_template_switch(p: Parser, m: Mode, t: Tok) -> Outcome {
    Outcome::Reprocess(Parser { template_modes: p.template_modes.drop_last().push(m), mode: m, ..p }, t)
}

/// W3C HTML 5.2 §8.2.5.4.18 the "in template" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#the-in-template-insertion-mode>).
pub open spec fn w3c_mode_in_template(env: EncFns, p: Parser, t: Tok) -> Outcome {
    let tag = w3c_tag(t);
    if t is Char || t is Comment || t is Doctype {
        // "A character token", "A comment token", "A DOCTYPE token": "Process
        // the token using the rules for the "in body" insertion mode."
        Outcome::Using(Mode::InBody, p, t)
    } else if (t is Start && (tag == Tag::Base || tag == Tag::Basefont || tag == Tag::Bgsound || tag == Tag::Link || tag
        == Tag::Meta || tag == Tag::Noframes || tag == Tag::Script || tag == Tag::Style || tag == Tag::Template || tag
        == Tag::Title)) || w3c_end(t, Tag::Template) {
        // "A start tag whose tag name is one of: "base", "basefont",
        // "bgsound", "link", "meta", "noframes", "script", "style",
        // "template", "title"", "An end tag whose tag name is "template"":
        // "Process the token using the rules for the "in head" insertion
        // mode."
        Outcome::Using(Mode::InHead, p, t)
    } else if t is Start && (tag == Tag::Caption || tag == Tag::Colgroup || tag == Tag::Tbody || tag == Tag::Tfoot || tag
        == Tag::Thead) {
        // "A start tag whose tag name is one of: "caption", "colgroup",
        // "tbody", "tfoot", "thead"": … "in table" …
        w3c_template_switch(p, Mode::InTable, t)
    } else if w3c_start(t, Tag::Col) {
        // "A start tag whose tag name is "col"": … "in column group" …
        w3c_template_switch(p, Mode::InColumnGroup, t)
    } else if w3c_start(t, Tag::Tr) {
        // "A start tag whose tag name is "tr"": … "in table body" …
        w3c_template_switch(p, Mode::InTableBody, t)
    } else if w3c_start(t, Tag::Td) || w3c_start(t, Tag::Th) {
        // "A start tag whose tag name is one of: "td", "th"": … "in row" …
        w3c_template_switch(p, Mode::InRow, t)
    } else if t is Start {
        // "Any other start tag": … "in body" …
        w3c_template_switch(p, Mode::InBody, t)
    } else if t is End {
        // "Any other end tag": "Parse error."
        Outcome::Done(p)
    } else {
        // "An end-of-file token":
        if !open_has_html(p, Tag::Template) {
            // "If there is no template element on the stack of open elements,
            // then stop parsing. (fragment case)"
            Outcome::Done(stop_parsing(p))
        } else {
            // "Otherwise, this is a parse error. Pop elements from the stack of
            // open elements until a template element has been popped from the
            // stack. Clear the list of active formatting elements up to the
            // last marker. Pop the current template insertion mode off the
            // stack of template insertion modes. Reset the insertion mode
            // appropriately. Reprocess the token."
            let q = clear_to_last_marker(pop_until_popped(p, Tag::Template));
            Outcome::Reprocess(reset_insertion_mode(Parser { template_modes: q.template_modes.drop_last(), ..q }), t)
        }
    }
}

} // verus!
