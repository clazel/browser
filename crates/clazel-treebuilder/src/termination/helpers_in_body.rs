//! Characterisations of the "in body" mode's outcomes, for
//! [`super::in_body`]: every case is `Done` except the "in head" start tags
//! and the `template` end tag (using the "in head" rules), the end-of-file
//! token with template modes (using the "in template" rules), the `html` end
//! tag (reprocessed in "after body") and the `image` start tag (reprocessed
//! as `img`), each with the parser otherwise unchanged.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The `image` start tag reprocessed as `img`.
pub open spec fn image_as_img(tt: TagTok) -> Tok {
    Tok::Start(TagTok { name: name_img(), tag: Tag::Img, ..tt })
}

/// The start tag cases are `Done` except case 8 (using the "in head" rules)
/// and case 41 (`image` reprocessed as `img`).
#[verifier::spinoff_prover]
pub proof fn lemma_in_body_start_tag_outcome(p: Parser, t: Tok, tt: TagTok)
    ensures
        match in_body_start_tag(p, t, tt) {
            Outcome::Done(_) => true,
            Outcome::Using(m, q, t2) => m == Mode::InHead && q == p && t2 == t && is_in_head_start_tag(tt.tag),
            Outcome::Reprocess(q, t2) => q == p && tt.tag == Tag::Image && t2 == image_as_img(tt),
        },
{
    hide(in_body_start_html);
    hide(in_body_start_body);
    hide(in_body_start_frameset);
    hide(insert_html_element);
    hide(close_p_if_in_button_scope);
    hide(in_body_start_heading);
    hide(in_body_start_pre);
    hide(in_body_start_form);
    hide(in_body_start_li);
    hide(in_body_start_dd_dt);
    hide(in_body_start_button);
    hide(in_body_start_a);
    hide(reconstruct_formatting);
    hide(push_formatting);
    hide(in_body_start_nobr);
    hide(push_marker);
    hide(frameset_not_ok);
    hide(doc_is_quirks);
    hide(has_in_scope);
    hide(close_p_element);
    hide(in_body_void_start_tag);
    hide(in_body_start_input);
    hide(insert_and_pop);
    hide(in_body_start_hr);
    hide(in_body_start_textarea);
    hide(generic_text_parsing);
    hide(in_body_start_select);
    hide(in_body_start_option);
    hide(in_body_start_optgroup);
    hide(generate_implied_end_tags);
    hide(in_body_start_math);
    hide(in_body_start_svg);
}

/// The end tag cases are `Done` except case 8 (`template`, using the "in
/// head" rules) and case 13 (`html`, reprocessed in "after body").
pub proof fn lemma_in_body_end_tag_outcome(p: Parser, t: Tok, tt: TagTok)
    ensures
        match in_body_end_tag(p, t, tt) {
            Outcome::Done(_) => true,
            Outcome::Using(m, q, t2) => m == Mode::InHead && q == p && t2 == t && tt.tag == Tag::Template,
            Outcome::Reprocess(q, t2) => q == Parser { mode: Mode::AfterBody, ..p } && t2 == t && tt.tag == Tag::Html,
        },
{
}

/// Case 11 is `Done` or uses the "in template" rules with template modes.
pub proof fn lemma_in_body_eof_outcome(p: Parser, t: Tok)
    ensures
        match in_body_eof(p, t) {
            Outcome::Done(_) => true,
            Outcome::Using(m, q, t2) => m == Mode::InTemplate && q == p && t2 == t && p.template_modes.len() > 0,
            Outcome::Reprocess(_, _) => false,
        },
{
}

} // verus!
