//! The edges of the "in body" mode are ranked
//! (see [`super`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The edges of the "in body" mode are ranked.
pub proof fn lemma_in_body_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InBody), p),
    ensures
        edge_ok(Rules::Html(Mode::InBody), p, t, mode_in_body(env, p, t)),
{
    hide(in_body_start_tag);
    hide(in_body_end_tag);
    hide(in_body_eof);
    hide(in_body_char);
    hide(insert_comment);
    hide(insert_pi);
    let r = Rules::Html(Mode::InBody);
    assert(p.mode != Mode::Text && p.mode != Mode::InTableText);
    match t {
        Tok::Start(tt) => {
            helpers_in_body::lemma_in_body_start_tag_outcome(p, t, tt);
            assert(mode_in_body(env, p, t) == in_body_start_tag(p, t, tt));
            match in_body_start_tag(p, t, tt) {
                Outcome::Done(_) => {},
                Outcome::Using(m, q, t2) => {
                    // Case 8: an "in head" start tag, which "in head" handles.
                    assert(headish(t));
                    assert(img(t) == 0);
                    assert(decreases_to(r, p, t, Rules::Html(m), q, t2));
                },
                Outcome::Reprocess(q, t2) => {
                    // Case 41: `image` becomes `img`; `img` drops from 1 to 0
                    // and pays for any growth of the next rules.
                    assert(img(t) == 1);
                    assert(img(t2) == 0) by {
                        assert(t2 == helpers_in_body::image_as_img(tt));
                    }
                    lemma_components_bounded(Rules::Html(q.mode), t2);
                    assert(decreases_to(r, p, t, Rules::Html(q.mode), q, t2));
                },
            }
        },
        Tok::End(tt) => {
            helpers_in_body::lemma_in_body_end_tag_outcome(p, t, tt);
            assert(mode_in_body(env, p, t) == in_body_end_tag(p, t, tt));
            match in_body_end_tag(p, t, tt) {
                Outcome::Done(_) => {},
                Outcome::Using(m, q, t2) => {
                    // Case 8: the `template` end tag, which "in head" handles.
                    assert(headish(t));
                    assert(img(t) == 0);
                    assert(decreases_to(r, p, t, Rules::Html(m), q, t2));
                },
                Outcome::Reprocess(q, t2) => {
                    // Case 13: the `html` end tag, reprocessed in "after body".
                    assert(is_end(t2, Tag::Html));
                    assert(img(t) == 0);
                    assert(decreases_to(r, p, t, Rules::Html(q.mode), q, t2));
                    assert(modes_ok(q)) by {
                        assert(q.template_modes == p.template_modes);
                    }
                },
            }
        },
        Tok::Eof => {
            helpers_in_body::lemma_in_body_eof_outcome(p, t);
            assert(mode_in_body(env, p, t) == in_body_eof(p, t));
            match in_body_eof(p, t) {
                Outcome::Done(_) => {},
                Outcome::Using(m, q, t2) => {
                    // Case 11 with template modes: "in template"'s EOF has
                    // order 1.
                    assert(img(t) == 0);
                    assert(decreases_to(r, p, t, Rules::Html(m), q, t2));
                },
                Outcome::Reprocess(_, _) => {},
            }
        },
        _ => {
            assert(mode_in_body(env, p, t) is Done);
        },
    }
}

} // verus!
