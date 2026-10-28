//! The edges of the "initial", "before html", "before head", "in head", "in head noscript", "after head", "text" modes are ranked
//! (see [`super`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The edges of the "initial" mode are ranked.
pub proof fn lemma_initial_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::Initial), p),
    ensures
        edge_ok(Rules::Html(Mode::Initial), p, t, mode_initial(env, p, t)),
{
}

/// The edges of the "before html" mode are ranked.
pub proof fn lemma_before_html_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::BeforeHtml), p),
    ensures
        edge_ok(Rules::Html(Mode::BeforeHtml), p, t, mode_before_html(env, p, t)),
{
    let o = mode_before_html(env, p, t);
    if o is Reprocess {
        // "Anything else": create an `html` element, push it, switch to
        // "before head" and reprocess: G 3 to 2, L up by at most one.
        assert(o == before_html_anything_else(p, t));
        let tt = start_tag_named(seq![0x68u32, 0x74, 0x6d, 0x6c]);
        helpers_ranking::lemma_not_template(tt.name);
        helpers_ranking::lemma_create_element_for_token(p, tt, 0);
        let (p1, e) = create_element_for_token(p, tt, Namespace::Html, 0);
        helpers_ranking::lemma_insert_element_at(p1, e.id, Some(document_location()));
        let p2 = insert_element_at(p1, e.id, Some(document_location()));
        helpers_ranking::lemma_push_created(p, p2, e);
        let q = Parser { mode: Mode::BeforeHead, ..push(p2, e) };
        assert(o == Outcome::Reprocess(q, t));
        helpers_ranking::lemma_modes_ok_from(p, q);
    }
}

/// The edges of the "before head" mode are ranked.
pub proof fn lemma_before_head_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::BeforeHead), p),
    ensures
        edge_ok(Rules::Html(Mode::BeforeHead), p, t, mode_before_head(env, p, t)),
{
    let o = mode_before_head(env, p, t);
    if o is Reprocess {
        // "Anything else": insert a `head` element, switch to "in head" and
        // reprocess: G 2 to at most 1, L up by at most one.
        assert(o == before_head_anything_else(p, t));
        let tt = start_tag_named(seq![0x68u32, 0x65, 0x61, 0x64]);
        helpers_ranking::lemma_not_template(tt.name);
        helpers_ranking::lemma_insert_html_element(p, tt);
        let (p1, e) = insert_html_element(p, tt);
        let q = Parser { head: Some(e.id), mode: Mode::InHead, ..p1 };
        assert(o == Outcome::Reprocess(q, t));
        helpers_ranking::lemma_modes_ok_from(p, q);
    }
}

/// The edges of the "in head" mode are ranked.
pub proof fn lemma_in_head_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InHead), p),
    ensures
        edge_ok(Rules::Html(Mode::InHead), p, t, mode_in_head(env, p, t)),
{
    let o = mode_in_head(env, p, t);
    if headish(t) || t is Doctype || is_start(t, Tag::Html) {
        assert(o is Done || o == Outcome::Using(Mode::InBody, p, t));
    } else if o is Reprocess {
        // "Anything else": pop the current node, switch to "after head" and
        // reprocess (same growth, the stack shortens by one, or stays empty
        // with the order 11 to 10).
        assert(o == in_head_anything_else(p, t));
        helpers_ranking::lemma_pop(p);
        let q = Parser { mode: Mode::AfterHead, ..pop(p) };
        helpers_ranking::lemma_modes_ok_from(p, q);
    }
}

/// The edges of the "in head noscript" mode are ranked.
pub proof fn lemma_in_head_noscript_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InHeadNoscript), p),
    ensures
        edge_ok(Rules::Html(Mode::InHeadNoscript), p, t, mode_in_head_noscript(env, p, t)),
{
    let o = mode_in_head_noscript(env, p, t);
    if o is Reprocess {
        // "Anything else": pop the current node, switch to "in head" and
        // reprocess (growth no larger, the stack no longer, the order 21 to
        // 11).
        assert(o == in_head_noscript_anything_else(p, t));
        helpers_ranking::lemma_pop(p);
        let q = Parser { mode: Mode::InHead, ..pop(p) };
        helpers_ranking::lemma_modes_ok_from(p, q);
    }
}

/// The edges of the "after head" mode are ranked.
pub proof fn lemma_after_head_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::AfterHead), p),
    ensures
        edge_ok(Rules::Html(Mode::AfterHead), p, t, mode_after_head(env, p, t)),
{
    let o = mode_after_head(env, p, t);
    if t is Start && after_head_in_head_tag(t->Start_0.tag) {
        // The "in head" start tags: the "in head" rules handle them.
        if let Some(h) = p.head {
            helpers_early::lemma_in_head_start_done(env, push(p, head_elem(h)), t);
        }
        assert(o == after_head_using_in_head(env, p, t));
        assert(o is Done);
    } else if o is Reprocess {
        // "Anything else": insert a `body` element, switch to "in body" and
        // reprocess: G 1 to 0, L up by at most one.
        assert(o == after_head_anything_else(p, t));
        let tt = start_tag_named(seq![0x62u32, 0x6f, 0x64, 0x79]);
        helpers_ranking::lemma_not_template(tt.name);
        helpers_ranking::lemma_insert_html_element(p, tt);
        let p1 = insert_html_element(p, tt).0;
        let q = Parser { frameset_ok: true, mode: Mode::InBody, ..p1 };
        assert(o == Outcome::Reprocess(q, t));
        helpers_ranking::lemma_modes_ok_from(p, q);
    }
}

/// The edges of the "text" mode are ranked.
pub proof fn lemma_text_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::Text), p),
    ensures
        edge_ok(Rules::Html(Mode::Text), p, t, mode_text(env, p, t)),
{
    if t is Eof {
        // "An end-of-file token": pop the current node, switch to the
        // original insertion mode and reprocess: G 5 to at most 4 (the
        // original mode is neither "text" nor "in table text"), the stack
        // no longer, and the pending characters no longer counted.
        assert(p.mode == Mode::Text);
        helpers_tables::lemma_growth_le_4(p.original_mode, t);
        helpers_ranking::lemma_pop(p);
        let q = Parser { mode: p.original_mode, ..pop(p) };
        assert(mode_text(env, p, t) == Outcome::Reprocess(q, t));
        helpers_ranking::lemma_modes_ok_from(p, q);
    }
}

} // verus!
