//! `theorem_dispatch_total` (Phase 4 item 4.9): reprocessing a token always
//! ends, within `fuel_bound(parser)` rule applications.
//!
//! The ranking. Each rule application is a triple (rules, parser, token);
//! "reprocess the token" and "using the rules for" lead from one to the
//! next. Its rank is the lexicographic tuple
//!
//! 1. `img`: 1 for an `image` start tag (in body turns it into `img`), else 0;
//! 2. `T`: the length of the stack of template insertion modes;
//! 3. `G`: a growth budget, [`growth`]: how many more elements the token can
//!    still push before it is handled (the implicit `html`, `head` and `body`
//!    elements, and the implicit `colgroup`, `tbody` and `tr` of tables);
//! 4. `L`: the length of the stack of open elements;
//! 5. `h`: the order of the rules for the token, [`order`].
//!
//! Every edge decreases the rank (the per-mode lemmas in the submodules),
//! and `B = L + G + 5T + 5 img` never increases, so `L` stays below the
//! starting `B`; with each component bounded, the rank is a number below
//! `fuel_bound`, which decreases on every edge ([`lemma_run_some`]).
//!
//! Two facts about the parser's modes are needed, [`modes_ok`]: the stack of
//! template insertion modes holds only the modes the parser pushes onto it
//! (so "reset the insertion mode appropriately" lands on a mode whose budget
//! is known), and in the "in table text" mode the original insertion mode
//! is neither "text" nor "in table text" (else "in table text"'s anything
//! else would reprocess in itself forever), and likewise in the "text" mode. They are part of the reachable
//! state invariant; within one token they are kept by every edge.

#[allow(unused_imports)]
use crate::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

pub mod early;
pub mod frameset;
pub mod helpers_early;
pub mod in_body;
pub mod tables;

/// Every name of the transcription and of this module, for the ghost
/// imports of the submodules (`use super::spec::*;`).
mod spec {
    #[cfg(verus_only)]
    pub use super::*;
    #[cfg(verus_only)]
    pub use crate::spec::*;
}

verus! {

// ---------------------------------------------------------------------
// Token classes

/// The token is a start tag named `tag`.
pub open spec fn is_start(t: Tok, tag: Tag) -> bool {
    t is Start && t->Start_0.tag == tag
}

/// The token is an end tag named `tag`.
pub open spec fn is_end(t: Tok, tag: Tag) -> bool {
    t is End && t->End_0.tag == tag
}

/// The tokens the "in head" rules handle themselves, which other modes
/// send to them ("using the rules for the in head insertion mode").
pub open spec fn headish(t: Tok) -> bool {
    (t is Char && is_ascii_whitespace(t->Char_0)) || t is Comment || t is Pi || is_end(t, Tag::Template) || (t is Start && match t->Start_0.tag {
        Tag::Base | Tag::Basefont | Tag::Bgsound | Tag::Link | Tag::Meta | Tag::Noframes | Tag::Script | Tag::Style | Tag::Template
        | Tag::Title => true,
        _ => false,
    })
}

/// 1 for an `image` start tag.
pub open spec fn img(t: Tok) -> nat {
    if is_start(t, Tag::Image) {
        1
    } else {
        0
    }
}

// ---------------------------------------------------------------------
// The ranking

/// The largest growth budget.
pub open spec fn growth_max() -> nat {
    5
}

/// The largest order.
pub open spec fn order_max() -> nat {
    30
}

/// The growth budget of the table modes (see [`growth`]).
pub open spec fn table_growth(m: Mode, t: Tok) -> nat {
    if is_start(t, Tag::Td) || is_start(t, Tag::Th) {
        match m {
            Mode::InTable | Mode::InCaption | Mode::InColumnGroup => 4,
            Mode::InTableBody => 3,
            _ => 2,
        }
    } else if is_start(t, Tag::Tr) {
        if m == Mode::InTableBody {
            0
        } else {
            1
        }
    } else if is_start(t, Tag::Col) {
        if m == Mode::InColumnGroup {
            0
        } else {
            1
        }
    } else if is_start(t, Tag::Table) {
        2
    } else {
        0
    }
}

/// The growth budget `G` of a rule application: an upper bound on the
/// elements the token can still push onto the stack of open elements by
/// reprocessing before it is handled, in the modes that push one and
/// reprocess (before html, before head, after head; in table for `col`,
/// `td`, `th`, `tr`; in table body for `td`, `th`).
pub open spec fn growth(r: Rules, t: Tok) -> nat {
    match r {
        Rules::Foreign => growth_max(),
        Rules::Html(m) => match m {
            Mode::Text => growth_max(),
            Mode::InTableText => if t is Char {
                0
            } else {
                growth_max()
            },
            Mode::Initial | Mode::BeforeHtml => 3,
            Mode::BeforeHead => 2,
            Mode::InHead => if headish(t) {
                0
            } else {
                1
            },
            Mode::InHeadNoscript | Mode::AfterHead => 1,
            Mode::InTable | Mode::InTableBody | Mode::InRow | Mode::InCaption | Mode::InCell | Mode::InColumnGroup
            | Mode::InTemplate => table_growth(m, t),
            _ => 0,
        },
    }
}

/// The order `h` of a rule application: the rules a token goes to by
/// "using the rules for" or a reprocessing that keeps the stack come
/// lower.
pub open spec fn order(r: Rules, t: Tok) -> nat {
    match r {
        Rules::Foreign => 30,
        Rules::Html(m) => match m {
            Mode::Text => 29,
            Mode::InTableText => if t is Char {
                0
            } else {
                28
            },
            Mode::AfterAfterBody | Mode::AfterAfterFrameset => 27,
            Mode::AfterBody => if is_end(t, Tag::Html) {
                1
            } else {
                26
            },
            Mode::AfterFrameset => 26,
            Mode::InFrameset => 25,
            Mode::Initial => 24,
            Mode::BeforeHtml => 23,
            Mode::BeforeHead => 22,
            Mode::InHeadNoscript => 21,
            Mode::AfterHead => 10,
            Mode::InTemplate => if t is Eof {
                1
            } else {
                19
            },
            Mode::InColumnGroup => 18,
            Mode::InCell => 17,
            Mode::InCaption => 16,
            Mode::InRow => 15,
            Mode::InTableBody => 14,
            Mode::InTable => 13,
            Mode::InBody => if is_start(t, Tag::Html) {
                0
            } else {
                12
            },
            Mode::InHead => 11,
        },
    }
}

/// The bound `B = L + G + 5T + 5 img`, which no edge increases.
pub open spec fn budget(r: Rules, p: Parser, t: Tok) -> nat {
    p.open.len() + growth(r, t) + 5 * p.template_modes.len() + 5 * img(t)
}

/// The rank of (r2, q, t2) is lexicographically below that of (r, p, t), the
/// stack of template modes does not grow, and the budget does not increase.
pub open spec fn decreases_to(r: Rules, p: Parser, t: Tok, r2: Rules, q: Parser, t2: Tok) -> bool {
    let (a1, b1, c1, d1, e1) = (img(t), p.template_modes.len(), growth(r, t), p.open.len(), order(r, t));
    let (a2, b2, c2, d2, e2) = (img(t2), q.template_modes.len(), growth(r2, t2), q.open.len(), order(r2, t2));
    &&& b2 <= b1
    &&& budget(r2, q, t2) <= budget(r, p, t)
    &&& (a2 < a1 || (a2 == a1 && (b2 < b1 || (b2 == b1 && (c2 < c1 || (c2 == c1 && (d2 < d1 || (d2 == d1
        && e2 < e1))))))))
}

// ---------------------------------------------------------------------
// The modes invariant

/// A mode the parser pushes onto the stack of template insertion modes ("in
/// template", and the modes "in template" switches it to).
pub open spec fn template_mode_ok(m: Mode) -> bool {
    m == Mode::InTemplate || m == Mode::InTable || m == Mode::InColumnGroup || m == Mode::InTableBody || m == Mode::InRow
        || m == Mode::InBody
}

/// See the module comment.
pub open spec fn modes_ok(p: Parser) -> bool {
    &&& forall|i: int| 0 <= i < p.template_modes.len() ==> template_mode_ok(#[trigger] p.template_modes[i])
    &&& p.mode == Mode::InTableText ==> p.original_mode != Mode::Text && p.original_mode != Mode::InTableText
    &&& p.mode == Mode::Text ==> p.original_mode != Mode::Text && p.original_mode != Mode::InTableText
}

/// Within a token, rules other than the current mode's (reached by "using the
/// rules for") are never applied while the mode is "text" or "in table
/// text", which use no other mode's rules.
pub open spec fn rules_ok(r: Rules, p: Parser) -> bool {
    match r {
        Rules::Html(m) => (m != p.mode ==> p.mode != Mode::Text && p.mode != Mode::InTableText) && (m == Mode::Text || m
            == Mode::InTableText ==> m == p.mode),
        Rules::Foreign => true,
    }
}

/// What every edge of a rule application satisfies: if the outcome
/// reprocesses (and the parser has not stopped), the rank decreases and the
/// invariants carry over; "using the rules for" keeps the insertion mode.
pub open spec fn edge_ok(r: Rules, p: Parser, t: Tok, o: Outcome) -> bool {
    match o {
        Outcome::Done(_) => true,
        Outcome::Reprocess(q, t2) => q.stopped || (decreases_to(r, p, t, Rules::Html(q.mode), q, t2) && modes_ok(q)),
        Outcome::Using(m, q, t2) => q.stopped || (decreases_to(r, p, t, Rules::Html(m), q, t2) && modes_ok(q) && q.mode
            == p.mode && m != Mode::Text && m != Mode::InTableText && p.mode != Mode::Text && p.mode
            != Mode::InTableText),
    }
}

/// The edges of every set of rules are ranked (the per-mode lemmas).
pub proof fn lemma_rules_edges(env: EncFns, r: Rules, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(r, p),
    ensures
        edge_ok(r, p, t, apply_rules(env, r, p, t)),
{
    match r {
        Rules::Foreign => frameset::lemma_foreign_edges(env, p, t),
        Rules::Html(m) => match m {
            Mode::Initial => early::lemma_initial_edges(env, p, t),
            Mode::BeforeHtml => early::lemma_before_html_edges(env, p, t),
            Mode::BeforeHead => early::lemma_before_head_edges(env, p, t),
            Mode::InHead => early::lemma_in_head_edges(env, p, t),
            Mode::InHeadNoscript => early::lemma_in_head_noscript_edges(env, p, t),
            Mode::AfterHead => early::lemma_after_head_edges(env, p, t),
            Mode::InBody => in_body::lemma_in_body_edges(env, p, t),
            Mode::Text => early::lemma_text_edges(env, p, t),
            Mode::InTable => tables::lemma_in_table_edges(env, p, t),
            Mode::InTableText => tables::lemma_in_table_text_edges(env, p, t),
            Mode::InCaption => tables::lemma_in_caption_edges(env, p, t),
            Mode::InColumnGroup => tables::lemma_in_column_group_edges(env, p, t),
            Mode::InTableBody => tables::lemma_in_table_body_edges(env, p, t),
            Mode::InRow => tables::lemma_in_row_edges(env, p, t),
            Mode::InCell => tables::lemma_in_cell_edges(env, p, t),
            Mode::InTemplate => tables::lemma_in_template_edges(env, p, t),
            Mode::AfterBody => frameset::lemma_after_body_edges(env, p, t),
            Mode::InFrameset => frameset::lemma_in_frameset_edges(env, p, t),
            Mode::AfterFrameset => frameset::lemma_after_frameset_edges(env, p, t),
            Mode::AfterAfterBody => frameset::lemma_after_after_body_edges(env, p, t),
            Mode::AfterAfterFrameset => frameset::lemma_after_after_frameset_edges(env, p, t),
        },
    }
}

// ---------------------------------------------------------------------
// The run

/// The rank as a number, with the bounds `t0` on the template modes and
/// `b0` on the budget fixed at the start of the token.
pub open spec fn rank(r: Rules, p: Parser, t: Tok, t0: nat, b0: nat) -> nat {
    ((((img(t) * (t0 + 1) + p.template_modes.len()) * 6 + growth(r, t)) * (b0 + 1) + p.open.len()) * 31 + order(r, t)) as nat
}

/// Bounds of the components.
pub proof fn lemma_components_bounded(r: Rules, t: Tok)
    ensures
        growth(r, t) <= growth_max(),
        order(r, t) <= order_max(),
        img(t) <= 1,
{
}

/// A lexicographic decrease with bounded components is a numeric decrease
/// of [`rank`].
pub proof fn lemma_rank_decreases(r: Rules, p: Parser, t: Tok, r2: Rules, q: Parser, t2: Tok, t0: nat, b0: nat)
    requires
        decreases_to(r, p, t, r2, q, t2),
        p.template_modes.len() <= t0,
        budget(r, p, t) <= b0,
    ensures
        rank(r2, q, t2, t0, b0) < rank(r, p, t, t0, b0),
{
    lemma_components_bounded(r, t);
    lemma_components_bounded(r2, t2);
    let (a1, b1, c1, d1, e1) = (img(t) as int, p.template_modes.len() as int, growth(r, t) as int, p.open.len() as int, order(r, t) as int);
    let (a2, b2, c2, d2, e2) = (img(t2) as int, q.template_modes.len() as int, growth(r2, t2) as int, q.open.len() as int, order(r2, t2) as int);
    let (tt, bb) = (t0 as int, b0 as int);
    assert(d1 <= bb && d2 <= bb);
    lemma_lex5(a1, b1, c1, d1, e1, a2, b2, c2, d2, e2, tt, bb);
}

/// The arithmetic of [`lemma_rank_decreases`].
pub proof fn lemma_lex5(a1: int, b1: int, c1: int, d1: int, e1: int, a2: int, b2: int, c2: int, d2: int, e2: int, tt: int, bb: int)
    requires
        0 <= a1 <= 1,
        0 <= a2 <= 1,
        0 <= b2 <= b1 <= tt,
        0 <= c1 <= 5,
        0 <= c2 <= 5,
        0 <= d1 <= bb,
        0 <= d2 <= bb,
        0 <= e1 <= 30,
        0 <= e2 <= 30,
        a2 < a1 || (a2 == a1 && (b2 < b1 || (b2 == b1 && (c2 < c1 || (c2 == c1 && (d2 < d1 || (d2 == d1 && e2 < e1))))))),
    ensures
        (((a2 * (tt + 1) + b2) * 6 + c2) * (bb + 1) + d2) * 31 + e2 < (((a1 * (tt + 1) + b1) * 6 + c1) * (bb + 1) + d1) * 31 + e1,
{
    let x1 = a1 * (tt + 1) + b1;
    let x2 = a2 * (tt + 1) + b2;
    if a2 < a1 {
        assert(x2 < x1) by (nonlinear_arith)
            requires a2 < a1, 0 <= a2, 0 <= b2 <= tt, 0 <= b1, x1 == a1 * (tt + 1) + b1, x2 == a2 * (tt + 1) + b2;
    } else {
        assert(x2 <= x1) by (nonlinear_arith)
            requires a2 == a1, b2 <= b1, x1 == a1 * (tt + 1) + b1, x2 == a2 * (tt + 1) + b2;
    }
    let y1 = x1 * 6 + c1;
    let y2 = x2 * 6 + c2;
    assert(y2 < y1 || (y2 == y1 && (d2 < d1 || (d2 == d1 && e2 < e1)))) by (nonlinear_arith)
        requires
            x2 < x1 || (x2 == x1 && (c2 < c1 || (c2 == c1 && (d2 < d1 || (d2 == d1 && e2 < e1))))),
            0 <= c1 <= 5, 0 <= c2 <= 5, y1 == x1 * 6 + c1, y2 == x2 * 6 + c2;
    let z1 = y1 * (bb + 1) + d1;
    let z2 = y2 * (bb + 1) + d2;
    assert(z2 < z1 || (z2 == z1 && e2 < e1)) by (nonlinear_arith)
        requires
            y2 < y1 || (y2 == y1 && (d2 < d1 || (d2 == d1 && e2 < e1))),
            0 <= d1 <= bb, 0 <= d2 <= bb, 0 <= y2, z1 == y1 * (bb + 1) + d1, z2 == y2 * (bb + 1) + d2;
    assert(z2 * 31 + e2 < z1 * 31 + e1) by (nonlinear_arith)
        requires z2 < z1 || (z2 == z1 && e2 < e1), 0 <= e1 <= 30, 0 <= e2 <= 30;
}

/// The run ends with fuel above the rank.
pub proof fn lemma_run_some(env: EncFns, p: Parser, t: Tok, r: Rules, fuel: nat, t0: nat, b0: nat)
    requires
        modes_ok(p),
        rules_ok(r, p),
        p.template_modes.len() <= t0,
        budget(r, p, t) <= b0,
        fuel > rank(r, p, t, t0, b0),
    ensures
        run(env, p, t, r, fuel) is Some,
    decreases fuel,
{
    lemma_rules_edges(env, r, p, t);
    match apply_rules(env, r, p, t) {
        Outcome::Done(_) => {},
        Outcome::Reprocess(q, t2) => {
            if !q.stopped {
                let r2 = Rules::Html(q.mode);
                lemma_rank_decreases(r, p, t, r2, q, t2, t0, b0);
                lemma_run_some(env, q, t2, r2, (fuel - 1) as nat, t0, b0);
            }
        },
        Outcome::Using(m, q, t2) => {
            if !q.stopped {
                let r2 = Rules::Html(m);
                lemma_rank_decreases(r, p, t, r2, q, t2, t0, b0);
                lemma_run_some(env, q, t2, r2, (fuel - 1) as nat, t0, b0);
            }
        },
    }
}

/// The dispatcher chooses the current mode's rules or foreign content.
pub proof fn lemma_dispatcher_rules_ok(p: Parser, t: Tok)
    ensures
        rules_ok(dispatcher(p, t), p),
{
}

/// **Reprocessing ends** (Phase 4 item 4.9): for every parser whose modes
/// satisfy [`modes_ok`] (part of the reachable state invariant) and every
/// token, the tree construction stage handles the token within
/// `fuel_bound(p)` rule applications, so `tree_construction` never takes its
/// fallback.
pub proof fn theorem_dispatch_total(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
    ensures
        run(env, p, t, dispatcher(p, t), fuel_bound(p)) is Some,
{
    let r = dispatcher(p, t);
    lemma_dispatcher_rules_ok(p, t);
    lemma_components_bounded(r, t);
    let t0 = p.template_modes.len();
    let l = p.open.len();
    let b0 = budget(r, p, t);
    assert(b0 <= l + 5 * t0 + 10);
    let f = fuel_bound(p);
    assert(rank(r, p, t, t0, b0) < f) by {
        let a = img(t) as int;
        let c = growth(r, t) as int;
        let e = order(r, t) as int;
        let (ti, li, bi) = (t0 as int, l as int, b0 as int);
        assert((((a * (ti + 1) + ti) * 6 + c) * (bi + 1) + li) * 31 + e < 372 * (ti + 1) * (li + 5 * ti + 11)) by (nonlinear_arith)
            requires 0 <= a <= 1, 0 <= ti, 0 <= c <= 5, 0 <= li <= bi, bi <= li + 5 * ti + 10, 0 <= e <= 30;
    }
    lemma_run_some(env, p, t, r, f, t0, b0);
}

} // verus!
