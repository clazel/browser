//! A proven check of [`spec::d`] over a whole arena, for the part of the grammar
//! it covers (item 7.3): [`check_derivation`] takes the arena of an
//! [`Ast`] that has passed [`crate::check::finish`] and the tokens the parser
//! consumed (with the gaps where it inserted a `;`), and returns
//! [`Derivation::Verified`] only if `derives_root` holds for it: every node
//! derives the tokens it spans, bottom-up, in the context the root's goal gives.
//!
//! **Covered:** a `Script` or `Module` of `EmptyStatement`s and
//! `ExpressionStatement`s whose expressions are numeric and string literals,
//! parenthesized expressions and the binary operators `+ - * / % < >`. For any
//! other node the result is [`Derivation::Unsupported`]: nothing is claimed.
//! [`crate::derive`] has the rule lemmas for more productions; they are not yet
//! wired into this check.
//!
//! **Assumptions, stated plainly:** the executable tokens are the specification's
//! (`dtok_matches`, `gaps_match`): that they are what the lexer's specification says
//! (`lexes_as`) is the lexer's contract (item 7.2), which the executable lexer does
//! not meet yet; and that every inserted `;` is justified (`gap_justified`: no
//! sentence of the grammar goes on with the offending token), which this check
//! does not look at.

use crate::ast::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// A token as the parser consumed it.
pub struct DTok {
    /// The kind, as the specification's.
    pub kind: TokKind,
    /// The index of the first code point.
    pub start: usize,
    /// One past the last code point.
    pub end: usize,
    /// A line terminator precedes it.
    pub nl: bool,
    /// Written with a `UnicodeEscapeSequence`.
    pub escaped: bool,
}

/// The executable token `e` is the specification's token `t` of the source `src`.
pub open spec fn dtok_matches(src: Seq<u32>, e: DTok, t: Tok) -> bool {
    e.kind == t.kind && e.start as int == t.start && e.end as int == t.end && e.start <= e.end
        && e.end <= src.len() && t.text =~= src.subrange(e.start as int, e.end as int)
        && e.escaped == t.escaped && e.nl == t.nl_before
}

/// The executable tokens and gaps are the specification's stream `ts`.
pub open spec fn stream_matches(src: Seq<u32>, toks: Seq<DTok>, gaps: Seq<Ins>, ts: Stream) -> bool {
    toks.len() == ts.toks.len() && gaps =~= ts.gaps && (forall|k: int|
        0 <= k < toks.len() ==> dtok_matches(src, toks[k], #[trigger] ts.toks[k]))
}

/// Tokens are not empty and their ends increase.
pub open spec fn toks_wf(ts: Stream) -> bool {
    (forall|k: int| 0 <= k < tn(ts) ==> (#[trigger] ts.toks[k]).start < ts.toks[k].end) && (
    forall|x: int, y: int|
        0 <= x < y < tn(ts) ==> (#[trigger] ts.toks[x]).end < (#[trigger] ts.toks[y]).end)
}

/// The arena of `nodes` with the root last.
pub open spec fn arena_of(nodes: Seq<Node>) -> AstV {
    AstV { nodes: nodes.map_values(|nd: Node| nd@), root: nodes.len() - 1 }
}

/// `ed` of a node that spans tokens `lo..hi` is `hi`.
proof fn lemma_ed_of(a: AstV, ts: Stream, c: int, lo: int, hi: int)
    requires
        toks_wf(ts),
        0 <= c < a.nodes.len(),
        0 <= lo < hi <= tn(ts),
        a.nodes[c].start == ts.toks[lo].start,
        a.nodes[c].end == ts.toks[hi - 1].end,
    ensures
        ed(a, ts, c, lo) == hi,
{
    assert(ts.toks[lo].start < ts.toks[lo].end);
    assert(ts.toks[lo].end <= ts.toks[hi - 1].end) by {
        if lo < hi - 1 {
            assert(ts.toks[lo].end < ts.toks[hi - 1].end);
        }
    }
    assert(a.nodes[c].start < a.nodes[c].end);
    assert(exists|x: int| lo <= x < tn(ts) && ts.toks[x].end == a.nodes[c].end) by {
        assert(ts.toks[hi - 1].end == a.nodes[c].end);
    }
    let y = choose|x: int| lo <= x < tn(ts) && ts.toks[x].end == a.nodes[c].end;
    assert(y == hi - 1) by {
        if y < hi - 1 {
            assert(ts.toks[y].end < ts.toks[hi - 1].end);
        }
        if y > hi - 1 {
            assert(ts.toks[hi - 1].end < ts.toks[y].end);
        }
    }
}

/// A node is derived over tokens `lo..hi` in context `cx`, and its `ed` is `hi`.
pub open spec fn node_done(a: AstV, ts: Stream, c: int, cx: Ctx, lo: int, hi: int) -> bool {
    0 <= lo < hi <= tn(ts) && d(a, ts, c, cx, lo, hi) && ed(a, ts, c, lo) == hi
}

/// §14.5 `ExpressionStatement : Expression ;`, for a first token that is not an
/// `IdentifierName` and not `{`.
proof fn lemma_expr_stmt_derives(a: AstV, ts: Stream, n: int, cx: Ctx, i: int, m: int, j: int, c: int)
    requires
        0 <= n < a.nodes.len(),
        0 <= i < m <= tn(ts),
        a.nodes[n].kind == NodeKind::ExpressionStatement,
        a.nodes[n].children =~= seq![c],
        0 <= c < n,
        lvl(a, c) >= -1,
        ts.toks[i].kind != TokKind::IdentifierName,
        !is_p(ts, i, "{"@),
        ed(a, ts, c, i) == m,
        d(a, ts, c, cx_in(cx, true), i, m),
        semi(ts, m, j, false),
        0 <= j <= tn(ts),
        span_ok(a, ts, n, i, j),
    ensures
        d(a, ts, n, cx, i, j),
{
    assert(a.nodes[n].children[0] == c);
    assert(dc(a, ts, n, c, cx_in(cx, true), i, m));
    assert(!is_kw(ts, i, "function"@));
    assert(!is_kw(ts, i, "class"@));
    assert(!is_kw(ts, i, "async"@));
    assert(!is_kw(ts, i, "let"@));
    assert(d_stmt(a, ts, n, cx, i, j));
}

/// §14.4 `EmptyStatement : ;`.
proof fn lemma_empty_statement_derives(a: AstV, ts: Stream, n: int, cx: Ctx, i: int)
    requires
        0 <= n < a.nodes.len(),
        0 <= i < tn(ts),
        a.nodes[n].kind == NodeKind::EmptyStatement,
        a.nodes[n].children.len() == 0,
        is_p(ts, i, ";"@),
        span_ok(a, ts, n, i, i + 1),
    ensures
        d(a, ts, n, cx, i, i + 1),
{
    assert(d_stmt(a, ts, n, cx, i, i + 1));
}

/// §16.1 and §16.2: a root whose items derive consecutive token ranges that make
/// the whole stream. `dl` is built from the back.
proof fn lemma_dl_cons(a: AstV, ts: Stream, bound: int, ks: Seq<int>, k: int, cx: Ctx, i: int, m: int, j: int)
    requires
        0 <= k < ks.len(),
        ed(a, ts, ks[k], i) == m,
        dc(a, ts, bound, ks[k], cx, i, m),
        dl(a, ts, bound, ks, k + 1, cx, m, j),
    ensures
        dl(a, ts, bound, ks, k, cx, i, j),
{
}

/// The `Script` or `Module` root `n` derives the whole stream.
proof fn lemma_root_derives(a: AstV, ts: Stream, n: int, cx: Ctx, g: SourceGoal)
    requires
        0 <= n < a.nodes.len(),
        a.nodes[n].kind == (if g == SourceGoal::Script {
            NodeKind::Script
        } else {
            NodeKind::Module
        }),
        all_items(a, a.nodes[n].children),
        dl(a, ts, n, a.nodes[n].children, 0, cx, 0, tn(ts)),
        span_ok(a, ts, n, 0, tn(ts)),
    ensures
        d(a, ts, n, cx, 0, tn(ts)),
{
    assert(d_stmt(a, ts, n, cx, 0, tn(ts))) by {
        if g == SourceGoal::Module {
            assert forall|k: int| 0 <= k < a.nodes[n].children.len() implies is_module_item_kind(
                kd(a, #[trigger] a.nodes[n].children[k]),
            ) by {}
        }
    }
}

/// `text` of the source between the token's bounds is `w`.
fn text_is(src: &Vec<u32>, t: &DTok, w: &[u32]) -> (r: bool)
    requires
        t.start <= t.end <= src.len(),
    ensures
        r == (src@.subrange(t.start as int, t.end as int) =~= w@),
{
    let len = t.end.saturating_sub(t.start);
    if len != w.len() {
        return false;
    }
    let mut k: usize = 0;
    while k < len
        invariant
            t.start <= t.end <= src.len(),
            len == t.end - t.start,
            len == w.len(),
            k <= len,
            forall|q: int| 0 <= q < k ==> src@[t.start as int + q] == w@[q],
        decreases len - k,
    {
        let a = match src.as_slice().get(t.start.saturating_add(k)) {
            Some(x) => *x,
            None => {
                return false;
            },
        };
        let b = match w.get(k) {
            Some(x) => *x,
            None => {
                return false;
            },
        };
        if a != b {
            proof {
                assert(src@.subrange(t.start as int, t.end as int)[k as int] == src@[t.start as int
                    + k]);
            }
            return false;
        }
        k = k.saturating_add(1);
    }
    true
}

} // verus!
