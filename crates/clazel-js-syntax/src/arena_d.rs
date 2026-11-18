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

/// The source text of the token is the one code point `code`.
fn text_is1(src: &Vec<u32>, t: &DTok, code: u32) -> (r: bool)
    requires
        t.start <= t.end <= src.len(),
    ensures
        r == (src@.subrange(t.start as int, t.end as int) =~= seq![code]),
{
    if t.end.saturating_sub(t.start) != 1 {
        return false;
    }
    let r = match src.as_slice().get(t.start) {
        Some(x) => *x == code,
        None => false,
    };
    proof {
        let sub = src@.subrange(t.start as int, t.end as int);
        assert(sub.len() == 1);
        assert(sub[0] == src@[t.start as int]);
        assert(sub =~= seq![src@[t.start as int]]);
    }
    r
}

/// The code point of a one-character operator that the check covers.
pub open spec fn op_code(op: Op) -> u32 {
    match op {
        Op::Add => 0x2B,
        Op::Sub => 0x2D,
        Op::Mul => 0x2A,
        Op::Div => 0x2F,
        Op::Rem => 0x25,
        Op::Lt => 0x3C,
        Op::Gt => 0x3E,
        _ => 0,
    }
}

/// The text of the punctuators the check reads, as code points.
proof fn lemma_punct_text()
    ensures
        cps(";"@) =~= seq![0x3Bu32],
        cps("("@) =~= seq![0x28u32],
        cps(")"@) =~= seq![0x29u32],
        cps("{"@) =~= seq![0x7Bu32],
        cps("+"@) =~= seq![0x2Bu32],
        cps("-"@) =~= seq![0x2Du32],
        cps("*"@) =~= seq![0x2Au32],
        cps("/"@) =~= seq![0x2Fu32],
        cps("%"@) =~= seq![0x25u32],
        cps("<"@) =~= seq![0x3Cu32],
        cps(">"@) =~= seq![0x3Eu32],
{
    reveal_strlit(";");
    reveal_strlit("(");
    reveal_strlit(")");
    reveal_strlit("{");
    reveal_strlit("+");
    reveal_strlit("-");
    reveal_strlit("*");
    reveal_strlit("/");
    reveal_strlit("%");
    reveal_strlit("<");
    reveal_strlit(">");
    assert(";"@ =~= seq![';']);
    assert("("@ =~= seq!['(']);
    assert(")"@ =~= seq![')']);
    assert("{"@ =~= seq!['{']);
    assert("+"@ =~= seq!['+']);
    assert("-"@ =~= seq!['-']);
    assert("*"@ =~= seq!['*']);
    assert("/"@ =~= seq!['/']);
    assert("%"@ =~= seq!['%']);
    assert("<"@ =~= seq!['<']);
    assert(">"@ =~= seq!['>']);
}

/// A one-character operator of the check is the punctuator with its code point.
proof fn lemma_op_is_tok(ts: Stream, i: int, op: Op)
    requires
        op == Op::Add || op == Op::Sub || op == Op::Mul || op == Op::Div || op == Op::Rem || op
            == Op::Lt || op == Op::Gt,
        0 <= i < tn(ts),
        ts.toks[i].kind == TokKind::Punctuator,
        ts.toks[i].text =~= seq![op_code(op)],
    ensures
        is_op_tok(ts, i, op),
{
    lemma_punct_text();
}

/// What a processed node `j < m` has proven: it derives tokens `lo[j]..hi[j]` in
/// context `cx`, and has the binding strength `lv[j]`.
pub open spec fn inv(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    lo: Seq<usize>,
    hi: Seq<usize>,
    lv: Seq<i32>,
    m: int,
) -> bool {
    lo.len() == m && hi.len() == m && lv.len() == m && (forall|j: int|
        0 <= j < m ==> node_done(a, ts, j, cx, lo[j] as int, hi[j] as int) && lv[j] as int
            == lvl(a, j))
}

/// The binding strengths of the kinds the check covers.
pub open spec fn covered_kind(k: NodeKind) -> bool {
    k == NodeKind::NumericLiteral || k == NodeKind::StringLiteral || k
        == NodeKind::RegularExpressionLiteral || k == NodeKind::ParenthesizedExpression || k
        == NodeKind::AdditiveExpression || k == NodeKind::MultiplicativeExpression || k
        == NodeKind::RelationalExpression || k == NodeKind::ExpressionStatement || k
        == NodeKind::EmptyStatement
}

/// §13.2.3, §13.2.7 a literal leaf: its token is found from its start.
fn check_literal(
    nodes: &Vec<Node>,
    toks: &Vec<DTok>,
    by_start: &Vec<usize>,
    m: usize,
    Ghost(ts): Ghost<Stream>,
    Ghost(cx): Ghost<Ctx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        m < nodes.len(),
        arena_of(nodes@).nodes.len() == nodes.len(),
        toks_wf(ts),
        toks@.len() == tn(ts),
        forall|k: int| 0 <= k < toks@.len() ==> (toks@[k].kind == (#[trigger] ts.toks[k]).kind
            && toks@[k].start as int == ts.toks[k].start && toks@[k].end as int == ts.toks[k].end),
    ensures
        match r {
            Some((lo, hi, l)) => node_done(arena_of(nodes@), ts, m as int, cx, lo as int, hi as int)
                && l as int == lvl(arena_of(nodes@), m as int),
            None => true,
        },
{
    let nd = match nodes.as_slice().get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let a = Ghost(arena_of(nodes@));
    let kind_ok = match nd.kind {
        NodeKind::NumericLiteral => 1,
        NodeKind::StringLiteral => 2,
        NodeKind::RegularExpressionLiteral => 3,
        _ => 0,
    };
    if kind_ok == 0 || !nd.children.is_empty() {
        return None;
    }
    let x = match by_start.as_slice().get(nd.start) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let t = match toks.as_slice().get(x) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    let ok = t.start == nd.start && t.end == nd.end && (match nd.kind {
        NodeKind::NumericLiteral => matches!(t.kind, TokKind::NumericLiteral),
        NodeKind::StringLiteral => matches!(t.kind, TokKind::StringLiteral),
        _ => matches!(t.kind, TokKind::RegularExpressionLiteral),
    });
    if !ok {
        return None;
    }
    let x1 = x.saturating_add(1);
    proof {
        let av = arena_of(nodes@);
        assert(av.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(t == &toks@[x as int]);
        assert(nd.children@.len() == 0);
        assert(av.nodes[m as int].children.len() == 0);
        assert(av.nodes[m as int].start == nd.start as int);
        assert(av.nodes[m as int].end == nd.end as int);
        assert(ts.toks[x as int].start == t.start as int);
        assert(ts.toks[x as int].end == t.end as int);
        assert(ts.toks[x as int].kind == t.kind);
        assert(x < toks.len());
        assert(toks.len() <= usize::MAX);
        assert(x1 as int == x as int + 1);
        assert(x as int + 1 <= tn(ts));
        match nd.kind {
            NodeKind::NumericLiteral => {
                assert(t.kind == TokKind::NumericLiteral);
            },
            NodeKind::StringLiteral => {
                assert(t.kind == TokKind::StringLiteral);
            },
            _ => {
                assert(t.kind == TokKind::RegularExpressionLiteral);
            },
        }
        lemma_leaf_literal_in(av, ts, m as int, cx, x as int);
        assert(span_ok(av, ts, m as int, x as int, x as int + 1));
        lemma_ed_of(av, ts, m as int, x as int, x as int + 1);
        assert(lvl(av, m as int) == 17);
    }
    Some((x, x1, 17))
}

/// `lemma_leaf_literal` for the three literal kinds.
proof fn lemma_leaf_literal_in(a: AstV, ts: Stream, n: int, cx: Ctx, i: int)
    requires
        0 <= n < a.nodes.len(),
        0 <= i < tn(ts),
        a.nodes[n].children.len() == 0,
        a.nodes[n].start == ts.toks[i].start,
        a.nodes[n].end == ts.toks[i].end,
        toks_wf(ts),
        a.nodes[n].kind == NodeKind::NumericLiteral && ts.toks[i].kind == TokKind::NumericLiteral
            || a.nodes[n].kind == NodeKind::StringLiteral && ts.toks[i].kind
            == TokKind::StringLiteral || a.nodes[n].kind == NodeKind::RegularExpressionLiteral
            && ts.toks[i].kind == TokKind::RegularExpressionLiteral,
    ensures
        node_done(a, ts, n, cx, i, i + 1),
{
    assert(ts.toks[i].start < ts.toks[i].end);
    crate::derive::lemma_leaf_literal(a, ts, n, cx, i);
    assert(span_ok(a, ts, n, i, i + 1));
    lemma_ed_of(a, ts, n, i, i + 1);
}

} // verus!
