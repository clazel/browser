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
#[verifier::opaque]
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
        0 <= j < m ==> #[trigger] node_done(a, ts, j, cx, lo[j] as int, hi[j] as int) && lv[j] as int
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

/// What the helpers below assume of the executable data: the stream is the
/// specification's, the tokens are not empty and increase, and the arena is
/// well formed.
#[verifier::opaque]
pub open spec fn env_ok(
    src: Seq<u32>,
    nodes: Seq<Node>,
    toks: Seq<DTok>,
    gaps: Seq<Ins>,
    ts: Stream,
) -> bool {
    stream_matches(src, toks, gaps, ts) && toks_wf(ts) && ast_wf(arena_of(nodes)) && gaps.len()
        == toks.len() + 1
}

/// The children of a node of a well-formed arena are before it.
proof fn lemma_child_before(a: AstV, m: int, k: int)
    requires
        ast_wf(a),
        0 <= m < a.nodes.len(),
        0 <= k < a.nodes[m].children.len(),
    ensures
        0 <= a.nodes[m].children[k] < m,
{
}

/// The binding strength and operand minima of the binary kinds of the check.
pub open spec fn bin_levels(k: NodeKind) -> (int, int, int) {
    match k {
        NodeKind::AdditiveExpression => (9, 9, 10),
        NodeKind::MultiplicativeExpression => (10, 10, 11),
        _ => (7, 7, 8),
    }
}

/// A binary node of the check whose operands and operator token are as read.
#[verifier::spinoff_prover]
proof fn lemma_binary_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    l: int,
    r: int,
    lo_l: int,
    mi: int,
    lo_r: int,
    j: int,
    code: u32,
    own: int,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= l < m,
        0 <= r < m,
        cx_in(cx, true) == cx,
        a.nodes[m].children =~= seq![l, r],
        a.nodes[m].kind == NodeKind::AdditiveExpression || a.nodes[m].kind
            == NodeKind::MultiplicativeExpression || a.nodes[m].kind
            == NodeKind::RelationalExpression,
        a.nodes[m].kind == NodeKind::AdditiveExpression ==> (a.nodes[m].op == Op::Add
            || a.nodes[m].op == Op::Sub),
        a.nodes[m].kind == NodeKind::MultiplicativeExpression ==> (a.nodes[m].op == Op::Mul
            || a.nodes[m].op == Op::Div || a.nodes[m].op == Op::Rem),
        a.nodes[m].kind == NodeKind::RelationalExpression ==> (a.nodes[m].op == Op::Lt
            || a.nodes[m].op == Op::Gt),
        code == op_code(a.nodes[m].op),
        own == bin_levels(a.nodes[m].kind).0,
        lvl(a, l) >= bin_levels(a.nodes[m].kind).1,
        lvl(a, r) >= bin_levels(a.nodes[m].kind).2,
        node_done(a, ts, l, cx, lo_l, mi),
        node_done(a, ts, r, cx, lo_r, j),
        lo_r == mi + 1,
        0 <= mi < tn(ts),
        ts.toks[mi].kind == TokKind::Punctuator,
        ts.toks[mi].text =~= seq![code],
        a.nodes[m].start == ts.toks[lo_l].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, lo_l, j),
        lvl(a, m) == own,
{
    lemma_op_is_tok(ts, mi, a.nodes[m].op);
    assert(span_ok(a, ts, m, lo_l, j));
    assert(bin_op_ok(a.nodes[m].kind, a.nodes[m].op));
    assert(binary_operands_ok(a, a.nodes[m].kind, a.nodes[m].op, l, r));
    crate::derive::lemma_binary_derives(a, ts, m, cx, lo_l, mi, j, l, r);
    lemma_ed_of(a, ts, m, lo_l, j);
}

/// The binding strengths, the operator check and the code point of a binary
/// kind and operator of the check.
fn bin_info(kind: NodeKind, op: Op) -> (r: (i32, i32, i32, bool, u32))
    ensures
        r.3 ==> ((kind == NodeKind::AdditiveExpression && (op == Op::Add || op == Op::Sub))
            || (kind == NodeKind::MultiplicativeExpression && (op == Op::Mul || op == Op::Div
            || op == Op::Rem)) || (kind == NodeKind::RelationalExpression && (op == Op::Lt || op
            == Op::Gt))) && r.4 == op_code(op) && r.0 == bin_levels(kind).0 && r.1
            == bin_levels(kind).1 && r.2 == bin_levels(kind).2,
{
    match kind {
        NodeKind::AdditiveExpression => match op {
            Op::Add => (9, 9, 10, true, 0x2B),
            Op::Sub => (9, 9, 10, true, 0x2D),
            _ => (0, 0, 0, false, 0),
        },
        NodeKind::MultiplicativeExpression => match op {
            Op::Mul => (10, 10, 11, true, 0x2A),
            Op::Div => (10, 10, 11, true, 0x2F),
            Op::Rem => (10, 10, 11, true, 0x25),
            _ => (0, 0, 0, false, 0),
        },
        NodeKind::RelationalExpression => match op {
            Op::Lt => (7, 7, 8, true, 0x3C),
            Op::Gt => (7, 7, 8, true, 0x3E),
            _ => (0, 0, 0, false, 0),
        },
        _ => (0, 0, 0, false, 0),
    }
}

/// §13.6 to §13.13 `+ - * / % < >`: a binary node of the check.
#[verifier::spinoff_prover]
fn check_binary(
    src: &Vec<u32>,
    nodes: &Vec<Node>,
    toks: &Vec<DTok>,
    gaps: &Vec<Ins>,
    lo: &Vec<usize>,
    hi: &Vec<usize>,
    lv: &Vec<i32>,
    m: usize,
    Ghost(ts): Ghost<Stream>,
    Ghost(cx): Ghost<Ctx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        m < nodes.len(),
        cx_in(cx, true) == cx,
        env_ok(src@, nodes@, toks@, gaps@, ts),
        inv(arena_of(nodes@), ts, cx, lo@, hi@, lv@, m as int),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(arena_of(nodes@), ts, m as int, cx, l0 as int, h0 as int)
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
    let (own, lmin, rmin, opok, code) = bin_info(nd.kind, nd.op);
    if !opok || nd.children.len() != 2 {
        return None;
    }
    let l = match nd.children.as_slice().get(0) {
        Some(x) => *x as usize,
        None => {
            return None;
        },
    };
    let r = match nd.children.as_slice().get(1) {
        Some(x) => *x as usize,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, ts);
        lemma_child_before(a, m as int, 0);
        lemma_child_before(a, m as int, 1);
    }
    if l >= m || r >= m {
        return None;
    }
    let lo_l = match lo.as_slice().get(l) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let mi = match hi.as_slice().get(l) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lo_r = match lo.as_slice().get(r) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let j = match hi.as_slice().get(r) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_l = match lv.as_slice().get(l) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_r = match lv.as_slice().get(r) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    if lvl_l < lmin || lvl_r < rmin || lo_r != mi.saturating_add(1) {
        return None;
    }
    let opt = match toks.as_slice().get(mi) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    let first = match toks.as_slice().get(lo_l) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    let last = match toks.as_slice().get(j.saturating_sub(1)) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, ts, mi as int);
        assert(opt == &toks@[mi as int]);
    }
    if !matches!(opt.kind, TokKind::Punctuator) || !text_is1(src, opt, code) || nd.start
        != first.start || nd.end != last.end {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(a.nodes[m as int].children =~= seq![l as int, r as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
            assert(a.nodes[m as int].children[0] == l as int);
            assert(a.nodes[m as int].children[1] == r as int);
        }
        lemma_inv_get(a, ts, cx, lo@, hi@, lv@, m as int, l as int);
        lemma_inv_get(a, ts, cx, lo@, hi@, lv@, m as int, r as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, ts, mi as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, ts, lo_l as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, ts, j as int - 1);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, ts);
        assert(mi < toks.len());
        assert(toks.len() <= usize::MAX);
        assert(lo_r == mi + 1);
        assert(j >= 1);
        assert(first.start as int == ts.toks[lo_l as int].start);
        assert(last.end as int == ts.toks[j as int - 1].end);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].op == nd.op);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(ts.toks[mi as int].kind == TokKind::Punctuator);
        assert(ts.toks[mi as int].text =~= seq![code]);
        lemma_binary_done(
            a,
            ts,
            cx,
            m as int,
            l as int,
            r as int,
            lo_l as int,
            mi as int,
            lo_r as int,
            j as int,
            code,
            own as int,
        );
    }
    Some((lo_l, j, own))
}

/// Node `j < m` is done (`inv`).
proof fn lemma_inv_get(a: AstV, ts: Stream, cx: Ctx, lo: Seq<usize>, hi: Seq<usize>, lv: Seq<i32>, m: int, j: int)
    requires
        inv(a, ts, cx, lo, hi, lv, m),
        0 <= j < m,
    ensures
        node_done(a, ts, j, cx, lo[j] as int, hi[j] as int),
        lv[j] as int == lvl(a, j),
{
    reveal(inv);
    assert(node_done(a, ts, j, cx, lo[j] as int, hi[j] as int));
}

/// Token `k` of the executable tokens is the specification's.
proof fn lemma_env_tok(src: Seq<u32>, nodes: Seq<Node>, toks: Seq<DTok>, gaps: Seq<Ins>, ts: Stream, k: int)
    requires
        env_ok(src, nodes, toks, gaps, ts),
        0 <= k < toks.len(),
    ensures
        dtok_matches(src, toks[k], ts.toks[k]),
{
    reveal(env_ok);
}

/// The specification's tokens are not empty and their ends increase.
proof fn lemma_env_toks_wf(src: Seq<u32>, nodes: Seq<Node>, toks: Seq<DTok>, gaps: Seq<Ins>, ts: Stream)
    requires
        env_ok(src, nodes, toks, gaps, ts),
    ensures
        toks_wf(ts),
        tn(ts) == toks.len(),
        ast_wf(arena_of(nodes)),
{
    reveal(env_ok);
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

/// What `check_literal` reads of the stream.
proof fn lemma_env_literal_facts(src: Seq<u32>, nodes: Seq<Node>, toks: Seq<DTok>, gaps: Seq<Ins>, ts: Stream)
    requires
        env_ok(src, nodes, toks, gaps, ts),
    ensures
        toks_wf(ts),
        toks.len() == tn(ts),
        arena_of(nodes).nodes.len() == nodes.len(),
        forall|k: int|
            0 <= k < toks.len() ==> (toks[k].kind == (#[trigger] ts.toks[k]).kind && toks[k].start
                as int == ts.toks[k].start && toks[k].end as int == ts.toks[k].end),
{
    reveal(env_ok);
    assert forall|k: int| 0 <= k < toks.len() implies (toks[k].kind == (#[trigger] ts.toks[k]).kind
        && toks[k].start as int == ts.toks[k].start && toks[k].end as int == ts.toks[k].end) by {
        assert(dtok_matches(src, toks[k], ts.toks[k]));
    }
}

/// The inserted `;` of gap `k` is the specification's.
proof fn lemma_env_gap(src: Seq<u32>, nodes: Seq<Node>, toks: Seq<DTok>, gaps: Seq<Ins>, ts: Stream, k: int)
    requires
        env_ok(src, nodes, toks, gaps, ts),
        0 <= k < gaps.len(),
    ensures
        0 <= k < ts.gaps.len(),
        ts.gaps[k] == gaps[k],
        ts.gaps.len() == tn(ts) + 1,
{
    reveal(env_ok);
}

/// Extending the processed nodes by one.
proof fn lemma_inv_push(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    lo: Seq<usize>,
    hi: Seq<usize>,
    lv: Seq<i32>,
    m: int,
    l0: usize,
    h0: usize,
    l: i32,
)
    requires
        inv(a, ts, cx, lo, hi, lv, m),
        node_done(a, ts, m, cx, l0 as int, h0 as int),
        l as int == lvl(a, m),
    ensures
        inv(a, ts, cx, lo.push(l0), hi.push(h0), lv.push(l), m + 1),
{
    let lo2 = lo.push(l0);
    let hi2 = hi.push(h0);
    let lv2 = lv.push(l);
    assert(inv(a, ts, cx, lo2, hi2, lv2, m + 1)) by {
        reveal(inv);
        assert(lo2.len() == m + 1);
        assert(hi2.len() == m + 1);
        assert(lv2.len() == m + 1);
        assert forall|j: int| 0 <= j < m + 1 implies #[trigger] node_done(a, ts, j, cx, lo2[j] as int, hi2[j] as int)
            && lv2[j] as int == lvl(a, j) by {
            if j < m {
                assert(lo2[j] == lo[j]);
                assert(hi2[j] == hi[j]);
                assert(lv2[j] == lv[j]);
            } else {
                assert(lo2[j] == l0);
                assert(hi2[j] == h0);
                assert(lv2[j] == l);
            }
        }
    }
}

/// A parenthesized node of the check whose parts are as read.
#[verifier::spinoff_prover]
proof fn lemma_paren_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    c: int,
    lo_c: int,
    hc: int,
)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= c < m,
        a.nodes[m].kind == NodeKind::ParenthesizedExpression,
        a.nodes[m].children =~= seq![c],
        node_done(a, ts, c, cx, lo_c, hc),
        lvl(a, c) >= -1,
        1 <= lo_c,
        hc < tn(ts),
        ts.toks[lo_c - 1].kind == TokKind::Punctuator,
        ts.toks[lo_c - 1].text =~= seq![0x28u32],
        ts.toks[hc].kind == TokKind::Punctuator,
        ts.toks[hc].text =~= seq![0x29u32],
        a.nodes[m].start == ts.toks[lo_c - 1].start,
        a.nodes[m].end == ts.toks[hc].end,
    ensures
        node_done(a, ts, m, cx, lo_c - 1, hc + 1),
        lvl(a, m) == 17,
{
    lemma_punct_text();
    assert(is_p(ts, lo_c - 1, "("@));
    assert(is_p(ts, hc, ")"@));
    assert(span_ok(a, ts, m, lo_c - 1, hc + 1));
    crate::derive::lemma_parenthesized_derives(a, ts, m, cx, lo_c - 1, hc, c);
    lemma_ed_of(a, ts, m, lo_c - 1, hc + 1);
}

/// An `ExpressionStatement` of the check whose parts are as read.
#[verifier::spinoff_prover]
proof fn lemma_exprstmt_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    c: int,
    lo_c: int,
    hc: int,
    j: int,
    real_semicolon: bool,
)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= c < m,
        a.nodes[m].kind == NodeKind::ExpressionStatement,
        a.nodes[m].children =~= seq![c],
        node_done(a, ts, c, cx, lo_c, hc),
        lvl(a, c) >= -1,
        ts.toks[lo_c].kind != TokKind::IdentifierName,
        !(ts.toks[lo_c].kind == TokKind::Punctuator && ts.toks[lo_c].text =~= seq![0x7Bu32]),
        a.nodes[m].start == ts.toks[lo_c].start,
        0 <= j <= tn(ts),
        if real_semicolon {
            hc < tn(ts) && ts.toks[hc].kind == TokKind::Punctuator && ts.toks[hc].text
                =~= seq![0x3Bu32] && j == hc + 1 && a.nodes[m].end == ts.toks[hc].end
        } else {
            0 <= hc < ts.gaps.len() && ts.gaps[hc] == Ins::Semicolon && j == hc && a.nodes[m].end
                == ts.toks[hc - 1].end
        },
    ensures
        node_done(a, ts, m, cx, lo_c, j),
        lvl(a, m) == -100,
{
    lemma_punct_text();
    assert(!is_p(ts, lo_c, "{"@));
    assert(semi(ts, hc, j, false)) by {
        if real_semicolon {
            assert(is_p(ts, hc, ";"@));
        }
    }
    assert(span_ok(a, ts, m, lo_c, j));
    lemma_expr_stmt_derives(a, ts, m, cx, lo_c, hc, j, c);
    lemma_ed_of(a, ts, m, lo_c, j);
}

/// The goal symbol of the source text.
pub open spec fn goal_of(module: bool) -> SourceGoal {
    if module {
        SourceGoal::Module
    } else {
        SourceGoal::Script
    }
}

/// The context of the root has `[+In]` and no `[Default]`, so `cx_in` does not change it.
proof fn lemma_root_cx(g: SourceGoal)
    ensures
        cx_in(root_ctx(g), true) == root_ctx(g),
{
}

/// §13.2.9 `( Expression )`.
#[verifier::spinoff_prover]
fn check_paren(
    src: &Vec<u32>,
    nodes: &Vec<Node>,
    toks: &Vec<DTok>,
    gaps: &Vec<Ins>,
    lo: &Vec<usize>,
    hi: &Vec<usize>,
    lv: &Vec<i32>,
    m: usize,
    Ghost(ts): Ghost<Stream>,
    Ghost(cx): Ghost<Ctx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        m < nodes.len(),
        cx_in(cx, true) == cx,
        env_ok(src@, nodes@, toks@, gaps@, ts),
        inv(arena_of(nodes@), ts, cx, lo@, hi@, lv@, m as int),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(arena_of(nodes@), ts, m as int, cx, l0 as int, h0 as int)
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
    if !matches!(nd.kind, NodeKind::ParenthesizedExpression) || nd.children.len() != 1 {
        return None;
    }
    let c = match nd.children.as_slice().get(0) {
        Some(x) => *x as usize,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, ts);
        lemma_child_before(a, m as int, 0);
    }
    if c >= m {
        return None;
    }
    let lo_c = match lo.as_slice().get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let hc = match hi.as_slice().get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_c = match lv.as_slice().get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    if lvl_c < -1 || lo_c < 1 {
        return None;
    }
    let open = match toks.as_slice().get(lo_c.saturating_sub(1)) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    let close = match toks.as_slice().get(hc) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, ts, lo_c as int - 1);
        lemma_env_tok(src@, nodes@, toks@, gaps@, ts, hc as int);
        assert(open == &toks@[lo_c as int - 1]);
        assert(close == &toks@[hc as int]);
    }
    if !matches!(open.kind, TokKind::Punctuator) || !text_is1(src, open, 0x28) || !matches!(
        close.kind,
        TokKind::Punctuator,
    ) || !text_is1(src, close, 0x29) || nd.start != open.start || nd.end != close.end {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
            assert(a.nodes[m as int].children[0] == c as int);
        }
        lemma_inv_get(a, ts, cx, lo@, hi@, lv@, m as int, c as int);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(ts.toks[lo_c as int - 1].kind == TokKind::Punctuator);
        assert(ts.toks[lo_c as int - 1].text =~= seq![0x28u32]);
        assert(ts.toks[hc as int].kind == TokKind::Punctuator);
        assert(ts.toks[hc as int].text =~= seq![0x29u32]);
        assert(open.start as int == ts.toks[lo_c as int - 1].start);
        assert(close.end as int == ts.toks[hc as int].end);
        lemma_paren_done(a, ts, cx, m as int, c as int, lo_c as int, hc as int);
        assert(lo_c >= 1);
        assert(lo_c.saturating_sub(1) as int == lo_c as int - 1);
        assert(hc < toks.len());
        assert(toks.len() <= usize::MAX);
        assert(hc.saturating_add(1) as int == hc as int + 1);
    }
    Some((lo_c.saturating_sub(1), hc.saturating_add(1), 17))
}

/// §14.5 `Expression ;`.
#[verifier::spinoff_prover]
fn check_exprstmt(
    src: &Vec<u32>,
    nodes: &Vec<Node>,
    toks: &Vec<DTok>,
    gaps: &Vec<Ins>,
    lo: &Vec<usize>,
    hi: &Vec<usize>,
    lv: &Vec<i32>,
    m: usize,
    Ghost(ts): Ghost<Stream>,
    Ghost(cx): Ghost<Ctx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        m < nodes.len(),
        cx_in(cx, true) == cx,
        env_ok(src@, nodes@, toks@, gaps@, ts),
        inv(arena_of(nodes@), ts, cx, lo@, hi@, lv@, m as int),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(arena_of(nodes@), ts, m as int, cx, l0 as int, h0 as int)
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
    if !matches!(nd.kind, NodeKind::ExpressionStatement) || nd.children.len() != 1 {
        return None;
    }
    let c = match nd.children.as_slice().get(0) {
        Some(x) => *x as usize,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, ts);
        lemma_child_before(a, m as int, 0);
    }
    if c >= m {
        return None;
    }
    let lo_c = match lo.as_slice().get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let hc = match hi.as_slice().get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_c = match lv.as_slice().get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    if lvl_c < -1 {
        return None;
    }
    let t0 = match toks.as_slice().get(lo_c) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, ts, lo_c as int);
        assert(t0 == &toks@[lo_c as int]);
    }
    if matches!(t0.kind, TokKind::IdentifierName) || (matches!(t0.kind, TokKind::Punctuator)
        && text_is1(src, t0, 0x7B)) || nd.start != t0.start {
        return None;
    }
    // The `;`: a has_semi one at token `hc`, or one inserted in the gap before it.
    let mut has_semi = false;
    if let Some(st) = toks.as_slice().get(hc) {
        proof {
            lemma_env_tok(src@, nodes@, toks@, gaps@, ts, hc as int);
            assert(st == &toks@[hc as int]);
        }
        if matches!(st.kind, TokKind::Punctuator) && text_is1(src, st, 0x3B) && nd.end == st.end {
            has_semi = true;
        }
    }
    let j: usize;
    if has_semi {
        j = hc.saturating_add(1);
    } else {
        let g = match gaps.as_slice().get(hc) {
            Some(g) => g,
            None => {
                return None;
            },
        };
        let prev = match toks.as_slice().get(hc.saturating_sub(1)) {
            Some(t) => t,
            None => {
                return None;
            },
        };
        if !matches!(g, Ins::Semicolon) || hc < 1 || nd.end != prev.end {
            return None;
        }
        j = hc;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
            assert(a.nodes[m as int].children[0] == c as int);
        }
        lemma_inv_get(a, ts, cx, lo@, hi@, lv@, m as int, c as int);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(t0.start as int == ts.toks[lo_c as int].start);
        assert(ts.toks[lo_c as int].kind == t0.kind);
        assert(!(ts.toks[lo_c as int].kind == TokKind::Punctuator && ts.toks[lo_c as int].text
            =~= seq![0x7Bu32]));
        if has_semi {
            lemma_env_tok(src@, nodes@, toks@, gaps@, ts, hc as int);
            assert(hc < toks.len());
            assert(ts.toks[hc as int].kind == TokKind::Punctuator);
            assert(ts.toks[hc as int].text =~= seq![0x3Bu32]);
            assert(j as int == hc as int + 1);
            assert(toks@[hc as int].end as int == ts.toks[hc as int].end);
            lemma_exprstmt_done(a, ts, cx, m as int, c as int, lo_c as int, hc as int, j as int, true);
        } else {
            lemma_env_gap(src@, nodes@, toks@, gaps@, ts, hc as int);
            lemma_env_tok(src@, nodes@, toks@, gaps@, ts, hc as int - 1);
            assert(ts.gaps[hc as int] == Ins::Semicolon);
            assert(toks@[hc as int - 1].end as int == ts.toks[hc as int - 1].end);
            assert(hc <= toks.len());
            lemma_exprstmt_done(a, ts, cx, m as int, c as int, lo_c as int, hc as int, j as int, false);
        }
    }
    Some((lo_c, j, -100))
}

/// §14.4 `;`.
#[verifier::spinoff_prover]
fn check_empty(
    src: &Vec<u32>,
    nodes: &Vec<Node>,
    toks: &Vec<DTok>,
    gaps: &Vec<Ins>,
    by_start: &Vec<usize>,
    m: usize,
    Ghost(ts): Ghost<Stream>,
    Ghost(cx): Ghost<Ctx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        m < nodes.len(),
        env_ok(src@, nodes@, toks@, gaps@, ts),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(arena_of(nodes@), ts, m as int, cx, l0 as int, h0 as int)
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
    if !matches!(nd.kind, NodeKind::EmptyStatement) || !nd.children.is_empty() {
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
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, ts, x as int);
        assert(t == &toks@[x as int]);
    }
    if !matches!(t.kind, TokKind::Punctuator) || !text_is1(src, t, 0x3B) || t.start != nd.start
        || t.end != nd.end {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, ts);
        assert(a.nodes[m as int].children.len() == 0);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(ts.toks[x as int].kind == TokKind::Punctuator);
        assert(ts.toks[x as int].text =~= seq![0x3Bu32]);
        assert(x < toks.len());
        assert(toks.len() <= usize::MAX);
        lemma_empty_done(a, ts, cx, m as int, x as int);
    }
    Some((x, x.saturating_add(1), -100))
}

/// An `EmptyStatement` of the check.
proof fn lemma_empty_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= x < tn(ts),
        a.nodes[m].kind == NodeKind::EmptyStatement,
        a.nodes[m].children.len() == 0,
        ts.toks[x].kind == TokKind::Punctuator,
        ts.toks[x].text =~= seq![0x3Bu32],
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[x].end,
    ensures
        node_done(a, ts, m, cx, x, x + 1),
        lvl(a, m) == -100,
{
    lemma_punct_text();
    assert(is_p(ts, x, ";"@));
    assert(span_ok(a, ts, m, x, x + 1));
    lemma_empty_statement_derives(a, ts, m, cx, x);
    lemma_ed_of(a, ts, m, x, x + 1);
}

} // verus!
