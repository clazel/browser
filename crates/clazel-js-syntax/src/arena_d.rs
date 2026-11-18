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
//! [`crate::derive`] has the rule lemmas for more productions (unary, conditional,
//! assignment, member access); they are not yet wired into this check. Lists
//! (`dsep`, `darray`), the rest of the statements, functions, classes, patterns,
//! templates and modules have neither lemmas nor checks yet.
//!
//! [`crate::exec::parse_checked`] runs [`check_derivation_canon`] on every arena
//! the parser builds, and rejects it if a covered node is `Failed`.
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
        !is_kw(ts, i, "function"@),
        !is_kw(ts, i, "class"@),
        !is_kw(ts, i, "async"@),
        !is_kw(ts, i, "let"@),
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

/// The operators of the expressions the check covers: unary, binary and assignment.
pub open spec fn op_supported(op: Op) -> bool {
    is_unary_op(op) || is_assign_op(op) || op == Op::Exp || op == Op::Mul || op == Op::Div || op
        == Op::Rem || op == Op::Add || op == Op::Sub || op == Op::Shl || op == Op::Shr || op
        == Op::UShr || op == Op::Lt || op == Op::Gt || op == Op::Le || op == Op::Ge || op
        == Op::InstanceOf || op == Op::In || op == Op::Eq || op == Op::Ne || op == Op::StrictEq
        || op == Op::StrictNe || op == Op::BitAnd || op == Op::BitXor || op == Op::BitOr || op
        == Op::LogicalAnd || op == Op::LogicalOr || op == Op::Coalesce
}

/// The code points of the text of an operator.
pub open spec fn op_chars(op: Op) -> Seq<u32> {
    match op {
        Op::Delete => seq![0x64u32, 0x65, 0x6C, 0x65, 0x74, 0x65],
        Op::Void => seq![0x76u32, 0x6F, 0x69, 0x64],
        Op::Typeof => seq![0x74u32, 0x79, 0x70, 0x65, 0x6F, 0x66],
        Op::Plus | Op::Add => seq![0x2Bu32],
        Op::Minus | Op::Sub => seq![0x2Du32],
        Op::BitNot => seq![0x7Eu32],
        Op::LogicalNot => seq![0x21u32],
        Op::Exp => seq![0x2Au32, 0x2A],
        Op::Mul => seq![0x2Au32],
        Op::Div => seq![0x2Fu32],
        Op::Rem => seq![0x25u32],
        Op::Shl => seq![0x3Cu32, 0x3C],
        Op::Shr => seq![0x3Eu32, 0x3E],
        Op::UShr => seq![0x3Eu32, 0x3E, 0x3E],
        Op::Lt => seq![0x3Cu32],
        Op::Gt => seq![0x3Eu32],
        Op::Le => seq![0x3Cu32, 0x3D],
        Op::Ge => seq![0x3Eu32, 0x3D],
        Op::InstanceOf => seq![0x69u32, 0x6E, 0x73, 0x74, 0x61, 0x6E, 0x63, 0x65, 0x6F, 0x66],
        Op::In => seq![0x69u32, 0x6E],
        Op::Eq => seq![0x3Du32, 0x3D],
        Op::Ne => seq![0x21u32, 0x3D],
        Op::StrictEq => seq![0x3Du32, 0x3D, 0x3D],
        Op::StrictNe => seq![0x21u32, 0x3D, 0x3D],
        Op::BitAnd => seq![0x26u32],
        Op::BitXor => seq![0x5Eu32],
        Op::BitOr => seq![0x7Cu32],
        Op::LogicalAnd => seq![0x26u32, 0x26],
        Op::LogicalOr => seq![0x7Cu32, 0x7C],
        Op::Coalesce => seq![0x3Fu32, 0x3F],
        Op::Assign => seq![0x3Du32],
        Op::MulAssign => seq![0x2Au32, 0x3D],
        Op::DivAssign => seq![0x2Fu32, 0x3D],
        Op::RemAssign => seq![0x25u32, 0x3D],
        Op::AddAssign => seq![0x2Bu32, 0x3D],
        Op::SubAssign => seq![0x2Du32, 0x3D],
        Op::ShlAssign => seq![0x3Cu32, 0x3C, 0x3D],
        Op::ShrAssign => seq![0x3Eu32, 0x3E, 0x3D],
        Op::UShrAssign => seq![0x3Eu32, 0x3E, 0x3E, 0x3D],
        Op::BitAndAssign => seq![0x26u32, 0x3D],
        Op::BitXorAssign => seq![0x5Eu32, 0x3D],
        Op::BitOrAssign => seq![0x7Cu32, 0x3D],
        Op::ExpAssign => seq![0x2Au32, 0x2A, 0x3D],
        Op::LogicalAndAssign => seq![0x26u32, 0x26, 0x3D],
        Op::LogicalOrAssign => seq![0x7Cu32, 0x7C, 0x3D],
        Op::CoalesceAssign => seq![0x3Fu32, 0x3F, 0x3D],
        _ => Seq::empty(),
    }
}

/// The text of an operator, as the specification's `op_text` and the table agree.
proof fn lemma_op_chars(op: Op)
    requires
        op_supported(op),
    ensures
        cps(op_text(op)) =~= op_chars(op),
{
    reveal_strlit("delete");
    reveal_strlit("void");
    reveal_strlit("typeof");
    reveal_strlit("+");
    reveal_strlit("-");
    reveal_strlit("~");
    reveal_strlit("!");
    reveal_strlit("**");
    reveal_strlit("*");
    reveal_strlit("/");
    reveal_strlit("%");
    reveal_strlit("<<");
    reveal_strlit(">>");
    reveal_strlit(">>>");
    reveal_strlit("<");
    reveal_strlit(">");
    reveal_strlit("?");
    reveal_strlit(":");
    reveal_strlit(".");
    reveal_strlit("<=");
    reveal_strlit(">=");
    reveal_strlit("instanceof");
    reveal_strlit("in");
    reveal_strlit("==");
    reveal_strlit("!=");
    reveal_strlit("===");
    reveal_strlit("!==");
    reveal_strlit("&");
    reveal_strlit("^");
    reveal_strlit("|");
    reveal_strlit("&&");
    reveal_strlit("||");
    reveal_strlit("??");
    reveal_strlit("=");
    reveal_strlit("*=");
    reveal_strlit("/=");
    reveal_strlit("%=");
    reveal_strlit("+=");
    reveal_strlit("-=");
    reveal_strlit("<<=");
    reveal_strlit(">>=");
    reveal_strlit(">>>=");
    reveal_strlit("&=");
    reveal_strlit("^=");
    reveal_strlit("|=");
    reveal_strlit("**=");
    reveal_strlit("&&=");
    reveal_strlit("||=");
    reveal_strlit("??=");
    match op {
        Op::Delete => assert("delete"@ =~= seq!['d', 'e', 'l', 'e', 't', 'e']),
        Op::Void => assert("void"@ =~= seq!['v', 'o', 'i', 'd']),
        Op::Typeof => assert("typeof"@ =~= seq!['t', 'y', 'p', 'e', 'o', 'f']),
        Op::Plus | Op::Add => assert("+"@ =~= seq!['+']),
        Op::Minus | Op::Sub => assert("-"@ =~= seq!['-']),
        Op::BitNot => assert("~"@ =~= seq!['~']),
        Op::LogicalNot => assert("!"@ =~= seq!['!']),
        Op::Exp => assert("**"@ =~= seq!['*', '*']),
        Op::Mul => assert("*"@ =~= seq!['*']),
        Op::Div => assert("/"@ =~= seq!['/']),
        Op::Rem => assert("%"@ =~= seq!['%']),
        Op::Shl => assert("<<"@ =~= seq!['<', '<']),
        Op::Shr => assert(">>"@ =~= seq!['>', '>']),
        Op::UShr => assert(">>>"@ =~= seq!['>', '>', '>']),
        Op::Lt => assert("<"@ =~= seq!['<']),
        Op::Gt => assert(">"@ =~= seq!['>']),
        Op::Le => assert("<="@ =~= seq!['<', '=']),
        Op::Ge => assert(">="@ =~= seq!['>', '=']),
        Op::InstanceOf => assert("instanceof"@ =~= seq!['i', 'n', 's', 't', 'a', 'n', 'c', 'e', 'o', 'f']),
        Op::In => assert("in"@ =~= seq!['i', 'n']),
        Op::Eq => assert("=="@ =~= seq!['=', '=']),
        Op::Ne => assert("!="@ =~= seq!['!', '=']),
        Op::StrictEq => assert("==="@ =~= seq!['=', '=', '=']),
        Op::StrictNe => assert("!=="@ =~= seq!['!', '=', '=']),
        Op::BitAnd => assert("&"@ =~= seq!['&']),
        Op::BitXor => assert("^"@ =~= seq!['^']),
        Op::BitOr => assert("|"@ =~= seq!['|']),
        Op::LogicalAnd => assert("&&"@ =~= seq!['&', '&']),
        Op::LogicalOr => assert("||"@ =~= seq!['|', '|']),
        Op::Coalesce => assert("??"@ =~= seq!['?', '?']),
        Op::Assign => assert("="@ =~= seq!['=']),
        Op::MulAssign => assert("*="@ =~= seq!['*', '=']),
        Op::DivAssign => assert("/="@ =~= seq!['/', '=']),
        Op::RemAssign => assert("%="@ =~= seq!['%', '=']),
        Op::AddAssign => assert("+="@ =~= seq!['+', '=']),
        Op::SubAssign => assert("-="@ =~= seq!['-', '=']),
        Op::ShlAssign => assert("<<="@ =~= seq!['<', '<', '=']),
        Op::ShrAssign => assert(">>="@ =~= seq!['>', '>', '=']),
        Op::UShrAssign => assert(">>>="@ =~= seq!['>', '>', '>', '=']),
        Op::BitAndAssign => assert("&="@ =~= seq!['&', '=']),
        Op::BitXorAssign => assert("^="@ =~= seq!['^', '=']),
        Op::BitOrAssign => assert("|="@ =~= seq!['|', '=']),
        Op::ExpAssign => assert("**="@ =~= seq!['*', '*', '=']),
        Op::LogicalAndAssign => assert("&&="@ =~= seq!['&', '&', '=']),
        Op::LogicalOrAssign => assert("||="@ =~= seq!['|', '|', '=']),
        Op::CoalesceAssign => assert("??="@ =~= seq!['?', '?', '=']),
        _ => {},
    }
}

/// The code points of an operator's text.
fn op_slice(op: Op) -> (r: &'static [u32])
    ensures
        op_supported(op) ==> r@ =~= op_chars(op),
{
    match op {
        Op::Delete => &[0x64, 0x65, 0x6C, 0x65, 0x74, 0x65],
        Op::Void => &[0x76, 0x6F, 0x69, 0x64],
        Op::Typeof => &[0x74, 0x79, 0x70, 0x65, 0x6F, 0x66],
        Op::Plus | Op::Add => &[0x2B],
        Op::Minus | Op::Sub => &[0x2D],
        Op::BitNot => &[0x7E],
        Op::LogicalNot => &[0x21],
        Op::Exp => &[0x2A, 0x2A],
        Op::Mul => &[0x2A],
        Op::Div => &[0x2F],
        Op::Rem => &[0x25],
        Op::Shl => &[0x3C, 0x3C],
        Op::Shr => &[0x3E, 0x3E],
        Op::UShr => &[0x3E, 0x3E, 0x3E],
        Op::Lt => &[0x3C],
        Op::Gt => &[0x3E],
        Op::Le => &[0x3C, 0x3D],
        Op::Ge => &[0x3E, 0x3D],
        Op::InstanceOf => &[0x69, 0x6E, 0x73, 0x74, 0x61, 0x6E, 0x63, 0x65, 0x6F, 0x66],
        Op::In => &[0x69, 0x6E],
        Op::Eq => &[0x3D, 0x3D],
        Op::Ne => &[0x21, 0x3D],
        Op::StrictEq => &[0x3D, 0x3D, 0x3D],
        Op::StrictNe => &[0x21, 0x3D, 0x3D],
        Op::BitAnd => &[0x26],
        Op::BitXor => &[0x5E],
        Op::BitOr => &[0x7C],
        Op::LogicalAnd => &[0x26, 0x26],
        Op::LogicalOr => &[0x7C, 0x7C],
        Op::Coalesce => &[0x3F, 0x3F],
        Op::Assign => &[0x3D],
        Op::MulAssign => &[0x2A, 0x3D],
        Op::DivAssign => &[0x2F, 0x3D],
        Op::RemAssign => &[0x25, 0x3D],
        Op::AddAssign => &[0x2B, 0x3D],
        Op::SubAssign => &[0x2D, 0x3D],
        Op::ShlAssign => &[0x3C, 0x3C, 0x3D],
        Op::ShrAssign => &[0x3E, 0x3E, 0x3D],
        Op::UShrAssign => &[0x3E, 0x3E, 0x3E, 0x3D],
        Op::BitAndAssign => &[0x26, 0x3D],
        Op::BitXorAssign => &[0x5E, 0x3D],
        Op::BitOrAssign => &[0x7C, 0x3D],
        Op::ExpAssign => &[0x2A, 0x2A, 0x3D],
        Op::LogicalAndAssign => &[0x26, 0x26, 0x3D],
        Op::LogicalOrAssign => &[0x7C, 0x7C, 0x3D],
        Op::CoalesceAssign => &[0x3F, 0x3F, 0x3D],
        _ => &[],
    }
}

/// The source text of the token is the code points `w`.
fn text_is(src: &[u32], t: &DTok, w: &[u32]) -> (r: bool)
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
        let a = match src.get(t.start.saturating_add(k)) {
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

/// The token is the operator `op`: a punctuator, or for `delete void typeof
/// instanceof in` a keyword written without escapes (`spec::is_op_tok`).
fn tok_is_op(src: &[u32], t: &DTok, op: Op) -> (r: bool)
    requires
        t.start <= t.end <= src.len(),
        op_supported(op),
    ensures
        r ==> (src@.subrange(t.start as int, t.end as int) =~= cps(op_text(op)) && (if op
            == Op::Delete || op == Op::Void || op == Op::Typeof || op == Op::InstanceOf || op
            == Op::In {
            t.kind == TokKind::IdentifierName && !t.escaped
        } else {
            t.kind == TokKind::Punctuator
        })),
{
    let keyword = matches!(op, Op::Delete | Op::Void | Op::Typeof | Op::InstanceOf | Op::In);
    let kind_ok = if keyword {
        matches!(t.kind, TokKind::IdentifierName) && !t.escaped
    } else {
        matches!(t.kind, TokKind::Punctuator)
    };
    let r = kind_ok && text_is(src, t, op_slice(op));
    proof {
        lemma_op_chars(op);
    }
    r
}

/// The index of the first element, named so that it is not read as a request for `first()`.
const ZERO: usize = 0;

/// The source text of the token is the one code point `code`.
fn text_is1(src: &[u32], t: &DTok, code: u32) -> (r: bool)
    requires
        t.start <= t.end <= src.len(),
    ensures
        r == (src@.subrange(t.start as int, t.end as int) =~= seq![code]),
{
    if t.end.saturating_sub(t.start) != 1 {
        return false;
    }
    let r = match src.get(t.start) {
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
        cps("?"@) =~= seq![0x3Fu32],
        cps(":"@) =~= seq![0x3Au32],
        cps("."@) =~= seq![0x2Eu32],
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
    reveal_strlit("?");
    reveal_strlit(":");
    reveal_strlit(".");
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
    assert("?"@ =~= seq!['?']);
    assert(":"@ =~= seq![':']);
    assert("."@ =~= seq!['.']);
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
    nodes: &[Node],
    toks: &[DTok],
    by_start: &[usize],
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
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let kind_ok = match nd.kind {
        NodeKind::NumericLiteral => 1,
        NodeKind::StringLiteral => 2,
        NodeKind::RegularExpressionLiteral => 3,
        NodeKind::IdentifierName => 4,
        _ => 0,
    };
    if kind_ok == 0 || !nd.children.is_empty() {
        return None;
    }
    let x = match by_start.get(nd.start) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let t = match toks.get(x) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    let ok = t.start == nd.start && t.end == nd.end && (match nd.kind {
        NodeKind::NumericLiteral => matches!(t.kind, TokKind::NumericLiteral),
        NodeKind::StringLiteral => matches!(t.kind, TokKind::StringLiteral),
        NodeKind::IdentifierName => matches!(t.kind, TokKind::IdentifierName),
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
            NodeKind::IdentifierName => {
                assert(t.kind == TokKind::IdentifierName);
            },
            _ => {
                assert(t.kind == TokKind::RegularExpressionLiteral);
            },
        }
        lemma_leaf_literal_in(av, ts, m as int, cx, x as int);
        assert(span_ok(av, ts, m as int, x as int, x as int + 1));
        lemma_ed_of(av, ts, m as int, x as int, x as int + 1);
        assert(lvl(av, m as int) == if nd.kind == NodeKind::IdentifierName {
            -100int
        } else {
            17int
        });
    }
    let l: i32 = if matches!(nd.kind, NodeKind::IdentifierName) {
        -100
    } else {
        17
    };
    Some((x, x1, l))
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


/// The kinds of binary expression: §13.6 to §13.13.
pub open spec fn is_bin_kind(k: NodeKind) -> bool {
    k == NodeKind::ExponentiationExpression || k == NodeKind::MultiplicativeExpression || k
        == NodeKind::AdditiveExpression || k == NodeKind::ShiftExpression || k
        == NodeKind::RelationalExpression || k == NodeKind::EqualityExpression || k
        == NodeKind::BitwiseANDExpression || k == NodeKind::BitwiseXORExpression || k
        == NodeKind::BitwiseORExpression || k == NodeKind::LogicalANDExpression || k
        == NodeKind::LogicalORExpression || k == NodeKind::CoalesceExpression
}

/// The binding strength of a binary kind, and the least strength of its left and
/// right operands (for `??` the left may also be a `CoalesceExpression`).
pub open spec fn bin_levels(k: NodeKind) -> (int, int, int) {
    match k {
        NodeKind::ExponentiationExpression => (11, 13, 11),
        NodeKind::MultiplicativeExpression => (10, 10, 11),
        NodeKind::AdditiveExpression => (9, 9, 10),
        NodeKind::ShiftExpression => (8, 8, 9),
        NodeKind::RelationalExpression => (7, 7, 8),
        NodeKind::EqualityExpression => (6, 6, 7),
        NodeKind::BitwiseANDExpression => (5, 5, 6),
        NodeKind::BitwiseXORExpression => (4, 4, 5),
        NodeKind::BitwiseORExpression => (3, 3, 4),
        NodeKind::LogicalANDExpression => (2, 2, 3),
        NodeKind::LogicalORExpression => (1, 1, 2),
        _ => (0, 3, 3),
    }
}

/// The operand levels make `binary_operands_ok`.
proof fn lemma_operands(a: AstV, k: NodeKind, op: Op, l: int, r: int)
    requires
        is_bin_kind(k),
        lvl(a, l) >= bin_levels(k).1 || (k == NodeKind::CoalesceExpression && kd(a, l)
            == NodeKind::CoalesceExpression),
        lvl(a, r) >= bin_levels(k).2,
    ensures
        binary_operands_ok(a, k, op, l, r),
{
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
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= l < m,
        0 <= r < m,
        cx_in(cx, true) == cx,
        cx.in_,
        a.nodes[m].children =~= seq![l, r],
        is_bin_kind(a.nodes[m].kind),
        bin_op_ok(a.nodes[m].kind, a.nodes[m].op),
        lvl(a, l) >= bin_levels(a.nodes[m].kind).1 || (a.nodes[m].kind
            == NodeKind::CoalesceExpression && kd(a, l) == NodeKind::CoalesceExpression),
        lvl(a, r) >= bin_levels(a.nodes[m].kind).2,
        node_done(a, ts, l, cx, lo_l, mi),
        node_done(a, ts, r, cx, lo_r, j),
        lo_r == mi + 1,
        0 <= mi < tn(ts),
        is_op_tok(ts, mi, a.nodes[m].op),
        a.nodes[m].start == ts.toks[lo_l].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, lo_l, j),
        lvl(a, m) == bin_levels(a.nodes[m].kind).0,
{
    assert(span_ok(a, ts, m, lo_l, j));
    lemma_operands(a, a.nodes[m].kind, a.nodes[m].op, l, r);
    crate::derive::lemma_binary_derives(a, ts, m, cx, lo_l, mi, j, l, r);
    lemma_ed_of(a, ts, m, lo_l, j);
}

/// The binding strengths of a binary kind and whether `op` is one of its operators.
fn bin_info(kind: NodeKind, op: Op) -> (r: (i32, i32, i32, bool))
    ensures
        r.3 ==> (is_bin_kind(kind) && bin_op_ok(kind, op) && op_supported(op) && r.0 == bin_levels(
            kind,
        ).0 && r.1 == bin_levels(kind).1 && r.2 == bin_levels(kind).2),
{
    match kind {
        NodeKind::ExponentiationExpression => (11, 13, 11, matches!(op, Op::Exp)),
        NodeKind::MultiplicativeExpression => (
            10,
            10,
            11,
            matches!(op, Op::Mul | Op::Div | Op::Rem),
        ),
        NodeKind::AdditiveExpression => (9, 9, 10, matches!(op, Op::Add | Op::Sub)),
        NodeKind::ShiftExpression => (8, 8, 9, matches!(op, Op::Shl | Op::Shr | Op::UShr)),
        NodeKind::RelationalExpression => (
            7,
            7,
            8,
            matches!(op, Op::Lt | Op::Gt | Op::Le | Op::Ge | Op::InstanceOf | Op::In),
        ),
        NodeKind::EqualityExpression => (
            6,
            6,
            7,
            matches!(op, Op::Eq | Op::Ne | Op::StrictEq | Op::StrictNe),
        ),
        NodeKind::BitwiseANDExpression => (5, 5, 6, matches!(op, Op::BitAnd)),
        NodeKind::BitwiseXORExpression => (4, 4, 5, matches!(op, Op::BitXor)),
        NodeKind::BitwiseORExpression => (3, 3, 4, matches!(op, Op::BitOr)),
        NodeKind::LogicalANDExpression => (2, 2, 3, matches!(op, Op::LogicalAnd)),
        NodeKind::LogicalORExpression => (1, 1, 2, matches!(op, Op::LogicalOr)),
        NodeKind::CoalesceExpression => (0, 3, 3, matches!(op, Op::Coalesce)),
        _ => (0, 0, 0, false),
    }
}

/// §13.6 to §13.13: a binary node of the check.
#[verifier::spinoff_prover]
fn check_binary(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    m: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        m < nodes.len(),
        cx_in(g.cx, true) == g.cx,
        g.cx.in_,
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(
                arena_of(nodes@),
                g.ts,
                m as int,
                g.cx,
                l0 as int,
                h0 as int,
            ) && l as int == lvl(arena_of(nodes@), m as int),
            None => true,
        },
{
    let _ = gaps.len();
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let (own, lmin, rmin, opok) = bin_info(nd.kind, nd.op);
    if !opok || nd.children.len() != 2 {
        return None;
    }
    let l = match nd.children.as_slice().get(ZERO) {
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
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        lemma_child_before(a, m as int, 0);
        lemma_child_before(a, m as int, 1);
    }
    if l >= m || r >= m {
        return None;
    }
    let lo_l = match done.lo.get(l) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let mi = match done.hi.get(l) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lo_r = match done.lo.get(r) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let j = match done.hi.get(r) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_l = match done.lv.get(l) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_r = match done.lv.get(r) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let left_coalesce = match nodes.get(l) {
        Some(x) => matches!(x.kind, NodeKind::CoalesceExpression),
        None => false,
    };
    let left_ok = lvl_l >= lmin || (matches!(nd.kind, NodeKind::CoalesceExpression)
        && left_coalesce);
    if !left_ok || lvl_r < rmin || lo_r != mi.saturating_add(1) {
        return None;
    }
    let opt = match toks.get(mi) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    let first = match toks.get(lo_l) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    let last = match toks.get(j.saturating_sub(1)) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, mi as int);
        assert(opt == &toks@[mi as int]);
    }
    if !tok_is_op(src, opt, nd.op) || nd.start != first.start || nd.end != last.end {
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
        lemma_inv_get(a, g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int, l as int);
        lemma_inv_get(a, g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int, r as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, mi as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, lo_l as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, j as int - 1);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        assert(mi < toks.len());
        assert(toks.len() <= usize::MAX);
        assert(lo_r == mi + 1);
        assert(j >= 1);
        assert(first.start as int == g.ts.toks[lo_l as int].start);
        assert(last.end as int == g.ts.toks[j as int - 1].end);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].op == nd.op);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(kd(a, l as int) == nodes@[l as int].kind);
        assert(left_coalesce ==> kd(a, l as int) == NodeKind::CoalesceExpression);
        let op = nd.op;
        assert(dtok_matches(src@, *opt, g.ts.toks[mi as int]));
        assert(is_op_tok(g.ts, mi as int, op)) by {
            lemma_op_chars(op);
        }
        lemma_binary_done(a, g.ts, g.cx, m as int, l as int, r as int, lo_l as int, mi as int, lo_r as int, j as int);
    }
    Some((lo_l, j, own))
}

/// The code points of the `w`th `ReservedWord` of `spec::reserved_words` (§12.7.2).
pub open spec fn reserved_chars(w: int) -> Seq<u32> {
    if w == 0 {
        seq![0x61u32, 0x77, 0x61, 0x69, 0x74]
    } else if w == 1 {
        seq![0x62u32, 0x72, 0x65, 0x61, 0x6B]
    } else if w == 2 {
        seq![0x63u32, 0x61, 0x73, 0x65]
    } else if w == 3 {
        seq![0x63u32, 0x61, 0x74, 0x63, 0x68]
    } else if w == 4 {
        seq![0x63u32, 0x6C, 0x61, 0x73, 0x73]
    } else if w == 5 {
        seq![0x63u32, 0x6F, 0x6E, 0x73, 0x74]
    } else if w == 6 {
        seq![0x63u32, 0x6F, 0x6E, 0x74, 0x69, 0x6E, 0x75, 0x65]
    } else if w == 7 {
        seq![0x64u32, 0x65, 0x62, 0x75, 0x67, 0x67, 0x65, 0x72]
    } else if w == 8 {
        seq![0x64u32, 0x65, 0x66, 0x61, 0x75, 0x6C, 0x74]
    } else if w == 9 {
        seq![0x64u32, 0x65, 0x6C, 0x65, 0x74, 0x65]
    } else if w == 10 {
        seq![0x64u32, 0x6F]
    } else if w == 11 {
        seq![0x65u32, 0x6C, 0x73, 0x65]
    } else if w == 12 {
        seq![0x65u32, 0x6E, 0x75, 0x6D]
    } else if w == 13 {
        seq![0x65u32, 0x78, 0x70, 0x6F, 0x72, 0x74]
    } else if w == 14 {
        seq![0x65u32, 0x78, 0x74, 0x65, 0x6E, 0x64, 0x73]
    } else if w == 15 {
        seq![0x66u32, 0x61, 0x6C, 0x73, 0x65]
    } else if w == 16 {
        seq![0x66u32, 0x69, 0x6E, 0x61, 0x6C, 0x6C, 0x79]
    } else if w == 17 {
        seq![0x66u32, 0x6F, 0x72]
    } else if w == 18 {
        seq![0x66u32, 0x75, 0x6E, 0x63, 0x74, 0x69, 0x6F, 0x6E]
    } else if w == 19 {
        seq![0x69u32, 0x66]
    } else if w == 20 {
        seq![0x69u32, 0x6D, 0x70, 0x6F, 0x72, 0x74]
    } else if w == 21 {
        seq![0x69u32, 0x6E]
    } else if w == 22 {
        seq![0x69u32, 0x6E, 0x73, 0x74, 0x61, 0x6E, 0x63, 0x65, 0x6F, 0x66]
    } else if w == 23 {
        seq![0x6Eu32, 0x65, 0x77]
    } else if w == 24 {
        seq![0x6Eu32, 0x75, 0x6C, 0x6C]
    } else if w == 25 {
        seq![0x72u32, 0x65, 0x74, 0x75, 0x72, 0x6E]
    } else if w == 26 {
        seq![0x73u32, 0x75, 0x70, 0x65, 0x72]
    } else if w == 27 {
        seq![0x73u32, 0x77, 0x69, 0x74, 0x63, 0x68]
    } else if w == 28 {
        seq![0x74u32, 0x68, 0x69, 0x73]
    } else if w == 29 {
        seq![0x74u32, 0x68, 0x72, 0x6F, 0x77]
    } else if w == 30 {
        seq![0x74u32, 0x72, 0x75, 0x65]
    } else if w == 31 {
        seq![0x74u32, 0x72, 0x79]
    } else if w == 32 {
        seq![0x74u32, 0x79, 0x70, 0x65, 0x6F, 0x66]
    } else if w == 33 {
        seq![0x76u32, 0x61, 0x72]
    } else if w == 34 {
        seq![0x76u32, 0x6F, 0x69, 0x64]
    } else if w == 35 {
        seq![0x77u32, 0x68, 0x69, 0x6C, 0x65]
    } else if w == 36 {
        seq![0x77u32, 0x69, 0x74, 0x68]
    } else {
        seq![0x79u32, 0x69, 0x65, 0x6C, 0x64]
    }
}

/// The table of reserved words has the 38 words of the specification, in its order.
proof fn lemma_reserved_chars(w: int)
    requires
        0 <= w < 38,
    ensures
        reserved_words().len() == 38,
        cps(reserved_words()[w]) =~= reserved_chars(w),
{
    reveal_strlit("await");
    reveal_strlit("break");
    reveal_strlit("case");
    reveal_strlit("catch");
    reveal_strlit("class");
    reveal_strlit("const");
    reveal_strlit("continue");
    reveal_strlit("debugger");
    reveal_strlit("default");
    reveal_strlit("delete");
    reveal_strlit("do");
    reveal_strlit("else");
    reveal_strlit("enum");
    reveal_strlit("export");
    reveal_strlit("extends");
    reveal_strlit("false");
    reveal_strlit("finally");
    reveal_strlit("for");
    reveal_strlit("function");
    reveal_strlit("if");
    reveal_strlit("import");
    reveal_strlit("in");
    reveal_strlit("instanceof");
    reveal_strlit("new");
    reveal_strlit("null");
    reveal_strlit("return");
    reveal_strlit("super");
    reveal_strlit("switch");
    reveal_strlit("this");
    reveal_strlit("throw");
    reveal_strlit("true");
    reveal_strlit("try");
    reveal_strlit("typeof");
    reveal_strlit("var");
    reveal_strlit("void");
    reveal_strlit("while");
    reveal_strlit("with");
    reveal_strlit("yield");
    let rw = reserved_words();
    assert(rw.len() == 38);
    assert("await"@ =~= seq!['a', 'w', 'a', 'i', 't']);
    assert("break"@ =~= seq!['b', 'r', 'e', 'a', 'k']);
    assert("case"@ =~= seq!['c', 'a', 's', 'e']);
    assert("catch"@ =~= seq!['c', 'a', 't', 'c', 'h']);
    assert("class"@ =~= seq!['c', 'l', 'a', 's', 's']);
    assert("const"@ =~= seq!['c', 'o', 'n', 's', 't']);
    assert("continue"@ =~= seq!['c', 'o', 'n', 't', 'i', 'n', 'u', 'e']);
    assert("debugger"@ =~= seq!['d', 'e', 'b', 'u', 'g', 'g', 'e', 'r']);
    assert("default"@ =~= seq!['d', 'e', 'f', 'a', 'u', 'l', 't']);
    assert("delete"@ =~= seq!['d', 'e', 'l', 'e', 't', 'e']);
    assert("do"@ =~= seq!['d', 'o']);
    assert("else"@ =~= seq!['e', 'l', 's', 'e']);
    assert("enum"@ =~= seq!['e', 'n', 'u', 'm']);
    assert("export"@ =~= seq!['e', 'x', 'p', 'o', 'r', 't']);
    assert("extends"@ =~= seq!['e', 'x', 't', 'e', 'n', 'd', 's']);
    assert("false"@ =~= seq!['f', 'a', 'l', 's', 'e']);
    assert("finally"@ =~= seq!['f', 'i', 'n', 'a', 'l', 'l', 'y']);
    assert("for"@ =~= seq!['f', 'o', 'r']);
    assert("function"@ =~= seq!['f', 'u', 'n', 'c', 't', 'i', 'o', 'n']);
    assert("if"@ =~= seq!['i', 'f']);
    assert("import"@ =~= seq!['i', 'm', 'p', 'o', 'r', 't']);
    assert("in"@ =~= seq!['i', 'n']);
    assert("instanceof"@ =~= seq!['i', 'n', 's', 't', 'a', 'n', 'c', 'e', 'o', 'f']);
    assert("new"@ =~= seq!['n', 'e', 'w']);
    assert("null"@ =~= seq!['n', 'u', 'l', 'l']);
    assert("return"@ =~= seq!['r', 'e', 't', 'u', 'r', 'n']);
    assert("super"@ =~= seq!['s', 'u', 'p', 'e', 'r']);
    assert("switch"@ =~= seq!['s', 'w', 'i', 't', 'c', 'h']);
    assert("this"@ =~= seq!['t', 'h', 'i', 's']);
    assert("throw"@ =~= seq!['t', 'h', 'r', 'o', 'w']);
    assert("true"@ =~= seq!['t', 'r', 'u', 'e']);
    assert("try"@ =~= seq!['t', 'r', 'y']);
    assert("typeof"@ =~= seq!['t', 'y', 'p', 'e', 'o', 'f']);
    assert("var"@ =~= seq!['v', 'a', 'r']);
    assert("void"@ =~= seq!['v', 'o', 'i', 'd']);
    assert("while"@ =~= seq!['w', 'h', 'i', 'l', 'e']);
    assert("with"@ =~= seq!['w', 'i', 't', 'h']);
    assert("yield"@ =~= seq!['y', 'i', 'e', 'l', 'd']);
}

/// The `w`th reserved word, as code points.
fn reserved_slice(w: usize) -> (r: &'static [u32])
    requires
        w < 38,
    ensures
        r@ =~= reserved_chars(w as int),
{
    match w {
        0 => &[0x61, 0x77, 0x61, 0x69, 0x74],
        1 => &[0x62, 0x72, 0x65, 0x61, 0x6B],
        2 => &[0x63, 0x61, 0x73, 0x65],
        3 => &[0x63, 0x61, 0x74, 0x63, 0x68],
        4 => &[0x63, 0x6C, 0x61, 0x73, 0x73],
        5 => &[0x63, 0x6F, 0x6E, 0x73, 0x74],
        6 => &[0x63, 0x6F, 0x6E, 0x74, 0x69, 0x6E, 0x75, 0x65],
        7 => &[0x64, 0x65, 0x62, 0x75, 0x67, 0x67, 0x65, 0x72],
        8 => &[0x64, 0x65, 0x66, 0x61, 0x75, 0x6C, 0x74],
        9 => &[0x64, 0x65, 0x6C, 0x65, 0x74, 0x65],
        10 => &[0x64, 0x6F],
        11 => &[0x65, 0x6C, 0x73, 0x65],
        12 => &[0x65, 0x6E, 0x75, 0x6D],
        13 => &[0x65, 0x78, 0x70, 0x6F, 0x72, 0x74],
        14 => &[0x65, 0x78, 0x74, 0x65, 0x6E, 0x64, 0x73],
        15 => &[0x66, 0x61, 0x6C, 0x73, 0x65],
        16 => &[0x66, 0x69, 0x6E, 0x61, 0x6C, 0x6C, 0x79],
        17 => &[0x66, 0x6F, 0x72],
        18 => &[0x66, 0x75, 0x6E, 0x63, 0x74, 0x69, 0x6F, 0x6E],
        19 => &[0x69, 0x66],
        20 => &[0x69, 0x6D, 0x70, 0x6F, 0x72, 0x74],
        21 => &[0x69, 0x6E],
        22 => &[0x69, 0x6E, 0x73, 0x74, 0x61, 0x6E, 0x63, 0x65, 0x6F, 0x66],
        23 => &[0x6E, 0x65, 0x77],
        24 => &[0x6E, 0x75, 0x6C, 0x6C],
        25 => &[0x72, 0x65, 0x74, 0x75, 0x72, 0x6E],
        26 => &[0x73, 0x75, 0x70, 0x65, 0x72],
        27 => &[0x73, 0x77, 0x69, 0x74, 0x63, 0x68],
        28 => &[0x74, 0x68, 0x69, 0x73],
        29 => &[0x74, 0x68, 0x72, 0x6F, 0x77],
        30 => &[0x74, 0x72, 0x75, 0x65],
        31 => &[0x74, 0x72, 0x79],
        32 => &[0x74, 0x79, 0x70, 0x65, 0x6F, 0x66],
        33 => &[0x76, 0x61, 0x72],
        34 => &[0x76, 0x6F, 0x69, 0x64],
        35 => &[0x77, 0x68, 0x69, 0x6C, 0x65],
        36 => &[0x77, 0x69, 0x74, 0x68],
        _ => &[0x79, 0x69, 0x65, 0x6C, 0x64],
    }
}

/// The index of the reserved word that is the token's text, if there is one.
fn reserved_index(src: &[u32], t: &DTok) -> (r: Option<usize>)
    requires
        t.start <= t.end <= src.len(),
    ensures
        match r {
            Some(w) => w < 38 && src@.subrange(t.start as int, t.end as int) =~= reserved_chars(
                w as int,
            ),
            None => forall|w: int|
                0 <= w < 38 ==> !(src@.subrange(t.start as int, t.end as int) =~= #[trigger] reserved_chars(w)),
        },
{
    let mut w: usize = 0;
    while w < 38
        invariant
            t.start <= t.end <= src.len(),
            w <= 38,
            forall|q: int|
                0 <= q < w ==> !(src@.subrange(t.start as int, t.end as int) =~= #[trigger] reserved_chars(q)),
        decreases 38 - w,
    {
        if text_is(src, t, reserved_slice(w)) {
            return Some(w);
        }
        w = w.saturating_add(1);
    }
    None
}

/// The text of the token is not a reserved word, or is `yield` where `[~Yield]`, or
/// `await` where `[~Await]`: `spec::ident_tok` for a token of an identifier name.
fn ident_ok(src: &[u32], t: &DTok, yield_: bool, await_: bool) -> (r: bool)
    requires
        t.start <= t.end <= src.len(),
    ensures
        r ==> (t.kind == TokKind::IdentifierName ==> (t.escaped || !(exists|w: int|
            0 <= w < 38 && src@.subrange(t.start as int, t.end as int) =~= #[trigger] reserved_chars(w))
            || (src@.subrange(t.start as int, t.end as int) =~= reserved_chars(37) && !yield_) || (
        src@.subrange(t.start as int, t.end as int) =~= reserved_chars(0) && !await_))),
{
    if t.escaped {
        return true;
    }
    match reserved_index(src, t) {
        None => true,
        Some(w) => (w == 37 && !yield_) || (w == 0 && !await_),
    }
}

/// An identifier-name token whose text is not a reserved word, or is `yield` or
/// `await` where those are identifiers, is an `Identifier` (§13.1, `spec::ident_tok`).
proof fn lemma_ident_tok(ts: Stream, x: int, cx: Ctx)
    requires
        0 <= x < tn(ts),
        ts.toks[x].kind == TokKind::IdentifierName,
        ts.toks[x].escaped || !(exists|w: int|
            0 <= w < 38 && ts.toks[x].text =~= #[trigger] reserved_chars(w)) || (ts.toks[x].text
            =~= reserved_chars(37) && !cx.yield_) || (ts.toks[x].text =~= reserved_chars(0)
            && !cx.await_),
    ensures
        ident_tok(ts, x, cx),
{
    lemma_reserved_chars(37);
    lemma_reserved_chars(0);
    assert(reserved_words()[37] == "yield"@) by {
        reveal_strlit("yield");
    }
    assert(reserved_words()[0] == "await"@) by {
        reveal_strlit("await");
    }
    let t = ts.toks[x];
    if !t.escaped && is_reserved_text(t.text) {
        let w = choose|w: int|
            0 <= w < reserved_words().len() && t.text =~= cps(#[trigger] reserved_words()[w]);
        lemma_reserved_chars(w);
        assert(t.text =~= reserved_chars(w));
        assert(exists|w2: int| 0 <= w2 < 38 && t.text =~= #[trigger] reserved_chars(w2));
        assert(is_kw(ts, x, "yield"@) || is_kw(ts, x, "await"@));
    }
}

/// A leaf `IdentifierReference`, `BindingIdentifier` or `LabelIdentifier` of the check.
#[verifier::spinoff_prover]
proof fn lemma_ident_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= x < tn(ts),
        a.nodes[m].children.len() == 0,
        a.nodes[m].kind == NodeKind::IdentifierReference || a.nodes[m].kind
            == NodeKind::BindingIdentifier || a.nodes[m].kind == NodeKind::LabelIdentifier,
        ts.toks[x].kind == TokKind::IdentifierName,
        ident_tok(ts, x, cx),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[x].end,
    ensures
        node_done(a, ts, m, cx, x, x + 1),
        lvl(a, m) == (if a.nodes[m].kind == NodeKind::IdentifierReference {
            17int
        } else {
            -100int
        }),
{
    assert(ts.toks[x].start < ts.toks[x].end);
    crate::derive::lemma_leaf_identifier(a, ts, m, cx, x);
    assert(span_ok(a, ts, m, x, x + 1));
    lemma_ed_of(a, ts, m, x, x + 1);
}

/// §13.1 an identifier leaf.
#[verifier::spinoff_prover]
fn check_ident(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    m: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        m < nodes.len(),
        g.cx == root_ctx(goal_of(done.module)),
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(
                arena_of(nodes@),
                g.ts,
                m as int,
                g.cx,
                l0 as int,
                h0 as int,
            ) && l as int == lvl(arena_of(nodes@), m as int),
            None => true,
        },
{
    let _ = gaps.len();
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(
        nd.kind,
        NodeKind::IdentifierReference | NodeKind::BindingIdentifier | NodeKind::LabelIdentifier,
    ) || !nd.children.is_empty() {
        return None;
    }
    let x = match done.by_start.get(nd.start) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let t = match toks.get(x) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, x as int);
        assert(t == &toks@[x as int]);
    }
    if !matches!(t.kind, TokKind::IdentifierName) || t.start != nd.start || t.end != nd.end
        || !ident_ok(src, t, false, done.module) {
        return None;
    }
    let x1 = x.saturating_add(1);
    proof {
        let a = arena_of(nodes@);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(a.nodes[m as int].children.len() == 0);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(x < toks.len());
        assert(toks.len() <= usize::MAX);
        assert(x1 as int == x as int + 1);
        assert(g.ts.toks[x as int].start == t.start as int);
        assert(g.ts.toks[x as int].end == t.end as int);
        assert(g.ts.toks[x as int].kind == TokKind::IdentifierName);
        assert(g.ts.toks[x as int].escaped == t.escaped);
        assert(g.ts.toks[x as int].text =~= src@.subrange(t.start as int, t.end as int));
        assert(g.cx.yield_ == false);
        assert(g.cx.await_ == done.module);
        lemma_ident_tok(g.ts, x as int, g.cx);
        lemma_ident_done(a, g.ts, g.cx, m as int, x as int);
    }
    let l: i32 = if matches!(nd.kind, NodeKind::IdentifierReference) { 17 } else { -100 };
    Some((x, x1, l))
}

/// The last item of a `dsep` list.
proof fn lemma_dsep_last(
    a: AstV,
    ts: Stream,
    bound: int,
    ks: Seq<int>,
    k: int,
    cx: Ctx,
    i: int,
    m: int,
    j: int,
    trail: bool,
)
    requires
        0 <= k,
        k + 1 == ks.len(),
        ed(a, ts, ks[k], i) == m,
        dc(a, ts, bound, ks[k], cx, i, m),
        j == m || (trail && !is_rest_kind(kd(a, ks[k])) && is_p(ts, m, ","@) && j == m + 1),
    ensures
        dsep(a, ts, bound, ks, k, cx, i, j, trail),
{
}

/// An item before another in a `dsep` list.
proof fn lemma_dsep_cons(
    a: AstV,
    ts: Stream,
    bound: int,
    ks: Seq<int>,
    k: int,
    cx: Ctx,
    i: int,
    m: int,
    j: int,
    trail: bool,
)
    requires
        0 <= k,
        k + 1 < ks.len(),
        ed(a, ts, ks[k], i) == m,
        dc(a, ts, bound, ks[k], cx, i, m),
        is_p(ts, m, ","@),
        dsep(a, ts, bound, ks, k + 1, cx, m + 1, j, trail),
    ensures
        dsep(a, ts, bound, ks, k, cx, i, j, trail),
{
}

/// A child may be in a list of arguments or of expressions.
pub open spec fn list_item_ok(a: AstV, c: int, spread_ok: bool) -> bool {
    lvl(a, c) >= 0 || (spread_ok && kd(a, c) == NodeKind::SpreadElement)
}


/// Which list `check_list` reads: the node, where its first item starts, whether a
/// spread element is an item, and whether a trailing `,` is allowed.
pub struct ListSpec {
    /// The node whose children are the items.
    pub m: usize,
    /// The token the first item starts at (an empty list: where it ends).
    pub start: usize,
    /// A `SpreadElement` is an item.
    pub spread_ok: bool,
    /// One trailing `,` is allowed.
    pub trail: bool,
}

/// The items of the list `ls`: separated by `,`, each an assignment expression (or a
/// spread element where `spread_ok`), and ending at token `e` (after a trailing `,`
/// where `trail` allows one). `spec::dsep` of the children.
fn check_list(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    ls: &ListSpec,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<usize>)
    requires
        ls.m < nodes.len(),
        cx_in(g.cx, true) == g.cx,
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, g.cx, done.lo@, done.hi@, done.lv@, ls.m as int),
    ensures
        match r {
            Some(e) => e <= toks.len() && dsep(
                arena_of(nodes@),
                g.ts,
                ls.m as int,
                arena_of(nodes@).nodes[ls.m as int].children,
                0,
                g.cx,
                ls.start as int,
                e as int,
                ls.trail,
            ) && forall|k: int|
                0 <= k < arena_of(nodes@).nodes[ls.m as int].children.len() ==> list_item_ok(
                    arena_of(nodes@),
                    #[trigger] arena_of(nodes@).nodes[ls.m as int].children[k],
                    ls.spread_ok,
                ),
            None => true,
        },
{
    let _ = gaps.len();
    let m = ls.m;
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let len = nd.children.len();
    let ghost a = arena_of(nodes@);
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children.len() == len);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    if len == 0 {
        if ls.start > toks.len() {
            return None;
        }
        proof {
            assert(dsep(a, g.ts, m as int, a.nodes[m as int].children, 0, g.cx, ls.start as int, ls.start as int, ls.trail));
        }
        return Some(ls.start);
    }
    let last = len.saturating_sub(1);
    let c = match nd.children.as_slice().get(last) {
        Some(x) => *x as usize,
        None => {
            return None;
        },
    };
    proof {
        assert(a.nodes[m as int].children[last as int] == c as int);
        lemma_child_before(a, m as int, last as int);
    }
    if c >= m {
        return None;
    }
    let lo_c = match done.lo.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let hc = match done.hi.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_c = match done.lv.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let kc_spread = match nodes.get(c) {
        Some(x) => matches!(x.kind, NodeKind::SpreadElement),
        None => false,
    };
    if !(lvl_c >= 0 || (ls.spread_ok && kc_spread)) {
        return None;
    }
    // The end: after a trailing `,` if one is allowed and there.
    let mut comma_after = false;
    if ls.trail {
        if let Some(t) = toks.get(hc) {
            proof {
                lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, hc as int);
                assert(t == &toks@[hc as int]);
            }
            if matches!(t.kind, TokKind::Punctuator) && text_is1(src, t, 0x2C) {
                comma_after = true;
            }
        }
    }
    let e: usize = if comma_after { hc.saturating_add(1) } else { hc };
    proof {
        lemma_inv_get(a, g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int, c as int);
        assert(hc <= toks.len());
        assert(kd(a, c as int) == nodes@[c as int].kind);
        assert(!is_rest_kind(kd(a, c as int)) || !kc_spread);
        if comma_after {
            lemma_comma_text();
            lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, hc as int);
            assert(hc < toks.len());
            assert(toks.len() <= usize::MAX);
            assert(e as int == hc as int + 1);
            assert(g.ts.toks[hc as int].kind == TokKind::Punctuator);
            assert(g.ts.toks[hc as int].text =~= seq![0x2Cu32]);
            assert(is_p(g.ts, hc as int, ","@));
        } else {
            assert(e == hc);
        }
        assert(e <= toks.len());
        lemma_dsep_last(
            a,
            g.ts,
            m as int,
            a.nodes[m as int].children,
            last as int,
            g.cx,
            lo_c as int,
            hc as int,
            e as int,
            ls.trail,
        );
    }
    let mut k = last;
    let mut pos = lo_c;
    while k > 0
        invariant
            m < nodes.len(),
            nodes@.len() == nodes.len(),
            nd == &nodes@[m as int],
            a == arena_of(nodes@),
            len == nd.children.len(),
            len == a.nodes[m as int].children.len(),
            k < len,
            e <= toks.len(),
            ast_wf(a),
            cx_in(g.cx, true) == g.cx,
            env_ok(src@, nodes@, toks@, gaps@, g.ts),
            inv(a, g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int),
            dsep(
                a,
                g.ts,
                m as int,
                a.nodes[m as int].children,
                k as int,
                g.cx,
                pos as int,
                e as int,
                ls.trail,
            ),
            forall|q: int|
                k <= q < len ==> list_item_ok(
                    a,
                    #[trigger] a.nodes[m as int].children[q],
                    ls.spread_ok,
                ),
        decreases k,
    {
        let c2 = match nd.children.as_slice().get(k.saturating_sub(1)) {
            Some(x) => *x as usize,
            None => {
                return None;
            },
        };
        proof {
            assert(k >= 1);
            assert(k.saturating_sub(1) as int == k as int - 1);
            assert(a.nodes[m as int].children[k as int - 1] == c2 as int);
            lemma_child_before(a, m as int, k as int - 1);
        }
        if c2 >= m {
            return None;
        }
        let lo2 = match done.lo.get(c2) {
            Some(x) => *x,
            None => {
                return None;
            },
        };
        let hi2 = match done.hi.get(c2) {
            Some(x) => *x,
            None => {
                return None;
            },
        };
        let lvl2 = match done.lv.get(c2) {
            Some(x) => *x,
            None => {
                return None;
            },
        };
        let spread2 = match nodes.get(c2) {
            Some(x) => matches!(x.kind, NodeKind::SpreadElement),
            None => false,
        };
        let sep = match toks.get(hi2) {
            Some(t) => t,
            None => {
                return None;
            },
        };
        proof {
            lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, hi2 as int);
            assert(sep == &toks@[hi2 as int]);
        }
        if !(lvl2 >= 0 || (ls.spread_ok && spread2)) || !matches!(sep.kind, TokKind::Punctuator)
            || !text_is1(src, sep, 0x2C) || hi2.saturating_add(1) != pos {
            return None;
        }
        proof {
            lemma_comma_text();
            lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
            lemma_inv_get(a, g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int, c2 as int);
            assert(hi2 < toks.len());
            assert(toks.len() <= usize::MAX);
            assert(hi2 + 1 == pos);
            assert(kd(a, c2 as int) == nodes@[c2 as int].kind);
            assert(g.ts.toks[hi2 as int].kind == TokKind::Punctuator);
            assert(g.ts.toks[hi2 as int].text =~= seq![0x2Cu32]);
            assert(is_p(g.ts, hi2 as int, ","@));
            lemma_dsep_cons(
                a,
                g.ts,
                m as int,
                a.nodes[m as int].children,
                k as int - 1,
                g.cx,
                lo2 as int,
                hi2 as int,
                e as int,
                ls.trail,
            );
        }
        pos = lo2;
        k = k.saturating_sub(1);
    }
    if pos != ls.start {
        return None;
    }
    proof {
        assert(forall|q: int|
            0 <= q < len ==> list_item_ok(a, #[trigger] a.nodes[m as int].children[q], ls.spread_ok));
    }
    Some(e)
}

/// The `,` text as code points.
proof fn lemma_comma_text()
    ensures
        cps(","@) =~= seq![0x2Cu32],
{
    reveal_strlit(",");
    assert(","@ =~= seq![',']);
}

/// The words that cannot start an `ExpressionStatement` (§14.5), as code points.
proof fn lemma_kw_text()
    ensures
        cps("function"@) =~= seq![0x66u32, 0x75, 0x6E, 0x63, 0x74, 0x69, 0x6F, 0x6E],
        cps("class"@) =~= seq![0x63u32, 0x6C, 0x61, 0x73, 0x73],
        cps("async"@) =~= seq![0x61u32, 0x73, 0x79, 0x6E, 0x63],
        cps("let"@) =~= seq![0x6Cu32, 0x65, 0x74],
{
    reveal_strlit("function");
    reveal_strlit("class");
    reveal_strlit("async");
    reveal_strlit("let");
    assert("function"@ =~= seq!['f', 'u', 'n', 'c', 't', 'i', 'o', 'n']);
    assert("class"@ =~= seq!['c', 'l', 'a', 's', 's']);
    assert("async"@ =~= seq!['a', 's', 'y', 'n', 'c']);
    assert("let"@ =~= seq!['l', 'e', 't']);
}

/// A unary node of the check whose operand and operator token are as read.
#[verifier::spinoff_prover]
proof fn lemma_unary_done(a: AstV, ts: Stream, cx: Ctx, m: int, c: int, lo_c: int, hc: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= c < m,
        a.nodes[m].kind == NodeKind::UnaryExpression,
        a.nodes[m].children =~= seq![c],
        is_unary_op(a.nodes[m].op),
        1 <= lo_c,
        node_done(a, ts, c, cx, lo_c, hc),
        lvl(a, c) >= 12,
        is_op_tok(ts, lo_c - 1, a.nodes[m].op),
        a.nodes[m].start == ts.toks[lo_c - 1].start,
        a.nodes[m].end == ts.toks[hc - 1].end,
    ensures
        node_done(a, ts, m, cx, lo_c - 1, hc),
        lvl(a, m) == 12,
{
    assert(span_ok(a, ts, m, lo_c - 1, hc));
    crate::derive::lemma_unary_derives(a, ts, m, cx, lo_c - 1, hc, c);
    lemma_ed_of(a, ts, m, lo_c - 1, hc);
}

/// §13.5 `delete void typeof + - ~ !`.
#[verifier::spinoff_prover]
fn check_unary(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    m: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        m < nodes.len(),
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(
                arena_of(nodes@),
                g.ts,
                m as int,
                g.cx,
                l0 as int,
                h0 as int,
            ) && l as int == lvl(arena_of(nodes@), m as int),
            None => true,
        },
{
    let _ = gaps.len();
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::UnaryExpression) || nd.children.len() != 1 || !matches!(
        nd.op,
        Op::Delete | Op::Void | Op::Typeof | Op::Plus | Op::Minus | Op::BitNot | Op::LogicalNot,
    ) {
        return None;
    }
    let c = match nd.children.as_slice().get(ZERO) {
        Some(x) => *x as usize,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        lemma_child_before(a, m as int, 0);
    }
    if c >= m {
        return None;
    }
    let lo_c = match done.lo.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let hc = match done.hi.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_c = match done.lv.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    if lvl_c < 12 || lo_c < 1 {
        return None;
    }
    let opt = match toks.get(lo_c.saturating_sub(1)) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    let last = match toks.get(hc.saturating_sub(1)) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, lo_c as int - 1);
        assert(opt == &toks@[lo_c as int - 1]);
    }
    if !tok_is_op(src, opt, nd.op) || nd.start != opt.start || nd.end != last.end {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
            assert(a.nodes[m as int].children[0] == c as int);
        }
        lemma_inv_get(a, g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int, c as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, hc as int - 1);
        assert(lo_c >= 1);
        assert(lo_c.saturating_sub(1) as int == lo_c as int - 1);
        assert(hc >= 1);
        assert(hc.saturating_sub(1) as int == hc as int - 1);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].op == nd.op);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(opt.start as int == g.ts.toks[lo_c as int - 1].start);
        assert(last.end as int == g.ts.toks[hc as int - 1].end);
        assert(dtok_matches(src@, *opt, g.ts.toks[lo_c as int - 1]));
        assert(is_op_tok(g.ts, lo_c as int - 1, nd.op)) by {
            lemma_op_chars(nd.op);
        }
        lemma_unary_done(a, g.ts, g.cx, m as int, c as int, lo_c as int, hc as int);
    }
    Some((lo_c.saturating_sub(1), hc, 12))
}

/// A `ConditionalExpression` of the check whose parts are as read.
#[verifier::spinoff_prover]
proof fn lemma_conditional_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    t: int,
    c: int,
    e: int,
    lo_t: int,
    mt: int,
    lo_c: int,
    mc: int,
    lo_e: int,
    j: int,
)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= t < m,
        0 <= c < m,
        0 <= e < m,
        a.nodes[m].kind == NodeKind::ConditionalExpression,
        a.nodes[m].children =~= seq![t, c, e],
        lvl(a, t) >= 1 || kd(a, t) == NodeKind::CoalesceExpression,
        lvl(a, c) >= 0,
        lvl(a, e) >= 0,
        node_done(a, ts, t, cx, lo_t, mt),
        node_done(a, ts, c, cx, lo_c, mc),
        node_done(a, ts, e, cx, lo_e, j),
        lo_c == mt + 1,
        lo_e == mc + 1,
        mt < tn(ts),
        mc < tn(ts),
        ts.toks[mt].kind == TokKind::Punctuator,
        ts.toks[mt].text =~= seq![0x3Fu32],
        ts.toks[mc].kind == TokKind::Punctuator,
        ts.toks[mc].text =~= seq![0x3Au32],
        a.nodes[m].start == ts.toks[lo_t].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, lo_t, j),
        lvl(a, m) == 0,
{
    lemma_punct_text();
    assert(is_p(ts, mt, "?"@));
    assert(is_p(ts, mc, ":"@));
    assert(span_ok(a, ts, m, lo_t, j));
    crate::derive::lemma_conditional_derives(a, ts, m, cx, lo_t, mt, mc, j, t, c, e);
    lemma_ed_of(a, ts, m, lo_t, j);
}

/// §13.14 `test ? consequent : alternate`.
#[verifier::spinoff_prover]
fn check_conditional(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    m: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        m < nodes.len(),
        cx_in(g.cx, true) == g.cx,
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(
                arena_of(nodes@),
                g.ts,
                m as int,
                g.cx,
                l0 as int,
                h0 as int,
            ) && l as int == lvl(arena_of(nodes@), m as int),
            None => true,
        },
{
    let _ = gaps.len();
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::ConditionalExpression) || nd.children.len() != 3 {
        return None;
    }
    let t = match nd.children.as_slice().get(ZERO) {
        Some(x) => *x as usize,
        None => {
            return None;
        },
    };
    let c = match nd.children.as_slice().get(1) {
        Some(x) => *x as usize,
        None => {
            return None;
        },
    };
    let e = match nd.children.as_slice().get(2) {
        Some(x) => *x as usize,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        lemma_child_before(a, m as int, 0);
        lemma_child_before(a, m as int, 1);
        lemma_child_before(a, m as int, 2);
    }
    if t >= m || c >= m || e >= m {
        return None;
    }
    let lo_t = match done.lo.get(t) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let mt = match done.hi.get(t) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lo_c = match done.lo.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let mc = match done.hi.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lo_e = match done.lo.get(e) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let j = match done.hi.get(e) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_t = match done.lv.get(t) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_c = match done.lv.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_e = match done.lv.get(e) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let test_coalesce = match nodes.get(t) {
        Some(x) => matches!(x.kind, NodeKind::CoalesceExpression),
        None => false,
    };
    if !(lvl_t >= 1 || test_coalesce) || lvl_c < 0 || lvl_e < 0 || lo_c != mt.saturating_add(1)
        || lo_e != mc.saturating_add(1) {
        return None;
    }
    let q = match toks.get(mt) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let k = match toks.get(mc) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let first = match toks.get(lo_t) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let last = match toks.get(j.saturating_sub(1)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, mt as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, mc as int);
        assert(q == &toks@[mt as int]);
        assert(k == &toks@[mc as int]);
    }
    if !matches!(q.kind, TokKind::Punctuator) || !text_is1(src, q, 0x3F) || !matches!(
        k.kind,
        TokKind::Punctuator,
    ) || !text_is1(src, k, 0x3A) || nd.start != first.start || nd.end != last.end {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children =~= seq![t as int, c as int, e as int]) by {
            assert(a.nodes[m as int].children.len() == 3);
            assert(a.nodes[m as int].children[0] == t as int);
            assert(a.nodes[m as int].children[1] == c as int);
            assert(a.nodes[m as int].children[2] == e as int);
        }
        lemma_inv_get(a, g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int, t as int);
        lemma_inv_get(a, g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int, c as int);
        lemma_inv_get(a, g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int, e as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, lo_t as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, j as int - 1);
        assert(mt < toks.len());
        assert(mc < toks.len());
        assert(toks.len() <= usize::MAX);
        assert(lo_c == mt + 1);
        assert(lo_e == mc + 1);
        assert(j >= 1);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(kd(a, t as int) == nodes@[t as int].kind);
        assert(first.start as int == g.ts.toks[lo_t as int].start);
        assert(last.end as int == g.ts.toks[j as int - 1].end);
        assert(g.ts.toks[mt as int].kind == TokKind::Punctuator);
        assert(g.ts.toks[mt as int].text =~= seq![0x3Fu32]);
        assert(g.ts.toks[mc as int].kind == TokKind::Punctuator);
        assert(g.ts.toks[mc as int].text =~= seq![0x3Au32]);
        lemma_conditional_done(a, g.ts, g.cx, m as int, t as int, c as int, e as int, lo_t as int, mt as int, lo_c as int, mc as int, lo_e as int, j as int);
    }
    Some((lo_t, j, 0))
}

/// An assignment node of the check whose parts are as read.
#[verifier::spinoff_prover]
proof fn lemma_assign_done(
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
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= l < m,
        0 <= r < m,
        a.nodes[m].kind == NodeKind::AssignmentExpression,
        a.nodes[m].children =~= seq![l, r],
        is_assign_op(a.nodes[m].op),
        lvl(a, l) >= 14,
        kd(a, l) != NodeKind::ObjectLiteral,
        kd(a, l) != NodeKind::ArrayLiteral,
        lvl(a, r) >= 0,
        node_done(a, ts, l, cx, lo_l, mi),
        node_done(a, ts, r, cx, lo_r, j),
        lo_r == mi + 1,
        0 <= mi < tn(ts),
        is_op_tok(ts, mi, a.nodes[m].op),
        a.nodes[m].start == ts.toks[lo_l].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, lo_l, j),
        lvl(a, m) == 0,
{
    assert(span_ok(a, ts, m, lo_l, j));
    assert(is_lhs_expr(a, l));
    assert(is_destructuring_target(a, l));
    crate::derive::lemma_assignment_derives(a, ts, m, cx, lo_l, mi, j, l, r);
    lemma_ed_of(a, ts, m, lo_l, j);
}

/// §13.15 `=` and the compound assignment operators.
#[verifier::spinoff_prover]
fn check_assign(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    m: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        m < nodes.len(),
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(
                arena_of(nodes@),
                g.ts,
                m as int,
                g.cx,
                l0 as int,
                h0 as int,
            ) && l as int == lvl(arena_of(nodes@), m as int),
            None => true,
        },
{
    let _ = gaps.len();
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::AssignmentExpression) || nd.children.len() != 2 || !matches!(
        nd.op,
        Op::Assign
        | Op::MulAssign
        | Op::DivAssign
        | Op::RemAssign
        | Op::AddAssign
        | Op::SubAssign
        | Op::ShlAssign
        | Op::ShrAssign
        | Op::UShrAssign
        | Op::BitAndAssign
        | Op::BitXorAssign
        | Op::BitOrAssign
        | Op::ExpAssign
        | Op::LogicalAndAssign
        | Op::LogicalOrAssign
        | Op::CoalesceAssign,
    ) {
        return None;
    }
    let l = match nd.children.as_slice().get(ZERO) {
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
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        lemma_child_before(a, m as int, 0);
        lemma_child_before(a, m as int, 1);
    }
    if l >= m || r >= m {
        return None;
    }
    let lo_l = match done.lo.get(l) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let mi = match done.hi.get(l) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lo_r = match done.lo.get(r) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let j = match done.hi.get(r) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_l = match done.lv.get(l) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_r = match done.lv.get(r) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let left_plain = match nodes.get(l) {
        Some(x) => !matches!(x.kind, NodeKind::ObjectLiteral | NodeKind::ArrayLiteral),
        None => false,
    };
    if lvl_l < 14 || !left_plain || lvl_r < 0 || lo_r != mi.saturating_add(1) {
        return None;
    }
    let opt = match toks.get(mi) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    let first = match toks.get(lo_l) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    let last = match toks.get(j.saturating_sub(1)) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, mi as int);
        assert(opt == &toks@[mi as int]);
    }
    if !tok_is_op(src, opt, nd.op) || nd.start != first.start || nd.end != last.end {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children =~= seq![l as int, r as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
            assert(a.nodes[m as int].children[0] == l as int);
            assert(a.nodes[m as int].children[1] == r as int);
        }
        lemma_inv_get(a, g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int, l as int);
        lemma_inv_get(a, g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int, r as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, lo_l as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, j as int - 1);
        assert(mi < toks.len());
        assert(toks.len() <= usize::MAX);
        assert(lo_r == mi + 1);
        assert(j >= 1);
        assert(first.start as int == g.ts.toks[lo_l as int].start);
        assert(last.end as int == g.ts.toks[j as int - 1].end);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].op == nd.op);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(kd(a, l as int) == nodes@[l as int].kind);
        assert(dtok_matches(src@, *opt, g.ts.toks[mi as int]));
        assert(is_op_tok(g.ts, mi as int, nd.op)) by {
            lemma_op_chars(nd.op);
        }
        lemma_assign_done(a, g.ts, g.cx, m as int, l as int, r as int, lo_l as int, mi as int, lo_r as int, j as int);
    }
    Some((lo_l, j, 0))
}

/// A `MemberExpression` `object . name` of the check whose parts are as read.
#[verifier::spinoff_prover]
proof fn lemma_member_dot_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    o: int,
    p: int,
    lo_o: int,
    mo: int,
    lo_p: int,
    j: int,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= o < m,
        0 <= p < m,
        a.nodes[m].kind == NodeKind::MemberExpression,
        a.nodes[m].op == Op::Dot,
        a.nodes[m].children =~= seq![o, p],
        lvl(a, o) == 15 || lvl(a, o) == 17,
        kd(a, p) == NodeKind::IdentifierName,
        node_done(a, ts, o, cx, lo_o, mo),
        node_done(a, ts, p, cx, lo_p, j),
        lo_p == mo + 1,
        j == mo + 2,
        mo + 2 <= tn(ts),
        ts.toks[mo].kind == TokKind::Punctuator,
        ts.toks[mo].text =~= seq![0x2Eu32],
        a.nodes[m].start == ts.toks[lo_o].start,
        a.nodes[m].end == ts.toks[mo + 1].end,
    ensures
        node_done(a, ts, m, cx, lo_o, mo + 2),
        lvl(a, m) == (if lvl(a, o) == 17 {
            17int
        } else {
            15int
        }),
{
    lemma_punct_text();
    assert(is_p(ts, mo, "."@));
    assert(is_member_or_call(a, o));
    assert(span_ok(a, ts, m, lo_o, mo + 2));
    crate::derive::lemma_member_dot_derives(a, ts, m, cx, lo_o, mo, o, p);
    lemma_ed_of(a, ts, m, lo_o, mo + 2);
}

/// §13.3.2 `object . name`.
#[verifier::spinoff_prover]
fn check_member_dot(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    m: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        m < nodes.len(),
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(
                arena_of(nodes@),
                g.ts,
                m as int,
                g.cx,
                l0 as int,
                h0 as int,
            ) && l as int == lvl(arena_of(nodes@), m as int),
            None => true,
        },
{
    let _ = gaps.len();
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::MemberExpression) || !matches!(nd.op, Op::Dot)
        || nd.children.len() != 2 {
        return None;
    }
    let o = match nd.children.as_slice().get(ZERO) {
        Some(x) => *x as usize,
        None => {
            return None;
        },
    };
    let p = match nd.children.as_slice().get(1) {
        Some(x) => *x as usize,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        lemma_child_before(a, m as int, 0);
        lemma_child_before(a, m as int, 1);
    }
    if o >= m || p >= m {
        return None;
    }
    let lo_o = match done.lo.get(o) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let mo = match done.hi.get(o) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lo_p = match done.lo.get(p) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let j = match done.hi.get(p) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_o = match done.lv.get(o) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let name_ok = match nodes.get(p) {
        Some(x) => matches!(x.kind, NodeKind::IdentifierName),
        None => false,
    };
    if !(lvl_o == 15 || lvl_o == 17) || !name_ok || lo_p != mo.saturating_add(1)
        || j != mo.saturating_add(2) {
        return None;
    }
    let dot = match toks.get(mo) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    let first = match toks.get(lo_o) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    let last = match toks.get(mo.saturating_add(1)) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, mo as int);
        assert(dot == &toks@[mo as int]);
    }
    if !matches!(dot.kind, TokKind::Punctuator) || !text_is1(src, dot, 0x2E) || nd.start
        != first.start || nd.end != last.end {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children =~= seq![o as int, p as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
            assert(a.nodes[m as int].children[0] == o as int);
            assert(a.nodes[m as int].children[1] == p as int);
        }
        lemma_inv_get(a, g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int, o as int);
        lemma_inv_get(a, g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int, p as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, lo_o as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, mo as int + 1);
        assert(mo < toks.len());
        assert(toks.len() <= usize::MAX);
        assert(lo_p == mo + 1);
        assert(j == mo + 2);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].op == nd.op);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(kd(a, p as int) == nodes@[p as int].kind);
        assert(first.start as int == g.ts.toks[lo_o as int].start);
        assert(last.end as int == g.ts.toks[mo as int + 1].end);
        assert(g.ts.toks[mo as int].kind == TokKind::Punctuator);
        assert(g.ts.toks[mo as int].text =~= seq![0x2Eu32]);
        lemma_member_dot_done(a, g.ts, g.cx, m as int, o as int, p as int, lo_o as int, mo as int, lo_p as int, j as int);
    }
    let own: i32 = if lvl_o == 17 { 17 } else { 15 };
    Some((lo_o, j, own))
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
        a.nodes[n].kind == NodeKind::IdentifierName && ts.toks[i].kind == TokKind::IdentifierName
            || a.nodes[n].kind == NodeKind::NumericLiteral && ts.toks[i].kind == TokKind::NumericLiteral
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
        ts.toks[lo_c].kind != TokKind::IdentifierName || ts.toks[lo_c].escaped || (!(ts.toks[lo_c].text
            =~= seq![0x66u32, 0x75, 0x6E, 0x63, 0x74, 0x69, 0x6F, 0x6E]) && !(ts.toks[lo_c].text
            =~= seq![0x63u32, 0x6C, 0x61, 0x73, 0x73]) && !(ts.toks[lo_c].text =~= seq![0x61u32,
            0x73, 0x79, 0x6E, 0x63]) && !(ts.toks[lo_c].text =~= seq![0x6Cu32, 0x65, 0x74])),
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
    lemma_kw_text();
    assert(!is_kw(ts, lo_c, "function"@));
    assert(!is_kw(ts, lo_c, "class"@));
    assert(!is_kw(ts, lo_c, "async"@));
    assert(!is_kw(ts, lo_c, "let"@));
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
        root_ctx(g).in_,
        cx_in(root_ctx(g), true) == root_ctx(g),
{
}

/// §13.2.9 `( Expression )`.
#[verifier::spinoff_prover]
fn check_paren(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    m: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        m < nodes.len(),
        cx_in(g.cx, true) == g.cx,
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(arena_of(nodes@), g.ts, m as int, g.cx, l0 as int, h0 as int)
                && l as int == lvl(arena_of(nodes@), m as int),
            None => true,
        },
{
    let _ = gaps.len();
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::ParenthesizedExpression) || nd.children.len() != 1 {
        return None;
    }
    let c = match nd.children.as_slice().get(ZERO) {
        Some(x) => *x as usize,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        lemma_child_before(a, m as int, 0);
    }
    if c >= m {
        return None;
    }
    let lo_c = match done.lo.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let hc = match done.hi.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_c = match done.lv.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    if lvl_c < -1 || lo_c < 1 {
        return None;
    }
    let open = match toks.get(lo_c.saturating_sub(1)) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    let close = match toks.get(hc) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, lo_c as int - 1);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, hc as int);
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
        lemma_inv_get(a, g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int, c as int);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(g.ts.toks[lo_c as int - 1].kind == TokKind::Punctuator);
        assert(g.ts.toks[lo_c as int - 1].text =~= seq![0x28u32]);
        assert(g.ts.toks[hc as int].kind == TokKind::Punctuator);
        assert(g.ts.toks[hc as int].text =~= seq![0x29u32]);
        assert(open.start as int == g.ts.toks[lo_c as int - 1].start);
        assert(close.end as int == g.ts.toks[hc as int].end);
        lemma_paren_done(a, g.ts, g.cx, m as int, c as int, lo_c as int, hc as int);
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
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    m: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        m < nodes.len(),
        cx_in(g.cx, true) == g.cx,
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(arena_of(nodes@), g.ts, m as int, g.cx, l0 as int, h0 as int)
                && l as int == lvl(arena_of(nodes@), m as int),
            None => true,
        },
{
    let _ = gaps.len();
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::ExpressionStatement) || nd.children.len() != 1 {
        return None;
    }
    let c = match nd.children.as_slice().get(ZERO) {
        Some(x) => *x as usize,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        lemma_child_before(a, m as int, 0);
    }
    if c >= m {
        return None;
    }
    let lo_c = match done.lo.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let hc = match done.hi.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_c = match done.lv.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    if lvl_c < -1 {
        return None;
    }
    let t0 = match toks.get(lo_c) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, lo_c as int);
        assert(t0 == &toks@[lo_c as int]);
    }
    let kw_start = matches!(t0.kind, TokKind::IdentifierName) && !t0.escaped && (text_is(
        src,
        t0,
        &[0x66, 0x75, 0x6E, 0x63, 0x74, 0x69, 0x6F, 0x6E],
    ) || text_is(src, t0, &[0x63, 0x6C, 0x61, 0x73, 0x73]) || text_is(
        src,
        t0,
        &[0x61, 0x73, 0x79, 0x6E, 0x63],
    ) || text_is(src, t0, &[0x6C, 0x65, 0x74]));
    if kw_start || (matches!(t0.kind, TokKind::Punctuator) && text_is1(src, t0, 0x7B))
        || nd.start != t0.start {
        return None;
    }
    // The `;`: a has_semi one at token `hc`, or one inserted in the gap before it.
    let mut has_semi = false;
    if let Some(st) = toks.get(hc) {
        proof {
            lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, hc as int);
            assert(st == &toks@[hc as int]);
        }
        if matches!(st.kind, TokKind::Punctuator) && text_is1(src, st, 0x3B) && nd.end == st.end {
            has_semi = true;
        }
    }
    let j: usize = if has_semi {
        hc.saturating_add(1)
    } else {
        let g = match gaps.get(hc) {
            Some(g) => g,
            None => {
                return None;
            },
        };
        let prev = match toks.get(hc.saturating_sub(1)) {
            Some(t) => t,
            None => {
                return None;
            },
        };
        if !matches!(g, Ins::Semicolon) || hc < 1 || nd.end != prev.end {
            return None;
        }
        hc
    };
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
            assert(a.nodes[m as int].children[0] == c as int);
        }
        lemma_inv_get(a, g.ts, g.cx, done.lo@, done.hi@, done.lv@, m as int, c as int);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(t0.start as int == g.ts.toks[lo_c as int].start);
        assert(g.ts.toks[lo_c as int].kind == t0.kind);
        assert(!(g.ts.toks[lo_c as int].kind == TokKind::Punctuator && g.ts.toks[lo_c as int].text
            =~= seq![0x7Bu32]));
        if has_semi {
            lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, hc as int);
            assert(hc < toks.len());
            assert(g.ts.toks[hc as int].kind == TokKind::Punctuator);
            assert(g.ts.toks[hc as int].text =~= seq![0x3Bu32]);
            assert(j as int == hc as int + 1);
            assert(toks@[hc as int].end as int == g.ts.toks[hc as int].end);
            lemma_exprstmt_done(a, g.ts, g.cx, m as int, c as int, lo_c as int, hc as int, j as int, true);
        } else {
            lemma_env_gap(src@, nodes@, toks@, gaps@, g.ts, hc as int);
            lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, hc as int - 1);
            assert(g.ts.gaps[hc as int] == Ins::Semicolon);
            assert(toks@[hc as int - 1].end as int == g.ts.toks[hc as int - 1].end);
            assert(hc <= toks.len());
            lemma_exprstmt_done(a, g.ts, g.cx, m as int, c as int, lo_c as int, hc as int, j as int, false);
        }
    }
    Some((lo_c, j, -100))
}

/// §14.4 `;`.
#[verifier::spinoff_prover]
fn check_empty(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    by_start: &[usize],
    m: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        m < nodes.len(),
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(arena_of(nodes@), g.ts, m as int, g.cx, l0 as int, h0 as int)
                && l as int == lvl(arena_of(nodes@), m as int),
            None => true,
        },
{
    let _ = gaps.len();
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::EmptyStatement) || !nd.children.is_empty() {
        return None;
    }
    let x = match by_start.get(nd.start) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let t = match toks.get(x) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, x as int);
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
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        assert(a.nodes[m as int].children.len() == 0);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(g.ts.toks[x as int].kind == TokKind::Punctuator);
        assert(g.ts.toks[x as int].text =~= seq![0x3Bu32]);
        assert(x < toks.len());
        assert(toks.len() <= usize::MAX);
        lemma_empty_done(a, g.ts, g.cx, m as int, x as int);
    }
    Some((x, x.saturating_add(1), -100))
}

/// The token ranges and binding strengths of the nodes checked so far, node by node.
pub struct Done {
    /// The first token of each node.
    pub lo: Vec<usize>,
    /// One past the last token of each node.
    pub hi: Vec<usize>,
    /// The binding strength (`spec::lvl`) of each node.
    pub lv: Vec<i32>,
    /// The token that starts at each source position (a hint, checked at use).
    pub by_start: Vec<usize>,
    /// The goal symbol is `Module`.
    pub module: bool,
}

/// The specification's stream and the context the nodes are derived in (ghost).
pub struct GCx {
    /// The stream.
    pub ts: Stream,
    /// The context.
    pub cx: Ctx,
}

/// What `check_derivation` found.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Derivation {
    /// Every node derives the tokens it spans: `derives_root` holds.
    Verified,
    /// A node of a kind the check does not cover: nothing is claimed.
    Unsupported,
    /// A covered node that is not derived: the parser built what the grammar does not allow.
    Failed,
}

/// §16.1, §16.2: the root derives the whole stream, from the items it holds.
#[verifier::spinoff_prover]
fn check_root(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    module: bool,
    Ghost(ts): Ghost<Stream>,
) -> (r: bool)
    requires
        nodes.len() > 0,
        env_ok(src@, nodes@, toks@, gaps@, ts),
        inv(
            arena_of(nodes@),
            ts,
            root_ctx(goal_of(module)),
            done.lo@,
            done.hi@,
            done.lv@,
            nodes.len() as int - 1,
        ),
    ensures
        r ==> derives_root(arena_of(nodes@), ts, goal_of(module)),
{
    let n = nodes.len();
    let root = n.saturating_sub(1);
    let _ = (src.len(), gaps.len(), done.lv.len());
    let nt = toks.len();
    let ghost a = arena_of(nodes@);
    let ghost cx = root_ctx(goal_of(module));
    let nd = match nodes.get(root) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    let kind_ok = if module {
        matches!(nd.kind, NodeKind::Module)
    } else {
        matches!(nd.kind, NodeKind::Script)
    };
    if !kind_ok {
        return false;
    }
    proof {
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, ts);
        assert(a.nodes[root as int] == nodes@[root as int]@);
        assert(nd == &nodes@[root as int]);
        assert(a.nodes[root as int].kind == nd.kind);
    }
    let len = nd.children.len();
    let mut k = len;
    let mut pos = nt;
    while k > 0
        invariant
            nodes.len() > 0,
            n == nodes.len(),
            root + 1 == n,
            nt == toks.len(),
            tn(ts) == nt,
            ast_wf(a),
            a == arena_of(nodes@),
            cx == root_ctx(goal_of(module)),
            nd == &nodes@[root as int],
            len == nd.children.len(),
            k <= len,
            pos <= nt,
            env_ok(src@, nodes@, toks@, gaps@, ts),
            inv(a, ts, cx, done.lo@, done.hi@, done.lv@, root as int),
            dl(a, ts, root as int, a.nodes[root as int].children, k as int, cx, pos as int, nt as int),
            forall|j: int|
                k <= j < len ==> is_item_kind(kd(a, #[trigger] a.nodes[root as int].children[j])),
        decreases k,
    {
        let c = match nd.children.as_slice().get(k.saturating_sub(1)) {
            Some(x) => *x as usize,
            None => {
                return false;
            },
        };
        proof {
            assert(a.nodes[root as int].children[k as int - 1] == c as int);
            lemma_child_before(a, root as int, k as int - 1);
        }
        let lo_c = match done.lo.get(c) {
            Some(x) => *x,
            None => {
                return false;
            },
        };
        let hi_c = match done.hi.get(c) {
            Some(x) => *x,
            None => {
                return false;
            },
        };
        let item = match nodes.get(c) {
            Some(x) => matches!(x.kind, NodeKind::ExpressionStatement | NodeKind::EmptyStatement),
            None => false,
        };
        if hi_c != pos || !item {
            return false;
        }
        proof {
            lemma_inv_get(a, ts, cx, done.lo@, done.hi@, done.lv@, root as int, c as int);
            assert(a.nodes[c as int] == nodes@[c as int]@);
            let ks = a.nodes[root as int].children;
            lemma_dl_cons(a, ts, root as int, ks, k as int - 1, cx, lo_c as int, hi_c as int, nt as int);
            assert(is_item_kind(kd(a, c as int)));
        }
        pos = lo_c;
        k = k.saturating_sub(1);
    }
    if pos != 0 {
        return false;
    }
    let spans = if nt == 0 {
        nd.start == 0 && nd.end == 0
    } else {
        let first = match toks.get(ZERO) {
            Some(t) => t,
            None => {
                return false;
            },
        };
        let last = match toks.get(nt.saturating_sub(1)) {
            Some(t) => t,
            None => {
                return false;
            },
        };
        nd.start == first.start && nd.end == last.end
    };
    if !spans {
        return false;
    }
    proof {
        lemma_root_cx(goal_of(module));
        assert(nd.start as int == a.nodes[root as int].start);
        assert(nd.end as int == a.nodes[root as int].end);
        if nt == 0 {
            assert(span_ok(a, ts, root as int, 0, 0));
        } else {
            lemma_env_tok(src@, nodes@, toks@, gaps@, ts, 0);
            lemma_env_tok(src@, nodes@, toks@, gaps@, ts, nt as int - 1);
            assert(span_ok(a, ts, root as int, 0, tn(ts)));
        }
        assert(all_items(a, a.nodes[root as int].children));
        lemma_root_derives(a, ts, root as int, cx, goal_of(module));
    }
    true
}

/// Checks, bottom-up, that every node of the arena derives the tokens it spans
/// (`spec::d`), for the kinds the check covers, and that the root derives the
/// whole stream. `ast` has passed [`crate::check::finish`]; `toks` and `gaps` are
/// the tokens the parser consumed and the gaps where it inserted a `;`
/// (`gaps.len() == toks.len() + 1`). Proven: `Verified` implies
/// `derives_root(ast, ts, goal)` for every stream `ts` that is the executable
/// one (`stream_matches`), which is the assumption; see the module header.
pub fn check_derivation(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    module: bool,
    Ghost(ts): Ghost<Stream>,
) -> (r: Derivation)
    requires
        ast_wf(arena_of(nodes@)),
        stream_matches(src@, toks@, gaps@, ts),
        gaps@.len() == toks@.len() + 1,
    ensures
        r is Verified ==> derives_root(arena_of(nodes@), ts, goal_of(module)),
{
    let n = nodes.len();
    let nt = toks.len();
    // The tokens are not empty and their ends increase.
    let mut k: usize = 0;
    while k < nt
        invariant
            nt == toks.len(),
            k <= nt,
            stream_matches(src@, toks@, gaps@, ts),
            forall|x: int| 0 <= x < k ==> toks@[x].start < toks@[x].end,
            forall|x: int, y: int| 0 <= x < y < k ==> toks@[x].end < toks@[y].end,
        decreases nt - k,
    {
        let t = match toks.get(k) {
            Some(t) => t,
            None => {
                return Derivation::Failed;
            },
        };
        if t.start >= t.end {
            return Derivation::Failed;
        }
        if k > 0 {
            let p = match toks.get(k.saturating_sub(1)) {
                Some(p) => p,
                None => {
                    return Derivation::Failed;
                },
            };
            if p.end >= t.end {
                return Derivation::Failed;
            }
        }
        k = k.saturating_add(1);
    }
    proof {
        assert(toks_wf(ts)) by {
            assert forall|x: int| 0 <= x < tn(ts) implies (#[trigger] ts.toks[x]).start
                < ts.toks[x].end by {
                assert(dtok_matches(src@, toks@[x], ts.toks[x]));
            }
            assert forall|x: int, y: int| 0 <= x < y < tn(ts) implies (#[trigger] ts.toks[x]).end
                < (#[trigger] ts.toks[y]).end by {
                assert(dtok_matches(src@, toks@[x], ts.toks[x]));
                assert(dtok_matches(src@, toks@[y], ts.toks[y]));
            }
        }
        assert(env_ok(src@, nodes@, toks@, gaps@, ts)) by {
            reveal(env_ok);
        }
        lemma_root_cx(goal_of(module));
    }
    // A hint for finding a token from the start of a node.
    let mut by_start: Vec<usize> = Vec::new();
    let mut q: usize = 0;
    let size = src.len().saturating_add(1);
    while q < size
        invariant
            q <= size,
            by_start.len() == q,
        decreases size - q,
    {
        by_start.push(usize::MAX);
        q = q.saturating_add(1);
    }
    let mut x: usize = 0;
    while x < nt
        invariant
            x <= nt,
            nt == toks.len(),
            by_start.len() == size,
        decreases nt - x,
    {
        let t = match toks.get(x) {
            Some(t) => t,
            None => {
                return Derivation::Failed;
            },
        };
        if t.start < by_start.len() {
            by_start.set(t.start, x);
        }
        x = x.saturating_add(1);
    }
    let ghost cx = root_ctx(goal_of(module));
    let mut done = Done {
        lo: Vec::new(),
        hi: Vec::new(),
        lv: Vec::new(),
        by_start,
        module,
    };
    let last = n.saturating_sub(1);
    let mut m: usize = 0;
    proof {
        reveal(inv);
    }
    while m < last
        invariant
            n == nodes.len(),
            last + 1 == n,
            n > 0,
            m <= last,
            cx == root_ctx(goal_of(module)),
            cx_in(cx, true) == cx,
            cx.in_,
            done.module == module,
            env_ok(src@, nodes@, toks@, gaps@, ts),
            inv(arena_of(nodes@), ts, cx, done.lo@, done.hi@, done.lv@, m as int),
        decreases last - m,
    {
        let nd = match nodes.get(m) {
            Some(x) => x,
            None => {
                return Derivation::Failed;
            },
        };
        let res = match nd.kind {
            NodeKind::NumericLiteral | NodeKind::StringLiteral | NodeKind::RegularExpressionLiteral | NodeKind::IdentifierName => {
                proof {
                    lemma_env_literal_facts(src@, nodes@, toks@, gaps@, ts);
                }
                check_literal(nodes, toks, &done.by_start, m, Ghost(ts), Ghost(cx))
            },
            NodeKind::ParenthesizedExpression => check_paren(
                src,
                nodes,
                toks,
                gaps,
                &done,
                m,
                Ghost(GCx { ts, cx }),
            ),
            NodeKind::AdditiveExpression | NodeKind::MultiplicativeExpression | NodeKind::ExponentiationExpression | NodeKind::ShiftExpression | NodeKind::EqualityExpression | NodeKind::BitwiseANDExpression | NodeKind::BitwiseXORExpression | NodeKind::BitwiseORExpression | NodeKind::LogicalANDExpression | NodeKind::LogicalORExpression | NodeKind::CoalesceExpression
            | NodeKind::RelationalExpression => check_binary(
                src,
                nodes,
                toks,
                gaps,
                &done,
                m,
                Ghost(GCx { ts, cx }),
            ),
            NodeKind::IdentifierReference | NodeKind::BindingIdentifier | NodeKind::LabelIdentifier => check_ident(
                src,
                nodes,
                toks,
                gaps,
                &done,
                m,
                Ghost(GCx { ts, cx }),
            ),
            NodeKind::UnaryExpression => check_unary(
                src,
                nodes,
                toks,
                gaps,
                &done,
                m,
                Ghost(GCx { ts, cx }),
            ),
            NodeKind::ConditionalExpression => check_conditional(
                src,
                nodes,
                toks,
                gaps,
                &done,
                m,
                Ghost(GCx { ts, cx }),
            ),
            NodeKind::AssignmentExpression => check_assign(
                src,
                nodes,
                toks,
                gaps,
                &done,
                m,
                Ghost(GCx { ts, cx }),
            ),
            NodeKind::MemberExpression => check_member_dot(
                src,
                nodes,
                toks,
                gaps,
                &done,
                m,
                Ghost(GCx { ts, cx }),
            ),
            NodeKind::ExpressionStatement => check_exprstmt(
                src,
                nodes,
                toks,
                gaps,
                &done,
                m,
                Ghost(GCx { ts, cx }),
            ),
            NodeKind::EmptyStatement => check_empty(
                src,
                nodes,
                toks,
                gaps,
                &done.by_start,
                m,
                Ghost(GCx { ts, cx }),
            ),
            _ => {
                return Derivation::Unsupported;
            },
        };
        match res {
            Some((l0, h0, l)) => {
                proof {
                    lemma_inv_push(arena_of(nodes@), ts, cx, done.lo@, done.hi@, done.lv@, m as int, l0, h0, l);
                }
                done.lo.push(l0);
                done.hi.push(h0);
                done.lv.push(l);
            },
            None => {
                return Derivation::Unsupported;
            },
        }
        m = m.saturating_add(1);
    }
    if check_root(src, nodes, toks, gaps, &done, module, Ghost(ts)) {
        Derivation::Verified
    } else {
        Derivation::Unsupported
    }
}

/// The specification's token for an executable one: the fields the check reads, and
/// the lexer's other fields (`name`, `legacy`, ...) left as the empty or false
/// default; the productions the check covers read none of them.
pub open spec fn canon_tok(src: Seq<u32>, e: DTok) -> Tok {
    Tok {
        kind: e.kind,
        start: e.start as int,
        end: e.end as int,
        text: src.subrange(e.start as int, e.end as int),
        name: Seq::empty(),
        escaped: e.escaped,
        nl_before: e.nl,
        legacy: false,
        bigint: false,
        invalid_escape: false,
        regexp_valid: false,
    }
}

/// The stream of the executable tokens and gaps.
pub open spec fn canon_stream(src: Seq<u32>, toks: Seq<DTok>, gaps: Seq<Ins>) -> Stream {
    Stream { toks: toks.map_values(|e: DTok| canon_tok(src, e)), gaps: gaps }
}

/// [`check_derivation`] on the canonical stream, which needs no ghost argument.
///
/// Proven: `Verified` implies `derives_root` for [`canon_stream`]. That the real
/// stream (the lexer's tokens, with its own `name`, `legacy` and the like) derives
/// the same is the lexer's contract, which is assumed (item 7.2), and that the
/// productions covered read only the fields `canon_tok` keeps.
pub fn check_derivation_canon(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    module: bool,
) -> (r: Derivation)
    requires
        ast_wf(arena_of(nodes@)),
        gaps@.len() == toks@.len() + 1,
    ensures
        r is Verified ==> derives_root(
            arena_of(nodes@),
            canon_stream(src@, toks@, gaps@),
            goal_of(module),
        ),
{
    let nt = toks.len();
    let mut k: usize = 0;
    while k < nt
        invariant
            nt == toks.len(),
            k <= nt,
            forall|x: int| 0 <= x < k ==> (#[trigger] toks@[x]).start <= toks@[x].end && toks@[x].end <= src@.len(),
        decreases nt - k,
    {
        let t = match toks.get(k) {
            Some(t) => t,
            None => {
                return Derivation::Failed;
            },
        };
        if t.start > t.end || t.end > src.len() {
            return Derivation::Failed;
        }
        k = k.saturating_add(1);
    }
    let ghost ts = canon_stream(src@, toks@, gaps@);
    proof {
        assert(stream_matches(src@, toks@, gaps@, ts)) by {
            assert(toks@.len() == ts.toks.len());
            assert(gaps@ =~= ts.gaps);
            assert forall|x: int| 0 <= x < toks@.len() implies dtok_matches(
                src@,
                toks@[x],
                #[trigger] ts.toks[x],
            ) by {
                assert(ts.toks[x] == canon_tok(src@, toks@[x]));
            }
        }
    }
    check_derivation(src, nodes, toks, gaps, module, Ghost(ts))
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
