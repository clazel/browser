//! A proven check of [`spec::d`] over a whole arena, for the part of the grammar
//! it covers (item 7.3): [`check_derivation`] takes the arena of an
//! [`Ast`] that has passed [`crate::check::finish`] and the tokens the parser
//! consumed (with the gaps where it inserted a `;`), and returns
//! [`Derivation::Verified`] only if `derives_root` holds for it: every node
//! derives the tokens it spans, bottom-up, in the context the root's goal gives.
//!
//! **Covered:** a `Script` or `Module` whose nodes are: literals, identifiers,
//! parentheses, every binary level, unary, `++`/`--`, conditional, assignment
//! (with assignment patterns), member access (`.name`, `.#name`, `[expr]`),
//! arguments, calls, `new`, the comma operator, spread, array and object
//! literals (properties, methods, accessors, computed names), templates and tagged
//! templates, `this`/`null`/`true`/`false`, function and class declarations and
//! expressions (generators, `async`, arrows, methods, fields, static blocks,
//! private names), `yield` and `await`, binding patterns; and every statement of
//! §14 (`for` with declarations and identifier or member heads, `with`,
//! `switch`, `try`, labels, ...). Each node is checked in the context its
//! parent's production gives it (`Done::cxs`, [`Cx5`]: `[~In]` in a `for` head,
//! `cx_fn` in functions, `[+Await]` in a static block, ...); the assignment is
//! untrusted and compared by the parent's check. For any other node the result is
//! [`Derivation::Unsupported`]: nothing is claimed. Also covered, in [`crate::arena_e`]
//! and here: optional chains, `super`, `new.target`, `import(...)`, `import.meta`,
//! patterns and Annex B forms as `for` heads, `for await`, function declarations as
//! statement bodies, and operands of `[~In]` heads (bracketed operands are `[+In]`:
//! `cx_ok_t`, `cx_ok_init`). `CoverInitializedName` never survives the early errors; its
//! assignment-pattern reading is covered. Not covered: `await`, `yield` and class
//! expressions inside `[~In]` heads, and modules' `import` and `export`.
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
pub(crate) proof fn lemma_ed_of(a: AstV, ts: Stream, c: int, lo: int, hi: int)
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
pub(crate) proof fn lemma_dl_cons(a: AstV, ts: Stream, bound: int, ks: Seq<int>, k: int, cx: Ctx, i: int, m: int, j: int)
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
pub(crate) fn text_is(src: &[u32], t: &DTok, w: &[u32]) -> (r: bool)
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
pub(crate) const ZERO: usize = 0;

/// The source text of the token is the one code point `code`.
pub(crate) fn text_is1(src: &[u32], t: &DTok, code: u32) -> (r: bool)
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
pub(crate) proof fn lemma_punct_text()
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

/// The context a node is checked in, as the check carries it: the booleans of
/// [`Ctx`] (`[Yield]`, `[Await]`, `[In]`, `[Return]`, `[Default]`).
#[derive(Clone, Copy)]
pub struct Cx5 {
    /// `[Yield]`.
    pub y: bool,
    /// `[Await]`.
    pub a: bool,
    /// `[In]`.
    pub i: bool,
    /// `[Return]`.
    pub r: bool,
    /// `[Default]`.
    pub d: bool,
}

/// The specification's context of a carried one.
pub open spec fn cx_of(c: Cx5) -> Ctx {
    Ctx { yield_: c.y, await_: c.a, in_: c.i, return_: c.r, deflt: c.d }
}

/// Two carried contexts are the same.
fn cx_eq(p: &Cx5, q: &Cx5) -> (r: bool)
    ensures
        r == (cx_of(*p) == cx_of(*q)),
{
    p.y == q.y && p.a == q.a && p.i == q.i && p.r == q.r && p.d == q.d
}

/// Node `m` is checked in `cx`, and so are all its children (the productions of
/// the statements and expressions the check covers pass their context down).
pub open spec fn cx_ok(a: AstV, cxs: Seq<Cx5>, m: int, cx: Ctx) -> bool {
    kids_ok(a, cxs, m, cx) && cx_of(cxs[m]) == cx
}

/// Every child of node `m` is checked in `cx` (the node itself is checked in another
/// context where its production gives its children `[+In]`: [`cx_ok_t`]).
pub open spec fn kids_ok(a: AstV, cxs: Seq<Cx5>, m: int, cx: Ctx) -> bool {
    0 <= m < a.nodes.len() && m < cxs.len() && (forall|k: int|
        0 <= k < a.nodes[m].children.len() ==> 0 <= a.nodes[m].children[k] < cxs.len() && cx_of(
            cxs[#[trigger] a.nodes[m].children[k]],
        ) == cx)
}

/// Node `m` is checked in `cx` and its children in `cx_in(cx, true)`: the
/// productions whose operands are in brackets, `[+In]` whatever the context.
pub open spec fn cx_ok_t(a: AstV, cxs: Seq<Cx5>, m: int, cx: Ctx) -> bool {
    kids_ok(a, cxs, m, cx_in(cx, true)) && cx_of(cxs[m]) == cx
}

/// What a processed node `j < m` has proven: it derives tokens `lo[j]..hi[j]` in
/// its context `cxs[j]`, and has the binding strength `lv[j]`.
#[verifier::opaque]
pub open spec fn inv(
    a: AstV,
    ts: Stream,
    cxs: Seq<Cx5>,
    lo: Seq<usize>,
    hi: Seq<usize>,
    lv: Seq<i32>,
    m: int,
) -> bool {
    lo.len() == m && hi.len() == m && lv.len() == m && m <= cxs.len() && (forall|j: int|
        0 <= j < m ==> (#[trigger] lv[j]) as int == lvl(a, j) && (kd(a, j) != NodeKind::Absent
            ==> node_done(a, ts, j, cx_of(cxs[j]), lo[j] as int, hi[j] as int)))
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
pub(crate) proof fn lemma_child_before(a: AstV, m: int, k: int)
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
        a.nodes[m].op == Op::In ==> cx.in_,
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
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    let cxm = match done.cxs.get(m) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    if !opok || nd.children.len() != 2 || (matches!(nd.op, Op::In) && !cxm.i) {
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
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, l as int, g.cx, 0);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, r as int, g.cx, 1);
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
        assert(cxm == &done.cxs@[m as int]);
        assert(g.cx.in_ == cxm.i);
        assert(a.nodes[m as int].op == nd.op);
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
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    let cxm = match done.cxs.get(m) {
        Some(c) => c,
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
        || !ident_ok(src, t, cxm.y, cxm.a) {
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
        assert(cxm == &done.cxs@[m as int]);
        assert(g.cx.yield_ == cxm.y);
        assert(g.cx.await_ == cxm.a);
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
pub open spec fn list_item_ok(a: AstV, c: int, mode: int) -> bool {
    item_ok_val(lvl(a, c), kd(a, c), mode)
}

/// What a list of mode `mode` accepts as an item of binding strength `l` and kind `k`:
/// 0 an assignment expression, 1 that or a `SpreadElement`, 2 a `VariableDeclaration`,
/// 3 a `LexicalBinding`.
pub open spec fn item_ok_val(l: int, k: NodeKind, mode: int) -> bool {
    if mode == 0 {
        l >= 0
    } else if mode == 1 {
        l >= 0 || k == NodeKind::SpreadElement
    } else if mode == 2 {
        k == NodeKind::VariableDeclaration
    } else if mode == 3 {
        k == NodeKind::LexicalBinding
    } else if mode == 5 {
        k == NodeKind::PropertyDefinition || k == NodeKind::MethodDefinition
    } else if mode == 7 {
        k == NodeKind::BindingProperty || k == NodeKind::BindingRestProperty
    } else if mode == 9 {
        k == NodeKind::AssignmentProperty || k == NodeKind::AssignmentRestProperty
    } else {
        k == NodeKind::BindingElement || k == NodeKind::FunctionRestParameter
    }
}

/// `item_ok_val`, executable.
fn item_ok_exec(l: i32, k: NodeKind, mode: u8) -> (r: bool)
    ensures
        r == item_ok_val(l as int, k, mode as int),
{
    if mode == 0 {
        l >= 0
    } else if mode == 1 {
        l >= 0 || matches!(k, NodeKind::SpreadElement)
    } else if mode == 2 {
        matches!(k, NodeKind::VariableDeclaration)
    } else if mode == 3 {
        matches!(k, NodeKind::LexicalBinding)
    } else if mode == 5 {
        matches!(k, NodeKind::PropertyDefinition | NodeKind::MethodDefinition)
    } else if mode == 7 {
        matches!(k, NodeKind::BindingProperty | NodeKind::BindingRestProperty)
    } else if mode == 9 {
        matches!(k, NodeKind::AssignmentProperty | NodeKind::AssignmentRestProperty)
    } else {
        matches!(k, NodeKind::BindingElement | NodeKind::FunctionRestParameter)
    }
}


/// Which list `check_list` reads: the node, where its first item starts, whether a
/// spread element is an item, and whether a trailing `,` is allowed.
pub struct ListSpec {
    /// The node whose children are the items.
    pub m: usize,
    /// The token the first item starts at (an empty list: where it ends).
    pub start: usize,
    /// A `SpreadElement` is an item.
    pub mode: u8,
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
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, ls.m as int),
        kids_ok(arena_of(nodes@), done.cxs@, ls.m as int, g.cx),
    ensures
        match r {
            Some(e) => ls.start <= e && e <= toks.len() && dsep(
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
                    ls.mode as int,
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
    let kc_kind = match nodes.get(c) {
        Some(x) => x.kind,
        None => {
            return None;
        },
    };
    if !item_ok_exec(lvl_c, kc_kind, ls.mode) {
        return None;
    }
    // The end: after a trailing `,` if one is allowed and there.
    let mut comma_after = false;
    let tok_after = if ls.trail
        && !matches!(
            kc_kind,
            NodeKind::FunctionRestParameter | NodeKind::BindingRestProperty | NodeKind::AssignmentRestProperty
        ) {
        toks.get(hc)
    } else {
        None
    };
    if let Some(t) = tok_after {
        proof {
            lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, hc as int);
            assert(t == &toks@[hc as int]);
        }
        if matches!(t.kind, TokKind::Punctuator) && text_is1(src, t, 0x2C) {
            comma_after = true;
        }
    }
    let e: usize = if comma_after { hc.saturating_add(1) } else { hc };
    proof {
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, last as int);
        assert(hc <= toks.len());
        assert(kd(a, c as int) == nodes@[c as int].kind);
        if comma_after {
            assert(!is_rest_kind(kd(a, c as int)));
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
    proof {
        assert(node_done(a, g.ts, c as int, g.cx, lo_c as int, hc as int));
    }
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
            pos <= e,
            ast_wf(a),
            env_ok(src@, nodes@, toks@, gaps@, g.ts),
            inv(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
            kids_ok(a, done.cxs@, m as int, g.cx),
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
                    ls.mode as int,
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
        let kind2 = match nodes.get(c2) {
            Some(x) => x.kind,
            None => {
                return None;
            },
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
        if !item_ok_exec(lvl2, kind2, ls.mode) || !matches!(sep.kind, TokKind::Punctuator)
            || !text_is1(src, sep, 0x2C) || hi2.saturating_add(1) != pos {
            return None;
        }
        proof {
            lemma_comma_text();
            lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c2 as int, g.cx, k as int - 1);
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
        proof {
            assert(node_done(a, g.ts, c2 as int, g.cx, lo2 as int, hi2 as int));
        }
        pos = lo2;
        k = k.saturating_sub(1);
    }
    if pos != ls.start {
        return None;
    }
    proof {
        assert(forall|q: int|
            0 <= q < len ==> list_item_ok(a, #[trigger] a.nodes[m as int].children[q], ls.mode as int));
    }
    Some(e)
}

/// An `Arguments` node of the check whose list and brackets are as read.
#[verifier::spinoff_prover]
proof fn lemma_arguments_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int, e: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= x,
        e < tn(ts),
        x + 1 <= e,
        a.nodes[m].kind == NodeKind::Arguments,
        dsep(a, ts, m, a.nodes[m].children, 0, cx_in(cx, true), x + 1, e, true),
        forall|k: int|
            0 <= k < a.nodes[m].children.len() ==> list_item_ok(
                a,
                #[trigger] a.nodes[m].children[k],
                1,
            ),
        ts.toks[x].kind == TokKind::Punctuator,
        ts.toks[x].text =~= seq![0x28u32],
        ts.toks[e].kind == TokKind::Punctuator,
        ts.toks[e].text =~= seq![0x29u32],
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[e].end,
    ensures
        node_done(a, ts, m, cx, x, e + 1),
        lvl(a, m) == -100,
{
    lemma_punct_text();
    assert(is_p(ts, x, "("@));
    assert(is_p(ts, e, ")"@));
    assert(all_args(a, a.nodes[m].children)) by {
        assert forall|k: int| 0 <= k < a.nodes[m].children.len() implies is_assign_expr(
            a,
            #[trigger] a.nodes[m].children[k],
        ) || kd(a, a.nodes[m].children[k]) == NodeKind::SpreadElement by {
            assert(list_item_ok(a, a.nodes[m].children[k], 1));
        }
    }
    assert(span_ok(a, ts, m, x, e + 1));
    assert(d_expr_lhs(a, ts, m, cx, x, e + 1));
    assert(d(a, ts, m, cx, x, e + 1));
    lemma_ed_of(a, ts, m, x, e + 1);
}

/// §13.3.8 `( ArgumentList )`.
#[verifier::spinoff_prover]
fn check_arguments(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok_t(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::Arguments) {
        return None;
    }
    let x = match done.by_start.get(nd.start) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let open = match toks.get(x) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, x as int);
        assert(open == &toks@[x as int]);
    }
    if !matches!(open.kind, TokKind::Punctuator) || !text_is1(src, open, 0x28) || open.start
        != nd.start {
        return None;
    }
    let ghost gt = GCx { ts: g.ts, cx: cx_in(g.cx, true) };
    let ls = ListSpec { m, start: x.saturating_add(1), mode: 1, trail: true };
    let e = match check_list(src, nodes, toks, gaps, done, &ls, Ghost(gt)) {
        Some(e) => e,
        None => {
            return None;
        },
    };
    let close = match toks.get(e) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, e as int);
        assert(close == &toks@[e as int]);
    }
    if !matches!(close.kind, TokKind::Punctuator) || !text_is1(src, close, 0x29) || close.end
        != nd.end {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        assert(x < toks.len());
        assert(toks.len() <= usize::MAX);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(open.start as int == g.ts.toks[x as int].start);
        assert(close.end as int == g.ts.toks[e as int].end);
        assert(g.ts.toks[x as int].kind == TokKind::Punctuator);
        assert(g.ts.toks[x as int].text =~= seq![0x28u32]);
        assert(g.ts.toks[e as int].kind == TokKind::Punctuator);
        assert(g.ts.toks[e as int].text =~= seq![0x29u32]);
        assert(e < toks.len());
        assert(x as int + 1 <= e as int) by {
            // The list starts at x + 1 and ends at e; its items lie between.
            assert(dsep(a, g.ts, m as int, a.nodes[m as int].children, 0, cx_in(g.cx, true), x as int + 1, e as int, true));
        }
        lemma_arguments_done(a, g.ts, g.cx, m as int, x as int, e as int);
    }
    Some((x, e.saturating_add(1), -100))
}

/// A `CallExpression` of the check whose callee and arguments are as read.
#[verifier::spinoff_prover]
proof fn lemma_call_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    f: int,
    args: int,
    lo_f: int,
    mf: int,
    lo_a: int,
    j: int,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= f < m,
        0 <= args < m,
        a.nodes[m].kind == NodeKind::CallExpression,
        a.nodes[m].children =~= seq![f, args],
        lvl(a, f) == 15 || lvl(a, f) == 17,
        kd(a, args) == NodeKind::Arguments,
        node_done(a, ts, f, cx, lo_f, mf),
        node_done(a, ts, args, cx, lo_a, j),
        lo_a == mf,
        a.nodes[m].start == ts.toks[lo_f].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, lo_f, j),
        lvl(a, m) == 15,
{
    assert(is_member_or_call(a, f));
    assert(span_ok(a, ts, m, lo_f, j));
    assert(a.nodes[m].children[0] == f);
    assert(a.nodes[m].children[1] == args);
    assert(dc(a, ts, m, f, cx, lo_f, mf));
    assert(dc(a, ts, m, args, cx, mf, j));
    assert(d_expr_lhs(a, ts, m, cx, lo_f, j));
    assert(d(a, ts, m, cx, lo_f, j));
    lemma_ed_of(a, ts, m, lo_f, j);
}

/// §13.3.6 `callee Arguments`.
#[verifier::spinoff_prover]
fn check_call(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    let _ = src.len();
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::CallExpression) || nd.children.len() != 2 {
        return None;
    }
    let f = match nd.children.as_slice().get(ZERO) {
        Some(x) => *x as usize,
        None => {
            return None;
        },
    };
    let args = match nd.children.as_slice().get(1) {
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
    if f >= m || args >= m {
        return None;
    }
    let lo_f = match done.lo.get(f) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let mf = match done.hi.get(f) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lo_a = match done.lo.get(args) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let j = match done.hi.get(args) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_f = match done.lv.get(f) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let args_ok = match nodes.get(args) {
        Some(x) => matches!(x.kind, NodeKind::Arguments),
        None => false,
    };
    if !(lvl_f == 15 || lvl_f == 17) || !args_ok || lo_a != mf {
        return None;
    }
    let first = match toks.get(lo_f) {
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
    if nd.start != first.start || nd.end != last.end {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children =~= seq![f as int, args as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
            assert(a.nodes[m as int].children[0] == f as int);
            assert(a.nodes[m as int].children[1] == args as int);
        }
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, f as int, g.cx, 0);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, args as int, g.cx, 1);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, lo_f as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, j as int - 1);
        assert(j >= 1);
        assert(first.start as int == g.ts.toks[lo_f as int].start);
        assert(last.end as int == g.ts.toks[j as int - 1].end);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(kd(a, args as int) == nodes@[args as int].kind);
        lemma_call_done(a, g.ts, g.cx, m as int, f as int, args as int, lo_f as int, mf as int, lo_a as int, j as int);
    }
    Some((lo_f, j, 15))
}

/// An `Expression` (comma list) of the check.
#[verifier::spinoff_prover]
proof fn lemma_expression_done(a: AstV, ts: Stream, cx: Ctx, m: int, lo: int, j: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= lo < j <= tn(ts),
        a.nodes[m].kind == NodeKind::Expression,
        a.nodes[m].children.len() >= 2,
        dsep(a, ts, m, a.nodes[m].children, 0, cx, lo, j, false),
        forall|k: int|
            0 <= k < a.nodes[m].children.len() ==> list_item_ok(
                a,
                #[trigger] a.nodes[m].children[k],
                0,
            ),
        a.nodes[m].start == ts.toks[lo].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, lo, j),
        lvl(a, m) == -1,
{
    assert(span_ok(a, ts, m, lo, j));
    assert forall|k: int| 0 <= k < a.nodes[m].children.len() implies is_assign_expr(
        a,
        #[trigger] a.nodes[m].children[k],
    ) by {
        assert(list_item_ok(a, a.nodes[m].children[k], 0));
    }
    assert(d_expr(a, ts, m, cx, lo, j));
    assert(d(a, ts, m, cx, lo, j));
    lemma_ed_of(a, ts, m, lo, j);
}

/// §13.16 `Expression , AssignmentExpression`.
#[verifier::spinoff_prover]
fn check_expression(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::Expression) || nd.children.len() < 2 {
        return None;
    }
    let first_c = match nd.children.as_slice().get(ZERO) {
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
    if first_c >= m {
        return None;
    }
    let lo = match done.lo.get(first_c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let ls = ListSpec { m, start: lo, mode: 0, trail: false };
    let e = match check_list(src, nodes, toks, gaps, done, &ls, Ghost(g)) {
        Some(e) => e,
        None => {
            return None;
        },
    };
    let first = match toks.get(lo) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    let last = match toks.get(e.saturating_sub(1)) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    if lo >= e || nd.start != first.start || nd.end != last.end {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, lo as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, e as int - 1);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(a.nodes[m as int].children.len() == nd.children.len());
        assert(e >= 1);
        assert(first.start as int == g.ts.toks[lo as int].start);
        assert(last.end as int == g.ts.toks[e as int - 1].end);
        lemma_expression_done(a, g.ts, g.cx, m as int, lo as int, e as int);
    }
    Some((lo, e, -1))
}

/// A `SpreadElement` of the check.
#[verifier::spinoff_prover]
proof fn lemma_spread_done(a: AstV, ts: Stream, cx: Ctx, m: int, c: int, x: int, hc: int)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= c < m,
        a.nodes[m].kind == NodeKind::SpreadElement,
        a.nodes[m].children =~= seq![c],
        node_done(a, ts, c, cx, x + 1, hc),
        lvl(a, c) >= 0,
        0 <= x < tn(ts),
        ts.toks[x].kind == TokKind::Punctuator,
        ts.toks[x].text =~= seq![0x2Eu32, 0x2E, 0x2E],
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[hc - 1].end,
    ensures
        node_done(a, ts, m, cx, x, hc),
        lvl(a, m) == -100,
{
    reveal_strlit("...");
    assert("..."@ =~= seq!['.', '.', '.']);
    assert(is_p(ts, x, "..."@));
    assert(span_ok(a, ts, m, x, hc));
    assert(a.nodes[m].children[0] == c);
    assert(dc(a, ts, m, c, cx_in(cx, true), x + 1, hc));
    assert(d_expr(a, ts, m, cx, x, hc));
    assert(d(a, ts, m, cx, x, hc));
    lemma_ed_of(a, ts, m, x, hc);
}

/// §13.3.8 `... AssignmentExpression`.
#[verifier::spinoff_prover]
fn check_spread(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    if !matches!(nd.kind, NodeKind::SpreadElement) || nd.children.len() != 1 {
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
    if lvl_c < 0 || lo_c < 1 {
        return None;
    }
    let dots = match toks.get(lo_c.saturating_sub(1)) {
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
        assert(dots == &toks@[lo_c as int - 1]);
    }
    if !matches!(dots.kind, TokKind::Punctuator) || !text_is(src, dots, &[0x2E, 0x2E, 0x2E])
        || nd.start != dots.start || nd.end != last.end {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
            assert(a.nodes[m as int].children[0] == c as int);
        }
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 0);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, hc as int - 1);
        assert(lo_c >= 1);
        assert(lo_c.saturating_sub(1) as int == lo_c as int - 1);
        assert(hc >= 1);
        assert(hc.saturating_sub(1) as int == hc as int - 1);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(dots.start as int == g.ts.toks[lo_c as int - 1].start);
        assert(last.end as int == g.ts.toks[hc as int - 1].end);
        assert(g.ts.toks[lo_c as int - 1].kind == TokKind::Punctuator);
        assert(g.ts.toks[lo_c as int - 1].text =~= seq![0x2Eu32, 0x2E, 0x2E]);
        lemma_spread_done(a, g.ts, g.cx, m as int, c as int, lo_c as int - 1, hc as int);
    }
    Some((lo_c.saturating_sub(1), hc, -100))
}

/// The words `this`, `null`, `true` and `false`, as code points.
pub(crate) proof fn lemma_literal_words()
    ensures
        cps("this"@) =~= seq![0x74u32, 0x68, 0x69, 0x73],
        cps("null"@) =~= seq![0x6Eu32, 0x75, 0x6C, 0x6C],
        cps("true"@) =~= seq![0x74u32, 0x72, 0x75, 0x65],
        cps("false"@) =~= seq![0x66u32, 0x61, 0x6C, 0x73, 0x65],
{
    reveal_strlit("this");
    reveal_strlit("null");
    reveal_strlit("true");
    reveal_strlit("false");
    assert("this"@ =~= seq!['t', 'h', 'i', 's']);
    assert("null"@ =~= seq!['n', 'u', 'l', 'l']);
    assert("true"@ =~= seq!['t', 'r', 'u', 'e']);
    assert("false"@ =~= seq!['f', 'a', 'l', 's', 'e']);
}

/// A `this`, `null`, `true` or `false` leaf of the check.
#[verifier::spinoff_prover]
proof fn lemma_kw_leaf_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= x < tn(ts),
        a.nodes[m].children.len() == 0,
        ts.toks[x].kind == TokKind::IdentifierName,
        !ts.toks[x].escaped,
        match a.nodes[m].kind {
            NodeKind::ThisExpression => ts.toks[x].text =~= seq![0x74u32, 0x68, 0x69, 0x73],
            NodeKind::NullLiteral => ts.toks[x].text =~= seq![0x6Eu32, 0x75, 0x6C, 0x6C],
            NodeKind::BooleanLiteral => ts.toks[x].text =~= seq![0x74u32, 0x72, 0x75, 0x65]
                || ts.toks[x].text =~= seq![0x66u32, 0x61, 0x6C, 0x73, 0x65],
            _ => false,
        },
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[x].end,
    ensures
        node_done(a, ts, m, cx, x, x + 1),
        lvl(a, m) == 17,
{
    lemma_literal_words();
    assert(ts.toks[x].start < ts.toks[x].end);
    crate::derive::lemma_leaf_keyword(a, ts, m, cx, x);
    assert(span_ok(a, ts, m, x, x + 1));
    lemma_ed_of(a, ts, m, x, x + 1);
}

/// §13.2.1, §13.2.3 `this`, `null`, `true`, `false`.
#[verifier::spinoff_prover]
fn check_keyword_leaf(
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
    if !nd.children.is_empty() {
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
    let text_ok = match nd.kind {
        NodeKind::ThisExpression => text_is(src, t, &[0x74, 0x68, 0x69, 0x73]),
        NodeKind::NullLiteral => text_is(src, t, &[0x6E, 0x75, 0x6C, 0x6C]),
        NodeKind::BooleanLiteral => text_is(src, t, &[0x74, 0x72, 0x75, 0x65]) || text_is(
            src,
            t,
            &[0x66, 0x61, 0x6C, 0x73, 0x65],
        ),
        _ => false,
    };
    if !text_ok || !matches!(t.kind, TokKind::IdentifierName) || t.escaped || t.start != nd.start
        || t.end != nd.end {
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
        lemma_kw_leaf_done(a, g.ts, g.cx, m as int, x as int);
    }
    Some((x, x1, 17))
}

/// An `Absent` node at token position `p` of the check: placed where the production
/// has the optional symbol (`spec::span_ok`, `spec::d`).
pub(crate) fn check_absent(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    c: usize,
    p: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: bool)
    requires
        c < nodes.len(),
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
    ensures
        r ==> (p <= toks.len() && kd(arena_of(nodes@), c as int) == NodeKind::Absent && d(
            arena_of(nodes@),
            g.ts,
            c as int,
            g.cx,
            p as int,
            p as int,
        ) && ed(arena_of(nodes@), g.ts, c as int, p as int) == p as int),
{
    let _ = gaps.len();
    let _ = src.len();
    let nd = match nodes.get(c) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    if !matches!(nd.kind, NodeKind::Absent) || !nd.children.is_empty() || nd.start != nd.end
        || p > toks.len() {
        return false;
    }
    let prev: usize = if p == 0 {
        0
    } else {
        match toks.get(p.saturating_sub(1)) {
            Some(t) => t.end,
            None => {
                return false;
            },
        }
    };
    if prev > nd.start {
        return false;
    }
    if p < toks.len() {
        match toks.get(p) {
            Some(t) => {
                if nd.start > t.start {
                    return false;
                }
            },
            None => {
                return false;
            },
        }
    } else if nd.start != prev {
        return false;
    }
    proof {
        let a = arena_of(nodes@);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        assert(nd == &nodes@[c as int]);
        assert(a.nodes[c as int] == nodes@[c as int]@);
        assert(a.nodes[c as int].children.len() == 0);
        assert(a.nodes[c as int].kind == NodeKind::Absent);
        assert(a.nodes[c as int].start == nd.start as int);
        assert(a.nodes[c as int].end == nd.start as int);
        if p >= 1 {
            lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, p as int - 1);
            assert(p.saturating_sub(1) as int == p as int - 1);
        }
        if p < toks.len() {
            lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, p as int);
        }
        assert(prev_end(g.ts, p as int) == prev as int);
        assert(span_ok(a, g.ts, c as int, p as int, p as int));
        assert(d_expr(a, g.ts, c as int, g.cx, p as int, p as int));
        assert(d(a, g.ts, c as int, g.cx, p as int, p as int));
    }
    true
}

/// The end of a statement that ends with `;`: a real `;` at token `hc`, or one
/// inserted in the gap before it; `end` is where the statement's last token ends.
pub(crate) fn find_semi(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    hc: usize,
    end: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<usize>)
    requires
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
    ensures
        match r {
            Some(j) => semi(g.ts, hc as int, j as int, false) && 1 <= j && j <= toks.len() && g.ts.toks[j as int
                - 1].end == end as int && hc <= j,
            None => true,
        },
{
    let _ = nodes.len();
    if let Some(st) = toks.get(hc) {
        proof {
            lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, hc as int);
            assert(st == &toks@[hc as int]);
        }
        if matches!(st.kind, TokKind::Punctuator) && text_is1(src, st, 0x3B) && end == st.end {
            proof {
                lemma_punct_text();
                lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
                assert(hc < toks.len());
                assert(toks.len() <= usize::MAX);
                assert(g.ts.toks[hc as int].kind == TokKind::Punctuator);
                assert(g.ts.toks[hc as int].text =~= seq![0x3Bu32]);
                assert(is_p(g.ts, hc as int, ";"@));
                assert(hc.saturating_add(1) as int == hc as int + 1);
                assert(st.end as int == g.ts.toks[hc as int].end);
            }
            return Some(hc.saturating_add(1));
        }
    }
    let g0 = match gaps.get(hc) {
        Some(x) => x,
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
    if !matches!(g0, Ins::Semicolon) || hc < 1 || end != prev.end {
        return None;
    }
    proof {
        lemma_env_gap(src@, nodes@, toks@, gaps@, g.ts, hc as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, hc as int - 1);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        assert(hc.saturating_sub(1) as int == hc as int - 1);
        assert(prev.end as int == g.ts.toks[hc as int - 1].end);
        assert(hc <= toks.len());
    }
    Some(hc)
}

/// The end of a list of `dsep` items is `list_next` when the last item ends it.
proof fn lemma_list_next(
    a: AstV,
    ts: Stream,
    bound: int,
    ks: Seq<int>,
    k: int,
    cx: Ctx,
    i: int,
    j: int,
)
    requires
        0 <= k < ks.len(),
        dsep(a, ts, bound, ks, k, cx, i, j, false),
    ensures
        list_next(a, ts, ks, k, i) == j,
    decreases ks.len() - k,
{
    if k + 1 < ks.len() {
        let m = ed(a, ts, ks[k], i);
        lemma_list_next(a, ts, bound, ks, k + 1, cx, m + 1, j);
    }
}

/// A `VariableDeclaration` or `LexicalBinding` of the check: a binding identifier and
/// an optional initializer.
#[verifier::spinoff_prover]
#[verifier::rlimit(150)]
proof fn lemma_binding_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    t: int,
    init: int,
    lo_t: int,
    mt: int,
    j: int,
    with_init: bool,
    lo_i: int,
    ci: Ctx,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= t < m,
        0 <= init < m,
        a.nodes[m].kind == NodeKind::VariableDeclaration || a.nodes[m].kind
            == NodeKind::LexicalBinding || a.nodes[m].kind == NodeKind::BindingElement
            || a.nodes[m].kind == NodeKind::AssignmentElement,
        ci == (if a.nodes[m].kind == NodeKind::BindingElement || a.nodes[m].kind
            == NodeKind::AssignmentElement {
            cx_in(cx, true)
        } else {
            cx
        }),
        a.nodes[m].children =~= seq![t, init],
        if a.nodes[m].kind == NodeKind::AssignmentElement { is_destructuring_target(a, t) } else { is_binding_target_kind(kd(a, t)) },
        node_done(a, ts, t, cx, lo_t, mt),
        a.nodes[m].start == ts.toks[lo_t].start,
        a.nodes[m].end == ts.toks[j - 1].end,
        0 <= j <= tn(ts),
        lo_t < j,
        if with_init {
            lvl(a, init) >= 0 && mt < tn(ts) && ts.toks[mt].kind == TokKind::Punctuator
                && ts.toks[mt].text =~= seq![0x3Du32] && lo_i == mt + 1 && node_done(
                a,
                ts,
                init,
                ci,
                lo_i,
                j,
            )
        } else {
            kd(a, init) == NodeKind::Absent && (a.nodes[m].kind == NodeKind::BindingElement || a.nodes[m].kind == NodeKind::AssignmentElement || !is_binding_pattern_kind(kd(a, t))) && j == mt && d(a, ts, init, ci, mt, mt) && ed(
                a,
                ts,
                init,
                mt,
            ) == mt
        },
    ensures
        node_done(a, ts, m, cx, lo_t, j),
        lvl(a, m) == -100,
{
    lemma_punct_text();
    assert(span_ok(a, ts, m, lo_t, j));
    assert(a.nodes[m].children[0] == t);
    assert(a.nodes[m].children[1] == init);
    assert(dc(a, ts, m, t, cx, lo_t, mt));
    if with_init {
        reveal_strlit("=");
        assert("="@ =~= seq!['=']);
        assert(is_p(ts, mt, "="@));
        assert(is_assign_expr(a, init));
        assert(dc(a, ts, m, init, ci, lo_i, j));
        assert(d_init(a, ts, m, init, ci, mt, j, false));
        assert(d_init(a, ts, m, init, ci, mt, j, true));
    } else {
        assert(dc(a, ts, m, init, ci, mt, mt));
        assert(d_init(a, ts, m, init, ci, mt, j, false));
    }
    if a.nodes[m].kind == NodeKind::BindingElement || a.nodes[m].kind == NodeKind::AssignmentElement {
        assert(d_pat(a, ts, m, cx, lo_t, j));
    } else {
        assert(d_stmt(a, ts, m, cx, lo_t, j));
    }
    lemma_ed_of(a, ts, m, lo_t, j);
}

/// §14.3.2, §14.3.1 `BindingIdentifier Initializer?`.
#[verifier::spinoff_prover]
fn check_binding(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok_init(
            arena_of(nodes@),
            done.cxs@,
            m as int,
            g.cx,
            if nodes@[m as int].kind == NodeKind::BindingElement || nodes@[m as int].kind
                == NodeKind::AssignmentElement {
                cx_in(g.cx, true)
            } else {
                g.cx
            },
        ),
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
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::VariableDeclaration | NodeKind::LexicalBinding | NodeKind::BindingElement | NodeKind::AssignmentElement)
        || nd.children.len() != 2 {
        return None;
    }
    let ghost ci: Ctx = if nd.kind == NodeKind::BindingElement || nd.kind == NodeKind::AssignmentElement {
        cx_in(g.cx, true)
    } else {
        g.cx
    };
    let ghost gi = GCx { ts: g.ts, cx: ci };
    let t = match nd.children.as_slice().get(ZERO) {
        Some(x) => *x as usize,
        None => {
            return None;
        },
    };
    let init = match nd.children.as_slice().get(1) {
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
    if t >= m || init >= m {
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
    let lv_t = match done.lv.get(t) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let target_ok = match nodes.get(t) {
        Some(x) => if matches!(nd.kind, NodeKind::AssignmentElement) {
            matches!(x.kind, NodeKind::ObjectAssignmentPattern | NodeKind::ArrayAssignmentPattern)
                || (lv_t >= 14 && !matches!(x.kind, NodeKind::ObjectLiteral | NodeKind::ArrayLiteral))
        } else {
            matches!(
                x.kind,
                NodeKind::BindingIdentifier | NodeKind::ObjectBindingPattern | NodeKind::ArrayBindingPattern
            )
        },
        None => false,
    };
    if !target_ok {
        return None;
    }
    let init_absent = match nodes.get(init) {
        Some(x) => matches!(x.kind, NodeKind::Absent),
        None => false,
    };
    let first = match toks.get(lo_t) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    if init_absent {
        let pat = !matches!(nd.kind, NodeKind::BindingElement | NodeKind::AssignmentElement)
            && match nodes.get(t) {
                Some(x) => !matches!(x.kind, NodeKind::BindingIdentifier),
                None => true,
            };
        if pat || !check_absent(src, nodes, toks, gaps, init, mt, Ghost(gi)) {
            return None;
        }
        let prev = match toks.get(mt.saturating_sub(1)) {
            Some(t) => t,
            None => {
                return None;
            },
        };
        if mt < 1 || nd.start != first.start || nd.end != prev.end || lo_t >= mt {
            return None;
        }
        proof {
            let a = arena_of(nodes@);
            lemma_inv_get_init(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, t as int, g.cx, ci, 0);
            lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, lo_t as int);
            lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, mt as int - 1);
            assert(nd == &nodes@[m as int]);
            assert(a.nodes[m as int].children =~= seq![t as int, init as int]) by {
                assert(a.nodes[m as int].children.len() == 2);
                assert(a.nodes[m as int].children[0] == t as int);
                assert(a.nodes[m as int].children[1] == init as int);
            }
            assert(kd(a, t as int) == nodes@[t as int].kind);
            assert(a.nodes[m as int].kind == nd.kind);
            assert(a.nodes[m as int].start == nd.start as int);
            assert(a.nodes[m as int].end == nd.end as int);
            assert(mt.saturating_sub(1) as int == mt as int - 1);
            assert(first.start as int == g.ts.toks[lo_t as int].start);
            assert(prev.end as int == g.ts.toks[mt as int - 1].end);
            assert(mt <= toks.len());
            lemma_binding_done(a, g.ts, g.cx, m as int, t as int, init as int, lo_t as int, mt as int, mt as int, false, 0, ci);
        }
        return Some((lo_t, mt, -100));
    }
    let lo_i = match done.lo.get(init) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let j = match done.hi.get(init) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let lvl_i = match done.lv.get(init) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let eq = match toks.get(mt) {
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
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, mt as int);
        assert(eq == &toks@[mt as int]);
    }
    if lvl_i < 0 || !matches!(eq.kind, TokKind::Punctuator) || !text_is1(src, eq, 0x3D)
        || lo_i != mt.saturating_add(1) || nd.start != first.start || nd.end != last.end {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        lemma_inv_get_init(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, t as int, g.cx, ci, 0);
        lemma_inv_get_init(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, init as int, g.cx, ci, 1);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, lo_t as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, j as int - 1);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children =~= seq![t as int, init as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
            assert(a.nodes[m as int].children[0] == t as int);
            assert(a.nodes[m as int].children[1] == init as int);
        }
        assert(kd(a, t as int) == nodes@[t as int].kind);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(mt < toks.len());
        assert(toks.len() <= usize::MAX);
        assert(lo_i == mt + 1);
        assert(j >= 1);
        assert(first.start as int == g.ts.toks[lo_t as int].start);
        assert(last.end as int == g.ts.toks[j as int - 1].end);
        assert(g.ts.toks[mt as int].kind == TokKind::Punctuator);
        assert(g.ts.toks[mt as int].text =~= seq![0x3Du32]);
        assert(lvl(a, init as int) >= 0);
        assert(node_done(a, g.ts, init as int, ci, lo_i as int, j as int));
        assert(mt < j);
        assert(j <= toks.len());
        lemma_binding_done(a, g.ts, g.cx, m as int, t as int, init as int, lo_t as int, mt as int, j as int, true, lo_i as int, ci);
    }
    Some((lo_t, j, -100))
}

/// The words `var`, `let` and `const`, as code points.
proof fn lemma_decl_words()
    ensures
        cps("var"@) =~= seq![0x76u32, 0x61, 0x72],
        cps("let"@) =~= seq![0x6Cu32, 0x65, 0x74],
        cps("const"@) =~= seq![0x63u32, 0x6F, 0x6E, 0x73, 0x74],
{
    reveal_strlit("var");
    reveal_strlit("let");
    reveal_strlit("const");
    assert("var"@ =~= seq!['v', 'a', 'r']);
    assert("let"@ =~= seq!['l', 'e', 't']);
    assert("const"@ =~= seq!['c', 'o', 'n', 's', 't']);
}

/// A `VariableStatement` or `LexicalDeclaration` of the check.
#[verifier::spinoff_prover]
proof fn lemma_decl_stmt_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    x: int,
    e: int,
    j: int,
    word: Seq<u32>,
)
    requires
        toks_wf(ts),
        a.nodes[m].kind == NodeKind::VariableStatement ==> cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= x < tn(ts),
        a.nodes[m].children.len() > 0,
        a.nodes[m].kind == NodeKind::VariableStatement || a.nodes[m].kind
            == NodeKind::LexicalDeclaration,
        a.nodes[m].kind == NodeKind::VariableStatement ==> (word =~= seq![0x76u32, 0x61, 0x72]),
        a.nodes[m].kind == NodeKind::LexicalDeclaration ==> (a.nodes[m].op == Op::Let && word
            =~= seq![0x6Cu32, 0x65, 0x74]) || (a.nodes[m].op == Op::Const && word
            =~= seq![0x63u32, 0x6F, 0x6E, 0x73, 0x74]),
        ts.toks[x].kind == TokKind::IdentifierName,
        !ts.toks[x].escaped,
        ts.toks[x].text =~= word,
        dsep(a, ts, m, a.nodes[m].children, 0, cx, x + 1, e, false),
        forall|k: int|
            0 <= k < a.nodes[m].children.len() ==> list_item_ok(
                a,
                #[trigger] a.nodes[m].children[k],
                if a.nodes[m].kind == NodeKind::VariableStatement {
                    2int
                } else {
                    3int
                },
            ),
        semi(ts, e, j, false),
        x + 1 <= e,
        e <= tn(ts),
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    lemma_decl_words();
    let ks = a.nodes[m].children;
    lemma_list_next(a, ts, m, ks, 0, cx, x + 1, e);
    assert(span_ok(a, ts, m, x, j));
    if a.nodes[m].kind == NodeKind::VariableStatement {
        assert(is_kw(ts, x, "var"@));
        assert forall|k: int| 0 <= k < ks.len() implies kd(a, #[trigger] ks[k])
            == NodeKind::VariableDeclaration by {
            assert(list_item_ok(a, ks[k], 2));
        }
    } else {
        assert forall|k: int| 0 <= k < ks.len() implies kd(a, #[trigger] ks[k])
            == NodeKind::LexicalBinding by {
            assert(list_item_ok(a, ks[k], 3));
        }
        if a.nodes[m].op == Op::Let {
            assert(is_kw(ts, x, "let"@));
        } else {
            assert(is_kw(ts, x, "const"@));
        }
    }
    assert(d_stmt(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.3.2, §14.3.1 `var`, `let` or `const` and a list of bindings, then `;`.
#[verifier::spinoff_prover]
fn check_decl_stmt(
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
        nodes@[m as int].kind == NodeKind::VariableStatement ==> cx_in(g.cx, true) == g.cx,
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let is_var = matches!(nd.kind, NodeKind::VariableStatement);
    let ok_kind = is_var || (matches!(nd.kind, NodeKind::LexicalDeclaration) && matches!(
        nd.op,
        Op::Let | Op::Const,
    ));
    if !ok_kind || nd.children.is_empty() {
        return None;
    }
    let x = match done.by_start.get(nd.start) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let kw = match toks.get(x) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, x as int);
        assert(kw == &toks@[x as int]);
    }
    let word: &'static [u32] = if is_var {
        &[0x76, 0x61, 0x72]
    } else if matches!(nd.op, Op::Let) {
        &[0x6C, 0x65, 0x74]
    } else {
        &[0x63, 0x6F, 0x6E, 0x73, 0x74]
    };
    if !matches!(kw.kind, TokKind::IdentifierName) || kw.escaped || !text_is(src, kw, word)
        || kw.start != nd.start {
        return None;
    }
    let ls = ListSpec {
        m,
        start: x.saturating_add(1),
        mode: if is_var { 2 } else { 3 },
        trail: false,
    };
    let e = match check_list(src, nodes, toks, gaps, done, &ls, Ghost(g)) {
        Some(e) => e,
        None => {
            return None;
        },
    };
    let j = match find_semi(src, nodes, toks, gaps, e, nd.end, Ghost(g)) {
        Some(j) => j,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        assert(x < toks.len());
        assert(toks.len() <= usize::MAX);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(a.nodes[m as int].children.len() == nd.children.len());
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].op == nd.op);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(kw.start as int == g.ts.toks[x as int].start);
        assert(g.ts.toks[x as int].kind == TokKind::IdentifierName);
        assert(g.ts.toks[x as int].escaped == kw.escaped);
        assert(g.ts.toks[x as int].text =~= src@.subrange(kw.start as int, kw.end as int));
        assert(word@ =~= (if is_var {
            seq![0x76u32, 0x61, 0x72]
        } else if nd.op == Op::Let {
            seq![0x6Cu32, 0x65, 0x74]
        } else {
            seq![0x63u32, 0x6F, 0x6E, 0x73, 0x74]
        }));
        assert(x < j);
        lemma_decl_stmt_done(a, g.ts, g.cx, m as int, x as int, e as int, j as int, word@);
    }
    Some((x, j, -100))
}

/// A statement kind, executable (`spec::is_statement_kind`).
fn stmt_kind_exec(k: NodeKind) -> (r: bool)
    ensures
        r ==> is_statement_kind(k),
{
    matches!(
        k,
        NodeKind::BlockStatement
            | NodeKind::VariableStatement
            | NodeKind::EmptyStatement
            | NodeKind::ExpressionStatement
            | NodeKind::IfStatement
            | NodeKind::DoWhileStatement
            | NodeKind::WhileStatement
            | NodeKind::ForStatement
            | NodeKind::ForInStatement
            | NodeKind::ForOfStatement
            | NodeKind::ContinueStatement
            | NodeKind::BreakStatement
            | NodeKind::ReturnStatement
            | NodeKind::WithStatement
            | NodeKind::SwitchStatement
            | NodeKind::LabelledStatement
            | NodeKind::ThrowStatement
            | NodeKind::TryStatement
            | NodeKind::DebuggerStatement
    )
}

/// A `Statement` kind or a `FunctionDeclaration`, executable (`spec::is_stmt_or_function`): the
/// body of an `if` clause (Annex B.3.3) or a label (§14.13, Annex B.3.1).
fn stmt_or_fn_exec(k: NodeKind) -> (r: bool)
    ensures
        r ==> (is_statement_kind(k) || k == NodeKind::FunctionDeclaration),
{
    stmt_kind_exec(k) || matches!(k, NodeKind::FunctionDeclaration)
}

/// A `StatementListItem` kind, executable (`spec::is_item_kind`).
fn item_kind_exec(k: NodeKind) -> (r: bool)
    ensures
        r ==> is_item_kind(k),
{
    stmt_kind_exec(k) || matches!(
        k,
        NodeKind::LexicalDeclaration
            | NodeKind::FunctionDeclaration
            | NodeKind::GeneratorDeclaration
            | NodeKind::AsyncFunctionDeclaration
            | NodeKind::AsyncGeneratorDeclaration
            | NodeKind::ClassDeclaration
    )
}

/// The token range a statement list of node `m` covers, from `start` to `end`.
pub struct Rng {
    /// The node whose children are the statements.
    pub m: usize,
    /// The first token of the list (where it ends, if empty).
    pub start: usize,
    /// One past the last token of the list.
    pub end: usize,
}

/// The children of `rng.m` are `StatementListItem`s that derive consecutive token
/// ranges from `start` to `end` (`spec::dl`, `spec::all_items`).
fn check_dl(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    rng: &Rng,
    Ghost(g): Ghost<GCx>,
) -> (r: bool)
    requires
        rng.m < nodes.len(),
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, rng.m as int),
        cx_ok(arena_of(nodes@), done.cxs@, rng.m as int, g.cx),
        rng.end <= toks.len(),
    ensures
        r ==> (dl(
            arena_of(nodes@),
            g.ts,
            rng.m as int,
            arena_of(nodes@).nodes[rng.m as int].children,
            0,
            g.cx,
            rng.start as int,
            rng.end as int,
        ) && all_items(arena_of(nodes@), arena_of(nodes@).nodes[rng.m as int].children) && rng.start <= rng.end),
{
    let _ = (src.len(), gaps.len(), toks.len());
    let m = rng.m;
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return false;
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
    let mut k = len;
    let mut pos = rng.end;
    while k > 0
        invariant
            m < nodes.len(),
            nodes@.len() == nodes.len(),
            nd == &nodes@[m as int],
            a == arena_of(nodes@),
            len == nd.children.len(),
            len == a.nodes[m as int].children.len(),
            k <= len,
            pos <= toks.len(),
            pos <= rng.end,
            tn(g.ts) == toks.len(),
            ast_wf(a),
            env_ok(src@, nodes@, toks@, gaps@, g.ts),
            inv(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
            cx_ok(a, done.cxs@, m as int, g.cx),
            dl(
                a,
                g.ts,
                m as int,
                a.nodes[m as int].children,
                k as int,
                g.cx,
                pos as int,
                rng.end as int,
            ),
            forall|q: int|
                k <= q < len ==> is_item_kind(kd(a, #[trigger] a.nodes[m as int].children[q])),
        decreases k,
    {
        let c = match nd.children.as_slice().get(k.saturating_sub(1)) {
            Some(x) => *x as usize,
            None => {
                return false;
            },
        };
        proof {
            assert(k >= 1);
            assert(k.saturating_sub(1) as int == k as int - 1);
            assert(a.nodes[m as int].children[k as int - 1] == c as int);
            lemma_child_before(a, m as int, k as int - 1);
        }
        if c >= m {
            return false;
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
            Some(x) => item_kind_exec(x.kind),
            None => false,
        };
        if hi_c != pos || !item {
            return false;
        }
        proof {
            assert(a.nodes[c as int] == nodes@[c as int]@);
            assert(kd(a, c as int) == nodes@[c as int].kind);
            assert(is_item_kind(kd(a, c as int)));
            assert(kd(a, c as int) != NodeKind::Absent);
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, k as int - 1);
            let ks = a.nodes[m as int].children;
            assert(node_done(a, g.ts, c as int, g.cx, lo_c as int, hi_c as int));
            lemma_dl_cons(a, g.ts, m as int, ks, k as int - 1, g.cx, lo_c as int, hi_c as int, rng.end as int);
        }
        pos = lo_c;
        k = k.saturating_sub(1);
    }
    if pos != rng.start {
        return false;
    }
    proof {
        assert(all_items(a, a.nodes[m as int].children));
    }
    true
}

/// The words `if`, `else`, `while` and `throw`, as code points.
proof fn lemma_stmt_words()
    ensures
        cps("if"@) =~= seq![0x69u32, 0x66],
        cps("else"@) =~= seq![0x65u32, 0x6C, 0x73, 0x65],
        cps("while"@) =~= seq![0x77u32, 0x68, 0x69, 0x6C, 0x65],
        cps("throw"@) =~= seq![0x74u32, 0x68, 0x72, 0x6F, 0x77],
{
    reveal_strlit("if");
    reveal_strlit("else");
    reveal_strlit("while");
    reveal_strlit("throw");
    assert("if"@ =~= seq!['i', 'f']);
    assert("else"@ =~= seq!['e', 'l', 's', 'e']);
    assert("while"@ =~= seq!['w', 'h', 'i', 'l', 'e']);
    assert("throw"@ =~= seq!['t', 'h', 'r', 'o', 'w']);
}

/// A `Block` of the check.
#[verifier::spinoff_prover]
proof fn lemma_block_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int, e: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= x,
        x < e < tn(ts),
        a.nodes[m].kind == NodeKind::BlockStatement || a.nodes[m].kind == NodeKind::FunctionBody,
        all_items(a, a.nodes[m].children),
        dl(a, ts, m, a.nodes[m].children, 0, cx, x + 1, e),
        ts.toks[x].kind == TokKind::Punctuator,
        ts.toks[x].text =~= seq![0x7Bu32],
        ts.toks[e].kind == TokKind::Punctuator,
        ts.toks[e].text =~= seq![0x7Du32],
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[e].end,
    ensures
        node_done(a, ts, m, cx, x, e + 1),
        lvl(a, m) == -100,
{
    lemma_brace_text();
    assert(is_p(ts, x, "{"@));
    assert(is_p(ts, e, "}"@));
    assert(span_ok(a, ts, m, x, e + 1));
    if a.nodes[m].kind == NodeKind::BlockStatement {
        assert(d_stmt(a, ts, m, cx, x, e + 1));
    } else {
        assert(d_func(a, ts, m, cx, x, e + 1));
    }
    lemma_ed_of(a, ts, m, x, e + 1);
}

/// The brace texts as code points.
pub(crate) proof fn lemma_brace_text()
    ensures
        cps("{"@) =~= seq![0x7Bu32],
        cps("}"@) =~= seq![0x7Du32],
{
    reveal_strlit("{");
    reveal_strlit("}");
    assert("{"@ =~= seq!['{']);
    assert("}"@ =~= seq!['}']);
}

/// §14.2 `{ StatementList? }`.
#[verifier::spinoff_prover]
fn check_block(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::BlockStatement | NodeKind::FunctionBody) {
        return None;
    }
    let x = match done.by_start.get(nd.start) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let open = match toks.get(x) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, x as int);
        assert(open == &toks@[x as int]);
    }
    if !matches!(open.kind, TokKind::Punctuator) || !text_is1(src, open, 0x7B) || open.start
        != nd.start {
        return None;
    }
    let len = nd.children.len();
    let close: usize = if len == 0 {
        x.saturating_add(1)
    } else {
        let last = match nd.children.as_slice().get(len.saturating_sub(1)) {
            Some(x) => *x as usize,
            None => {
                return None;
            },
        };
        match done.hi.get(last) {
            Some(h) => *h,
            None => {
                return None;
            },
        }
    };
    if close > toks.len() {
        return None;
    }
    let rng = Rng { m, start: x.saturating_add(1), end: close };
    if !check_dl(src, nodes, toks, gaps, done, &rng, Ghost(g)) {
        return None;
    }
    let cl = match toks.get(close) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, close as int);
        assert(cl == &toks@[close as int]);
    }
    if !matches!(cl.kind, TokKind::Punctuator) || !text_is1(src, cl, 0x7D) || cl.end != nd.end {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        assert(x < toks.len());
        assert(toks.len() <= usize::MAX);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(open.start as int == g.ts.toks[x as int].start);
        assert(cl.end as int == g.ts.toks[close as int].end);
        assert(g.ts.toks[x as int].kind == TokKind::Punctuator);
        assert(g.ts.toks[x as int].text =~= seq![0x7Bu32]);
        assert(g.ts.toks[close as int].kind == TokKind::Punctuator);
        assert(g.ts.toks[close as int].text =~= seq![0x7Du32]);
        assert(a.nodes[m as int].children.len() == len);
        assert(x as int + 1 <= close as int);
        lemma_block_done(a, g.ts, g.cx, m as int, x as int, close as int);
    }
    Some((x, close.saturating_add(1), -100))
}

/// An `IfStatement` of the check.
#[verifier::spinoff_prover]
proof fn lemma_if_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    t: int,
    c: int,
    alt: int,
    x: int,
    lo_t: int,
    mt: int,
    lo_c: int,
    q: int,
    j: int,
    lo_a: int,
    with_else: bool,
)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= t < m,
        0 <= c < m,
        0 <= alt < m,
        a.nodes[m].kind == NodeKind::IfStatement,
        a.nodes[m].children =~= seq![t, c, alt],
        0 <= x,
        x + 1 < tn(ts),
        ts.toks[x].kind == TokKind::IdentifierName,
        !ts.toks[x].escaped,
        ts.toks[x].text =~= seq![0x69u32, 0x66],
        ts.toks[x + 1].kind == TokKind::Punctuator,
        ts.toks[x + 1].text =~= seq![0x28u32],
        lo_t == x + 2,
        node_done(a, ts, t, cx, lo_t, mt),
        lvl(a, t) >= -1,
        mt < tn(ts),
        ts.toks[mt].kind == TokKind::Punctuator,
        ts.toks[mt].text =~= seq![0x29u32],
        lo_c == mt + 1,
        node_done(a, ts, c, cx, lo_c, q),
        is_stmt_or_function(a, c),
        0 <= j <= tn(ts),
        if with_else {
            q < tn(ts) && ts.toks[q].kind == TokKind::IdentifierName && !ts.toks[q].escaped
                && ts.toks[q].text =~= seq![0x65u32, 0x6C, 0x73, 0x65] && is_stmt_or_function(
                a,
                alt,
            ) && lo_a == q + 1 && node_done(a, ts, alt, cx, lo_a, j)
        } else {
            kd(a, alt) == NodeKind::Absent && j == q && d(a, ts, alt, cx, q, q) && ed(
                a,
                ts,
                alt,
                q,
            ) == q
        },
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
        x < j,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    lemma_stmt_words();
    lemma_punct_text();
    assert(is_kw(ts, x, "if"@));
    assert(is_p(ts, x + 1, "("@));
    assert(is_p(ts, mt, ")"@));
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == t);
    assert(a.nodes[m].children[1] == c);
    assert(a.nodes[m].children[2] == alt);
    assert(dc(a, ts, m, t, cx_in(cx, true), x + 2, mt));
    assert(dc(a, ts, m, c, cx, mt + 1, q));
    if with_else {
        assert(is_kw(ts, q, "else"@));
        assert(dc(a, ts, m, alt, cx, q + 1, j));
    } else {
        assert(dc(a, ts, m, alt, cx, q, q));
    }
    assert(d_stmt(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.6 `if ( Expression ) Statement else Statement`.
#[verifier::spinoff_prover]
fn check_if(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::IfStatement) || nd.children.len() != 3 {
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
    let alt = match nd.children.as_slice().get(2) {
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
    if t >= m || c >= m || alt >= m {
        return None;
    }
    let x = match done.by_start.get(nd.start) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
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
    let q = match done.hi.get(c) {
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
    let c_ok = match nodes.get(c) {
        Some(x) => stmt_or_fn_exec(x.kind),
        None => false,
    };
    let kw = match toks.get(x) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    let lp = match toks.get(x.saturating_add(1)) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    let rp = match toks.get(mt) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        assert(x < toks.len());
        assert(toks.len() <= usize::MAX);
        assert(x.saturating_add(1) as int == x as int + 1);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, x as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, x as int + 1);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, mt as int);
        assert(kw == &toks@[x as int]);
        assert(lp == &toks@[x as int + 1]);
        assert(rp == &toks@[mt as int]);
    }
    if !c_ok || lvl_t < -1 || !matches!(kw.kind, TokKind::IdentifierName) || kw.escaped
        || !text_is(src, kw, &[0x69, 0x66]) || kw.start != nd.start || !matches!(
        lp.kind,
        TokKind::Punctuator,
    ) || !text_is1(src, lp, 0x28) || lo_t != x.saturating_add(2) || !matches!(
        rp.kind,
        TokKind::Punctuator,
    ) || !text_is1(src, rp, 0x29) || lo_c != mt.saturating_add(1) {
        return None;
    }
    let alt_absent = match nodes.get(alt) {
        Some(a) => matches!(a.kind, NodeKind::Absent),
        None => false,
    };
    let (j, lo_a): (usize, usize) = if alt_absent {
        if !check_absent(src, nodes, toks, gaps, alt, q, Ghost(g)) {
            return None;
        }
        (q, 0)
    } else {
        let alt_ok = match nodes.get(alt) {
            Some(x) => stmt_or_fn_exec(x.kind),
            None => false,
        };
        let ej = match done.hi.get(alt) {
            Some(x) => *x,
            None => {
                return None;
            },
        };
        let lo_a = match done.lo.get(alt) {
            Some(x) => *x,
            None => {
                return None;
            },
        };
        let ek = match toks.get(q) {
            Some(t) => t,
            None => {
                return None;
            },
        };
        proof {
            lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, q as int);
            assert(ek == &toks@[q as int]);
        }
        if !alt_ok || !matches!(ek.kind, TokKind::IdentifierName) || ek.escaped || !text_is(
            src,
            ek,
            &[0x65, 0x6C, 0x73, 0x65],
        ) || lo_a != q.saturating_add(1) {
            return None;
        }
        (ej, lo_a)
    };
    let _ = lo_a;
    let last = match toks.get(j.saturating_sub(1)) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    if nd.end != last.end || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children =~= seq![t as int, c as int, alt as int]) by {
            assert(a.nodes[m as int].children.len() == 3);
            assert(a.nodes[m as int].children[0] == t as int);
            assert(a.nodes[m as int].children[1] == c as int);
            assert(a.nodes[m as int].children[2] == alt as int);
        }
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, t as int, g.cx, 0);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 1);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, j as int - 1);
        assert(x < toks.len());
        assert(toks.len() <= usize::MAX);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(x.saturating_add(2) as int == x as int + 2);
        assert(mt < toks.len());
        assert(lo_c == mt + 1);
        assert(j >= 1);
        assert(j.saturating_sub(1) as int == j as int - 1);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(kd(a, c as int) == nodes@[c as int].kind);
        assert(kd(a, c as int) != NodeKind::Absent);
        assert(is_stmt_or_function(a, c as int));
        assert(last.end as int == g.ts.toks[j as int - 1].end);
        assert(kw.start as int == g.ts.toks[x as int].start);
        assert(g.ts.toks[x as int].kind == TokKind::IdentifierName);
        assert(g.ts.toks[x as int].escaped == kw.escaped);
        assert(g.ts.toks[x as int].text =~= src@.subrange(kw.start as int, kw.end as int));
        assert(g.ts.toks[x as int + 1].kind == TokKind::Punctuator);
        assert(g.ts.toks[x as int + 1].text =~= seq![0x28u32]);
        assert(g.ts.toks[mt as int].kind == TokKind::Punctuator);
        assert(g.ts.toks[mt as int].text =~= seq![0x29u32]);
        assert(j <= toks.len());
        if alt_absent {
            assert(kd(a, alt as int) == NodeKind::Absent);
            lemma_if_done(a, g.ts, g.cx, m as int, t as int, c as int, alt as int, x as int, lo_t as int, mt as int, lo_c as int, q as int, j as int, 0, false);
        } else {
            let ek = toks@[q as int];
            lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, q as int);
            assert(q < toks.len());
            assert(kd(a, alt as int) == nodes@[alt as int].kind);
            assert(is_stmt_or_function(a, alt as int));
            assert(kd(a, alt as int) != NodeKind::Absent);
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, alt as int, g.cx, 2);
            assert(g.ts.toks[q as int].kind == TokKind::IdentifierName);
            assert(g.ts.toks[q as int].text =~= seq![0x65u32, 0x6C, 0x73, 0x65]);
            lemma_if_done(a, g.ts, g.cx, m as int, t as int, c as int, alt as int, x as int, lo_t as int, mt as int, lo_c as int, q as int, j as int, lo_a as int, true);
        }
    }
    Some((x, j, -100))
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 0);
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
        node_done(a, ts, c, cx_in(cx, true), lo_c, mc),
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
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok_init(arena_of(nodes@), done.cxs@, m as int, g.cx, cx_in(g.cx, true)),
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
        lemma_inv_get_init(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, t as int, g.cx, cx_in(g.cx, true), 0);
        lemma_inv_get_init(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, cx_in(g.cx, true), 1);
        lemma_inv_get_init(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, e as int, g.cx, cx_in(g.cx, true), 2);
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
        if a.nodes[m].op == Op::Assign {
            is_destructuring_target(a, l)
        } else {
            is_lhs_expr(a, l)
        },
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    let left_pattern = matches!(nd.op, Op::Assign)
        && matches!(
            kind_at(nodes, l),
            NodeKind::ObjectAssignmentPattern | NodeKind::ArrayAssignmentPattern
        );
    if !((lvl_l >= 14 && left_plain) || left_pattern) || lvl_r < 0
        || lo_r != mi.saturating_add(1) {
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
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, l as int, g.cx, 0);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, r as int, g.cx, 1);
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, o as int, g.cx, 0);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, p as int, g.cx, 1);
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

/// Node `j < m`, the child `k` of node `m` checked in `cx`, is done (`inv`).
pub(crate) proof fn lemma_inv_get(
    a: AstV,
    ts: Stream,
    cxs: Seq<Cx5>,
    lo: Seq<usize>,
    hi: Seq<usize>,
    lv: Seq<i32>,
    m: int,
    j: int,
    cx: Ctx,
    k: int,
)
    requires
        inv(a, ts, cxs, lo, hi, lv, m),
        kids_ok(a, cxs, m, cx),
        0 <= j < m,
        0 <= k < a.nodes[m].children.len(),
        a.nodes[m].children[k] == j,
    ensures
        kd(a, j) != NodeKind::Absent ==> node_done(a, ts, j, cx, lo[j] as int, hi[j] as int),
        lvl(a, j) != -100 ==> node_done(a, ts, j, cx, lo[j] as int, hi[j] as int),
        lv[j] as int == lvl(a, j),
{
    reveal(inv);
    assert(cx_of(cxs[a.nodes[m].children[k]]) == cx);
    assert(cx_of(cxs[j]) == cx);
    assert(lv[j] as int == lvl(a, j));
    if kd(a, j) == NodeKind::Absent {
        assert(lvl(a, j) == -100);
    }
}

/// Node `m` is checked in `cx`, its second child (the initializer of a pattern
/// element) in `ci`, and every other child in `cx`: the productions with an
/// `Initializer[+In]` inside a `[~In]` head.
pub open spec fn cx_ok_init(a: AstV, cxs: Seq<Cx5>, m: int, cx: Ctx, ci: Ctx) -> bool {
    0 <= m < a.nodes.len() && m < cxs.len() && cx_of(cxs[m]) == cx && (forall|k: int|
        0 <= k < a.nodes[m].children.len() ==> 0 <= a.nodes[m].children[k] < cxs.len() && cx_of(
            cxs[#[trigger] a.nodes[m].children[k]],
        ) == (if k == 1 {
            ci
        } else {
            cx
        }))
}

/// [`lemma_inv_get`] for a node under [`cx_ok_init`].
pub(crate) proof fn lemma_inv_get_init(
    a: AstV,
    ts: Stream,
    cxs: Seq<Cx5>,
    lo: Seq<usize>,
    hi: Seq<usize>,
    lv: Seq<i32>,
    m: int,
    j: int,
    cx: Ctx,
    ci: Ctx,
    k: int,
)
    requires
        inv(a, ts, cxs, lo, hi, lv, m),
        cx_ok_init(a, cxs, m, cx, ci),
        0 <= j < m,
        0 <= k < a.nodes[m].children.len(),
        a.nodes[m].children[k] == j,
    ensures
        kd(a, j) != NodeKind::Absent ==> node_done(
            a,
            ts,
            j,
            if k == 1 {
                ci
            } else {
                cx
            },
            lo[j] as int,
            hi[j] as int,
        ),
        lvl(a, j) != -100 ==> node_done(
            a,
            ts,
            j,
            if k == 1 {
                ci
            } else {
                cx
            },
            lo[j] as int,
            hi[j] as int,
        ),
        lv[j] as int == lvl(a, j),
{
    reveal(inv);
    assert(cx_of(cxs[a.nodes[m].children[k]]) == (if k == 1 {
        ci
    } else {
        cx
    }));
    assert(lv[j] as int == lvl(a, j));
    if kd(a, j) == NodeKind::Absent {
        assert(lvl(a, j) == -100);
    }
}

/// Token `k` of the executable tokens is the specification's.
pub(crate) proof fn lemma_env_tok(src: Seq<u32>, nodes: Seq<Node>, toks: Seq<DTok>, gaps: Seq<Ins>, ts: Stream, k: int)
    requires
        env_ok(src, nodes, toks, gaps, ts),
        0 <= k < toks.len(),
    ensures
        dtok_matches(src, toks[k], ts.toks[k]),
{
    reveal(env_ok);
}

/// The specification's tokens are not empty and their ends increase.
pub(crate) proof fn lemma_env_toks_wf(src: Seq<u32>, nodes: Seq<Node>, toks: Seq<DTok>, gaps: Seq<Ins>, ts: Stream)
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
#[verifier::rlimit(100)]
proof fn lemma_inv_push(
    a: AstV,
    ts: Stream,
    cxs: Seq<Cx5>,
    lo: Seq<usize>,
    hi: Seq<usize>,
    lv: Seq<i32>,
    m: int,
    l0: usize,
    h0: usize,
    l: i32,
)
    requires
        inv(a, ts, cxs, lo, hi, lv, m),
        m < cxs.len(),
        node_done(a, ts, m, cx_of(cxs[m]), l0 as int, h0 as int),
        l as int == lvl(a, m),
    ensures
        inv(a, ts, cxs, lo.push(l0), hi.push(h0), lv.push(l), m + 1),
{
    let lo2 = lo.push(l0);
    let hi2 = hi.push(h0);
    let lv2 = lv.push(l);
    assert(inv(a, ts, cxs, lo2, hi2, lv2, m + 1)) by {
        reveal(inv);
        assert(m + 1 <= cxs.len());
        assert(m >= 0);
        assert(lo2.len() == m + 1);
        assert(hi2.len() == m + 1);
        assert(lv2.len() == m + 1);
        assert forall|j: int| 0 <= j < m + 1 implies (#[trigger] lv2[j]) as int == lvl(a, j) by {
            if j < m {
                assert(lv2[j] == lv[j]);
            } else {
                assert(lv2[j] == l);
            }
        }
        assert forall|j: int| 0 <= j < m + 1 implies (kd(a, j) != NodeKind::Absent ==> node_done(
            a,
            ts,
            j,
            cx_of(cxs[j]),
            #[trigger] lo2[j] as int,
            hi2[j] as int,
        )) by {
            if j < m {
                assert(lv[j] as int == lvl(a, j));
                assert(lo2[j] == lo[j]);
                assert(hi2[j] == hi[j]);
            } else {
                assert(lo2[j] == l0);
                assert(hi2[j] == h0);
            }
        }
    }
}

/// Extending the processed nodes by an `Absent` node, which has no token range of
/// its own: its parent places it.
#[verifier::rlimit(100)]
proof fn lemma_inv_push_absent(
    a: AstV,
    ts: Stream,
    cxs: Seq<Cx5>,
    lo: Seq<usize>,
    hi: Seq<usize>,
    lv: Seq<i32>,
    m: int,
)
    requires
        inv(a, ts, cxs, lo, hi, lv, m),
        0 <= m < a.nodes.len(),
        m < cxs.len(),
        kd(a, m) == NodeKind::Absent,
    ensures
        inv(a, ts, cxs, lo.push(usize::MAX), hi.push(usize::MAX), lv.push(-100i32), m + 1),
{
    let lo2 = lo.push(usize::MAX);
    let hi2 = hi.push(usize::MAX);
    let lv2 = lv.push(-100i32);
    assert(lvl(a, m) == -100);
    assert(inv(a, ts, cxs, lo2, hi2, lv2, m + 1)) by {
        reveal(inv);
        assert(lo2.len() == m + 1);
        assert(hi2.len() == m + 1);
        assert(lv2.len() == m + 1);
        assert forall|j: int| 0 <= j < m + 1 implies (#[trigger] lv2[j]) as int == lvl(a, j)
            && (kd(a, j) != NodeKind::Absent ==> node_done(
            a,
            ts,
            j,
            cx_of(cxs[j]),
            lo2[j] as int,
            hi2[j] as int,
        )) by {
            if j < m {
                assert(lo2[j] == lo[j]);
                assert(hi2[j] == hi[j]);
                assert(lv2[j] == lv[j]);
            } else {
                assert(lv2[j] == -100i32);
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
        0 <= m < a.nodes.len(),
        0 <= c < m,
        a.nodes[m].kind == NodeKind::ParenthesizedExpression,
        a.nodes[m].children =~= seq![c],
        node_done(a, ts, c, cx_in(cx, true), lo_c, hc),
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
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok_t(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, cx_in(g.cx, true), 0);
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 0);
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
    /// The context each node is checked in: the one its parent's production gives
    /// it, which the parent's check compares (`cx_ok`); not trusted otherwise.
    pub cxs: Vec<Cx5>,
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
            done.cxs@,
            done.lo@,
            done.hi@,
            done.lv@,
            nodes.len() as int - 1,
        ),
        cx_ok(arena_of(nodes@), done.cxs@, nodes.len() as int - 1, root_ctx(goal_of(module))),
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
            inv(a, ts, done.cxs@, done.lo@, done.hi@, done.lv@, root as int),
            cx_ok(a, done.cxs@, root as int, cx),
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
            Some(x) => item_kind_exec(x.kind),
            None => false,
        };
        if hi_c != pos || !item {
            return false;
        }
        proof {
            lemma_inv_get(a, ts, done.cxs@, done.lo@, done.hi@, done.lv@, root as int, c as int, cx, k as int - 1);
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
#[verifier::rlimit(400)]
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
    let cxs = assign_ctx(nodes, module);
    let ghost cxs0 = cxs@;
    let mut done = Done {
        lo: Vec::new(),
        hi: Vec::new(),
        lv: Vec::new(),
        cxs,
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
            done.cxs@ == cxs0,
            done.cxs.len() == n,
            done.module == module,
            env_ok(src@, nodes@, toks@, gaps@, ts),
            inv(arena_of(nodes@), ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        decreases last - m,
    {
        let nd = match nodes.get(m) {
            Some(x) => x,
            None => {
                return Derivation::Failed;
            },
        };
        if matches!(nd.kind, NodeKind::Absent) {
            proof {
                let a = arena_of(nodes@);
                assert(a.nodes[m as int] == nodes@[m as int]@);
                assert(nd == &nodes@[m as int]);
                assert(kd(a, m as int) == NodeKind::Absent);
                lemma_env_toks_wf(src@, nodes@, toks@, gaps@, ts);
                lemma_inv_push_absent(a, ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int);
            }
            done.lo.push(usize::MAX);
            done.hi.push(usize::MAX);
            done.lv.push(-100);
            m = m.saturating_add(1);
            continue;
        }
        let cxm: Cx5 = match done.cxs.get(m) {
            Some(c) => *c,
            None => {
                return Derivation::Failed;
            },
        };
        // Most statements and expressions are checked with `[+In]` and no `[Default]`.
        let plain = cxm.i && !cxm.d;
        proof {
            lemma_env_toks_wf(src@, nodes@, toks@, gaps@, ts);
        }
        let ghost cx = cx_of(cxm);
        proof {
            if plain {
                assert(cx_in(cx, true) == cx);
                assert(!cx.deflt);
            }
            assert(cxm == done.cxs@[m as int]);
        }
        let is_arrow = matches!(nd.kind, NodeKind::ArrowFunction | NodeKind::AsyncArrowFunction);
        let is_for = matches!(
            nd.kind,
            NodeKind::ForStatement | NodeKind::ForInStatement | NodeKind::ForOfStatement
        );
        let res = if is_for {
            if !plain {
                return Derivation::Unsupported;
            }
            let cxi = cx5_noin(&cxm);
            if matches!(nd.kind, NodeKind::ForStatement) {
                if !kids_cx4(nodes, done.cxs.as_slice(), m, &cxi, &cxm, &cxm, &cxm) {
                    return Derivation::Unsupported;
                }
                proof {
                    assert(nd == &nodes@[m as int]);
                }
                check_for(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx }))
            } else {
                if !kids_cx3(nodes, done.cxs.as_slice(), m, &cxi, &cxm, &cxm) {
                    return Derivation::Unsupported;
                }
                let sh = InOfShape { m, of: matches!(nd.kind, NodeKind::ForOfStatement) };
                proof {
                    assert(nd == &nodes@[m as int]);
                }
                check_for_in_of(src, nodes, toks, gaps, &done, &sh, Ghost(GCx { ts, cx }))
            }
        } else if matches!(nd.kind, NodeKind::MethodDefinition) {
            let is_async = matches!(nd.op, Op::AsyncMethod | Op::AsyncGeneratorMethod);
            let is_gen = matches!(nd.op, Op::GeneratorMethod | Op::AsyncGeneratorMethod);
            let (c0, c1, c2) = fn_cx5(&cxm, is_async, is_gen, false);
            if !kids_cx3(nodes, done.cxs.as_slice(), m, &c0, &c1, &c2) {
                return Derivation::Unsupported;
            }
            proof {
                assert(nd == &nodes@[m as int]);
            }
            check_method(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx }))
        } else if matches!(nd.kind, NodeKind::ClassStaticBlock) {
            let c0 = Cx5 { y: false, a: true, i: true, r: false, d: false };
            if !kids_cx1(nodes, done.cxs.as_slice(), m, &c0) {
                return Derivation::Unsupported;
            }
            proof {
                assert(nd == &nodes@[m as int]);
            }
            check_static_block(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx }))
        } else if matches!(
            nd.kind,
            NodeKind::VariableDeclaration | NodeKind::LexicalBinding | NodeKind::BindingElement
                | NodeKind::AssignmentElement | NodeKind::AssignmentProperty
        ) {
            // A binding or pattern element has an `Initializer[+In]`; a declaration has `[?In]`.
            let own_init = matches!(nd.kind, NodeKind::BindingElement | NodeKind::AssignmentElement)
                || (matches!(nd.kind, NodeKind::AssignmentProperty) && matches!(nd.op, Op::Shorthand));
            let ci = cx5_in(&cxm);
            let c1 = if own_init { ci } else { cxm };
            if !kids_init(nodes, done.cxs.as_slice(), m, &cxm, &c1) {
                return Derivation::Unsupported;
            }
            proof {
                assert(nd == &nodes@[m as int]);
            }
            if matches!(nd.kind, NodeKind::AssignmentProperty) {
                check_assignment_property(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx }))
            } else {
                check_binding(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx }))
            }
        } else if matches!(nd.kind, NodeKind::ConditionalExpression)
            || (matches!(nd.kind, NodeKind::MemberExpression) && matches!(nd.op, Op::Bracket))
        {
            // The second child (the consequent, the bracketed property) is `[+In]`.
            let ci = cx5_in(&cxm);
            if !kids_init(nodes, done.cxs.as_slice(), m, &cxm, &ci) {
                return Derivation::Unsupported;
            }
            proof {
                assert(nd == &nodes@[m as int]);
            }
            if matches!(nd.kind, NodeKind::ConditionalExpression) {
                check_conditional(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx }))
            } else {
                check_member_bracket(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx }))
            }
        } else if matches!(
            nd.kind,
            NodeKind::ParenthesizedExpression | NodeKind::Arguments | NodeKind::ArrayLiteral
                | NodeKind::ObjectLiteral | NodeKind::TemplateLiteral
        ) {
            // Operands in brackets are `[+In]` whatever the context of the node.
            let ct = cx5_in(&cxm);
            if !kids_cx_t(nodes, done.cxs.as_slice(), m, &cxm, &ct) {
                return Derivation::Unsupported;
            }
            proof {
                assert(nd == &nodes@[m as int]);
            }
            match nd.kind {
                NodeKind::ParenthesizedExpression => check_paren(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
                NodeKind::Arguments => check_arguments(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
                NodeKind::ArrayLiteral => check_array(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
                NodeKind::ObjectLiteral => check_object(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
                _ => check_template(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            }
        } else if is_arrow {
            let is_async = matches!(nd.kind, NodeKind::AsyncArrowFunction);
            if nd.children.len() != 2 {
                return Derivation::Unsupported;
            }
            let pc = match kid_of(nodes, m, 0) {
                Some(c) => c,
                None => {
                    return Derivation::Unsupported;
                },
            };
            let bc = match kid_of(nodes, m, 1) {
                Some(c) => c,
                None => {
                    return Derivation::Unsupported;
                },
            };
            let ident = matches!(kind_at(nodes, pc), NodeKind::BindingIdentifier);
            let braced = matches!(kind_at(nodes, bc), NodeKind::FunctionBody);
            let (c0, c1) = arrow_cx5(&cxm, is_async, ident, braced);
            if !kids_cx2(nodes, done.cxs.as_slice(), m, &c0, &c1) {
                return Derivation::Unsupported;
            }
            let sh = ArrowShape { m, is_async };
            proof {
                assert(nd == &nodes@[m as int]);
            }
            check_arrow(src, nodes, toks, gaps, &done, &sh, Ghost(GCx { ts, cx }))
        } else {
        match fn_flags(nd.kind) {
            Some((fa, fg, fe)) => {
                let (c0, c1, c2) = fn_cx5(&cxm, fa, fg, fe);
                if !kids_cx3(nodes, done.cxs.as_slice(), m, &c0, &c1, &c2) {
                    return Derivation::Unsupported;
                }
                let fs = FuncShape { m, is_async: fa, is_gen: fg, is_expr: fe };
                proof {
                    assert(nd == &nodes@[m as int]);
                }
                check_function(src, nodes, toks, gaps, &done, &fs, Ghost(GCx { ts, cx }))
            },
            None => {
        if !kids_cx(nodes, done.cxs.as_slice(), m, &cxm) {
            return Derivation::Unsupported;
        }
        // The kinds whose checks do not need `[+In]`.
        let any_ctx = matches!(
            nd.kind,
            NodeKind::NumericLiteral | NodeKind::StringLiteral | NodeKind::RegularExpressionLiteral
                | NodeKind::IdentifierName | NodeKind::AdditiveExpression | NodeKind::MultiplicativeExpression
                | NodeKind::ExponentiationExpression | NodeKind::ShiftExpression | NodeKind::EqualityExpression
                | NodeKind::BitwiseANDExpression | NodeKind::BitwiseXORExpression | NodeKind::BitwiseORExpression
                | NodeKind::LogicalANDExpression | NodeKind::LogicalORExpression | NodeKind::CoalesceExpression
                | NodeKind::RelationalExpression | NodeKind::IdentifierReference | NodeKind::BindingIdentifier
                | NodeKind::LabelIdentifier | NodeKind::ThisExpression | NodeKind::NullLiteral
                | NodeKind::BooleanLiteral | NodeKind::UnaryExpression | NodeKind::AssignmentExpression
                | NodeKind::MemberExpression | NodeKind::VariableDeclaration | NodeKind::LexicalBinding
                | NodeKind::VariableDeclarationList | NodeKind::ForDeclaration | NodeKind::LexicalDeclaration
                | NodeKind::UpdateExpression | NodeKind::NewTarget | NodeKind::ImportMeta
                | NodeKind::SuperProperty | NodeKind::SuperCall | NodeKind::OptionalChain
                | NodeKind::OptionalExpression | NodeKind::ArrayBindingPattern
                | NodeKind::ObjectBindingPattern | NodeKind::ArrayAssignmentPattern
                | NodeKind::ObjectAssignmentPattern | NodeKind::BindingProperty
                | NodeKind::BindingRestElement | NodeKind::BindingRestProperty
                | NodeKind::AssignmentRestElement | NodeKind::AssignmentRestProperty
                | NodeKind::Elision | NodeKind::CallExpression | NodeKind::NewExpression
                | NodeKind::TaggedTemplate | NodeKind::Expression
        );
        if !plain && !any_ctx {
            return Derivation::Unsupported;
        }
        match nd.kind {
            NodeKind::VariableDeclarationList => check_var_list(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::ForDeclaration => check_for_decl(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::NumericLiteral | NodeKind::StringLiteral | NodeKind::RegularExpressionLiteral | NodeKind::IdentifierName => {
                proof {
                    lemma_env_literal_facts(src@, nodes@, toks@, gaps@, ts);
                }
                check_literal(nodes, toks, &done.by_start, m, Ghost(ts), Ghost(cx))
            },
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
            NodeKind::ThisExpression | NodeKind::NullLiteral | NodeKind::BooleanLiteral => {
                check_keyword_leaf(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx }))
            },
            NodeKind::IfStatement => check_if(
                src,
                nodes,
                toks,
                gaps,
                &done,
                m,
                Ghost(GCx { ts, cx }),
            ),
            NodeKind::BlockStatement | NodeKind::FunctionBody => check_block(
                src,
                nodes,
                toks,
                gaps,
                &done,
                m,
                Ghost(GCx { ts, cx }),
            ),
            NodeKind::VariableStatement | NodeKind::LexicalDeclaration => check_decl_stmt(
                src,
                nodes,
                toks,
                gaps,
                &done,
                m,
                Ghost(GCx { ts, cx }),
            ),
            NodeKind::CallExpression => check_call(
                src,
                nodes,
                toks,
                gaps,
                &done,
                m,
                Ghost(GCx { ts, cx }),
            ),
            NodeKind::Expression => check_expression(
                src,
                nodes,
                toks,
                gaps,
                &done,
                m,
                Ghost(GCx { ts, cx }),
            ),
            NodeKind::SpreadElement => check_spread(
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
            NodeKind::AssignmentExpression => check_assign(
                src,
                nodes,
                toks,
                gaps,
                &done,
                m,
                Ghost(GCx { ts, cx }),
            ),
            NodeKind::MemberExpression => {
                if matches!(nd.op, Op::Bracket) {
                    return Derivation::Unsupported;
                } else if matches!(nd.op, Op::PrivateDot) {
                    check_member_private(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx }))
                } else {
                    check_member_dot(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx }))
                }
            },
            NodeKind::UpdateExpression => check_update(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::NewExpression => check_new(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
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
            NodeKind::DebuggerStatement => check_debugger(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::ThrowStatement => check_throw(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::BreakStatement | NodeKind::ContinueStatement => check_jump(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::WhileStatement | NodeKind::WithStatement => check_while(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::DoWhileStatement => check_do_while(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::LabelledStatement => check_labelled(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::TryStatement => check_try(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::Catch => check_catch(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::Finally => check_finally(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::SwitchStatement => check_switch(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::CaseClause => check_case(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::DefaultClause => check_default(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::ReturnStatement => check_return(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::FormalParameters => check_params(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::AssignmentRestElement | NodeKind::AssignmentRestProperty => check_binding_rest(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::ArrayBindingPattern | NodeKind::ObjectBindingPattern | NodeKind::ArrayAssignmentPattern
            | NodeKind::ObjectAssignmentPattern => {
                let sh = PatShape {
                    m,
                    array: matches!(nd.kind, NodeKind::ArrayBindingPattern | NodeKind::ArrayAssignmentPattern),
                    assign: matches!(nd.kind, NodeKind::ArrayAssignmentPattern | NodeKind::ObjectAssignmentPattern),
                };
                proof {
                    assert(nd == &nodes@[m as int]);
                }
                check_pattern(src, nodes, toks, gaps, &done, &sh, Ghost(GCx { ts, cx }))
            },
            NodeKind::BindingProperty => check_binding_property(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::BindingRestElement | NodeKind::BindingRestProperty => check_binding_rest(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::TemplateElement => check_template_element(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::TaggedTemplate => check_tagged(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::PrivateIdentifier => check_private(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::FieldDefinition => check_field(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::ClassBody => check_class_body(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::ClassDeclaration | NodeKind::ClassExpression => {
                let sh = ClassShape { m, is_expr: matches!(nd.kind, NodeKind::ClassExpression) };
                proof {
                    assert(nd == &nodes@[m as int]);
                }
                check_class(src, nodes, toks, gaps, &done, &sh, Ghost(GCx { ts, cx }))
            },
            NodeKind::PropertyDefinition => check_property(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::ComputedPropertyName => check_computed(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::Elision => check_elision(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::FunctionRestParameter => check_rest_param(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::YieldExpression => check_yield(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::AwaitExpression => check_await(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::NewTarget | NodeKind::ImportMeta => crate::arena_e::check_meta(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::SuperProperty => crate::arena_e::check_super_prop(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::SuperCall => crate::arena_e::check_super_call(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::ImportCall => {
                if !plain {
                    return Derivation::Unsupported;
                }
                crate::arena_e::check_import_call(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx }))
            },
            NodeKind::OptionalChain => crate::arena_e::check_chain_link(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            NodeKind::OptionalExpression => crate::arena_e::check_optional(src, nodes, toks, gaps, &done, m, Ghost(GCx { ts, cx })),
            _ => {
                return Derivation::Unsupported;
            },
        }
            },
        }
        };
        match res {
            Some((l0, h0, l)) => {
                proof {
                    lemma_inv_push(arena_of(nodes@), ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, l0, h0, l);
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
    // The root's items are in the root's context.
    let root_cx = Cx5 { y: false, a: module, i: true, r: false, d: false };
    proof {
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, ts);
        assert(cx_of(root_cx) == root_ctx(goal_of(module)));
    }
    if !kids_cx(nodes, done.cxs.as_slice(), last, &root_cx) {
        return Derivation::Unsupported;
    }
    if check_root(src, nodes, toks, gaps, &done, module, Ghost(ts)) {
        Derivation::Verified
    } else {
        Derivation::Unsupported
    }
}

/// The context each node of the arena is to be checked in, from the root down (a
/// node's index is above its children's). Untrusted: [`kids_cx`] compares it with
/// what the production of the parent gives, so a wrong guess is `Unsupported`.
fn assign_ctx(nodes: &[Node], module: bool) -> (r: Vec<Cx5>)
    ensures
        r.len() == nodes.len(),
{
    let n = nodes.len();
    let root = Cx5 { y: false, a: module, i: true, r: false, d: false };
    let mut cxs: Vec<Cx5> = Vec::new();
    let mut q: usize = 0;
    while q < n
        invariant
            q <= n,
            cxs.len() == q,
        decreases n - q,
    {
        cxs.push(root);
        q = q.saturating_add(1);
    }
    let mut i = n;
    while i > 0
        invariant
            i <= n,
            n == nodes.len(),
            cxs.len() == n,
        decreases i,
    {
        i = i.saturating_sub(1);
        let p: Cx5 = match cxs.get(i) {
            Some(p) => *p,
            None => {
                return cxs;
            },
        };
        let nd = match nodes.get(i) {
            Some(x) => x,
            None => {
                return cxs;
            },
        };
        let len = nd.children.len();
        // An arrow function's parts depend on the kinds of its parameters and body.
        let arrow = matches!(nd.kind, NodeKind::ArrowFunction | NodeKind::AsyncArrowFunction);
        let method = matches!(nd.kind, NodeKind::MethodDefinition);
        let ident = if method {
            matches!(nd.op, Op::AsyncMethod | Op::AsyncGeneratorMethod)
        } else if matches!(nd.kind, NodeKind::AssignmentProperty) {
            matches!(nd.op, Op::Shorthand)
        } else if matches!(nd.kind, NodeKind::MemberExpression) {
            matches!(nd.op, Op::Bracket)
        } else {
            arrow && child_kind_is(nodes, nd, 0, true)
        };
        let braced = if method {
            matches!(nd.op, Op::GeneratorMethod | Op::AsyncGeneratorMethod)
        } else {
            arrow && child_kind_is(nodes, nd, 1, false)
        };
        let mut k: usize = 0;
        while k < len
            invariant
                k <= len,
                len == nd.children.len(),
                cxs.len() == n,
            decreases len - k,
        {
            if let Some(c) = nd.children.as_slice().get(k) {
                let c = *c as usize;
                if c < n {
                    let cc = child_cx(nd.kind, k, &p, ident, braced);
                    cxs.set(c, cc);
                }
            }
            k = k.saturating_add(1);
        }
    }
    cxs
}

/// Child `idx` of `nd` is a `BindingIdentifier` (`ident`) or a `FunctionBody`.
fn child_kind_is(nodes: &[Node], nd: &Node, idx: usize, ident: bool) -> bool {
    let c = match nd.children.as_slice().get(idx) {
        Some(c) => *c as usize,
        None => {
            return false;
        },
    };
    match nodes.get(c) {
        Some(x) => if ident {
            matches!(x.kind, NodeKind::BindingIdentifier)
        } else {
            matches!(x.kind, NodeKind::FunctionBody)
        },
        None => false,
    }
}

/// The context the production of node kind `kind` gives its child `k`, when it is
/// checked in `p`: `[+In]`, as the statements and expressions covered so far have.
fn child_cx(kind: NodeKind, k: usize, p: &Cx5, ident: bool, braced: bool) -> (r: Cx5) {
    if let Some((fa, fg, fe)) = fn_flags(kind) {
        let (c0, c1, c2) = fn_cx5(p, fa, fg, fe);
        return if k == 0 {
            c0
        } else if k == 1 {
            c1
        } else {
            c2
        };
    }
    if matches!(kind, NodeKind::ArrowFunction | NodeKind::AsyncArrowFunction) {
        let (c0, c1) = arrow_cx5(p, matches!(kind, NodeKind::AsyncArrowFunction), ident, braced);
        return if k == 0 { c0 } else { c1 };
    }
    if matches!(kind, NodeKind::MethodDefinition) {
        // `ident` is `async`, `braced` a generator, for a method.
        let (c0, c1, c2) = fn_cx5(p, ident, braced, false);
        return if k == 0 {
            c0
        } else if k == 1 {
            c1
        } else {
            c2
        };
    }
    if matches!(kind, NodeKind::ClassStaticBlock) {
        return Cx5 { y: false, a: true, i: true, r: false, d: false };
    }
    if matches!(
        kind,
        NodeKind::ForStatement | NodeKind::ForInStatement | NodeKind::ForOfStatement
    ) {
        return if k == 0 { cx5_noin(p) } else { *p };
    }
    // `a[b]`: the property is `[+In]` (`ident` is the bracket form); `a ? b : c`: so is `b`.
    if matches!(kind, NodeKind::MemberExpression) {
        return if k == 1 && ident { Cx5 { y: p.y, a: p.a, i: true, r: p.r, d: false } } else { *p };
    }
    if matches!(kind, NodeKind::ConditionalExpression) {
        return if k == 1 { Cx5 { y: p.y, a: p.a, i: true, r: p.r, d: false } } else { *p };
    }
    // These productions pass their own context to their children.
    if matches!(
        kind,
        NodeKind::AdditiveExpression | NodeKind::MultiplicativeExpression | NodeKind::ExponentiationExpression
            | NodeKind::ShiftExpression | NodeKind::EqualityExpression | NodeKind::BitwiseANDExpression
            | NodeKind::BitwiseXORExpression | NodeKind::BitwiseORExpression | NodeKind::LogicalANDExpression
            | NodeKind::LogicalORExpression | NodeKind::CoalesceExpression | NodeKind::RelationalExpression
            | NodeKind::UnaryExpression | NodeKind::AssignmentExpression | NodeKind::MemberExpression
            | NodeKind::VariableDeclaration | NodeKind::LexicalBinding | NodeKind::VariableDeclarationList
            | NodeKind::LexicalDeclaration | NodeKind::ForDeclaration | NodeKind::UpdateExpression
            | NodeKind::SuperProperty | NodeKind::SuperCall | NodeKind::OptionalChain
            | NodeKind::OptionalExpression | NodeKind::ArrayBindingPattern
            | NodeKind::ObjectBindingPattern | NodeKind::ArrayAssignmentPattern
            | NodeKind::ObjectAssignmentPattern | NodeKind::BindingProperty
            | NodeKind::BindingRestElement | NodeKind::BindingRestProperty
            | NodeKind::AssignmentRestElement | NodeKind::AssignmentRestProperty
            | NodeKind::CallExpression | NodeKind::NewExpression | NodeKind::TaggedTemplate
            | NodeKind::Expression
    ) {
        return *p;
    }
    // A pattern element's initializer is `[+In]`, its target the element's own.
    if matches!(kind, NodeKind::BindingElement | NodeKind::AssignmentElement) {
        return if k == 0 { *p } else { Cx5 { y: p.y, a: p.a, i: true, r: p.r, d: false } };
    }
    // `ident` is a shorthand property: `{ a = 1 }`.
    if matches!(kind, NodeKind::AssignmentProperty) {
        return if k == 0 || !ident { *p } else { Cx5 { y: p.y, a: p.a, i: true, r: p.r, d: false } };
    }
    Cx5 { y: p.y, a: p.a, i: true, r: p.r, d: false }
}

/// Node `m` and its children are all checked in `p` (`cx_ok`).
fn kids_cx(nodes: &[Node], cxs: &[Cx5], m: usize, p: &Cx5) -> (r: bool)
    requires
        m < nodes.len(),
        cxs.len() == nodes.len(),
        ast_wf(arena_of(nodes@)),
    ensures
        r ==> cx_ok(arena_of(nodes@), cxs@, m as int, cx_of(*p)),
{
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    match cxs.get(m) {
        Some(c) => {
            if !cx_eq(c, p) {
                return false;
            }
        },
        None => {
            return false;
        },
    }
    let len = nd.children.len();
    let ghost a = arena_of(nodes@);
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children.len() == len);
    }
    let mut k: usize = 0;
    while k < len
        invariant
            m < nodes.len(),
            nodes@.len() == nodes.len(),
            a == arena_of(nodes@),
            ast_wf(a),
            nd == &nodes@[m as int],
            len == nd.children.len(),
            len == a.nodes[m as int].children.len(),
            k <= len,
            cxs.len() == nodes.len(),
            cx_of(cxs@[m as int]) == cx_of(*p),
            forall|q: int|
                0 <= q < k ==> 0 <= #[trigger] a.nodes[m as int].children[q] < cxs.len()
                    && cx_of(cxs@[a.nodes[m as int].children[q]]) == cx_of(*p),
        decreases len - k,
    {
        let c = match nd.children.as_slice().get(k) {
            Some(x) => *x as usize,
            None => {
                return false;
            },
        };
        proof {
            assert(a.nodes[m as int].children[k as int] == c as int);
            lemma_child_before(a, m as int, k as int);
        }
        let cc = match cxs.get(c) {
            Some(x) => x,
            None => {
                return false;
            },
        };
        if !cx_eq(cc, p) {
            return false;
        }
        k = k.saturating_add(1);
    }
    true
}

/// Node `m` is checked in `c` and each of its children in `ct`, the `[+In]` context of `c`
/// (`cx_ok_t`): the productions whose operands are in brackets.
fn kids_cx_t(nodes: &[Node], cxs: &[Cx5], m: usize, c: &Cx5, ct: &Cx5) -> (r: bool)
    requires
        m < nodes.len(),
        cxs.len() == nodes.len(),
        ast_wf(arena_of(nodes@)),
        cx_of(*ct) == cx_in(cx_of(*c), true),
    ensures
        r ==> cx_ok_t(arena_of(nodes@), cxs@, m as int, cx_of(*c)),
{
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    match cxs.get(m) {
        Some(x) => {
            if !cx_eq(x, c) {
                return false;
            }
        },
        None => {
            return false;
        },
    }
    let len = nd.children.len();
    let ghost a = arena_of(nodes@);
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children.len() == len);
    }
    let mut k: usize = 0;
    while k < len
        invariant
            m < nodes.len(),
            nodes@.len() == nodes.len(),
            a == arena_of(nodes@),
            ast_wf(a),
            nd == &nodes@[m as int],
            len == nd.children.len(),
            len == a.nodes[m as int].children.len(),
            k <= len,
            cxs.len() == nodes.len(),
            cx_of(*ct) == cx_in(cx_of(*c), true),
            cx_of(cxs@[m as int]) == cx_of(*c),
            forall|q: int|
                0 <= q < k ==> 0 <= #[trigger] a.nodes[m as int].children[q] < cxs.len()
                    && cx_of(cxs@[a.nodes[m as int].children[q]]) == cx_of(*ct),
        decreases len - k,
    {
        let ch = match nd.children.as_slice().get(k) {
            Some(x) => *x as usize,
            None => {
                return false;
            },
        };
        proof {
            assert(a.nodes[m as int].children[k as int] == ch as int);
            lemma_child_before(a, m as int, k as int);
        }
        let cc = match cxs.get(ch) {
            Some(x) => x,
            None => {
                return false;
            },
        };
        if !cx_eq(cc, ct) {
            return false;
        }
        k = k.saturating_add(1);
    }
    true
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

// ---------------------------------------------------------------------
// The rest of the statements of §14 that the check covers: `while`, `do`-`while`,
// `throw`, `break`, `continue`, labelled, `try`, `switch` and `debugger`.
// ---------------------------------------------------------------------

/// The words of those statements, as code points.
pub(crate) proof fn lemma_words2()
    ensures
        cps("do"@) =~= seq![0x64u32, 0x6F],
        cps("while"@) =~= seq![0x77u32, 0x68, 0x69, 0x6C, 0x65],
        cps("throw"@) =~= seq![0x74u32, 0x68, 0x72, 0x6F, 0x77],
        cps("break"@) =~= seq![0x62u32, 0x72, 0x65, 0x61, 0x6B],
        cps("continue"@) =~= seq![0x63u32, 0x6F, 0x6E, 0x74, 0x69, 0x6E, 0x75, 0x65],
        cps("debugger"@) =~= seq![0x64u32, 0x65, 0x62, 0x75, 0x67, 0x67, 0x65, 0x72],
        cps("try"@) =~= seq![0x74u32, 0x72, 0x79],
        cps("catch"@) =~= seq![0x63u32, 0x61, 0x74, 0x63, 0x68],
        cps("finally"@) =~= seq![0x66u32, 0x69, 0x6E, 0x61, 0x6C, 0x6C, 0x79],
        cps("switch"@) =~= seq![0x73u32, 0x77, 0x69, 0x74, 0x63, 0x68],
        cps("case"@) =~= seq![0x63u32, 0x61, 0x73, 0x65],
        cps("default"@) =~= seq![0x64u32, 0x65, 0x66, 0x61, 0x75, 0x6C, 0x74],
        cps("}"@) =~= seq![0x7Du32],
        cps("with"@) =~= seq![0x77u32, 0x69, 0x74, 0x68],
{
    reveal_strlit("with");
    assert("with"@ =~= seq!['w', 'i', 't', 'h']);
    reveal_strlit("do");
    reveal_strlit("while");
    reveal_strlit("throw");
    reveal_strlit("break");
    reveal_strlit("continue");
    reveal_strlit("debugger");
    reveal_strlit("try");
    reveal_strlit("catch");
    reveal_strlit("finally");
    reveal_strlit("switch");
    reveal_strlit("case");
    reveal_strlit("default");
    reveal_strlit("}");
    assert("do"@ =~= seq!['d', 'o']);
    assert("while"@ =~= seq!['w', 'h', 'i', 'l', 'e']);
    assert("throw"@ =~= seq!['t', 'h', 'r', 'o', 'w']);
    assert("break"@ =~= seq!['b', 'r', 'e', 'a', 'k']);
    assert("continue"@ =~= seq!['c', 'o', 'n', 't', 'i', 'n', 'u', 'e']);
    assert("debugger"@ =~= seq!['d', 'e', 'b', 'u', 'g', 'g', 'e', 'r']);
    assert("try"@ =~= seq!['t', 'r', 'y']);
    assert("catch"@ =~= seq!['c', 'a', 't', 'c', 'h']);
    assert("finally"@ =~= seq!['f', 'i', 'n', 'a', 'l', 'l', 'y']);
    assert("switch"@ =~= seq!['s', 'w', 'i', 't', 'c', 'h']);
    assert("case"@ =~= seq!['c', 'a', 's', 'e']);
    assert("default"@ =~= seq!['d', 'e', 'f', 'a', 'u', 'l', 't']);
    assert("}"@ =~= seq!['}']);
}

/// Child `k` of node `m` of a well-formed arena, which is before `m`.
pub(crate) fn kid_of(nodes: &[Node], m: usize, k: usize) -> (r: Option<usize>)
    requires
        m < nodes.len(),
        ast_wf(arena_of(nodes@)),
    ensures
        match r {
            Some(c) => c < m && k < arena_of(nodes@).nodes[m as int].children.len() && arena_of(
                nodes@,
            ).nodes[m as int].children[k as int] == c as int,
            None => true,
        },
{
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let c = match nd.children.as_slice().get(k) {
        Some(x) => *x as usize,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        lemma_child_before(a, m as int, k as int);
    }
    if c >= m {
        return None;
    }
    Some(c)
}

/// The kind of node `c`.
pub(crate) fn kind_at(nodes: &[Node], c: usize) -> (r: NodeKind)
    requires
        c < nodes.len(),
    ensures
        r == kd(arena_of(nodes@), c as int),
{
    match nodes.get(c) {
        Some(x) => {
            proof {
                let a = arena_of(nodes@);
                assert(a.nodes[c as int] == nodes@[c as int]@);
                assert(x == &nodes@[c as int]);
            }
            x.kind
        },
        None => {
            proof {
                assert(false);
            }
            NodeKind::Absent
        },
    }
}

/// What the check recorded of node `c`: first token, one past the last, strength.
pub(crate) fn done_at(done: &Done, c: usize) -> (r: Option<(usize, usize, i32)>)
    ensures
        match r {
            Some((l, h, v)) => c < done.lo@.len() && c < done.hi@.len() && c < done.lv@.len() && l
                == done.lo@[c as int] && h == done.hi@[c as int] && v == done.lv@[c as int],
            None => true,
        },
{
    let l = match done.lo.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let h = match done.hi.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    let v = match done.lv.get(c) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    Some((l, h, v))
}

/// The token a node starts at.
pub(crate) fn start_tok(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    m: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<usize>)
    requires
        m < nodes.len(),
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
    ensures
        match r {
            Some(x) => x < toks.len() && g.ts.toks[x as int].start == nodes@[m as int].start as int,
            None => true,
        },
{
    let _ = (src.len(), gaps.len());
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
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
        assert(nd == &nodes@[m as int]);
    }
    if t.start != nd.start {
        return None;
    }
    Some(x)
}

/// The context, and the characters of the word or punctuator a token is checked against.
pub struct GW {
    /// The stream and context.
    pub g: GCx,
    /// The characters of the word.
    pub w: Seq<char>,
}

/// Token `x` is the keyword `w` (`gw.w` as characters).
pub(crate) fn word_at(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    x: usize,
    w: &[u32],
    Ghost(gw): Ghost<GW>,
) -> (r: bool)
    requires
        env_ok(src@, nodes@, toks@, gaps@, gw.g.ts),
        cps(gw.w) =~= w@,
    ensures
        r ==> x < toks.len() && is_kw(gw.g.ts, x as int, gw.w),
{
    let _ = (nodes.len(), gaps.len());
    let ghost g = gw.g;
    let ghost ws = gw.w;
    let t = match toks.get(x) {
        Some(t) => t,
        None => {
            return false;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, x as int);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        assert(t == &toks@[x as int]);
    }
    let r = matches!(t.kind, TokKind::IdentifierName) && !t.escaped && text_is(src, t, w);
    proof {
        if r {
            assert(g.ts.toks[x as int].text =~= src@.subrange(t.start as int, t.end as int));
            assert(g.ts.toks[x as int].text =~= cps(ws));
        }
    }
    r
}

/// Token `x` is the one-character punctuator `lit` (code point `code`).
pub(crate) fn punct_at(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    x: usize,
    code: u32,
    Ghost(gw): Ghost<GW>,
) -> (r: bool)
    requires
        env_ok(src@, nodes@, toks@, gaps@, gw.g.ts),
        cps(gw.w) =~= seq![code],
    ensures
        r ==> x < toks.len() && is_p(gw.g.ts, x as int, gw.w),
{
    let _ = (nodes.len(), gaps.len());
    let ghost g = gw.g;
    let ghost lit = gw.w;
    let t = match toks.get(x) {
        Some(t) => t,
        None => {
            return false;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, x as int);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        assert(t == &toks@[x as int]);
    }
    let r = matches!(t.kind, TokKind::Punctuator) && text_is1(src, t, code);
    proof {
        if r {
            assert(g.ts.toks[x as int].text =~= src@.subrange(t.start as int, t.end as int));
            assert(g.ts.toks[x as int].text =~= cps(lit));
        }
    }
    r
}

/// No line terminator before token `x`.
pub(crate) fn no_nl_at(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    x: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: bool)
    requires
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
    ensures
        r ==> !nl(g.ts, x as int),
{
    let _ = (src.len(), nodes.len(), gaps.len());
    proof {
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    match toks.get(x) {
        Some(t) => {
            proof {
                lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, x as int);
                assert(t == &toks@[x as int]);
            }
            !t.nl
        },
        None => true,
    }
}

/// The token before `j` ends where `e` says.
pub(crate) fn end_ok(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    e: usize,
    j: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: bool)
    requires
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
    ensures
        r ==> 1 <= j && j <= toks.len() && g.ts.toks[j as int - 1].end == e as int,
{
    let _ = (src.len(), nodes.len(), gaps.len());
    if j < 1 || j > toks.len() {
        return false;
    }
    let t = match toks.get(j.saturating_sub(1)) {
        Some(t) => t,
        None => {
            return false;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, j as int - 1);
        assert(j.saturating_sub(1) as int == j as int - 1);
        assert(t == &toks@[j as int - 1]);
    }
    t.end == e
}

/// [`find_semi`] for the `;` after `do`-`while` (§12.10.1 rule 1, third condition).
pub(crate) fn find_semi_dw(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    hc: usize,
    end: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<usize>)
    requires
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
    ensures
        match r {
            Some(j) => semi(g.ts, hc as int, j as int, true) && 1 <= j && j <= toks.len() && g.ts.toks[j as int
                - 1].end == end as int && hc <= j,
            None => true,
        },
{
    if let Some(j) = find_semi(src, nodes, toks, gaps, hc, end, Ghost(g)) {
        proof {
            assert(semi(g.ts, hc as int, j as int, false));
        }
        return Some(j);
    }
    let g0 = match gaps.get(hc) {
        Some(x) => x,
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
    if !matches!(g0, Ins::DoWhile) || hc < 1 || end != prev.end {
        return None;
    }
    proof {
        lemma_env_gap(src@, nodes@, toks@, gaps@, g.ts, hc as int);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, hc as int - 1);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        assert(hc.saturating_sub(1) as int == hc as int - 1);
        assert(prev.end as int == g.ts.toks[hc as int - 1].end);
        assert(hc <= toks.len());
    }
    Some(hc)
}

/// §14.16 `debugger ;`.
#[verifier::spinoff_prover]
proof fn lemma_debugger_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int, j: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        a.nodes[m].kind == NodeKind::DebuggerStatement,
        a.nodes[m].children.len() == 0,
        is_kw(ts, x, "debugger"@),
        semi(ts, x + 1, j, false),
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(d_stmt(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.16 `debugger ;`.
#[verifier::spinoff_prover]
fn check_debugger(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_words2();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::DebuggerStatement) || !nd.children.is_empty() {
        return None;
    }
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !word_at(src, nodes, toks, gaps, x, &[0x64, 0x65, 0x62, 0x75, 0x67, 0x67, 0x65, 0x72], Ghost(GW { g, w: "debugger"@ })) {
        return None;
    }
    let j = match find_semi(src, nodes, toks, gaps, x.saturating_add(1), nd.end, Ghost(g)) {
        Some(j) => j,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(a.nodes[m as int].children.len() == 0);
        lemma_debugger_done(a, g.ts, g.cx, m as int, x as int, j as int);
    }
    Some((x, j, -100))
}

/// §14.14 `throw Expression ;`.
#[verifier::spinoff_prover]
proof fn lemma_throw_done(a: AstV, ts: Stream, cx: Ctx, m: int, e: int, x: int, me: int, j: int)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= e < m,
        a.nodes[m].kind == NodeKind::ThrowStatement,
        a.nodes[m].children =~= seq![e],
        is_kw(ts, x, "throw"@),
        !nl(ts, x + 1),
        lvl(a, e) >= -1,
        node_done(a, ts, e, cx, x + 1, me),
        semi(ts, me, j, false),
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == e);
    assert(dc(a, ts, m, e, cx_in(cx, true), x + 1, me));
    assert(d_stmt(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.14 `throw [no LineTerminator here] Expression ;`.
#[verifier::spinoff_prover]
fn check_throw(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_words2();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::ThrowStatement) || nd.children.len() != 1 {
        return None;
    }
    let e = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let (lo_e, me, lv_e) = match done_at(done, e) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if lv_e < -1 || lo_e != x.saturating_add(1) {
        return None;
    }
    if !word_at(src, nodes, toks, gaps, x, &[0x74, 0x68, 0x72, 0x6F, 0x77], Ghost(GW { g, w: "throw"@ }))
        || !no_nl_at(src, nodes, toks, gaps, x.saturating_add(1), Ghost(g)) {
        return None;
    }
    let j = match find_semi(src, nodes, toks, gaps, me, nd.end, Ghost(g)) {
        Some(j) => j,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![e as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
        }
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, e as int, g.cx, 0);
        assert(lvl(a, e as int) >= -1);
        lemma_throw_done(a, g.ts, g.cx, m as int, e as int, x as int, me as int, j as int);
    }
    Some((x, j, -100))
}

/// §14.8 `continue` and §14.9 `break`.
#[verifier::spinoff_prover]
proof fn lemma_jump_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    c: int,
    x: int,
    labelled: bool,
    j: int,
    is_break: bool,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= c < m,
        a.nodes[m].kind == (if is_break {
            NodeKind::BreakStatement
        } else {
            NodeKind::ContinueStatement
        }),
        a.nodes[m].children =~= seq![c],
        is_kw(ts, x, if is_break {
            "break"@
        } else {
            "continue"@
        }),
        if labelled {
            kd(a, c) == NodeKind::LabelIdentifier && !nl(ts, x + 1) && node_done(
                a,
                ts,
                c,
                cx,
                x + 1,
                x + 2,
            ) && semi(ts, x + 2, j, false)
        } else {
            kd(a, c) == NodeKind::Absent && d(a, ts, c, cx, x + 1, x + 1) && semi(
                ts,
                x + 1,
                j,
                false,
            )
        },
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == c);
    if labelled {
        assert(dc(a, ts, m, c, cx, x + 1, x + 2));
    } else {
        assert(dc(a, ts, m, c, cx, x + 1, x + 1));
    }
    assert(d_stmt(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.8 `continue`, §14.9 `break`, with an optional label.
#[verifier::spinoff_prover]
fn check_jump(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_words2();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let is_break = matches!(nd.kind, NodeKind::BreakStatement);
    if !(is_break || matches!(nd.kind, NodeKind::ContinueStatement)) || nd.children.len() != 1 {
        return None;
    }
    let c = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let ok = if is_break {
        word_at(src, nodes, toks, gaps, x, &[0x62, 0x72, 0x65, 0x61, 0x6B], Ghost(GW { g, w: "break"@ }))
    } else {
        word_at(src, nodes, toks, gaps, x, &[0x63, 0x6F, 0x6E, 0x74, 0x69, 0x6E, 0x75, 0x65], Ghost(GW { g, w: "continue"@ }))
    };
    if !ok {
        return None;
    }
    let x1 = x.saturating_add(1);
    let kc = kind_at(nodes, c);
    let labelled = matches!(kc, NodeKind::LabelIdentifier);
    let j: usize;
    if labelled {
        let (lo_c, hi_c, _) = match done_at(done, c) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        let x2 = x.saturating_add(2);
        if lo_c != x1 || hi_c != x2 || !no_nl_at(src, nodes, toks, gaps, x1, Ghost(g)) {
            return None;
        }
        j = match find_semi(src, nodes, toks, gaps, x2, nd.end, Ghost(g)) {
            Some(j) => j,
            None => {
                return None;
            },
        };
        proof {
            let a = arena_of(nodes@);
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 0);
            assert(x1 as int == x as int + 1);
            assert(x2 as int == x as int + 2);
        }
    } else {
        if !matches!(kc, NodeKind::Absent) {
            return None;
        }
        if !check_absent(src, nodes, toks, gaps, c, x1, Ghost(g)) {
            return None;
        }
        j = match find_semi(src, nodes, toks, gaps, x1, nd.end, Ghost(g)) {
            Some(j) => j,
            None => {
                return None;
            },
        };
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x1 as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_jump_done(a, g.ts, g.cx, m as int, c as int, x as int, labelled, j as int, is_break);
    }
    Some((x, j, -100))
}

/// §14.7.3 `while ( Expression ) Statement`.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
proof fn lemma_while_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    t: int,
    c: int,
    x: int,
    mt: int,
    j: int,
)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= t < m,
        0 <= c < m,
        a.nodes[m].kind == NodeKind::WhileStatement || a.nodes[m].kind == NodeKind::WithStatement,
        a.nodes[m].children =~= seq![t, c],
        is_p(ts, x + 1, "("@),
        is_kw(ts, x, if a.nodes[m].kind == NodeKind::WhileStatement { "while"@ } else { "with"@ }),
        lvl(a, t) >= -1,
        node_done(a, ts, t, cx, x + 2, mt),
        is_p(ts, mt, ")"@),
        node_done(a, ts, c, cx, mt + 1, j),
        is_statement_kind(kd(a, c)),
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == t);
    assert(a.nodes[m].children[1] == c);
    assert(dc(a, ts, m, t, cx_in(cx, true), x + 2, mt));
    assert(dc(a, ts, m, c, cx, mt + 1, j));
    assert(ed(a, ts, t, x + 2) == mt);
    assert(a.nodes[m].children.len() == 2);
    assert(is_p(ts, mt, ")"@));
    if a.nodes[m].kind == NodeKind::WhileStatement {
        assert(is_kw(ts, x, "while"@));
        assert(d_stmt(a, ts, m, cx, x, j));
    } else {
        assert(a.nodes[m].kind == NodeKind::WithStatement);
        assert(is_kw(ts, x, "with"@));
        assert(d_stmt(a, ts, m, cx, x, j));
    }
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.7.3 `while ( Expression ) Statement`.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
fn check_while(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_words2();
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::WhileStatement | NodeKind::WithStatement) || nd.children.len() != 2 {
        return None;
    }
    let t = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let c = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let (lo_t, mt, lv_t) = match done_at(done, t) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let (lo_c, j, _) = match done_at(done, c) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let c_ok = stmt_kind_exec(kind_at(nodes, c));
    if !c_ok || lv_t < -1 || lo_t != x.saturating_add(2) || lo_c != mt.saturating_add(1) {
        return None;
    }
    let kw_ok = if matches!(nd.kind, NodeKind::WhileStatement) {
        word_at(src, nodes, toks, gaps, x, &[0x77, 0x68, 0x69, 0x6C, 0x65], Ghost(GW { g, w: "while"@ }))
    } else {
        word_at(src, nodes, toks, gaps, x, &[0x77, 0x69, 0x74, 0x68], Ghost(GW { g, w: "with"@ }))
    };
    if !kw_ok
        || !punct_at(src, nodes, toks, gaps, x.saturating_add(1), 0x28, Ghost(GW { g, w: "("@ }))
        || !punct_at(src, nodes, toks, gaps, mt, 0x29, Ghost(GW { g, w: ")"@ }))
        || !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(x.saturating_add(2) as int == x as int + 2);
        assert(mt.saturating_add(1) as int == mt as int + 1);
        assert(a.nodes[m as int].children =~= seq![t as int, c as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, t as int, g.cx, 0);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 1);
        assert(lvl(a, t as int) >= -1);
        assert(is_statement_kind(kd(a, c as int)));
        if matches!(nd.kind, NodeKind::WhileStatement) {
            assert(is_kw(g.ts, x as int, "while"@));
        } else {
            assert(is_kw(g.ts, x as int, "with"@));
        }
        lemma_while_done(a, g.ts, g.cx, m as int, t as int, c as int, x as int, mt as int, j as int);
    }
    Some((x, j, -100))
}

/// §14.7.2 `do Statement while ( Expression ) ;`.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
proof fn lemma_do_while_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    b: int,
    t: int,
    x: int,
    mb: int,
    q: int,
    j: int,
)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= b < m,
        0 <= t < m,
        a.nodes[m].kind == NodeKind::DoWhileStatement,
        a.nodes[m].children =~= seq![b, t],
        is_kw(ts, x, "do"@),
        node_done(a, ts, b, cx, x + 1, mb),
        is_statement_kind(kd(a, b)),
        is_kw(ts, mb, "while"@),
        is_p(ts, mb + 1, "("@),
        lvl(a, t) >= -1,
        node_done(a, ts, t, cx, mb + 2, q),
        is_p(ts, q, ")"@),
        semi(ts, q + 1, j, true),
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == b);
    assert(a.nodes[m].children[1] == t);
    assert(dc(a, ts, m, b, cx, x + 1, mb));
    assert(dc(a, ts, m, t, cx_in(cx, true), mb + 2, q));
    assert(ed(a, ts, b, x + 1) == mb);
    assert(ed(a, ts, t, mb + 2) == q);
    assert(a.nodes[m].children.len() == 2);
    assert(is_kw(ts, mb, "while"@));
    assert(semi(ts, q + 1, j, true));
    assert(d_stmt(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.7.2 `do Statement while ( Expression ) ;`.
#[verifier::spinoff_prover]
fn check_do_while(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_words2();
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::DoWhileStatement) || nd.children.len() != 2 {
        return None;
    }
    let b = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let t = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let (lo_b, mb, _) = match done_at(done, b) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let (lo_t, q, lv_t) = match done_at(done, t) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let b_ok = stmt_kind_exec(kind_at(nodes, b));
    if !b_ok || lv_t < -1 || lo_b != x.saturating_add(1) || lo_t != mb.saturating_add(2) {
        return None;
    }
    if !word_at(src, nodes, toks, gaps, x, &[0x64, 0x6F], Ghost(GW { g, w: "do"@ }))
        || !word_at(src, nodes, toks, gaps, mb, &[0x77, 0x68, 0x69, 0x6C, 0x65], Ghost(GW { g, w: "while"@ }))
        || !punct_at(src, nodes, toks, gaps, mb.saturating_add(1), 0x28, Ghost(GW { g, w: "("@ }))
        || !punct_at(src, nodes, toks, gaps, q, 0x29, Ghost(GW { g, w: ")"@ })) {
        return None;
    }
    let j = match find_semi_dw(src, nodes, toks, gaps, q.saturating_add(1), nd.end, Ghost(g)) {
        Some(j) => j,
        None => {
            return None;
        },
    };
    if j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(mb.saturating_add(1) as int == mb as int + 1);
        assert(mb.saturating_add(2) as int == mb as int + 2);
        assert(q.saturating_add(1) as int == q as int + 1);
        assert(a.nodes[m as int].children =~= seq![b as int, t as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, b as int, g.cx, 0);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, t as int, g.cx, 1);
        assert(lvl(a, t as int) >= -1);
        assert(is_statement_kind(kd(a, b as int)));
        lemma_do_while_done(a, g.ts, g.cx, m as int, b as int, t as int, x as int, mb as int, q as int, j as int);
    }
    Some((x, j, -100))
}

/// §14.13 `LabelIdentifier : LabelledItem`.
#[verifier::spinoff_prover]
proof fn lemma_labelled_done(a: AstV, ts: Stream, cx: Ctx, m: int, l: int, b: int, x: int, j: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= l < m,
        0 <= b < m,
        a.nodes[m].kind == NodeKind::LabelledStatement,
        a.nodes[m].children =~= seq![l, b],
        kd(a, l) == NodeKind::LabelIdentifier,
        node_done(a, ts, l, cx, x, x + 1),
        is_p(ts, x + 1, ":"@),
        is_stmt_or_function(a, b),
        node_done(a, ts, b, cx, x + 2, j),
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == l);
    assert(a.nodes[m].children[1] == b);
    assert(dc(a, ts, m, l, cx, x, x + 1));
    assert(dc(a, ts, m, b, cx, x + 2, j));
    assert(d_stmt(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.13 `LabelIdentifier : LabelledItem`.
#[verifier::spinoff_prover]
fn check_labelled(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::LabelledStatement) || nd.children.len() != 2 {
        return None;
    }
    let l = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let b = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let (lo_l, hi_l, _) = match done_at(done, l) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let (lo_b, j, _) = match done_at(done, b) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let b_ok = stmt_or_fn_exec(kind_at(nodes, b));
    let l_ok = matches!(kind_at(nodes, l), NodeKind::LabelIdentifier);
    if !b_ok || !l_ok || lo_l != x || hi_l != x.saturating_add(1) || lo_b != x.saturating_add(2) {
        return None;
    }
    if !punct_at(src, nodes, toks, gaps, x.saturating_add(1), 0x3A, Ghost(GW { g, w: ":"@ }))
        || !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(x.saturating_add(2) as int == x as int + 2);
        assert(a.nodes[m as int].children =~= seq![l as int, b as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, l as int, g.cx, 0);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, b as int, g.cx, 1);
        assert(is_stmt_or_function(a, b as int));
        lemma_labelled_done(a, g.ts, g.cx, m as int, l as int, b as int, x as int, j as int);
    }
    Some((x, j, -100))
}

/// §14.15 `try Block Catch? Finally?`.
#[verifier::spinoff_prover]
proof fn lemma_try_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    b: int,
    ca: int,
    fi: int,
    x: int,
    mb: int,
    q: int,
    j: int,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= b < m,
        0 <= ca < m,
        0 <= fi < m,
        a.nodes[m].kind == NodeKind::TryStatement,
        a.nodes[m].children =~= seq![b, ca, fi],
        is_kw(ts, x, "try"@),
        kd(a, b) == NodeKind::BlockStatement,
        node_done(a, ts, b, cx, x + 1, mb),
        kd(a, ca) == NodeKind::Catch || kd(a, ca) == NodeKind::Absent,
        kd(a, fi) == NodeKind::Finally || kd(a, fi) == NodeKind::Absent,
        kd(a, ca) == NodeKind::Catch || kd(a, fi) == NodeKind::Finally,
        d(a, ts, ca, cx, mb, q),
        ed(a, ts, ca, mb) == q,
        d(a, ts, fi, cx, q, j),
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == b);
    assert(a.nodes[m].children[1] == ca);
    assert(a.nodes[m].children[2] == fi);
    assert(dc(a, ts, m, b, cx, x + 1, mb));
    assert(dc(a, ts, m, ca, cx, mb, q));
    assert(dc(a, ts, m, fi, cx, q, j));
    assert(d_stmt(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.15 `try Block Catch`, `try Block Finally`, `try Block Catch Finally`.
#[verifier::spinoff_prover]
fn check_try(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_words2();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::TryStatement) || nd.children.len() != 3 {
        return None;
    }
    let b = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let ca = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let fi = match kid_of(nodes, m, 2) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let (lo_b, mb, _) = match done_at(done, b) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    if !matches!(kind_at(nodes, b), NodeKind::BlockStatement) || lo_b != x.saturating_add(1) {
        return None;
    }
    if !word_at(src, nodes, toks, gaps, x, &[0x74, 0x72, 0x79], Ghost(GW { g, w: "try"@ })) {
        return None;
    }
    let kc = kind_at(nodes, ca);
    let kf = kind_at(nodes, fi);
    let has_catch = matches!(kc, NodeKind::Catch);
    let has_finally = matches!(kf, NodeKind::Finally);
    if !(has_catch || has_finally) {
        return None;
    }
    let q: usize = if has_catch {
        let (lo_c, hi_c, _) = match done_at(done, ca) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if lo_c != mb {
            return None;
        }
        hi_c
    } else {
        if !matches!(kc, NodeKind::Absent) || !check_absent(src, nodes, toks, gaps, ca, mb, Ghost(g)) {
            return None;
        }
        mb
    };
    let j: usize = if has_finally {
        let (lo_f, hi_f, _) = match done_at(done, fi) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if lo_f != q {
            return None;
        }
        hi_f
    } else {
        if !matches!(kf, NodeKind::Absent) || !check_absent(src, nodes, toks, gaps, fi, q, Ghost(g)) {
            return None;
        }
        q
    };
    if !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![b as int, ca as int, fi as int]) by {
            assert(a.nodes[m as int].children.len() == 3);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, b as int, g.cx, 0);
        if has_catch {
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, ca as int, g.cx, 1);
        }
        if has_finally {
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, fi as int, g.cx, 2);
        }
        lemma_try_done(a, g.ts, g.cx, m as int, b as int, ca as int, fi as int, x as int, mb as int, q as int, j as int);
    }
    Some((x, j, -100))
}

/// §14.15 `Catch : catch ( CatchParameter ) Block | catch Block`.
#[verifier::spinoff_prover]
proof fn lemma_catch_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    p: int,
    blk: int,
    x: int,
    has_param: bool,
    mp: int,
    j: int,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= p < m,
        0 <= blk < m,
        a.nodes[m].kind == NodeKind::Catch,
        a.nodes[m].children =~= seq![p, blk],
        is_kw(ts, x, "catch"@),
        kd(a, blk) == NodeKind::BlockStatement,
        if has_param {
            is_binding_target_kind(kd(a, p)) && is_p(ts, x + 1, "("@) && node_done(
                a,
                ts,
                p,
                cx,
                x + 2,
                mp,
            ) && is_p(ts, mp, ")"@) && node_done(a, ts, blk, cx, mp + 1, j)
        } else {
            kd(a, p) == NodeKind::Absent && d(a, ts, p, cx, x + 1, x + 1) && node_done(
                a,
                ts,
                blk,
                cx,
                x + 1,
                j,
            )
        },
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == p);
    assert(a.nodes[m].children[1] == blk);
    if has_param {
        assert(dc(a, ts, m, p, cx, x + 2, mp));
        assert(dc(a, ts, m, blk, cx, mp + 1, j));
    } else {
        assert(dc(a, ts, m, p, cx, x + 1, x + 1));
        assert(dc(a, ts, m, blk, cx, x + 1, j));
    }
    assert(d_stmt(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.15 `Catch : catch ( CatchParameter ) Block | catch Block`.
#[verifier::spinoff_prover]
fn check_catch(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_words2();
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::Catch) || nd.children.len() != 2 {
        return None;
    }
    let p = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let blk = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let (lo_k, j, _) = match done_at(done, blk) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    if !matches!(kind_at(nodes, blk), NodeKind::BlockStatement) {
        return None;
    }
    if !word_at(src, nodes, toks, gaps, x, &[0x63, 0x61, 0x74, 0x63, 0x68], Ghost(GW { g, w: "catch"@ })) {
        return None;
    }
    let x1 = x.saturating_add(1);
    let kp = kind_at(nodes, p);
    let has_param = matches!(kp, NodeKind::BindingIdentifier | NodeKind::ObjectBindingPattern | NodeKind::ArrayBindingPattern);
    let mp: usize = if has_param {
        let (lo_p, hi_p, _) = match done_at(done, p) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if lo_p != x.saturating_add(2) || lo_k != hi_p.saturating_add(1) || !punct_at(src, nodes, toks, gaps, x1, 0x28, Ghost(GW { g, w: "("@ }))
            || !punct_at(src, nodes, toks, gaps, hi_p, 0x29, Ghost(GW { g, w: ")"@ })) {
            return None;
        }
        hi_p
    } else {
        if !matches!(kp, NodeKind::Absent) || !check_absent(src, nodes, toks, gaps, p, x1, Ghost(g)) || lo_k != x1 {
            return None;
        }
        0
    };
    let _ = mp;
    if !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x1 as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![p as int, blk as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, blk as int, g.cx, 1);
        if has_param {
            assert(x.saturating_add(2) as int == x as int + 2);
            assert(mp.saturating_add(1) as int == mp as int + 1);
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, p as int, g.cx, 0);
        }
        lemma_catch_done(a, g.ts, g.cx, m as int, p as int, blk as int, x as int, has_param, mp as int, j as int);
    }
    Some((x, j, -100))
}

/// §14.15 `Finally : finally Block`.
#[verifier::spinoff_prover]
proof fn lemma_finally_done(a: AstV, ts: Stream, cx: Ctx, m: int, blk: int, x: int, j: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= blk < m,
        a.nodes[m].kind == NodeKind::Finally,
        a.nodes[m].children =~= seq![blk],
        is_kw(ts, x, "finally"@),
        kd(a, blk) == NodeKind::BlockStatement,
        node_done(a, ts, blk, cx, x + 1, j),
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == blk);
    assert(dc(a, ts, m, blk, cx, x + 1, j));
    assert(d_stmt(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.15 `Finally : finally Block`.
#[verifier::spinoff_prover]
fn check_finally(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_words2();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::Finally) || nd.children.len() != 1 {
        return None;
    }
    let blk = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let (lo_k, j, _) = match done_at(done, blk) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    if !matches!(kind_at(nodes, blk), NodeKind::BlockStatement) || lo_k != x.saturating_add(1) {
        return None;
    }
    if !word_at(src, nodes, toks, gaps, x, &[0x66, 0x69, 0x6E, 0x61, 0x6C, 0x6C, 0x79], Ghost(GW { g, w: "finally"@ }))
        || !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![blk as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, blk as int, g.cx, 0);
        lemma_finally_done(a, g.ts, g.cx, m as int, blk as int, x as int, j as int);
    }
    Some((x, j, -100))
}

/// What [`check_dl_from`] checks: the children `from..` of node `m` are statement list
/// items, or (`clauses`) the clauses of a `switch`, over the tokens `start..end`.
pub struct DlSpec {
    /// The node whose children are listed.
    pub m: usize,
    /// The first token of the list (where it ends, if empty).
    pub start: usize,
    /// One past the last token of the list.
    pub end: usize,
    /// The index of the first child of the list.
    pub from: usize,
    /// The children are `CaseClause`s and `DefaultClause`s.
    pub clauses: bool,
}

/// A `CaseClause` or `DefaultClause` kind, executable.
fn clause_kind_exec(k: NodeKind) -> (r: bool)
    ensures
        r ==> (k == NodeKind::CaseClause || k == NodeKind::DefaultClause),
{
    matches!(k, NodeKind::CaseClause | NodeKind::DefaultClause)
}

/// The children `from..` of `rng.m` derive consecutive token ranges from `start` to
/// `end` (`spec::dl`): statement list items, or (`clauses`) the clauses of a `switch`.
fn check_dl_from(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    sp: &DlSpec,
    Ghost(g): Ghost<GCx>,
) -> (r: bool)
    requires
        sp.m < nodes.len(),
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, sp.m as int),
        cx_ok(arena_of(nodes@), done.cxs@, sp.m as int, g.cx),
        sp.end <= toks.len(),
    ensures
        r ==> (dl(
            arena_of(nodes@),
            g.ts,
            sp.m as int,
            arena_of(nodes@).nodes[sp.m as int].children,
            sp.from as int,
            g.cx,
            sp.start as int,
            sp.end as int,
        ) && sp.start <= sp.end && sp.from <= arena_of(nodes@).nodes[sp.m as int].children.len()
            && (forall|q: int|
            sp.from <= q < arena_of(nodes@).nodes[sp.m as int].children.len() ==> (if sp.clauses {
                kd(arena_of(nodes@), #[trigger] arena_of(nodes@).nodes[sp.m as int].children[q])
                    == NodeKind::CaseClause || kd(arena_of(nodes@), arena_of(nodes@).nodes[sp.m as int].children[q])
                    == NodeKind::DefaultClause
            } else {
                is_item_kind(kd(arena_of(nodes@), #[trigger] arena_of(nodes@).nodes[sp.m as int].children[q]))
            }))),
{
    let _ = (src.len(), gaps.len(), toks.len());
    let m = sp.m;
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return false;
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
    if sp.from > len {
        return false;
    }
    let mut k = len;
    let mut pos = sp.end;
    while k > sp.from
        invariant
            m < nodes.len(),
            nodes@.len() == nodes.len(),
            nd == &nodes@[m as int],
            a == arena_of(nodes@),
            len == nd.children.len(),
            len == a.nodes[m as int].children.len(),
            sp.from <= k <= len,
            pos <= toks.len(),
            pos <= sp.end,
            tn(g.ts) == toks.len(),
            ast_wf(a),
            env_ok(src@, nodes@, toks@, gaps@, g.ts),
            inv(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
            cx_ok(a, done.cxs@, m as int, g.cx),
            dl(
                a,
                g.ts,
                m as int,
                a.nodes[m as int].children,
                k as int,
                g.cx,
                pos as int,
                sp.end as int,
            ),
            forall|q: int|
                k <= q < len ==> (if sp.clauses {
                    kd(a, #[trigger] a.nodes[m as int].children[q]) == NodeKind::CaseClause || kd(
                        a,
                        a.nodes[m as int].children[q],
                    ) == NodeKind::DefaultClause
                } else {
                    is_item_kind(kd(a, #[trigger] a.nodes[m as int].children[q]))
                }),
        decreases k,
    {
        let c = match nd.children.as_slice().get(k.saturating_sub(1)) {
            Some(x) => *x as usize,
            None => {
                return false;
            },
        };
        proof {
            assert(k >= 1);
            assert(k.saturating_sub(1) as int == k as int - 1);
            assert(a.nodes[m as int].children[k as int - 1] == c as int);
            lemma_child_before(a, m as int, k as int - 1);
        }
        if c >= m {
            return false;
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
            Some(x) => if sp.clauses {
                clause_kind_exec(x.kind)
            } else {
                item_kind_exec(x.kind)
            },
            None => false,
        };
        if hi_c != pos || !item {
            return false;
        }
        proof {
            assert(a.nodes[c as int] == nodes@[c as int]@);
            assert(kd(a, c as int) == nodes@[c as int].kind);
            assert(kd(a, c as int) != NodeKind::Absent);
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, k as int - 1);
            let ks = a.nodes[m as int].children;
            assert(node_done(a, g.ts, c as int, g.cx, lo_c as int, hi_c as int));
            lemma_dl_cons(a, g.ts, m as int, ks, k as int - 1, g.cx, lo_c as int, hi_c as int, sp.end as int);
        }
        pos = lo_c;
        k = k.saturating_sub(1);
    }
    if pos != sp.start {
        return false;
    }
    true
}

/// A `switch` has at most one `DefaultClause` (§14.12).
fn check_one_default(nodes: &[Node], m: usize) -> (r: bool)
    requires
        m < nodes.len(),
        ast_wf(arena_of(nodes@)),
    ensures
        r ==> at_most_one_default(
            arena_of(nodes@),
            arena_of(nodes@).nodes[m as int].children,
        ),
{
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    let len = nd.children.len();
    let ghost a = arena_of(nodes@);
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children.len() == len);
    }
    if len <= 1 {
        return true;
    }
    let mut k: usize = 1;
    let mut seen = false;
    while k < len
        invariant
            m < nodes.len(),
            nodes@.len() == nodes.len(),
            a == arena_of(nodes@),
            ast_wf(a),
            len == a.nodes[m as int].children.len(),
            1 <= k <= len,
            forall|x: int, y: int|
                1 <= x < y < k ==> !(kd(a, #[trigger] a.nodes[m as int].children[x])
                    == NodeKind::DefaultClause && kd(a, #[trigger] a.nodes[m as int].children[y])
                    == NodeKind::DefaultClause),
            !seen ==> forall|x: int|
                1 <= x < k ==> kd(a, #[trigger] a.nodes[m as int].children[x])
                    != NodeKind::DefaultClause,
        decreases len - k,
    {
        let c = match kid_of(nodes, m, k) {
            Some(c) => c,
            None => {
                return false;
            },
        };
        let is_default = matches!(kind_at(nodes, c), NodeKind::DefaultClause);
        if is_default {
            if seen {
                proof {
                    // A default before: the loop invariant `seen` is only set after one.
                }
                return false;
            }
            seen = true;
        }
        k = k.saturating_add(1);
    }
    true
}

/// §14.12 `CaseClause : case Expression : StatementList?`.
#[verifier::spinoff_prover]
proof fn lemma_case_done(a: AstV, ts: Stream, cx: Ctx, m: int, e: int, x: int, me: int, j: int)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= e < m,
        a.nodes[m].kind == NodeKind::CaseClause,
        a.nodes[m].children.len() >= 1,
        a.nodes[m].children[0] == e,
        is_kw(ts, x, "case"@),
        lvl(a, e) >= -1,
        forall|k: int|
            1 <= k < a.nodes[m].children.len() ==> is_item_kind(
                kd(a, #[trigger] a.nodes[m].children[k]),
            ),
        node_done(a, ts, e, cx, x + 1, me),
        is_p(ts, me, ":"@),
        dl(a, ts, m, a.nodes[m].children, 1, cx, me + 1, j),
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(dc(a, ts, m, e, cx_in(cx, true), x + 1, me));
    assert(d_stmt(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.12 `CaseClause : case Expression : StatementList?`.
#[verifier::spinoff_prover]
fn check_case(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_words2();
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::CaseClause) || nd.children.is_empty() {
        return None;
    }
    let len = nd.children.len();
    let e = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let (lo_e, me, lv_e) = match done_at(done, e) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if lv_e < -1 || lo_e != x.saturating_add(1) {
        return None;
    }
    if !word_at(src, nodes, toks, gaps, x, &[0x63, 0x61, 0x73, 0x65], Ghost(GW { g, w: "case"@ }))
        || !punct_at(src, nodes, toks, gaps, me, 0x3A, Ghost(GW { g, w: ":"@ })) {
        return None;
    }
    let start = me.saturating_add(1);
    let j: usize = if len == 1 {
        start
    } else {
        let last = match kid_of(nodes, m, len.saturating_sub(1)) {
            Some(c) => c,
            None => {
                return None;
            },
        };
        match done_at(done, last) {
            Some((_, h, _)) => h,
            None => {
                return None;
            },
        }
    };
    if j > toks.len() {
        return None;
    }
    let rng = DlSpec { m, start, end: j, from: 1, clauses: false };
    if !check_dl_from(src, nodes, toks, gaps, done, &rng, Ghost(g)) {
        return None;
    }
    if !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(a.nodes[m as int].children.len() == len);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(me.saturating_add(1) as int == me as int + 1);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, e as int, g.cx, 0);
        assert(lvl(a, e as int) >= -1);
        lemma_case_done(a, g.ts, g.cx, m as int, e as int, x as int, me as int, j as int);
    }
    Some((x, j, -100))
}

/// §14.12 `DefaultClause : default : StatementList?`.
#[verifier::spinoff_prover]
proof fn lemma_default_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int, j: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        a.nodes[m].kind == NodeKind::DefaultClause,
        is_kw(ts, x, "default"@),
        is_p(ts, x + 1, ":"@),
        all_items(a, a.nodes[m].children),
        dl(a, ts, m, a.nodes[m].children, 0, cx, x + 2, j),
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(d_stmt(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.12 `DefaultClause : default : StatementList?`.
#[verifier::spinoff_prover]
fn check_default(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_words2();
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::DefaultClause) {
        return None;
    }
    let len = nd.children.len();
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !word_at(src, nodes, toks, gaps, x, &[0x64, 0x65, 0x66, 0x61, 0x75, 0x6C, 0x74], Ghost(GW { g, w: "default"@ }))
        || !punct_at(src, nodes, toks, gaps, x.saturating_add(1), 0x3A, Ghost(GW { g, w: ":"@ })) {
        return None;
    }
    let start = x.saturating_add(2);
    let j: usize = if len == 0 {
        start
    } else {
        let last = match kid_of(nodes, m, len.saturating_sub(1)) {
            Some(c) => c,
            None => {
                return None;
            },
        };
        match done_at(done, last) {
            Some((_, h, _)) => h,
            None => {
                return None;
            },
        }
    };
    if j > toks.len() {
        return None;
    }
    let rng = DlSpec { m, start, end: j, from: 0, clauses: false };
    if !check_dl_from(src, nodes, toks, gaps, done, &rng, Ghost(g)) {
        return None;
    }
    if !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(x.saturating_add(2) as int == x as int + 2);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(all_items(a, a.nodes[m as int].children));
        lemma_default_done(a, g.ts, g.cx, m as int, x as int, j as int);
    }
    Some((x, j, -100))
}

/// §14.12 `switch ( Expression ) CaseBlock`.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
proof fn lemma_switch_done(a: AstV, ts: Stream, cx: Ctx, m: int, e: int, x: int, me: int, j: int)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= e < m,
        a.nodes[m].kind == NodeKind::SwitchStatement,
        a.nodes[m].children.len() >= 1,
        a.nodes[m].children[0] == e,
        is_kw(ts, x, "switch"@),
        is_p(ts, x + 1, "("@),
        lvl(a, e) >= -1,
        all_kind2(a, a.nodes[m].children, 1, NodeKind::CaseClause, NodeKind::DefaultClause),
        at_most_one_default(a, a.nodes[m].children),
        node_done(a, ts, e, cx, x + 2, me),
        is_p(ts, me, ")"@),
        is_p(ts, me + 1, "{"@),
        is_p(ts, j - 1, "}"@),
        me + 2 <= j - 1,
        dl(a, ts, m, a.nodes[m].children, 1, cx, me + 2, j - 1),
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(dc(a, ts, m, e, cx_in(cx, true), x + 2, me));
    assert(d_stmt(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.12 `switch ( Expression ) CaseBlock`.
#[verifier::spinoff_prover]
fn check_switch(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_words2();
        lemma_punct_text();
        lemma_brace_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::SwitchStatement) || nd.children.is_empty() {
        return None;
    }
    let len = nd.children.len();
    let e = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let (lo_e, me, lv_e) = match done_at(done, e) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if lv_e < -1 || lo_e != x.saturating_add(2) {
        return None;
    }
    if !word_at(src, nodes, toks, gaps, x, &[0x73, 0x77, 0x69, 0x74, 0x63, 0x68], Ghost(GW { g, w: "switch"@ }))
        || !punct_at(src, nodes, toks, gaps, x.saturating_add(1), 0x28, Ghost(GW { g, w: "("@ }))
        || !punct_at(src, nodes, toks, gaps, me, 0x29, Ghost(GW { g, w: ")"@ }))
        || !punct_at(src, nodes, toks, gaps, me.saturating_add(1), 0x7B, Ghost(GW { g, w: "{"@ })) {
        return None;
    }
    let start = me.saturating_add(2);
    let close: usize = if len == 1 {
        start
    } else {
        let last = match kid_of(nodes, m, len.saturating_sub(1)) {
            Some(c) => c,
            None => {
                return None;
            },
        };
        match done_at(done, last) {
            Some((_, h, _)) => h,
            None => {
                return None;
            },
        }
    };
    if close > toks.len() {
        return None;
    }
    let rng = DlSpec { m, start, end: close, from: 1, clauses: true };
    if !check_dl_from(src, nodes, toks, gaps, done, &rng, Ghost(g))
        || !check_one_default(nodes, m) {
        return None;
    }
    if !punct_at(src, nodes, toks, gaps, close, 0x7D, Ghost(GW { g, w: "}"@ })) {
        return None;
    }
    let j = close.saturating_add(1);
    if !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(a.nodes[m as int].children.len() == len);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(x.saturating_add(2) as int == x as int + 2);
        assert(me.saturating_add(1) as int == me as int + 1);
        assert(me.saturating_add(2) as int == me as int + 2);
        assert(close.saturating_add(1) as int == close as int + 1);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, e as int, g.cx, 0);
        assert(lvl(a, e as int) >= -1);
        assert(all_kind2(a, a.nodes[m as int].children, 1, NodeKind::CaseClause, NodeKind::DefaultClause));
        lemma_switch_done(a, g.ts, g.cx, m as int, e as int, x as int, me as int, j as int);
    }
    Some((x, j, -100))
}

// ---------------------------------------------------------------------
// Functions (§15.1 and §15.2): `return`, formal parameters, and the function
// declarations and expressions, which give their parts the contexts of
// `cx_fn` (a node is checked in the context `Done.cxs` assigns it).
// ---------------------------------------------------------------------

/// The ghost context of an assigned one, for a function's part.
pub open spec fn fcx(y: bool, a: bool, r: bool) -> Ctx {
    cx_fn(y, a, r)
}

/// Node `j < m`, the child `k` of node `m`, is done in the context `cxs` assigns it.
proof fn lemma_inv_get_at(
    a: AstV,
    ts: Stream,
    cxs: Seq<Cx5>,
    lo: Seq<usize>,
    hi: Seq<usize>,
    lv: Seq<i32>,
    m: int,
    j: int,
)
    requires
        inv(a, ts, cxs, lo, hi, lv, m),
        0 <= j < m,
    ensures
        kd(a, j) != NodeKind::Absent ==> node_done(a, ts, j, cx_of(cxs[j]), lo[j] as int, hi[j] as int),
        lvl(a, j) != -100 ==> node_done(a, ts, j, cx_of(cxs[j]), lo[j] as int, hi[j] as int),
        lv[j] as int == lvl(a, j),
{
    reveal(inv);
    assert(lv[j] as int == lvl(a, j));
    if kd(a, j) == NodeKind::Absent {
        assert(lvl(a, j) == -100);
    }
}

/// No child of node `m` but the last is a `...rest`.
fn check_rest_last(nodes: &[Node], m: usize) -> (r: bool)
    requires
        m < nodes.len(),
        ast_wf(arena_of(nodes@)),
    ensures
        r ==> rest_only_last(arena_of(nodes@), arena_of(nodes@).nodes[m as int].children),
{
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    let len = nd.children.len();
    let ghost a = arena_of(nodes@);
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children.len() == len);
    }
    let mut k: usize = len.saturating_sub(1);
    proof {
        let ks = a.nodes[m as int].children;
        assert(rest_free_from(a, ks, k as int));
    }
    while k > 0
        invariant
            m < nodes.len(),
            nodes@.len() == nodes.len(),
            a == arena_of(nodes@),
            ast_wf(a),
            len == a.nodes[m as int].children.len(),
            k < len || k == 0,
            rest_free_from(a, a.nodes[m as int].children, k as int),
        decreases k,
    {
        let c = match kid_of(nodes, m, k.saturating_sub(1)) {
            Some(c) => c,
            None => {
                return false;
            },
        };
        let kc = kind_at(nodes, c);
        if matches!(
            kc,
            NodeKind::FunctionRestParameter | NodeKind::BindingRestElement | NodeKind::BindingRestProperty
                | NodeKind::AssignmentRestElement | NodeKind::AssignmentRestProperty
        ) {
            return false;
        }
        proof {
            assert(k.saturating_sub(1) as int == k as int - 1);
            let ks = a.nodes[m as int].children;
            assert(ks[k as int - 1] == c as int);
            assert(!is_rest_kind(kd(a, ks[k as int - 1])));
            assert(rest_free_from(a, ks, k as int - 1));
        }
        k = k.saturating_sub(1);
    }
    true
}

/// §15.1 `FormalParameters : ( FormalParameterList? )`.
#[verifier::spinoff_prover]
proof fn lemma_params_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int, e: int)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= x,
        x + 1 <= e,
        e < tn(ts),
        a.nodes[m].kind == NodeKind::FormalParameters,
        dsep(a, ts, m, a.nodes[m].children, 0, cx, x + 1, e, true),
        forall|k: int|
            0 <= k < a.nodes[m].children.len() ==> list_item_ok(
                a,
                #[trigger] a.nodes[m].children[k],
                4,
            ),
        rest_only_last(a, a.nodes[m].children),
        is_p(ts, x, "("@),
        is_p(ts, e, ")"@),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[e].end,
    ensures
        node_done(a, ts, m, cx, x, e + 1),
        lvl(a, m) == -100,
{
    assert(all_kind2(a, a.nodes[m].children, 0, NodeKind::BindingElement, NodeKind::FunctionRestParameter)) by {
        assert forall|k: int| 0 <= k < a.nodes[m].children.len() implies kd(
            a,
            #[trigger] a.nodes[m].children[k],
        ) == NodeKind::BindingElement || kd(a, a.nodes[m].children[k])
            == NodeKind::FunctionRestParameter by {
            assert(list_item_ok(a, a.nodes[m].children[k], 4));
        }
    }
    assert(span_ok(a, ts, m, x, e + 1));
    assert(d_func(a, ts, m, cx, x, e + 1));
    lemma_ed_of(a, ts, m, x, e + 1);
}

/// §15.1 `FormalParameters : ( FormalParameterList? )`.
#[verifier::spinoff_prover]
fn check_params(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::FormalParameters) {
        return None;
    }
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !punct_at(src, nodes, toks, gaps, x, 0x28, Ghost(GW { g, w: "("@ })) {
        return None;
    }
    let ls = ListSpec { m, start: x.saturating_add(1), mode: 4, trail: true };
    let e = match check_list(src, nodes, toks, gaps, done, &ls, Ghost(g)) {
        Some(e) => e,
        None => {
            return None;
        },
    };
    if !punct_at(src, nodes, toks, gaps, e, 0x29, Ghost(GW { g, w: ")"@ }))
        || !end_ok(src, nodes, toks, gaps, nd.end, e.saturating_add(1), Ghost(g))
        || !check_rest_last(nodes, m) {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(e.saturating_add(1) as int == e as int + 1);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_params_done(a, g.ts, g.cx, m as int, x as int, e as int);
    }
    Some((x, e.saturating_add(1), -100))
}

/// §14.10 `return Expression? ;`.
#[verifier::spinoff_prover]
proof fn lemma_return_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    c: int,
    x: int,
    has_expr: bool,
    me: int,
    j: int,
)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        cx.return_,
        0 <= m < a.nodes.len(),
        0 <= c < m,
        a.nodes[m].kind == NodeKind::ReturnStatement,
        a.nodes[m].children =~= seq![c],
        is_kw(ts, x, "return"@),
        if has_expr {
            !nl(ts, x + 1) && lvl(a, c) >= -1 && node_done(a, ts, c, cx, x + 1, me) && semi(
                ts,
                me,
                j,
                false,
            )
        } else {
            kd(a, c) == NodeKind::Absent && d(a, ts, c, cx, x + 1, x + 1) && semi(
                ts,
                x + 1,
                j,
                false,
            )
        },
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == c);
    if has_expr {
        assert(kd(a, c) != NodeKind::Absent);
        assert(dc(a, ts, m, c, cx_in(cx, true), x + 1, me));
    } else {
        assert(dc(a, ts, m, c, cx, x + 1, x + 1));
    }
    assert(d_stmt(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.10 `return ;` and `return [no LineTerminator here] Expression ;`.
#[verifier::spinoff_prover]
fn check_return(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_words3();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let cxm = match done.cxs.get(m) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::ReturnStatement) || nd.children.len() != 1 || !cxm.r {
        return None;
    }
    let c = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !word_at(src, nodes, toks, gaps, x, &[0x72, 0x65, 0x74, 0x75, 0x72, 0x6E], Ghost(GW { g, w: "return"@ })) {
        return None;
    }
    let x1 = x.saturating_add(1);
    let has_expr = !matches!(kind_at(nodes, c), NodeKind::Absent);
    let (me, j): (usize, usize) = if has_expr {
        let (lo_c, hi_c, lv_c) = match done_at(done, c) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if lv_c < -1 || lo_c != x1 || !no_nl_at(src, nodes, toks, gaps, x1, Ghost(g)) {
            return None;
        }
        let j = match find_semi(src, nodes, toks, gaps, hi_c, nd.end, Ghost(g)) {
            Some(j) => j,
            None => {
                return None;
            },
        };
        (hi_c, j)
    } else {
        if !check_absent(src, nodes, toks, gaps, c, x1, Ghost(g)) {
            return None;
        }
        let j = match find_semi(src, nodes, toks, gaps, x1, nd.end, Ghost(g)) {
            Some(j) => j,
            None => {
                return None;
            },
        };
        (0, j)
    };
    let _ = me;
    if j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x1 as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(cxm == &done.cxs@[m as int]);
        assert(g.cx.return_);
        if has_expr {
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 0);
            assert(lvl(a, c as int) >= -1);
        }
        lemma_return_done(a, g.ts, g.cx, m as int, c as int, x as int, has_expr, me as int, j as int);
    }
    Some((x, j, -100))
}

/// The words `return` and `function`, as code points.
proof fn lemma_words3()
    ensures
        cps("return"@) =~= seq![0x72u32, 0x65, 0x74, 0x75, 0x72, 0x6E],
        cps("function"@) =~= seq![0x66u32, 0x75, 0x6E, 0x63, 0x74, 0x69, 0x6F, 0x6E],
        cps("async"@) =~= seq![0x61u32, 0x73, 0x79, 0x6E, 0x63],
        cps("*"@) =~= seq![0x2Au32],
{
    reveal_strlit("return");
    reveal_strlit("function");
    reveal_strlit("async");
    reveal_strlit("*");
    assert("return"@ =~= seq!['r', 'e', 't', 'u', 'r', 'n']);
    assert("function"@ =~= seq!['f', 'u', 'n', 'c', 't', 'i', 'o', 'n']);
    assert("async"@ =~= seq!['a', 's', 'y', 'n', 'c']);
    assert("*"@ =~= seq!['*']);
}

/// The kind of node of the function with the given flags.
pub open spec fn fn_kind(is_async: bool, is_gen: bool, is_expr: bool) -> NodeKind {
    if is_async {
        if is_gen {
            if is_expr {
                NodeKind::AsyncGeneratorExpression
            } else {
                NodeKind::AsyncGeneratorDeclaration
            }
        } else if is_expr {
            NodeKind::AsyncFunctionExpression
        } else {
            NodeKind::AsyncFunctionDeclaration
        }
    } else if is_gen {
        if is_expr {
            NodeKind::GeneratorExpression
        } else {
            NodeKind::GeneratorDeclaration
        }
    } else if is_expr {
        NodeKind::FunctionExpression
    } else {
        NodeKind::FunctionDeclaration
    }
}

/// The flags (`async`, generator, expression) of a function kind.
fn fn_flags(k: NodeKind) -> (r: Option<(bool, bool, bool)>)
    ensures
        match r {
            Some((a, g, e)) => k == fn_kind(a, g, e),
            None => true,
        },
{
    match k {
        NodeKind::FunctionDeclaration => Some((false, false, false)),
        NodeKind::FunctionExpression => Some((false, false, true)),
        NodeKind::GeneratorDeclaration => Some((false, true, false)),
        NodeKind::GeneratorExpression => Some((false, true, true)),
        NodeKind::AsyncFunctionDeclaration => Some((true, false, false)),
        NodeKind::AsyncFunctionExpression => Some((true, false, true)),
        NodeKind::AsyncGeneratorDeclaration => Some((true, true, false)),
        NodeKind::AsyncGeneratorExpression => Some((true, true, true)),
        _ => None,
    }
}

/// The three children of node `m` are checked in `c0`, `c1`, `c2`.
pub open spec fn cx_kids3(a: AstV, cxs: Seq<Cx5>, m: int, c0: Ctx, c1: Ctx, c2: Ctx) -> bool {
    0 <= m < a.nodes.len() && a.nodes[m].children.len() == 3 && 0 <= a.nodes[m].children[0]
        < cxs.len() && 0 <= a.nodes[m].children[1] < cxs.len() && 0 <= a.nodes[m].children[2]
        < cxs.len() && cx_of(cxs[a.nodes[m].children[0]]) == c0 && cx_of(
        cxs[a.nodes[m].children[1]],
    ) == c1 && cx_of(cxs[a.nodes[m].children[2]]) == c2
}

/// The contexts of the parts of a function (§15.2): the name in `cx` of a
/// declaration, in the function's own of an expression; the parameters and the
/// body in `cx_fn`.
pub open spec fn fn_cx(cx: Ctx, is_async: bool, is_gen: bool, is_expr: bool) -> (Ctx, Ctx, Ctx) {
    (
        if is_expr {
            cx_fn(is_gen, is_async, false)
        } else {
            cx
        },
        cx_fn(is_gen, is_async, false),
        cx_fn(is_gen, is_async, true),
    )
}

/// §15.2 `function BindingIdentifier? ( FormalParameters ) { FunctionBody }` and the
/// generator, `async` and `async` generator forms (`d_function`).
#[verifier::spinoff_prover]
proof fn lemma_function_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    n0: int,
    p: int,
    b: int,
    is_async: bool,
    is_gen: bool,
    is_expr: bool,
    x: int,
    nm: int,
    mn: int,
    q: int,
    j: int,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= n0 < m,
        0 <= p < m,
        0 <= b < m,
        a.nodes[m].kind == fn_kind(is_async, is_gen, is_expr),
        a.nodes[m].children =~= seq![n0, p, b],
        !is_async || (is_kw(ts, x, "async"@) && !nl(ts, x + 1)),
        is_kw(ts, if is_async {
            x + 1
        } else {
            x
        }, "function"@),
        nm == (if is_async {
            x + 2
        } else {
            x + 1
        }) + (if is_gen {
            1int
        } else {
            0int
        }),
        !is_gen || is_p(ts, nm - 1, "*"@),
        if kd(a, n0) == NodeKind::Absent {
            is_expr && d(a, ts, n0, fn_cx(cx, is_async, is_gen, is_expr).0, nm, nm) && mn == nm && ed(a, ts, n0, nm) == nm
        } else {
            kd(a, n0) == NodeKind::BindingIdentifier && node_done(
                a,
                ts,
                n0,
                fn_cx(cx, is_async, is_gen, is_expr).0,
                nm,
                mn,
            )
        },
        kd(a, p) == NodeKind::FormalParameters,
        node_done(a, ts, p, fn_cx(cx, is_async, is_gen, is_expr).1, mn, q),
        kd(a, b) == NodeKind::FunctionBody,
        node_done(a, ts, b, fn_cx(cx, is_async, is_gen, is_expr).2, q, j),
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == (if is_expr {
            17int
        } else {
            -100int
        }),
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == n0);
    assert(a.nodes[m].children[1] == p);
    assert(a.nodes[m].children[2] == b);
    let cxn = fn_cx(cx, is_async, is_gen, is_expr).0;
    assert(cxn == (if is_expr {
        cx_fn(is_gen, is_async, false)
    } else {
        cx
    }));
    assert(dc(a, ts, m, n0, cxn, nm, mn));
    assert(dc(a, ts, m, p, cx_fn(is_gen, is_async, false), mn, q));
    assert(dc(a, ts, m, b, cx_fn(is_gen, is_async, true), q, j));
    assert(ed(a, ts, n0, nm) == mn);
    assert(ed(a, ts, p, mn) == q);
    assert(d_function(a, ts, m, cx, x, j, is_async, is_gen, is_expr));
    assert(d_func(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// What `check_function` reads: the node and the flags of its kind.
pub struct FuncShape {
    /// The node.
    pub m: usize,
    /// `async`.
    pub is_async: bool,
    /// A generator.
    pub is_gen: bool,
    /// An expression (not a declaration).
    pub is_expr: bool,
}

/// §15.2 and §15.5, §15.8 and §15.6: a function, generator, `async` function or
/// `async` generator, declaration or expression.
#[verifier::spinoff_prover]
fn check_function(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    fs: &FuncShape,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        fs.m < nodes.len(),
        nodes@[fs.m as int].kind == fn_kind(fs.is_async, fs.is_gen, fs.is_expr),
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, fs.m as int),
        0 <= fs.m < done.cxs@.len(),
        cx_of(done.cxs@[fs.m as int]) == g.cx,
        cx_kids3(
            arena_of(nodes@),
            done.cxs@,
            fs.m as int,
            fn_cx(g.cx, fs.is_async, fs.is_gen, fs.is_expr).0,
            fn_cx(g.cx, fs.is_async, fs.is_gen, fs.is_expr).1,
            fn_cx(g.cx, fs.is_async, fs.is_gen, fs.is_expr).2,
        ),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(
                arena_of(nodes@),
                g.ts,
                fs.m as int,
                g.cx,
                l0 as int,
                h0 as int,
            ) && l as int == lvl(arena_of(nodes@), fs.m as int),
            None => true,
        },
{
    let m = fs.m;
    proof {
        lemma_words3();
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if nd.children.len() != 3 {
        return None;
    }
    let n0 = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let p = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let b = match kid_of(nodes, m, 2) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let x1 = x.saturating_add(1);
    let s: usize = if fs.is_async { x1 } else { x };
    if fs.is_async
        && (!word_at(src, nodes, toks, gaps, x, &[0x61, 0x73, 0x79, 0x6E, 0x63], Ghost(GW { g, w: "async"@ }))
            || !no_nl_at(src, nodes, toks, gaps, x1, Ghost(g))) {
        return None;
    }
    if !word_at(src, nodes, toks, gaps, s, &[0x66, 0x75, 0x6E, 0x63, 0x74, 0x69, 0x6F, 0x6E], Ghost(GW { g, w: "function"@ })) {
        return None;
    }
    let nm: usize = if fs.is_gen { s.saturating_add(2) } else { s.saturating_add(1) };
    if fs.is_gen
        && !punct_at(src, nodes, toks, gaps, s.saturating_add(1), 0x2A, Ghost(GW { g, w: "*"@ })) {
        return None;
    }
    let ghost cxn = fn_cx(g.cx, fs.is_async, fs.is_gen, fs.is_expr).0;
    let ghost cxp = fn_cx(g.cx, fs.is_async, fs.is_gen, fs.is_expr).1;
    let ghost cxb = fn_cx(g.cx, fs.is_async, fs.is_gen, fs.is_expr).2;
    let kn = kind_at(nodes, n0);
    let mn: usize = if matches!(kn, NodeKind::Absent) {
        if !fs.is_expr || !check_absent(src, nodes, toks, gaps, n0, nm, Ghost(GCx { ts: g.ts, cx: cxn })) {
            return None;
        }
        nm
    } else {
        if !matches!(kn, NodeKind::BindingIdentifier) {
            return None;
        }
        let (lo_n, hi_n, _) = match done_at(done, n0) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if lo_n != nm {
            return None;
        }
        hi_n
    };
    let (lo_p, q, _) = match done_at(done, p) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let (lo_b, j, _) = match done_at(done, b) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    if !matches!(kind_at(nodes, p), NodeKind::FormalParameters) || lo_p != mn
        || !matches!(kind_at(nodes, b), NodeKind::FunctionBody) || lo_b != q
        || !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x1 as int == x as int + 1);
        assert(s as int == (if fs.is_async { x as int + 1 } else { x as int }));
        assert(a.nodes[m as int].children =~= seq![n0 as int, p as int, b as int]) by {
            assert(a.nodes[m as int].children.len() == 3);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(s < toks.len());
        assert(nm as int == (if fs.is_async { x as int + 2 } else { x as int + 1 }) + (if fs.is_gen { 1int } else { 0int }));
        lemma_inv_get_at(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, p as int);
        lemma_inv_get_at(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, b as int);
        assert(cx_of(done.cxs@[p as int]) == cxp);
        assert(cx_of(done.cxs@[b as int]) == cxb);
        if !matches!(kn, NodeKind::Absent) {
            lemma_inv_get_at(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, n0 as int);
            assert(cx_of(done.cxs@[n0 as int]) == cxn);
        }
        lemma_function_done(
            a,
            g.ts,
            g.cx,
            m as int,
            n0 as int,
            p as int,
            b as int,
            fs.is_async,
            fs.is_gen,
            fs.is_expr,
            x as int,
            nm as int,
            mn as int,
            q as int,
            j as int,
        );
    }
    let l: i32 = if fs.is_expr { 17 } else { -100 };
    Some((x, j, l))
}

/// The three children of node `m` are checked in `c0`, `c1` and `c2`.
fn kids_cx3(nodes: &[Node], cxs: &[Cx5], m: usize, c0: &Cx5, c1: &Cx5, c2: &Cx5) -> (r: bool)
    requires
        m < nodes.len(),
        cxs.len() == nodes.len(),
        ast_wf(arena_of(nodes@)),
    ensures
        r ==> cx_kids3(arena_of(nodes@), cxs@, m as int, cx_of(*c0), cx_of(*c1), cx_of(*c2)),
{
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    if nd.children.len() != 3 {
        return false;
    }
    let a0 = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return false;
        },
    };
    let a1 = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return false;
        },
    };
    let a2 = match kid_of(nodes, m, 2) {
        Some(c) => c,
        None => {
            return false;
        },
    };
    let (k0, k1, k2) = match (cxs.get(a0), cxs.get(a1), cxs.get(a2)) {
        (Some(x), Some(y), Some(z)) => (x, y, z),
        _ => {
            return false;
        },
    };
    cx_eq(k0, c0) && cx_eq(k1, c1) && cx_eq(k2, c2)
}

/// The contexts of the parts of a function, as carried: `fn_cx`.
fn fn_cx5(cx: &Cx5, is_async: bool, is_gen: bool, is_expr: bool) -> (r: (Cx5, Cx5, Cx5))
    ensures
        cx_of(r.0) == fn_cx(cx_of(*cx), is_async, is_gen, is_expr).0,
        cx_of(r.1) == fn_cx(cx_of(*cx), is_async, is_gen, is_expr).1,
        cx_of(r.2) == fn_cx(cx_of(*cx), is_async, is_gen, is_expr).2,
{
    let own = Cx5 { y: is_gen, a: is_async, i: true, r: false, d: false };
    let n0 = if is_expr { own } else { *cx };
    let body = Cx5 { y: is_gen, a: is_async, i: true, r: true, d: false };
    (n0, own, body)
}

// ---------------------------------------------------------------------
// Arrow functions (§15.3, §15.9), `yield` (§15.5) and `await` (§15.8).
// ---------------------------------------------------------------------

/// The context of the parameters of an arrow function: the parent's, but an `async`
/// arrow's are `[+Await]` (§15.9).
pub open spec fn arrow_pcx(cx: Ctx, is_async: bool, ident: bool) -> Ctx {
    if !is_async {
        cx
    } else if ident {
        Ctx { yield_: cx.yield_, await_: true, in_: true, return_: false, deflt: false }
    } else {
        cx_fn(false, true, false)
    }
}

/// The context of the body of an arrow function: `cx_fn` for a braced one, `[?In]`
/// for an expression.
pub open spec fn arrow_bcx(cx: Ctx, is_async: bool, braced: bool) -> Ctx {
    if braced {
        cx_fn(false, is_async, true)
    } else {
        Ctx { yield_: false, await_: is_async, in_: cx.in_, return_: false, deflt: false }
    }
}

/// The two children of node `m` are checked in `c0` and `c1`.
pub open spec fn cx_kids2(a: AstV, cxs: Seq<Cx5>, m: int, c0: Ctx, c1: Ctx) -> bool {
    0 <= m < a.nodes.len() && a.nodes[m].children.len() == 2 && 0 <= a.nodes[m].children[0]
        < cxs.len() && 0 <= a.nodes[m].children[1] < cxs.len() && cx_of(
        cxs[a.nodes[m].children[0]],
    ) == c0 && cx_of(cxs[a.nodes[m].children[1]]) == c1
}

/// §15.3 `ArrowFunction`, §15.9 `AsyncArrowFunction`.
#[verifier::spinoff_prover]
proof fn lemma_arrow_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    p: int,
    b: int,
    is_async: bool,
    x: int,
    mp: int,
    j: int,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= p < m,
        0 <= b < m,
        a.nodes[m].kind == (if is_async {
            NodeKind::AsyncArrowFunction
        } else {
            NodeKind::ArrowFunction
        }),
        a.nodes[m].children =~= seq![p, b],
        !is_async || (is_kw(ts, x, "async"@) && !nl(ts, x + 1)),
        kd(a, p) == NodeKind::BindingIdentifier || kd(a, p) == NodeKind::FormalParameters,
        node_done(
            a,
            ts,
            p,
            arrow_pcx(cx, is_async, kd(a, p) == NodeKind::BindingIdentifier),
            if is_async {
                x + 1
            } else {
                x
            },
            mp,
        ),
        is_p(ts, mp, "=>"@),
        !nl(ts, mp),
        if kd(a, b) == NodeKind::FunctionBody {
            node_done(a, ts, b, arrow_bcx(cx, is_async, true), mp + 1, j)
        } else {
            is_assign_expr(a, b) && !is_p(ts, mp + 1, "{"@) && node_done(
                a,
                ts,
                b,
                arrow_bcx(cx, is_async, false),
                mp + 1,
                j,
            )
        },
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == 0,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == p);
    assert(a.nodes[m].children[1] == b);
    let s = if is_async {
        x + 1
    } else {
        x
    };
    if is_async {
        assert(dc(a, ts, m, p, arrow_pcx(cx, true, kd(a, p) == NodeKind::BindingIdentifier), x + 1, mp));
        assert(d_func(a, ts, m, cx, x, j));
    } else {
        assert(dc(a, ts, m, p, cx, x, mp));
        assert(d_func(a, ts, m, cx, x, j));
    }
    assert(ed(a, ts, p, s) == mp);
    lemma_ed_of(a, ts, m, x, j);
}

/// What `check_arrow` reads: the node and whether it is `async`.
pub struct ArrowShape {
    /// The node.
    pub m: usize,
    /// `async`.
    pub is_async: bool,
}

/// §15.3 `ArrowParameters => ConciseBody` and §15.9 `async ArrowParameters => ConciseBody`.
#[verifier::spinoff_prover]
fn check_arrow(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    sh: &ArrowShape,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        sh.m < nodes.len(),
        nodes@[sh.m as int].kind == (if sh.is_async {
            NodeKind::AsyncArrowFunction
        } else {
            NodeKind::ArrowFunction
        }),
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, sh.m as int),
        0 <= sh.m < done.cxs@.len(),
        cx_of(done.cxs@[sh.m as int]) == g.cx,
        cx_kids2(
            arena_of(nodes@),
            done.cxs@,
            sh.m as int,
            arrow_pcx(
                g.cx,
                sh.is_async,
                kd(arena_of(nodes@), arena_of(nodes@).nodes[sh.m as int].children[0])
                    == NodeKind::BindingIdentifier,
            ),
            arrow_bcx(
                g.cx,
                sh.is_async,
                kd(arena_of(nodes@), arena_of(nodes@).nodes[sh.m as int].children[1])
                    == NodeKind::FunctionBody,
            ),
        ),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(
                arena_of(nodes@),
                g.ts,
                sh.m as int,
                g.cx,
                l0 as int,
                h0 as int,
            ) && l as int == lvl(arena_of(nodes@), sh.m as int),
            None => true,
        },
{
    let m = sh.m;
    proof {
        lemma_words3();
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if nd.children.len() != 2 {
        return None;
    }
    let p = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let b = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let x1 = x.saturating_add(1);
    if sh.is_async
        && (!word_at(src, nodes, toks, gaps, x, &[0x61, 0x73, 0x79, 0x6E, 0x63], Ghost(GW { g, w: "async"@ }))
            || !no_nl_at(src, nodes, toks, gaps, x1, Ghost(g))) {
        return None;
    }
    let s: usize = if sh.is_async { x1 } else { x };
    let kp = kind_at(nodes, p);
    if !matches!(kp, NodeKind::BindingIdentifier | NodeKind::FormalParameters) {
        return None;
    }
    let (lo_p, mp, _) = match done_at(done, p) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let (lo_b, j, _) = match done_at(done, b) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let kb = kind_at(nodes, b);
    let braced = matches!(kb, NodeKind::FunctionBody);
    let mp1 = mp.saturating_add(1);
    if lo_p != s || lo_b != mp1 || !punct2_at(src, nodes, toks, gaps, mp, Ghost(g)) || !no_nl_at(src, nodes, toks, gaps, mp, Ghost(g)) {
        return None;
    }
    if !braced {
        let (_, _, lv_b) = match done_at(done, b) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if lv_b < 0 || brace_at(src, nodes, toks, gaps, mp1, Ghost(g)) {
            return None;
        }
    }
    if !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x1 as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![p as int, b as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(mp < toks.len());
        assert(mp1 as int == mp as int + 1);
        lemma_inv_get_at(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, p as int);
        lemma_inv_get_at(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, b as int);
        assert(kd(a, p as int) == kp);
        assert(kd(a, b as int) == kb);
        assert(cx_of(done.cxs@[p as int]) == arrow_pcx(g.cx, sh.is_async, kd(a, p as int) == NodeKind::BindingIdentifier));
        assert(cx_of(done.cxs@[b as int]) == arrow_bcx(g.cx, sh.is_async, kd(a, b as int) == NodeKind::FunctionBody));
        if !braced {
            assert(lvl(a, b as int) >= 0);
            assert(is_assign_expr(a, b as int));
        }
        lemma_arrow_done(a, g.ts, g.cx, m as int, p as int, b as int, sh.is_async, x as int, mp as int, j as int);
    }
    Some((x, j, 0))
}

/// Token `x` is `=>`.
fn punct2_at(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    x: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: bool)
    requires
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
    ensures
        r ==> x < toks.len() && is_p(g.ts, x as int, "=>"@),
{
    let _ = (nodes.len(), gaps.len());
    let t = match toks.get(x) {
        Some(t) => t,
        None => {
            return false;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, x as int);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        assert(t == &toks@[x as int]);
        reveal_strlit("=>");
        assert("=>"@ =~= seq!['=', '>']);
    }
    let r = matches!(t.kind, TokKind::Punctuator) && text_is(src, t, &[0x3D, 0x3E]);
    proof {
        if r {
            assert(g.ts.toks[x as int].text =~= src@.subrange(t.start as int, t.end as int));
            assert(cps("=>"@) =~= seq![0x3Du32, 0x3E]);
        }
    }
    r
}

/// Token `x` is `{`. (True when it is; a missing token is not.)
fn brace_at(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    x: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: bool)
    requires
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
    ensures
        !r ==> !is_p(g.ts, x as int, "{"@),
{
    proof {
        lemma_brace_text();
    }
    !punct_at_not(src, nodes, toks, gaps, x, Ghost(g))
}

/// Token `x` is not the punctuator `{` (it may not exist).
fn punct_at_not(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    x: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: bool)
    requires
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
    ensures
        r ==> !is_p(g.ts, x as int, "{"@),
{
    let _ = (nodes.len(), gaps.len());
    proof {
        lemma_brace_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let t = match toks.get(x) {
        Some(t) => t,
        None => {
            return true;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, x as int);
        assert(t == &toks@[x as int]);
    }
    let r = !(matches!(t.kind, TokKind::Punctuator) && text_is1(src, t, 0x7B));
    proof {
        if r {
            assert(g.ts.toks[x as int].text =~= src@.subrange(t.start as int, t.end as int));
        }
    }
    r
}

/// The two children of node `m` are checked in `c0` and `c1`.
fn kids_cx2(nodes: &[Node], cxs: &[Cx5], m: usize, c0: &Cx5, c1: &Cx5) -> (r: bool)
    requires
        m < nodes.len(),
        cxs.len() == nodes.len(),
        ast_wf(arena_of(nodes@)),
    ensures
        r ==> cx_kids2(arena_of(nodes@), cxs@, m as int, cx_of(*c0), cx_of(*c1)),
{
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    if nd.children.len() != 2 {
        return false;
    }
    let a0 = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return false;
        },
    };
    let a1 = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return false;
        },
    };
    let (k0, k1) = match (cxs.get(a0), cxs.get(a1)) {
        (Some(x), Some(y)) => (x, y),
        _ => {
            return false;
        },
    };
    cx_eq(k0, c0) && cx_eq(k1, c1)
}

/// The contexts of the parts of an arrow function, as carried (`arrow_pcx`, `arrow_bcx`).
fn arrow_cx5(cx: &Cx5, is_async: bool, ident: bool, braced: bool) -> (r: (Cx5, Cx5))
    ensures
        cx_of(r.0) == arrow_pcx(cx_of(*cx), is_async, ident),
        cx_of(r.1) == arrow_bcx(cx_of(*cx), is_async, braced),
{
    let pc = if !is_async {
        *cx
    } else if ident {
        Cx5 { y: cx.y, a: true, i: true, r: false, d: false }
    } else {
        Cx5 { y: false, a: true, i: true, r: false, d: false }
    };
    let bc = if braced {
        Cx5 { y: false, a: is_async, i: true, r: true, d: false }
    } else {
        Cx5 { y: false, a: is_async, i: cx.i, r: false, d: false }
    };
    (pc, bc)
}

/// §15.5 `yield`, `yield AssignmentExpression`, `yield * AssignmentExpression`.
#[verifier::spinoff_prover]
proof fn lemma_yield_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    c: int,
    x: int,
    delegate: bool,
    bare: bool,
    j: int,
)
    requires
        toks_wf(ts),
        cx.yield_,
        0 <= m < a.nodes.len(),
        0 <= c < m,
        a.nodes[m].kind == NodeKind::YieldExpression,
        a.nodes[m].children =~= seq![c],
        a.nodes[m].op == (if delegate {
            Op::YieldDelegate
        } else {
            Op::YieldPlain
        }),
        !(delegate && bare),
        is_kw(ts, x, "yield"@),
        if bare {
            kd(a, c) == NodeKind::Absent && j == x + 1 && d(a, ts, c, cx, x + 1, x + 1)
        } else if delegate {
            !nl(ts, x + 1) && is_p(ts, x + 1, "*"@) && is_assign_expr(a, c) && node_done(
                a,
                ts,
                c,
                cx,
                x + 2,
                j,
            )
        } else {
            !nl(ts, x + 1) && is_assign_expr(a, c) && node_done(a, ts, c, cx, x + 1, j)
        },
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == 0,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == c);
    if bare {
        assert(dc(a, ts, m, c, cx, x + 1, x + 1));
    } else if delegate {
        assert(dc(a, ts, m, c, cx, x + 2, j));
    } else {
        assert(dc(a, ts, m, c, cx, x + 1, j));
    }
    assert(d_expr(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §15.5 `YieldExpression`.
#[verifier::spinoff_prover]
fn check_yield(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_words4();
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let cxm = match done.cxs.get(m) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::YieldExpression) || nd.children.len() != 1 || !cxm.y {
        return None;
    }
    let delegate = matches!(nd.op, Op::YieldDelegate);
    if !(delegate || matches!(nd.op, Op::YieldPlain)) {
        return None;
    }
    let c = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !word_at(src, nodes, toks, gaps, x, &[0x79, 0x69, 0x65, 0x6C, 0x64], Ghost(GW { g, w: "yield"@ })) {
        return None;
    }
    let x1 = x.saturating_add(1);
    let bare = matches!(kind_at(nodes, c), NodeKind::Absent);
    if bare && delegate {
        return None;
    }
    let j: usize = if bare {
        if !check_absent(src, nodes, toks, gaps, c, x1, Ghost(g)) {
            return None;
        }
        x1
    } else {
        let lo_expect: usize = if delegate { x.saturating_add(2) } else { x1 };
        let (lo_c, hi_c, lv_c) = match done_at(done, c) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if lv_c < 0 || lo_c != lo_expect || !no_nl_at(src, nodes, toks, gaps, x1, Ghost(g)) {
            return None;
        }
        if delegate && !punct_at(src, nodes, toks, gaps, x1, 0x2A, Ghost(GW { g, w: "*"@ })) {
            return None;
        }
        hi_c
    };
    if !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x1 as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].op == nd.op);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(cxm == &done.cxs@[m as int]);
        assert(g.cx.yield_);
        if !bare {
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 0);
            assert(lvl(a, c as int) >= 0);
            assert(is_assign_expr(a, c as int));
            if delegate {
                assert(x.saturating_add(2) as int == x as int + 2);
            }
        }
        lemma_yield_done(a, g.ts, g.cx, m as int, c as int, x as int, delegate, bare, j as int);
    }
    Some((x, j, 0))
}

/// §15.8 `AwaitExpression : await UnaryExpression`.
#[verifier::spinoff_prover]
proof fn lemma_await_done(a: AstV, ts: Stream, cx: Ctx, m: int, c: int, x: int, j: int)
    requires
        toks_wf(ts),
        cx.await_,
        0 <= m < a.nodes.len(),
        0 <= c < m,
        a.nodes[m].kind == NodeKind::AwaitExpression,
        a.nodes[m].children =~= seq![c],
        is_kw(ts, x, "await"@),
        lvl(a, c) >= 12,
        node_done(a, ts, c, cx, x + 1, j),
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == 12,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == c);
    assert(dc(a, ts, m, c, cx, x + 1, j));
    assert(d_expr(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §15.8 `AwaitExpression`.
#[verifier::spinoff_prover]
fn check_await(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_words4();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let cxm = match done.cxs.get(m) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::AwaitExpression) || nd.children.len() != 1 || !cxm.a {
        return None;
    }
    let c = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let (lo_c, j, lv_c) = match done_at(done, c) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    if !word_at(src, nodes, toks, gaps, x, &[0x61, 0x77, 0x61, 0x69, 0x74], Ghost(GW { g, w: "await"@ }))
        || lv_c < 12 || lo_c != x.saturating_add(1) || !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g))
        || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(cxm == &done.cxs@[m as int]);
        assert(g.cx.await_);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 0);
        assert(lvl(a, c as int) >= 12);
        lemma_await_done(a, g.ts, g.cx, m as int, c as int, x as int, j as int);
    }
    Some((x, j, 12))
}

/// The words `yield` and `await`, as code points.
pub(crate) proof fn lemma_words4()
    ensures
        cps("yield"@) =~= seq![0x79u32, 0x69, 0x65, 0x6C, 0x64],
        cps("await"@) =~= seq![0x61u32, 0x77, 0x61, 0x69, 0x74],
{
    reveal_strlit("yield");
    reveal_strlit("await");
    assert("yield"@ =~= seq!['y', 'i', 'e', 'l', 'd']);
    assert("await"@ =~= seq!['a', 'w', 'a', 'i', 't']);
}

/// §15.1 `FunctionRestParameter : ... BindingIdentifier`.
#[verifier::spinoff_prover]
proof fn lemma_rest_param_done(a: AstV, ts: Stream, cx: Ctx, m: int, c: int, x: int, j: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= c < m,
        a.nodes[m].kind == NodeKind::FunctionRestParameter,
        a.nodes[m].children =~= seq![c],
        is_p(ts, x, "..."@),
        is_binding_target_kind(kd(a, c)),
        node_done(a, ts, c, cx, x + 1, j),
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == c);
    assert(dc(a, ts, m, c, cx, x + 1, j));
    assert(d_func(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// Token `x` is `...`.
fn ellipsis_at(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    x: usize,
    Ghost(g): Ghost<GCx>,
) -> (r: bool)
    requires
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
    ensures
        r ==> x < toks.len() && is_p(g.ts, x as int, "..."@),
{
    let _ = (nodes.len(), gaps.len());
    let t = match toks.get(x) {
        Some(t) => t,
        None => {
            return false;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, x as int);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        assert(t == &toks@[x as int]);
        reveal_strlit("...");
        assert("..."@ =~= seq!['.', '.', '.']);
    }
    let r = matches!(t.kind, TokKind::Punctuator) && text_is(src, t, &[0x2E, 0x2E, 0x2E]);
    proof {
        if r {
            assert(g.ts.toks[x as int].text =~= src@.subrange(t.start as int, t.end as int));
            assert(cps("..."@) =~= seq![0x2Eu32, 0x2E, 0x2E]);
        }
    }
    r
}

/// §15.1 `FunctionRestParameter`.
#[verifier::spinoff_prover]
fn check_rest_param(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::FunctionRestParameter) || nd.children.len() != 1 {
        return None;
    }
    let c = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let (lo_c, j, _) = match done_at(done, c) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    if !ellipsis_at(src, nodes, toks, gaps, x, Ghost(g))
        || !matches!(kind_at(nodes, c), NodeKind::BindingIdentifier | NodeKind::ObjectBindingPattern | NodeKind::ArrayBindingPattern)
        || lo_c != x.saturating_add(1) || !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g))
        || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 0);
        lemma_rest_param_done(a, g.ts, g.cx, m as int, c as int, x as int, j as int);
    }
    Some((x, j, -100))
}

// ---------------------------------------------------------------------
// The `for` statements (§14.7.4, §14.7.5): their heads are `[~In]`.
// ---------------------------------------------------------------------

/// The context of a `for` head: `[~In]`, `[Default]` cleared (`cx_in(cx, false)`).
fn cx5_noin(p: &Cx5) -> (r: Cx5)
    ensures
        cx_of(r) == cx_in(cx_of(*p), false),
{
    Cx5 { y: p.y, a: p.a, i: false, r: p.r, d: false }
}

/// The same context with `[+In]` and `[Default]` cleared (`cx_in(cx, true)`).
fn cx5_in(p: &Cx5) -> (r: Cx5)
    ensures
        cx_of(r) == cx_in(cx_of(*p), true),
{
    Cx5 { y: p.y, a: p.a, i: true, r: p.r, d: false }
}

/// Node `m` is checked in `c0`, its second child in `c1` (the initializer of a binding or
/// pattern element, the consequent of a conditional, the property of `a[b]`) and every other
/// child in `c0`: `cx_ok_init`.
fn kids_init(nodes: &[Node], cxs: &[Cx5], m: usize, c0: &Cx5, c1: &Cx5) -> (r: bool)
    requires
        m < nodes.len(),
        cxs.len() == nodes.len(),
        ast_wf(arena_of(nodes@)),
    ensures
        r ==> cx_ok_init(arena_of(nodes@), cxs@, m as int, cx_of(*c0), cx_of(*c1)),
{
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    match cxs.get(m) {
        Some(x) => {
            if !cx_eq(x, c0) {
                return false;
            }
        },
        None => {
            return false;
        },
    }
    let len = nd.children.len();
    let ghost a = arena_of(nodes@);
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children.len() == len);
    }
    let mut k: usize = 0;
    while k < len
        invariant
            m < nodes.len(),
            nodes@.len() == nodes.len(),
            a == arena_of(nodes@),
            ast_wf(a),
            nd == &nodes@[m as int],
            len == nd.children.len(),
            len == a.nodes[m as int].children.len(),
            k <= len,
            cxs.len() == nodes.len(),
            cx_of(cxs@[m as int]) == cx_of(*c0),
            forall|q: int|
                0 <= q < k ==> 0 <= #[trigger] a.nodes[m as int].children[q] < cxs.len()
                    && cx_of(cxs@[a.nodes[m as int].children[q]]) == (if q == 1 {
                    cx_of(*c1)
                } else {
                    cx_of(*c0)
                }),
        decreases len - k,
    {
        let ch = match nd.children.as_slice().get(k) {
            Some(x) => *x as usize,
            None => {
                return false;
            },
        };
        proof {
            assert(a.nodes[m as int].children[k as int] == ch as int);
            lemma_child_before(a, m as int, k as int);
        }
        let cc = match cxs.get(ch) {
            Some(x) => x,
            None => {
                return false;
            },
        };
        if !cx_eq(cc, if k == 1 { c1 } else { c0 }) {
            return false;
        }
        k = k.saturating_add(1);
    }
    true
}

/// The four children of node `m` are checked in `c0`..`c3`.
pub open spec fn cx_kids4(a: AstV, cxs: Seq<Cx5>, m: int, c0: Ctx, c1: Ctx, c2: Ctx, c3: Ctx) -> bool {
    0 <= m < a.nodes.len() && a.nodes[m].children.len() == 4 && (forall|k: int|
        0 <= k < 4 ==> 0 <= #[trigger] a.nodes[m].children[k] < cxs.len()) && cx_of(
        cxs[a.nodes[m].children[0]],
    ) == c0 && cx_of(cxs[a.nodes[m].children[1]]) == c1 && cx_of(cxs[a.nodes[m].children[2]])
        == c2 && cx_of(cxs[a.nodes[m].children[3]]) == c3
}

/// The four children of node `m` are checked in `c0`..`c3`.
fn kids_cx4(nodes: &[Node], cxs: &[Cx5], m: usize, c0: &Cx5, c1: &Cx5, c2: &Cx5, c3: &Cx5) -> (r: bool)
    requires
        m < nodes.len(),
        cxs.len() == nodes.len(),
        ast_wf(arena_of(nodes@)),
    ensures
        r ==> cx_kids4(arena_of(nodes@), cxs@, m as int, cx_of(*c0), cx_of(*c1), cx_of(*c2), cx_of(*c3)),
{
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    if nd.children.len() != 4 {
        return false;
    }
    let a0 = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return false;
        },
    };
    let a1 = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return false;
        },
    };
    let a2 = match kid_of(nodes, m, 2) {
        Some(c) => c,
        None => {
            return false;
        },
    };
    let a3 = match kid_of(nodes, m, 3) {
        Some(c) => c,
        None => {
            return false;
        },
    };
    let (k0, k1, k2, k3) = match (cxs.get(a0), cxs.get(a1), cxs.get(a2), cxs.get(a3)) {
        (Some(x), Some(y), Some(z), Some(w)) => (x, y, z, w),
        _ => {
            return false;
        },
    };
    let ok = cx_eq(k0, c0) && cx_eq(k1, c1) && cx_eq(k2, c2) && cx_eq(k3, c3);
    proof {
        let a = arena_of(nodes@);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        if ok {
            assert forall|k: int| 0 <= k < 4 implies 0 <= #[trigger] a.nodes[m as int].children[k] < cxs.len() by {
                lemma_child_before(a, m as int, k);
            }
        }
    }
    ok
}

/// Token `x` is not the keyword `w` (it may not exist).
fn not_word_at(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    x: usize,
    w: &[u32],
    Ghost(gw): Ghost<GW>,
) -> (r: bool)
    requires
        env_ok(src@, nodes@, toks@, gaps@, gw.g.ts),
        cps(gw.w) =~= w@,
    ensures
        r ==> !is_kw(gw.g.ts, x as int, gw.w),
{
    let _ = (nodes.len(), gaps.len());
    let ghost g = gw.g;
    proof {
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let t = match toks.get(x) {
        Some(t) => t,
        None => {
            return true;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, x as int);
        assert(t == &toks@[x as int]);
    }
    let r = !(matches!(t.kind, TokKind::IdentifierName) && !t.escaped && text_is(src, t, w));
    proof {
        if r {
            assert(g.ts.toks[x as int].text =~= src@.subrange(t.start as int, t.end as int));
        }
    }
    r
}

/// §14.3.2 `var VariableDeclarationList`, as the head of a `for`.
#[verifier::spinoff_prover]
proof fn lemma_vdl_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int, e: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        a.nodes[m].kind == NodeKind::VariableDeclarationList,
        a.nodes[m].children.len() > 0,
        is_kw(ts, x, "var"@),
        dsep(a, ts, m, a.nodes[m].children, 0, cx, x + 1, e, false),
        forall|k: int|
            0 <= k < a.nodes[m].children.len() ==> list_item_ok(a, #[trigger] a.nodes[m].children[k], 2),
        x + 1 <= e <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[e - 1].end,
    ensures
        node_done(a, ts, m, cx, x, e),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, e));
    assert forall|k: int| 0 <= k < a.nodes[m].children.len() implies kd(
        a,
        #[trigger] a.nodes[m].children[k],
    ) == NodeKind::VariableDeclaration by {
        assert(list_item_ok(a, a.nodes[m].children[k], 2));
    }
    assert(d_stmt(a, ts, m, cx, x, e));
    lemma_ed_of(a, ts, m, x, e);
}

/// §14.3.2 `var VariableDeclarationList`.
#[verifier::spinoff_prover]
fn check_var_list(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_decl_words();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::VariableDeclarationList) || nd.children.is_empty() {
        return None;
    }
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !word_at(src, nodes, toks, gaps, x, &[0x76, 0x61, 0x72], Ghost(GW { g, w: "var"@ })) {
        return None;
    }
    let ls = ListSpec { m, start: x.saturating_add(1), mode: 2, trail: false };
    let e = match check_list(src, nodes, toks, gaps, done, &ls, Ghost(g)) {
        Some(e) => e,
        None => {
            return None;
        },
    };
    if !end_ok(src, nodes, toks, gaps, nd.end, e, Ghost(g)) {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(a.nodes[m as int].children.len() > 0);
        lemma_vdl_done(a, g.ts, g.cx, m as int, x as int, e as int);
    }
    Some((x, e, -100))
}

/// §14.7.5 `ForDeclaration : var|let|const ForBinding`.
#[verifier::spinoff_prover]
proof fn lemma_for_decl_done(a: AstV, ts: Stream, cx: Ctx, m: int, c: int, x: int, j: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= c < m,
        a.nodes[m].kind == NodeKind::ForDeclaration,
        a.nodes[m].children =~= seq![c],
        if a.nodes[m].op == Op::Var {
            is_kw(ts, x, "var"@)
        } else if a.nodes[m].op == Op::Let {
            is_kw(ts, x, "let"@)
        } else {
            a.nodes[m].op == Op::Const && is_kw(ts, x, "const"@)
        },
        is_binding_target_kind(kd(a, c)) || (a.nodes[m].op == Op::Var && kd(a, c) == NodeKind::VariableDeclaration),
        node_done(a, ts, c, cx, x + 1, j),
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == c);
    assert(dc(a, ts, m, c, cx, x + 1, j));
    assert(d_stmt(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.7.5 `ForDeclaration`.
#[verifier::spinoff_prover]
fn check_for_decl(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_decl_words();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::ForDeclaration) || nd.children.len() != 1 {
        return None;
    }
    let c = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let kw_ok = match nd.op {
        Op::Var => word_at(src, nodes, toks, gaps, x, &[0x76, 0x61, 0x72], Ghost(GW { g, w: "var"@ })),
        Op::Let => word_at(src, nodes, toks, gaps, x, &[0x6C, 0x65, 0x74], Ghost(GW { g, w: "let"@ })),
        Op::Const => word_at(src, nodes, toks, gaps, x, &[0x63, 0x6F, 0x6E, 0x73, 0x74], Ghost(GW { g, w: "const"@ })),
        _ => false,
    };
    let (lo_c, j, _) = match done_at(done, c) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let target_ok = match kind_at(nodes, c) {
        NodeKind::BindingIdentifier | NodeKind::ObjectBindingPattern | NodeKind::ArrayBindingPattern => true,
        NodeKind::VariableDeclaration => matches!(nd.op, Op::Var),
        _ => false,
    };
    if !kw_ok || !target_ok
        || lo_c != x.saturating_add(1) || !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g))
        || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].op == nd.op);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 0);
        lemma_for_decl_done(a, g.ts, g.cx, m as int, c as int, x as int, j as int);
    }
    Some((x, j, -100))
}

/// §14.7.4 `for ( init ; test ; update ) Statement`.
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
proof fn lemma_for_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    k0: int,
    k1: int,
    k2: int,
    k3: int,
    x: int,
    m0: int,
    q: int,
    r: int,
    j: int,
)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= k0 < m,
        0 <= k1 < m,
        0 <= k2 < m,
        0 <= k3 < m,
        a.nodes[m].kind == NodeKind::ForStatement,
        a.nodes[m].children =~= seq![k0, k1, k2, k3],
        is_kw(ts, x, "for"@),
        is_p(ts, x + 1, "("@),
        is_statement_kind(kd(a, k3)),
        d(a, ts, k0, cx_in(cx, false), x + 2, m0),
        ed(a, ts, k0, x + 2) == m0,
        if kd(a, k0) == NodeKind::LexicalDeclaration {
            is_p(ts, m0 - 1, ";"@)
        } else {
            is_p(ts, m0, ";"@) && (kd(a, k0) == NodeKind::Absent || kd(a, k0)
                == NodeKind::VariableDeclarationList || (lvl(a, k0) >= -1 && !(is_kw(
                ts,
                x + 2,
                "let"@,
            ) && is_p(ts, x + 3, "["@))))
        },
        opt_expr(a, k1),
        d(a, ts, k1, cx, for_init_next(a, ts, k0, x + 2), q),
        ed(a, ts, k1, for_init_next(a, ts, k0, x + 2)) == q,
        is_p(ts, q, ";"@),
        opt_expr(a, k2),
        d(a, ts, k2, cx, q + 1, r),
        ed(a, ts, k2, q + 1) == r,
        is_p(ts, r, ")"@),
        d(a, ts, k3, cx, r + 1, j),
        0 <= x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == k0);
    assert(a.nodes[m].children[1] == k1);
    assert(a.nodes[m].children[2] == k2);
    assert(a.nodes[m].children[3] == k3);
    assert(for_init_ok(a, ts, m, k0, cx, x + 2));
    assert(dc(a, ts, m, k1, cx, for_init_next(a, ts, k0, x + 2), q));
    assert(dc(a, ts, m, k2, cx, q + 1, r));
    assert(dc(a, ts, m, k3, cx, r + 1, j));
    assert(d_stmt(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.7.4 `for ( init ; test ; update ) Statement`.
#[verifier::spinoff_prover]
fn check_for(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        0 <= m < done.cxs@.len(),
        cx_of(done.cxs@[m as int]) == g.cx,
        cx_kids4(
            arena_of(nodes@),
            done.cxs@,
            m as int,
            cx_in(g.cx, false),
            g.cx,
            g.cx,
            g.cx,
        ),
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
    proof {
        lemma_words5();
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::ForStatement) || nd.children.len() != 4 {
        return None;
    }
    let k0 = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let k1 = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let k2 = match kid_of(nodes, m, 2) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let k3 = match kid_of(nodes, m, 3) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !word_at(src, nodes, toks, gaps, x, &[0x66, 0x6F, 0x72], Ghost(GW { g, w: "for"@ }))
        || !punct_at(src, nodes, toks, gaps, x.saturating_add(1), 0x28, Ghost(GW { g, w: "("@ })) {
        return None;
    }
    let s = x.saturating_add(2);
    let ghost cxi = cx_in(g.cx, false);
    // The initializer.
    let ki = kind_at(nodes, k0);
    let lexical = matches!(ki, NodeKind::LexicalDeclaration);
    let (m0, lv0): (usize, i32) = if matches!(ki, NodeKind::Absent) {
        if !check_absent(src, nodes, toks, gaps, k0, s, Ghost(GCx { ts: g.ts, cx: cxi })) {
            return None;
        }
        (s, -100)
    } else {
        let (lo0, h0, lv0) = match done_at(done, k0) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if lo0 != s {
            return None;
        }
        (h0, lv0)
    };
    let p0: usize = if lexical { m0 } else { m0.saturating_add(1) };
    if lexical {
        if m0 < 1 || !punct_at(src, nodes, toks, gaps, m0.saturating_sub(1), 0x3B, Ghost(GW { g, w: ";"@ })) {
            return None;
        }
    } else {
        let init_ok = matches!(ki, NodeKind::Absent | NodeKind::VariableDeclarationList)
            || (lv0 >= -1 && not_word_at(src, nodes, toks, gaps, s, &[0x6C, 0x65, 0x74], Ghost(GW { g, w: "let"@ })));
        if !init_ok || !punct_at(src, nodes, toks, gaps, m0, 0x3B, Ghost(GW { g, w: ";"@ })) {
            return None;
        }
    }
    // The test.
    let kt = kind_at(nodes, k1);
    let q: usize = if matches!(kt, NodeKind::Absent) {
        if !check_absent(src, nodes, toks, gaps, k1, p0, Ghost(g)) {
            return None;
        }
        p0
    } else {
        let (lo1, h1, lv1) = match done_at(done, k1) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if lo1 != p0 || lv1 < -1 {
            return None;
        }
        h1
    };
    if !punct_at(src, nodes, toks, gaps, q, 0x3B, Ghost(GW { g, w: ";"@ })) {
        return None;
    }
    // The update.
    let q1 = q.saturating_add(1);
    let ku = kind_at(nodes, k2);
    let rr: usize = if matches!(ku, NodeKind::Absent) {
        if !check_absent(src, nodes, toks, gaps, k2, q1, Ghost(g)) {
            return None;
        }
        q1
    } else {
        let (lo2, h2, lv2) = match done_at(done, k2) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if lo2 != q1 || lv2 < -1 {
            return None;
        }
        h2
    };
    if !punct_at(src, nodes, toks, gaps, rr, 0x29, Ghost(GW { g, w: ")"@ })) {
        return None;
    }
    let (lo3, j, _) = match done_at(done, k3) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    if !stmt_kind_exec(kind_at(nodes, k3)) || lo3 != rr.saturating_add(1)
        || !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(s as int == x as int + 2);
        assert(q1 as int == q as int + 1);
        assert(rr.saturating_add(1) as int == rr as int + 1);
        assert(a.nodes[m as int].children =~= seq![k0 as int, k1 as int, k2 as int, k3 as int]) by {
            assert(a.nodes[m as int].children.len() == 4);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get_at(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, k0 as int);
        lemma_inv_get_at(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, k1 as int);
        lemma_inv_get_at(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, k2 as int);
        lemma_inv_get_at(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, k3 as int);
        assert(kd(a, k0 as int) == ki);
        assert(kd(a, k1 as int) == kt);
        assert(kd(a, k2 as int) == ku);
        assert(kd(a, k3 as int) == nodes@[k3 as int].kind);
        assert(is_statement_kind(kd(a, k3 as int)));
        assert(cx_of(done.cxs@[k0 as int]) == cxi);
        assert(cx_of(done.cxs@[k1 as int]) == g.cx);
        assert(cx_of(done.cxs@[k2 as int]) == g.cx);
        assert(cx_of(done.cxs@[k3 as int]) == g.cx);
        if !matches!(ki, NodeKind::Absent) {
            assert(lvl(a, k0 as int) == lv0 as int);
            assert(kd(a, k0 as int) != NodeKind::Absent);
        }
        if !matches!(kt, NodeKind::Absent) {
            assert(kd(a, k1 as int) != NodeKind::Absent);
        }
        if !matches!(ku, NodeKind::Absent) {
            assert(kd(a, k2 as int) != NodeKind::Absent);
        }
        assert(opt_expr(a, k1 as int));
        assert(opt_expr(a, k2 as int));
        assert(for_init_next(a, g.ts, k0 as int, x as int + 2) == p0 as int);
        assert(m0 >= 1 || !lexical);
        lemma_for_done(a, g.ts, g.cx, m as int, k0 as int, k1 as int, k2 as int, k3 as int, x as int, m0 as int, q as int, rr as int, j as int);
    }
    Some((x, j, -100))
}

/// §14.7.5 `for ( ForDeclaration|LeftHandSideExpression in|of ... ) Statement`.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
proof fn lemma_for_in_of_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    h: int,
    e: int,
    b: int,
    of: bool,
    x: int,
    mh: int,
    q: int,
    j: int,
    s: int,
)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= h < m,
        0 <= e < m,
        0 <= b < m,
        a.nodes[m].kind == (if of {
            NodeKind::ForOfStatement
        } else {
            NodeKind::ForInStatement
        }),
        a.nodes[m].children =~= seq![h, e, b],
        a.nodes[m].flag ==> (of && cx.await_ && is_kw(ts, x + 1, "await"@)),
        s == (if a.nodes[m].flag {
            x + 3
        } else {
            x + 2
        }),
        is_kw(ts, x, "for"@),
        is_p(ts, s - 1, "("@),
        for_head_ok(a, ts, h, s, of, a.nodes[m].flag),
        of ==> first_kid_kind(a, h) != NodeKind::VariableDeclaration,
        if of {
            is_assign_expr(a, e)
        } else {
            lvl(a, e) >= -1
        },
        is_statement_kind(kd(a, b)),
        d(a, ts, h, cx_in(cx, false), s, mh),
        ed(a, ts, h, s) == mh,
        is_kw(ts, mh, if of {
            "of"@
        } else {
            "in"@
        }),
        d(a, ts, e, cx, mh + 1, q),
        ed(a, ts, e, mh + 1) == q,
        is_p(ts, q, ")"@),
        d(a, ts, b, cx, q + 1, j),
        0 <= x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == h);
    assert(a.nodes[m].children[1] == e);
    assert(a.nodes[m].children[2] == b);
    assert(dc(a, ts, m, h, cx_in(cx, false), s, mh));
    assert(dc(a, ts, m, e, cx, mh + 1, q));
    assert(dc(a, ts, m, b, cx, q + 1, j));
    assert(d_stmt(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// What `check_for_in_of` reads: the node, and whether it is `for`-`of`.
pub struct InOfShape {
    /// The node.
    pub m: usize,
    /// `for`-`of` (else `for`-`in`).
    pub of: bool,
}

/// §14.7.5 `for ( head in|of expression ) Statement`, with a declaration or an
/// identifier as head.
#[verifier::spinoff_prover]
fn check_for_in_of(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    sh: &InOfShape,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        sh.m < nodes.len(),
        cx_in(g.cx, true) == g.cx,
        nodes@[sh.m as int].kind == (if sh.of {
            NodeKind::ForOfStatement
        } else {
            NodeKind::ForInStatement
        }),
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, sh.m as int),
        0 <= sh.m < done.cxs@.len(),
        cx_of(done.cxs@[sh.m as int]) == g.cx,
        cx_kids3(arena_of(nodes@), done.cxs@, sh.m as int, cx_in(g.cx, false), g.cx, g.cx),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(
                arena_of(nodes@),
                g.ts,
                sh.m as int,
                g.cx,
                l0 as int,
                h0 as int,
            ) && l as int == lvl(arena_of(nodes@), sh.m as int),
            None => true,
        },
{
    let m = sh.m;
    proof {
        lemma_words5();
        lemma_words4();
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if nd.children.len() != 3 || (nd.flag && !sh.of) {
        return None;
    }
    let cxm = match done.cxs.get(m) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let h = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let e = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let b = match kid_of(nodes, m, 2) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let flag = nd.flag;
    // `for await (`: the `await` is the second token, the head starts after the `(`.
    let s = if flag { x.saturating_add(3) } else { x.saturating_add(2) };
    if !word_at(src, nodes, toks, gaps, x, &[0x66, 0x6F, 0x72], Ghost(GW { g, w: "for"@ }))
        || (flag && !(cxm.a && word_at(src, nodes, toks, gaps, x.saturating_add(1), &[0x61, 0x77, 0x61, 0x69, 0x74], Ghost(GW { g, w: "await"@ }))))
        || !punct_at(src, nodes, toks, gaps, s.saturating_sub(1), 0x28, Ghost(GW { g, w: "("@ })) {
        return None;
    }
    let kh = kind_at(nodes, h);
    let decl = matches!(kh, NodeKind::ForDeclaration);
    let (lo_h, mh, lv_h) = match done_at(done, h) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    // A head that is not a declaration is a `LeftHandSideExpression` that is not an object or
    // array literal, or an assignment pattern; not `let` (`async` for `of`).
    let lhs_ok = matches!(kh, NodeKind::ArrayAssignmentPattern | NodeKind::ObjectAssignmentPattern)
        || (lv_h >= 14 && !matches!(kh, NodeKind::ObjectLiteral | NodeKind::ArrayLiteral));
    let head_ok = decl || (lhs_ok
        && not_word_at(src, nodes, toks, gaps, s, &[0x6C, 0x65, 0x74], Ghost(GW { g, w: "let"@ }))
        && (!sh.of || not_word_at(src, nodes, toks, gaps, s, &[0x61, 0x73, 0x79, 0x6E, 0x63], Ghost(GW { g, w: "async"@ }))));
    // Only `for (var a = 1 in x)` (Annex B.3.5) has a `VariableDeclaration` in its head.
    let head_first_ok = if decl {
        match kid_of(nodes, h, 0) {
            Some(c) => !sh.of || !matches!(kind_at(nodes, c), NodeKind::VariableDeclaration),
            None => false,
        }
    } else {
        match kid_of(nodes, h, 0) {
            Some(c) => !matches!(kind_at(nodes, c), NodeKind::VariableDeclaration),
            None => match nodes.get(h) {
                Some(hn) => hn.children.is_empty(),
                None => false,
            },
        }
    };
    let (lo_e, q, lv_e) = match done_at(done, e) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let (lo_b, j, _) = match done_at(done, b) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let kw_ok = if sh.of {
        word_at(src, nodes, toks, gaps, mh, &[0x6F, 0x66], Ghost(GW { g, w: "of"@ }))
    } else {
        word_at(src, nodes, toks, gaps, mh, &[0x69, 0x6E], Ghost(GW { g, w: "in"@ }))
    };
    let e_ok = if sh.of { lv_e >= 0 } else { lv_e >= -1 };
    if !head_ok || !head_first_ok || lo_h != s || !kw_ok || !e_ok || lo_e != mh.saturating_add(1)
        || !punct_at(src, nodes, toks, gaps, q, 0x29, Ghost(GW { g, w: ")"@ }))
        || !stmt_kind_exec(kind_at(nodes, b)) || lo_b != q.saturating_add(1)
        || !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(a.nodes[m as int].flag == nd.flag);
        assert(s as int == (if a.nodes[m as int].flag {
            x as int + 3
        } else {
            x as int + 2
        }));
        assert(s.saturating_sub(1) as int == s as int - 1);
        assert(cxm == &done.cxs@[m as int]);
        assert(mh.saturating_add(1) as int == mh as int + 1);
        assert(q.saturating_add(1) as int == q as int + 1);
        assert(a.nodes[m as int].children =~= seq![h as int, e as int, b as int]) by {
            assert(a.nodes[m as int].children.len() == 3);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].flag == nd.flag);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get_at(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, h as int);
        lemma_inv_get_at(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, e as int);
        lemma_inv_get_at(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, b as int);
        assert(kd(a, h as int) == kh);
        assert(kd(a, b as int) == nodes@[b as int].kind);
        assert(is_statement_kind(kd(a, b as int)));
        assert(cx_of(done.cxs@[h as int]) == cx_in(g.cx, false));
        assert(cx_of(done.cxs@[e as int]) == g.cx);
        assert(cx_of(done.cxs@[b as int]) == g.cx);
        assert(lvl(a, e as int) == lv_e as int);
        if sh.of {
            assert(is_assign_expr(a, e as int));
        }
        // The head.
        if !decl {
            assert(lvl(a, h as int) == lv_h as int);
            assert(is_destructuring_target(a, h as int));
        }
        assert(a.nodes[h as int] == nodes@[h as int]@);
        assert(for_head_ok(a, g.ts, h as int, s as int, sh.of, a.nodes[m as int].flag)) by {
            if !decl {
                assert(!is_kw(g.ts, s as int, "let"@));
            }
        }
        assert(sh.of ==> first_kid_kind(a, h as int) != NodeKind::VariableDeclaration) by {
            if sh.of {
                if decl {
                    let hc = a.nodes[h as int].children[0];
                    assert(kid(kids(a, h as int), 0) == hc);
                } else if a.nodes[h as int].children.len() == 0 {
                    assert(kid(kids(a, h as int), 0) == -1int);
                } else {
                    let hc = a.nodes[h as int].children[0];
                    assert(kid(kids(a, h as int), 0) == hc);
                }
            }
        }
        lemma_for_in_of_done(a, g.ts, g.cx, m as int, h as int, e as int, b as int, sh.of, x as int, mh as int, q as int, j as int, s as int);
    }
    Some((x, j, -100))
}

/// The words `for`, `of` and `in`, as code points.
proof fn lemma_words5()
    ensures
        cps("for"@) =~= seq![0x66u32, 0x6F, 0x72],
        cps("of"@) =~= seq![0x6Fu32, 0x66],
        cps("in"@) =~= seq![0x69u32, 0x6E],
        cps("let"@) =~= seq![0x6Cu32, 0x65, 0x74],
        cps("async"@) =~= seq![0x61u32, 0x73, 0x79, 0x6E, 0x63],
{
    reveal_strlit("for");
    reveal_strlit("of");
    reveal_strlit("in");
    reveal_strlit("let");
    reveal_strlit("async");
    assert("for"@ =~= seq!['f', 'o', 'r']);
    assert("of"@ =~= seq!['o', 'f']);
    assert("in"@ =~= seq!['i', 'n']);
    assert("let"@ =~= seq!['l', 'e', 't']);
    assert("async"@ =~= seq!['a', 's', 'y', 'n', 'c']);
}

// ---------------------------------------------------------------------
// Array and object literals (§13.2.4, §13.2.5): elements, holes, spread,
// properties (shorthand, `key: value`, spread), computed names.
// ---------------------------------------------------------------------

/// What an array literal accepts as an element.
pub open spec fn array_item_ok(a: AstV, c: int) -> bool {
    lvl(a, c) >= 0 || kd(a, c) == NodeKind::SpreadElement || kd(a, c) == NodeKind::Elision
}

/// What an array literal (mode 0) or an array binding pattern (mode 6) accepts as an element.
pub open spec fn array_item_mode_ok(a: AstV, c: int, mode: int) -> bool {
    if mode == 6 {
        kd(a, c) == NodeKind::BindingElement || kd(a, c) == NodeKind::Elision || kd(a, c)
            == NodeKind::BindingRestElement
    } else if mode == 8 {
        kd(a, c) == NodeKind::AssignmentElement || kd(a, c) == NodeKind::Elision || kd(a, c)
            == NodeKind::AssignmentRestElement
    } else {
        array_item_ok(a, c)
    }
}

/// `array_item_mode_ok`, executable.
fn array_item_exec(l: i32, k: NodeKind, mode: u8) -> (r: bool)
    ensures
        r ==> (if mode == 6 {
            k == NodeKind::BindingElement || k == NodeKind::Elision || k
                == NodeKind::BindingRestElement
        } else if mode == 8 {
            k == NodeKind::AssignmentElement || k == NodeKind::Elision || k
                == NodeKind::AssignmentRestElement
        } else {
            l as int >= 0 || k == NodeKind::SpreadElement || k == NodeKind::Elision
        }),
{
    if mode == 6 {
        matches!(k, NodeKind::BindingElement | NodeKind::Elision | NodeKind::BindingRestElement)
    } else if mode == 8 {
        matches!(k, NodeKind::AssignmentElement | NodeKind::Elision | NodeKind::AssignmentRestElement)
    } else {
        l >= 0 || matches!(k, NodeKind::SpreadElement | NodeKind::Elision)
    }
}

/// §13.2.4 `Elision : ,` (a hole): a `,`.
#[verifier::spinoff_prover]
proof fn lemma_elision_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= x < tn(ts),
        a.nodes[m].kind == NodeKind::Elision,
        a.nodes[m].children.len() == 0,
        is_p(ts, x, ","@),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[x].end,
    ensures
        node_done(a, ts, m, cx, x, x + 1),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, x + 1));
    assert(d_pat(a, ts, m, cx, x, x + 1));
    lemma_ed_of(a, ts, m, x, x + 1);
}

/// §13.2.4 an `Elision`.
#[verifier::spinoff_prover]
fn check_elision(
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
    proof {
        lemma_comma_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::Elision) || !nd.children.is_empty() {
        return None;
    }
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !punct_at(src, nodes, toks, gaps, x, 0x2C, Ghost(GW { g, w: ","@ }))
        || !end_ok(src, nodes, toks, gaps, nd.end, x.saturating_add(1), Ghost(g)) {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].children.len() == 0);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_elision_done(a, g.ts, g.cx, m as int, x as int);
    }
    Some((x, x.saturating_add(1), -100))
}

/// The elements of an array literal: `spec::darray` of the children, ending at `e`.
fn check_array_items(
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
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, ls.m as int),
        kids_ok(arena_of(nodes@), done.cxs@, ls.m as int, g.cx),
    ensures
        match r {
            Some(e) => ls.start <= e && e <= toks.len() && darray(
                arena_of(nodes@),
                g.ts,
                ls.m as int,
                arena_of(nodes@).nodes[ls.m as int].children,
                0,
                g.cx,
                ls.start as int,
                e as int,
            ) && forall|k: int|
                0 <= k < arena_of(nodes@).nodes[ls.m as int].children.len() ==> array_item_mode_ok(
                    arena_of(nodes@),
                    #[trigger] arena_of(nodes@).nodes[ls.m as int].children[k],
                    ls.mode as int,
                ),
            None => true,
        },
{
    let _ = gaps.len();
    let m = ls.m;
    let start = ls.start;
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
        if start > toks.len() {
            return None;
        }
        proof {
            assert(darray(a, g.ts, m as int, a.nodes[m as int].children, 0, g.cx, start as int, start as int));
        }
        return Some(start);
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
    let (lo_c, hc, lvl_c) = match done_at(done, c) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let kc_kind = kind_at(nodes, c);
    if !array_item_exec(lvl_c, kc_kind, ls.mode) {
        return None;
    }
    let is_hole = matches!(kc_kind, NodeKind::Elision);
    let mut comma_after = false;
    if let Some(t) = toks.get(hc) {
        proof {
            lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, hc as int);
            assert(t == &toks@[hc as int]);
        }
        if !is_hole
            && !matches!(kc_kind, NodeKind::BindingRestElement | NodeKind::AssignmentRestElement)
            && matches!(t.kind, TokKind::Punctuator) && text_is1(src, t, 0x2C) {
            comma_after = true;
        }
    }
    let e: usize = if comma_after { hc.saturating_add(1) } else { hc };
    proof {
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, last as int);
        assert(hc <= toks.len());
        assert(kd(a, c as int) == nodes@[c as int].kind);
        assert(kd(a, c as int) == kc_kind);
        if comma_after {
            lemma_comma_text();
            lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, hc as int);
            assert(hc < toks.len());
            assert(e as int == hc as int + 1);
            assert(g.ts.toks[hc as int].kind == TokKind::Punctuator);
            assert(g.ts.toks[hc as int].text =~= seq![0x2Cu32]);
            assert(is_p(g.ts, hc as int, ","@));
            assert(!is_rest_kind(kd(a, c as int)));
        } else {
            assert(e == hc);
        }
        assert(e <= toks.len());
        assert(ed(a, g.ts, c as int, lo_c as int) == hc as int);
        let ks = a.nodes[m as int].children;
        assert(dc(a, g.ts, m as int, c as int, g.cx, lo_c as int, hc as int));
        reveal_with_fuel(darray, 2);
        assert(darray(a, g.ts, m as int, ks, last as int, g.cx, lo_c as int, e as int));
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
            pos <= e,
            ast_wf(a),
            env_ok(src@, nodes@, toks@, gaps@, g.ts),
            inv(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
            kids_ok(a, done.cxs@, m as int, g.cx),
            darray(a, g.ts, m as int, a.nodes[m as int].children, k as int, g.cx, pos as int, e as int),
            forall|q: int|
                k <= q < len ==> array_item_mode_ok(a, #[trigger] a.nodes[m as int].children[q], ls.mode as int),
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
        let (lo2, hi2, lvl2) = match done_at(done, c2) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        let kind2 = kind_at(nodes, c2);
        if !array_item_exec(lvl2, kind2, ls.mode) {
            return None;
        }
        if matches!(kind2, NodeKind::Elision) {
            if hi2 != pos {
                return None;
            }
        } else {
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
            if !matches!(sep.kind, TokKind::Punctuator) || !text_is1(src, sep, 0x2C)
                || hi2.saturating_add(1) != pos {
                return None;
            }
        }
        proof {
            lemma_comma_text();
            lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c2 as int, g.cx, k as int - 1);
            assert(kd(a, c2 as int) == kind2);
            assert(hi2 <= toks.len());
            assert(ed(a, g.ts, c2 as int, lo2 as int) == hi2 as int);
            let ks = a.nodes[m as int].children;
            assert(dc(a, g.ts, m as int, c2 as int, g.cx, lo2 as int, hi2 as int));
            if !matches!(kind2, NodeKind::Elision) {
                assert(hi2 < toks.len());
                assert(hi2 + 1 == pos);
                assert(g.ts.toks[hi2 as int].kind == TokKind::Punctuator);
                assert(g.ts.toks[hi2 as int].text =~= seq![0x2Cu32]);
                assert(is_p(g.ts, hi2 as int, ","@));
            }
            reveal_with_fuel(darray, 2);
            assert(darray(a, g.ts, m as int, ks, k as int - 1, g.cx, lo2 as int, e as int));
        }
        pos = lo2;
        k = k.saturating_sub(1);
    }
    if pos != start {
        return None;
    }
    proof {
        assert(forall|q: int|
            0 <= q < len ==> array_item_mode_ok(a, #[trigger] a.nodes[m as int].children[q], ls.mode as int));
    }
    Some(e)
}

/// §13.2.4 `ArrayLiteral : [ elements ]`.
#[verifier::spinoff_prover]
proof fn lemma_array_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int, e: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= x,
        x + 1 <= e < tn(ts),
        a.nodes[m].kind == NodeKind::ArrayLiteral,
        darray(a, ts, m, a.nodes[m].children, 0, cx_in(cx, true), x + 1, e),
        forall|k: int|
            0 <= k < a.nodes[m].children.len() ==> array_item_ok(a, #[trigger] a.nodes[m].children[k]),
        is_p(ts, x, "["@),
        is_p(ts, e, "]"@),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[e].end,
    ensures
        node_done(a, ts, m, cx, x, e + 1),
        lvl(a, m) == 17,
{
    assert(span_ok(a, ts, m, x, e + 1));
    assert(d_expr_lhs(a, ts, m, cx, x, e + 1));
    lemma_ed_of(a, ts, m, x, e + 1);
}

/// §13.2.4 `ArrayLiteral`.
#[verifier::spinoff_prover]
fn check_array(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok_t(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_brackets();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::ArrayLiteral) {
        return None;
    }
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !punct_at(src, nodes, toks, gaps, x, 0x5B, Ghost(GW { g, w: "["@ })) {
        return None;
    }
    let ghost gt = GCx { ts: g.ts, cx: cx_in(g.cx, true) };
    let als = ListSpec { m, start: x.saturating_add(1), mode: 0, trail: true };
    let e = match check_array_items(src, nodes, toks, gaps, done, &als, Ghost(gt)) {
        Some(e) => e,
        None => {
            return None;
        },
    };
    if !punct_at(src, nodes, toks, gaps, e, 0x5D, Ghost(GW { g, w: "]"@ }))
        || !end_ok(src, nodes, toks, gaps, nd.end, e.saturating_add(1), Ghost(g)) {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(e.saturating_add(1) as int == e as int + 1);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(forall|k: int|
            0 <= k < a.nodes[m as int].children.len() ==> array_item_ok(a, #[trigger] a.nodes[m as int].children[k]));
        lemma_array_done(a, g.ts, g.cx, m as int, x as int, e as int);
    }
    Some((x, e.saturating_add(1), 17))
}

/// The brackets `[` and `]`, as code points.
pub(crate) proof fn lemma_brackets()
    ensures
        cps("["@) =~= seq![0x5Bu32],
        cps("]"@) =~= seq![0x5Du32],
{
    reveal_strlit("[");
    reveal_strlit("]");
    assert("["@ =~= seq!['[']);
    assert("]"@ =~= seq![']']);
}

/// §13.2.5 `ObjectLiteral : { PropertyDefinitionList ,? }`.
#[verifier::spinoff_prover]
proof fn lemma_object_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int, e: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= x,
        x + 1 <= e < tn(ts),
        a.nodes[m].kind == NodeKind::ObjectLiteral,
        dsep(a, ts, m, a.nodes[m].children, 0, cx_in(cx, true), x + 1, e, true),
        forall|k: int|
            0 <= k < a.nodes[m].children.len() ==> list_item_ok(a, #[trigger] a.nodes[m].children[k], 5),
        is_p(ts, x, "{"@),
        is_p(ts, e, "}"@),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[e].end,
    ensures
        node_done(a, ts, m, cx, x, e + 1),
        lvl(a, m) == 17,
{
    assert forall|k: int| 0 <= k < a.nodes[m].children.len() implies kd(
        a,
        #[trigger] a.nodes[m].children[k],
    ) == NodeKind::PropertyDefinition || kd(a, a.nodes[m].children[k])
        == NodeKind::CoverInitializedName || kd(a, a.nodes[m].children[k])
        == NodeKind::MethodDefinition by {
        assert(list_item_ok(a, a.nodes[m].children[k], 5));
    }
    assert(span_ok(a, ts, m, x, e + 1));
    assert(d_expr_lhs(a, ts, m, cx, x, e + 1));
    lemma_ed_of(a, ts, m, x, e + 1);
}

/// §13.2.5 `ObjectLiteral`.
#[verifier::spinoff_prover]
fn check_object(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok_t(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_brace_text();
        lemma_words2();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::ObjectLiteral) {
        return None;
    }
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !punct_at(src, nodes, toks, gaps, x, 0x7B, Ghost(GW { g, w: "{"@ })) {
        return None;
    }
    let ghost gt = GCx { ts: g.ts, cx: cx_in(g.cx, true) };
    let ls = ListSpec { m, start: x.saturating_add(1), mode: 5, trail: true };
    let e = match check_list(src, nodes, toks, gaps, done, &ls, Ghost(gt)) {
        Some(e) => e,
        None => {
            return None;
        },
    };
    if !punct_at(src, nodes, toks, gaps, e, 0x7D, Ghost(GW { g, w: "}"@ }))
        || !end_ok(src, nodes, toks, gaps, nd.end, e.saturating_add(1), Ghost(g)) {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(e.saturating_add(1) as int == e as int + 1);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_object_done(a, g.ts, g.cx, m as int, x as int, e as int);
    }
    Some((x, e.saturating_add(1), 17))
}

/// §13.2.5 `PropertyDefinition`: `name`, `key : value`, `... value`.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
proof fn lemma_property_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    k0: int,
    k1: int,
    x: int,
    mk: int,
    j: int,
)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= k0 < m,
        0 <= k1 < m,
        a.nodes[m].kind == NodeKind::PropertyDefinition,
        if a.nodes[m].op == Op::Shorthand {
            a.nodes[m].children =~= seq![k0] && kd(a, k0) == NodeKind::IdentifierReference
                && node_done(a, ts, k0, cx, x, x + 1) && j == x + 1
        } else if a.nodes[m].op == Op::KeyValue {
            a.nodes[m].children =~= seq![k0, k1] && is_prop_name_kind(kd(a, k0)) && is_assign_expr(
                a,
                k1,
            ) && node_done(a, ts, k0, cx, x, mk) && is_p(ts, mk, ":"@) && node_done(
                a,
                ts,
                k1,
                cx,
                mk + 1,
                j,
            )
        } else {
            a.nodes[m].op == Op::Spread && a.nodes[m].children =~= seq![k0] && is_p(ts, x, "..."@)
                && is_assign_expr(a, k0) && node_done(a, ts, k0, cx, x + 1, j)
        },
        0 <= x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == k0);
    if a.nodes[m].op == Op::KeyValue {
        assert(a.nodes[m].children[1] == k1);
        assert(dc(a, ts, m, k0, cx, x, mk));
        assert(dc(a, ts, m, k1, cx_in(cx, true), mk + 1, j));
    } else if a.nodes[m].op == Op::Shorthand {
        assert(dc(a, ts, m, k0, cx, x, x + 1));
    } else {
        assert(dc(a, ts, m, k0, cx_in(cx, true), x + 1, j));
    }
    assert(d_expr_lhs(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §13.2.5 `PropertyDefinition` (without methods and `name = init`).
#[verifier::spinoff_prover]
fn check_property(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::PropertyDefinition) {
        return None;
    }
    let k0 = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let (lo0, h0, lv0) = match done_at(done, k0) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let kk0 = kind_at(nodes, k0);
    let (j, k1, mk): (usize, usize, usize) = match nd.op {
        Op::Shorthand => {
            if nd.children.len() != 1 || !matches!(kk0, NodeKind::IdentifierReference) || lo0 != x {
                return None;
            }
            (h0, k0, 0)
        },
        Op::KeyValue => {
            if nd.children.len() != 2 {
                return None;
            }
            let v = match kid_of(nodes, m, 1) {
                Some(c) => c,
                None => {
                    return None;
                },
            };
            let (lo1, h1, lv1) = match done_at(done, v) {
                Some(r) => r,
                None => {
                    return None;
                },
            };
            if !matches!(
                kk0,
                NodeKind::IdentifierName | NodeKind::StringLiteral | NodeKind::NumericLiteral
                    | NodeKind::ComputedPropertyName
            ) || lo0 != x || lv1 < 0 || !punct_at(src, nodes, toks, gaps, h0, 0x3A, Ghost(GW { g, w: ":"@ }))
                || lo1 != h0.saturating_add(1) {
                return None;
            }
            (h1, v, h0)
        },
        Op::Spread => {
            if nd.children.len() != 1 || lv0 < 0 || lo0 != x.saturating_add(1)
                || !ellipsis_at(src, nodes, toks, gaps, x, Ghost(g)) {
                return None;
            }
            (h0, k0, 0)
        },
        _ => {
            return None;
        },
    };
    let _ = (k1, mk);
    if !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].op == nd.op);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(a.nodes[m as int].children.len() == nd.children.len());
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, k0 as int, g.cx, 0);
        assert(kd(a, k0 as int) == kk0);
        if nd.op == Op::KeyValue {
            assert(mk.saturating_add(0) == mk);
            assert(h0.saturating_add(1) as int == h0 as int + 1);
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, k1 as int, g.cx, 1);
            assert(a.nodes[m as int].children =~= seq![k0 as int, k1 as int]) by {
                assert(a.nodes[m as int].children.len() == 2);
            }
        } else {
            assert(a.nodes[m as int].children =~= seq![k0 as int]) by {
                assert(a.nodes[m as int].children.len() == 1);
            }
        }
        lemma_property_done(a, g.ts, g.cx, m as int, k0 as int, k1 as int, x as int, mk as int, j as int);
    }
    Some((x, j, -100))
}

/// §13.2.5 `ComputedPropertyName : [ AssignmentExpression ]`.
#[verifier::spinoff_prover]
proof fn lemma_computed_done(a: AstV, ts: Stream, cx: Ctx, m: int, c: int, x: int, mc: int)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= c < m,
        a.nodes[m].kind == NodeKind::ComputedPropertyName,
        a.nodes[m].children =~= seq![c],
        is_p(ts, x, "["@),
        is_assign_expr(a, c),
        node_done(a, ts, c, cx, x + 1, mc),
        is_p(ts, mc, "]"@),
        0 <= x,
        mc < tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[mc].end,
    ensures
        node_done(a, ts, m, cx, x, mc + 1),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, mc + 1));
    assert(a.nodes[m].children[0] == c);
    assert(dc(a, ts, m, c, cx_in(cx, true), x + 1, mc));
    assert(d_expr_lhs(a, ts, m, cx, x, mc + 1));
    lemma_ed_of(a, ts, m, x, mc + 1);
}

/// §13.2.5 `ComputedPropertyName`.
#[verifier::spinoff_prover]
fn check_computed(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_brackets();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::ComputedPropertyName) || nd.children.len() != 1 {
        return None;
    }
    let c = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let (lo_c, mc, lv_c) = match done_at(done, c) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    if !punct_at(src, nodes, toks, gaps, x, 0x5B, Ghost(GW { g, w: "["@ })) || lv_c < 0
        || lo_c != x.saturating_add(1) || !punct_at(src, nodes, toks, gaps, mc, 0x5D, Ghost(GW { g, w: "]"@ }))
        || !end_ok(src, nodes, toks, gaps, nd.end, mc.saturating_add(1), Ghost(g)) {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(mc.saturating_add(1) as int == mc as int + 1);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 0);
        assert(lvl(a, c as int) >= 0);
        lemma_computed_done(a, g.ts, g.cx, m as int, c as int, x as int, mc as int);
    }
    Some((x, mc.saturating_add(1), -100))
}

// ---------------------------------------------------------------------
// Binding patterns (§14.3.3): array and object patterns, their elements and
// properties, and `...rest` of a name or a pattern.
// ---------------------------------------------------------------------

/// §14.3.3 `BindingRestElement : ... target`, `BindingRestProperty : ... BindingIdentifier`.
#[verifier::spinoff_prover]
proof fn lemma_binding_rest_done(a: AstV, ts: Stream, cx: Ctx, m: int, c: int, x: int, j: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= c < m,
        a.nodes[m].kind == NodeKind::BindingRestElement || a.nodes[m].kind
            == NodeKind::BindingRestProperty || a.nodes[m].kind == NodeKind::AssignmentRestElement
            || a.nodes[m].kind == NodeKind::AssignmentRestProperty,
        a.nodes[m].children =~= seq![c],
        is_p(ts, x, "..."@),
        (a.nodes[m].kind == NodeKind::AssignmentRestElement || a.nodes[m].kind
            == NodeKind::AssignmentRestProperty) ==> is_destructuring_target(a, c),
        a.nodes[m].kind == NodeKind::BindingRestElement ==> is_binding_target_kind(kd(a, c)),
        a.nodes[m].kind == NodeKind::BindingRestProperty ==> kd(a, c) == NodeKind::BindingIdentifier,
        node_done(a, ts, c, cx, x + 1, j),
        x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == c);
    assert(dc(a, ts, m, c, cx, x + 1, j));
    assert(d_pat(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.3.3 `BindingRestElement`, `BindingRestProperty`.
#[verifier::spinoff_prover]
fn check_binding_rest(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(
        nd.kind,
        NodeKind::BindingRestElement | NodeKind::BindingRestProperty | NodeKind::AssignmentRestElement
            | NodeKind::AssignmentRestProperty
    ) || nd.children.len() != 1 {
        return None;
    }
    let c = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let (lo_c, j, lv_c) = match done_at(done, c) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let kc = kind_at(nodes, c);
    let kind_ok = match nd.kind {
        NodeKind::BindingRestElement => matches!(
            kc,
            NodeKind::BindingIdentifier | NodeKind::ObjectBindingPattern | NodeKind::ArrayBindingPattern
        ),
        NodeKind::BindingRestProperty => matches!(kc, NodeKind::BindingIdentifier),
        _ => matches!(kc, NodeKind::ObjectAssignmentPattern | NodeKind::ArrayAssignmentPattern)
            || (lv_c >= 14 && !matches!(kc, NodeKind::ObjectLiteral | NodeKind::ArrayLiteral)),
    };
    if !ellipsis_at(src, nodes, toks, gaps, x, Ghost(g)) || !kind_ok || lo_c != x.saturating_add(1)
        || !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 0);
        assert(kd(a, c as int) == kc);
        lemma_binding_rest_done(a, g.ts, g.cx, m as int, c as int, x as int, j as int);
    }
    Some((x, j, -100))
}

/// §14.3.3 `BindingProperty : SingleNameBinding | PropertyName : BindingElement`.
#[verifier::spinoff_prover]
proof fn lemma_binding_property_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    k0: int,
    k1: int,
    x: int,
    mk: int,
    j: int,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= k0 < m,
        0 <= k1 < m,
        a.nodes[m].kind == NodeKind::BindingProperty,
        if a.nodes[m].op == Op::Shorthand {
            a.nodes[m].children =~= seq![k0] && kd(a, k0) == NodeKind::BindingElement
                && first_kid_kind(a, k0) == NodeKind::BindingIdentifier && node_done(
                a,
                ts,
                k0,
                cx,
                x,
                j,
            )
        } else {
            a.nodes[m].op == Op::KeyValue && a.nodes[m].children =~= seq![k0, k1]
                && is_prop_name_kind(kd(a, k0)) && kd(a, k1) == NodeKind::BindingElement && node_done(
                a,
                ts,
                k0,
                cx,
                x,
                mk,
            ) && is_p(ts, mk, ":"@) && node_done(a, ts, k1, cx, mk + 1, j)
        },
        0 <= x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == k0);
    if a.nodes[m].op == Op::KeyValue {
        assert(a.nodes[m].children[1] == k1);
        assert(dc(a, ts, m, k0, cx, x, mk));
        assert(dc(a, ts, m, k1, cx, mk + 1, j));
    } else {
        assert(dc(a, ts, m, k0, cx, x, j));
    }
    assert(d_pat(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §14.3.3 `BindingProperty`.
#[verifier::spinoff_prover]
fn check_binding_property(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::BindingProperty) {
        return None;
    }
    let k0 = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let (lo0, h0, _) = match done_at(done, k0) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let kk0 = kind_at(nodes, k0);
    let (j, k1, mk): (usize, usize, usize) = match nd.op {
        Op::Shorthand => {
            // The element's target is a name.
            let first = match kid_of(nodes, k0, 0) {
                Some(c) => matches!(kind_at(nodes, c), NodeKind::BindingIdentifier),
                None => false,
            };
            if nd.children.len() != 1 || !matches!(kk0, NodeKind::BindingElement) || !first
                || lo0 != x {
                return None;
            }
            (h0, k0, 0)
        },
        Op::KeyValue => {
            if nd.children.len() != 2 {
                return None;
            }
            let v = match kid_of(nodes, m, 1) {
                Some(c) => c,
                None => {
                    return None;
                },
            };
            let (lo1, h1, _) = match done_at(done, v) {
                Some(r) => r,
                None => {
                    return None;
                },
            };
            if !matches!(
                kk0,
                NodeKind::IdentifierName | NodeKind::StringLiteral | NodeKind::NumericLiteral
                    | NodeKind::ComputedPropertyName
            ) || !matches!(kind_at(nodes, v), NodeKind::BindingElement) || lo0 != x
                || !punct_at(src, nodes, toks, gaps, h0, 0x3A, Ghost(GW { g, w: ":"@ }))
                || lo1 != h0.saturating_add(1) {
                return None;
            }
            (h1, v, h0)
        },
        _ => {
            return None;
        },
    };
    let _ = (k1, mk);
    if !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(a.nodes[k0 as int] == nodes@[k0 as int]@);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].op == nd.op);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, k0 as int, g.cx, 0);
        assert(kd(a, k0 as int) == kk0);
        if nd.op == Op::KeyValue {
            assert(h0.saturating_add(1) as int == h0 as int + 1);
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, k1 as int, g.cx, 1);
            assert(a.nodes[m as int].children =~= seq![k0 as int, k1 as int]) by {
                assert(a.nodes[m as int].children.len() == 2);
            }
        } else {
            assert(a.nodes[m as int].children =~= seq![k0 as int]) by {
                assert(a.nodes[m as int].children.len() == 1);
            }
        }
        lemma_binding_property_done(a, g.ts, g.cx, m as int, k0 as int, k1 as int, x as int, mk as int, j as int);
    }
    Some((x, j, -100))
}

/// §14.3.3 `ArrayBindingPattern : [ elements ]`.
#[verifier::spinoff_prover]
proof fn lemma_array_pattern_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int, e: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= x,
        x + 1 <= e < tn(ts),
        a.nodes[m].kind == NodeKind::ArrayBindingPattern,
        darray(a, ts, m, a.nodes[m].children, 0, cx, x + 1, e),
        forall|k: int|
            0 <= k < a.nodes[m].children.len() ==> array_item_mode_ok(
                a,
                #[trigger] a.nodes[m].children[k],
                6,
            ),
        rest_only_last(a, a.nodes[m].children),
        is_p(ts, x, "["@),
        is_p(ts, e, "]"@),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[e].end,
    ensures
        node_done(a, ts, m, cx, x, e + 1),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, e + 1));
    assert forall|k: int| 0 <= k < a.nodes[m].children.len() implies kd(
        a,
        #[trigger] a.nodes[m].children[k],
    ) == NodeKind::BindingElement || kd(a, a.nodes[m].children[k]) == NodeKind::Elision || kd(
        a,
        a.nodes[m].children[k],
    ) == NodeKind::BindingRestElement by {
        assert(array_item_mode_ok(a, a.nodes[m].children[k], 6));
    }
    assert(d_pat(a, ts, m, cx, x, e + 1));
    lemma_ed_of(a, ts, m, x, e + 1);
}

/// §14.3.3 `ObjectBindingPattern : { BindingPropertyList ,? }`.
#[verifier::spinoff_prover]
proof fn lemma_object_pattern_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int, e: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= x,
        x + 1 <= e < tn(ts),
        a.nodes[m].kind == NodeKind::ObjectBindingPattern,
        dsep(a, ts, m, a.nodes[m].children, 0, cx, x + 1, e, true),
        forall|k: int|
            0 <= k < a.nodes[m].children.len() ==> list_item_ok(a, #[trigger] a.nodes[m].children[k], 7),
        rest_only_last(a, a.nodes[m].children),
        is_p(ts, x, "{"@),
        is_p(ts, e, "}"@),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[e].end,
    ensures
        node_done(a, ts, m, cx, x, e + 1),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, e + 1));
    assert(all_kind2(a, a.nodes[m].children, 0, NodeKind::BindingProperty, NodeKind::BindingRestProperty)) by {
        assert forall|k: int| 0 <= k < a.nodes[m].children.len() implies kd(
            a,
            #[trigger] a.nodes[m].children[k],
        ) == NodeKind::BindingProperty || kd(a, a.nodes[m].children[k])
            == NodeKind::BindingRestProperty by {
            assert(list_item_ok(a, a.nodes[m].children[k], 7));
        }
    }
    assert(d_pat(a, ts, m, cx, x, e + 1));
    lemma_ed_of(a, ts, m, x, e + 1);
}

/// What `check_pattern` reads: the node and whether it is an array pattern.
pub struct PatShape {
    /// The node.
    pub m: usize,
    /// An array pattern (else an object pattern).
    pub array: bool,
    /// An assignment pattern (else a binding pattern).
    pub assign: bool,
}

/// §14.3.3 `ArrayBindingPattern`, `ObjectBindingPattern`.
#[verifier::spinoff_prover]
fn check_pattern(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    sh: &PatShape,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        sh.m < nodes.len(),
        nodes@[sh.m as int].kind == (if sh.assign {
            if sh.array {
                NodeKind::ArrayAssignmentPattern
            } else {
                NodeKind::ObjectAssignmentPattern
            }
        } else if sh.array {
            NodeKind::ArrayBindingPattern
        } else {
            NodeKind::ObjectBindingPattern
        }),
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, sh.m as int),
        cx_ok(arena_of(nodes@), done.cxs@, sh.m as int, g.cx),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(
                arena_of(nodes@),
                g.ts,
                sh.m as int,
                g.cx,
                l0 as int,
                h0 as int,
            ) && l as int == lvl(arena_of(nodes@), sh.m as int),
            None => true,
        },
{
    let m = sh.m;
    proof {
        lemma_brackets();
        lemma_brace_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let x1 = x.saturating_add(1);
    let (e, close_ok): (usize, bool) = if sh.array {
        if !punct_at(src, nodes, toks, gaps, x, 0x5B, Ghost(GW { g, w: "["@ })) {
            return None;
        }
        let als = ListSpec { m, start: x1, mode: if sh.assign { 8 } else { 6 }, trail: true };
        let e = match check_array_items(src, nodes, toks, gaps, done, &als, Ghost(g)) {
            Some(e) => e,
            None => {
                return None;
            },
        };
        (e, punct_at(src, nodes, toks, gaps, e, 0x5D, Ghost(GW { g, w: "]"@ })))
    } else {
        if !punct_at(src, nodes, toks, gaps, x, 0x7B, Ghost(GW { g, w: "{"@ })) {
            return None;
        }
        let ls = ListSpec { m, start: x1, mode: if sh.assign { 9 } else { 7 }, trail: true };
        let e = match check_list(src, nodes, toks, gaps, done, &ls, Ghost(g)) {
            Some(e) => e,
            None => {
                return None;
            },
        };
        (e, punct_at(src, nodes, toks, gaps, e, 0x7D, Ghost(GW { g, w: "}"@ })))
    };
    if !close_ok || !end_ok(src, nodes, toks, gaps, nd.end, e.saturating_add(1), Ghost(g))
        || !check_rest_last(nodes, m) {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x1 as int == x as int + 1);
        assert(e.saturating_add(1) as int == e as int + 1);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        if sh.assign {
            if sh.array {
                lemma_array_apattern_done(a, g.ts, g.cx, m as int, x as int, e as int);
            } else {
                lemma_object_apattern_done(a, g.ts, g.cx, m as int, x as int, e as int);
            }
        } else if sh.array {
            lemma_array_pattern_done(a, g.ts, g.cx, m as int, x as int, e as int);
        } else {
            lemma_object_pattern_done(a, g.ts, g.cx, m as int, x as int, e as int);
        }
    }
    Some((x, e.saturating_add(1), -100))
}

// ---------------------------------------------------------------------
// Assignment patterns (§13.15.5): `[a, b = 1, ...c] = d`, `({a, b: c, ...d} = e)`.
// ---------------------------------------------------------------------

/// §13.15.5 `ArrayAssignmentPattern : [ elements ]`.
#[verifier::spinoff_prover]
proof fn lemma_array_apattern_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int, e: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= x,
        x + 1 <= e < tn(ts),
        a.nodes[m].kind == NodeKind::ArrayAssignmentPattern,
        darray(a, ts, m, a.nodes[m].children, 0, cx, x + 1, e),
        forall|k: int|
            0 <= k < a.nodes[m].children.len() ==> array_item_mode_ok(
                a,
                #[trigger] a.nodes[m].children[k],
                8,
            ),
        rest_only_last(a, a.nodes[m].children),
        is_p(ts, x, "["@),
        is_p(ts, e, "]"@),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[e].end,
    ensures
        node_done(a, ts, m, cx, x, e + 1),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, e + 1));
    assert forall|k: int| 0 <= k < a.nodes[m].children.len() implies kd(
        a,
        #[trigger] a.nodes[m].children[k],
    ) == NodeKind::AssignmentElement || kd(a, a.nodes[m].children[k]) == NodeKind::Elision || kd(
        a,
        a.nodes[m].children[k],
    ) == NodeKind::AssignmentRestElement by {
        assert(array_item_mode_ok(a, a.nodes[m].children[k], 8));
    }
    assert(d_pat(a, ts, m, cx, x, e + 1));
    lemma_ed_of(a, ts, m, x, e + 1);
}

/// §13.15.5 `ObjectAssignmentPattern : { AssignmentPropertyList ,? }`.
#[verifier::spinoff_prover]
proof fn lemma_object_apattern_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int, e: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= x,
        x + 1 <= e < tn(ts),
        a.nodes[m].kind == NodeKind::ObjectAssignmentPattern,
        dsep(a, ts, m, a.nodes[m].children, 0, cx, x + 1, e, true),
        forall|k: int|
            0 <= k < a.nodes[m].children.len() ==> list_item_ok(a, #[trigger] a.nodes[m].children[k], 9),
        rest_only_last(a, a.nodes[m].children),
        is_p(ts, x, "{"@),
        is_p(ts, e, "}"@),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[e].end,
    ensures
        node_done(a, ts, m, cx, x, e + 1),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, e + 1));
    assert(all_kind2(a, a.nodes[m].children, 0, NodeKind::AssignmentProperty, NodeKind::AssignmentRestProperty)) by {
        assert forall|k: int| 0 <= k < a.nodes[m].children.len() implies kd(
            a,
            #[trigger] a.nodes[m].children[k],
        ) == NodeKind::AssignmentProperty || kd(a, a.nodes[m].children[k])
            == NodeKind::AssignmentRestProperty by {
            assert(list_item_ok(a, a.nodes[m].children[k], 9));
        }
    }
    assert(d_pat(a, ts, m, cx, x, e + 1));
    lemma_ed_of(a, ts, m, x, e + 1);
}

/// §13.15.5 `AssignmentProperty : IdentifierReference Initializer? | PropertyName : AssignmentElement`.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
proof fn lemma_assignment_property_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    k0: int,
    k1: int,
    x: int,
    mk: int,
    j: int,
    with_init: bool,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= k0 < m,
        0 <= k1 < m,
        a.nodes[m].kind == NodeKind::AssignmentProperty,
        a.nodes[m].children =~= seq![k0, k1],
        0 <= x < j <= tn(ts),
        if a.nodes[m].op == Op::Shorthand {
            kd(a, k0) == NodeKind::IdentifierReference && node_done(a, ts, k0, cx, x, x + 1) && (
            if with_init {
                is_p(ts, x + 1, "="@) && is_assign_expr(a, k1) && node_done(
                    a,
                    ts,
                    k1,
                    cx_in(cx, true),
                    x + 2,
                    j,
                )
            } else {
                kd(a, k1) == NodeKind::Absent && j == x + 1 && d(
                    a,
                    ts,
                    k1,
                    cx_in(cx, true),
                    x + 1,
                    x + 1,
                )
            })
        } else {
            a.nodes[m].op == Op::KeyValue && is_prop_name_kind(kd(a, k0)) && kd(a, k1)
                == NodeKind::AssignmentElement && node_done(a, ts, k0, cx, x, mk) && is_p(
                ts,
                mk,
                ":"@,
            ) && node_done(a, ts, k1, cx, mk + 1, j)
        },
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == k0);
    assert(a.nodes[m].children[1] == k1);
    if a.nodes[m].op == Op::KeyValue {
        assert(dc(a, ts, m, k0, cx, x, mk));
        assert(dc(a, ts, m, k1, cx, mk + 1, j));
    } else {
        assert(dc(a, ts, m, k0, cx, x, x + 1));
        if with_init {
            assert(dc(a, ts, m, k1, cx_in(cx, true), x + 2, j));
            assert(d_init(a, ts, m, k1, cx_in(cx, true), x + 1, j, false));
        } else {
            assert(dc(a, ts, m, k1, cx_in(cx, true), x + 1, x + 1));
            assert(d_init(a, ts, m, k1, cx_in(cx, true), x + 1, j, false));
        }
    }
    assert(d_pat(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §13.15.5 `AssignmentProperty`.
#[verifier::spinoff_prover]
fn check_assignment_property(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok_init(
            arena_of(nodes@),
            done.cxs@,
            m as int,
            g.cx,
            if nodes@[m as int].op == Op::Shorthand {
                cx_in(g.cx, true)
            } else {
                g.cx
            },
        ),
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
    proof {
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    proof {
        reveal_strlit("=");
        assert("="@ =~= seq!['=']);
    }
    let ghost gi = GCx { ts: g.ts, cx: cx_in(g.cx, true) };
    if !matches!(nd.kind, NodeKind::AssignmentProperty) || nd.children.len() != 2 {
        return None;
    }
    let k0 = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let k1 = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let (lo0, h0, _) = match done_at(done, k0) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let kk0 = kind_at(nodes, k0);
    let kk1 = kind_at(nodes, k1);
    let x1 = x.saturating_add(1);
    let (j, with_init): (usize, bool) = match nd.op {
        Op::Shorthand => {
            if !matches!(kk0, NodeKind::IdentifierReference) || lo0 != x || h0 != x1 {
                return None;
            }
            if matches!(kk1, NodeKind::Absent) {
                if !check_absent(src, nodes, toks, gaps, k1, x1, Ghost(gi)) {
                    return None;
                }
                (x1, false)
            } else {
                let (lo1, h1, lv1) = match done_at(done, k1) {
                    Some(r) => r,
                    None => {
                        return None;
                    },
                };
                if lv1 < 0 || lo1 != x.saturating_add(2)
                    || !punct_at(src, nodes, toks, gaps, x1, 0x3D, Ghost(GW { g, w: "="@ })) {
                    return None;
                }
                (h1, true)
            }
        },
        Op::KeyValue => {
            let (lo1, h1, _) = match done_at(done, k1) {
                Some(r) => r,
                None => {
                    return None;
                },
            };
            if !matches!(
                kk0,
                NodeKind::IdentifierName | NodeKind::StringLiteral | NodeKind::NumericLiteral
                    | NodeKind::ComputedPropertyName
            ) || !matches!(kk1, NodeKind::AssignmentElement) || lo0 != x
                || !punct_at(src, nodes, toks, gaps, h0, 0x3A, Ghost(GW { g, w: ":"@ }))
                || lo1 != h0.saturating_add(1) {
                return None;
            }
            (h1, false)
        },
        _ => {
            return None;
        },
    };
    let _ = with_init;
    if !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x1 as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![k0 as int, k1 as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].op == nd.op);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        let ci = if nd.op == Op::Shorthand { cx_in(g.cx, true) } else { g.cx };
        lemma_inv_get_init(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, k0 as int, g.cx, ci, 0);
        assert(kd(a, k0 as int) == kk0);
        assert(kd(a, k1 as int) == kk1);
        let mk: usize = if nd.op == Op::KeyValue { h0 } else { 0 };
        if nd.op == Op::KeyValue {
            assert(h0.saturating_add(1) as int == h0 as int + 1);
            lemma_inv_get_init(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, k1 as int, g.cx, ci, 1);
        } else if with_init {
            assert(x.saturating_add(2) as int == x as int + 2);
            lemma_inv_get_init(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, k1 as int, g.cx, ci, 1);
            assert(is_assign_expr(a, k1 as int));
        }
        lemma_assignment_property_done(a, g.ts, g.cx, m as int, k0 as int, k1 as int, x as int, mk as int, j as int, with_init);
    }
    Some((x, j, -100))
}

// ---------------------------------------------------------------------
// `++` and `--` (§13.4), `a[b]` (§13.3.2) and `new` (§13.3.5).
// ---------------------------------------------------------------------

/// The words `new` as code points, and the punctuators `++`, `--`.
proof fn lemma_words6()
    ensures
        cps("new"@) =~= seq![0x6Eu32, 0x65, 0x77],
        cps("++"@) =~= seq![0x2Bu32, 0x2B],
        cps("--"@) =~= seq![0x2Du32, 0x2D],
{
    reveal_strlit("new");
    reveal_strlit("++");
    reveal_strlit("--");
    assert("new"@ =~= seq!['n', 'e', 'w']);
    assert("++"@ =~= seq!['+', '+']);
    assert("--"@ =~= seq!['-', '-']);
}

/// Token `x` is `++` (`inc`) or `--`.
fn incdec_at(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    x: usize,
    inc: bool,
    Ghost(g): Ghost<GCx>,
) -> (r: bool)
    requires
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
    ensures
        r ==> x < toks.len() && is_p(g.ts, x as int, if inc {
            "++"@
        } else {
            "--"@
        }),
{
    let _ = (nodes.len(), gaps.len());
    let t = match toks.get(x) {
        Some(t) => t,
        None => {
            return false;
        },
    };
    proof {
        lemma_words6();
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, x as int);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        assert(t == &toks@[x as int]);
    }
    let r = matches!(t.kind, TokKind::Punctuator)
        && (if inc { text_is(src, t, &[0x2B, 0x2B]) } else { text_is(src, t, &[0x2D, 0x2D]) });
    proof {
        if r {
            assert(g.ts.toks[x as int].text =~= src@.subrange(t.start as int, t.end as int));
        }
    }
    r
}

/// §13.4 `UpdateExpression`.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
proof fn lemma_update_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    c: int,
    x: int,
    prefix: bool,
    inc: bool,
    mo: int,
    j: int,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= c < m,
        a.nodes[m].kind == NodeKind::UpdateExpression,
        a.nodes[m].children =~= seq![c],
        a.nodes[m].op == (if prefix {
            if inc {
                Op::PrefixIncrement
            } else {
                Op::PrefixDecrement
            }
        } else if inc {
            Op::PostfixIncrement
        } else {
            Op::PostfixDecrement
        }),
        if prefix {
            is_p(ts, x, if inc {
                "++"@
            } else {
                "--"@
            }) && lvl(a, c) >= 12 && node_done(a, ts, c, cx, x + 1, j)
        } else {
            lvl(a, c) >= 14 && node_done(a, ts, c, cx, x, mo) && is_p(ts, mo, if inc {
                "++"@
            } else {
                "--"@
            }) && !nl(ts, mo) && j == mo + 1
        },
        0 <= x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == 13,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == c);
    if prefix {
        assert(dc(a, ts, m, c, cx, x + 1, j));
        assert(is_op_tok(ts, x, a.nodes[m].op));
    } else {
        assert(is_lhs_expr(a, c));
        assert(dc(a, ts, m, c, cx, x, mo));
        assert(is_op_tok(ts, mo, a.nodes[m].op));
    }
    assert(d_expr(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §13.4 `UpdateExpression`.
#[verifier::spinoff_prover]
fn check_update(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::UpdateExpression) || nd.children.len() != 1 {
        return None;
    }
    let (prefix, inc): (bool, bool) = match nd.op {
        Op::PrefixIncrement => (true, true),
        Op::PrefixDecrement => (true, false),
        Op::PostfixIncrement => (false, true),
        Op::PostfixDecrement => (false, false),
        _ => {
            return None;
        },
    };
    let c = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let (lo_c, hi_c, lv_c) = match done_at(done, c) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let x1 = x.saturating_add(1);
    let j: usize = if prefix {
        if lv_c < 12 || lo_c != x1 || !incdec_at(src, nodes, toks, gaps, x, inc, Ghost(g)) {
            return None;
        }
        hi_c
    } else {
        if lv_c < 14 || lo_c != x || !incdec_at(src, nodes, toks, gaps, hi_c, inc, Ghost(g))
            || !no_nl_at(src, nodes, toks, gaps, hi_c, Ghost(g)) {
            return None;
        }
        hi_c.saturating_add(1)
    };
    if !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x1 as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].op == nd.op);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 0);
        if !prefix {
            assert(hi_c.saturating_add(1) as int == hi_c as int + 1);
        }
        lemma_update_done(a, g.ts, g.cx, m as int, c as int, x as int, prefix, inc, hi_c as int, j as int);
    }
    Some((x, j, 13))
}

/// §13.3.2 `MemberExpression [ Expression ]`.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
proof fn lemma_member_bracket_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    o: int,
    p: int,
    x: int,
    mo: int,
    q: int,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= o < m,
        0 <= p < m,
        a.nodes[m].kind == NodeKind::MemberExpression,
        a.nodes[m].op == Op::Bracket,
        a.nodes[m].children =~= seq![o, p],
        is_member_or_call(a, o),
        node_done(a, ts, o, cx, x, mo),
        is_p(ts, mo, "["@),
        lvl(a, p) >= -1,
        node_done(a, ts, p, cx_in(cx, true), mo + 1, q),
        is_p(ts, q, "]"@),
        0 <= x < q + 1 <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[q].end,
    ensures
        node_done(a, ts, m, cx, x, q + 1),
        lvl(a, m) == (if lvl(a, o) == 17 {
            17int
        } else {
            15int
        }),
{
    assert(span_ok(a, ts, m, x, q + 1));
    assert(a.nodes[m].children[0] == o);
    assert(a.nodes[m].children[1] == p);
    assert(dc(a, ts, m, o, cx, x, mo));
    assert(dc(a, ts, m, p, cx_in(cx, true), mo + 1, q));
    assert(d_expr_lhs(a, ts, m, cx, x, q + 1));
    lemma_ed_of(a, ts, m, x, q + 1);
}

/// §13.3.2 `object [ expression ]`.
#[verifier::spinoff_prover]
fn check_member_bracket(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok_init(arena_of(nodes@), done.cxs@, m as int, g.cx, cx_in(g.cx, true)),
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
    proof {
        lemma_brackets();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::MemberExpression) || !matches!(nd.op, Op::Bracket)
        || nd.children.len() != 2 {
        return None;
    }
    let o = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let p = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let (lo_o, mo, lv_o) = match done_at(done, o) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let (lo_p, q, lv_p) = match done_at(done, p) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if lo_o != x || !(lv_o == 17 || lv_o == 15) || lv_p < -1 || lo_p != mo.saturating_add(1)
        || !punct_at(src, nodes, toks, gaps, mo, 0x5B, Ghost(GW { g, w: "["@ }))
        || !punct_at(src, nodes, toks, gaps, q, 0x5D, Ghost(GW { g, w: "]"@ }))
        || !end_ok(src, nodes, toks, gaps, nd.end, q.saturating_add(1), Ghost(g)) || lo_o >= q {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(mo.saturating_add(1) as int == mo as int + 1);
        assert(q.saturating_add(1) as int == q as int + 1);
        assert(a.nodes[m as int].children =~= seq![o as int, p as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].op == nd.op);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get_init(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, o as int, g.cx, cx_in(g.cx, true), 0);
        lemma_inv_get_init(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, p as int, g.cx, cx_in(g.cx, true), 1);
        assert(is_member_or_call(a, o as int));
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, q as int);
        assert(g.ts.toks[q as int].end == nd.end as int);
        lemma_member_bracket_done(a, g.ts, g.cx, m as int, o as int, p as int, lo_o as int, mo as int, q as int);
    }
    let own: i32 = if lv_o == 17 { 17 } else { 15 };
    Some((lo_o, q.saturating_add(1), own))
}

/// §13.3.5 `new MemberExpression Arguments`, `new NewExpression`.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
proof fn lemma_new_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    c: int,
    ar: int,
    x: int,
    mc: int,
    with_args: bool,
    j: int,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= c < m,
        0 <= ar < m,
        a.nodes[m].kind == NodeKind::NewExpression,
        a.nodes[m].children =~= seq![c, ar],
        is_kw(ts, x, "new"@),
        node_done(a, ts, c, cx, x + 1, mc),
        if with_args {
            lvl(a, c) == 17 && kd(a, ar) == NodeKind::Arguments && node_done(a, ts, ar, cx, mc, j)
        } else {
            kd(a, ar) == NodeKind::Absent && (lvl(a, c) == 16 || lvl(a, c) == 17) && j == mc && d(
                a,
                ts,
                ar,
                cx,
                mc,
                mc,
            ) && ed(a, ts, ar, mc) == mc
        },
        0 <= x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == (if with_args {
            17int
        } else {
            16int
        }),
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == c);
    assert(a.nodes[m].children[1] == ar);
    assert(dc(a, ts, m, c, cx, x + 1, mc));
    if with_args {
        assert(dc(a, ts, m, ar, cx, mc, j));
    } else {
        assert(dc(a, ts, m, ar, cx, mc, mc));
    }
    assert(d_expr_lhs(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §13.3.5 `new callee Arguments?`.
#[verifier::spinoff_prover]
fn check_new(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_words6();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::NewExpression) || nd.children.len() != 2 {
        return None;
    }
    let c = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let ar = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let (lo_c, mc, lv_c) = match done_at(done, c) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    if !word_at(src, nodes, toks, gaps, x, &[0x6E, 0x65, 0x77], Ghost(GW { g, w: "new"@ }))
        || lo_c != x.saturating_add(1) {
        return None;
    }
    let ka = kind_at(nodes, ar);
    let with_args = !matches!(ka, NodeKind::Absent);
    let j: usize = if with_args {
        let (lo_a, h_a, _) = match done_at(done, ar) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if lv_c != 17 || !matches!(ka, NodeKind::Arguments) || lo_a != mc {
            return None;
        }
        h_a
    } else {
        if !(lv_c == 16 || lv_c == 17) || !check_absent(src, nodes, toks, gaps, ar, mc, Ghost(g)) {
            return None;
        }
        mc
    };
    if !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![c as int, ar as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 0);
        assert(kd(a, ar as int) == ka);
        if with_args {
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, ar as int, g.cx, 1);
        }
        lemma_new_done(a, g.ts, g.cx, m as int, c as int, ar as int, x as int, mc as int, with_args, j as int);
    }
    Some((x, j, if with_args { 17 } else { 16 }))
}

// ---------------------------------------------------------------------
// Classes (§15.7) and methods (§15.4 to §15.8): `class`, its body, methods,
// getters and setters, fields, static blocks, private names.
// ---------------------------------------------------------------------

/// §12.7 `PrivateIdentifier`.
#[verifier::spinoff_prover]
fn check_private(
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
    proof {
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::PrivateIdentifier) || !nd.children.is_empty() {
        return None;
    }
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
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
    if !matches!(t.kind, TokKind::PrivateIdentifier) || t.end != nd.end {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].children.len() == 0);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(g.ts.toks[x as int].end == t.end as int);
        assert(g.ts.toks[x as int].kind == TokKind::PrivateIdentifier);
        assert(g.ts.toks[x as int].start < g.ts.toks[x as int].end);
        assert(span_ok(a, g.ts, m as int, x as int, x as int + 1));
        assert(d_expr_lhs(a, g.ts, m as int, g.cx, x as int, x as int + 1));
        lemma_ed_of(a, g.ts, m as int, x as int, x as int + 1);
    }
    Some((x, x.saturating_add(1), -100))
}

/// The class element name kinds (§15.7 `ClassElementName`), executable.
fn element_name_exec(k: NodeKind) -> (r: bool)
    ensures
        r ==> is_class_element_name_kind(k),
{
    matches!(
        k,
        NodeKind::IdentifierName | NodeKind::StringLiteral | NodeKind::NumericLiteral
            | NodeKind::ComputedPropertyName | NodeKind::PrivateIdentifier
    )
}

/// §15.4 `MethodDefinition` and its generator, `async` and accessor forms.
#[verifier::spinoff_prover]
#[verifier::rlimit(150)]
proof fn lemma_method_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    n0: int,
    p: int,
    b: int,
    x: int,
    mn: int,
    q: int,
    j: int,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= n0 < m,
        0 <= p < m,
        0 <= b < m,
        a.nodes[m].kind == NodeKind::MethodDefinition,
        a.nodes[m].children =~= seq![n0, p, b],
        a.nodes[m].op == Op::Method || a.nodes[m].op == Op::Getter || a.nodes[m].op == Op::Setter
            || a.nodes[m].op == Op::GeneratorMethod || a.nodes[m].op == Op::AsyncMethod
            || a.nodes[m].op == Op::AsyncGeneratorMethod,
        !a.nodes[m].flag || is_kw(ts, x, "static"@),
        ({
            let p0 = if a.nodes[m].flag {
                x + 1
            } else {
                x
            };
            let op = a.nodes[m].op;
            let nm = match op {
                Op::Method => p0,
                Op::Getter | Op::Setter | Op::GeneratorMethod | Op::AsyncMethod => p0 + 1,
                _ => p0 + 2,
            };
            let is_gen = op == Op::GeneratorMethod || op == Op::AsyncGeneratorMethod;
            let is_async = op == Op::AsyncMethod || op == Op::AsyncGeneratorMethod;
            (match op {
                Op::Method => true,
                Op::Getter => is_kw(ts, p0, "get"@),
                Op::Setter => is_kw(ts, p0, "set"@),
                Op::GeneratorMethod => is_p(ts, p0, "*"@),
                Op::AsyncMethod => is_kw(ts, p0, "async"@) && !nl(ts, p0 + 1),
                Op::AsyncGeneratorMethod => is_kw(ts, p0, "async"@) && !nl(ts, p0 + 1) && is_p(
                    ts,
                    p0 + 1,
                    "*"@,
                ),
                _ => false,
            }) && is_class_element_name_kind(kd(a, n0)) && kd(a, p) == NodeKind::FormalParameters
                && kd(a, b) == NodeKind::FunctionBody && (op == Op::Getter ==> kids(a, p).len()
                == 0) && (op == Op::Setter ==> (kids(a, p).len() == 1 && kd(
                a,
                kid(kids(a, p), 0),
            ) == NodeKind::BindingElement)) && node_done(a, ts, n0, cx, nm, mn) && node_done(
                a,
                ts,
                p,
                cx_fn(is_gen, is_async, false),
                mn,
                q,
            ) && node_done(a, ts, b, cx_fn(is_gen, is_async, true), q, j)
        }),
        0 <= x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == n0);
    assert(a.nodes[m].children[1] == p);
    assert(a.nodes[m].children[2] == b);
    let p0 = if a.nodes[m].flag {
        x + 1
    } else {
        x
    };
    let op = a.nodes[m].op;
    let nm = match op {
        Op::Method => p0,
        Op::Getter | Op::Setter | Op::GeneratorMethod | Op::AsyncMethod => p0 + 1,
        _ => p0 + 2,
    };
    let is_gen = op == Op::GeneratorMethod || op == Op::AsyncGeneratorMethod;
    let is_async = op == Op::AsyncMethod || op == Op::AsyncGeneratorMethod;
    assert(dc(a, ts, m, n0, cx, nm, mn));
    assert(dc(a, ts, m, p, cx_fn(is_gen, is_async, false), mn, q));
    assert(dc(a, ts, m, b, cx_fn(is_gen, is_async, true), q, j));
    assert(ed(a, ts, n0, nm) == mn);
    assert(ed(a, ts, p, mn) == q);
    assert(d_method(a, ts, m, cx, x, j));
    assert(d_func(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §15.4 `MethodDefinition`.
#[verifier::spinoff_prover]
fn check_method(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        0 <= m < done.cxs@.len(),
        cx_of(done.cxs@[m as int]) == g.cx,
        cx_kids3(
            arena_of(nodes@),
            done.cxs@,
            m as int,
            g.cx,
            cx_fn(
                nodes@[m as int].op == Op::GeneratorMethod || nodes@[m as int].op
                    == Op::AsyncGeneratorMethod,
                nodes@[m as int].op == Op::AsyncMethod || nodes@[m as int].op
                    == Op::AsyncGeneratorMethod,
                false,
            ),
            cx_fn(
                nodes@[m as int].op == Op::GeneratorMethod || nodes@[m as int].op
                    == Op::AsyncGeneratorMethod,
                nodes@[m as int].op == Op::AsyncMethod || nodes@[m as int].op
                    == Op::AsyncGeneratorMethod,
                true,
            ),
        ),
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
    proof {
        lemma_words3();
        lemma_words7();
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::MethodDefinition) || nd.children.len() != 3 {
        return None;
    }
    let n0 = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let p = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let b = match kid_of(nodes, m, 2) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if nd.flag && !word_at(src, nodes, toks, gaps, x, &[0x73, 0x74, 0x61, 0x74, 0x69, 0x63], Ghost(GW { g, w: "static"@ })) {
        return None;
    }
    let p0: usize = if nd.flag { x.saturating_add(1) } else { x };
    let p1 = p0.saturating_add(1);
    let nm: usize = match nd.op {
        Op::Method => p0,
        Op::Getter | Op::Setter | Op::GeneratorMethod | Op::AsyncMethod => p1,
        Op::AsyncGeneratorMethod => p0.saturating_add(2),
        _ => {
            return None;
        },
    };
    let prefix_ok = match nd.op {
        Op::Method => true,
        Op::Getter => word_at(src, nodes, toks, gaps, p0, &[0x67, 0x65, 0x74], Ghost(GW { g, w: "get"@ })),
        Op::Setter => word_at(src, nodes, toks, gaps, p0, &[0x73, 0x65, 0x74], Ghost(GW { g, w: "set"@ })),
        Op::GeneratorMethod => punct_at(src, nodes, toks, gaps, p0, 0x2A, Ghost(GW { g, w: "*"@ })),
        Op::AsyncMethod => word_at(src, nodes, toks, gaps, p0, &[0x61, 0x73, 0x79, 0x6E, 0x63], Ghost(GW { g, w: "async"@ }))
            && no_nl_at(src, nodes, toks, gaps, p1, Ghost(g)),
        _ => word_at(src, nodes, toks, gaps, p0, &[0x61, 0x73, 0x79, 0x6E, 0x63], Ghost(GW { g, w: "async"@ }))
            && no_nl_at(src, nodes, toks, gaps, p1, Ghost(g))
            && punct_at(src, nodes, toks, gaps, p1, 0x2A, Ghost(GW { g, w: "*"@ })),
    };
    let kn = kind_at(nodes, n0);
    let (lo_n, mn, _) = match done_at(done, n0) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let (lo_p, q, _) = match done_at(done, p) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let (lo_b, j, _) = match done_at(done, b) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    // A getter has no parameters; a setter has one `BindingElement`.
    let pn = match nodes.get(p) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let params_ok = match nd.op {
        Op::Getter => pn.children.is_empty(),
        Op::Setter => {
            pn.children.len() == 1 && match kid_of(nodes, p, 0) {
                Some(c) => matches!(kind_at(nodes, c), NodeKind::BindingElement),
                None => false,
            }
        },
        _ => true,
    };
    if !prefix_ok || !element_name_exec(kn) || lo_n != nm || !params_ok
        || !matches!(kind_at(nodes, p), NodeKind::FormalParameters) || lo_p != mn
        || !matches!(kind_at(nodes, b), NodeKind::FunctionBody) || lo_b != q
        || !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(a.nodes[p as int] == nodes@[p as int]@);
        assert(pn == &nodes@[p as int]);
        assert(a.nodes[m as int].children =~= seq![n0 as int, p as int, b as int]) by {
            assert(a.nodes[m as int].children.len() == 3);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].op == nd.op);
        assert(a.nodes[m as int].flag == nd.flag);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(p0 as int == (if nd.flag { x as int + 1 } else { x as int }));
        assert(p0 < toks.len() || nd.op == Op::Method);
        lemma_inv_get_at(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, n0 as int);
        lemma_inv_get_at(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, p as int);
        lemma_inv_get_at(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, b as int);
        assert(kd(a, n0 as int) == kn);
        assert(kd(a, p as int) == NodeKind::FormalParameters);
        assert(kd(a, b as int) == NodeKind::FunctionBody);
        assert(a.nodes[p as int].children.len() == pn.children.len());
        assert(kids(a, p as int) == a.nodes[p as int].children);
        if nd.op == Op::Setter {
            let c0 = a.nodes[p as int].children[0];
            assert(kid(kids(a, p as int), 0) == c0);
        }
        assert(cx_of(done.cxs@[n0 as int]) == g.cx);
        lemma_method_done(a, g.ts, g.cx, m as int, n0 as int, p as int, b as int, x as int, mn as int, q as int, j as int);
    }
    Some((x, j, -100))
}

/// The words `static`, `get`, `set`, `extends`, as code points.
proof fn lemma_words7()
    ensures
        cps("static"@) =~= seq![0x73u32, 0x74, 0x61, 0x74, 0x69, 0x63],
        cps("get"@) =~= seq![0x67u32, 0x65, 0x74],
        cps("set"@) =~= seq![0x73u32, 0x65, 0x74],
        cps("extends"@) =~= seq![0x65u32, 0x78, 0x74, 0x65, 0x6E, 0x64, 0x73],
        cps("class"@) =~= seq![0x63u32, 0x6C, 0x61, 0x73, 0x73],
{
    reveal_strlit("static");
    reveal_strlit("get");
    reveal_strlit("set");
    reveal_strlit("extends");
    reveal_strlit("class");
    assert("static"@ =~= seq!['s', 't', 'a', 't', 'i', 'c']);
    assert("get"@ =~= seq!['g', 'e', 't']);
    assert("set"@ =~= seq!['s', 'e', 't']);
    assert("extends"@ =~= seq!['e', 'x', 't', 'e', 'n', 'd', 's']);
    assert("class"@ =~= seq!['c', 'l', 'a', 's', 's']);
}

/// §15.7 `FieldDefinition : ClassElementName Initializer? ;`, with `static`.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
proof fn lemma_field_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    n0: int,
    k1: int,
    x: int,
    mn: int,
    q: int,
    j: int,
    with_init: bool,
)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= n0 < m,
        0 <= k1 < m,
        a.nodes[m].kind == NodeKind::FieldDefinition,
        a.nodes[m].children =~= seq![n0, k1],
        !a.nodes[m].flag || is_kw(ts, x, "static"@),
        is_class_element_name_kind(kd(a, n0)),
        node_done(a, ts, n0, cx, if a.nodes[m].flag {
            x + 1
        } else {
            x
        }, mn),
        if with_init {
            is_p(ts, mn, "="@) && is_assign_expr(a, k1) && node_done(a, ts, k1, cx, mn + 1, q)
        } else {
            kd(a, k1) == NodeKind::Absent && q == mn && d(a, ts, k1, cx, mn, mn) && ed(
                a,
                ts,
                k1,
                mn,
            ) == mn
        },
        semi(ts, q, j, false),
        0 <= x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == n0);
    assert(a.nodes[m].children[1] == k1);
    let s = if a.nodes[m].flag {
        x + 1
    } else {
        x
    };
    assert(dc(a, ts, m, n0, cx, s, mn));
    if with_init {
        assert(dc(a, ts, m, k1, cx_in(cx, true), mn + 1, q));
        assert(d_init(a, ts, m, k1, cx_in(cx, true), mn, q, false));
        assert(ed(a, ts, k1, mn + 1) == q);
    } else {
        assert(dc(a, ts, m, k1, cx_in(cx, true), mn, mn));
        assert(d_init(a, ts, m, k1, cx_in(cx, true), mn, q, false));
    }
    assert(d_func(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §15.7 `FieldDefinition`.
#[verifier::spinoff_prover]
fn check_field(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_words7();
        reveal_strlit("=");
        assert("="@ =~= seq!['=']);
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::FieldDefinition) || nd.children.len() != 2 {
        return None;
    }
    let n0 = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let k1 = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if nd.flag && !word_at(src, nodes, toks, gaps, x, &[0x73, 0x74, 0x61, 0x74, 0x69, 0x63], Ghost(GW { g, w: "static"@ })) {
        return None;
    }
    let s: usize = if nd.flag { x.saturating_add(1) } else { x };
    let (lo_n, mn, _) = match done_at(done, n0) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    if !element_name_exec(kind_at(nodes, n0)) || lo_n != s {
        return None;
    }
    let ki = kind_at(nodes, k1);
    let with_init = !matches!(ki, NodeKind::Absent);
    let q: usize = if with_init {
        let (lo1, h1, lv1) = match done_at(done, k1) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if lv1 < 0 || lo1 != mn.saturating_add(1)
            || !punct_at(src, nodes, toks, gaps, mn, 0x3D, Ghost(GW { g, w: "="@ })) {
            return None;
        }
        h1
    } else {
        if !check_absent(src, nodes, toks, gaps, k1, mn, Ghost(g)) {
            return None;
        }
        mn
    };
    let j = match find_semi(src, nodes, toks, gaps, q, nd.end, Ghost(g)) {
        Some(j) => j,
        None => {
            return None;
        },
    };
    if j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(a.nodes[m as int].children =~= seq![n0 as int, k1 as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].flag == nd.flag);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(x.saturating_add(1) as int == x as int + 1);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, n0 as int, g.cx, 0);
        assert(kd(a, k1 as int) == ki);
        if with_init {
            assert(mn.saturating_add(1) as int == mn as int + 1);
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, k1 as int, g.cx, 1);
            assert(is_assign_expr(a, k1 as int));
        }
        lemma_field_done(a, g.ts, g.cx, m as int, n0 as int, k1 as int, x as int, mn as int, q as int, j as int, with_init);
    }
    Some((x, j, -100))
}

/// The one child of node `m` is checked in `c0`.
pub open spec fn cx_kid1(a: AstV, cxs: Seq<Cx5>, m: int, c0: Ctx) -> bool {
    0 <= m < a.nodes.len() && a.nodes[m].children.len() == 1 && 0 <= a.nodes[m].children[0]
        < cxs.len() && cx_of(cxs[a.nodes[m].children[0]]) == c0
}

/// The one child of node `m` is checked in `c0`.
fn kids_cx1(nodes: &[Node], cxs: &[Cx5], m: usize, c0: &Cx5) -> (r: bool)
    requires
        m < nodes.len(),
        cxs.len() == nodes.len(),
        ast_wf(arena_of(nodes@)),
    ensures
        r ==> cx_kid1(arena_of(nodes@), cxs@, m as int, cx_of(*c0)),
{
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    if nd.children.len() != 1 {
        return false;
    }
    let a0 = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return false;
        },
    };
    match cxs.get(a0) {
        Some(x) => cx_eq(x, c0),
        None => false,
    }
}

/// §15.7 `ClassStaticBlock : static { ClassStaticBlockBody }`.
#[verifier::spinoff_prover]
proof fn lemma_static_block_done(a: AstV, ts: Stream, cx: Ctx, m: int, c: int, x: int, j: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= c < m,
        a.nodes[m].kind == NodeKind::ClassStaticBlock,
        a.nodes[m].children =~= seq![c],
        is_kw(ts, x, "static"@),
        kd(a, c) == NodeKind::FunctionBody,
        node_done(
            a,
            ts,
            c,
            Ctx { yield_: false, await_: true, in_: true, return_: false, deflt: false },
            x + 1,
            j,
        ),
        0 <= x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == c);
    assert(dc(
        a,
        ts,
        m,
        c,
        Ctx { yield_: false, await_: true, in_: true, return_: false, deflt: false },
        x + 1,
        j,
    ));
    assert(d_func(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §15.7 `ClassStaticBlock`.
#[verifier::spinoff_prover]
fn check_static_block(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        0 <= m < done.cxs@.len(),
        cx_of(done.cxs@[m as int]) == g.cx,
        cx_kid1(
            arena_of(nodes@),
            done.cxs@,
            m as int,
            Ctx { yield_: false, await_: true, in_: true, return_: false, deflt: false },
        ),
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
    proof {
        lemma_words7();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::ClassStaticBlock) || nd.children.len() != 1 {
        return None;
    }
    let c = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let (lo_c, j, _) = match done_at(done, c) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    if !word_at(src, nodes, toks, gaps, x, &[0x73, 0x74, 0x61, 0x74, 0x69, 0x63], Ghost(GW { g, w: "static"@ }))
        || !matches!(kind_at(nodes, c), NodeKind::FunctionBody) || lo_c != x.saturating_add(1)
        || !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get_at(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int);
        assert(kd(a, c as int) == NodeKind::FunctionBody);
        lemma_static_block_done(a, g.ts, g.cx, m as int, c as int, x as int, j as int);
    }
    Some((x, j, -100))
}

/// A class element before a list (§15.7 `ClassElementList`).
#[verifier::spinoff_prover]
proof fn lemma_dclass_child(
    a: AstV,
    ts: Stream,
    bound: int,
    ks: Seq<int>,
    k: int,
    cx: Ctx,
    i: int,
    m: int,
    j: int,
)
    requires
        0 <= k < ks.len(),
        ed(a, ts, ks[k], i) == m,
        dc(a, ts, bound, ks[k], cx, i, m),
        dclass(a, ts, bound, ks, k + 1, cx, m, j),
    ensures
        dclass(a, ts, bound, ks, k, cx, i, j),
{
}

/// A `;` before a list (§15.7 `ClassElement : ;`).
#[verifier::spinoff_prover]
proof fn lemma_dclass_skip(a: AstV, ts: Stream, bound: int, ks: Seq<int>, k: int, cx: Ctx, i: int, j: int)
    requires
        i < j,
        is_p(ts, i, ";"@),
        dclass(a, ts, bound, ks, k, cx, i + 1, j),
    ensures
        dclass(a, ts, bound, ks, k, cx, i, j),
{
}

/// §15.7 `ClassBody : { ClassElementList? }`.
#[verifier::spinoff_prover]
proof fn lemma_class_body_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int, e: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= x,
        x + 1 <= e < tn(ts),
        a.nodes[m].kind == NodeKind::ClassBody,
        forall|k: int|
            0 <= k < a.nodes[m].children.len() ==> kd(a, #[trigger] a.nodes[m].children[k])
                == NodeKind::MethodDefinition || kd(a, a.nodes[m].children[k])
                == NodeKind::FieldDefinition || kd(a, a.nodes[m].children[k])
                == NodeKind::ClassStaticBlock,
        dclass(a, ts, m, a.nodes[m].children, 0, cx, x + 1, e),
        is_p(ts, x, "{"@),
        is_p(ts, e, "}"@),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[e].end,
    ensures
        node_done(a, ts, m, cx, x, e + 1),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, e + 1));
    assert(d_func(a, ts, m, cx, x, e + 1));
    lemma_ed_of(a, ts, m, x, e + 1);
}

/// §15.7 `ClassBody`.
#[verifier::spinoff_prover]
fn check_class_body(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_brace_text();
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::ClassBody) {
        return None;
    }
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !punct_at(src, nodes, toks, gaps, x, 0x7B, Ghost(GW { g, w: "{"@ })) {
        return None;
    }
    let start = x.saturating_add(1);
    let len = nd.children.len();
    // Where the list ends: after the last element and any `;` that follow it.
    let mut close: usize = if len == 0 {
        start
    } else {
        let last = match kid_of(nodes, m, len.saturating_sub(1)) {
            Some(c) => c,
            None => {
                return None;
            },
        };
        match done_at(done, last) {
            Some((_, h, _)) => h,
            None => {
                return None;
            },
        }
    };
    let ghost a = arena_of(nodes@);
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children.len() == len);
    }
    if close > toks.len() || close < start {
        return None;
    }
    let ghost close0 = close;
    loop
        invariant
            close <= toks.len(),
            close0 <= close,
            env_ok(src@, nodes@, toks@, gaps@, g.ts),
            cps(";"@) =~= seq![0x3Bu32],
        decreases toks.len() - close,
    {
        if close < toks.len() && punct_at(src, nodes, toks, gaps, close, 0x3B, Ghost(GW { g, w: ";"@ })) {
            close = close.saturating_add(1);
        } else {
            break;
        }
    }
    if close > toks.len() || !punct_at(src, nodes, toks, gaps, close, 0x7D, Ghost(GW { g, w: "}"@ }))
        || !end_ok(src, nodes, toks, gaps, nd.end, close.saturating_add(1), Ghost(g)) {
        return None;
    }
    // Backwards: each element ends where the rest starts, or a `;` is skipped.
    let mut k = len;
    let mut pos = close;
    proof {
        reveal_with_fuel(dclass, 2);
        assert(dclass(a, g.ts, m as int, a.nodes[m as int].children, len as int, g.cx, close as int, close as int));
    }
    while k > 0 || pos > start
        invariant
            m < nodes.len(),
            nodes@.len() == nodes.len(),
            nd == &nodes@[m as int],
            a == arena_of(nodes@),
            len == nd.children.len(),
            len == a.nodes[m as int].children.len(),
            k <= len,
            start <= pos,
            pos <= close,
            close < toks.len(),
            cps(";"@) =~= seq![0x3Bu32],
            tn(g.ts) == toks.len(),
            ast_wf(a),
            env_ok(src@, nodes@, toks@, gaps@, g.ts),
            inv(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
            cx_ok(a, done.cxs@, m as int, g.cx),
            dclass(a, g.ts, m as int, a.nodes[m as int].children, k as int, g.cx, pos as int, close as int),
            forall|q: int|
                k <= q < len ==> (kd(a, #[trigger] a.nodes[m as int].children[q]) == NodeKind::MethodDefinition
                    || kd(a, a.nodes[m as int].children[q]) == NodeKind::FieldDefinition
                    || kd(a, a.nodes[m as int].children[q]) == NodeKind::ClassStaticBlock),
        decreases pos,
    {
        let ghost ks = a.nodes[m as int].children;
        let child_ends_here = if k > 0 {
            match kid_of(nodes, m, k.saturating_sub(1)) {
                Some(c) => match done_at(done, c) {
                    Some((_, h, _)) => h == pos,
                    None => false,
                },
                None => false,
            }
        } else {
            false
        };
        if child_ends_here {
            let c = match kid_of(nodes, m, k.saturating_sub(1)) {
                Some(c) => c,
                None => {
                    return None;
                },
            };
            let (lo_c, hi_c, _) = match done_at(done, c) {
                Some(r) => r,
                None => {
                    return None;
                },
            };
            let _ = hi_c;
            let kc = kind_at(nodes, c);
            if !matches!(
                kc,
                NodeKind::MethodDefinition | NodeKind::FieldDefinition | NodeKind::ClassStaticBlock
            ) || lo_c < start {
                return None;
            }
            proof {
                assert(k >= 1);
                assert(k.saturating_sub(1) as int == k as int - 1);
                lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, k as int - 1);
                assert(kd(a, c as int) == kc);
                assert(ed(a, g.ts, c as int, lo_c as int) == hi_c as int);
                assert(dc(a, g.ts, m as int, c as int, g.cx, lo_c as int, hi_c as int));
                lemma_dclass_child(a, g.ts, m as int, ks, k as int - 1, g.cx, lo_c as int, hi_c as int, close as int);
            }
            pos = lo_c;
            k = k.saturating_sub(1);
        } else {
            if pos <= start || pos < 1 {
                return None;
            }
            let semi_before = pos.saturating_sub(1);
            if !punct_at(src, nodes, toks, gaps, semi_before, 0x3B, Ghost(GW { g, w: ";"@ })) {
                return None;
            }
            proof {
                assert(semi_before as int == pos as int - 1);
                lemma_dclass_skip(a, g.ts, m as int, ks, k as int, g.cx, pos as int - 1, close as int);
            }
            pos = semi_before;
        }
    }
    proof {
        assert(k == 0);
        assert(pos == start);
        assert(start as int == x as int + 1);
        assert(forall|q: int|
            0 <= q < len ==> (kd(a, #[trigger] a.nodes[m as int].children[q]) == NodeKind::MethodDefinition
                || kd(a, a.nodes[m as int].children[q]) == NodeKind::FieldDefinition
                || kd(a, a.nodes[m as int].children[q]) == NodeKind::ClassStaticBlock));
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(close.saturating_add(1) as int == close as int + 1);
        lemma_class_body_done(a, g.ts, g.cx, m as int, x as int, close as int);
    }
    Some((x, close.saturating_add(1), -100))
}

/// §15.7 `class Name? ClassHeritage? ClassBody`.
#[verifier::spinoff_prover]
#[verifier::rlimit(150)]
proof fn lemma_class_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    k0: int,
    k1: int,
    k2: int,
    is_expr: bool,
    x: int,
    mn: int,
    h: int,
    j: int,
)
    requires
        toks_wf(ts),
        !cx.deflt,
        0 <= m < a.nodes.len(),
        0 <= k0 < m,
        0 <= k1 < m,
        0 <= k2 < m,
        a.nodes[m].kind == (if is_expr {
            NodeKind::ClassExpression
        } else {
            NodeKind::ClassDeclaration
        }),
        a.nodes[m].children =~= seq![k0, k1, k2],
        is_kw(ts, x, "class"@),
        kd(a, k2) == NodeKind::ClassBody,
        if kd(a, k0) == NodeKind::Absent {
            is_expr && d(a, ts, k0, cx, x + 1, x + 1) && mn == x + 1 && ed(a, ts, k0, x + 1) == mn
        } else {
            kd(a, k0) == NodeKind::BindingIdentifier && node_done(a, ts, k0, cx, x + 1, mn)
        },
        if kd(a, k1) == NodeKind::Absent {
            d(a, ts, k1, cx, mn, mn) && ed(a, ts, k1, mn) == mn && h == mn
        } else {
            is_lhs_expr(a, k1) && is_kw(ts, mn, "extends"@) && node_done(a, ts, k1, cx, mn + 1, h)
        },
        node_done(a, ts, k2, cx, h, j),
        0 <= x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == (if is_expr {
            17int
        } else {
            -100int
        }),
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == k0);
    assert(a.nodes[m].children[1] == k1);
    assert(a.nodes[m].children[2] == k2);
    assert(dc(a, ts, m, k0, cx, x + 1, mn));
    let hs = if kd(a, k1) == NodeKind::Absent {
        mn
    } else {
        mn + 1
    };
    assert(dc(a, ts, m, k1, cx, hs, h));
    assert(dc(a, ts, m, k2, cx, h, j));
    assert(d_class(a, ts, m, cx, x, j, is_expr));
    assert(d_func(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// What `check_class` reads: the node and whether it is an expression.
pub struct ClassShape {
    /// The node.
    pub m: usize,
    /// A `ClassExpression` (else a `ClassDeclaration`).
    pub is_expr: bool,
}

/// §15.7 `ClassDeclaration`, `ClassExpression`.
#[verifier::spinoff_prover]
fn check_class(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    sh: &ClassShape,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<(usize, usize, i32)>)
    requires
        sh.m < nodes.len(),
        !g.cx.deflt,
        nodes@[sh.m as int].kind == (if sh.is_expr {
            NodeKind::ClassExpression
        } else {
            NodeKind::ClassDeclaration
        }),
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, sh.m as int),
        cx_ok(arena_of(nodes@), done.cxs@, sh.m as int, g.cx),
    ensures
        match r {
            Some((l0, h0, l)) => node_done(
                arena_of(nodes@),
                g.ts,
                sh.m as int,
                g.cx,
                l0 as int,
                h0 as int,
            ) && l as int == lvl(arena_of(nodes@), sh.m as int),
            None => true,
        },
{
    let m = sh.m;
    proof {
        lemma_words7();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if nd.children.len() != 3 {
        return None;
    }
    let k0 = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let k1 = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let k2 = match kid_of(nodes, m, 2) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !word_at(src, nodes, toks, gaps, x, &[0x63, 0x6C, 0x61, 0x73, 0x73], Ghost(GW { g, w: "class"@ })) {
        return None;
    }
    let x1 = x.saturating_add(1);
    let kn = kind_at(nodes, k0);
    let mn: usize = if matches!(kn, NodeKind::Absent) {
        if !sh.is_expr || !check_absent(src, nodes, toks, gaps, k0, x1, Ghost(g)) {
            return None;
        }
        x1
    } else {
        let (lo_n, hi_n, _) = match done_at(done, k0) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if !matches!(kn, NodeKind::BindingIdentifier) || lo_n != x1 {
            return None;
        }
        hi_n
    };
    let kh = kind_at(nodes, k1);
    let h: usize = if matches!(kh, NodeKind::Absent) {
        if !check_absent(src, nodes, toks, gaps, k1, mn, Ghost(g)) {
            return None;
        }
        mn
    } else {
        let (lo_h, hi_h, lv_h) = match done_at(done, k1) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if lv_h < 14 || lo_h != mn.saturating_add(1)
            || !word_at(src, nodes, toks, gaps, mn, &[0x65, 0x78, 0x74, 0x65, 0x6E, 0x64, 0x73], Ghost(GW { g, w: "extends"@ })) {
            return None;
        }
        hi_h
    };
    let (lo_b, j, _) = match done_at(done, k2) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    if !matches!(kind_at(nodes, k2), NodeKind::ClassBody) || lo_b != h
        || !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x1 as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![k0 as int, k1 as int, k2 as int]) by {
            assert(a.nodes[m as int].children.len() == 3);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(kd(a, k0 as int) == kn);
        assert(kd(a, k1 as int) == kh);
        assert(kd(a, k2 as int) == NodeKind::ClassBody);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, k2 as int, g.cx, 2);
        if !matches!(kn, NodeKind::Absent) {
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, k0 as int, g.cx, 0);
        }
        if !matches!(kh, NodeKind::Absent) {
            assert(mn.saturating_add(1) as int == mn as int + 1);
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, k1 as int, g.cx, 1);
            assert(is_lhs_expr(a, k1 as int));
        }
        lemma_class_done(a, g.ts, g.cx, m as int, k0 as int, k1 as int, k2 as int, sh.is_expr, x as int, mn as int, h as int, j as int);
    }
    let l: i32 = if sh.is_expr { 17 } else { -100 };
    Some((x, j, l))
}

// ---------------------------------------------------------------------
// Template literals (§13.2.8) and tagged templates (§13.3.11).
// ---------------------------------------------------------------------

/// §13.2.8 a `TemplateElement`: one template token.
#[verifier::spinoff_prover]
fn check_template_element(
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
    proof {
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::TemplateElement) || !nd.children.is_empty() {
        return None;
    }
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
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
    if !matches!(t.kind, TokKind::Template(_)) || t.end != nd.end {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(x.saturating_add(1) as int == x as int + 1);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].children.len() == 0);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        assert(g.ts.toks[x as int].end == t.end as int);
        assert(g.ts.toks[x as int].kind == t.kind);
        assert(g.ts.toks[x as int].start < g.ts.toks[x as int].end);
        assert(span_ok(a, g.ts, m as int, x as int, x as int + 1));
        assert(d_expr_lhs(a, g.ts, m as int, g.cx, x as int, x as int + 1));
        lemma_ed_of(a, g.ts, m as int, x as int, x as int + 1);
    }
    Some((x, x.saturating_add(1), -100))
}

/// The last component of a template.
#[verifier::spinoff_prover]
proof fn lemma_dtemplate_last(a: AstV, ts: Stream, bound: int, ks: Seq<int>, k: int, cx: Ctx, i: int, j: int)
    requires
        0 <= k,
        k + 1 == ks.len(),
        j == i + 1,
        kd(a, ks[k]) == NodeKind::TemplateElement,
        dc(a, ts, bound, ks[k], cx, i, j),
        if k == 0 {
            is_kind(ts, i, TokKind::Template(TemplateKind::NoSubstitution))
        } else {
            is_kind(ts, i, TokKind::Template(TemplateKind::Tail))
        },
    ensures
        dtemplate(a, ts, bound, ks, k, cx, i, j),
{
}

/// A component before an expression and the rest of a template.
#[verifier::spinoff_prover]
proof fn lemma_dtemplate_step(
    a: AstV,
    ts: Stream,
    bound: int,
    ks: Seq<int>,
    k: int,
    cx: Ctx,
    i: int,
    e: int,
    j: int,
)
    requires
        0 <= k,
        k + 1 < ks.len(),
        kd(a, ks[k]) == NodeKind::TemplateElement,
        dc(a, ts, bound, ks[k], cx, i, i + 1),
        if k == 0 {
            is_kind(ts, i, TokKind::Template(TemplateKind::Head))
        } else {
            is_kind(ts, i, TokKind::Template(TemplateKind::Middle))
        },
        lvl(a, ks[k + 1]) >= -1,
        dc(a, ts, bound, ks[k + 1], cx, i + 1, e),
        ed(a, ts, ks[k + 1], i + 1) == e,
        dtemplate(a, ts, bound, ks, k + 2, cx, e, j),
    ensures
        dtemplate(a, ts, bound, ks, k, cx, i, j),
{
}

/// §13.2.8 `TemplateLiteral`.
#[verifier::spinoff_prover]
proof fn lemma_template_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int, j: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        a.nodes[m].kind == NodeKind::TemplateLiteral,
        dtemplate(a, ts, m, a.nodes[m].children, 0, cx_in(cx, true), x, j),
        0 <= x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == 17,
{
    assert(span_ok(a, ts, m, x, j));
    assert(d_expr_lhs(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §13.2.8 `TemplateLiteral`: elements and substitutions alternate.
#[verifier::spinoff_prover]
fn check_template(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok_t(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    let ghost cxt = cx_in(g.cx, true);
    proof {
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let len = nd.children.len();
    if !matches!(nd.kind, NodeKind::TemplateLiteral) || len == 0 || len % 2 == 0 {
        return None;
    }
    let ghost a = arena_of(nodes@);
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children.len() == len);
    }
    let last_ix = len.saturating_sub(1);
    let last = match kid_of(nodes, m, last_ix) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let (lo_l, hi_l, _) = match done_at(done, last) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let kl = kind_at(nodes, last);
    let tk = match toks.get(lo_l) {
        Some(t) => t,
        None => {
            return None;
        },
    };
    proof {
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, lo_l as int);
        assert(tk == &toks@[lo_l as int]);
    }
    let last_kind_ok = if last_ix == 0 {
        matches!(tk.kind, TokKind::Template(TemplateKind::NoSubstitution))
    } else {
        matches!(tk.kind, TokKind::Template(TemplateKind::Tail))
    };
    if !matches!(kl, NodeKind::TemplateElement) || !last_kind_ok || hi_l != lo_l.saturating_add(1) {
        return None;
    }
    proof {
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, last as int, cxt, last_ix as int);
        assert(lo_l.saturating_add(1) as int == lo_l as int + 1);
        assert(kd(a, last as int) == kl);
        assert(lo_l < toks.len());
        let ks = a.nodes[m as int].children;
        assert(dc(a, g.ts, m as int, last as int, cxt, lo_l as int, hi_l as int));
        assert(g.ts.toks[lo_l as int].kind == tk.kind);
        lemma_dtemplate_last(a, g.ts, m as int, ks, last_ix as int, cxt, lo_l as int, hi_l as int);
    }
    let end = hi_l;
    let mut k = last_ix;
    let mut pos = lo_l;
    while k > 0
        invariant
            m < nodes.len(),
            nodes@.len() == nodes.len(),
            nd == &nodes@[m as int],
            a == arena_of(nodes@),
            len == nd.children.len(),
            len == a.nodes[m as int].children.len(),
            len % 2 == 1,
            k < len,
            k % 2 == 0,
            end <= toks.len(),
            pos < end,
            tn(g.ts) == toks.len(),
            ast_wf(a),
            env_ok(src@, nodes@, toks@, gaps@, g.ts),
            inv(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
            kids_ok(a, done.cxs@, m as int, cxt),
            dtemplate(a, g.ts, m as int, a.nodes[m as int].children, k as int, cxt, pos as int, end as int),
        decreases k,
    {
        let ix_e = k.saturating_sub(2);
        let ix_x = k.saturating_sub(1);
        let el = match kid_of(nodes, m, ix_e) {
            Some(c) => c,
            None => {
                return None;
            },
        };
        let ex = match kid_of(nodes, m, ix_x) {
            Some(c) => c,
            None => {
                return None;
            },
        };
        let (lo_e, hi_e, _) = match done_at(done, el) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        let (lo_x, hi_x, lv_x) = match done_at(done, ex) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        let tt = match toks.get(lo_e) {
            Some(t) => t,
            None => {
                return None;
            },
        };
        proof {
            lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, lo_e as int);
            assert(tt == &toks@[lo_e as int]);
        }
        let el_kind_ok = if ix_e == 0 {
            matches!(tt.kind, TokKind::Template(TemplateKind::Head))
        } else {
            matches!(tt.kind, TokKind::Template(TemplateKind::Middle))
        };
        if !matches!(kind_at(nodes, el), NodeKind::TemplateElement) || !el_kind_ok
            || hi_e != lo_e.saturating_add(1) || lo_x != hi_e || hi_x != pos || lv_x < -1 {
            return None;
        }
        proof {
            assert(k >= 2);
            assert(ix_e as int == k as int - 2);
            assert(ix_x as int == k as int - 1);
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, el as int, cxt, k as int - 2);
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, ex as int, cxt, k as int - 1);
            assert(lo_e.saturating_add(1) as int == lo_e as int + 1);
            assert(kd(a, el as int) == NodeKind::TemplateElement);
            assert(lvl(a, ex as int) >= -1);
            assert(lo_e < toks.len());
            let ks = a.nodes[m as int].children;
            assert(g.ts.toks[lo_e as int].kind == tt.kind);
            assert(dc(a, g.ts, m as int, el as int, cxt, lo_e as int, lo_e as int + 1));
            assert(dc(a, g.ts, m as int, ex as int, cxt, lo_e as int + 1, pos as int));
            assert(ed(a, g.ts, ex as int, lo_e as int + 1) == pos as int);
            lemma_dtemplate_step(a, g.ts, m as int, ks, k as int - 2, cxt, lo_e as int, pos as int, end as int);
        }
        pos = lo_e;
        k = k.saturating_sub(2);
    }
    let x = pos;
    if !end_ok(src, nodes, toks, gaps, nd.end, end, Ghost(g)) {
        return None;
    }
    let first = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if first != x || end <= x {
        return None;
    }
    proof {
        assert(k == 0);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_template_done(a, g.ts, g.cx, m as int, x as int, end as int);
    }
    Some((x, end, 17))
}

/// §13.3.11 `tag TemplateLiteral`.
#[verifier::spinoff_prover]
proof fn lemma_tagged_done(a: AstV, ts: Stream, cx: Ctx, m: int, t: int, l: int, x: int, mt: int, j: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= t < m,
        0 <= l < m,
        a.nodes[m].kind == NodeKind::TaggedTemplate,
        a.nodes[m].children =~= seq![t, l],
        is_member_or_call(a, t),
        kd(a, l) == NodeKind::TemplateLiteral,
        node_done(a, ts, t, cx, x, mt),
        node_done(a, ts, l, cx, mt, j),
        0 <= x < j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == (if lvl(a, t) == 17 {
            17int
        } else {
            15int
        }),
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == t);
    assert(a.nodes[m].children[1] == l);
    assert(dc(a, ts, m, t, cx, x, mt));
    assert(dc(a, ts, m, l, cx, mt, j));
    assert(d_expr_lhs(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §13.3.11 `TaggedTemplate`.
#[verifier::spinoff_prover]
fn check_tagged(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::TaggedTemplate) || nd.children.len() != 2 {
        return None;
    }
    let t = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let l = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let (lo_t, mt, lv_t) = match done_at(done, t) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let (lo_l, j, _) = match done_at(done, l) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    if lo_t != x || !(lv_t == 17 || lv_t == 15) || lo_l != mt
        || !matches!(kind_at(nodes, l), NodeKind::TemplateLiteral)
        || !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(a.nodes[m as int].children =~= seq![t as int, l as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, t as int, g.cx, 0);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, l as int, g.cx, 1);
        assert(kd(a, l as int) == NodeKind::TemplateLiteral);
        assert(is_member_or_call(a, t as int));
        lemma_tagged_done(a, g.ts, g.cx, m as int, t as int, l as int, x as int, mt as int, j as int);
    }
    let own: i32 = if lv_t == 17 { 17 } else { 15 };
    Some((x, j, own))
}

// ---------------------------------------------------------------------
// `object.#name` (§13.3.2).
// ---------------------------------------------------------------------

/// §13.3.2 `MemberExpression . PrivateIdentifier`.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
proof fn lemma_member_private_done(a: AstV, ts: Stream, cx: Ctx, m: int, o: int, p: int, x: int, mo: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= o < m,
        0 <= p < m,
        a.nodes[m].kind == NodeKind::MemberExpression,
        a.nodes[m].op == Op::PrivateDot,
        a.nodes[m].children =~= seq![o, p],
        is_member_or_call(a, o),
        kd(a, p) == NodeKind::PrivateIdentifier,
        node_done(a, ts, o, cx, x, mo),
        is_p(ts, mo, "."@),
        node_done(a, ts, p, cx, mo + 1, mo + 2),
        0 <= x,
        mo + 2 <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[mo + 1].end,
    ensures
        node_done(a, ts, m, cx, x, mo + 2),
        lvl(a, m) == (if lvl(a, o) == 17 {
            17int
        } else {
            15int
        }),
{
    assert(span_ok(a, ts, m, x, mo + 2));
    assert(a.nodes[m].children[0] == o);
    assert(a.nodes[m].children[1] == p);
    assert(dc(a, ts, m, o, cx, x, mo));
    assert(dc(a, ts, m, p, cx, mo + 1, mo + 2));
    assert(d_expr_lhs(a, ts, m, cx, x, mo + 2));
    lemma_ed_of(a, ts, m, x, mo + 2);
}

/// §13.3.2 `object . #name`.
#[verifier::spinoff_prover]
fn check_member_private(
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
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
        cx_ok(arena_of(nodes@), done.cxs@, m as int, g.cx),
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
    proof {
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::MemberExpression) || !matches!(nd.op, Op::PrivateDot)
        || nd.children.len() != 2 {
        return None;
    }
    let o = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let p = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let (lo_o, mo, lv_o) = match done_at(done, o) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let (lo_p, hi_p, _) = match done_at(done, p) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let mo1 = mo.saturating_add(1);
    if lo_o != x || !(lv_o == 17 || lv_o == 15) || !matches!(kind_at(nodes, p), NodeKind::PrivateIdentifier)
        || lo_p != mo1 || hi_p != mo.saturating_add(2)
        || !punct_at(src, nodes, toks, gaps, mo, 0x2E, Ghost(GW { g, w: "."@ }))
        || !end_ok(src, nodes, toks, gaps, nd.end, hi_p, Ghost(g)) {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(mo1 as int == mo as int + 1);
        assert(a.nodes[m as int].children =~= seq![o as int, p as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
        }
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].op == nd.op);
        assert(a.nodes[m as int].start == nd.start as int);
        assert(a.nodes[m as int].end == nd.end as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, o as int, g.cx, 0);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, p as int, g.cx, 1);
        assert(kd(a, p as int) == NodeKind::PrivateIdentifier);
        assert(is_member_or_call(a, o as int));
        assert(hi_p as int == mo as int + 2);
        lemma_env_tok(src@, nodes@, toks@, gaps@, g.ts, hi_p as int - 1);
        assert(g.ts.toks[mo as int + 1].end == nd.end as int);
        lemma_member_private_done(a, g.ts, g.cx, m as int, o as int, p as int, x as int, mo as int);
    }
    let own: i32 = if lv_o == 17 { 17 } else { 15 };
    Some((x, hi_p, own))
}

} // verus!
