//! Proofs that what the parser builds derives from the tokens by the
//! grammar of [`crate::spec`]: the first pieces of "an `Ok` arena satisfies
//! [`is_valid_parse`]" (item 7.3, second half).
//!
//! Two kinds of statement are proven here, neither about the whole parser:
//!
//! - **Rule lemmas** (`lemma_*`): for one production, the shape the parser builds
//!   (the node's kind, children and span, and the tokens it consumed) is
//!   derived by [`d`]. They are the steps of an induction over the arena that
//!   the parser's code would discharge production by production.
//! - **Checked leaves** ([`check_leaf`]): an executable check, on the source
//!   text and the tokens as the parser read them, that a leaf node is derived
//!   by [`d`] at a token. It is relative to the tokens: that they are what the
//!   lexer's specification says ([`lexes_as`]) is the lexer's contract
//!   (item 7.2), which the executable lexer does not meet yet.

use crate::ast::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// A leaf node `n` (no children) of one of the kinds below, at token `i`, whose
/// span is the token's and whose token has the kind the production wants, is
/// derived: `d(n, i, i + 1)`. §12.7 `IdentifierName`, `PrivateIdentifier`,
/// §13.2.3 `NumericLiteral`, `StringLiteral`, §13.2.7
/// `RegularExpressionLiteral`, §13.2.8 `TemplateElement`.
pub proof fn lemma_leaf_literal(a: AstV, ts: Stream, n: int, cx: Ctx, i: int)
    requires
        0 <= n < a.nodes.len(),
        0 <= i < tn(ts),
        a.nodes[n].children.len() == 0,
        a.nodes[n].start == ts.toks[i].start,
        a.nodes[n].end == ts.toks[i].end,
        ts.toks[i].start < ts.toks[i].end,
        match a.nodes[n].kind {
            NodeKind::IdentifierName => ts.toks[i].kind == TokKind::IdentifierName,
            NodeKind::PrivateIdentifier => ts.toks[i].kind == TokKind::PrivateIdentifier,
            NodeKind::NumericLiteral => ts.toks[i].kind == TokKind::NumericLiteral,
            NodeKind::StringLiteral => ts.toks[i].kind == TokKind::StringLiteral,
            NodeKind::RegularExpressionLiteral => ts.toks[i].kind
                == TokKind::RegularExpressionLiteral,
            NodeKind::TemplateElement => ts.toks[i].kind is Template,
            _ => false,
        },
    ensures
        d(a, ts, n, cx, i, i + 1),
{
    assert(span_ok(a, ts, n, i, i + 1));
    assert(d_expr_lhs(a, ts, n, cx, i, i + 1));
    assert(d_expr(a, ts, n, cx, i, i + 1));
}

/// §13.6 to §13.13 a binary operator node `n` (kind `k`, operator `op`) with
/// children `l` and `r`: `l` derives `ts[i..m)`, the operator is the token `m`,
/// `r` derives `ts[m + 1..j)`, the operands bind tightly enough
/// ([`binary_operands_ok`]), and `in` only where `[+In]`. Then `n` derives
/// `ts[i..j)`.
pub proof fn lemma_binary_derives(
    a: AstV,
    ts: Stream,
    n: int,
    cx: Ctx,
    i: int,
    m: int,
    j: int,
    l: int,
    r: int,
)
    requires
        0 <= n < a.nodes.len(),
        0 <= i < m,
        m < j <= tn(ts),
        a.nodes[n].children =~= seq![l, r],
        0 <= l < n,
        0 <= r < n,
        bin_op_ok(a.nodes[n].kind, a.nodes[n].op),
        a.nodes[n].op == Op::In ==> cx.in_,
        binary_operands_ok(a, a.nodes[n].kind, a.nodes[n].op, l, r),
        ed(a, ts, l, i) == m,
        d(a, ts, l, cx, i, m),
        is_op_tok(ts, m, a.nodes[n].op),
        d(a, ts, r, cx, m + 1, j),
        span_ok(a, ts, n, i, j),
    ensures
        d(a, ts, n, cx, i, j),
{
    let k = a.nodes[n].kind;
    assert(a.nodes[n].children[0] == l);
    assert(dc(a, ts, n, l, cx, i, m));
    assert(dc(a, ts, n, r, cx, m + 1, j));
    assert(d_expr(a, ts, n, cx, i, j));
}

/// The arena of `nodes` as the specification reads it (the root is irrelevant to [`d`]).
pub open spec fn nodes_arena(nodes: Seq<Node>) -> AstV {
    AstV { nodes: nodes.map_values(|nd: Node| nd@), root: 0 }
}

/// What the executable parser knows of a token that the leaf productions read:
/// its kind and its span (the rest of [`Tok`] is the lexer's).
pub struct ETok {
    /// The lexer's kind.
    pub kind: TokKind,
    /// The index of the first code point.
    pub start: usize,
    /// One past the last code point.
    pub end: usize,
}

/// The executable token `e` is the specification's token `t`, as far as
/// [`ETok`] goes.
pub open spec fn etok_matches(e: ETok, t: Tok) -> bool {
    e.kind == t.kind && e.start as int == t.start && e.end as int == t.end
}

/// Checks that node `n` of `nodes` is a literal or name leaf derived by the
/// grammar at token `i` of `toks`: it has no children, its span is the token's,
/// and the token is of the kind of the production. If so, [`d`] says so, in
/// every context. `ts` is the specification's view of the tokens: that the
/// executable tokens are the specification's (`etok_matches`) is the
/// assumption, since the executable lexer does not yet meet the lexer's
/// contract (item 7.2).
pub fn check_leaf(nodes: &Vec<Node>, toks: &Vec<ETok>, n: usize, i: usize, Ghost(ts): Ghost<Stream>) -> (ok: bool)
    requires
        toks@.len() == tn(ts),
        forall|k: int| 0 <= k < toks@.len() ==> etok_matches(toks@[k], #[trigger] ts.toks[k]),
    ensures
        ok ==> (0 <= n < nodes@.len() && 0 <= i < tn(ts) && forall|cx: Ctx|
            #[trigger] d(nodes_arena(nodes@), ts, n as int, cx, i as int, i as int + 1)),
{
    let nd = match nodes.as_slice().get(n) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    let t = match toks.as_slice().get(i) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    if !nd.children.is_empty() || nd.start != t.start || nd.end != t.end || !(t.start < t.end) {
        return false;
    }
    let kind_ok = match nd.kind {
        NodeKind::IdentifierName => matches!(t.kind, TokKind::IdentifierName),
        NodeKind::PrivateIdentifier => matches!(t.kind, TokKind::PrivateIdentifier),
        NodeKind::NumericLiteral => matches!(t.kind, TokKind::NumericLiteral),
        NodeKind::StringLiteral => matches!(t.kind, TokKind::StringLiteral),
        NodeKind::RegularExpressionLiteral => matches!(t.kind, TokKind::RegularExpressionLiteral),
        NodeKind::TemplateElement => matches!(t.kind, TokKind::Template(_)),
        _ => false,
    };
    if !kind_ok {
        return false;
    }
    proof {
        let a = nodes_arena(nodes@);
        assert(a.nodes[n as int] == nodes@[n as int]@);
        assert(etok_matches(toks@[i as int], ts.toks[i as int]));
        assert forall|cx: Ctx| #[trigger] d(a, ts, n as int, cx, i as int, i as int + 1) by {
            lemma_leaf_literal(a, ts, n as int, cx, i as int);
        }
    }
    true
}

/// §13.1 `IdentifierReference`, `BindingIdentifier`, `LabelIdentifier`: a leaf at
/// an identifier token ([`ident_tok`]).
pub proof fn lemma_leaf_identifier(a: AstV, ts: Stream, n: int, cx: Ctx, i: int)
    requires
        0 <= n < a.nodes.len(),
        0 <= i < tn(ts),
        a.nodes[n].children.len() == 0,
        a.nodes[n].kind == NodeKind::IdentifierReference || a.nodes[n].kind
            == NodeKind::BindingIdentifier || a.nodes[n].kind == NodeKind::LabelIdentifier,
        a.nodes[n].start == ts.toks[i].start,
        a.nodes[n].end == ts.toks[i].end,
        ts.toks[i].start < ts.toks[i].end,
        ident_tok(ts, i, cx),
    ensures
        d(a, ts, n, cx, i, i + 1),
{
    assert(span_ok(a, ts, n, i, i + 1));
    assert(d_expr_lhs(a, ts, n, cx, i, i + 1));
    assert(d_expr(a, ts, n, cx, i, i + 1));
}

/// §13.2.1, §13.2.3 `this`, `null`, `true`, `false`: a leaf at that keyword.
pub proof fn lemma_leaf_keyword(a: AstV, ts: Stream, n: int, cx: Ctx, i: int)
    requires
        0 <= n < a.nodes.len(),
        0 <= i < tn(ts),
        a.nodes[n].children.len() == 0,
        a.nodes[n].start == ts.toks[i].start,
        a.nodes[n].end == ts.toks[i].end,
        ts.toks[i].start < ts.toks[i].end,
        match a.nodes[n].kind {
            NodeKind::ThisExpression => is_kw(ts, i, "this"@),
            NodeKind::NullLiteral => is_kw(ts, i, "null"@),
            NodeKind::BooleanLiteral => is_kw(ts, i, "true"@) || is_kw(ts, i, "false"@),
            _ => false,
        },
    ensures
        d(a, ts, n, cx, i, i + 1),
{
    assert(span_ok(a, ts, n, i, i + 1));
    assert(d_expr_lhs(a, ts, n, cx, i, i + 1));
    assert(d_expr(a, ts, n, cx, i, i + 1));
}

/// §13.5 `UnaryExpression : delete | void | typeof | + | - | ~ | ! UnaryExpression`.
pub proof fn lemma_unary_derives(a: AstV, ts: Stream, n: int, cx: Ctx, i: int, j: int, c: int)
    requires
        0 <= n < a.nodes.len(),
        0 <= i < j <= tn(ts),
        a.nodes[n].kind == NodeKind::UnaryExpression,
        a.nodes[n].children =~= seq![c],
        0 <= c < n,
        is_unary_op(a.nodes[n].op),
        is_op_tok(ts, i, a.nodes[n].op),
        lvl(a, c) >= 12,
        d(a, ts, c, cx, i + 1, j),
        span_ok(a, ts, n, i, j),
    ensures
        d(a, ts, n, cx, i, j),
{
    assert(a.nodes[n].children[0] == c);
    assert(dc(a, ts, n, c, cx, i + 1, j));
    assert(d_expr(a, ts, n, cx, i, j));
}

/// §13.14 `ConditionalExpression : ShortCircuitExpression ? AssignmentExpression :
/// AssignmentExpression`.
#[verifier::spinoff_prover]
pub proof fn lemma_conditional_derives(
    a: AstV,
    ts: Stream,
    n: int,
    cx: Ctx,
    i: int,
    m: int,
    q: int,
    j: int,
    t: int,
    c: int,
    e: int,
)
    requires
        0 <= n < a.nodes.len(),
        0 <= i < m,
        m < q < j <= tn(ts),
        a.nodes[n].kind == NodeKind::ConditionalExpression,
        a.nodes[n].children =~= seq![t, c, e],
        0 <= t < n,
        0 <= c < n,
        0 <= e < n,
        lvl(a, t) >= 1 || kd(a, t) == NodeKind::CoalesceExpression,
        is_assign_expr(a, c),
        is_assign_expr(a, e),
        ed(a, ts, t, i) == m,
        ed(a, ts, c, m + 1) == q,
        d(a, ts, t, cx, i, m),
        is_p(ts, m, "?"@),
        d(a, ts, c, cx_in(cx, true), m + 1, q),
        is_p(ts, q, ":"@),
        d(a, ts, e, cx, q + 1, j),
        span_ok(a, ts, n, i, j),
    ensures
        d(a, ts, n, cx, i, j),
{
    assert(a.nodes[n].children[0] == t);
    assert(a.nodes[n].children[1] == c);
    assert(a.nodes[n].children[2] == e);
    assert(dc(a, ts, n, t, cx, i, m));
    assert(dc(a, ts, n, c, cx_in(cx, true), m + 1, q));
    assert(dc(a, ts, n, e, cx, q + 1, j));
    assert(d_expr(a, ts, n, cx, i, j));
}

/// §13.15 `AssignmentExpression : LeftHandSideExpression AssignmentOperator
/// AssignmentExpression` (and `=` with a destructuring target).
pub proof fn lemma_assignment_derives(
    a: AstV,
    ts: Stream,
    n: int,
    cx: Ctx,
    i: int,
    m: int,
    j: int,
    l: int,
    r: int,
)
    requires
        0 <= n < a.nodes.len(),
        0 <= i < m,
        m < j <= tn(ts),
        a.nodes[n].kind == NodeKind::AssignmentExpression,
        a.nodes[n].children =~= seq![l, r],
        0 <= l < n,
        0 <= r < n,
        is_assign_op(a.nodes[n].op),
        if a.nodes[n].op == Op::Assign {
            is_destructuring_target(a, l)
        } else {
            is_lhs_expr(a, l)
        },
        is_assign_expr(a, r),
        ed(a, ts, l, i) == m,
        d(a, ts, l, cx, i, m),
        is_op_tok(ts, m, a.nodes[n].op),
        d(a, ts, r, cx, m + 1, j),
        span_ok(a, ts, n, i, j),
    ensures
        d(a, ts, n, cx, i, j),
{
    assert(a.nodes[n].children[0] == l);
    assert(dc(a, ts, n, l, cx, i, m));
    assert(dc(a, ts, n, r, cx, m + 1, j));
    assert(d_expr(a, ts, n, cx, i, j));
}

/// §13.2.9 `ParenthesizedExpression : ( Expression )`.
pub proof fn lemma_parenthesized_derives(a: AstV, ts: Stream, n: int, cx: Ctx, i: int, m: int, c: int)
    requires
        0 <= n < a.nodes.len(),
        0 <= i,
        i + 1 < m,
        m < tn(ts),
        a.nodes[n].kind == NodeKind::ParenthesizedExpression,
        a.nodes[n].children =~= seq![c],
        0 <= c < n,
        lvl(a, c) >= -1,
        ed(a, ts, c, i + 1) == m,
        is_p(ts, i, "("@),
        d(a, ts, c, cx_in(cx, true), i + 1, m),
        is_p(ts, m, ")"@),
        span_ok(a, ts, n, i, m + 1),
    ensures
        d(a, ts, n, cx, i, m + 1),
{
    assert(a.nodes[n].children[0] == c);
    assert(dc(a, ts, n, c, cx_in(cx, true), i + 1, m));
    assert(d_expr_lhs(a, ts, n, cx, i, m + 1));
    assert(d_expr(a, ts, n, cx, i, m + 1));
}

/// §13.3.2 `MemberExpression : MemberExpression . IdentifierName`.
pub proof fn lemma_member_dot_derives(
    a: AstV,
    ts: Stream,
    n: int,
    cx: Ctx,
    i: int,
    m: int,
    o: int,
    p: int,
)
    requires
        0 <= n < a.nodes.len(),
        0 <= i < m,
        m + 2 <= tn(ts),
        a.nodes[n].kind == NodeKind::MemberExpression,
        a.nodes[n].op == Op::Dot,
        a.nodes[n].children =~= seq![o, p],
        0 <= o < n,
        0 <= p < n,
        is_member_or_call(a, o),
        kd(a, p) == NodeKind::IdentifierName,
        ed(a, ts, o, i) == m,
        d(a, ts, o, cx, i, m),
        is_p(ts, m, "."@),
        d(a, ts, p, cx, m + 1, m + 2),
        span_ok(a, ts, n, i, m + 2),
    ensures
        d(a, ts, n, cx, i, m + 2),
{
    assert(a.nodes[n].children[0] == o);
    assert(a.nodes[n].children[1] == p);
    assert(dc(a, ts, n, o, cx, i, m));
    assert(dc(a, ts, n, p, cx, m + 1, m + 2));
    assert(d_expr_lhs(a, ts, n, cx, i, m + 2));
    assert(d_expr(a, ts, n, cx, i, m + 2));
}

} // verus!
