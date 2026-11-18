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

} // verus!
