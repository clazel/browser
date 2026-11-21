//! The names the early errors of [`crate::arena_early`] compare, computed over the
//! arena and proven equal to the specification's (item 7.3): BoundNames (§8.2.1) of
//! every node as token indices ([`bound_names_all`]), a Use Strict Directive
//! (`has_use_strict`, §11.2.1, [`use_strict_exec`]), the simple-parameter and
//! duplicate-name rules of function code (`function_early`, §15.1.1,
//! [`function_early_exec`]).
//!
//! A name is kept as the index of the token it is the name of, so a list of names is
//! a `Vec<usize>` and [`names_of`] is the specification's `Seq<Seq<u32>>` of it.

use crate::arena_d::*;
use crate::arena_early::*;
use crate::ast::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// What the executable checks read besides the arena: the source, the tokens, a hint for finding
/// a token from its start, and the BoundNames of every node.
pub struct Tk<'a> {
    /// The source text.
    pub src: &'a [u32],
    /// The tokens the parser consumed.
    pub toks: &'a [DTok],
    /// For a start position, the index of the token that starts there (`usize::MAX` for none).
    pub by_start: &'a [usize],
    /// The BoundNames of each node ([`bn_inv`]).
    pub bn: &'a [Vec<usize>],
}

/// The names of the tokens `xs`.
pub open spec fn names_of(toks: Seq<DTok>, xs: Seq<usize>) -> Seq<Seq<u32>> {
    Seq::new(xs.len(), |i: int| toks[xs[i] as int].name@)
}

/// Every index of `xs` is a token.
pub open spec fn idx_ok(toks: Seq<DTok>, xs: Seq<usize>) -> bool {
    forall|i: int| 0 <= i < xs.len() ==> (#[trigger] xs[i]) < toks.len()
}

/// `bn[j]` is the BoundNames of node `j`, for every node before `m`.
pub open spec fn bn_inv(a: AstV, ts: Stream, toks: Seq<DTok>, bn: Seq<Vec<usize>>, m: int) -> bool {
    forall|j: int|
        0 <= j < m ==> {
            let v = (#[trigger] bn[j])@;
            idx_ok(toks, v) && names_of(toks, v) =~= bound_names(a, ts, j)
        }
}

/// The names of two lists put together.
proof fn lemma_names_add(toks: Seq<DTok>, xs: Seq<usize>, ys: Seq<usize>)
    ensures
        names_of(toks, xs + ys) =~= names_of(toks, xs) + names_of(toks, ys),
{
}

/// `dst` gets the elements of `src` after its own.
fn push_all(dst: &mut Vec<usize>, src: &[usize])
    ensures
        final(dst)@ =~= old(dst)@ + src@,
{
    let len = src.len();
    let mut i: usize = 0;
    while i < len
        invariant
            len == src.len(),
            i <= len,
            dst@ =~= old(dst)@ + src@.subrange(0, i as int),
        decreases len - i,
    {
        match src.get(i) {
            Some(x) => {
                dst.push(*x);
            },
            None => {
                return;
            },
        }
        proof {
            assert(src@.subrange(0, i as int + 1) =~= src@.subrange(0, i as int).push(src@[i as int]));
        }
        i = i.saturating_add(1);
    }
    proof {
        assert(src@.subrange(0, len as int) =~= src@);
    }
}

/// The BoundNames of node `m` with one child: the first, or the last.
pub open spec fn bn_one(a: AstV, ts: Stream, m: int, last: bool) -> Seq<Seq<u32>> {
    let ch = a.nodes[m].children;
    let idx = if last {
        ch.len() - 1
    } else {
        0
    };
    if ch.len() > 0 && 0 <= ch[idx] < m {
        bound_names(a, ts, ch[idx])
    } else {
        Seq::empty()
    }
}

/// The BoundNames of the children `ks[..k]` of node `n`, put together.
pub open spec fn bn_pre(a: AstV, ts: Stream, n: int, ks: Seq<int>, k: int) -> Seq<Seq<u32>>
    decreases k,
{
    if k <= 0 {
        Seq::empty()
    } else {
        bn_pre(a, ts, n, ks, k - 1) + (if 0 <= ks[k - 1] < n {
            bound_names(a, ts, ks[k - 1])
        } else {
            Seq::empty()
        })
    }
}

/// `bound_names_list` is the prefix and what is left.
proof fn lemma_bn_pre(a: AstV, ts: Stream, n: int, ks: Seq<int>, k: int)
    requires
        0 <= k <= ks.len(),
    ensures
        bound_names_list(a, ts, n, ks, 0) =~= bn_pre(a, ts, n, ks, k) + bound_names_list(a, ts, n, ks, k),
    decreases k,
{
    if k > 0 {
        lemma_bn_pre(a, ts, n, ks, k - 1);
        reveal_with_fuel(bound_names_list, 2);
        let here = if 0 <= ks[k - 1] < n {
            bound_names(a, ts, ks[k - 1])
        } else {
            Seq::empty()
        };
        assert(bound_names_list(a, ts, n, ks, k - 1) =~= here + bound_names_list(a, ts, n, ks, k));
        assert(bn_pre(a, ts, n, ks, k) =~= bn_pre(a, ts, n, ks, k - 1) + here);
    }
}

/// The BoundNames of node `m` of a kind with one child.
fn bn_child(
    nodes: &[Node],
    toks: &[DTok],
    bn: &[Vec<usize>],
    m: usize,
    last: bool,
    Ghost(ts): Ghost<Stream>,
) -> (r: Option<Vec<usize>>)
    requires
        m < nodes.len(),
        bn.len() == m,
        ast_wf(arena_of(nodes@)),
        bn_inv(arena_of(nodes@), ts, toks@, bn@, m as int),
    ensures
        match r {
            Some(v) => idx_ok(toks@, v@) && names_of(toks@, v@) =~= bn_one(
                arena_of(nodes@),
                ts,
                m as int,
                last,
            ),
            None => true,
        },
{
    let ghost a = arena_of(nodes@);
    let _ = toks.len();
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children.len() == nd.children.len());
    }
    let len = nd.children.len();
    if len == 0 {
        return Some(Vec::new());
    }
    let idx = if last {
        len.saturating_sub(1)
    } else {
        0
    };
    let c = match nd.children.as_slice().get(idx) {
        Some(c) => *c as usize,
        None => {
            return None;
        },
    };
    proof {
        assert(a.nodes[m as int].children[idx as int] == c as int);
        lemma_child_before(a, m as int, idx as int);
    }
    if c >= m {
        return None;
    }
    let from = match bn.get(c) {
        Some(v) => v,
        None => {
            return None;
        },
    };
    let mut out: Vec<usize> = Vec::new();
    push_all(&mut out, from.as_slice());
    proof {
        assert(bn@[c as int] == from);
        assert(out@ =~= from@);
    }
    Some(out)
}

/// The BoundNames of node `m` of a kind that binds its children's, in order.
fn bn_list(
    nodes: &[Node],
    toks: &[DTok],
    bn: &[Vec<usize>],
    m: usize,
    Ghost(ts): Ghost<Stream>,
) -> (r: Option<Vec<usize>>)
    requires
        m < nodes.len(),
        bn.len() == m,
        ast_wf(arena_of(nodes@)),
        bn_inv(arena_of(nodes@), ts, toks@, bn@, m as int),
    ensures
        match r {
            Some(v) => idx_ok(toks@, v@) && names_of(toks@, v@) =~= bound_names_list(
                arena_of(nodes@),
                ts,
                m as int,
                arena_of(nodes@).nodes[m as int].children,
                0,
            ),
            None => true,
        },
{
    let ghost a = arena_of(nodes@);
    let _ = toks.len();
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let len = nd.children.len();
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children.len() == len);
    }
    let ghost ks = a.nodes[m as int].children;
    let mut out: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < len
        invariant
            k <= len,
            len == nd.children.len(),
            m < nodes.len(),
            bn.len() == m,
            nd == &nodes@[m as int],
            a == arena_of(nodes@),
            ast_wf(a),
            ks == a.nodes[m as int].children,
            len == ks.len(),
            bn_inv(a, ts, toks@, bn@, m as int),
            idx_ok(toks@, out@),
            names_of(toks@, out@) =~= bn_pre(a, ts, m as int, ks, k as int),
        decreases len - k,
    {
        let c = match nd.children.as_slice().get(k) {
            Some(c) => *c as usize,
            None => {
                return None;
            },
        };
        proof {
            assert(a.nodes[m as int].children[k as int] == c as int);
            lemma_child_before(a, m as int, k as int);
        }
        if c >= m {
            return None;
        }
        let from = match bn.get(c) {
            Some(v) => v,
            None => {
                return None;
            },
        };
        let ghost before = out@;
        push_all(&mut out, from.as_slice());
        proof {
            assert(bn@[c as int] == from);
            lemma_names_add(toks@, before, from@);
            assert(bn_pre(a, ts, m as int, ks, k as int + 1) =~= bn_pre(a, ts, m as int, ks, k as int)
                + bound_names(a, ts, c as int));
            assert forall|i: int| 0 <= i < out@.len() implies (#[trigger] out@[i]) < toks.len() by {
                if i < before.len() {
                    assert(out@[i] == before[i]);
                } else {
                    assert(out@[i] == from@[i - before.len()]);
                }
            }
        }
        k = k.saturating_add(1);
    }
    proof {
        lemma_bn_pre(a, ts, m as int, ks, len as int);
        assert(bound_names_list(a, ts, m as int, ks, len as int) =~= Seq::<Seq<u32>>::empty());
    }
    Some(out)
}

/// The BoundNames of the `BindingIdentifier` node `m`.
fn bn_ident(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    by_start: &[usize],
    m: usize,
    Ghost(ts): Ghost<Stream>,
) -> (r: Option<Vec<usize>>)
    requires
        m < nodes.len(),
        ast_wf(arena_of(nodes@)),
        toks_match(src@, toks@, ts),
        starts_inc(ts),
    ensures
        match r {
            Some(v) => idx_ok(toks@, v@) && names_of(toks@, v@) =~= seq![name_of(
                arena_of(nodes@),
                ts,
                m as int,
            )],
            None => true,
        },
{
    let _ = src.len();
    let x = match node_token(nodes, toks, by_start, m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let out: Vec<usize> = vec![x];
    proof {
        let a = arena_of(nodes@);
        assert(dtok_matches(src@, toks@[x as int], ts.toks[x as int]));
        lemma_node_tok_at(a, ts, m as int, x as int);
        assert(a.nodes.len() == nodes@.len());
        assert(out@ =~= seq![x]);
        assert(names_of(toks@, out@) =~= seq![toks@[x as int].name@]);
        assert(name_of(a, ts, m as int) =~= toks@[x as int].name@);
    }
    Some(out)
}

/// The BoundNames of every node, as the tokens that name them.
#[verifier::rlimit(400)]
pub fn bound_names_all(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    by_start: &[usize],
    Ghost(ts): Ghost<Stream>,
) -> (r: Option<Vec<Vec<usize>>>)
    requires
        ast_wf(arena_of(nodes@)),
        toks_match(src@, toks@, ts),
        starts_inc(ts),
    ensures
        match r {
            Some(bn) => bn.len() == nodes.len() && bn_inv(
                arena_of(nodes@),
                ts,
                toks@,
                bn@,
                nodes.len() as int,
            ),
            None => true,
        },
{
    let ghost a = arena_of(nodes@);
    let n = nodes.len();
    let mut bn: Vec<Vec<usize>> = Vec::new();
    let mut m: usize = 0;
    while m < n
        invariant
            m <= n,
            n == nodes.len(),
            bn.len() == m,
            a == arena_of(nodes@),
            ast_wf(a),
            toks_match(src@, toks@, ts),
            starts_inc(ts),
            bn_inv(a, ts, toks@, bn@, m as int),
        decreases n - m,
    {
        let kind = match nodes.get(m) {
            Some(x) => x.kind,
            None => {
                return None;
            },
        };
        proof {
            assert(a.nodes[m as int] == nodes@[m as int]@);
            assert(a.nodes[m as int].kind == kind);
        }
        let cur: Vec<usize> = match kind {
            NodeKind::BindingIdentifier => match bn_ident(src, nodes, toks, by_start, m, Ghost(ts)) {
                Some(v) => v,
                None => {
                    return None;
                },
            },
            NodeKind::BindingElement | NodeKind::BindingRestElement | NodeKind::BindingRestProperty
            | NodeKind::FunctionRestParameter | NodeKind::VariableDeclaration | NodeKind::LexicalBinding
            | NodeKind::ForDeclaration => match bn_child(nodes, toks, bn.as_slice(), m, false, Ghost(ts)) {
                Some(v) => v,
                None => {
                    return None;
                },
            },
            NodeKind::BindingProperty => match bn_child(nodes, toks, bn.as_slice(), m, true, Ghost(ts)) {
                Some(v) => v,
                None => {
                    return None;
                },
            },
            NodeKind::ObjectBindingPattern | NodeKind::ArrayBindingPattern | NodeKind::FormalParameters
            | NodeKind::VariableStatement | NodeKind::LexicalDeclaration
            | NodeKind::VariableDeclarationList => match bn_list(nodes, toks, bn.as_slice(), m, Ghost(ts)) {
                Some(v) => v,
                None => {
                    return None;
                },
            },
            _ => Vec::new(),
        };
        proof {
            assert(idx_ok(toks@, cur@));
            assert(names_of(toks@, cur@) =~= bound_names(a, ts, m as int));
        }
        let ghost old_bn = bn@;
        bn.push(cur);
        proof {
            assert forall|j: int| 0 <= j < m as int + 1 implies {
                let v = (#[trigger] bn@[j])@;
                idx_ok(toks@, v) && names_of(toks@, v) =~= bound_names(a, ts, j)
            } by {
                if j < m as int {
                    assert(bn@[j] == old_bn[j]);
                }
            }
        }
        m = m.saturating_add(1);
    }
    Some(bn)
}

// ---------------------------------------------------------------------
// Use Strict Directive.
// ---------------------------------------------------------------------

/// The text of the two forms of a Use Strict Directive, as code points.
proof fn lemma_use_strict_words()
    ensures
        cps("\"use strict\""@) =~= seq![34u32, 117, 115, 101, 32, 115, 116, 114, 105, 99, 116, 34],
        cps("'use strict'"@) =~= seq![39u32, 117, 115, 101, 32, 115, 116, 114, 105, 99, 116, 39],
{
    reveal_strlit("\"use strict\"");
    reveal_strlit("'use strict'");
    assert("\"use strict\""@ =~= seq!['"', 'u', 's', 'e', ' ', 's', 't', 'r', 'i', 'c', 't', '"']);
    assert("'use strict'"@ =~= seq!['\'', 'u', 's', 'e', ' ', 's', 't', 'r', 'i', 'c', 't', '\'']);
}

/// The code points of `src` from `start` to `end` are `lit`.
fn range_is(src: &[u32], start: usize, end: usize, lit: &[u32]) -> (r: bool)
    requires
        start <= end,
        end <= src.len(),
    ensures
        r == (src@.subrange(start as int, end as int) =~= lit@),
{
    if end.saturating_sub(start) != lit.len() {
        return false;
    }
    let len = lit.len();
    let mut i: usize = 0;
    while i < len
        invariant
            len == lit.len(),
            len == end - start,
            end <= src.len(),
            start <= end,
            i <= len,
            forall|q: int| 0 <= q < i ==> src@[start as int + q] == lit@[q],
        decreases len - i,
    {
        let (x, y) = match (src.get(start.saturating_add(i)), lit.get(i)) {
            (Some(x), Some(y)) => (*x, *y),
            _ => {
                return false;
            },
        };
        if x != y {
            proof {
                assert(src@.subrange(start as int, end as int)[i as int] == src@[start as int + i as int]);
            }
            return false;
        }
        i = i.saturating_add(1);
    }
    proof {
        assert(src@.subrange(start as int, end as int) =~= lit@);
    }
    true
}

/// No item of `ks` before `k` is a Use Strict Directive, they are all directives, and `k`
/// is not a directive or the end: the items have no Use Strict Directive.
proof fn lemma_no_use_strict(a: AstV, ts: Stream, ks: Seq<int>, k: int)
    requires
        0 <= k <= ks.len(),
        forall|m: int|
            0 <= m < k ==> is_directive(a, #[trigger] ks[m]) && !is_use_strict_directive(
                a,
                ts,
                ks[m],
            ),
        k == ks.len() || !is_directive(a, ks[k]),
    ensures
        !has_use_strict(a, ts, ks),
{
    assert forall|kk: int|
        0 <= kk < ks.len() implies !(is_use_strict_directive(a, ts, #[trigger] ks[kk]) && (forall|m: int|
        0 <= m <= kk ==> is_directive(a, #[trigger] ks[m]))) by {
        if kk < k {
            assert(!is_use_strict_directive(a, ts, ks[kk]));
        } else {
            assert(0 <= k <= kk);
            assert(k < ks.len());
            assert(!is_directive(a, ks[k]));
        }
    }
}

/// The items of node `b` have a Use Strict Directive (`has_use_strict`).
#[verifier::rlimit(400)]
pub fn use_strict_exec(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    by_start: &[usize],
    b: usize,
    Ghost(ts): Ghost<Stream>,
) -> (r: Option<bool>)
    requires
        b < nodes.len(),
        ast_wf(arena_of(nodes@)),
        toks_match(src@, toks@, ts),
        starts_inc(ts),
    ensures
        match r {
            Some(v) => v == has_use_strict(arena_of(nodes@), ts, kids(arena_of(nodes@), b as int)),
            None => true,
        },
{
    let ghost a = arena_of(nodes@);
    let nd = match nodes.get(b) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let len = nd.children.len();
    proof {
        assert(a.nodes[b as int] == nodes@[b as int]@);
        assert(nd == &nodes@[b as int]);
        assert(a.nodes[b as int].children.len() == len);
        lemma_use_strict_words();
    }
    let ghost ks = a.nodes[b as int].children;
    let mut k: usize = 0;
    while k < len
        invariant
            k <= len,
            len == nd.children.len(),
            b < nodes.len(),
            nd == &nodes@[b as int],
            a == arena_of(nodes@),
            ast_wf(a),
            toks_match(src@, toks@, ts),
            starts_inc(ts),
            ks == a.nodes[b as int].children,
            len == ks.len(),
            forall|m: int|
                0 <= m < k ==> is_directive(a, #[trigger] ks[m]) && !is_use_strict_directive(
                    a,
                    ts,
                    ks[m],
                ),
        decreases len - k,
    {
        let c = match nd.children.as_slice().get(k) {
            Some(c) => *c as usize,
            None => {
                return None;
            },
        };
        proof {
            assert(a.nodes[b as int].children[k as int] == c as int);
            lemma_child_before(a, b as int, k as int);
        }
        let cnd = match nodes.get(c) {
            Some(x) => x,
            None => {
                return None;
            },
        };
        proof {
            assert(a.nodes[c as int] == nodes@[c as int]@);
            assert(cnd == &nodes@[c as int]);
        }
        let not_directive = if !matches!(cnd.kind, NodeKind::ExpressionStatement) {
            true
        } else {
            match kid_kind(nodes, c, 0) {
                Some(k0) => !matches!(k0, NodeKind::StringLiteral),
                None => {
                    return None;
                },
            }
        };
        if not_directive {
            proof {
                assert(!is_directive(a, ks[k as int]));
                lemma_no_use_strict(a, ts, ks, k as int);
            }
            return Some(false);
        }
        let e = match cnd.children.as_slice().get(ZERO) {
            Some(e) => *e as usize,
            None => {
                return None;
            },
        };
        proof {
            assert(a.nodes[c as int].children[0] == e as int);
            lemma_child_before(a, c as int, 0);
            assert(is_directive(a, ks[k as int]));
        }
        let x = match node_token(nodes, toks, by_start, e) {
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
            assert(t == &toks@[x as int]);
            assert(dtok_matches(src@, toks@[x as int], ts.toks[x as int]));
            lemma_node_tok_at(a, ts, e as int, x as int);
        }
        let r1 = range_is(src, t.start, t.end, &[34, 117, 115, 101, 32, 115, 116, 114, 105, 99, 116, 34]);
        let r2 = range_is(src, t.start, t.end, &[39, 117, 115, 101, 32, 115, 116, 114, 105, 99, 116, 39]);
        proof {
            let c_ = ks[k as int];
            assert(c_ == c as int);
            assert(kids(a, c as int) == a.nodes[c as int].children);
            assert(kid(kids(a, c_), 0) == e as int);
            assert(node_tok(a, ts, e as int) == ts.toks[x as int]);
            assert(ts.toks[x as int].text =~= src@.subrange(t.start as int, t.end as int));
            assert(is_directive(a, c_));
            lemma_use_strict_words();
            assert(r1 == (ts.toks[x as int].text =~= cps("\"use strict\""@)));
            assert(r2 == (ts.toks[x as int].text =~= cps("'use strict'"@)));
            assert(is_use_strict_directive(a, ts, c_) == (ts.toks[x as int].text =~= cps(
                "\"use strict\""@,
            ) || ts.toks[x as int].text =~= cps("'use strict'"@)));
        }
        if r1 || r2 {
            proof {
                assert(is_use_strict_directive(a, ts, ks[k as int]));
                assert(0 <= k as int && (k as int) < ks.len() && is_use_strict_directive(
                    a,
                    ts,
                    #[trigger] ks[k as int],
                ) && (forall|m: int| 0 <= m <= k as int ==> is_directive(a, #[trigger] ks[m])));
                assert(has_use_strict(a, ts, ks));
            }
            return Some(true);
        }
        proof {
            assert(!is_use_strict_directive(a, ts, ks[k as int]));
        }
        k = k.saturating_add(1);
    }
    proof {
        lemma_no_use_strict(a, ts, ks, len as int);
    }
    Some(false)
}

// ---------------------------------------------------------------------
// Parameters.
// ---------------------------------------------------------------------

/// Each parameter of the `FormalParameters` node `p` is a plain `BindingIdentifier`, without an
/// initializer (`is_simple_params`).
pub fn simple_params_exec(nodes: &[Node], p: usize) -> (r: bool)
    requires
        p < nodes.len(),
        ast_wf(arena_of(nodes@)),
    ensures
        r ==> is_simple_params(arena_of(nodes@), p as int),
{
    let ghost a = arena_of(nodes@);
    let nd = match nodes.get(p) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    let len = nd.children.len();
    proof {
        assert(a.nodes[p as int] == nodes@[p as int]@);
        assert(nd == &nodes@[p as int]);
        assert(a.nodes[p as int].children.len() == len);
    }
    let mut k: usize = 0;
    while k < len
        invariant
            k <= len,
            len == nd.children.len(),
            p < nodes.len(),
            nd == &nodes@[p as int],
            a == arena_of(nodes@),
            ast_wf(a),
            len == a.nodes[p as int].children.len(),
            forall|q: int|
                0 <= q < k ==> {
                    let e = #[trigger] kids(a, p as int)[q];
                    kd(a, e) == NodeKind::BindingElement && first_kid_kind(a, e)
                        == NodeKind::BindingIdentifier && kd(a, kid(kids(a, e), 1))
                        == NodeKind::Absent
                },
        decreases len - k,
    {
        let c = match nd.children.as_slice().get(k) {
            Some(c) => *c as usize,
            None => {
                return false;
            },
        };
        proof {
            assert(a.nodes[p as int].children[k as int] == c as int);
            lemma_child_before(a, p as int, k as int);
            assert(kids(a, p as int) == a.nodes[p as int].children);
        }
        let ck = match nodes.get(c) {
            Some(x) => x.kind,
            None => {
                return false;
            },
        };
        proof {
            assert(a.nodes[c as int] == nodes@[c as int]@);
        }
        if !matches!(ck, NodeKind::BindingElement) {
            return false;
        }
        match (kid_kind(nodes, c, 0), kid_kind(nodes, c, 1)) {
            (Some(NodeKind::BindingIdentifier), Some(NodeKind::Absent)) => {},
            _ => {
                return false;
            },
        }
        proof {
            assert(kd(a, c as int) == NodeKind::BindingElement);
        }
        k = k.saturating_add(1);
    }
    true
}

/// The names `xs` have no name twice.
pub fn no_dup_exec(toks: &[DTok], xs: &[usize]) -> (r: bool)
    requires
        idx_ok(toks@, xs@),
    ensures
        r ==> !has_duplicate(names_of(toks@, xs@)),
{
    let len = xs.len();
    let mut i: usize = 0;
    while i < len
        invariant
            len == xs.len(),
            i <= len,
            idx_ok(toks@, xs@),
            forall|x: int, y: int|
                0 <= x < i && x < y < len ==> !(names_of(toks@, xs@)[x] =~= names_of(toks@, xs@)[y]),
        decreases len - i,
    {
        let ni = match xs.get(i) {
            Some(x) => match toks.get(*x) {
                Some(t) => t,
                None => {
                    return false;
                },
            },
            None => {
                return false;
            },
        };
        let mut j: usize = i.saturating_add(1);
        while j < len
            invariant
                len == xs.len(),
                i < len,
                i < j,
                j <= len,
                idx_ok(toks@, xs@),
                ni == &toks@[xs@[i as int] as int],
                forall|x: int, y: int|
                    0 <= x < i && x < y < len ==> !(names_of(toks@, xs@)[x] =~= names_of(toks@, xs@)[y]),
                forall|y: int| i < y < j ==> !(names_of(toks@, xs@)[i as int] =~= names_of(toks@, xs@)[y]),
            decreases len - j,
        {
            let nj = match xs.get(j) {
                Some(x) => match toks.get(*x) {
                    Some(t) => t,
                    None => {
                        return false;
                    },
                },
                None => {
                    return false;
                },
            };
            if seq_eq(ni.name.as_slice(), nj.name.as_slice()) {
                return false;
            }
            j = j.saturating_add(1);
        }
        i = i.saturating_add(1);
    }
    proof {
        assert forall|x: int, y: int|
            0 <= x < y < names_of(toks@, xs@).len() implies !(#[trigger] names_of(toks@, xs@)[x]
            =~= #[trigger] names_of(toks@, xs@)[y]) by {
            assert(x < len && y < len);
        }
    }
    true
}

/// `function_early` of the function-like production with the `FormalParameters` node `params`
/// and the body whose statements are the children of node `body` (none, for `None`), in code
/// that is strict if `env_strict` or if the body has a Use Strict Directive.
#[verifier::rlimit(400)]
pub fn function_early_exec(
    tk: &Tk,
    nodes: &[Node],
    params: usize,
    body: Option<usize>,
    unique: bool,
    env_strict: bool,
    Ghost(ts): Ghost<Stream>,
) -> (r: bool)
    requires
        params < nodes.len(),
        match body {
            Some(b) => b < nodes.len(),
            None => true,
        },
        ast_wf(arena_of(nodes@)),
        toks_match(tk.src@, tk.toks@, ts),
        starts_inc(ts),
        tk.bn.len() == nodes.len(),
        bn_inv(arena_of(nodes@), ts, tk.toks@, tk.bn@, nodes.len() as int),
    ensures
        r ==> {
            let a = arena_of(nodes@);
            let body_ks = match body {
                Some(b) => kids(a, b as int),
                None => Seq::empty(),
            };
            function_early(a, ts, params as int, body_ks, unique, env_strict || has_use_strict(
                a,
                ts,
                body_ks,
            ))
        },
{
    let src = tk.src;
    let toks = tk.toks;
    let by_start = tk.by_start;
    let bn = tk.bn;
    let ghost a = arena_of(nodes@);
    let (hus, lex_empty) = match body {
        Some(b) => {
            let h = match use_strict_exec(src, nodes, toks, by_start, b, Ghost(ts)) {
                Some(h) => h,
                None => {
                    return false;
                },
            };
            (h, items_lex_empty(nodes, b, true))
        },
        None => (false, true),
    };
    if !lex_empty {
        return false;
    }
    let simple = simple_params_exec(nodes, params);
    if hus && !simple {
        return false;
    }
    let names = match bn.get(params) {
        Some(v) => v,
        None => {
            return false;
        },
    };
    proof {
        assert(bn@[params as int] == names);
        assert(idx_ok(toks@, names@));
    }
    let need_unique = env_strict || hus || unique || !simple;
    let distinct = no_dup_exec(toks, names.as_slice());
    if need_unique && !distinct {
        return false;
    }
    proof {
        let body_ks = match body {
            Some(b) => kids(a, b as int),
            None => Seq::empty(),
        };
        let nb = a.nodes.len() as int;
        let strict = env_strict || has_use_strict(a, ts, body_ks);
        assert(has_use_strict(a, ts, body_ks) == hus);
        if let Some(b) = body {
            lemma_lex_list_empty(a, ts, nb, body_ks, 0, true);
        }
        assert(lex_names_list(a, ts, nb, body_ks, 0, true) =~= Seq::<DeclName>::empty());
        assert(plain_names(lex_names_list(a, ts, nb, body_ks, 0, true)) =~= Seq::<Seq<u32>>::empty());
        let bnames = bound_names(a, ts, params as int);
        assert(bnames =~= names_of(toks@, names@));
        assert(!intersects(bnames, plain_names(lex_names_list(a, ts, nb, body_ks, 0, true))));
        if strict || unique || !is_simple_params(a, params as int) {
            if env_strict || hus || unique || !simple {
                assert(!has_duplicate(names_of(toks@, names@)));
            } else {
                assert(simple);
                assert(is_simple_params(a, params as int));
            }
        }
    }
    true
}

// ---------------------------------------------------------------------
// Object literals.
// ---------------------------------------------------------------------

/// `__proto__` as code points.
proof fn lemma_proto_word()
    ensures
        sv("__proto__"@) =~= seq![0x5Fu32, 0x5F, 0x70, 0x72, 0x6F, 0x74, 0x6F, 0x5F, 0x5F],
{
    reveal_strlit("__proto__");
    assert("__proto__"@ =~= seq!['_', '_', 'p', 'r', 'o', 't', 'o', '_', '_']);
}

/// The property `c` is a `__proto__: value` entry (`is_proto_entry`).
#[verifier::rlimit(400)]
fn is_proto_exec(tk: &Tk, nodes: &[Node], c: usize, Ghost(ts): Ghost<Stream>) -> (r: Option<bool>)
    requires
        c < nodes.len(),
        ast_wf(arena_of(nodes@)),
        toks_match(tk.src@, tk.toks@, ts),
        starts_inc(ts),
    ensures
        match r {
            Some(v) => v == is_proto_entry(arena_of(nodes@), ts, c as int),
            None => true,
        },
{
    let src = tk.src;
    let toks = tk.toks;
    let by_start = tk.by_start;
    let _ = src.len();
    let ghost a = arena_of(nodes@);
    let nd = match nodes.get(c) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    proof {
        assert(a.nodes[c as int] == nodes@[c as int]@);
        assert(nd == &nodes@[c as int]);
        assert(a.nodes[c as int].kind == nd.kind);
        assert(a.nodes[c as int].op == nd.op);
        assert(a.nodes[c as int].children.len() == nd.children.len());
        assert(kids(a, c as int) == a.nodes[c as int].children);
    }
    if !matches!(nd.kind, NodeKind::PropertyDefinition) || !matches!(nd.op, Op::KeyValue) {
        return Some(false);
    }
    let key = match nd.children.as_slice().get(ZERO) {
        Some(k) => *k as usize,
        None => {
            return Some(false);
        },
    };
    proof {
        assert(a.nodes[c as int].children[0] == key as int);
        lemma_child_before(a, c as int, 0);
    }
    let kk = match nodes.get(key) {
        Some(x) => x.kind,
        None => {
            return None;
        },
    };
    proof {
        assert(a.nodes[key as int] == nodes@[key as int]@);
        assert(a.nodes[key as int].kind == kk);
    }
    if !matches!(kk, NodeKind::IdentifierName | NodeKind::StringLiteral) {
        return Some(false);
    }
    let x = match node_token(nodes, toks, by_start, key) {
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
        assert(t == &toks@[x as int]);
        assert(dtok_matches(src@, toks@[x as int], ts.toks[x as int]));
        lemma_node_tok_at(a, ts, key as int, x as int);
        lemma_proto_word();
    }
    Some(seq_eq(t.name.as_slice(), &[0x5F, 0x5F, 0x70, 0x72, 0x6F, 0x74, 0x6F, 0x5F, 0x5F]))
}

/// `early_local` of an `ObjectLiteral` node `m`: at most one `__proto__: v` entry, and no method
/// with a private name.
#[verifier::rlimit(400)]
pub fn object_literal_exec(tk: &Tk, nodes: &[Node], m: usize, Ghost(ts): Ghost<Stream>) -> (r: bool)
    requires
        m < nodes.len(),
        ast_wf(arena_of(nodes@)),
        toks_match(tk.src@, tk.toks@, ts),
        starts_inc(ts),
    ensures
        r ==> {
            let a = arena_of(nodes@);
            let ks = a.nodes[m as int].children;
            (!exists|x: int, y: int|
                0 <= x < y < ks.len() && is_proto_entry(a, ts, #[trigger] ks[x]) && is_proto_entry(
                    a,
                    ts,
                    #[trigger] ks[y],
                )) && (forall|x: int|
                0 <= x < ks.len() ==> !(kd(a, #[trigger] ks[x]) == NodeKind::MethodDefinition && kd(
                    a,
                    kid(kids(a, ks[x]), 0),
                ) == NodeKind::PrivateIdentifier))
        },
{
    let ghost a = arena_of(nodes@);
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    let len = nd.children.len();
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children.len() == len);
    }
    let ghost ks = a.nodes[m as int].children;
    let mut seen = false;
    let mut k: usize = 0;
    while k < len
        invariant
            k <= len,
            len == nd.children.len(),
            m < nodes.len(),
            nd == &nodes@[m as int],
            a == arena_of(nodes@),
            ast_wf(a),
            toks_match(tk.src@, tk.toks@, ts),
            starts_inc(ts),
            ks == a.nodes[m as int].children,
            len == ks.len(),
            seen ==> exists|x: int| 0 <= x < k && is_proto_entry(a, ts, #[trigger] ks[x]),
            !seen ==> forall|x: int| 0 <= x < k ==> !is_proto_entry(a, ts, #[trigger] ks[x]),
            forall|x: int, y: int|
                0 <= x < y < k ==> !(is_proto_entry(a, ts, #[trigger] ks[x]) && is_proto_entry(
                    a,
                    ts,
                    #[trigger] ks[y],
                )),
            forall|x: int|
                0 <= x < k ==> !(kd(a, #[trigger] ks[x]) == NodeKind::MethodDefinition && kd(
                    a,
                    kid(kids(a, ks[x]), 0),
                ) == NodeKind::PrivateIdentifier),
        decreases len - k,
    {
        let c = match nd.children.as_slice().get(k) {
            Some(c) => *c as usize,
            None => {
                return false;
            },
        };
        proof {
            assert(a.nodes[m as int].children[k as int] == c as int);
            lemma_child_before(a, m as int, k as int);
        }
        let is_p = match is_proto_exec(tk, nodes, c, Ghost(ts)) {
            Some(v) => v,
            None => {
                return false;
            },
        };
        if is_p && seen {
            return false;
        }
        let ck = match nodes.get(c) {
            Some(x) => x.kind,
            None => {
                return false;
            },
        };
        proof {
            assert(a.nodes[c as int] == nodes@[c as int]@);
            assert(a.nodes[c as int].kind == ck);
        }
        if matches!(ck, NodeKind::MethodDefinition) {
            match kid_kind(nodes, c, 0) {
                Some(NodeKind::PrivateIdentifier) => {
                    return false;
                },
                Some(_) => {},
                None => {
                    return false;
                },
            }
        }
        proof {
            assert(kids(a, c as int) == a.nodes[c as int].children);
            assert(ks[k as int] == c as int);
        }
        if is_p {
            seen = true;
        }
        k = k.saturating_add(1);
    }
    true
}

} // verus!
