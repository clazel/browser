//! The arena check: the part of the parser that is proven.
//!
//! [`finish`] takes the nodes the recursive-descent parser built (after the
//! nodes that the cover grammars left behind are dropped) and returns an
//! [`Ast`] only if it is well formed ([`ast_wf`]), every span is inside the
//! source text and every child's span inside its parent's ([`spans_wf`]), and its
//! height is at most [`MAX_DEPTH`]: the structural half of
//! [`crate::contract::parse_ensures`] for an `Ok`, whatever the parser did to
//! build the nodes. The check is linear: one pass for the shape and the spans,
//! one for the parents (no garbage), one for the heights.
//!
//! What is *not* proven: that the arena is a derivation of a token stream of
//! the source text by the grammar, with no early error, and that an `Err` means
//! there is no parse (the rest of `parse_ensures`). Those are tested.

use crate::api::ParseError;
use crate::ast::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// The arena of `nodes` with the root `root`, as the specification reads it
/// (the view of an [`Ast`]).
pub open spec fn arena(nodes: Seq<Node>, root: int) -> AstV {
    AstV { nodes: nodes.map_values(|n: Node| n@), root: root }
}

/// Node `m` of `a` is well formed in an arena whose root is `a.root`, in a source
/// text of length `len`: its children are before it, only the root is a `Script` or
/// `Module`, its span is inside the source text, and its children's spans inside it.
pub open spec fn node_ok(a: AstV, m: int, len: int) -> bool {
    let nd = a.nodes[m];
    (forall|k: int| 0 <= k < nd.children.len() ==> 0 <= #[trigger] nd.children[k] < m) && ((
    nd.kind == NodeKind::Script || nd.kind == NodeKind::Module) <==> m == a.root) && 0 <= nd.start
        <= nd.end <= len && (forall|k: int|
        0 <= k < nd.children.len() ==> nd.start <= a.nodes[#[trigger] nd.children[k]].start
            && a.nodes[nd.children[k]].end <= nd.end)
}

/// What [`finish`] promises of an `Ok`: the structural half of
/// [`crate::contract::parse_ensures`].
pub open spec fn finish_ensures(src_len: int, r: Result<Ast, ParseError>) -> bool {
    match r {
        Ok(ast) => ast_wf(ast@) && spans_wf(ast@, src_len) && height(ast@, ast@.root)
            <= MAX_DEPTH as int,
        Err(_) => true,
    }
}

/// `height(a, c) <= b` for every child of `n` in `ks[k..]`, so is `max_height`.
proof fn lemma_max_height_le(a: AstV, n: int, ks: Seq<int>, k: int, b: int)
    requires
        b >= 0,
        forall|j: int| k <= j < ks.len() ==> (0 <= #[trigger] ks[j] < n ==> height(a, ks[j]) <= b),
    ensures
        max_height(a, n, ks, k) <= b,
    decreases ks.len() - k,
{
    if k < 0 || k >= ks.len() {
    } else {
        lemma_max_height_le(a, n, ks, k + 1, b);
    }
}

/// `height(a, n) <= b + 1` when every child of `n` has height at most `b`.
proof fn lemma_height_le(a: AstV, n: int, b: int)
    requires
        b >= 0,
        0 <= n < a.nodes.len(),
        forall|j: int|
            0 <= j < a.nodes[n].children.len() ==> (0 <= #[trigger] a.nodes[n].children[j] < n
                ==> height(a, a.nodes[n].children[j]) <= b),
    ensures
        height(a, n) <= b + 1,
{
    lemma_max_height_le(a, n, a.nodes[n].children, 0, b);
}

/// Checks the arena `nodes` (children before parents, the root last) of a
/// source text of `src_len` code points, and returns it as an [`Ast`] if it is
/// well formed, inside the source text and at most [`MAX_DEPTH`] high.
///
/// Proven: [`finish_ensures`] of the result.
pub fn finish(nodes: Vec<Node>, src_len: usize) -> (r: Result<Ast, ParseError>)
    ensures
        finish_ensures(src_len as int, r),
{
    let n = nodes.len();
    if n == 0 || n > 0xFFFF_FFFFusize {
        return Err(ParseError::Syntax);
    }
    let root = n.saturating_sub(1);
    let ghost a = arena(nodes@, root as int);
    assert(a.nodes.len() == n);
    // Pass 1: the shape of every node, and its span.
    let mut m: usize = 0;
    while m < n
        invariant
            n == nodes.len(),
            root + 1 == n,
            n <= 0xFFFF_FFFF,
            a == arena(nodes@, root as int),
            m <= n,
            forall|j: int| 0 <= j < m ==> node_ok(a, j, src_len as int),
        decreases n - m,
    {
        let nd = match nodes.as_slice().get(m) {
            Some(x) => x,
            None => {
                return Err(ParseError::Syntax);
            },
        };
        let is_root_kind = matches!(nd.kind, NodeKind::Script | NodeKind::Module);
        if is_root_kind != (m == root) {
            return Err(ParseError::Syntax);
        }
        if !(nd.start <= nd.end && nd.end <= src_len) {
            return Err(ParseError::Syntax);
        }
        let mut k: usize = 0;
        while k < nd.children.len()
            invariant
                n == nodes.len(),
                m < n,
                nd == nodes@[m as int],
                a == arena(nodes@, root as int),
                k <= nd.children.len(),
                forall|j: int|
                    0 <= j < k ==> (0 <= #[trigger] nd.children@[j] as int) && (nd.children@[j] as int)
                        < m && nd.start as int <= nodes@[nd.children@[j] as int].start as int
                        && nodes@[nd.children@[j] as int].end as int <= nd.end as int,
            decreases nd.children.len() - k,
        {
            let c = match nd.children.as_slice().get(k) {
                Some(x) => *x,
                None => {
                    return Err(ParseError::Syntax);
                },
            };
            let cu = c as usize;
            if cu >= m {
                return Err(ParseError::Syntax);
            }
            let cn = match nodes.as_slice().get(cu) {
                Some(x) => x,
                None => {
                    return Err(ParseError::Syntax);
                },
            };
            if !(nd.start <= cn.start && cn.end <= nd.end) {
                return Err(ParseError::Syntax);
            }
            k = k.saturating_add(1);
        }
        proof {
            assert(node_ok(a, m as int, src_len as int)) by {
                let ndv = a.nodes[m as int];
                assert(ndv.children.len() == nd.children.len());
                assert forall|k2: int| 0 <= k2 < ndv.children.len() implies 0 <= #[trigger] ndv.children[k2]
                    < m by {
                    assert(ndv.children[k2] == nd.children@[k2] as int);
                }
                assert forall|k2: int|
                    0 <= k2 < ndv.children.len() implies ndv.start <= a.nodes[#[trigger] ndv.children[k2]].start
                    && a.nodes[ndv.children[k2]].end <= ndv.end by {
                    assert(ndv.children[k2] == nd.children@[k2] as int);
                    let c2 = nd.children@[k2] as int;
                    assert(a.nodes[c2] == nodes@[c2]@);
                }
            }
        }
        m = m.saturating_add(1);
    }
    // Pass 2: every node but the root is a child of some node.
    let mut marks: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            marks.len() == i,
            forall|q: int| 0 <= q < i ==> !#[trigger] marks@[q],
        decreases n - i,
    {
        marks.push(false);
        i = i.saturating_add(1);
    }
    let mut p: usize = 0;
    while p < n
        invariant
            n == nodes.len(),
            root + 1 == n,
            a == arena(nodes@, root as int),
            marks.len() == n,
            p <= n,
            forall|j: int| 0 <= j < n ==> node_ok(a, j, src_len as int),
            forall|q: int| 0 <= q < n && #[trigger] marks@[q] ==> has_parent(a, q),
        decreases n - p,
    {
        let nd = match nodes.as_slice().get(p) {
            Some(x) => x,
            None => {
                return Err(ParseError::Syntax);
            },
        };
        let mut k: usize = 0;
        while k < nd.children.len()
            invariant
                n == nodes.len(),
                p < n,
                nd == nodes@[p as int],
                a == arena(nodes@, root as int),
                marks.len() == n,
                k <= nd.children.len(),
                forall|j: int| 0 <= j < n ==> node_ok(a, j, src_len as int),
                forall|q: int| 0 <= q < n && #[trigger] marks@[q] ==> has_parent(a, q),
            decreases nd.children.len() - k,
        {
            let c = match nd.children.as_slice().get(k) {
                Some(x) => *x,
                None => {
                    return Err(ParseError::Syntax);
                },
            };
            let cu = c as usize;
            if cu >= n {
                return Err(ParseError::Syntax);
            }
            proof {
                let ndv = a.nodes[p as int];
                assert(ndv.children[k as int] == nd.children@[k as int] as int);
                assert(node_ok(a, p as int, src_len as int));
                assert(cu < p) by {
                    assert(0 <= ndv.children[k as int] < p as int);
                }
                assert(has_parent(a, cu as int)) by {
                    assert(a.nodes[p as int].children[k as int] == cu as int);
                }
            }
            marks.set(cu, true);
            k = k.saturating_add(1);
        }
        p = p.saturating_add(1);
    }
    let mut q: usize = 0;
    while q < root
        invariant
            root + 1 == n,
            marks.len() == n,
            q <= root,
            forall|j: int| 0 <= j < n && #[trigger] marks@[j] ==> has_parent(a, j),
            forall|j: int| 0 <= j < q ==> has_parent(a, j),
        decreases root - q,
    {
        match marks.as_slice().get(q) {
            Some(true) => {},
            _ => {
                return Err(ParseError::Syntax);
            },
        }
        q = q.saturating_add(1);
    }
    // Pass 3: the heights. A height past the limit is stored as `cap`.
    let cap: usize = MAX_DEPTH.saturating_add(1);
    let mut h: Vec<usize> = Vec::new();
    let mut m: usize = 0;
    while m < n
        invariant
            n == nodes.len(),
            root + 1 == n,
            a == arena(nodes@, root as int),
            m <= n,
            h.len() == m,
            cap == MAX_DEPTH + 1,
            forall|j: int| 0 <= j < n ==> node_ok(a, j, src_len as int),
            forall|j: int|
                0 <= j < m ==> 1 <= #[trigger] h@[j] <= cap && (h@[j] <= MAX_DEPTH ==> height(a, j)
                    <= h@[j] as int),
        decreases n - m,
    {
        let nd = match nodes.as_slice().get(m) {
            Some(x) => x,
            None => {
                return Err(ParseError::Syntax);
            },
        };
        let mut best: usize = 0;
        let mut k: usize = 0;
        while k < nd.children.len()
            invariant
                n == nodes.len(),
                m < n,
                nd == nodes@[m as int],
                a == arena(nodes@, root as int),
                h.len() == m,
                best <= cap,
                k <= nd.children.len(),
                forall|j: int| 0 <= j < n ==> node_ok(a, j, src_len as int),
                forall|j: int| 0 <= j < k ==> (nd.children@[j] as int) < m,
                forall|j: int|
                    0 <= j < k ==> #[trigger] h@[nd.children@[j] as int] <= best,
                forall|j: int|
                    0 <= j < m ==> 1 <= #[trigger] h@[j] <= cap && (h@[j] <= MAX_DEPTH ==> height(a, j)
                        <= h@[j] as int),
            decreases nd.children.len() - k,
        {
            let c = match nd.children.as_slice().get(k) {
                Some(x) => *x,
                None => {
                    return Err(ParseError::Syntax);
                },
            };
            let cu = c as usize;
            proof {
                let ndv = a.nodes[m as int];
                assert(ndv.children[k as int] == nd.children@[k as int] as int);
                assert(node_ok(a, m as int, src_len as int));
            }
            let hc = match h.as_slice().get(cu) {
                Some(x) => *x,
                None => {
                    return Err(ParseError::Syntax);
                },
            };
            if hc > best {
                best = hc;
            }
            k = k.saturating_add(1);
        }
        let hm = if best >= MAX_DEPTH {
            cap
        } else {
            best.saturating_add(1)
        };
        proof {
            if hm <= MAX_DEPTH {
                let ndv = a.nodes[m as int];
                assert(node_ok(a, m as int, src_len as int));
                assert forall|j: int|
                    0 <= j < ndv.children.len() implies 0 <= #[trigger] ndv.children[j] < m as int
                    && height(a, ndv.children[j]) <= best as int by {
                    assert(ndv.children[j] == nd.children@[j] as int);
                    let cc = ndv.children[j];
                    assert(h@[cc] <= best);
                    assert(h@[cc] <= MAX_DEPTH);
                    assert(height(a, cc) <= h@[cc] as int);
                }
                lemma_height_le(a, m as int, best as int);
            }
        }
        h.push(hm);
        m = m.saturating_add(1);
    }
    let hr = match h.as_slice().get(root) {
        Some(x) => *x,
        None => {
            return Err(ParseError::Syntax);
        },
    };
    if hr > MAX_DEPTH {
        return Err(ParseError::TooDeep);
    }
    let ast = Ast { nodes, root: root as u32 };
    proof {
        assert(ast@ == a);
        assert(ast_wf(a)) by {
            assert forall|j: int| 0 <= j < a.nodes.len() implies {
                let nd = #[trigger] a.nodes[j];
                (forall|k: int| 0 <= k < nd.children.len() ==> 0 <= #[trigger] nd.children[k] < j)
                    && ((nd.kind == NodeKind::Script || nd.kind == NodeKind::Module) <==> j == a.root)
            } by {
                assert(node_ok(a, j, src_len as int));
            }
        }
        assert(spans_wf(a, src_len as int)) by {
            assert forall|j: int| 0 <= j < a.nodes.len() implies {
                let nd = #[trigger] a.nodes[j];
                0 <= nd.start <= nd.end <= src_len as int && (forall|k: int|
                    0 <= k < nd.children.len() ==> nd.start <= a.nodes[#[trigger] nd.children[k]].start
                        && a.nodes[nd.children[k]].end <= nd.end)
            } by {
                assert(node_ok(a, j, src_len as int));
            }
        }
        assert(height(a, a.root) <= MAX_DEPTH as int);
    }
    Ok(ast)
}

} // verus!
