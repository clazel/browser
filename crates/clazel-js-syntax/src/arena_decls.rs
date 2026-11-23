//! The declared names of every node, computed over the arena and proven equal to the
//! specification's (item 7.3): LexicallyDeclaredNames and TopLevelLexicallyDeclaredNames
//! (`spec::lex_names_item`), VarDeclaredNames and TopLevelVarDeclaredNames
//! (`spec::var_names_item`), each as a list of [`Decl`]s (the token that names the
//! declaration, and whether it is a plain function declaration), bottom-up
//! ([`decl_names_all`]), and the lists of a statement list put together ([`cat_exec`]).
//!
//! The `import` and `export` declarations of a module are not covered: the computation
//! returns `None` for them.

use crate::arena_d::*;
use crate::arena_early::*;
use crate::arena_names::*;
use crate::ast::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// A declared name: the token that names it, and whether the declaration is a
/// `FunctionDeclaration` that is not a generator or an async function.
#[derive(Clone, Copy)]
pub struct Decl {
    /// The token.
    pub x: usize,
    /// A plain function declaration.
    pub pf: bool,
}

/// The specification's declared names of `ds`.
pub open spec fn decls_of(toks: Seq<DTok>, ds: Seq<Decl>) -> Seq<DeclName> {
    Seq::new(ds.len(), |i: int| DeclName { name: toks[ds[i].x as int].name@, plain_function: ds[i].pf })
}

/// The names of `ds`.
pub open spec fn dn(toks: Seq<DTok>, ds: Seq<Decl>) -> Seq<Seq<u32>> {
    Seq::new(ds.len(), |i: int| toks[ds[i].x as int].name@)
}

/// Every declaration of `ds` names a token.
pub open spec fn decl_ok(toks: Seq<DTok>, ds: Seq<Decl>) -> bool {
    forall|i: int| 0 <= i < ds.len() ==> (#[trigger] ds[i]).x < toks.len()
}

/// `plain_names` of the declared names.
proof fn lemma_dn_plain(toks: Seq<DTok>, ds: Seq<Decl>)
    ensures
        plain_names(decls_of(toks, ds)) =~= dn(toks, ds),
{
}

/// The declared names of two lists put together.
pub proof fn lemma_decls_add(toks: Seq<DTok>, xs: Seq<Decl>, ys: Seq<Decl>)
    ensures
        decls_of(toks, xs + ys) =~= decls_of(toks, xs) + decls_of(toks, ys),
        dn(toks, xs + ys) =~= dn(toks, xs) + dn(toks, ys),
{
}

/// The declarations the names `xs` make, none of them a plain function declaration.
pub open spec fn decls_of_names(xs: Seq<usize>) -> Seq<Decl> {
    Seq::new(xs.len(), |i: int| Decl { x: xs[i], pf: false })
}

/// `dst` gets the elements of `src` after its own.
fn push_decls(dst: &mut Vec<Decl>, src: &[Decl])
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

/// The declarations of the names `xs`.
pub fn decls_from_names(xs: &[usize]) -> (r: Vec<Decl>)
    ensures
        r@ =~= decls_of_names(xs@),
{
    let mut out: Vec<Decl> = Vec::new();
    let mut i: usize = 0;
    while i < xs.len()
        invariant
            i <= xs.len(),
            out@ =~= decls_of_names(xs@).subrange(0, i as int),
        decreases xs.len() - i,
    {
        match xs.get(i) {
            Some(x) => {
                out.push(Decl { x: *x, pf: false });
            },
            None => {
                return out;
            },
        }
        proof {
            assert(decls_of_names(xs@).subrange(0, i as int + 1) =~= decls_of_names(xs@).subrange(
                0,
                i as int,
            ).push(decls_of_names(xs@)[i as int]));
        }
        i = i.saturating_add(1);
    }
    proof {
        assert(decls_of_names(xs@).subrange(0, xs@.len() as int) =~= decls_of_names(xs@));
    }
    out
}

/// The declarations of the children `ks[k..]`, put together, from the declarations `arr` of each node.
pub open spec fn cat_d(arr: Seq<Vec<Decl>>, ks: Seq<int>, k: int) -> Seq<Decl>
    decreases ks.len() - k,
{
    if k < 0 || k >= ks.len() {
        Seq::empty()
    } else {
        arr[ks[k]]@ + cat_d(arr, ks, k + 1)
    }
}

/// The declarations `arr[j]` name tokens, for `j < m`.
pub open spec fn arr_ok(toks: Seq<DTok>, arr: Seq<Vec<Decl>>, m: int) -> bool {
    forall|j: int| 0 <= j < m ==> decl_ok(toks, (#[trigger] arr[j])@)
}

/// A concatenation of declarations that name tokens does.
proof fn lemma_cat_ok(toks: Seq<DTok>, arr: Seq<Vec<Decl>>, ks: Seq<int>, k: int, m: int)
    requires
        arr_ok(toks, arr, m),
        forall|q: int| 0 <= q < ks.len() ==> 0 <= #[trigger] ks[q] < m,
    ensures
        decl_ok(toks, cat_d(arr, ks, k)),
    decreases ks.len() - k,
{
    if 0 <= k < ks.len() {
        lemma_cat_ok(toks, arr, ks, k + 1, m);
        let r = cat_d(arr, ks, k + 1);
        let l = arr[ks[k]]@;
        assert(decl_ok(toks, l));
        assert forall|i: int| 0 <= i < (l + r).len() implies (#[trigger] (l + r)[i]).x < toks.len() by {
            if i < l.len() {
                assert((l + r)[i] == l[i]);
            } else {
                assert((l + r)[i] == r[i - l.len()]);
            }
        }
    }
}

/// The declarations of the children of node `m` from `from` on, put together.
pub fn cat_exec(nodes: &[Node], arr: &[Vec<Decl>], m: usize, from: usize) -> (r: Option<Vec<Decl>>)
    requires
        m < nodes.len(),
        ast_wf(arena_of(nodes@)),
        arr.len() >= m,
    ensures
        match r {
            Some(v) => v@ =~= cat_d(arr@, arena_of(nodes@).nodes[m as int].children, from as int),
            None => true,
        },
{
    let ghost a = arena_of(nodes@);
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
    let mut acc: Vec<Decl> = Vec::new();
    if from >= len {
        return Some(acc);
    }
    let mut k = len;
    while k > from
        invariant
            from <= k <= len,
            len == nd.children.len(),
            len == ks.len(),
            m < nodes.len(),
            arr.len() >= m,
            nd == &nodes@[m as int],
            a == arena_of(nodes@),
            ast_wf(a),
            ks == a.nodes[m as int].children,
            acc@ =~= cat_d(arr@, ks, k as int),
        decreases k,
    {
        k = k.saturating_sub(1);
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
        let item = match arr.get(c) {
            Some(v) => v,
            None => {
                return None;
            },
        };
        let mut next: Vec<Decl> = Vec::new();
        push_decls(&mut next, item.as_slice());
        push_decls(&mut next, acc.as_slice());
        proof {
            assert(arr@[c as int] == item);
            assert(next@ =~= cat_d(arr@, ks, k as int));
        }
        acc = next;
    }
    Some(acc)
}

// ---------------------------------------------------------------------
// The names of every node.
// ---------------------------------------------------------------------

/// `arr[j]` is the lexically declared names of node `j` (`top`: top-level), for `j < m`.
pub open spec fn inv_l(a: AstV, ts: Stream, toks: Seq<DTok>, arr: Seq<Vec<Decl>>, top: bool, m: int) -> bool {
    forall|j: int|
        0 <= j < m ==> {
            let v = (#[trigger] arr[j])@;
            decl_ok(toks, v) && decls_of(toks, v) =~= lex_names_item(a, ts, j, top)
        }
}

/// `arr[j]` is the var declared names of node `j` (`top`: top-level), for `j < m`.
pub open spec fn inv_v(a: AstV, ts: Stream, toks: Seq<DTok>, arr: Seq<Vec<Decl>>, top: bool, m: int) -> bool {
    forall|j: int|
        0 <= j < m ==> {
            let v = (#[trigger] arr[j])@;
            decl_ok(toks, v) && dn(toks, v) =~= var_names_item(a, ts, j, top)
        }
}

/// The declarations of child `i` of a node, none if there is no such child.
pub open spec fn kid_spec(arr: Seq<Vec<Decl>>, ks: Seq<int>, i: int) -> Seq<Decl> {
    if 0 <= i < ks.len() {
        arr[ks[i]]@
    } else {
        Seq::empty()
    }
}

/// The declarations of child `i` of node `m`.
fn kid_d(nodes: &[Node], arr: &[Vec<Decl>], m: usize, i: usize) -> (r: Option<Vec<Decl>>)
    requires
        m < nodes.len(),
        ast_wf(arena_of(nodes@)),
        arr.len() >= m,
    ensures
        match r {
            Some(v) => v@ =~= kid_spec(arr@, arena_of(nodes@).nodes[m as int].children, i as int),
            None => true,
        },
{
    let ghost a = arena_of(nodes@);
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
    let c = match nd.children.as_slice().get(i) {
        Some(c) => *c as usize,
        None => {
            return Some(Vec::new());
        },
    };
    proof {
        assert(a.nodes[m as int].children[i as int] == c as int);
        lemma_child_before(a, m as int, i as int);
    }
    let item = match arr.get(c) {
        Some(v) => v,
        None => {
            return None;
        },
    };
    let mut out: Vec<Decl> = Vec::new();
    push_decls(&mut out, item.as_slice());
    proof {
        assert(arr@[c as int] == item);
    }
    Some(out)
}

/// The declarations of children `i`, `j` and `l` of node `m` put together.
fn sum3(nodes: &[Node], arr: &[Vec<Decl>], m: usize, i: usize, j: usize, l: usize) -> (r: Option<Vec<Decl>>)
    requires
        m < nodes.len(),
        ast_wf(arena_of(nodes@)),
        arr.len() == m,
    ensures
        match r {
            Some(v) => {
                let ks = arena_of(nodes@).nodes[m as int].children;
                v@ =~= kid_spec(arr@, ks, i as int) + kid_spec(arr@, ks, j as int) + kid_spec(
                    arr@,
                    ks,
                    l as int,
                )
            },
            None => true,
        },
{
    let x = match kid_d(nodes, arr, m, i) {
        Some(v) => v,
        None => {
            return None;
        },
    };
    let y = match kid_d(nodes, arr, m, j) {
        Some(v) => v,
        None => {
            return None;
        },
    };
    let z = match kid_d(nodes, arr, m, l) {
        Some(v) => v,
        None => {
            return None;
        },
    };
    let mut out: Vec<Decl> = Vec::new();
    push_decls(&mut out, x.as_slice());
    push_decls(&mut out, y.as_slice());
    push_decls(&mut out, z.as_slice());
    Some(out)
}

/// A declaration list that names tokens, of a child.
proof fn lemma_kid_ok(toks: Seq<DTok>, arr: Seq<Vec<Decl>>, ks: Seq<int>, i: int, m: int)
    requires
        arr_ok(toks, arr, m),
        forall|q: int| 0 <= q < ks.len() ==> 0 <= #[trigger] ks[q] < m,
    ensures
        decl_ok(toks, kid_spec(arr, ks, i)),
{
}

/// Two lists of declarations that name tokens, put together, do.
proof fn lemma_ok_add(toks: Seq<DTok>, xs: Seq<Decl>, ys: Seq<Decl>)
    requires
        decl_ok(toks, xs),
        decl_ok(toks, ys),
    ensures
        decl_ok(toks, xs + ys),
{
    assert forall|i: int| 0 <= i < (xs + ys).len() implies (#[trigger] (xs + ys)[i]).x < toks.len() by {
        if i < xs.len() {
            assert((xs + ys)[i] == xs[i]);
        } else {
            assert((xs + ys)[i] == ys[i - xs.len()]);
        }
    }
}

/// The lexically declared names of a list of items are those of its items put together.
proof fn lemma_lex_cat(
    a: AstV,
    ts: Stream,
    toks: Seq<DTok>,
    arr: Seq<Vec<Decl>>,
    top: bool,
    n: int,
    ks: Seq<int>,
    k: int,
)
    requires
        inv_l(a, ts, toks, arr, top, n),
        arr.len() >= n,
        forall|q: int| 0 <= q < ks.len() ==> 0 <= #[trigger] ks[q] < n,
    ensures
        decls_of(toks, cat_d(arr, ks, k)) =~= lex_names_list(a, ts, n, ks, k, top),
    decreases ks.len() - k,
{
    if 0 <= k < ks.len() {
        lemma_lex_cat(a, ts, toks, arr, top, n, ks, k + 1);
        lemma_decls_add(toks, arr[ks[k]]@, cat_d(arr, ks, k + 1));
        assert(decls_of(toks, arr[ks[k]]@) =~= lex_names_item(a, ts, ks[k], top));
    }
}

/// The var declared names of a list of items are those of its items put together.
proof fn lemma_var_cat(
    a: AstV,
    ts: Stream,
    toks: Seq<DTok>,
    arr: Seq<Vec<Decl>>,
    top: bool,
    n: int,
    ks: Seq<int>,
    k: int,
)
    requires
        inv_v(a, ts, toks, arr, top, n),
        arr.len() >= n,
        forall|q: int| 0 <= q < ks.len() ==> 0 <= #[trigger] ks[q] < n,
    ensures
        dn(toks, cat_d(arr, ks, k)) =~= (if top {
            top_var_names_list(a, ts, n, ks, k)
        } else {
            var_names_list(a, ts, n, ks, k)
        }),
    decreases ks.len() - k,
{
    if 0 <= k < ks.len() {
        lemma_var_cat(a, ts, toks, arr, top, n, ks, k + 1);
        lemma_decls_add(toks, arr[ks[k]]@, cat_d(arr, ks, k + 1));
        assert(dn(toks, arr[ks[k]]@) =~= var_names_item(a, ts, ks[k], top));
        if top {
            assert(top_var_names_list(a, ts, n, ks, k) =~= var_names_sub_top(a, ts, n, ks[k], true)
                + top_var_names_list(a, ts, n, ks, k + 1));
            assert(var_names_sub_top(a, ts, n, ks[k], true) =~= var_names_item(a, ts, ks[k], true));
        } else {
            assert(var_names_list(a, ts, n, ks, k) =~= var_names_sub(a, ts, n, ks[k]) + var_names_list(
                a,
                ts,
                n,
                ks,
                k + 1,
            ));
            assert(var_names_sub(a, ts, n, ks[k]) =~= var_names_item(a, ts, ks[k], false));
        }
    }
}

/// The var declared names of child `i` of node `m`, as a `var_names_sub` (not top-level) or
/// the item itself.
proof fn lemma_kid_var(a: AstV, ts: Stream, toks: Seq<DTok>, arr: Seq<Vec<Decl>>, top: bool, m: int, i: int)
    requires
        inv_v(a, ts, toks, arr, top, m),
        arr.len() >= m,
        forall|q: int| 0 <= q < a.nodes[m].children.len() ==> 0 <= #[trigger] a.nodes[m].children[q] < m,
    ensures
        dn(toks, kid_spec(arr, a.nodes[m].children, i)) =~= var_names_sub_top(
            a,
            ts,
            m,
            kid(a.nodes[m].children, i),
            top,
        ),
{
}

/// The lexically declared names of child `i` of node `m`.
proof fn lemma_kid_lex(a: AstV, ts: Stream, toks: Seq<DTok>, arr: Seq<Vec<Decl>>, top: bool, m: int, i: int)
    requires
        inv_l(a, ts, toks, arr, top, m),
        arr.len() >= m,
        forall|q: int| 0 <= q < a.nodes[m].children.len() ==> 0 <= #[trigger] a.nodes[m].children[q] < m,
    ensures
        decls_of(toks, kid_spec(arr, a.nodes[m].children, i)) =~= (if 0 <= kid(a.nodes[m].children, i)
            < m {
            lex_names_item(a, ts, kid(a.nodes[m].children, i), top)
        } else {
            Seq::empty()
        }),
{
}

/// The declaration of the name of the `BindingIdentifier` node `c`.
fn decl_of_ident(
    tk: &Tk,
    nodes: &[Node],
    c: usize,
    pf: bool,
    Ghost(ts): Ghost<Stream>,
) -> (r: Option<Decl>)
    requires
        c < nodes.len(),
        ast_wf(arena_of(nodes@)),
        toks_match(tk.src@, tk.toks@, ts),
        starts_inc(ts),
    ensures
        match r {
            Some(d) => d.x < tk.toks@.len() && d.pf == pf && tk.toks@[d.x as int].name@ =~= name_of(
                arena_of(nodes@),
                ts,
                c as int,
            ),
            None => true,
        },
{
    let toks = tk.toks;
    let x = match node_token(nodes, toks, tk.by_start, c) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        assert(dtok_matches(tk.src@, toks@[x as int], ts.toks[x as int]));
        lemma_node_tok_at(a, ts, c as int, x as int);
    }
    Some(Decl { x, pf })
}

/// The preconditions the per-node computations share.
pub open spec fn names_pre(tk: &Tk, nodes: Seq<Node>, ts: Stream, m: int) -> bool {
    let a = arena_of(nodes);
    0 <= m < nodes.len() && ast_wf(a) && toks_match(tk.src@, tk.toks@, ts) && starts_inc(ts)
        && tk.bn.len() == nodes.len() && bn_inv(a, ts, tk.toks@, tk.bn@, nodes.len() as int)
}

/// The children of node `m` are before it.
proof fn lemma_kids_before(a: AstV, m: int)
    requires
        ast_wf(a),
        0 <= m < a.nodes.len(),
    ensures
        forall|q: int| 0 <= q < a.nodes[m].children.len() ==> 0 <= #[trigger] a.nodes[m].children[q] < m,
{
}

/// The lexically declared names of node `m`, not top-level and top-level.
#[verifier::rlimit(400)]
pub fn item_lex(tk: &Tk, nodes: &[Node], m: usize, lf: &[Vec<Decl>], Ghost(ts): Ghost<Stream>) -> (r: Option<
    (Vec<Decl>, Vec<Decl>),
>)
    requires
        names_pre(tk, nodes@, ts, m as int),
        lf.len() == m,
        inv_l(arena_of(nodes@), ts, tk.toks@, lf@, false, m as int),
    ensures
        match r {
            Some((l1, l2)) => {
                let a = arena_of(nodes@);
                decl_ok(tk.toks@, l1@) && decl_ok(tk.toks@, l2@) && decls_of(tk.toks@, l1@) =~= lex_names_item(
                    a,
                    ts,
                    m as int,
                    false,
                ) && decls_of(tk.toks@, l2@) =~= lex_names_item(a, ts, m as int, true)
            },
            None => true,
        },
{
    let ghost a = arena_of(nodes@);
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].children.len() == nd.children.len());
        lemma_kids_before(a, m as int);
    }
    let kind = nd.kind;
    match kind {
        NodeKind::LexicalDeclaration => {
            let names = match tk.bn.get(m) {
                Some(v) => v,
                None => {
                    return None;
                },
            };
            let l1 = decls_from_names(names.as_slice());
            let l2 = decls_from_names(names.as_slice());
            proof {
                assert(tk.bn@[m as int] == names);
                assert(decls_of(tk.toks@, l1@) =~= bound_names(a, ts, m as int).map_values(
                    |n: Seq<u32>| DeclName { name: n, plain_function: false },
                ));
                assert(decl_ok(tk.toks@, l1@));
            }
            Some((l1, l2))
        },
        NodeKind::ClassDeclaration | NodeKind::FunctionDeclaration | NodeKind::GeneratorDeclaration
        | NodeKind::AsyncFunctionDeclaration | NodeKind::AsyncGeneratorDeclaration => {
            let k0 = match kid_kind(nodes, m, 0) {
                Some(k) => k,
                None => {
                    return None;
                },
            };
            let is_class = matches!(kind, NodeKind::ClassDeclaration);
            if !matches!(k0, NodeKind::BindingIdentifier) {
                proof {
                    assert(decls_of(tk.toks@, Seq::<Decl>::empty()) =~= Seq::<DeclName>::empty());
                }
                return Some((Vec::new(), Vec::new()));
            }
            let c0 = match nd.children.as_slice().get(ZERO) {
                Some(c) => *c as usize,
                None => {
                    return None;
                },
            };
            proof {
                assert(a.nodes[m as int].children[0] == c0 as int);
                lemma_child_before(a, m as int, 0);
            }
            let pf = matches!(kind, NodeKind::FunctionDeclaration);
            let d = match decl_of_ident(tk, nodes, c0, if is_class {
                false
            } else {
                pf
            }, Ghost(ts)) {
                Some(d) => d,
                None => {
                    return None;
                },
            };
            let l1 = vec![d];
            let l2: Vec<Decl> = if is_class {
                vec![d]
            } else {
                Vec::new()
            };
            proof {
                assert(decls_of(tk.toks@, l1@) =~= seq![DeclName {
                    name: name_of(a, ts, c0 as int),
                    plain_function: if is_class {
                        false
                    } else {
                        pf
                    },
                }]);
                assert(decl_ok(tk.toks@, l1@));
                assert(decl_ok(tk.toks@, l2@));
                if is_class {
                    assert(decls_of(tk.toks@, l2@) =~= seq![DeclName {
                        name: name_of(a, ts, c0 as int),
                        plain_function: false,
                    }]);
                } else {
                    assert(decls_of(tk.toks@, l2@) =~= Seq::<DeclName>::empty());
                }
            }
            Some((l1, l2))
        },
        NodeKind::LabelledStatement => {
            let l1 = match kid_d(nodes, lf, m, 1) {
                Some(v) => v,
                None => {
                    return None;
                },
            };
            proof {
                lemma_kid_lex(a, ts, tk.toks@, lf@, false, m as int, 1);
                lemma_kid_ok(tk.toks@, lf@, a.nodes[m as int].children, 1, m as int);
                assert(decls_of(tk.toks@, Seq::<Decl>::empty()) =~= Seq::<DeclName>::empty());
            }
            Some((l1, Vec::new()))
        },
        NodeKind::ImportDeclaration | NodeKind::ExportDeclaration => None,
        _ => {
            proof {
                assert(decls_of(tk.toks@, Seq::<Decl>::empty()) =~= Seq::<DeclName>::empty());
            }
            Some((Vec::new(), Vec::new()))
        },
    }
}

/// `dn` of three children's declarations put together is the three `var_names_sub`.
proof fn lemma_sum3_dn(a: AstV, ts: Stream, toks: Seq<DTok>, vf: Seq<Vec<Decl>>, m: int, i: int, j: int, l: int)
    requires
        inv_v(a, ts, toks, vf, false, m),
        vf.len() >= m,
        0 <= m < a.nodes.len(),
        forall|q: int| 0 <= q < a.nodes[m].children.len() ==> 0 <= #[trigger] a.nodes[m].children[q] < m,
    ensures
        ({
            let ks = a.nodes[m].children;
            dn(toks, kid_spec(vf, ks, i) + kid_spec(vf, ks, j) + kid_spec(vf, ks, l)) =~= var_names_sub(
                a,
                ts,
                m,
                kid(ks, i),
            ) + var_names_sub(a, ts, m, kid(ks, j)) + var_names_sub(a, ts, m, kid(ks, l))
        }),
{
    let ks = a.nodes[m].children;
    lemma_kid_var(a, ts, toks, vf, false, m, i);
    lemma_kid_var(a, ts, toks, vf, false, m, j);
    lemma_kid_var(a, ts, toks, vf, false, m, l);
    lemma_decls_add(toks, kid_spec(vf, ks, i), kid_spec(vf, ks, j));
    lemma_decls_add(toks, kid_spec(vf, ks, i) + kid_spec(vf, ks, j), kid_spec(vf, ks, l));
    assert(var_names_sub_top(a, ts, m, kid(ks, i), false) =~= var_names_sub(a, ts, m, kid(ks, i)));
    assert(var_names_sub_top(a, ts, m, kid(ks, j), false) =~= var_names_sub(a, ts, m, kid(ks, j)));
    assert(var_names_sub_top(a, ts, m, kid(ks, l), false) =~= var_names_sub(a, ts, m, kid(ks, l)));
}

/// The var declared names of node `m` that are a sum of up to three children's, the same
/// whether top-level or not.
#[verifier::rlimit(400)]
fn item_var_sum(
    nodes: &[Node],
    Ghost(toks): Ghost<Seq<DTok>>,
    vf: &[Vec<Decl>],
    m: usize,
    ix: (usize, usize, usize),
    Ghost(ts): Ghost<Stream>,
) -> (r: Option<Vec<Decl>>)
    requires
        m < nodes.len(),
        ast_wf(arena_of(nodes@)),
        vf.len() == m,
        inv_v(arena_of(nodes@), ts, toks, vf@, false, m as int),
    ensures
        match r {
            Some(v) => {
                let a = arena_of(nodes@);
                decl_ok(toks, v@) && dn(toks, v@) =~= var_names_sub(
                    a,
                    ts,
                    m as int,
                    kid(a.nodes[m as int].children, ix.0 as int),
                ) + var_names_sub(a, ts, m as int, kid(a.nodes[m as int].children, ix.1 as int))
                    + var_names_sub(a, ts, m as int, kid(a.nodes[m as int].children, ix.2 as int))
            },
            None => true,
        },
{
    let v = match sum3(nodes, vf, m, ix.0, ix.1, ix.2) {
        Some(v) => v,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        lemma_kids_before(a, m as int);
        lemma_sum3_dn(a, ts, toks, vf@, m as int, ix.0 as int, ix.1 as int, ix.2 as int);
        let ks = a.nodes[m as int].children;
        lemma_kid_ok(toks, vf@, ks, ix.0 as int, m as int);
        lemma_kid_ok(toks, vf@, ks, ix.1 as int, m as int);
        lemma_kid_ok(toks, vf@, ks, ix.2 as int, m as int);
        lemma_ok_add(toks, kid_spec(vf@, ks, ix.0 as int), kid_spec(vf@, ks, ix.1 as int));
        lemma_ok_add(
            toks,
            kid_spec(vf@, ks, ix.0 as int) + kid_spec(vf@, ks, ix.1 as int),
            kid_spec(vf@, ks, ix.2 as int),
        );
    }
    Some(v)
}

/// A kind whose var declared names depend on whether the item is top-level, or that
/// this module does not cover.
pub open spec fn var_special(k: NodeKind) -> bool {
    k == NodeKind::LabelledStatement || k == NodeKind::FunctionDeclaration || k
        == NodeKind::GeneratorDeclaration || k == NodeKind::AsyncFunctionDeclaration || k
        == NodeKind::AsyncGeneratorDeclaration || k == NodeKind::ForInStatement || k
        == NodeKind::ForOfStatement || k == NodeKind::ImportDeclaration || k
        == NodeKind::ExportDeclaration
}

/// The var declared names of node `m` of a kind that is not [`var_special`]: the same whether
/// top-level or not.
#[verifier::rlimit(800)]
fn item_var_same(tk: &Tk, nodes: &[Node], m: usize, vf: &[Vec<Decl>], Ghost(ts): Ghost<Stream>) -> (r: Option<
    Vec<Decl>,
>)
    requires
        names_pre(tk, nodes@, ts, m as int),
        vf.len() == m,
        inv_v(arena_of(nodes@), ts, tk.toks@, vf@, false, m as int),
        !var_special(nodes@[m as int].kind),
    ensures
        match r {
            Some(v) => {
                let a = arena_of(nodes@);
                decl_ok(tk.toks@, v@) && dn(tk.toks@, v@) =~= var_names_item(a, ts, m as int, false)
                    && dn(tk.toks@, v@) =~= var_names_item(a, ts, m as int, true)
            },
            None => true,
        },
{
    let ghost a = arena_of(nodes@);
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].children.len() == nd.children.len());
        lemma_kids_before(a, m as int);
        assert(dn(tk.toks@, Seq::<Decl>::empty()) =~= Seq::<Seq<u32>>::empty());
    }
    let toks = Ghost(tk.toks@);
    let kind = nd.kind;
    let none = usize::MAX;
    match kind {
        NodeKind::VariableStatement | NodeKind::VariableDeclarationList => {
            let names = match tk.bn.get(m) {
                Some(v) => v,
                None => {
                    return None;
                },
            };
            let v = decls_from_names(names.as_slice());
            proof {
                assert(tk.bn@[m as int] == names);
                assert(dn(tk.toks@, v@) =~= bound_names(a, ts, m as int));
                assert(decl_ok(tk.toks@, v@));
            }
            Some(v)
        },
        NodeKind::BlockStatement | NodeKind::SwitchStatement | NodeKind::CaseClause
        | NodeKind::DefaultClause => {
            let from: usize = if matches!(kind, NodeKind::BlockStatement | NodeKind::DefaultClause) {
                0
            } else {
                1
            };
            let v = match cat_exec(nodes, vf, m, from) {
                Some(v) => v,
                None => {
                    return None;
                },
            };
            proof {
                let ks = a.nodes[m as int].children;
                lemma_var_cat(a, ts, tk.toks@, vf@, false, m as int, ks, from as int);
                lemma_cat_ok(tk.toks@, vf@, ks, from as int, m as int);
            }
            Some(v)
        },
        NodeKind::IfStatement => item_var_sum(nodes, toks, vf, m, (1, 2, none), Ghost(ts)),
        NodeKind::DoWhileStatement | NodeKind::Finally => item_var_sum(nodes, toks, vf, m, (0, none, none), Ghost(ts)),
        NodeKind::WhileStatement | NodeKind::WithStatement => item_var_sum(nodes, toks, vf, m, (1, none, none), Ghost(ts)),
        NodeKind::ForStatement => item_var_sum(nodes, toks, vf, m, (0, 3, none), Ghost(ts)),
        NodeKind::TryStatement => item_var_sum(nodes, toks, vf, m, (0, 1, 2), Ghost(ts)),
        NodeKind::Catch => item_var_sum(nodes, toks, vf, m, (1, none, none), Ghost(ts)),
        _ => Some(Vec::new()),
    }
}

/// The var declared names of node `m`, not top-level and top-level.
#[verifier::rlimit(800)]
pub fn item_var(
    tk: &Tk,
    nodes: &[Node],
    m: usize,
    vf: &[Vec<Decl>],
    Ghost(ts): Ghost<Stream>,
) -> (r: Option<(Vec<Decl>, Vec<Decl>)>)
    requires
        names_pre(tk, nodes@, ts, m as int),
        vf.len() == m,
        inv_v(arena_of(nodes@), ts, tk.toks@, vf@, false, m as int),
    ensures
        match r {
            Some((v1, v2)) => {
                let a = arena_of(nodes@);
                decl_ok(tk.toks@, v1@) && decl_ok(tk.toks@, v2@) && dn(tk.toks@, v1@) =~= var_names_item(
                    a,
                    ts,
                    m as int,
                    false,
                ) && dn(tk.toks@, v2@) =~= var_names_item(a, ts, m as int, true)
            },
            None => true,
        },
{
    let ghost a = arena_of(nodes@);
    let kind = match nodes.get(m) {
        Some(x) => x.kind,
        None => {
            return None;
        },
    };
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(a.nodes[m as int].kind == kind);
        assert(dn(tk.toks@, Seq::<Decl>::empty()) =~= Seq::<Seq<u32>>::empty());
    }
    match kind {
        NodeKind::FunctionDeclaration | NodeKind::GeneratorDeclaration | NodeKind::AsyncFunctionDeclaration
        | NodeKind::AsyncGeneratorDeclaration => {
            let k0 = match kid_kind(nodes, m, 0) {
                Some(k) => k,
                None => {
                    return None;
                },
            };
            if !matches!(k0, NodeKind::BindingIdentifier) {
                return Some((Vec::new(), Vec::new()));
            }
            let c0 = match nodes.get(m) {
                Some(nd) => match nd.children.as_slice().get(ZERO) {
                    Some(c) => *c as usize,
                    None => {
                        return None;
                    },
                },
                None => {
                    return None;
                },
            };
            proof {
                assert(a.nodes[m as int].children.len() > 0);
                assert(a.nodes[m as int] == nodes@[m as int]@);
                lemma_child_before(a, m as int, 0);
            }
            let d = match decl_of_ident(tk, nodes, c0, false, Ghost(ts)) {
                Some(d) => d,
                None => {
                    return None;
                },
            };
            proof {
                assert(dn(tk.toks@, seq![d]) =~= seq![name_of(a, ts, c0 as int)]);
                assert(a.nodes[m as int].children[0] == c0 as int);
            }
            Some((Vec::new(), vec![d]))
        },
        NodeKind::LabelledStatement | NodeKind::ForInStatement | NodeKind::ForOfStatement
        | NodeKind::ImportDeclaration | NodeKind::ExportDeclaration => None,
        _ => {
            let v = match item_var_same(tk, nodes, m, vf, Ghost(ts)) {
                Some(v) => v,
                None => {
                    return None;
                },
            };
            let mut w: Vec<Decl> = Vec::new();
            push_decls(&mut w, v.as_slice());
            Some((v, w))
        },
    }
}

/// The declared names of every node, bottom-up.
pub struct Names {
    /// LexicallyDeclaredNames of each node.
    pub lf: Vec<Vec<Decl>>,
    /// TopLevelLexicallyDeclaredNames.
    pub lt: Vec<Vec<Decl>>,
    /// VarDeclaredNames.
    pub vf: Vec<Vec<Decl>>,
    /// TopLevelVarDeclaredNames.
    pub vt: Vec<Vec<Decl>>,
}

/// Every node's four lists of declared names (`None` where a node is not covered).
#[verifier::rlimit(400)]
pub fn decl_names_all(tk: &Tk, nodes: &[Node], Ghost(ts): Ghost<Stream>) -> (r: Option<Names>)
    requires
        nodes.len() > 0,
        ast_wf(arena_of(nodes@)),
        toks_match(tk.src@, tk.toks@, ts),
        starts_inc(ts),
        tk.bn.len() == nodes.len(),
        bn_inv(arena_of(nodes@), ts, tk.toks@, tk.bn@, nodes.len() as int),
    ensures
        match r {
            Some(nm) => {
                let a = arena_of(nodes@);
                let n = nodes.len() as int;
                nm.lf.len() == nodes.len() && nm.lt.len() == nodes.len() && nm.vf.len() == nodes.len()
                    && nm.vt.len() == nodes.len() && inv_l(a, ts, tk.toks@, nm.lf@, false, n) && inv_l(
                    a,
                    ts,
                    tk.toks@,
                    nm.lt@,
                    true,
                    n,
                ) && inv_v(a, ts, tk.toks@, nm.vf@, false, n) && inv_v(a, ts, tk.toks@, nm.vt@, true, n)
            },
            None => true,
        },
{
    let ghost a = arena_of(nodes@);
    let n = nodes.len();
    let mut lf: Vec<Vec<Decl>> = Vec::new();
    let mut lt: Vec<Vec<Decl>> = Vec::new();
    let mut vf: Vec<Vec<Decl>> = Vec::new();
    let mut vt: Vec<Vec<Decl>> = Vec::new();
    let mut m: usize = 0;
    while m < n
        invariant
            m <= n,
            n == nodes.len(),
            lf.len() == m,
            lt.len() == m,
            vf.len() == m,
            vt.len() == m,
            a == arena_of(nodes@),
            ast_wf(a),
            toks_match(tk.src@, tk.toks@, ts),
            starts_inc(ts),
            tk.bn.len() == nodes.len(),
            bn_inv(a, ts, tk.toks@, tk.bn@, nodes.len() as int),
            inv_l(a, ts, tk.toks@, lf@, false, m as int),
            inv_l(a, ts, tk.toks@, lt@, true, m as int),
            inv_v(a, ts, tk.toks@, vf@, false, m as int),
            inv_v(a, ts, tk.toks@, vt@, true, m as int),
        decreases n - m,
    {
        let (l1, l2) = match item_lex(tk, nodes, m, lf.as_slice(), Ghost(ts)) {
            Some(p) => p,
            None => {
                return None;
            },
        };
        let (v1, v2) = match item_var(tk, nodes, m, vf.as_slice(), Ghost(ts)) {
            Some(p) => p,
            None => {
                return None;
            },
        };
        let ghost (olf, olt, ovf, ovt) = (lf@, lt@, vf@, vt@);
        lf.push(l1);
        lt.push(l2);
        vf.push(v1);
        vt.push(v2);
        proof {
            assert forall|j: int| 0 <= j < m as int + 1 implies {
                let v = (#[trigger] lf@[j])@;
                decl_ok(tk.toks@, v) && decls_of(tk.toks@, v) =~= lex_names_item(a, ts, j, false)
            } by {
                if j < m as int {
                    assert(lf@[j] == olf[j]);
                }
            }
            assert forall|j: int| 0 <= j < m as int + 1 implies {
                let v = (#[trigger] lt@[j])@;
                decl_ok(tk.toks@, v) && decls_of(tk.toks@, v) =~= lex_names_item(a, ts, j, true)
            } by {
                if j < m as int {
                    assert(lt@[j] == olt[j]);
                }
            }
            assert forall|j: int| 0 <= j < m as int + 1 implies {
                let v = (#[trigger] vf@[j])@;
                decl_ok(tk.toks@, v) && dn(tk.toks@, v) =~= var_names_item(a, ts, j, false)
            } by {
                if j < m as int {
                    assert(vf@[j] == ovf[j]);
                }
            }
            assert forall|j: int| 0 <= j < m as int + 1 implies {
                let v = (#[trigger] vt@[j])@;
                decl_ok(tk.toks@, v) && dn(tk.toks@, v) =~= var_names_item(a, ts, j, true)
            } by {
                if j < m as int {
                    assert(vt@[j] == ovt[j]);
                }
            }
        }
        m = m.saturating_add(1);
    }
    Some(Names { lf, lt, vf, vt })
}

// ---------------------------------------------------------------------
// The rules that read the declared names.
// ---------------------------------------------------------------------

/// `tk.nm` holds the declared names of every node.
pub open spec fn names_inv(tk: &Tk, nodes: Seq<Node>, ts: Stream) -> bool {
    let a = arena_of(nodes);
    let n = nodes.len() as int;
    tk.nm.lf.len() == nodes.len() && tk.nm.lt.len() == nodes.len() && tk.nm.vf.len() == nodes.len()
        && tk.nm.vt.len() == nodes.len() && inv_l(a, ts, tk.toks@, tk.nm.lf@, false, n) && inv_l(
        a,
        ts,
        tk.toks@,
        tk.nm.lt@,
        true,
        n,
    ) && inv_v(a, ts, tk.toks@, tk.nm.vf@, false, n) && inv_v(a, ts, tk.toks@, tk.nm.vt@, true, n)
}

/// No name of `ds` is declared twice, except by plain function declarations in sloppy mode code.
pub fn forbid_dup_exec(toks: &[DTok], ds: &[Decl], strict: bool) -> (r: bool)
    requires
        decl_ok(toks@, ds@),
    ensures
        r ==> !has_forbidden_duplicate(decls_of(toks@, ds@), strict),
{
    let len = ds.len();
    let mut i: usize = 0;
    while i < len
        invariant
            len == ds.len(),
            i <= len,
            decl_ok(toks@, ds@),
            forall|x: int, y: int|
                0 <= x < i && x < y < len ==> !(dn(toks@, ds@)[x] =~= dn(toks@, ds@)[y] && !(!strict
                    && ds@[x].pf && ds@[y].pf)),
        decreases len - i,
    {
        let di = match ds.get(i) {
            Some(d) => *d,
            None => {
                return false;
            },
        };
        let ni = match toks.get(di.x) {
            Some(t) => t,
            None => {
                return false;
            },
        };
        let mut j: usize = i.saturating_add(1);
        while j < len
            invariant
                len == ds.len(),
                i < len,
                i < j,
                j <= len,
                decl_ok(toks@, ds@),
                di == ds@[i as int],
                ni == &toks@[di.x as int],
                forall|x: int, y: int|
                    0 <= x < i && x < y < len ==> !(dn(toks@, ds@)[x] =~= dn(toks@, ds@)[y] && !(
                    !strict && ds@[x].pf && ds@[y].pf)),
                forall|y: int|
                    i < y < j ==> !(dn(toks@, ds@)[i as int] =~= dn(toks@, ds@)[y] && !(!strict
                        && ds@[i as int].pf && ds@[y].pf)),
            decreases len - j,
        {
            let dj = match ds.get(j) {
                Some(d) => *d,
                None => {
                    return false;
                },
            };
            let nj = match toks.get(dj.x) {
                Some(t) => t,
                None => {
                    return false;
                },
            };
            if seq_eq(ni.name.as_slice(), nj.name.as_slice()) && !(!strict && di.pf && dj.pf) {
                return false;
            }
            j = j.saturating_add(1);
        }
        i = i.saturating_add(1);
    }
    proof {
        let dd = decls_of(toks@, ds@);
        assert forall|x: int, y: int|
            0 <= x < y < dd.len() implies !(#[trigger] decl_name(dd, x) =~= #[trigger] decl_name(dd, y)
            && !(!strict && dd[x].plain_function && dd[y].plain_function)) by {
            assert(x < len && y < len);
            assert(decl_name(dd, x) == dn(toks@, ds@)[x]);
            assert(decl_name(dd, y) == dn(toks@, ds@)[y]);
        }
    }
    true
}

/// No name is in both `xs` and `ys`.
pub fn no_intersect_dd(toks: &[DTok], xs: &[Decl], ys: &[Decl]) -> (r: bool)
    requires
        decl_ok(toks@, xs@),
        decl_ok(toks@, ys@),
    ensures
        r ==> !intersects(dn(toks@, xs@), dn(toks@, ys@)),
{
    let xl = xs.len();
    let yl = ys.len();
    let mut i: usize = 0;
    while i < xl
        invariant
            xl == xs.len(),
            yl == ys.len(),
            i <= xl,
            decl_ok(toks@, xs@),
            decl_ok(toks@, ys@),
            forall|x: int, y: int|
                0 <= x < i && 0 <= y < yl ==> !(dn(toks@, xs@)[x] =~= dn(toks@, ys@)[y]),
        decreases xl - i,
    {
        let dx = match xs.get(i) {
            Some(d) => *d,
            None => {
                return false;
            },
        };
        let nx = match toks.get(dx.x) {
            Some(t) => t,
            None => {
                return false;
            },
        };
        let mut j: usize = 0;
        while j < yl
            invariant
                xl == xs.len(),
                yl == ys.len(),
                i < xl,
                j <= yl,
                decl_ok(toks@, xs@),
                decl_ok(toks@, ys@),
                dx == xs@[i as int],
                nx == &toks@[dx.x as int],
                forall|x: int, y: int|
                    0 <= x < i && 0 <= y < yl ==> !(dn(toks@, xs@)[x] =~= dn(toks@, ys@)[y]),
                forall|y: int| 0 <= y < j ==> !(dn(toks@, xs@)[i as int] =~= dn(toks@, ys@)[y]),
            decreases yl - j,
        {
            let dy = match ys.get(j) {
                Some(d) => *d,
                None => {
                    return false;
                },
            };
            let ny = match toks.get(dy.x) {
                Some(t) => t,
                None => {
                    return false;
                },
            };
            if seq_eq(nx.name.as_slice(), ny.name.as_slice()) {
                return false;
            }
            j = j.saturating_add(1);
        }
        i = i.saturating_add(1);
    }
    proof {
        assert forall|x: int, y: int|
            0 <= x < dn(toks@, xs@).len() && 0 <= y < dn(toks@, ys@).len() implies !(
            #[trigger] dn(toks@, xs@)[x] =~= #[trigger] dn(toks@, ys@)[y]) by {
            assert(x < xl && y < yl);
        }
    }
    true
}

/// `list_early` of the statement list that is the children of node `m`.
#[verifier::rlimit(400)]
pub fn list_early_exec(tk: &Tk, nodes: &[Node], m: usize, strict: bool, top: bool, Ghost(ts): Ghost<Stream>) -> (r: bool)
    requires
        names_pre(tk, nodes@, ts, m as int),
        names_inv(tk, nodes@, ts),
    ensures
        r ==> list_early(arena_of(nodes@), ts, m as int, arena_of(nodes@).nodes[m as int].children, strict, top),
{
    let ghost a = arena_of(nodes@);
    let toks = tk.toks;
    let lexa: &Vec<Vec<Decl>> = if top {
        &tk.nm.lt
    } else {
        &tk.nm.lf
    };
    let vara: &Vec<Vec<Decl>> = if top {
        &tk.nm.vt
    } else {
        &tk.nm.vf
    };
    let lex = match cat_exec(nodes, lexa.as_slice(), m, 0) {
        Some(v) => v,
        None => {
            return false;
        },
    };
    let vars = match cat_exec(nodes, vara.as_slice(), m, 0) {
        Some(v) => v,
        None => {
            return false;
        },
    };
    proof {
        lemma_kids_before(a, m as int);
        let ks = a.nodes[m as int].children;
        let la = if top {
            tk.nm.lt@
        } else {
            tk.nm.lf@
        };
        let va = if top {
            tk.nm.vt@
        } else {
            tk.nm.vf@
        };
        assert(arr_ok(toks@, la, m as int));
        assert(arr_ok(toks@, va, m as int));
        lemma_cat_ok(toks@, la, ks, 0, m as int);
        lemma_cat_ok(toks@, va, ks, 0, m as int);
        assert(lexa@ == la);
        assert(vara@ == va);
        lemma_lex_cat(a, ts, toks@, la, top, m as int, ks, 0);
        lemma_var_cat(a, ts, toks@, va, top, m as int, ks, 0);
    }
    let ok1 = forbid_dup_exec(toks, lex.as_slice(), strict);
    let ok2 = no_intersect_dd(toks, lex.as_slice(), vars.as_slice());
    proof {
        lemma_dn_plain(toks@, lex@);
    }
    ok1 && ok2
}

/// The `LexicalDeclaration` node `m` has no `let` binding, no name twice, and an initializer for
/// each `const` (`early_local`, §14.3.1.1).
#[verifier::rlimit(400)]
pub fn lexical_decl_exec(tk: &Tk, nodes: &[Node], m: usize, Ghost(ts): Ghost<Stream>) -> (r: bool)
    requires
        names_pre(tk, nodes@, ts, m as int),
        arena_of(nodes@).nodes[m as int].kind == NodeKind::LexicalDeclaration,
    ensures
        r ==> ({
            let a = arena_of(nodes@);
            let nd = a.nodes[m as int];
            let bn = bound_names(a, ts, m as int);
            !has_name(bn, sv("let"@)) && !has_duplicate(bn) && (nd.op == Op::Const ==> forall|k: int|
                0 <= k < nd.children.len() ==> kd(a, kid(kids(a, #[trigger] nd.children[k]), 1))
                    != NodeKind::Absent)
        }),
{
    let ghost a = arena_of(nodes@);
    let toks = tk.toks;
    let names = match tk.bn.get(m) {
        Some(v) => v,
        None => {
            return false;
        },
    };
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    proof {
        assert(tk.bn@[m as int] == names);
        assert(bound_names(a, ts, m as int) =~= names_of(toks@, names@));
        assert(idx_ok(toks@, names@));
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].op == nd.op);
        assert(a.nodes[m as int].children.len() == nd.children.len());
        lemma_words_early();
    }
    // No binding named `let`.
    let len = names.len();
    let mut i: usize = 0;
    while i < len
        invariant
            len == names.len(),
            i <= len,
            idx_ok(toks@, names@),
            forall|q: int| 0 <= q < i ==> !(names_of(toks@, names@)[q] =~= sv("let"@)),
        decreases len - i,
    {
        let t = match names.get(i) {
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
        proof {
            lemma_words_early();
            assert(t == &toks@[names@[i as int] as int]);
        }
        if seq_eq(t.name.as_slice(), &[0x6C, 0x65, 0x74]) {
            return false;
        }
        i = i.saturating_add(1);
    }
    if !no_dup_exec(toks, names.as_slice()) {
        return false;
    }
    if matches!(nd.op, Op::Const) {
        let cl = nd.children.len();
        let mut k: usize = 0;
        while k < cl
            invariant
                cl == nd.children.len(),
                k <= cl,
                m < nodes.len(),
                nd == &nodes@[m as int],
                a == arena_of(nodes@),
                ast_wf(a),
                cl == a.nodes[m as int].children.len(),
                forall|q: int|
                    0 <= q < k ==> kd(a, kid(kids(a, #[trigger] a.nodes[m as int].children[q]), 1))
                        != NodeKind::Absent,
            decreases cl - k,
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
            match kid_kind(nodes, c, 1) {
                Some(NodeKind::Absent) => {
                    return false;
                },
                Some(_) => {},
                None => {
                    return false;
                },
            }
            proof {
                assert(kids(a, c as int) == a.nodes[c as int].children);
            }
            k = k.saturating_add(1);
        }
    }
    true
}

/// A `for ( LexicalDeclaration ...; ...; ...) Statement` node `m` has no bound name that the
/// body var-declares (`early_local`, §14.7.4.1); true for any other head.
#[verifier::rlimit(400)]
pub fn for_lex_exec(tk: &Tk, nodes: &[Node], m: usize, Ghost(ts): Ghost<Stream>) -> (r: bool)
    requires
        names_pre(tk, nodes@, ts, m as int),
        names_inv(tk, nodes@, ts),
    ensures
        r ==> ({
            let a = arena_of(nodes@);
            let ks = a.nodes[m as int].children;
            kd(a, kid(ks, 0)) == NodeKind::LexicalDeclaration ==> !intersects(
                bound_names(a, ts, kid(ks, 0)),
                var_names_sub(a, ts, m as int, kid(ks, 3)),
            )
        }),
{
    let ghost a = arena_of(nodes@);
    let toks = tk.toks;
    let k0 = match kid_kind(nodes, m, 0) {
        Some(k) => k,
        None => {
            return false;
        },
    };
    if !matches!(k0, NodeKind::LexicalDeclaration) {
        return true;
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children.len() == nd.children.len());
        lemma_kids_before(a, m as int);
    }
    let (c0, c3) = match (nd.children.as_slice().get(ZERO), nd.children.as_slice().get(3)) {
        (Some(x), Some(y)) => (*x as usize, *y as usize),
        _ => {
            return false;
        },
    };
    proof {
        assert(a.nodes[m as int].children[0] == c0 as int);
        assert(a.nodes[m as int].children[3] == c3 as int);
        lemma_child_before(a, m as int, 0);
        lemma_child_before(a, m as int, 3);
    }
    let names = match tk.bn.get(c0) {
        Some(v) => v,
        None => {
            return false;
        },
    };
    let body = match tk.nm.vf.get(c3) {
        Some(v) => v,
        None => {
            return false;
        },
    };
    let dd = decls_from_names(names.as_slice());
    proof {
        assert(tk.bn@[c0 as int] == names);
        assert(tk.nm.vf@[c3 as int] == body);
        assert(dn(toks@, dd@) =~= names_of(toks@, names@));
        assert(bound_names(a, ts, c0 as int) =~= dn(toks@, dd@));
        assert(decl_ok(toks@, dd@));
        assert(dn(toks@, body@) =~= var_names_item(a, ts, c3 as int, false));
        assert(var_names_sub(a, ts, m as int, c3 as int) =~= var_names_item(a, ts, c3 as int, false));
    }
    no_intersect_dd(toks, dd.as_slice(), body.as_slice())
}

/// The declarations of names that are tokens are of tokens.
pub proof fn lemma_decl_ok_names(toks: Seq<DTok>, xs: Seq<usize>)
    requires
        idx_ok(toks, xs),
    ensures
        decl_ok(toks, decls_of_names(xs)),
{
}

/// The lexically declared names of the top-level items of node `b` (a function body).
pub proof fn lemma_lex_body(a: AstV, ts: Stream, tk: &Tk, nodes: Seq<Node>, b: int)
    requires
        names_inv(tk, nodes, ts),
        a == arena_of(nodes),
        ast_wf(a),
        0 <= b < nodes.len(),
    ensures
        decl_ok(tk.toks@, cat_d(tk.nm.lt@, a.nodes[b].children, 0)),
        decls_of(tk.toks@, cat_d(tk.nm.lt@, a.nodes[b].children, 0)) =~= lex_names_list(
            a,
            ts,
            a.nodes.len() as int,
            a.nodes[b].children,
            0,
            true,
        ),
{
    let ks = a.nodes[b].children;
    let n = nodes.len() as int;
    lemma_kids_before(a, b);
    assert forall|q: int| 0 <= q < ks.len() implies 0 <= #[trigger] ks[q] < n by {
        assert(0 <= ks[q] < b);
    }
    assert(arr_ok(tk.toks@, tk.nm.lt@, n));
    lemma_cat_ok(tk.toks@, tk.nm.lt@, ks, 0, n);
    lemma_lex_cat(a, ts, tk.toks@, tk.nm.lt@, true, n, ks, 0);
}

/// The lexically and var declared names of the statements of block `b` (not top-level).
proof fn lemma_block_names(a: AstV, ts: Stream, tk: &Tk, nodes: Seq<Node>, b: int)
    requires
        names_inv(tk, nodes, ts),
        a == arena_of(nodes),
        ast_wf(a),
        0 <= b < nodes.len(),
    ensures
        decl_ok(tk.toks@, cat_d(tk.nm.lf@, a.nodes[b].children, 0)),
        decl_ok(tk.toks@, cat_d(tk.nm.vf@, a.nodes[b].children, 0)),
        decls_of(tk.toks@, cat_d(tk.nm.lf@, a.nodes[b].children, 0)) =~= lex_names_list(
            a,
            ts,
            a.nodes.len() as int,
            a.nodes[b].children,
            0,
            false,
        ),
        dn(tk.toks@, cat_d(tk.nm.vf@, a.nodes[b].children, 0)) =~= var_names_list(
            a,
            ts,
            a.nodes.len() as int,
            a.nodes[b].children,
            0,
        ),
{
    let ks = a.nodes[b].children;
    let n = nodes.len() as int;
    lemma_kids_before(a, b);
    assert forall|q: int| 0 <= q < ks.len() implies 0 <= #[trigger] ks[q] < n by {
        assert(0 <= ks[q] < b);
    }
    assert(arr_ok(tk.toks@, tk.nm.lf@, n));
    assert(arr_ok(tk.toks@, tk.nm.vf@, n));
    lemma_cat_ok(tk.toks@, tk.nm.lf@, ks, 0, n);
    lemma_cat_ok(tk.toks@, tk.nm.vf@, ks, 0, n);
    lemma_lex_cat(a, ts, tk.toks@, tk.nm.lf@, false, n, ks, 0);
    lemma_var_cat(a, ts, tk.toks@, tk.nm.vf@, false, n, ks, 0);
}

/// The `Catch` node `m`: its parameter has no name twice, no name that its block declares lexically,
/// and, unless a plain identifier, none that it var-declares (`early_local`, §14.15.1, Annex B.3.4).
#[verifier::rlimit(400)]
pub fn catch_exec(tk: &Tk, nodes: &[Node], m: usize, Ghost(ts): Ghost<Stream>) -> (r: bool)
    requires
        names_pre(tk, nodes@, ts, m as int),
        names_inv(tk, nodes@, ts),
    ensures
        r ==> ({
            let a = arena_of(nodes@);
            let ks = a.nodes[m as int].children;
            let bn = bound_names(a, ts, kid(ks, 0));
            let bk = kids(a, kid(ks, 1));
            let nb = a.nodes.len() as int;
            !has_duplicate(bn) && !intersects(bn, plain_names(lex_names_list(a, ts, nb, bk, 0, false)))
                && (kd(a, kid(ks, 0)) != NodeKind::BindingIdentifier ==> !intersects(
                bn,
                var_names_list(a, ts, nb, bk, 0),
            ))
        }),
{
    let ghost a = arena_of(nodes@);
    let toks = tk.toks;
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children.len() == nd.children.len());
        lemma_kids_before(a, m as int);
    }
    let (c0, c1) = match (nd.children.as_slice().get(ZERO), nd.children.as_slice().get(1)) {
        (Some(x), Some(y)) => (*x as usize, *y as usize),
        _ => {
            return false;
        },
    };
    proof {
        assert(a.nodes[m as int].children[0] == c0 as int);
        assert(a.nodes[m as int].children[1] == c1 as int);
        lemma_child_before(a, m as int, 0);
        lemma_child_before(a, m as int, 1);
    }
    let k0 = match kid_kind(nodes, m, 0) {
        Some(k) => k,
        None => {
            return false;
        },
    };
    let names = match tk.bn.get(c0) {
        Some(v) => v,
        None => {
            return false;
        },
    };
    let lex = match cat_exec(nodes, tk.nm.lf.as_slice(), c1, 0) {
        Some(v) => v,
        None => {
            return false;
        },
    };
    let vars = match cat_exec(nodes, tk.nm.vf.as_slice(), c1, 0) {
        Some(v) => v,
        None => {
            return false;
        },
    };
    let dd = decls_from_names(names.as_slice());
    proof {
        assert(tk.bn@[c0 as int] == names);
        lemma_decl_ok_names(toks@, names@);
        lemma_block_names(a, ts, tk, nodes@, c1 as int);
        lemma_dn_plain(toks@, lex@);
        assert(bound_names(a, ts, c0 as int) =~= dn(toks@, dd@));
        assert(kids(a, c1 as int) == a.nodes[c1 as int].children);
    }
    if !no_dup_exec(toks, names.as_slice()) {
        return false;
    }
    if !no_intersect_dd(toks, dd.as_slice(), lex.as_slice()) {
        return false;
    }
    let ok_vars = no_intersect_dd(toks, dd.as_slice(), vars.as_slice());
    if !matches!(k0, NodeKind::BindingIdentifier) && !ok_vars {
        return false;
    }
    true
}

} // verus!
