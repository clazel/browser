//! Checks of [`spec::d`] for the module items of §16.2: `import` and `export` in all
//! their forms, with import attributes, `export default`, `export * as ns` and string
//! `ModuleExportName`s. Dispatched from [`crate::arena_d::check_derivation`]; each
//! `check_*` has the contract of its siblings there (`node_done` of the node, in its
//! context, only if the specification's `d_module` arm follows from what the children
//! recorded and the executable tokens). The assumptions are those of [`crate::arena_d`].

use crate::arena_d::*;
use crate::arena_e::*;
use crate::ast::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// The words of the module items, as code points.
pub(crate) proof fn lemma_words_m()
    ensures
        cps("as"@) =~= seq![0x61u32, 0x73],
        cps("from"@) =~= seq![0x66u32, 0x72, 0x6F, 0x6D],
        cps("with"@) =~= seq![0x77u32, 0x69, 0x74, 0x68],
        cps("default"@) =~= seq![0x64u32, 0x65, 0x66, 0x61, 0x75, 0x6C, 0x74],
        cps("export"@) =~= seq![0x65u32, 0x78, 0x70, 0x6F, 0x72, 0x74],
        cps("*"@) =~= seq![0x2Au32],
        cps("}"@) =~= seq![0x7Du32],
        cps(":"@) =~= seq![0x3Au32],
{
    reveal_strlit("as");
    reveal_strlit("from");
    reveal_strlit("with");
    reveal_strlit("default");
    reveal_strlit("export");
    reveal_strlit("*");
    reveal_strlit("}");
    reveal_strlit(":");
    assert("as"@ =~= seq!['a', 's']);
    assert("from"@ =~= seq!['f', 'r', 'o', 'm']);
    assert("with"@ =~= seq!['w', 'i', 't', 'h']);
    assert("default"@ =~= seq!['d', 'e', 'f', 'a', 'u', 'l', 't']);
    assert("export"@ =~= seq!['e', 'x', 'p', 'o', 'r', 't']);
    assert("*"@ =~= seq!['*']);
    assert("}"@ =~= seq!['}']);
    assert(":"@ =~= seq![':']);
}

/// The executable form of `is_module_export_name_kind`.
fn name_kind(k: NodeKind) -> (r: bool)
    ensures
        r == is_module_export_name_kind(k),
{
    matches!(k, NodeKind::IdentifierName | NodeKind::StringLiteral)
}

// ---------------------------------------------------------------------
// Small nodes: `* as ns`, `a as b`, `k: "v"`.
// ---------------------------------------------------------------------

/// `NameSpaceImport : * as ImportedBinding`.
#[verifier::spinoff_prover]
proof fn lemma_ns_done(a: AstV, ts: Stream, cx: Ctx, m: int, c: int, x: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= c < m,
        0 <= x,
        x + 3 <= tn(ts),
        a.nodes[m].kind == NodeKind::NameSpaceImport,
        a.nodes[m].children =~= seq![c],
        is_p(ts, x, "*"@),
        is_kw(ts, x + 1, "as"@),
        kd(a, c) == NodeKind::BindingIdentifier,
        node_done(a, ts, c, cx, x + 2, x + 3),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[x + 2].end,
    ensures
        node_done(a, ts, m, cx, x, x + 3),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, x + 3));
    assert(a.nodes[m].children[0] == c);
    assert(dc(a, ts, m, c, cx, x + 2, x + 3));
    assert(d_module(a, ts, m, cx, x, x + 3));
    lemma_ed_of(a, ts, m, x, x + 3);
}

/// §16.2.2 `* as ImportedBinding`.
#[verifier::spinoff_prover]
pub(crate) fn check_ns_import(
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
        lemma_words_m();
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        lemma_node_view(nodes@, m as int);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::NameSpaceImport) || nd.children.len() != 1 {
        return None;
    }
    let c = match kid_of(nodes, m, 0) {
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
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if x > usize::MAX - 8 {
        return None;
    }
    let x1 = x.saturating_add(1);
    let x2 = x.saturating_add(2);
    let x3 = x.saturating_add(3);
    if !punct_at(src, nodes, toks, gaps, x, 0x2A, Ghost(GW { g, w: "*"@ }))
        || !word_at(src, nodes, toks, gaps, x1, &[0x61, 0x73], Ghost(GW { g, w: "as"@ }))
        || !matches!(kind_at(nodes, c), NodeKind::BindingIdentifier) || lo_c != x2 || hi_c != x3
        || !end_ok(src, nodes, toks, gaps, nd.end, x3, Ghost(g)) {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(x1 as int == x as int + 1);
        assert(x2 as int == x as int + 2);
        assert(x3 as int == x as int + 3);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
        }
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 0);
        lemma_ns_done(a, g.ts, g.cx, m as int, c as int, x as int);
    }
    Some((x, x3, -100))
}

/// A node of two children `name`, `x`: one token each, with the token between (`as` or `:`) or
/// nothing: `ImportSpecifier`, `ImportAttribute` and `ExportSpecifier`.
#[verifier::spinoff_prover]
proof fn lemma_pair_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    c0: int,
    c1: int,
    x: int,
    j: int,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= c0 < m,
        0 <= c1 < m,
        0 <= x,
        x < j <= tn(ts),
        a.nodes[m].children =~= seq![c0, c1],
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
        match a.nodes[m].kind {
            NodeKind::ImportSpecifier => kd(a, c1) == NodeKind::BindingIdentifier && (if kd(a, c0)
                == NodeKind::Absent {
                j == x + 1 && d(a, ts, c0, cx, x, x) && node_done(a, ts, c1, cx, x, j)
            } else {
                is_module_export_name_kind(kd(a, c0)) && is_kw(ts, x + 1, "as"@) && j == x + 3
                    && node_done(a, ts, c0, cx, x, x + 1) && node_done(a, ts, c1, cx, x + 2, j)
            }),
            NodeKind::ImportAttribute => is_module_export_name_kind(kd(a, c0)) && kd(a, c1)
                == NodeKind::StringLiteral && is_p(ts, x + 1, ":"@) && j == x + 3 && node_done(
                a,
                ts,
                c0,
                cx,
                x,
                x + 1,
            ) && node_done(a, ts, c1, cx, x + 2, j),
            NodeKind::ExportSpecifier => is_module_export_name_kind(kd(a, c0)) && node_done(
                a,
                ts,
                c0,
                cx,
                x,
                x + 1,
            ) && (if kd(a, c1) == NodeKind::Absent {
                j == x + 1 && d(a, ts, c1, cx, x + 1, x + 1)
            } else {
                is_module_export_name_kind(kd(a, c1)) && is_kw(ts, x + 1, "as"@) && j == x + 3
                    && node_done(a, ts, c1, cx, x + 2, j)
            }),
            _ => false,
        },
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == c0);
    assert(a.nodes[m].children[1] == c1);
    match a.nodes[m].kind {
        NodeKind::ImportSpecifier => {
            if kd(a, c0) == NodeKind::Absent {
                assert(dc(a, ts, m, c0, cx, x, x));
                assert(dc(a, ts, m, c1, cx, x, j));
            } else {
                assert(dc(a, ts, m, c0, cx, x, x + 1));
                assert(dc(a, ts, m, c1, cx, x + 2, j));
            }
        },
        NodeKind::ImportAttribute => {
            assert(dc(a, ts, m, c0, cx, x, x + 1));
            assert(dc(a, ts, m, c1, cx, x + 2, j));
        },
        _ => {
            assert(dc(a, ts, m, c0, cx, x, x + 1));
            if kd(a, c1) == NodeKind::Absent {
                assert(dc(a, ts, m, c1, cx, x + 1, x + 1));
            } else {
                assert(dc(a, ts, m, c1, cx, x + 2, j));
            }
        },
    }
    assert(d_module(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §16.2.2 `ImportSpecifier`, `ImportAttribute`; §16.2.3 `ExportSpecifier`.
#[verifier::spinoff_prover]
pub(crate) fn check_pair(
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
        lemma_words_m();
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        lemma_node_view(nodes@, m as int);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let kind = nd.kind;
    if !matches!(kind, NodeKind::ImportSpecifier | NodeKind::ImportAttribute | NodeKind::ExportSpecifier)
        || nd.children.len() != 2 {
        return None;
    }
    let c0 = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let c1 = match kid_of(nodes, m, 1) {
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
    if x > usize::MAX - 8 {
        return None;
    }
    let x1 = x.saturating_add(1);
    let x2 = x.saturating_add(2);
    let x3 = x.saturating_add(3);
    let k0 = kind_at(nodes, c0);
    let k1 = kind_at(nodes, c1);
    let a0 = matches!(k0, NodeKind::Absent);
    let a1 = matches!(k1, NodeKind::Absent);
    let j: usize;
    match kind {
        NodeKind::ImportSpecifier => {
            if !matches!(k1, NodeKind::BindingIdentifier) {
                return None;
            }
            let (lo1, hi1, _) = match done_at(done, c1) {
                Some(r) => r,
                None => {
                    return None;
                },
            };
            if a0 {
                if !check_absent(src, nodes, toks, gaps, c0, x, Ghost(g)) || lo1 != x || hi1 != x1 {
                    return None;
                }
                j = x1;
            } else {
                let (lo0, hi0, _) = match done_at(done, c0) {
                    Some(r) => r,
                    None => {
                        return None;
                    },
                };
                if !name_kind(k0) || lo0 != x || hi0 != x1 || lo1 != x2 || hi1 != x3
                    || !word_at(src, nodes, toks, gaps, x1, &[0x61, 0x73], Ghost(GW { g, w: "as"@ })) {
                    return None;
                }
                j = x3;
            }
        },
        NodeKind::ImportAttribute => {
            let (lo0, hi0, _) = match done_at(done, c0) {
                Some(r) => r,
                None => {
                    return None;
                },
            };
            let (lo1, hi1, _) = match done_at(done, c1) {
                Some(r) => r,
                None => {
                    return None;
                },
            };
            if !name_kind(k0) || !matches!(k1, NodeKind::StringLiteral) || lo0 != x || hi0 != x1
                || lo1 != x2 || hi1 != x3
                || !punct_at(src, nodes, toks, gaps, x1, 0x3A, Ghost(GW { g, w: ":"@ })) {
                return None;
            }
            j = x3;
        },
        _ => {
            let (lo0, hi0, _) = match done_at(done, c0) {
                Some(r) => r,
                None => {
                    return None;
                },
            };
            if !name_kind(k0) || lo0 != x || hi0 != x1 {
                return None;
            }
            if a1 {
                if !check_absent(src, nodes, toks, gaps, c1, x1, Ghost(g)) {
                    return None;
                }
                j = x1;
            } else {
                let (lo1, hi1, _) = match done_at(done, c1) {
                    Some(r) => r,
                    None => {
                        return None;
                    },
                };
                if !name_kind(k1) || lo1 != x2 || hi1 != x3
                    || !word_at(src, nodes, toks, gaps, x1, &[0x61, 0x73], Ghost(GW { g, w: "as"@ })) {
                    return None;
                }
                j = x3;
            }
        },
    }
    if !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(x1 as int == x as int + 1);
        assert(x2 as int == x as int + 2);
        assert(x3 as int == x as int + 3);
        assert(a.nodes[m as int].children =~= seq![c0 as int, c1 as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
        }
        assert(kd(a, c0 as int) == k0);
        assert(kd(a, c1 as int) == k1);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c0 as int, g.cx, 0);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c1 as int, g.cx, 1);
        lemma_pair_done(a, g.ts, g.cx, m as int, c0 as int, c1 as int, x as int, j as int);
    }
    Some((x, j, -100))
}

// ---------------------------------------------------------------------
// Braced lists: `{ a, b as c }`, `with { type: "json" }`.
// ---------------------------------------------------------------------

/// `NamedImports`, `NamedExports`: `{ list }`; `WithClause`: `with { list }`.
#[verifier::spinoff_prover]
proof fn lemma_braced_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int, s: int, e: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= x,
        s == (if a.nodes[m].kind == NodeKind::WithClause {
            x + 2
        } else {
            x + 1
        }),
        s <= e < tn(ts),
        a.nodes[m].kind == NodeKind::NamedImports || a.nodes[m].kind == NodeKind::NamedExports
            || a.nodes[m].kind == NodeKind::WithClause,
        dsep(a, ts, m, a.nodes[m].children, 0, cx, s, e, true),
        forall|k: int|
            0 <= k < a.nodes[m].children.len() ==> list_item_ok(
                a,
                #[trigger] a.nodes[m].children[k],
                if a.nodes[m].kind == NodeKind::NamedImports {
                    11int
                } else if a.nodes[m].kind == NodeKind::NamedExports {
                    15int
                } else {
                    13int
                },
            ),
        a.nodes[m].kind == NodeKind::WithClause ==> (is_kw(ts, x, "with"@) && is_p(ts, x + 1, "{"@)),
        a.nodes[m].kind != NodeKind::WithClause ==> is_p(ts, x, "{"@),
        is_p(ts, e, "}"@),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[e].end,
    ensures
        node_done(a, ts, m, cx, x, e + 1),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, e + 1));
    let kk = a.nodes[m].kind;
    assert forall|k: int| 0 <= k < a.nodes[m].children.len() implies kd(
        a,
        #[trigger] a.nodes[m].children[k],
    ) == (if kk == NodeKind::NamedImports {
        NodeKind::ImportSpecifier
    } else if kk == NodeKind::NamedExports {
        NodeKind::ExportSpecifier
    } else {
        NodeKind::ImportAttribute
    }) by {
        assert(list_item_ok(a, a.nodes[m].children[k], if kk == NodeKind::NamedImports {
            11int
        } else if kk == NodeKind::NamedExports {
            15int
        } else {
            13int
        }));
    }
    assert(all_kind2(a, a.nodes[m].children, 0, NodeKind::ImportSpecifier, NodeKind::ImportSpecifier)
        || kk != NodeKind::NamedImports);
    assert(d_module(a, ts, m, cx, x, e + 1));
    lemma_ed_of(a, ts, m, x, e + 1);
}

/// §16.2.2 `NamedImports`, `WithClause`; §16.2.3 `NamedExports`.
#[verifier::spinoff_prover]
pub(crate) fn check_braced(
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
        lemma_words_m();
        lemma_punct_text();
        lemma_brace_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        lemma_node_view(nodes@, m as int);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let kind = nd.kind;
    let with = matches!(kind, NodeKind::WithClause);
    if !(with || matches!(kind, NodeKind::NamedImports | NodeKind::NamedExports)) {
        return None;
    }
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if x > usize::MAX - 8 {
        return None;
    }
    let x1 = x.saturating_add(1);
    let x2 = x.saturating_add(2);
    let s: usize = if with { x2 } else { x1 };
    if with {
        if !word_at(src, nodes, toks, gaps, x, &[0x77, 0x69, 0x74, 0x68], Ghost(GW { g, w: "with"@ }))
            || !punct_at(src, nodes, toks, gaps, x1, 0x7B, Ghost(GW { g, w: "{"@ })) {
            return None;
        }
    } else if !punct_at(src, nodes, toks, gaps, x, 0x7B, Ghost(GW { g, w: "{"@ })) {
        return None;
    }
    let mode: u8 = if matches!(kind, NodeKind::NamedImports) {
        11
    } else if matches!(kind, NodeKind::NamedExports) {
        15
    } else {
        13
    };
    let ls = ListSpec { m, start: s, mode, trail: true };
    let e = match check_list(src, nodes, toks, gaps, done, &ls, Ghost(g)) {
        Some(e) => e,
        None => {
            return None;
        },
    };
    let e1 = e.saturating_add(1);
    if !punct_at(src, nodes, toks, gaps, e, 0x7D, Ghost(GW { g, w: "}"@ }))
        || !end_ok(src, nodes, toks, gaps, nd.end, e1, Ghost(g)) {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(x1 as int == x as int + 1);
        assert(x2 as int == x as int + 2);
        assert(e1 as int == e as int + 1);
        assert(a.nodes[m as int].kind == kind);
        assert(s as int == (if a.nodes[m as int].kind == NodeKind::WithClause {
            x as int + 2
        } else {
            x as int + 1
        }));
        assert(mode as int == (if a.nodes[m as int].kind == NodeKind::NamedImports {
            11int
        } else if a.nodes[m as int].kind == NodeKind::NamedExports {
            15int
        } else {
            13int
        }));
        lemma_braced_done(a, g.ts, g.cx, m as int, x as int, s as int, e as int);
    }
    Some((x, e1, -100))
}

// ---------------------------------------------------------------------
// `import` declarations.
// ---------------------------------------------------------------------

/// Where [`check_with_semi`] looks: child `k` of node `m`, from token `s`, the node ending at `end`.
pub struct WsSpec {
    /// The node.
    pub m: usize,
    /// The index of the child that is the optional `WithClause`.
    pub k: usize,
    /// The token the clause would start at.
    pub s: usize,
    /// Where the node's last token ends.
    pub end: usize,
}

/// Child `k` of node `m` is an optional `WithClause` starting at token `s`, then the `;`
/// (`spec::d_with_semi`); `end` is where the node's last token ends.
#[verifier::spinoff_prover]
pub(crate) fn check_with_semi(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    done: &Done,
    ws: &WsSpec,
    Ghost(g): Ghost<GCx>,
) -> (r: Option<usize>)
    requires
        ws.m < nodes.len(),
        env_ok(src@, nodes@, toks@, gaps@, g.ts),
        inv(arena_of(nodes@), g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, ws.m as int),
        kids_ok(arena_of(nodes@), done.cxs@, ws.m as int, g.cx),
    ensures
        match r {
            Some(j) => ws.k < arena_of(nodes@).nodes[ws.m as int].children.len() && d_with_semi(
                arena_of(nodes@),
                g.ts,
                ws.m as int,
                arena_of(nodes@).nodes[ws.m as int].children[ws.k as int],
                g.cx,
                ws.s as int,
                j as int,
            ) && 1 <= j && j <= toks.len() && g.ts.toks[j as int - 1].end == ws.end as int,
            None => true,
        },
{
    let (m, k, s, end) = (ws.m, ws.k, ws.s, ws.end);
    proof {
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
    }
    let c = match kid_of(nodes, m, k) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let kc = kind_at(nodes, c);
    let r: usize = if matches!(kc, NodeKind::Absent) {
        if !check_absent(src, nodes, toks, gaps, c, s, Ghost(g)) {
            return None;
        }
        s
    } else if matches!(kc, NodeKind::WithClause) {
        let (lo, hi, _) = match done_at(done, c) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if lo != s {
            return None;
        }
        hi
    } else {
        return None;
    };
    let j = match find_semi(src, nodes, toks, gaps, r, end, Ghost(g)) {
        Some(j) => j,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, k as int);
        assert(a.nodes[m as int].children[k as int] == c as int);
        assert(kd(a, c as int) == kc);
        if kc == NodeKind::WithClause {
            assert(node_done(a, g.ts, c as int, g.cx, s as int, r as int));
        }
        assert(d_with_semi(a, g.ts, m as int, c as int, g.cx, s as int, j as int));
    }
    Some(j)
}

/// `ImportClause`.
#[verifier::spinoff_prover]
proof fn lemma_import_clause_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    c0: int,
    c1: int,
    x: int,
    j: int,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= c0 < m,
        0 <= c1 < m,
        0 <= x,
        x < j <= tn(ts),
        a.nodes[m].kind == NodeKind::ImportClause,
        a.nodes[m].children =~= seq![c0, c1],
        kd(a, c0) == NodeKind::BindingIdentifier || kd(a, c0) == NodeKind::Absent,
        kd(a, c1) == NodeKind::NameSpaceImport || kd(a, c1) == NodeKind::NamedImports || kd(a, c1)
            == NodeKind::Absent,
        if kd(a, c1) == NodeKind::Absent {
            kd(a, c0) == NodeKind::BindingIdentifier && j == x + 1 && node_done(
                a,
                ts,
                c0,
                cx,
                x,
                x + 1,
            ) && d(a, ts, c1, cx, j, j)
        } else if kd(a, c0) == NodeKind::Absent {
            d(a, ts, c0, cx, x, x) && node_done(a, ts, c1, cx, x, j)
        } else {
            node_done(a, ts, c0, cx, x, x + 1) && is_p(ts, x + 1, ","@) && node_done(
                a,
                ts,
                c1,
                cx,
                x + 2,
                j,
            )
        },
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == c0);
    assert(a.nodes[m].children[1] == c1);
    if kd(a, c1) == NodeKind::Absent {
        assert(dc(a, ts, m, c0, cx, x, j));
        assert(dc(a, ts, m, c1, cx, j, j));
    } else if kd(a, c0) == NodeKind::Absent {
        assert(dc(a, ts, m, c0, cx, x, x));
        assert(dc(a, ts, m, c1, cx, x, j));
    } else {
        assert(dc(a, ts, m, c0, cx, x, x + 1));
        assert(dc(a, ts, m, c1, cx, x + 2, j));
    }
    assert(d_module(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §16.2.2 `ImportClause`.
#[verifier::spinoff_prover]
pub(crate) fn check_import_clause(
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
        lemma_words_e();
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        lemma_node_view(nodes@, m as int);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::ImportClause) || nd.children.len() != 2 {
        return None;
    }
    let c0 = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let c1 = match kid_of(nodes, m, 1) {
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
    if x > usize::MAX - 8 {
        return None;
    }
    let x1 = x.saturating_add(1);
    let x2 = x.saturating_add(2);
    let k0 = kind_at(nodes, c0);
    let k1 = kind_at(nodes, c1);
    if !(matches!(k0, NodeKind::BindingIdentifier | NodeKind::Absent)
        && matches!(k1, NodeKind::NameSpaceImport | NodeKind::NamedImports | NodeKind::Absent)) {
        return None;
    }
    let j: usize = if matches!(k1, NodeKind::Absent) {
        let (lo0, hi0, _) = match done_at(done, c0) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if !matches!(k0, NodeKind::BindingIdentifier) || lo0 != x || hi0 != x1
            || !check_absent(src, nodes, toks, gaps, c1, x1, Ghost(g)) {
            return None;
        }
        x1
    } else if matches!(k0, NodeKind::Absent) {
        let (lo1, hi1, _) = match done_at(done, c1) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if !check_absent(src, nodes, toks, gaps, c0, x, Ghost(g)) || lo1 != x {
            return None;
        }
        hi1
    } else {
        let (lo0, hi0, _) = match done_at(done, c0) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        let (lo1, hi1, _) = match done_at(done, c1) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if lo0 != x || hi0 != x1 || lo1 != x2
            || !punct_n_at(src, nodes, toks, gaps, x1, &[0x2C], Ghost(GW { g, w: ","@ })) {
            return None;
        }
        hi1
    };
    if !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(x1 as int == x as int + 1);
        assert(x2 as int == x as int + 2);
        assert(a.nodes[m as int].children =~= seq![c0 as int, c1 as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
        }
        assert(kd(a, c0 as int) == k0);
        assert(kd(a, c1 as int) == k1);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c0 as int, g.cx, 0);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c1 as int, g.cx, 1);
        lemma_import_clause_done(a, g.ts, g.cx, m as int, c0 as int, c1 as int, x as int, j as int);
    }
    Some((x, j, -100))
}

/// `ImportDeclaration`.
#[verifier::spinoff_prover]
proof fn lemma_import_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    c0: int,
    c1: int,
    c2: int,
    x: int,
    mm: int,
    j: int,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= c0 < m,
        0 <= c1 < m,
        0 <= c2 < m,
        0 <= x,
        x < j <= tn(ts),
        a.nodes[m].kind == NodeKind::ImportDeclaration,
        a.nodes[m].children =~= seq![c0, c1, c2],
        is_kw(ts, x, "import"@),
        kd(a, c1) == NodeKind::StringLiteral,
        kd(a, c0) == NodeKind::Absent || kd(a, c0) == NodeKind::ImportClause,
        if kd(a, c0) == NodeKind::Absent {
            mm == x + 1 && d(a, ts, c0, cx, x + 1, x + 1) && ed(a, ts, c0, x + 1) == x + 1
                && node_done(a, ts, c1, cx, mm, mm + 1) && d_with_semi(a, ts, m, c2, cx, mm + 1, j)
        } else {
            node_done(a, ts, c0, cx, x + 1, mm) && is_kw(ts, mm, "from"@) && node_done(
                a,
                ts,
                c1,
                cx,
                mm + 1,
                mm + 2,
            ) && d_with_semi(a, ts, m, c2, cx, mm + 2, j)
        },
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == c0);
    assert(a.nodes[m].children[1] == c1);
    assert(a.nodes[m].children[2] == c2);
    assert(dc(a, ts, m, c0, cx, x + 1, mm));
    assert(dc(a, ts, m, c1, cx, mm + if kd(a, c0) == NodeKind::Absent { 0int } else { 1int }, mm + if kd(
        a,
        c0,
    ) == NodeKind::Absent {
        1int
    } else {
        2int
    }));
    assert(d_module(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §16.2.2 `import ImportClause from "m" with {..} ;` and `import "m" with {..} ;`.
#[verifier::spinoff_prover]
pub(crate) fn check_import(
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
        lemma_words_m();
        lemma_words_e();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        lemma_node_view(nodes@, m as int);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::ImportDeclaration) || nd.children.len() != 3 {
        return None;
    }
    let c0 = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let c1 = match kid_of(nodes, m, 1) {
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
    if x > usize::MAX - 8 {
        return None;
    }
    let x1 = x.saturating_add(1);
    let k0 = kind_at(nodes, c0);
    let (lo1, hi1, _) = match done_at(done, c1) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    if !word_at(src, nodes, toks, gaps, x, &[0x69, 0x6D, 0x70, 0x6F, 0x72, 0x74], Ghost(GW { g, w: "import"@ }))
        || !matches!(kind_at(nodes, c1), NodeKind::StringLiteral)
        || !matches!(k0, NodeKind::Absent | NodeKind::ImportClause) {
        return None;
    }
    let mm: usize;
    let s: usize;
    if matches!(k0, NodeKind::Absent) {
        if !check_absent(src, nodes, toks, gaps, c0, x1, Ghost(g)) || lo1 != x1 {
            return None;
        }
        mm = x1;
        s = hi1;
    } else {
        let (lo0, hi0, _) = match done_at(done, c0) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        let h1 = hi0.saturating_add(1);
        if lo0 != x1 || !word_at(src, nodes, toks, gaps, hi0, &[0x66, 0x72, 0x6F, 0x6D], Ghost(GW { g, w: "from"@ }))
            || lo1 != h1 {
            return None;
        }
        mm = hi0;
        s = hi1;
    }
    if s != mm.saturating_add(if matches!(k0, NodeKind::Absent) { 1 } else { 2 }) || hi1 != s {
        return None;
    }
    let j = match check_with_semi(src, nodes, toks, gaps, done, &WsSpec { m, k: 2, s, end: nd.end }, Ghost(g)) {
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
        assert(x1 as int == x as int + 1);
        let c2g: int = a.nodes[m as int].children[2];
        lemma_child_before(a, m as int, 2);
        assert(a.nodes[m as int].children =~= seq![c0 as int, c1 as int, c2g]) by {
            assert(a.nodes[m as int].children.len() == 3);
        }
        assert(kd(a, c0 as int) == k0);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c0 as int, g.cx, 0);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c1 as int, g.cx, 1);
        assert(a.nodes[m as int].children[2] == c2g);
        if k0 == NodeKind::Absent {
            assert(mm as int == x as int + 1);
            assert(s as int == mm as int + 1);
        } else {
            assert(mm.saturating_add(2) as int == mm as int + 2);
            assert(s as int == mm as int + 2);
        }
        lemma_import_done(
            a,
            g.ts,
            g.cx,
            m as int,
            c0 as int,
            c1 as int,
            c2g,
            x as int,
            mm as int,
            j as int,
        );
    }
    Some((x, j, -100))
}

// ---------------------------------------------------------------------
// `export` declarations.
// ---------------------------------------------------------------------

/// The context of `export default` declarations: `[+Default]`.
pub open spec fn cx_default(cx: Ctx) -> Ctx {
    Ctx { yield_: cx.yield_, await_: cx.await_, in_: cx.in_, return_: cx.return_, deflt: true }
}

/// `ExportDeclaration`: `c0`, `c1`, `c2` are the children there are; `mm` is where `c0` ends.
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
proof fn lemma_export_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    c0: int,
    c1: int,
    c2: int,
    x: int,
    mm: int,
    j: int,
)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= c0 < m,
        0 <= c1 < m,
        0 <= c2 < m,
        0 <= x,
        x < j <= tn(ts),
        a.nodes[m].kind == NodeKind::ExportDeclaration,
        a.nodes[m].children.len() == (match a.nodes[m].op {
            Op::ExportAll => 2int,
            Op::ExportAllAs | Op::ExportFrom => 3int,
            _ => 1int,
        }),
        a.nodes[m].children[0] == c0,
        a.nodes[m].children.len() >= 2 ==> a.nodes[m].children[1] == c1,
        a.nodes[m].children.len() >= 3 ==> a.nodes[m].children[2] == c2,
        is_kw(ts, x, "export"@),
        match a.nodes[m].op {
            Op::ExportAll => is_p(ts, x + 1, "*"@) && is_kw(ts, x + 2, "from"@) && kd(a, c0)
                == NodeKind::StringLiteral && node_done(a, ts, c0, cx, x + 3, x + 4)
                && d_with_semi(a, ts, m, c1, cx, x + 4, j),
            Op::ExportAllAs => is_p(ts, x + 1, "*"@) && is_kw(ts, x + 2, "as"@)
                && is_module_export_name_kind(kd(a, c0)) && node_done(a, ts, c0, cx, x + 3, x + 4)
                && is_kw(ts, x + 4, "from"@) && kd(a, c1) == NodeKind::StringLiteral && node_done(
                a,
                ts,
                c1,
                cx,
                x + 5,
                x + 6,
            ) && d_with_semi(a, ts, m, c2, cx, x + 6, j),
            Op::ExportFrom => kd(a, c0) == NodeKind::NamedExports && kd(a, c1)
                == NodeKind::StringLiteral && node_done(a, ts, c0, cx, x + 1, mm) && is_kw(
                ts,
                mm,
                "from"@,
            ) && node_done(a, ts, c1, cx, mm + 1, mm + 2) && d_with_semi(a, ts, m, c2, cx, mm + 2, j),
            Op::ExportNamed => kd(a, c0) == NodeKind::NamedExports && node_done(
                a,
                ts,
                c0,
                cx,
                x + 1,
                mm,
            ) && semi(ts, mm, j, false),
            Op::ExportVar => kd(a, c0) == NodeKind::VariableStatement && node_done(
                a,
                ts,
                c0,
                cx,
                x + 1,
                j,
            ),
            Op::ExportDecl => is_declaration_kind(kd(a, c0)) && node_done(a, ts, c0, cx, x + 1, j),
            Op::ExportDefaultHoistable => is_kw(ts, x + 1, "default"@) && is_hoistable_kind(kd(a, c0))
                && node_done(a, ts, c0, cx_default(cx), x + 2, j),
            Op::ExportDefaultClass => is_kw(ts, x + 1, "default"@) && kd(a, c0)
                == NodeKind::ClassDeclaration && node_done(a, ts, c0, cx_default(cx), x + 2, j),
            Op::ExportDefaultExpression => is_kw(ts, x + 1, "default"@) && !is_kw(
                ts,
                x + 2,
                "function"@,
            ) && !is_kw(ts, x + 2, "async"@) && !is_kw(ts, x + 2, "class"@) && lvl(a, c0) >= 0
                && node_done(a, ts, c0, cx, x + 2, mm) && semi(ts, mm, j, false),
            _ => false,
        },
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(cx_default(cx) == Ctx {
        yield_: cx.yield_,
        await_: cx.await_,
        in_: cx.in_,
        return_: cx.return_,
        deflt: true,
    });
    match a.nodes[m].op {
        Op::ExportAll => {
            assert(dc(a, ts, m, c0, cx, x + 3, x + 4));
        },
        Op::ExportAllAs => {
            assert(dc(a, ts, m, c0, cx, x + 3, x + 4));
            assert(dc(a, ts, m, c1, cx, x + 5, x + 6));
        },
        Op::ExportFrom => {
            assert(dc(a, ts, m, c0, cx, x + 1, mm));
            assert(dc(a, ts, m, c1, cx, mm + 1, mm + 2));
        },
        Op::ExportNamed => {
            assert(dc(a, ts, m, c0, cx, x + 1, mm));
        },
        Op::ExportVar | Op::ExportDecl => {
            assert(dc(a, ts, m, c0, cx, x + 1, j));
        },
        Op::ExportDefaultHoistable | Op::ExportDefaultClass => {
            assert(dc(a, ts, m, c0, cx_default(cx), x + 2, j));
        },
        _ => {
            assert(is_assign_expr(a, c0));
            assert(dc(a, ts, m, c0, cx_in(cx, true), x + 2, mm));
        },
    }
    assert(d_module(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §16.2.3 `ExportDeclaration`, in all its forms.
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub(crate) fn check_export(
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
        cx_of(done.cxs@[m as int]) == g.cx,
        kids_ok(
            arena_of(nodes@),
            done.cxs@,
            m as int,
            if nodes@[m as int].op == Op::ExportDefaultHoistable || nodes@[m as int].op
                == Op::ExportDefaultClass {
                cx_default(g.cx)
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
        lemma_words_m();
        lemma_words_e();
        lemma_kw_text();
        lemma_punct_text();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        lemma_node_view(nodes@, m as int);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::ExportDeclaration) {
        return None;
    }
    let op = nd.op;
    let want: usize = match op {
        Op::ExportAll => 2,
        Op::ExportAllAs | Op::ExportFrom => 3,
        Op::ExportNamed | Op::ExportVar | Op::ExportDecl | Op::ExportDefaultHoistable
        | Op::ExportDefaultClass | Op::ExportDefaultExpression => 1,
        _ => {
            return None;
        },
    };
    if nd.children.len() != want {
        return None;
    }
    let c0 = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let (lo0, hi0, lv0) = match done_at(done, c0) {
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
    if x > usize::MAX - 16 || !word_at(src, nodes, toks, gaps, x, &[0x65, 0x78, 0x70, 0x6F, 0x72, 0x74], Ghost(GW { g, w: "export"@ })) {
        return None;
    }
    let x1 = x.saturating_add(1);
    let x2 = x.saturating_add(2);
    let x3 = x.saturating_add(3);
    let x4 = x.saturating_add(4);
    let k0 = kind_at(nodes, c0);
    // `c1` is the second child where there is one (`c0` stands in otherwise).
    let c1 = if want >= 2 {
        match kid_of(nodes, m, 1) {
            Some(c) => c,
            None => {
                return None;
            },
        }
    } else {
        c0
    };
    let j: usize;
    match op {
        Op::ExportAll | Op::ExportAllAs => {
            let all_as = matches!(op, Op::ExportAllAs);
            if !punct_at(src, nodes, toks, gaps, x1, 0x2A, Ghost(GW { g, w: "*"@ })) {
                return None;
            }
            if all_as {
                if !word_at(src, nodes, toks, gaps, x2, &[0x61, 0x73], Ghost(GW { g, w: "as"@ }))
                    || !name_kind(k0) {
                    return None;
                }
            } else if !word_at(src, nodes, toks, gaps, x2, &[0x66, 0x72, 0x6F, 0x6D], Ghost(GW { g, w: "from"@ }))
                || !matches!(k0, NodeKind::StringLiteral) {
                return None;
            }
            if lo0 != x3 || hi0 != x4 {
                return None;
            }
            if all_as {
                let (lo1, hi1, _) = match done_at(done, c1) {
                    Some(r) => r,
                    None => {
                        return None;
                    },
                };
                let x5 = x.saturating_add(5);
                let x6 = x.saturating_add(6);
                if !word_at(src, nodes, toks, gaps, x4, &[0x66, 0x72, 0x6F, 0x6D], Ghost(GW { g, w: "from"@ }))
                    || !matches!(kind_at(nodes, c1), NodeKind::StringLiteral) || lo1 != x5 || hi1 != x6 {
                    return None;
                }
                j = match check_with_semi(src, nodes, toks, gaps, done, &WsSpec { m, k: 2, s: x6, end: nd.end }, Ghost(g)) {
                    Some(j) => j,
                    None => {
                        return None;
                    },
                };
            } else {
                j = match check_with_semi(src, nodes, toks, gaps, done, &WsSpec { m, k: 1, s: x4, end: nd.end }, Ghost(g)) {
                    Some(j) => j,
                    None => {
                        return None;
                    },
                };
            }
        },
        Op::ExportFrom => {
            if !matches!(k0, NodeKind::NamedExports) || lo0 != x1
                || !word_at(src, nodes, toks, gaps, hi0, &[0x66, 0x72, 0x6F, 0x6D], Ghost(GW { g, w: "from"@ })) {
                return None;
            }
            let (lo1, hi1, _) = match done_at(done, c1) {
                Some(r) => r,
                None => {
                    return None;
                },
            };
            let h1 = hi0.saturating_add(1);
            let h2 = hi0.saturating_add(2);
            if !matches!(kind_at(nodes, c1), NodeKind::StringLiteral) || lo1 != h1 || hi1 != h2 {
                return None;
            }
            j = match check_with_semi(src, nodes, toks, gaps, done, &WsSpec { m, k: 2, s: h2, end: nd.end }, Ghost(g)) {
                Some(j) => j,
                None => {
                    return None;
                },
            };
        },
        Op::ExportNamed => {
            if !matches!(k0, NodeKind::NamedExports) || lo0 != x1 {
                return None;
            }
            j = match find_semi(src, nodes, toks, gaps, hi0, nd.end, Ghost(g)) {
                Some(j) => j,
                None => {
                    return None;
                },
            };
        },
        Op::ExportVar | Op::ExportDecl => {
            let kind_ok = if matches!(op, Op::ExportVar) {
                matches!(k0, NodeKind::VariableStatement)
            } else {
                matches!(
                    k0,
                    NodeKind::FunctionDeclaration | NodeKind::GeneratorDeclaration
                        | NodeKind::AsyncFunctionDeclaration | NodeKind::AsyncGeneratorDeclaration
                        | NodeKind::ClassDeclaration | NodeKind::LexicalDeclaration
                )
            };
            if !kind_ok || lo0 != x1 || !end_ok(src, nodes, toks, gaps, nd.end, hi0, Ghost(g)) {
                return None;
            }
            j = hi0;
        },
        Op::ExportDefaultHoistable | Op::ExportDefaultClass => {
            let kind_ok = if matches!(op, Op::ExportDefaultClass) {
                matches!(k0, NodeKind::ClassDeclaration)
            } else {
                matches!(
                    k0,
                    NodeKind::FunctionDeclaration | NodeKind::GeneratorDeclaration
                        | NodeKind::AsyncFunctionDeclaration | NodeKind::AsyncGeneratorDeclaration
                )
            };
            if !kind_ok || lo0 != x2
                || !word_at(src, nodes, toks, gaps, x1, &[0x64, 0x65, 0x66, 0x61, 0x75, 0x6C, 0x74], Ghost(GW { g, w: "default"@ }))
                || !end_ok(src, nodes, toks, gaps, nd.end, hi0, Ghost(g)) {
                return None;
            }
            j = hi0;
        },
        _ => {
            if lv0 < 0 || lo0 != x2
                || !word_at(src, nodes, toks, gaps, x1, &[0x64, 0x65, 0x66, 0x61, 0x75, 0x6C, 0x74], Ghost(GW { g, w: "default"@ }))
                || !not_word_at(src, nodes, toks, gaps, x2, &[0x66, 0x75, 0x6E, 0x63, 0x74, 0x69, 0x6F, 0x6E], Ghost(GW { g, w: "function"@ }))
                || !not_word_at(src, nodes, toks, gaps, x2, &[0x61, 0x73, 0x79, 0x6E, 0x63], Ghost(GW { g, w: "async"@ }))
                || !not_word_at(src, nodes, toks, gaps, x2, &[0x63, 0x6C, 0x61, 0x73, 0x73], Ghost(GW { g, w: "class"@ })) {
                return None;
            }
            j = match find_semi(src, nodes, toks, gaps, hi0, nd.end, Ghost(g)) {
                Some(j) => j,
                None => {
                    return None;
                },
            };
        },
    }
    if j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].op == op);
        assert(x1 as int == x as int + 1);
        assert(x2 as int == x as int + 2);
        assert(x3 as int == x as int + 3);
        assert(x4 as int == x as int + 4);
        let dd = op == Op::ExportDefaultHoistable || op == Op::ExportDefaultClass;
        let ck = if dd { cx_default(g.cx) } else { g.cx };
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c0 as int, ck, 0);
        assert(a.nodes[m as int].children[0] == c0 as int);
        if a.nodes[m as int].children.len() >= 2 {
            assert(a.nodes[m as int].children[1] == c1 as int);
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c1 as int, ck, 1);
        }
        let c2g: int = if a.nodes[m as int].children.len() >= 3 { a.nodes[m as int].children[2] } else { c0 as int };
        if a.nodes[m as int].children.len() >= 3 {
            lemma_child_before(a, m as int, 2);
            assert(a.nodes[m as int].children[2] == c2g);
        }
        assert(kd(a, c0 as int) == k0);
        match op {
            Op::ExportAllAs => {
                assert(x.saturating_add(5) as int == x as int + 5);
                assert(x.saturating_add(6) as int == x as int + 6);
            },
            Op::ExportFrom => {
                assert(hi0.saturating_add(1) as int == hi0 as int + 1);
                assert(hi0.saturating_add(2) as int == hi0 as int + 2);
            },
            _ => {},
        }
        assert(g.cx.in_ || !g.cx.in_);
        lemma_export_done(
            a,
            g.ts,
            g.cx,
            m as int,
            c0 as int,
            c1 as int,
            c2g,
            x as int,
            hi0 as int,
            j as int,
        );
    }
    Some((x, j, -100))
}

} // verus!
