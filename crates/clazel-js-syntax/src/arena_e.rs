//! More checks of [`spec::d`] for [`crate::arena_d::check_derivation`]: the
//! constructs of the script grammar that [`crate::arena_d`] did not cover when
//! it was written. Each `check_*` here is dispatched from `check_derivation`
//! and has the same contract as its siblings there: it reads what the parser
//! built (the node, its children's recorded ranges) and the executable tokens,
//! and returns the node's token range and binding strength only if
//! `node_done` (the node derives that range in its context, and ends there)
//! follows from the specification.
//!
//! **Covered here:** `new.target`, `import.meta` (§13.3.12), `super.name`,
//! `super[expr]` and `super(args)` (§13.3.7), `import(spec, options)`
//! (§13.3.10), and optional chains (§13.3.9: `a?.b`, `a?.[b]`, `a?.(c)`,
//! `a?.#p`, `a?.b.c(d)`).
//!
//! The assumptions are those of [`crate::arena_d`].

use crate::arena_d::*;
use crate::ast::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// The words and punctuators of these checks, as code points.
pub(crate) proof fn lemma_words_e()
    ensures
        cps("super"@) =~= seq![0x73u32, 0x75, 0x70, 0x65, 0x72],
        cps("import"@) =~= seq![0x69u32, 0x6D, 0x70, 0x6F, 0x72, 0x74],
        cps("meta"@) =~= seq![0x6Du32, 0x65, 0x74, 0x61],
        cps("new"@) =~= seq![0x6Eu32, 0x65, 0x77],
        cps("target"@) =~= seq![0x74u32, 0x61, 0x72, 0x67, 0x65, 0x74],
        cps("?."@) =~= seq![0x3Fu32, 0x2E],
        cps(","@) =~= seq![0x2Cu32],
{
    reveal_strlit("super");
    reveal_strlit("import");
    reveal_strlit("meta");
    reveal_strlit("new");
    reveal_strlit("target");
    reveal_strlit("?.");
    reveal_strlit(",");
    assert("super"@ =~= seq!['s', 'u', 'p', 'e', 'r']);
    assert("import"@ =~= seq!['i', 'm', 'p', 'o', 'r', 't']);
    assert("meta"@ =~= seq!['m', 'e', 't', 'a']);
    assert("new"@ =~= seq!['n', 'e', 'w']);
    assert("target"@ =~= seq!['t', 'a', 'r', 'g', 'e', 't']);
    assert("?."@ =~= seq!['?', '.']);
    assert(","@ =~= seq![',']);
}

/// Token `x` is the punctuator `gw.w`, whose code points are `w`.
pub(crate) fn punct_n_at(
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
    let r = matches!(t.kind, TokKind::Punctuator) && text_is(src, t, w);
    proof {
        if r {
            assert(g.ts.toks[x as int].text =~= src@.subrange(t.start as int, t.end as int));
            assert(g.ts.toks[x as int].text =~= cps(lit));
        }
    }
    r
}

/// The facts the checks read of node `m` of the arena of `nodes`.
pub(crate) proof fn lemma_node_view(nodes: Seq<Node>, m: int)
    requires
        0 <= m < nodes.len(),
    ensures
        arena_of(nodes).nodes.len() == nodes.len(),
        arena_of(nodes).nodes[m] == nodes[m]@,
        arena_of(nodes).nodes[m].kind == nodes[m].kind,
        arena_of(nodes).nodes[m].op == nodes[m].op,
        arena_of(nodes).nodes[m].flag == nodes[m].flag,
        arena_of(nodes).nodes[m].start == nodes[m].start as int,
        arena_of(nodes).nodes[m].end == nodes[m].end as int,
        arena_of(nodes).nodes[m].children.len() == nodes[m].children@.len(),
{
}

// ---------------------------------------------------------------------
// §13.3.12 `new.target`, `import.meta`.
// ---------------------------------------------------------------------

/// `NewTarget : new . target` and `ImportMeta : import . meta`.
#[verifier::spinoff_prover]
proof fn lemma_meta_done(a: AstV, ts: Stream, cx: Ctx, m: int, x: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= x,
        x + 3 <= tn(ts),
        a.nodes[m].children.len() == 0,
        a.nodes[m].kind == NodeKind::NewTarget && is_kw(ts, x, "new"@) && is_p(ts, x + 1, "."@)
            && is_kw(ts, x + 2, "target"@) || a.nodes[m].kind == NodeKind::ImportMeta && is_kw(
            ts,
            x,
            "import"@,
        ) && is_p(ts, x + 1, "."@) && is_kw(ts, x + 2, "meta"@),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[x + 2].end,
    ensures
        node_done(a, ts, m, cx, x, x + 3),
        lvl(a, m) == 17,
{
    assert(span_ok(a, ts, m, x, x + 3));
    assert(d_expr_lhs(a, ts, m, cx, x, x + 3));
    assert(d_expr(a, ts, m, cx, x, x + 3));
    lemma_ed_of(a, ts, m, x, x + 3);
}

/// §13.3.12 `new . target`, `import . meta`.
#[verifier::spinoff_prover]
pub(crate) fn check_meta(
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
    let is_new = matches!(nd.kind, NodeKind::NewTarget);
    if !(is_new || matches!(nd.kind, NodeKind::ImportMeta)) || !nd.children.is_empty() {
        return None;
    }
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let x1 = x.saturating_add(1);
    let x2 = x.saturating_add(2);
    let x3 = x.saturating_add(3);
    if is_new {
        if !word_at(src, nodes, toks, gaps, x, &[0x6E, 0x65, 0x77], Ghost(GW { g, w: "new"@ }))
            || !word_at(
            src,
            nodes,
            toks,
            gaps,
            x2,
            &[0x74, 0x61, 0x72, 0x67, 0x65, 0x74],
            Ghost(GW { g, w: "target"@ }),
        ) {
            return None;
        }
    } else {
        if !word_at(
            src,
            nodes,
            toks,
            gaps,
            x,
            &[0x69, 0x6D, 0x70, 0x6F, 0x72, 0x74],
            Ghost(GW { g, w: "import"@ }),
        ) || !word_at(src, nodes, toks, gaps, x2, &[0x6D, 0x65, 0x74, 0x61], Ghost(GW { g, w: "meta"@ })) {
            return None;
        }
    }
    if !punct_at(src, nodes, toks, gaps, x1, 0x2E, Ghost(GW { g, w: "."@ }))
        || !end_ok(src, nodes, toks, gaps, nd.end, x3, Ghost(g)) {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(x1 as int == x as int + 1);
        assert(x2 as int == x as int + 2);
        assert(x3 as int == x as int + 3);
        assert(a.nodes[m as int].children.len() == 0);
        lemma_meta_done(a, g.ts, g.cx, m as int, x as int);
    }
    Some((x, x3, 17))
}

// ---------------------------------------------------------------------
// §13.3.7 `super.name`, `super[expr]`, `super(args)`.
// ---------------------------------------------------------------------

/// `SuperProperty : super . IdentifierName | super [ Expression ]`.
#[verifier::spinoff_prover]
proof fn lemma_super_prop_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    c: int,
    x: int,
    lo_c: int,
    hi_c: int,
    j: int,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= c < m,
        0 <= x,
        a.nodes[m].kind == NodeKind::SuperProperty,
        a.nodes[m].children =~= seq![c],
        is_kw(ts, x, "super"@),
        x + 3 <= j <= tn(ts),
        lo_c == x + 2,
        node_done(a, ts, c, cx, lo_c, hi_c),
        match a.nodes[m].op {
            Op::Dot => is_p(ts, x + 1, "."@) && kd(a, c) == NodeKind::IdentifierName && j == x + 3,
            Op::Bracket => cx_in(cx, true) == cx && is_p(ts, x + 1, "["@) && lvl(a, c) >= -1
                && is_p(ts, hi_c, "]"@) && j == hi_c + 1,
            _ => false,
        },
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == 17,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == c);
    assert(dc(a, ts, m, c, cx, lo_c, hi_c));
    assert(d_expr_lhs(a, ts, m, cx, x, j));
    assert(d_expr(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §13.3.7 `super . name` and `super [ expression ]`.
#[verifier::spinoff_prover]
pub(crate) fn check_super_prop(
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
        lemma_brackets();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        lemma_node_view(nodes@, m as int);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let dot = matches!(nd.op, Op::Dot);
    if !matches!(nd.kind, NodeKind::SuperProperty) || !(dot || matches!(nd.op, Op::Bracket))
        || nd.children.len() != 1 {
        return None;
    }
    let cxm = match done.cxs.get(m) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let c = match kid_of(nodes, m, 0) {
        Some(c) => c,
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
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let x1 = x.saturating_add(1);
    let x2 = x.saturating_add(2);
    if lo_c != x2
        || !word_at(src, nodes, toks, gaps, x, &[0x73, 0x75, 0x70, 0x65, 0x72], Ghost(GW { g, w: "super"@ })) {
        return None;
    }
    let j: usize;
    if dot {
        j = x.saturating_add(3);
        if !punct_at(src, nodes, toks, gaps, x1, 0x2E, Ghost(GW { g, w: "."@ }))
            || !matches!(kind_at(nodes, c), NodeKind::IdentifierName) || hi_c != j {
            return None;
        }
    } else {
        if !cxm.i || cxm.d || lv_c < -1 || !punct_at(src, nodes, toks, gaps, x1, 0x5B, Ghost(GW { g, w: "["@ }))
            || !punct_at(src, nodes, toks, gaps, hi_c, 0x5D, Ghost(GW { g, w: "]"@ })) {
            return None;
        }
        j = hi_c.saturating_add(1);
    }
    if !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(cxm == &done.cxs@[m as int]);
        assert(x1 as int == x as int + 1);
        assert(x2 as int == x as int + 2);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
        }
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 0);
        if dot {
            assert(j as int == x as int + 3);
        } else {
            assert(j as int == hi_c as int + 1);
            assert(g.cx.in_ && !g.cx.deflt);
            assert(cx_in(g.cx, true) == g.cx);
        }
        lemma_super_prop_done(a, g.ts, g.cx, m as int, c as int, x as int, lo_c as int, hi_c as int, j as int);
    }
    Some((x, j, 17))
}

/// `SuperCall : super Arguments`.
#[verifier::spinoff_prover]
proof fn lemma_super_call_done(a: AstV, ts: Stream, cx: Ctx, m: int, c: int, x: int, lo_c: int, j: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= c < m,
        0 <= x,
        a.nodes[m].kind == NodeKind::SuperCall,
        a.nodes[m].children =~= seq![c],
        is_kw(ts, x, "super"@),
        kd(a, c) == NodeKind::Arguments,
        lo_c == x + 1,
        node_done(a, ts, c, cx, lo_c, j),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == 15,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == c);
    assert(dc(a, ts, m, c, cx, lo_c, j));
    assert(d_expr_lhs(a, ts, m, cx, x, j));
    assert(d_expr(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §13.3.7 `super Arguments`.
#[verifier::spinoff_prover]
pub(crate) fn check_super_call(
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
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        lemma_node_view(nodes@, m as int);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::SuperCall) || nd.children.len() != 1 {
        return None;
    }
    let c = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let (lo_c, j, _lv_c) = match done_at(done, c) {
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
    let x1 = x.saturating_add(1);
    if lo_c != x1 || !matches!(kind_at(nodes, c), NodeKind::Arguments)
        || !word_at(src, nodes, toks, gaps, x, &[0x73, 0x75, 0x70, 0x65, 0x72], Ghost(GW { g, w: "super"@ }))
        || !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(x1 as int == x as int + 1);
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
        }
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 0);
        lemma_super_call_done(a, g.ts, g.cx, m as int, c as int, x as int, lo_c as int, j as int);
    }
    Some((x, j, 15))
}

// ---------------------------------------------------------------------
// §13.3.10 `import(specifier)`, `import(specifier, options)`.
// ---------------------------------------------------------------------

/// `ImportCall`: the specifier, the options or `Absent`, a trailing `,` allowed.
#[verifier::spinoff_prover]
proof fn lemma_import_call_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    s: int,
    o: int,
    x: int,
    mc: int,
    q: int,
    lo_o: int,
    j: int,
)
    requires
        toks_wf(ts),
        cx_in(cx, true) == cx,
        0 <= m < a.nodes.len(),
        0 <= s < m,
        0 <= o < m,
        0 <= x,
        a.nodes[m].kind == NodeKind::ImportCall,
        a.nodes[m].children =~= seq![s, o],
        is_kw(ts, x, "import"@),
        is_p(ts, x + 1, "("@),
        lvl(a, s) >= 0,
        node_done(a, ts, s, cx, x + 2, mc),
        if kd(a, o) == NodeKind::Absent {
            d(a, ts, o, cx, mc, mc) && ed(a, ts, o, mc) == mc && q == mc
        } else {
            lvl(a, o) >= 0 && is_p(ts, mc, ","@) && lo_o == mc + 1 && node_done(a, ts, o, cx, lo_o, q)
        },
        (is_p(ts, q, ")"@) && j == q + 1) || (is_p(ts, q, ","@) && is_p(ts, q + 1, ")"@) && j == q
            + 2),
        x + 3 <= j <= tn(ts),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == 15,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == s);
    assert(a.nodes[m].children[1] == o);
    assert(dc(a, ts, m, s, cx, x + 2, mc));
    assert(is_assign_expr(a, s));
    if kd(a, o) == NodeKind::Absent {
        assert(dc(a, ts, m, o, cx, mc, mc));
    } else {
        assert(dc(a, ts, m, o, cx, mc + 1, q));
        assert(is_assign_expr(a, o));
    }
    assert(d_expr_lhs(a, ts, m, cx, x, j));
    assert(d_expr(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §13.3.10 `import ( specifier ,? )` and `import ( specifier , options ,? )`.
#[verifier::spinoff_prover]
pub(crate) fn check_import_call(
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
    if !matches!(nd.kind, NodeKind::ImportCall) || nd.children.len() != 2 {
        return None;
    }
    let s = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let o = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let (lo_s, mc, lv_s) = match done_at(done, s) {
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
    let x1 = x.saturating_add(1);
    let x2 = x.saturating_add(2);
    if lv_s < 0 || lo_s != x2
        || !word_at(src, nodes, toks, gaps, x, &[0x69, 0x6D, 0x70, 0x6F, 0x72, 0x74], Ghost(GW { g, w: "import"@ }))
        || !punct_at(src, nodes, toks, gaps, x1, 0x28, Ghost(GW { g, w: "("@ })) {
        return None;
    }
    let absent = matches!(kind_at(nodes, o), NodeKind::Absent);
    let (lo_o, q_e, lv_o) = if absent {
        if !check_absent(src, nodes, toks, gaps, o, mc, Ghost(g)) {
            return None;
        }
        (mc, mc, 0i32)
    } else {
        match done_at(done, o) {
            Some(r) => r,
            None => {
                return None;
            },
        }
    };
    if !absent && (lv_o < 0 || lo_o != mc.saturating_add(1)
        || !punct_n_at(src, nodes, toks, gaps, mc, &[0x2C], Ghost(GW { g, w: ","@ }))) {
        return None;
    }
    // After the last operand, which ends at `q_e`: `)`, or `, )`.
    let e1 = q_e.saturating_add(1);
    let j: usize = if punct_at(src, nodes, toks, gaps, q_e, 0x29, Ghost(GW { g, w: ")"@ })) {
        e1
    } else if punct_n_at(src, nodes, toks, gaps, q_e, &[0x2C], Ghost(GW { g, w: ","@ }))
        && punct_at(src, nodes, toks, gaps, e1, 0x29, Ghost(GW { g, w: ")"@ })) {
        q_e.saturating_add(2)
    } else {
        return None;
    };
    if !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(x1 as int == x as int + 1);
        assert(x2 as int == x as int + 2);
        assert(e1 as int == q_e as int + 1);
        assert(a.nodes[m as int].children =~= seq![s as int, o as int]) by {
            assert(a.nodes[m as int].children.len() == 2);
        }
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, s as int, g.cx, 0);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, o as int, g.cx, 1);
        if !absent {
            assert(kd(a, o as int) != NodeKind::Absent);
        }
        lemma_import_call_done(
            a,
            g.ts,
            g.cx,
            m as int,
            s as int,
            o as int,
            x as int,
            mc as int,
            q_e as int,
            lo_o as int,
            j as int,
        );
    }
    Some((x, j, 15))
}

// ---------------------------------------------------------------------
// §13.3.9 optional chains: `a?.b`, `a?.[b]`, `a?.(c)`, `a?.#p`, and the links that
// continue them.
// ---------------------------------------------------------------------

/// One link of an `OptionalChain`.
#[verifier::spinoff_prover]
proof fn lemma_chain_done(
    a: AstV,
    ts: Stream,
    cx: Ctx,
    m: int,
    c: int,
    x: int,
    s: int,
    lo_c: int,
    hi_c: int,
    j: int,
)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= c < m,
        0 <= x < j <= tn(ts),
        a.nodes[m].kind == NodeKind::OptionalChain,
        a.nodes[m].children =~= seq![c],
        s == (if a.nodes[m].flag {
            x + 1
        } else {
            x
        }),
        a.nodes[m].flag ==> is_p(ts, x, "?."@),
        node_done(a, ts, c, cx, lo_c, hi_c),
        match a.nodes[m].op {
            Op::ChainDot => (a.nodes[m].flag || is_p(ts, x, "."@)) && kd(a, c)
                == NodeKind::IdentifierName && j == x + 2 && lo_c == x + 1 && hi_c == j,
            Op::ChainPrivateDot => (a.nodes[m].flag || is_p(ts, x, "."@)) && kd(a, c)
                == NodeKind::PrivateIdentifier && j == x + 2 && lo_c == x + 1 && hi_c == j,
            Op::ChainBracket => cx_in(cx, true) == cx && is_p(ts, s, "["@) && lvl(a, c) >= -1
                && lo_c == s + 1 && is_p(ts, hi_c, "]"@) && j == hi_c + 1,
            Op::ChainCall => kd(a, c) == NodeKind::Arguments && lo_c == s && j == hi_c,
            _ => false,
        },
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == -100,
{
    assert(span_ok(a, ts, m, x, j));
    assert(a.nodes[m].children[0] == c);
    assert(dc(a, ts, m, c, cx, lo_c, hi_c));
    assert(d_chain_link(a, ts, m, cx, x, j));
    assert(d_expr_lhs(a, ts, m, cx, x, j));
    assert(d_expr(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §13.3.9 one link of an `OptionalChain`: `?. name`, `?. [ expr ]`, `?. ( args )`, `?. #name`,
/// or the same without the `?.` (`. name`, `[ expr ]`, `( args )`, `. #name`).
#[verifier::spinoff_prover]
pub(crate) fn check_chain_link(
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
        lemma_brackets();
        lemma_env_toks_wf(src@, nodes@, toks@, gaps@, g.ts);
        lemma_node_view(nodes@, m as int);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    if !matches!(nd.kind, NodeKind::OptionalChain) || nd.children.len() != 1 {
        return None;
    }
    let cxm = match done.cxs.get(m) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let c = match kid_of(nodes, m, 0) {
        Some(c) => c,
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
    let x = match start_tok(src, nodes, toks, gaps, done, m, Ghost(g)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let x1 = x.saturating_add(1);
    let flag = nd.flag;
    let s: usize = if flag {
        x1
    } else {
        x
    };
    if flag && !punct_n_at(src, nodes, toks, gaps, x, &[0x3F, 0x2E], Ghost(GW { g, w: "?."@ })) {
        return None;
    }
    let j: usize = match nd.op {
        Op::ChainDot | Op::ChainPrivateDot => {
            let private = matches!(nd.op, Op::ChainPrivateDot);
            let kc = kind_at(nodes, c);
            let kind_ok = if private {
                matches!(kc, NodeKind::PrivateIdentifier)
            } else {
                matches!(kc, NodeKind::IdentifierName)
            };
            let j = x.saturating_add(2);
            if (!flag && !punct_at(src, nodes, toks, gaps, x, 0x2E, Ghost(GW { g, w: "."@ }))) || !kind_ok
                || lo_c != x1 || hi_c != j {
                return None;
            }
            j
        },
        Op::ChainBracket => {
            if !cxm.i || cxm.d || lv_c < -1 || lo_c != s.saturating_add(1)
                || !punct_at(src, nodes, toks, gaps, s, 0x5B, Ghost(GW { g, w: "["@ }))
                || !punct_at(src, nodes, toks, gaps, hi_c, 0x5D, Ghost(GW { g, w: "]"@ })) {
                return None;
            }
            hi_c.saturating_add(1)
        },
        Op::ChainCall => {
            if !matches!(kind_at(nodes, c), NodeKind::Arguments) || lo_c != s {
                return None;
            }
            hi_c
        },
        _ => {
            return None;
        },
    };
    if !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    proof {
        let a = arena_of(nodes@);
        assert(nd == &nodes@[m as int]);
        assert(cxm == &done.cxs@[m as int]);
        assert(x1 as int == x as int + 1);
        assert(s as int == (if a.nodes[m as int].flag {
            x as int + 1
        } else {
            x as int
        }));
        assert(a.nodes[m as int].children =~= seq![c as int]) by {
            assert(a.nodes[m as int].children.len() == 1);
        }
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, 0);
        match a.nodes[m as int].op {
            Op::ChainDot => {
                assert(j as int == x as int + 2);
            },
            Op::ChainPrivateDot => {
                assert(j as int == x as int + 2);
            },
            Op::ChainBracket => {
                assert(s.saturating_add(1) as int == s as int + 1);
                assert(hi_c.saturating_add(1) as int == hi_c as int + 1);
                assert(g.cx.in_ && !g.cx.deflt);
                assert(cx_in(g.cx, true) == g.cx);
            },
            _ => {},
        }
        lemma_chain_done(
            a,
            g.ts,
            g.cx,
            m as int,
            c as int,
            x as int,
            s as int,
            lo_c as int,
            hi_c as int,
            j as int,
        );
    }
    Some((x, j, -100))
}

/// `OptionalExpression : base link links...`.
#[verifier::spinoff_prover]
proof fn lemma_optional_done(a: AstV, ts: Stream, cx: Ctx, m: int, base: int, x: int, mb: int, j: int)
    requires
        toks_wf(ts),
        0 <= m < a.nodes.len(),
        0 <= base < m,
        0 <= x < j <= tn(ts),
        a.nodes[m].kind == NodeKind::OptionalExpression,
        a.nodes[m].children.len() >= 2,
        a.nodes[m].children[0] == base,
        is_member_or_call(a, base),
        all_kind2(a, a.nodes[m].children, 1, NodeKind::OptionalChain, NodeKind::OptionalChain),
        flag_of(a, a.nodes[m].children[1]),
        node_done(a, ts, base, cx, x, mb),
        dl(a, ts, m, a.nodes[m].children, 1, cx, mb, j),
        a.nodes[m].start == ts.toks[x].start,
        a.nodes[m].end == ts.toks[j - 1].end,
    ensures
        node_done(a, ts, m, cx, x, j),
        lvl(a, m) == 14,
{
    assert(span_ok(a, ts, m, x, j));
    assert(dc(a, ts, m, base, cx, x, mb));
    assert(d_expr_lhs(a, ts, m, cx, x, j));
    assert(d_expr(a, ts, m, cx, x, j));
    lemma_ed_of(a, ts, m, x, j);
}

/// §13.3.9 `OptionalExpression`: a base and its links.
#[verifier::spinoff_prover]
pub(crate) fn check_optional(
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
        lemma_node_view(nodes@, m as int);
    }
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let len = nd.children.len();
    if !matches!(nd.kind, NodeKind::OptionalExpression) || len < 2 {
        return None;
    }
    let base = match kid_of(nodes, m, 0) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let first_link = match kid_of(nodes, m, 1) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let last_link = match kid_of(nodes, m, len.saturating_sub(1)) {
        Some(c) => c,
        None => {
            return None;
        },
    };
    let (lo_b, mb, lv_b) = match done_at(done, base) {
        Some(r) => r,
        None => {
            return None;
        },
    };
    let (_lo_l, j, _lv_l) = match done_at(done, last_link) {
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
    let flag_first = match nodes.get(first_link) {
        Some(l) => l.flag,
        None => {
            return None;
        },
    };
    if !(lv_b == 15 || lv_b == 17) || lo_b != x || !flag_first
        || !end_ok(src, nodes, toks, gaps, nd.end, j, Ghost(g)) || j <= x {
        return None;
    }
    let ghost a = arena_of(nodes@);
    proof {
        assert(nd == &nodes@[m as int]);
        assert(first_link < nodes.len());
        assert(nodes@[first_link as int].flag == a.nodes[first_link as int].flag);
    }
    let mut k = len;
    let mut pos = j;
    while k > 1
        invariant
            m < nodes.len(),
            nodes@.len() == nodes.len(),
            a == arena_of(nodes@),
            ast_wf(a),
            nd == &nodes@[m as int],
            len == nd.children.len(),
            len == a.nodes[m as int].children.len(),
            1 <= k <= len,
            pos <= toks.len(),
            j <= toks.len(),
            env_ok(src@, nodes@, toks@, gaps@, g.ts),
            inv(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int),
            cx_ok(a, done.cxs@, m as int, g.cx),
            dl(a, g.ts, m as int, a.nodes[m as int].children, k as int, g.cx, pos as int, j as int),
            forall|q: int|
                k <= q < len ==> kd(a, #[trigger] a.nodes[m as int].children[q])
                    == NodeKind::OptionalChain,
        decreases k,
    {
        let km1 = k.saturating_sub(1);
        let c = match kid_of(nodes, m, km1) {
            Some(c) => c,
            None => {
                return None;
            },
        };
        let (lo_c, hi_c, _lv_c) = match done_at(done, c) {
            Some(r) => r,
            None => {
                return None;
            },
        };
        if hi_c != pos || !matches!(kind_at(nodes, c), NodeKind::OptionalChain) {
            return None;
        }
        proof {
            assert(km1 as int == k as int - 1);
            lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, c as int, g.cx, km1 as int);
            assert(a.nodes[m as int].children[k as int - 1] == c as int);
            lemma_dl_cons(
                a,
                g.ts,
                m as int,
                a.nodes[m as int].children,
                k as int - 1,
                g.cx,
                lo_c as int,
                hi_c as int,
                j as int,
            );
        }
        pos = lo_c;
        k = km1;
    }
    if pos != mb {
        return None;
    }
    proof {
        assert(a.nodes[m as int].children[0] == base as int);
        lemma_inv_get(a, g.ts, done.cxs@, done.lo@, done.hi@, done.lv@, m as int, base as int, g.cx, 0);
        assert(all_kind2(
            a,
            a.nodes[m as int].children,
            1,
            NodeKind::OptionalChain,
            NodeKind::OptionalChain,
        ));
        assert(a.nodes[m as int].children[1] == first_link as int);
        assert(flag_of(a, first_link as int));
        assert(is_member_or_call(a, base as int));
        lemma_optional_done(a, g.ts, g.cx, m as int, base as int, x as int, mb as int, j as int);
    }
    Some((x, j, 14))
}

} // verus!
