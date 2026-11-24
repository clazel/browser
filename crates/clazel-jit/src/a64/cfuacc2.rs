//! The units of every A64 template are well formed and accepted by the
//! validator's scan, by induction over the program (jit.md item J.9, "every
//! emitted blob is accepted"): [`lemma_utmpl_uok`] and
//! [`lemma_utmpl_ucheck`]. The leaves are in [`super::cfuacc`]. The
//! counterpart of [`crate::cfuacc2`].

#[cfg(verus_only)]
use super::cfaccept::*;
#[cfg(verus_only)]
use super::cfbs::*;
#[cfg(verus_only)]
use super::cflens::*;
#[cfg(verus_only)]
use super::cfsimple::*;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cftemplates::*;
#[cfg(verus_only)]
use super::cfuacc::*;
#[cfg(verus_only)]
use super::cfunits::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every unit of the list is well formed.
pub open spec fn uok_all(us: Us) -> bool {
    forall|k: int| 0 <= k < us.len() ==> uok(#[trigger] us[k])
}

/// Well-formed units followed by well-formed units.
pub proof fn lemma_uok_cat(a: Us, b: Us)
    requires
        uok_all(a),
        uok_all(b),
    ensures
        uok_all(a + b),
{
    assert forall|k: int| 0 <= k < (a + b).len() implies uok(#[trigger] (a + b)[k]) by {
        if k < a.len() {
            assert((a + b)[k] == a[k]);
        } else {
            assert((a + b)[k] == b[k - a.len()]);
        }
    }
}

/// A list of simple instructions is a list of well-formed units.
proof fn lemma_simp_uok(c: Seq<isa::Instr>)
    requires
        all_simp(c),
    ensures
        uok_all(ones(c)),
{
    assert forall|k: int| 0 <= k < c.len() implies ok2(#[trigger] c[k]) by {
        assert(simp(c[k]));
    }
    lemma_ones_uok(c);
}

/// An exit sequence is a well-formed unit.
pub proof fn lemma_exit_uok(c: u16)
    ensures
        uok(exit_seq(c)),
{
    let e = exit_seq(c);
    assert(e.len() == 3);
    assert(clazel_codecheck::a64::spec::exit_unit_at(e, 0));
}

/// A memory instruction's units are well formed.
proof fn lemma_mem_uok(m: MemOp, nl: nat, h: nat)
    requires
        cf_flow(Node::Mem(m), nl, h, 0) is Some,
    ensures
        uok_all(mem_units(m, nl, h)),
{
    assert(max_slots() == 31) by {
        super::tlemmas::lemma_abi_consts_t();
    }
    let pre = mem_pre(m, nl, h);
    let tail = mem_tail(m, nl, h);
    let chk = mem_check(m, nl, h);
    let jm = seq![b_i(code_len(exit_seq(mem_exit_code(m))) as int + 4)];
    let stub = exit_seq(mem_exit_code(m));
    let c0 = mem_chk(mem_region(m), mem_n(m), mem_r1(m, nl, h), mem_r2(m, nl, h));
    lemma_mem_check_ok(m, nl, h);
    lemma_check_unit(c0);
    assert(chk == clazel_codecheck::a64::spec::check_seq(c0));
    // operands
    assert(forall|q: int| 0 <= q < pre.len() ==> ok2(#[trigger] pre[q])) by {
        assert forall|q: int| 0 <= q < pre.len() implies ok2(pre[q]) by {
            match m {
                MemOp::BoundsCheck { .. } => {
                    assert(q == 0);
                },
                MemOp::Load { .. } => {
                    assert(q == 0 || q == 1);
                },
                MemOp::Store { .. } => {
                    assert(q == 0 || q == 1 || q == 2);
                },
            }
        }
    }
    lemma_ones_uok(pre);
    assert(forall|q: int| 0 <= q < tail.len() ==> ok2(#[trigger] tail[q])) by {
        assert forall|q: int| 0 <= q < tail.len() implies ok2(tail[q]) by {
            match m {
                MemOp::BoundsCheck { .. } => {},
                MemOp::Load { .. } => {
                    assert(q == 0 || q == 1);
                },
                MemOp::Store { .. } => {
                    assert(q == 0);
                },
            }
        }
    }
    lemma_ones_uok(tail);
    lemma_exit_uok(mem_exit_code(m));
    let u2 = seq![chk];
    let u4 = seq![jm, stub];
    assert(uok_all(u2)) by {
        assert forall|k: int| 0 <= k < u2.len() implies uok(#[trigger] u2[k]) by {
            assert(k == 0);
            assert(u2[0] == chk);
        }
    }
    assert(uok_all(u4)) by {
        assert forall|k: int| 0 <= k < u4.len() implies uok(#[trigger] u4[k]) by {
            assert(k == 0 || k == 1);
        }
    }
    lemma_uok_cat(ones(pre), u2);
    lemma_uok_cat(ones(pre) + u2, ones(tail));
    lemma_uok_cat(ones(pre) + u2 + ones(tail), u4);
}

/// **Every unit of a template is well formed.**
pub proof fn lemma_utmpl_uok(n: Node, nl: nat, h: nat, offs: Seq<int>)
    requires
        cf_flow(n, nl, h, offs.len()) is Some,
    ensures
        uok_all(utmpl(n, nl, h, offs)),
    decreases n,
{
    let d = offs.len();
    match n {
        Node::Op(o) => {
            lemma_tmpl_straight(o, nl, h);
            assert(all_simp(tmpl(o, nl, h))) by {
                assert forall|k: int| 0 <= k < tmpl(o, nl, h).len() implies simp(
                    #[trigger] tmpl(o, nl, h)[k],
                ) by {
                    assert(straight(tmpl(o, nl, h)[k]));
                }
            }
            lemma_simp_uok(tmpl(o, nl, h));
        },
        Node::Mem(m) => {
            assert(cf_flow(n, nl, h, 0) is Some);
            lemma_mem_uok(m, nl, h);
        },
        Node::Then(a, b) => {
            let ob = shift(offs, csize(*a, nl, h, d) as int);
            lemma_utmpl_uok(*a, nl, h, offs);
            match cf_flow(*a, nl, h, d) {
                Some(Flow::Falls(h1)) => {
                    assert(ob.len() == d);
                    lemma_utmpl_uok(*b, nl, flow_h(*a, nl, h, d), ob);
                    lemma_uok_cat(utmpl(*a, nl, h, offs), utmpl(*b, nl, flow_h(*a, nl, h, d), ob));
                },
                Some(Flow::Dead) => {
                    assert(*b == Node::Op(Op::Nop));
                    assert(utmpl(*b, nl, flow_h(*a, nl, h, d), ob) =~= Seq::<
                        Seq<isa::Instr>,
                    >::empty());
                    assert(utmpl(*a, nl, h, offs) + utmpl(*b, nl, flow_h(*a, nl, h, d), ob)
                        =~= utmpl(*a, nl, h, offs));
                },
                None => {},
            }
        },
        Node::Block(b) => {
            let ob = seq![csize(*b, nl, h, d + 1) as int] + offs;
            assert(ob.len() == d + 1);
            lemma_utmpl_uok(*b, nl, h, ob);
        },
        Node::Loop(b) => {
            let ob = seq![0int] + offs;
            assert(ob.len() == d + 1);
            lemma_utmpl_uok(*b, nl, h, ob);
        },
        Node::If(t, e) => {
            let st = csize(*t, nl, (h - 1) as nat, d + 1) as int;
            let se = csize(*e, nl, (h - 1) as nat, d + 1) as int;
            let ot = seq![st + 4 + se] + shift(offs, 8);
            let oe = seq![se] + shift(offs, 12 + st);
            assert(ot.len() == d + 1 && oe.len() == d + 1);
            lemma_utmpl_uok(*t, nl, (h - 1) as nat, ot);
            lemma_utmpl_uok(*e, nl, (h - 1) as nat, oe);
            let cp = cond_pre(nl, h, true, st + 8);
            lemma_cond_pre_simp(nl, h, true, st + 8);
            lemma_simp_uok(cp);
            lemma_b_simp(se + 4);
            lemma_simp_uok(seq![b_i(se + 4)]);
            let jmu = seq![seq![b_i(se + 4)]];
            assert(uok_all(jmu)) by {
                assert forall|k: int| 0 <= k < jmu.len() implies uok(#[trigger] jmu[k]) by {
                    assert(k == 0);
                    assert(ones(seq![b_i(se + 4)])[0] == seq![b_i(se + 4)]);
                }
            }
            lemma_uok_cat(ones(cp), utmpl(*t, nl, (h - 1) as nat, ot));
            lemma_uok_cat(ones(cp) + utmpl(*t, nl, (h - 1) as nat, ot), jmu);
            lemma_uok_cat(
                ones(cp) + utmpl(*t, nl, (h - 1) as nat, ot) + jmu,
                utmpl(*e, nl, (h - 1) as nat, oe),
            );
        },
        Node::Br(l) => {
            assert(ctmpl(n, nl, h, offs) == seq![b_i(if l < offs.len() {
                offs[l as int]
            } else {
                0
            })]);
            lemma_b_simp(if l < offs.len() {
                offs[l as int]
            } else {
                0
            });
            lemma_simp_uok(ctmpl(n, nl, h, offs));
        },
        Node::BrIf(l) => {
            let rel = if l < offs.len() {
                offs[l as int] - 4
            } else {
                0
            };
            lemma_cond_pre_simp(nl, h, false, rel);
            assert(ctmpl(n, nl, h, offs) == cond_pre(nl, h, false, rel));
            lemma_simp_uok(ctmpl(n, nl, h, offs));
        },
        Node::BrTable(ls, dd) => {
            lemma_brt_simp(ls@, dd, nl, h, offs);
            lemma_simp_uok(ctmpl(n, nl, h, offs));
        },
        Node::Exit(c, _) => {
            lemma_exit_uok(c as u16);
            let us = seq![exit_seq(c as u16)];
            assert(uok_all(us)) by {
                assert forall|k: int| 0 <= k < us.len() implies uok(#[trigger] us[k]) by {
                    assert(k == 0);
                }
            }
        },
    }
}

// ----------------------------------------------------------------------------
// The scan accepts them
// ----------------------------------------------------------------------------

/// No protected position of the node (starting at `pos`) is a branch target.
pub open spec fn pf(n: Node, nl: nat, h: nat, d: nat, pos: int, p: spec_fn(int) -> bool) -> bool {
    forall|x: int| #[trigger] prot(n, nl, h, d, x) ==> !p(pos + x)
}

/// The statement of [`lemma_utmpl_ucheck`] for a node: from any position, with
/// whatever the scan knew, and any set of branch targets that avoids
/// [`prot`], the scan accepts the units.
pub open spec fn uc_all(n: Node, nl: nat, h: nat, offs: Seq<int>, p: spec_fn(int) -> bool) -> bool {
    forall|pos: int, fs: clazel_codecheck::a64::spec::Facts|
        pf(n, nl, h, offs.len(), pos, p) ==> #[trigger] ucheck(
            utmpl(n, nl, h, offs),
            pos,
            fs,
            p,
        ) is Some
}

/// `then`.
proof fn lemma_uc_then(
    a: Node,
    b: Node,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    p: spec_fn(int) -> bool,
)
    requires
        cf_flow(Node::Then(Box::new(a), Box::new(b)), nl, h, offs.len()) is Some,
        cf_flow(a, nl, h, offs.len()) is Some,
        uc_all(a, nl, h, offs, p),
        match cf_flow(a, nl, h, offs.len()) {
            Some(Flow::Falls(h1)) => uc_all(
                b,
                nl,
                flow_h(a, nl, h, offs.len()),
                shift(offs, csize(a, nl, h, offs.len()) as int),
                p,
            ),
            _ => true,
        },
    ensures
        uc_all(Node::Then(Box::new(a), Box::new(b)), nl, h, offs, p),
{
    let n = Node::Then(Box::new(a), Box::new(b));
    let d = offs.len();
    let sa = csize(a, nl, h, d);
    let h1 = flow_h(a, nl, h, d);
    let ob = shift(offs, sa as int);
    lemma_utmpl_blen(a, nl, h, offs);
    assert forall|pos: int, fs: clazel_codecheck::a64::spec::Facts|
        pf(n, nl, h, d, pos, p) implies #[trigger] ucheck(
        utmpl(n, nl, h, offs),
        pos,
        fs,
        p,
    ) is Some by {
        let ua = utmpl(a, nl, h, offs);
        let ub = utmpl(b, nl, h1, ob);
        assert(pf(a, nl, h, d, pos, p)) by {
            assert forall|x: int| #[trigger] prot(a, nl, h, d, x) implies !p(pos + x) by {
                assert(prot(n, nl, h, d, x));
            }
        }
        assert(ucheck(ua, pos, fs, p) is Some);
        let f = ucheck(ua, pos, fs, p)->Some_0;
        lemma_ucheck_cat(ua, ub, pos, fs, p);
        match cf_flow(a, nl, h, d) {
            Some(Flow::Falls(_)) => {
                assert(ob.len() == d);
                assert(pf(b, nl, h1, d, pos + sa as int, p)) by {
                    assert forall|y: int| #[trigger] prot(b, nl, h1, d, y) implies !p(
                        pos + sa as int + y,
                    ) by {
                        assert(prot(n, nl, h, d, y + sa as int));
                    }
                }
                assert(ucheck(ub, pos + sa as int, f, p) is Some);
            },
            Some(Flow::Dead) => {
                assert(b == Node::Op(Op::Nop));
                assert(ub =~= Seq::<Seq<isa::Instr>>::empty());
            },
            None => {},
        }
    }
}

/// The part of `if` after the condition, from the scan's facts after it.
proof fn lemma_uc_if_rest(
    t: Node,
    e: Node,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    p: spec_fn(int) -> bool,
    pos: int,
    f1: clazel_codecheck::a64::spec::Facts,
)
    requires
        cf_flow(Node::If(Box::new(t), Box::new(e)), nl, h, offs.len()) is Some,
        uc_all(t, nl, (h - 1) as nat, seq![
            csize(t, nl, (h - 1) as nat, offs.len() + 1) as int + 4 + csize(
                e,
                nl,
                (h - 1) as nat,
                offs.len() + 1,
            ) as int,
        ] + shift(offs, 8), p),
        uc_all(e, nl, (h - 1) as nat, seq![csize(e, nl, (h - 1) as nat, offs.len() + 1) as int]
            + shift(offs, 12 + csize(t, nl, (h - 1) as nat, offs.len() + 1) as int), p),
        pf(Node::If(Box::new(t), Box::new(e)), nl, h, offs.len(), pos, p),
    ensures
        ucheck(
            utmpl(t, nl, (h - 1) as nat, seq![
                csize(t, nl, (h - 1) as nat, offs.len() + 1) as int + 4 + csize(
                    e,
                    nl,
                    (h - 1) as nat,
                    offs.len() + 1,
                ) as int,
            ] + shift(offs, 8))
                + seq![seq![b_i(csize(e, nl, (h - 1) as nat, offs.len() + 1) as int + 4)]]
                + utmpl(e, nl, (h - 1) as nat, seq![
                csize(e, nl, (h - 1) as nat, offs.len() + 1) as int,
            ] + shift(offs, 12 + csize(t, nl, (h - 1) as nat, offs.len() + 1) as int)),
            pos + 8,
            f1,
            p,
        ) is Some,
{
    let n = Node::If(Box::new(t), Box::new(e));
    let d = offs.len();
    let h0 = (h - 1) as nat;
    let st = csize(t, nl, h0, d + 1) as int;
    let se = csize(e, nl, h0, d + 1) as int;
    let ot = seq![st + 4 + se] + shift(offs, 8);
    let oe = seq![se] + shift(offs, 12 + st);
    assert(ot.len() == d + 1 && oe.len() == d + 1);
    let ut = utmpl(t, nl, h0, ot);
    let ue = utmpl(e, nl, h0, oe);
    let jmu = seq![seq![b_i(se + 4)]];
    lemma_utmpl_blen(t, nl, h0, ot);
    lemma_utmpl_blen(e, nl, h0, oe);
    lemma_blen_one(seq![b_i(se + 4)]);
    lemma_b_simp(se + 4);
    assert(pf(t, nl, h0, d + 1, pos + 8, p)) by {
        assert forall|x: int| #[trigger] prot(t, nl, h0, d + 1, x) implies !p(pos + 8 + x) by {
            assert(prot(n, nl, h, d, x + 8));
        }
    }
    assert(ucheck(ut, pos + 8, f1, p) is Some);
    let f2 = ucheck(ut, pos + 8, f1, p)->Some_0;
    let q = pos + 8 + st;
    let fj = if p(q) {
        clazel_codecheck::a64::spec::no_facts()
    } else {
        f2
    };
    lemma_simp_plain(fj, b_i(se + 4));
    lemma_ucheck_one(seq![b_i(se + 4)], q, f2, p);
    let f3 = ufacts(seq![b_i(se + 4)], fj)->Some_0;
    assert(pf(e, nl, h0, d + 1, pos + (12 + st), p)) by {
        assert forall|x: int| #[trigger] prot(e, nl, h0, d + 1, x) implies !p(pos + (12 + st) + x) by {
            assert(prot(n, nl, h, d, x + (12 + st)));
        }
    }
    assert(ucheck(ue, pos + (12 + st), f3, p) is Some);
    lemma_ucheck_cat(ut, jmu + ue, pos + 8, f1, p);
    lemma_ucheck_cat(jmu, ue, pos + 8 + st, f2, p);
    assert(ucheck(jmu, q, f2, p) == Some(f3)) by {
        lemma_ucheck_one(seq![b_i(se + 4)], q, f2, p);
    }
    assert(blen(jmu) == 4);
    assert(ut + jmu + ue =~= ut + (jmu + ue));
}

/// `if`.
proof fn lemma_uc_if(t: Node, e: Node, nl: nat, h: nat, offs: Seq<int>, p: spec_fn(int) -> bool)
    requires
        cf_flow(Node::If(Box::new(t), Box::new(e)), nl, h, offs.len()) is Some,
        uc_all(t, nl, (h - 1) as nat, seq![
            csize(t, nl, (h - 1) as nat, offs.len() + 1) as int + 4 + csize(
                e,
                nl,
                (h - 1) as nat,
                offs.len() + 1,
            ) as int,
        ] + shift(offs, 8), p),
        uc_all(e, nl, (h - 1) as nat, seq![csize(e, nl, (h - 1) as nat, offs.len() + 1) as int]
            + shift(offs, 12 + csize(t, nl, (h - 1) as nat, offs.len() + 1) as int), p),
    ensures
        uc_all(Node::If(Box::new(t), Box::new(e)), nl, h, offs, p),
{
    let n = Node::If(Box::new(t), Box::new(e));
    let d = offs.len();
    let h0 = (h - 1) as nat;
    let st = csize(t, nl, h0, d + 1) as int;
    let se = csize(e, nl, h0, d + 1) as int;
    let ot = seq![st + 4 + se] + shift(offs, 8);
    let oe = seq![se] + shift(offs, 12 + st);
    assert(ot.len() == d + 1 && oe.len() == d + 1);
    let cp = cond_pre(nl, h, true, st + 8);
    let ut = utmpl(t, nl, h0, ot);
    let ue = utmpl(e, nl, h0, oe);
    let jmu = seq![seq![b_i(se + 4)]];
    lemma_blen_ones(cp);
    lemma_cond_pre_simp(nl, h, true, st + 8);
    assert(code_len(cp) == 8);
    assert(utmpl(n, nl, h, offs) =~= ones(cp) + (ut + jmu + ue));
    assert forall|pos: int, fs: clazel_codecheck::a64::spec::Facts|
        pf(n, nl, h, d, pos, p) implies #[trigger] ucheck(
        utmpl(n, nl, h, offs),
        pos,
        fs,
        p,
    ) is Some by {
        let a1 = ones(cp);
        lemma_ones_ucheck(cp, pos, fs, p);
        let f1 = ucheck(a1, pos, fs, p)->Some_0;
        lemma_uc_if_rest(t, e, nl, h, offs, p, pos, f1);
        lemma_ucheck_cat(a1, ut + jmu + ue, pos, fs, p);
    }
}

/// `block`.
proof fn lemma_uc_block(b: Node, nl: nat, h: nat, offs: Seq<int>, p: spec_fn(int) -> bool)
    requires
        uc_all(b, nl, h, seq![csize(b, nl, h, offs.len() + 1) as int] + offs, p),
    ensures
        uc_all(Node::Block(Box::new(b)), nl, h, offs, p),
{
    let n = Node::Block(Box::new(b));
    let ob = seq![csize(b, nl, h, offs.len() + 1) as int] + offs;
    assert(ob.len() == offs.len() + 1);
    assert forall|pos: int, fs: clazel_codecheck::a64::spec::Facts|
        pf(n, nl, h, offs.len(), pos, p) implies #[trigger] ucheck(
        utmpl(n, nl, h, offs),
        pos,
        fs,
        p,
    ) is Some by {
        assert(pf(b, nl, h, ob.len(), pos, p)) by {
            assert forall|x: int| #[trigger] prot(b, nl, h, ob.len(), x) implies !p(pos + x) by {
                assert(prot(n, nl, h, offs.len(), x));
            }
        }
    }
}

/// `loop`.
proof fn lemma_uc_loop(b: Node, nl: nat, h: nat, offs: Seq<int>, p: spec_fn(int) -> bool)
    requires
        uc_all(b, nl, h, seq![0int] + offs, p),
    ensures
        uc_all(Node::Loop(Box::new(b)), nl, h, offs, p),
{
    let n = Node::Loop(Box::new(b));
    let ob = seq![0int] + offs;
    assert(ob.len() == offs.len() + 1);
    assert forall|pos: int, fs: clazel_codecheck::a64::spec::Facts|
        pf(n, nl, h, offs.len(), pos, p) implies #[trigger] ucheck(
        utmpl(n, nl, h, offs),
        pos,
        fs,
        p,
    ) is Some by {
        assert(pf(b, nl, h, ob.len(), pos, p)) by {
            assert forall|x: int| #[trigger] prot(b, nl, h, ob.len(), x) implies !p(pos + x) by {
                assert(prot(n, nl, h, offs.len(), x));
            }
        }
    }
}

/// A node whose units are simple instructions, or an exit sequence.
proof fn lemma_uc_leaf(n: Node, nl: nat, h: nat, offs: Seq<int>, p: spec_fn(int) -> bool)
    requires
        cf_flow(n, nl, h, offs.len()) is Some,
        n is Op || n is Br || n is BrIf || n is BrTable || n is Exit,
    ensures
        uc_all(n, nl, h, offs, p),
{
    assert forall|pos: int, fs: clazel_codecheck::a64::spec::Facts|
        pf(n, nl, h, offs.len(), pos, p) implies #[trigger] ucheck(
        utmpl(n, nl, h, offs),
        pos,
        fs,
        p,
    ) is Some by {
        match n {
            Node::Op(o) => {
                lemma_tmpl_straight(o, nl, h);
                assert(all_simp(tmpl(o, nl, h))) by {
                    assert forall|k: int| 0 <= k < tmpl(o, nl, h).len() implies simp(
                        #[trigger] tmpl(o, nl, h)[k],
                    ) by {
                        assert(straight(tmpl(o, nl, h)[k]));
                    }
                }
                lemma_ones_ucheck(tmpl(o, nl, h), pos, fs, p);
            },
            Node::Br(l) => {
                let rel = if l < offs.len() {
                    offs[l as int]
                } else {
                    0
                };
                assert(ctmpl(n, nl, h, offs) == seq![b_i(rel)]);
                lemma_b_simp(rel);
                lemma_ones_ucheck(ctmpl(n, nl, h, offs), pos, fs, p);
            },
            Node::BrIf(l) => {
                let rel = if l < offs.len() {
                    offs[l as int] - 4
                } else {
                    0
                };
                lemma_cond_pre_simp(nl, h, false, rel);
                assert(ctmpl(n, nl, h, offs) == cond_pre(nl, h, false, rel));
                lemma_ones_ucheck(ctmpl(n, nl, h, offs), pos, fs, p);
            },
            Node::BrTable(ls, dd) => {
                lemma_brt_simp(ls@, dd, nl, h, offs);
                lemma_ones_ucheck(ctmpl(n, nl, h, offs), pos, fs, p);
            },
            Node::Exit(c, _) => {
                lemma_ucheck_one(exit_seq(c as u16), pos, fs, p);
                assert(exit_seq(c as u16).len() == 3);
            },
            _ => {},
        }
    }
}

/// A memory instruction.
proof fn lemma_uc_mem_node(m: MemOp, nl: nat, h: nat, offs: Seq<int>, p: spec_fn(int) -> bool)
    requires
        cf_flow(Node::Mem(m), nl, h, offs.len()) is Some,
    ensures
        uc_all(Node::Mem(m), nl, h, offs, p),
{
    let n = Node::Mem(m);
    let d = offs.len();
    assert(cf_flow(n, nl, h, 0) is Some);
    assert forall|pos: int, fs: clazel_codecheck::a64::spec::Facts|
        pf(n, nl, h, d, pos, p) implies #[trigger] ucheck(utmpl(n, nl, h, offs), pos, fs, p) is Some by {
        let x1 = code_len(mem_pre(m, nl, h)) as int;
        let x2 = (code_len(mem_pre(m, nl, h)) + code_len(mem_check(m, nl, h))) as int;
        assert(prot(n, nl, h, d, x1));
        assert(prot(n, nl, h, d, x2));
        lemma_uc_mem(m, nl, h, pos, fs, p);
    }
}

/// **The scan accepts the units of every template.**
pub proof fn lemma_utmpl_ucheck(n: Node, nl: nat, h: nat, offs: Seq<int>, p: spec_fn(int) -> bool)
    requires
        cf_flow(n, nl, h, offs.len()) is Some,
    ensures
        uc_all(n, nl, h, offs, p),
    decreases n,
{
    let d = offs.len();
    match n {
        Node::Mem(m) => {
            lemma_uc_mem_node(m, nl, h, offs, p);
        },
        Node::Then(a, b) => {
            let sa = csize(*a, nl, h, d);
            let ob = shift(offs, sa as int);
            lemma_utmpl_ucheck(*a, nl, h, offs, p);
            match cf_flow(*a, nl, h, d) {
                Some(Flow::Falls(h1)) => {
                    assert(ob.len() == d);
                    lemma_utmpl_ucheck(*b, nl, h1, ob, p);
                },
                _ => {},
            }
            lemma_uc_then(*a, *b, nl, h, offs, p);
        },
        Node::Block(b) => {
            let ob = seq![csize(*b, nl, h, d + 1) as int] + offs;
            assert(ob.len() == d + 1);
            lemma_utmpl_ucheck(*b, nl, h, ob, p);
            lemma_uc_block(*b, nl, h, offs, p);
        },
        Node::Loop(b) => {
            let ob = seq![0int] + offs;
            assert(ob.len() == d + 1);
            lemma_utmpl_ucheck(*b, nl, h, ob, p);
            lemma_uc_loop(*b, nl, h, offs, p);
        },
        Node::If(t, e) => {
            let st = csize(*t, nl, (h - 1) as nat, d + 1) as int;
            let se = csize(*e, nl, (h - 1) as nat, d + 1) as int;
            let ot = seq![st + 4 + se] + shift(offs, 8);
            let oe = seq![se] + shift(offs, 12 + st);
            assert(ot.len() == d + 1 && oe.len() == d + 1);
            lemma_utmpl_ucheck(*t, nl, (h - 1) as nat, ot, p);
            lemma_utmpl_ucheck(*e, nl, (h - 1) as nat, oe, p);
            lemma_uc_if(*t, *e, nl, h, offs, p);
        },
        _ => {
            lemma_uc_leaf(n, nl, h, offs, p);
        },
    }
}

} // verus!
