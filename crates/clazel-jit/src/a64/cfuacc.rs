//! The validator accepts the units of every A64 template (jit.md item J.9,
//! "every emitted blob is accepted"): every unit of [`utmpl`] is well formed
//! ([`super::cfunits::uok`]) and the scan ([`ucheck`]) accepts them, whatever
//! it knew before, provided no branch lands on the start of a memory
//! instruction's check or access ([`prot`]). The counterpart of
//! [`crate::cfuacc`].
//!
//! The one place the scan needs what it learnt earlier is the access of a
//! `load` or `store`: it needs `x3` to hold region `k`'s base (the load before
//! the check) and `x1` to be checked for the access's size (the check
//! itself), and nothing may have made it forget in between, which is what
//! [`prot`] rules out.

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
use super::cfunits::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every instruction of the list is simple.
pub open spec fn all_simp(c: Seq<isa::Instr>) -> bool {
    forall|k: int| 0 <= k < c.len() ==> simp(#[trigger] c[k])
}

/// Single-instruction units of simple instructions are well formed.
pub proof fn lemma_ones_uok(c: Seq<isa::Instr>)
    requires
        forall|k: int| 0 <= k < c.len() ==> ok2(#[trigger] c[k]),
    ensures
        forall|k: int| 0 <= k < ones(c).len() ==> uok(#[trigger] ones(c)[k]),
{
    lemma_uflat_ones(c);
    assert forall|k: int| 0 <= k < ones(c).len() implies uok(#[trigger] ones(c)[k]) by {
        assert(ones(c)[k] == seq![c[k]]);
        assert(ok2(c[k]));
    }
}

/// The scan accepts single-instruction units of simple instructions, whatever
/// it knew.
pub proof fn lemma_ones_ucheck(
    c: Seq<isa::Instr>,
    pos: int,
    fs: clazel_codecheck::a64::spec::Facts,
    p: spec_fn(int) -> bool,
)
    requires
        all_simp(c),
    ensures
        ucheck(ones(c), pos, fs, p) is Some,
    decreases c.len(),
{
    if c.len() > 0 {
        lemma_uflat_ones(c);
        assert(ones(c)[0] == seq![c[0]]);
        let fs0 = if p(pos) {
            clazel_codecheck::a64::spec::no_facts()
        } else {
            fs
        };
        lemma_simp_plain(fs0, c[0]);
        let f = clazel_codecheck::a64::spec::plain_ok(fs0, c[0])->Some_0;
        assert(ufacts(seq![c[0]], fs0) == Some(f));
        assert(ones(c).skip(1) =~= ones(c.skip(1)));
        assert(all_simp(c.skip(1))) by {
            assert forall|k: int| 0 <= k < c.skip(1).len() implies simp(#[trigger] c.skip(1)[k]) by {
                assert(c.skip(1)[k] == c[k + 1]);
            }
        }
        lemma_ones_ucheck(c.skip(1), pos + code_len(seq![c[0]]) as int, f, p);
    }
}

// ----------------------------------------------------------------------------
// The simple instructions of the templates
// ----------------------------------------------------------------------------

/// The condition test is simple.
pub proof fn lemma_cond_pre_simp(nl: nat, h: nat, iszero: bool, rel: int)
    requires
        1 <= h,
        nl + h <= max_slots(),
    ensures
        all_simp(cond_pre(nl, h, iszero, rel)),
{
    assert(max_slots() == 31) by {
        super::tlemmas::lemma_abi_consts_t();
    }
    let c = cond_pre(nl, h, iszero, rel);
    assert forall|k: int| 0 <= k < c.len() implies simp(#[trigger] c[k]) by {
        assert(k == 0 || k == 1);
    }
}

/// A `b` is simple.
pub proof fn lemma_b_simp(rel: int)
    ensures
        all_simp(seq![b_i(rel)]),
{
    let c = seq![b_i(rel)];
    assert forall|k: int| 0 <= k < c.len() implies simp(#[trigger] c[k]) by {
        assert(k == 0);
    }
}

/// The chain of `br_table` is simple.
pub proof fn lemma_entries_simp(ls: Seq<usize>, offs: Seq<int>, p0: int, i: nat)
    ensures
        all_simp(brt_entries(ls, offs, p0, i)),
    decreases ls.len() - i,
{
    if i < ls.len() {
        let e = brt_entry(i, brt_rel(offs, ls[i as int], p0 + i * brt_e() + 8));
        assert forall|k: int| 0 <= k < e.len() implies simp(#[trigger] e[k]) by {
            assert(k == 0 || k == 1 || k == 2);
        }
        lemma_entries_simp(ls, offs, p0, i + 1);
        let r = brt_entries(ls, offs, p0, i + 1);
        assert(brt_entries(ls, offs, p0, i) == e + r);
        assert forall|k: int| 0 <= k < (e + r).len() implies simp(#[trigger] (e + r)[k]) by {
            if k < e.len() {
                assert((e + r)[k] == e[k]);
            } else {
                assert((e + r)[k] == r[k - e.len()]);
            }
        }
    } else {
        assert(brt_entries(ls, offs, p0, i) =~= Seq::<isa::Instr>::empty());
    }
}

/// The whole `br_table` is simple.
pub proof fn lemma_brt_simp(ls: Seq<usize>, d: usize, nl: nat, h: nat, offs: Seq<int>)
    requires
        1 <= h,
        nl + h <= max_slots(),
    ensures
        all_simp(brt_code(ls, d, nl, h, offs)),
{
    assert(max_slots() == 31) by {
        super::tlemmas::lemma_abi_consts_t();
    }
    let p0 = brt_p0(nl, h);
    let a = seq![load_slot(x0(), (nl + h - 1) as nat)];
    let ch = brt_entries(ls, offs, p0, 0);
    let jm = seq![b_i(brt_rel(offs, d, p0 + ls.len() * brt_e()))];
    lemma_entries_simp(ls, offs, p0, 0);
    assert(all_simp(a)) by {
        assert forall|k: int| 0 <= k < a.len() implies simp(#[trigger] a[k]) by {
            assert(k == 0);
        }
    }
    lemma_b_simp(brt_rel(offs, d, p0 + ls.len() * brt_e()));
    let whole = brt_code(ls, d, nl, h, offs);
    assert(whole == a + ch + jm);
    assert forall|k: int| 0 <= k < whole.len() implies simp(#[trigger] whole[k]) by {
        if k < a.len() {
            assert(whole[k] == a[k]);
        } else if k < a.len() + ch.len() {
            assert(whole[k] == ch[k - a.len()]);
        } else {
            assert(whole[k] == jm[k - a.len() - ch.len()]);
        }
    }
}

// ----------------------------------------------------------------------------
// Memory instructions
// ----------------------------------------------------------------------------

/// The validator reads the bounds-check sequence of the template as a unit.
pub proof fn lemma_check_unit(c: clazel_codecheck::a64::spec::Chk)
    requires
        clazel_codecheck::a64::spec::check_ok(c),
        0 <= c.n <= 8,
    ensures
        clazel_codecheck::a64::spec::check_unit_at(clazel_codecheck::a64::spec::check_seq(c), 0),
        clazel_codecheck::a64::spec::check_params(clazel_codecheck::a64::spec::check_seq(c), 0)
            == Some(c),
{
    let cs = clazel_codecheck::a64::spec::check_seq(c);
    assert(cs[0] == clazel_codecheck::a64::spec::check_instr(0, c));
    assert(cs[1] == clazel_codecheck::a64::spec::check_instr(1, c));
    assert(cs[2] == clazel_codecheck::a64::spec::check_instr(2, c));
    assert(cs[3] == clazel_codecheck::a64::spec::check_instr(3, c));
    assert(cs[4] == clazel_codecheck::a64::spec::check_instr(4, c));
    assert(cs[5] == clazel_codecheck::a64::spec::check_instr(5, c));
    assert(cs[6] == clazel_codecheck::a64::spec::check_instr(6, c));
    let bo = abi::bound_off(c.k);
    assert(bo == 16 * c.k + 8);
    assert((bo / 8) as u16 as int == 2 * c.k + 1) by (nonlinear_arith)
        requires
            bo == 16 * c.k + 8,
            0 <= c.k < 16,
    ;
    assert((c.n as u16) as int == c.n);
    let o = (bo / 8) as u16;
    assert(((o as int) * 8 - 8) / 16 == c.k) by (nonlinear_arith)
        requires
            o as int == 2 * c.k + 1,
            0 <= c.k < 16,
    ;
    let c2 = clazel_codecheck::a64::spec::check_params(cs, 0)->Some_0;
    assert(c2 == c);
}

/// `fact_of` after one more binding.
pub proof fn lemma_fact_of_push(
    fs: clazel_codecheck::a64::spec::Facts,
    b: clazel_codecheck::a64::spec::Binding,
    r: u8,
)
    ensures
        clazel_codecheck::a64::spec::fact_of(fs.push(b), r) == if b.reg == r {
            b.fact
        } else {
            clazel_codecheck::a64::spec::fact_of(fs, r)
        },
{
    assert(fs.push(b).drop_last() =~= fs);
    assert(fs.push(b).last() == b);
}

/// The load of a region's base gives `x3` that region, whatever the scan
/// knew.
pub proof fn lemma_base_load(fs: clazel_codecheck::a64::spec::Facts, k: nat)
    requires
        k < 16,
    ensures
        clazel_codecheck::a64::spec::plain_ok(fs, base_ld(k)) == Some(
            fs.push(
                clazel_codecheck::a64::spec::Binding {
                    reg: 3,
                    fact: clazel_codecheck::a64::spec::Fact::Base(k as int),
                },
            ),
        ),
{
    let i = base_ld(k);
    assert(abi::base_off(k as int) == 16 * k);
    assert(((16 * k) / 8) as u16 as int == 2 * k) by (nonlinear_arith)
        requires
            k < 16,
    ;
    assert(clazel_codecheck::a64::spec::base_load_region(i) == Some(k as int)) by {
        assert((2 * k * 8) / 16 == k) by (nonlinear_arith);
    }
    assert(clazel_codecheck::a64::spec::access_ok(
        fs,
        clazel_codecheck::a64::spec::mem_access(i)->Some_0,
    ));
}

/// What the scan knows after the check: `x3` is region `k`'s base, and `x1`
/// is checked for `n` bytes. Then an access of at most `n` bytes through
/// `[x3, x1]` is admitted.
pub proof fn lemma_access_after(
    fs: clazel_codecheck::a64::spec::Facts,
    k: int,
    n: int,
    size: int,
    store: bool,
    sf: isa::Width,
    t: u8,
)
    requires
        size <= n,
        clazel_codecheck::a64::spec::fact_of(fs, 3) == clazel_codecheck::a64::spec::Fact::Base(k),
    ensures
        clazel_codecheck::a64::spec::access_ok(
            fs.push(clazel_codecheck::a64::spec::Binding {
                reg: 0,
                fact: clazel_codecheck::a64::spec::Fact::Unknown,
            }).push(
                clazel_codecheck::a64::spec::Binding {
                    reg: 2,
                    fact: clazel_codecheck::a64::spec::Fact::Unknown,
                },
            ).push(
                clazel_codecheck::a64::spec::Binding {
                    reg: 1,
                    fact: clazel_codecheck::a64::spec::Fact::Idx(k, n),
                },
            ),
            clazel_codecheck::a64::spec::Access {
                base: 3,
                index: Some(1u8),
                scaled: false,
                off: 0,
                size: size,
                store: store,
            },
        ),
{
    let b0 = clazel_codecheck::a64::spec::Binding {
        reg: 0,
        fact: clazel_codecheck::a64::spec::Fact::Unknown,
    };
    let b2 = clazel_codecheck::a64::spec::Binding {
        reg: 2,
        fact: clazel_codecheck::a64::spec::Fact::Unknown,
    };
    let b1 = clazel_codecheck::a64::spec::Binding {
        reg: 1,
        fact: clazel_codecheck::a64::spec::Fact::Idx(k, n),
    };
    let f1 = fs.push(b0);
    let f2 = f1.push(b2);
    let f3 = f2.push(b1);
    lemma_fact_of_push(fs, b0, 3);
    lemma_fact_of_push(f1, b2, 3);
    lemma_fact_of_push(f2, b1, 3);
    lemma_fact_of_push(f2, b1, 1);
}

/// What the scan knows after the check, as the validator computes it from the
/// check's instructions.
proof fn lemma_check_facts_of(
    c: clazel_codecheck::a64::spec::Chk,
    fs: clazel_codecheck::a64::spec::Facts,
)
    requires
        clazel_codecheck::a64::spec::check_ok(c),
        0 <= c.n <= 8,
    ensures
        clazel_codecheck::a64::spec::check_facts(
            fs,
            clazel_codecheck::a64::spec::check_seq(c),
            0,
        ) == fs.push(
            clazel_codecheck::a64::spec::Binding {
                reg: c.t,
                fact: clazel_codecheck::a64::spec::Fact::Unknown,
            },
        ).push(
            clazel_codecheck::a64::spec::Binding {
                reg: c.bnd,
                fact: clazel_codecheck::a64::spec::Fact::Unknown,
            },
        ).push(
            clazel_codecheck::a64::spec::Binding {
                reg: c.i,
                fact: clazel_codecheck::a64::spec::Fact::Idx(c.k, c.n),
            },
        ),
{
    lemma_check_unit(c);
}

/// The check of a memory instruction is well formed for the validator.
pub proof fn lemma_mem_check_ok(m: MemOp, nl: nat, h: nat)
    requires
        cf_flow(Node::Mem(m), nl, h, 0) is Some,
    ensures
        clazel_codecheck::a64::spec::check_ok(
            mem_chk(mem_region(m), mem_n(m), mem_r1(m, nl, h), mem_r2(m, nl, h)),
        ),
        0 <= mem_n(m) <= 8,
        mem_region(m) < 16,
{
    assert(abi::reserved(0) == false && abi::reserved(1) == false && abi::reserved(2) == false);
    match m {
        MemOp::BoundsCheck { .. } => {},
        MemOp::Load { ty, .. } => {
            assert(ty.size() == 4 || ty.size() == 8);
        },
        MemOp::Store { ty, .. } => {
            assert(ty.size() == 4 || ty.size() == 8);
        },
    }
}

/// The scan over one unit.
pub proof fn lemma_ucheck_one(
    u: Seq<isa::Instr>,
    pos: int,
    fs: clazel_codecheck::a64::spec::Facts,
    p: spec_fn(int) -> bool,
)
    ensures
        ucheck(seq![u], pos, fs, p) == ufacts(u, if p(pos) {
            clazel_codecheck::a64::spec::no_facts()
        } else {
            fs
        }),
{
    assert(seq![u].skip(1) =~= Seq::<Seq<isa::Instr>>::empty());
    let fs0 = if p(pos) {
        clazel_codecheck::a64::spec::no_facts()
    } else {
        fs
    };
    match ufacts(u, fs0) {
        None => {},
        Some(f) => {
            assert(ucheck(Seq::<Seq<isa::Instr>>::empty(), pos + code_len(u) as int, f, p) == Some(
                f,
            ));
        },
    }
}

/// One instruction as a one-unit list.
pub proof fn lemma_ones_one(i: isa::Instr)
    ensures
        ones(seq![i]) =~= seq![seq![i]],
{
    lemma_uflat_ones(seq![i]);
    assert(ones(seq![i]).len() == 1);
    assert(ones(seq![i])[0] == seq![i]);
}

/// `ones` of a concatenation.
proof fn lemma_ones_cat(a: Seq<isa::Instr>, b: Seq<isa::Instr>)
    ensures
        ones(a + b) =~= ones(a) + ones(b),
{
    lemma_uflat_ones(a);
    lemma_uflat_ones(b);
    lemma_uflat_ones(a + b);
    assert forall|q: int| 0 <= q < ones(a + b).len() implies ones(a + b)[q] == (ones(a)
        + ones(b))[q] by {
        if q < a.len() {
            assert((a + b)[q] == a[q]);
        } else {
            assert((a + b)[q] == b[q - a.len()]);
        }
    }
}

/// The scan over the first part of a memory instruction: the operands and the
/// base. For a load or a store it ends knowing `x3` is region `k`'s base.
proof fn lemma_pre_ucheck(
    m: MemOp,
    nl: nat,
    h: nat,
    pos: int,
    fs: clazel_codecheck::a64::spec::Facts,
    p: spec_fn(int) -> bool,
)
    requires
        cf_flow(Node::Mem(m), nl, h, 0) is Some,
    ensures
        ucheck(ones(mem_pre(m, nl, h)), pos, fs, p) is Some,
        !(m is BoundsCheck) ==> clazel_codecheck::a64::spec::fact_of(
            ucheck(ones(mem_pre(m, nl, h)), pos, fs, p)->Some_0,
            3,
        ) == clazel_codecheck::a64::spec::Fact::Base(mem_region(m) as int),
{
    assert(max_slots() == 31) by {
        super::tlemmas::lemma_abi_consts_t();
    }
    let pre = mem_pre(m, nl, h);
    let k = mem_region(m);
    match m {
        MemOp::BoundsCheck { .. } => {
            assert(all_simp(pre)) by {
                assert forall|q: int| 0 <= q < pre.len() implies simp(#[trigger] pre[q]) by {
                    assert(q == 0);
                }
            }
            lemma_ones_ucheck(pre, pos, fs, p);
        },
        MemOp::Load { .. } | MemOp::Store { .. } => {
            let last = base_ld(k);
            let init = pre.drop_last();
            assert(pre.last() == last);
            lemma_load_slot_straight(x1(), (nl + h - 1) as nat);
            lemma_load_slot_straight(x4(), (nl + h - 1) as nat);
            if m is Store {
                lemma_load_slot_straight(x1(), (nl + h - 2) as nat);
            }
            assert(all_simp(init)) by {
                assert forall|q: int| 0 <= q < init.len() implies simp(#[trigger] init[q]) by {
                    assert(init[q] == pre[q]);
                    assert(q == 0 || q == 1);
                }
            }
            assert(pre =~= init + seq![last]);
            lemma_ones_cat(init, seq![last]);
            lemma_ones_one(last);
            lemma_ucheck_cat(ones(init), ones(seq![last]), pos, fs, p);
            lemma_ones_ucheck(init, pos, fs, p);
            let f0 = ucheck(ones(init), pos, fs, p)->Some_0;
            lemma_blen_ones(init);
            let q = pos + code_len(init);
            let fs0 = if p(q) {
                clazel_codecheck::a64::spec::no_facts()
            } else {
                f0
            };
            lemma_base_load(fs0, k);
            lemma_ucheck_one(seq![last], q, f0, p);
            let b3 = clazel_codecheck::a64::spec::Binding {
                reg: 3,
                fact: clazel_codecheck::a64::spec::Fact::Base(k as int),
            };
            assert(ufacts(seq![last], fs0) == Some(fs0.push(b3)));
            lemma_fact_of_push(fs0, b3, 3);
        },
    }
}

/// The access of a load or a store is admitted after the check.
proof fn lemma_tail_ucheck(
    m: MemOp,
    nl: nat,
    h: nat,
    pos: int,
    f1: clazel_codecheck::a64::spec::Facts,
    p: spec_fn(int) -> bool,
)
    requires
        cf_flow(Node::Mem(m), nl, h, 0) is Some,
        !(m is BoundsCheck) ==> clazel_codecheck::a64::spec::fact_of(f1, 3)
            == clazel_codecheck::a64::spec::Fact::Base(mem_region(m) as int),
        !p(pos),
    ensures
        ucheck(
            ones(mem_tail(m, nl, h)),
            pos,
            f1.push(clazel_codecheck::a64::spec::Binding {
                reg: 0,
                fact: clazel_codecheck::a64::spec::Fact::Unknown,
            }).push(
                clazel_codecheck::a64::spec::Binding {
                    reg: 2,
                    fact: clazel_codecheck::a64::spec::Fact::Unknown,
                },
            ).push(
                clazel_codecheck::a64::spec::Binding {
                    reg: 1,
                    fact: clazel_codecheck::a64::spec::Fact::Idx(
                        mem_region(m) as int,
                        mem_n(m) as int,
                    ),
                },
            ),
            p,
        ) is Some,
{
    assert(max_slots() == 31) by {
        super::tlemmas::lemma_abi_consts_t();
    }
    let tail = mem_tail(m, nl, h);
    let k = mem_region(m) as int;
    let n = mem_n(m) as int;
    let f3 = f1.push(
        clazel_codecheck::a64::spec::Binding {
            reg: 0,
            fact: clazel_codecheck::a64::spec::Fact::Unknown,
        },
    ).push(
        clazel_codecheck::a64::spec::Binding {
            reg: 2,
            fact: clazel_codecheck::a64::spec::Fact::Unknown,
        },
    ).push(
        clazel_codecheck::a64::spec::Binding {
            reg: 1,
            fact: clazel_codecheck::a64::spec::Fact::Idx(k, n),
        },
    );
    match m {
        MemOp::BoundsCheck { .. } => {
            assert(tail =~= Seq::<isa::Instr>::empty());
            assert(ones(tail) =~= Seq::<Seq<isa::Instr>>::empty());
            assert(ucheck(ones(tail), pos, f3, p) == Some(f3));
        },
        MemOp::Load { ty, .. } => {
            let acc = isa::Instr::LoadStoreReg {
                sf: mty_sf(ty),
                load: true,
                t: x0(),
                n: x3(),
                m: x1(),
                s: false,
            };
            let st = store_slot((nl + h - 1) as nat, x0());
            assert(tail == seq![acc, st]);
            lemma_access_after(f1, k, n, clazel_codecheck::a64::spec::nbytes(mty_sf(ty)), false, mty_sf(ty), x0());
            let a = clazel_codecheck::a64::spec::mem_access(acc)->Some_0;
            assert(clazel_codecheck::a64::spec::access_ok(f3, a));
            assert(!clazel_codecheck::a64::spec::writes_reserved(acc));
            assert(clazel_codecheck::a64::spec::plain_ok(f3, acc) is Some);
            let f4 = clazel_codecheck::a64::spec::plain_ok(f3, acc)->Some_0;
            assert(tail =~= seq![acc] + seq![st]);
            lemma_ones_cat(seq![acc], seq![st]);
            lemma_ones_one(acc);
            lemma_ucheck_cat(ones(seq![acc]), ones(seq![st]), pos, f3, p);
            lemma_ucheck_one(seq![acc], pos, f3, p);
            assert(ufacts(seq![acc], f3) == Some(f4));
            lemma_blen_ones(seq![acc]);
            lemma_load_slot_straight(0, (nl + h - 1) as nat);
            assert(all_simp(seq![st])) by {
                assert forall|q: int| 0 <= q < 1 implies simp(#[trigger] seq![st][q]) by {
                    assert(q == 0);
                }
            }
            lemma_ones_ucheck(seq![st], pos + code_len(seq![acc]) as int, f4, p);
        },
        MemOp::Store { ty, .. } => {
            let acc = isa::Instr::LoadStoreReg {
                sf: mty_sf(ty),
                load: false,
                t: x4(),
                n: x3(),
                m: x1(),
                s: false,
            };
            assert(tail == seq![acc]);
            lemma_access_after(f1, k, n, clazel_codecheck::a64::spec::nbytes(mty_sf(ty)), true, mty_sf(ty), x4());
            let a = clazel_codecheck::a64::spec::mem_access(acc)->Some_0;
            assert(clazel_codecheck::a64::spec::access_ok(f3, a));
            assert(!clazel_codecheck::a64::spec::writes_reserved(acc));
            assert(clazel_codecheck::a64::spec::plain_ok(f3, acc) is Some);
            lemma_ones_one(acc);
            lemma_ucheck_one(seq![acc], pos, f3, p);
        },
    }
}

/// **A memory instruction is accepted**, whatever the scan knew, if no branch
/// lands on the start of its check or of its access.
pub proof fn lemma_uc_mem(
    m: MemOp,
    nl: nat,
    h: nat,
    pos: int,
    fs: clazel_codecheck::a64::spec::Facts,
    p: spec_fn(int) -> bool,
)
    requires
        cf_flow(Node::Mem(m), nl, h, 0) is Some,
        !p(pos + code_len(mem_pre(m, nl, h))),
        !p(pos + code_len(mem_pre(m, nl, h)) + code_len(mem_check(m, nl, h))),
    ensures
        ucheck(mem_units(m, nl, h), pos, fs, p) is Some,
{
    lemma_mem_check_ok(m, nl, h);
    let pre = mem_pre(m, nl, h);
    let tail = mem_tail(m, nl, h);
    let chk = mem_check(m, nl, h);
    let jm = seq![b_i(code_len(exit_seq(mem_exit_code(m))) as int + 4)];
    let stub = exit_seq(mem_exit_code(m));
    let c0 = mem_chk(mem_region(m), mem_n(m), mem_r1(m, nl, h), mem_r2(m, nl, h));
    let k = mem_region(m) as int;
    let n = mem_n(m) as int;
    let b1 = code_len(pre) as int;
    let b2 = b1 + code_len(chk) as int;
    lemma_pre_ucheck(m, nl, h, pos, fs, p);
    let f1 = ucheck(ones(pre), pos, fs, p)->Some_0;
    lemma_blen_ones(pre);
    // the check
    lemma_check_unit(c0);
    assert(chk == clazel_codecheck::a64::spec::check_seq(c0));
    lemma_check_facts_of(c0, f1);
    let f2 = clazel_codecheck::a64::spec::check_facts(f1, chk, 0);
    lemma_ucheck_one(chk, pos + b1, f1, p);
    assert(ufacts(chk, f1) == Some(f2));
    lemma_blen_one(chk);
    // the access
    lemma_tail_ucheck(m, nl, h, pos + b2, f1, p);
    let f3 = ucheck(ones(tail), pos + b2, f2, p)->Some_0;
    lemma_blen_ones(tail);
    // the b and the stub
    lemma_b_simp(code_len(stub) as int + 4);
    let q = pos + b2 + code_len(tail) as int;
    let fj = if p(q) {
        clazel_codecheck::a64::spec::no_facts()
    } else {
        f3
    };
    lemma_simp_plain(fj, jm[0]);
    assert(ufacts(jm, fj) is Some);
    assert(code_len(stub) == 12);
    assert(seq![jm, stub] =~= seq![jm] + seq![stub]);
    lemma_ucheck_cat(seq![jm], seq![stub], q, f3, p);
    lemma_ucheck_one(jm, q, f3, p);
    lemma_blen_one(jm);
    let fj1 = ufacts(jm, fj)->Some_0;
    lemma_ucheck_one(stub, q + code_len(jm) as int, fj1, p);
    assert(stub.len() == 3);
    // put the parts together
    let u1 = ones(pre);
    let u2 = seq![chk];
    let u3 = ones(tail);
    let u4 = seq![jm, stub];
    assert(mem_units(m, nl, h) =~= u1 + u2 + u3 + u4);
    lemma_ucheck_cat(u1, u2, pos, fs, p);
    lemma_ucheck_cat(u1 + u2, u3, pos, fs, p);
    lemma_ucheck_cat(u1 + u2 + u3, u4, pos, fs, p);
    lemma_blen_cat(u1, u2);
    lemma_blen_cat(u1 + u2, u3);
    assert(blen(u1) == b1);
    assert(blen(u1 + u2) == b2);
    assert(blen(u1 + u2 + u3) == b2 + code_len(tail));
}

} // verus!
