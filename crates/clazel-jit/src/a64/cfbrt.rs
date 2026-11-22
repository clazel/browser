//! **`br_table` refines its LIR instruction** ([`lemma_brt_cf`]): the code is
//! [`super::cftemplates::brt_code`], `ldr x0, [index]`, a `movz`, `cmp` and
//! `b.eq` per target, and a `b` to the default (the subset has no indirect
//! branch). The proof runs the chain by induction on the entry. The A64
//! counterpart of [`crate::cfbrt`]; each entry is 3 words, so entry `i` is at
//! word `1 + 3 i` and the final `b` at word `1 + 3 n`.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::cfalg::*;
#[cfg(verus_only)]
use super::cfchk::*;
#[cfg(verus_only)]
use super::cfcontract::*;
#[cfg(verus_only)]
use super::cffit::*;
#[cfg(verus_only)]
use super::cfleaf::*;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cfsteps::*;
#[cfg(verus_only)]
use super::cftemplates::*;
#[cfg(verus_only)]
use super::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The chain from entry `k` is 12 bytes per entry left, and entry `i`'s words
/// are at `3 (i - k)` in it.
pub proof fn lemma_entries_at(ls: Seq<usize>, offs: Seq<int>, p0: int, k: nat)
    ensures
        brt_entries(ls, offs, p0, k).len() == if k >= ls.len() {
            0nat
        } else {
            (3 * (ls.len() - k)) as nat
        },
        forall|i: nat, t: int|
            k <= i < ls.len() && 0 <= t < 3 ==> #[trigger] brt_entries(ls, offs, p0, k)[3 * (i
                - k) + t] == brt_entry(
                i,
                brt_rel(offs, ls[i as int], p0 + i * brt_e() + 8),
            )[t],
    decreases ls.len() - k,
{
    if k < ls.len() {
        let e = brt_entry(k, brt_rel(offs, ls[k as int], p0 + k * brt_e() + 8));
        lemma_entries_at(ls, offs, p0, k + 1);
        let rest = brt_entries(ls, offs, p0, k + 1);
        let ch = brt_entries(ls, offs, p0, k);
        assert(ch == e + rest);
        assert(e.len() == 3);
        assert forall|i: nat, t: int|
            k <= i < ls.len() && 0 <= t < 3 implies #[trigger] ch[3 * (i - k) + t] == brt_entry(
            i,
            brt_rel(offs, ls[i as int], p0 + i * brt_e() + 8),
        )[t] by {
            if i == k {
            } else {
                assert(ch[3 * (i - k) + t] == rest[3 * (i - (k + 1)) + t]);
            }
        }
    }
}

/// **The shape of the whole code**: the load, entry `i`'s words at `1 + 3 i`,
/// and the final `b` at `1 + 3 n`.
pub proof fn lemma_brt_shape(ls: Seq<usize>, d: usize, nl: nat, h: nat, offs: Seq<int>)
    ensures
        ({
            let w = brt_code(ls, d, nl, h, offs);
            let n = ls.len();
            &&& w.len() == 2 + 3 * n
            &&& w[0] == load_slot(x0(), (nl + h - 1) as nat)
            &&& forall|i: nat, t: int|
                i < n && 0 <= t < 3 ==> #[trigger] w[(1 + 3 * i) as int + t] == brt_entry(
                    i,
                    brt_rel(offs, ls[i as int], (4 + i * 12 + 8) as int),
                )[t]
            &&& w[(1 + 3 * n) as int] == b_i(brt_rel(offs, d, (4 + n * 12) as int))
        }),
{
    assert(brt_p0(nl, h) == 4);
    assert(brt_e() == 12);
    let p0 = brt_p0(nl, h);
    lemma_entries_at(ls, offs, p0, 0);
    let a = seq![load_slot(x0(), (nl + h - 1) as nat)];
    let ch = brt_entries(ls, offs, p0, 0);
    let jm = seq![b_i(brt_rel(offs, d, p0 + ls.len() * brt_e()))];
    let w = brt_code(ls, d, nl, h, offs);
    assert(w == a + ch + jm);
    let n = ls.len();
    assert forall|i: nat, t: int|
        i < n && 0 <= t < 3 implies #[trigger] w[(1 + 3 * i) as int + t] == brt_entry(
        i,
        brt_rel(offs, ls[i as int], (4 + i * 12 + 8) as int),
    )[t] by {
        assert(3 * (i - 0) + t == 3 * i + t);
        assert(ch[3 * (i - 0) + t] == brt_entry(
            i,
            brt_rel(offs, ls[i as int], p0 + i * brt_e() + 8),
        )[t]);
        assert(p0 + i * brt_e() + 8 == (4 + i * 12 + 8) as int);
    }
}

/// What the chain needs of the labels: in scope, within a conditional
/// branch's reach of every place in the code, aligned and addresses.
pub open spec fn brt_labels_ok(ls: Seq<usize>, d: usize, offs: Seq<int>, b0: int) -> bool {
    d < offs.len() && (forall|q: int| 0 <= q < ls.len() ==> #[trigger] ls[q] < offs.len())
        && labels_fit(offs, 8 + 12 * ls.len()) && (forall|l: int|
        0 <= l < offs.len() ==> 0 <= b0 + #[trigger] offs[l] && b0 + offs[l]
            < 0x1_0000_0000_0000_0000) && 0 <= b0 && b0 + 8 + 12 * ls.len()
        < 0x1_0000_0000_0000_0000
}

/// What the chain leaves alone: everything but `x1` (and the flags, `pc`).
pub open spec fn brt_fr(s: isa::State, s2: isa::State) -> bool {
    s2.r.len() == 31 && s.r.len() == 31 && s2.vreg == s.vreg && s2.mem == s.mem && s2.sp == s.sp
        && forall|k: int| 0 <= k < 31 && k != 1 ==> #[trigger] s2.r[k] == s.r[k]
}

/// [`brt_fr`] is transitive.
pub proof fn lemma_brt_fr_trans(s: isa::State, s1: isa::State, s2: isa::State)
    requires
        brt_fr(s, s1),
        brt_fr(s1, s2),
    ensures
        brt_fr(s, s2),
{
}

/// **The final `b`** of the chain, to the default label.
pub proof fn lemma_brt_last(
    ls: Seq<usize>,
    d: usize,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    s: isa::State,
    b0: int,
)
    requires
        ls.len() <= max_targets(),
        brt_labels_ok(ls, d, offs, b0),
        isa::wf(s),
        s.pc as int == b0 + 4 + 12 * ls.len(),
    ensures
        ({
            let whole = brt_code(ls, d, nl, h, offs);
            exists|me: isa::State|
                #![trigger reaches(whole, b0, s, me)]
                reaches(whole, b0, s, me) && isa::wf(me) && brt_fr(s, me) && me.pc as int == b0
                    + offs[d as int]
        }),
{
    super::memlemmas::lemma_p2_consts();
    let whole = brt_code(ls, d, nl, h, offs);
    let n = ls.len();
    lemma_brt_shape(ls, d, nl, h, offs);
    let rel = brt_rel(offs, d, (4 + n * 12) as int);
    assert(rel == offs[d as int] - (4 + n * 12));
    assert(rel % 4 == 0);
    assert(0 <= b0 + offs[d as int] < 0x1_0000_0000_0000_0000);
    lemma_step_b(s, rel);
    let me = isa::State { pc: (s.pc as int + rel) as u64, ..s };
    assert(whole[(1 + 3 * n) as int] == b_i(rel));
    lemma_reach_step(whole, b0, s, (1 + 3 * n) as int, me);
}

/// **One entry of the chain**: `movz w1, #i; cmp w0, w1; b.eq`. The run reaches
/// the label of target `i` when `x0 == i`, else the next entry.
#[verifier::rlimit(800)]
pub proof fn lemma_brt_entry(
    ls: Seq<usize>,
    d: usize,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    i: nat,
    c: u32,
    s: isa::State,
    b0: int,
)
    requires
        i < ls.len(),
        ls.len() <= max_targets(),
        brt_labels_ok(ls, d, offs, b0),
        isa::wf(s),
        s.pc as int == b0 + 4 + 12 * i,
        s.r[0] == c as u64,
    ensures
        ({
            let whole = brt_code(ls, d, nl, h, offs);
            exists|s3: isa::State|
                #![trigger reaches(whole, b0, s, s3)]
                reaches(whole, b0, s, s3) && isa::wf(s3) && brt_fr(s, s3) && s3.pc as int == (
                if c as nat == i {
                    b0 + offs[ls[i as int] as int]
                } else {
                    b0 + 4 + 12 * (i + 1)
                })
        }),
{
    super::memlemmas::lemma_p2_consts();
    let whole = brt_code(ls, d, nl, h, offs);
    let n = ls.len();
    lemma_brt_shape(ls, d, nl, h, offs);
    let li = ls[i as int];
    assert(li < offs.len());
    let pos: int = (4 + i * 12 + 8) as int;
    let rel = brt_rel(offs, li, pos);
    assert(rel == offs[li as int] - pos);
    assert(rel % 4 == 0);
    assert(-0x10_0000 <= rel < 0x10_0000);
    let e = brt_entry(i, rel);
    assert(whole[(1 + 3 * i) as int + 0] == brt_entry(i, brt_rel(offs, ls[i as int], pos))[0]);
    assert(whole[(1 + 3 * i) as int] == e[0]);
    assert(whole[(1 + 3 * i) as int + 1] == e[1]);
    assert(whole[(1 + 3 * i) as int + 2] == e[2]);
    assert(i < 0x1_0000);
    // movz w1, #i
    super::bitmid::lemma_step_movz(s, isa::Width::W32, 1, i as u16, 0);
    assert(super::bitmid::chunk_val(i as u16, 0) == i as int);
    let s1 = isa::step(s, e[0]).unwrap();
    assert(s1.r == s.r.update(1, i as u64));
    lemma_reach_step(whole, b0, s, (1 + 3 * i) as int, s1);
    // cmp w0, w1
    assert(s1.r[0] == c as u64 && s1.r[1] == i as u64);
    assert(e[1] == cmp_rr(isa::Width::W32, 0, 1));
    super::flags::lemma_step_cmp(s1, isa::Width::W32, c as u64, i as u64);
    let s2 = isa::step(s1, e[1]).unwrap();
    lemma_reach_step(whole, b0, s1, (1 + 3 * i) as int + 1, s2);
    lemma_reaches_trans(whole, b0, s, s1, s2);
    super::flags::lemma_cc_icmp(s1, lir::ICmp::Eq, 32, c as int, i as int);
    assert(cset_cond(lir::ICmp::Eq) == 1);
    assert(isa::condition_holds(s2, 0) == (c as nat == i)) by {
        assert(s2 == isa::State {
            pc: (s1.pc + 4) as u64,
            ..isa::set_nzcv(s1, super::flags::cmp_nzcv(32, c as int, i as int))
        });
    }
    // b.eq
    assert(e[2] == bcond_i(0, rel));
    assert(0 <= s2.pc as int + rel < 0x1_0000_0000_0000_0000);
    lemma_step_bcond(s2, 0, rel);
    let s3 = isa::step(s2, e[2]).unwrap();
    lemma_reach_step(whole, b0, s2, (1 + 3 * i) as int + 2, s3);
    lemma_reaches_trans(whole, b0, s, s2, s3);
}

/// **The chain, run from entry `i`**, with `x0` holding `c >= i`: it reaches
/// the label the `br_table` selects, with memory and everything but `x1` as
/// they were.
#[verifier::rlimit(400)]
pub proof fn lemma_brt_chain(
    ls: Seq<usize>,
    d: usize,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    i: nat,
    c: u32,
    s: isa::State,
    b0: int,
)
    requires
        i <= ls.len(),
        ls.len() <= max_targets(),
        c as nat >= i,
        brt_labels_ok(ls, d, offs, b0),
        isa::wf(s),
        s.pc as int == b0 + 4 + 12 * i,
        s.r[0] == c as u64,
    ensures
        ({
            let whole = brt_code(ls, d, nl, h, offs);
            exists|me: isa::State|
                #![trigger reaches(whole, b0, s, me)]
                reaches(whole, b0, s, me) && isa::wf(me) && brt_fr(s, me) && me.pc as int == b0 + (
                if (c as nat) < ls.len() {
                    offs[ls[c as int] as int]
                } else {
                    offs[d as int]
                })
        }),
    decreases ls.len() - i,
{
    let whole = brt_code(ls, d, nl, h, offs);
    let n = ls.len();
    if i == n {
        lemma_brt_last(ls, d, nl, h, offs, s, b0);
        assert(c as nat >= n);
    } else {
        lemma_brt_entry(ls, d, nl, h, offs, i, c, s, b0);
        let s3 = choose|s3: isa::State|
            reaches(whole, b0, s, s3) && isa::wf(s3) && brt_fr(s, s3) && s3.pc as int == (if c as nat
                == i {
                b0 + offs[ls[i as int] as int]
            } else {
                b0 + 4 + 12 * (i + 1)
            });
        if c as nat == i {
            assert((c as nat) < n);
        } else {
            assert(s3.r[0] == c as u64);
            lemma_brt_chain(ls, d, nl, h, offs, i + 1, c, s3, b0);
            let me = choose|me: isa::State|
                reaches(whole, b0, s3, me) && isa::wf(me) && brt_fr(s3, me) && me.pc as int == b0 + (
                if (c as nat) < n {
                    offs[ls[c as int] as int]
                } else {
                    offs[d as int]
                });
            lemma_reaches_trans(whole, b0, s, s3, me);
            lemma_brt_fr_trans(s, s3, me);
        }
    }
}

/// **`br_table ls d`.**
#[verifier::rlimit(1500)]
pub proof fn lemma_brt_cf(ls: Vec<usize>, d: usize, nl: nat, h: nat, offs: Seq<int>)
    requires
        1 <= h,
        nl + h <= max_slots(),
        ls@.len() <= max_targets(),
        d < offs.len(),
        forall|q: int| 0 <= q < ls@.len() ==> #[trigger] ls@[q] < offs.len(),
        labels_fit(offs, 8 + 12 * ls@.len()),
    ensures
        cf_refines(Node::BrTable(ls, d)@, nl, h, offs, brt_code(ls@, d, nl, h, offs)),
{
    super::memlemmas::lemma_p2_consts();
    let lsq = ls@;
    let code = brt_code(lsq, d, nl, h, offs);
    lemma_brt_shape(lsq, d, nl, h, offs);
    let j = (nl + h - 1) as nat;
    let i0 = load_slot(x0(), j);
    assert(code[0] == i0);
    assert forall|
        lay: lir::Layout,
        base: Seq<lir::Val>,
        a: lir::St,
        m: isa::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, code, m, lir::eval(lay, Node::BrTable(ls, d)@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && cf_canon(
            m.pc as int,
            offs,
            code,
        ) implies cf_post(
        lay,
        base,
        nl,
        offs,
        code,
        m,
        lir::eval(lay, Node::BrTable(ls, d)@, a, fuel),
    ) by {
        let n0 = a.stack.len();
        if fuel > 0 && n0 >= 1 {
            match a.stack[(n0 - 1) as int] {
                lir::Val::I32(c) => {
                    lemma_rel_base_unfold(lay, base, a, m, nl);
                    let ac = a.with_stack(base + a.stack);
                    assert(ac.stack[(h - 1) as int] == lir::Val::I32(c));
                    assert(slot_val(ac, nl, j) == lir::Val::I32(c));
                    assert(j < nl + ac.stack.len());
                    let b0 = m.pc as int;
                    assert(code_len(code) == 8 + 12 * lsq.len());
                    assert(brt_labels_ok(lsq, d, offs, b0)) by {
                        assert forall|l: int| 0 <= l < offs.len() implies 0 <= b0 + #[trigger] offs[l]
                            && b0 + offs[l] < 0x1_0000_0000_0000_0000 by {}
                    }
                    super::rel::lemma_load_rel(lay, ac, m, 0, j, nl);
                    let m1 = isa::step(m, i0).unwrap();
                    assert(m1.r[0] == c as u64);
                    lemma_reach_step(code, b0, m, 0, m1);
                    assert(m1.pc as int == b0 + 4);
                    lemma_brt_chain(lsq, d, nl, h, offs, 0, c, m1, b0);
                    let me = choose|q: isa::State|
                        reaches(code, b0, m1, q) && isa::wf(q) && brt_fr(m1, q) && q.pc as int == b0
                            + (if (c as nat) < lsq.len() {
                            offs[lsq[c as int] as int]
                        } else {
                            offs[d as int]
                        });
                    lemma_reaches_trans(code, b0, m, m1, me);
                    let l: nat = if (c as nat) < lsq.len() {
                        lsq[c as int] as nat
                    } else {
                        d as nat
                    };
                    let mapped = lsq.map_values(|x: usize| x as nat);
                    assert(mapped.len() == lsq.len());
                    assert(lir::eval(lay, Node::BrTable(ls, d)@, a, fuel) == lir::Outcome::Branch(
                        l,
                        a.with_stack(lir::below(a.stack, 1)),
                    )) by {
                        if (c as nat) < lsq.len() {
                            assert(mapped[c as int] == lsq[c as int] as nat);
                        }
                    }
                    assert(l < offs.len());
                    assert(me.pc as int == b0 + offs[l as int]);
                    assert(me.r[28] == m1.r[28] && me.r[30] == m1.r[30] && m1.r[28] == m.r[28]);
                    assert(me.vreg.len() == 32);
                    super::rel::lemma_rel_regs(lay, ac, m1, me, nl);
                    lemma_preserved_same(lay, m, me);
                    lemma_table_pres(lay, m, me);
                    let s = a.with_stack(lir::below(a.stack, 1));
                    assert((base + a.stack).take((base + lir::below(a.stack, 1)).len() as int)
                        =~= base + lir::below(a.stack, 1));
                    lemma_rel_prefix(
                        lay,
                        a,
                        base + a.stack,
                        base + lir::below(a.stack, 1),
                        me,
                        nl,
                    );
                    assert(s.with_stack(base + s.stack) == a.with_stack(
                        base + lir::below(a.stack, 1),
                    ));
                    reveal(rel_base);
                    assert(rel_base(lay, base, s, me, nl));
                    assert(base + Seq::<lir::Val>::empty() =~= base);
                    assert(rel_ext(lay, base, s, me, nl));
                },
                _ => {},
            }
        }
    }
}

} // verus!
