//! **`br_table` refines its LIR instruction** ([`brt_cf`]): the code is
//! [`crate::cftemplates::brt_code`], `mov rax, [index]`, a compare and `je`
//! per target, and a `jmp` to the default (the subset has no indirect
//! branch). The proof runs the chain by induction on the entry.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfalg::*;
#[cfg(verus_only)]
use crate::cfcheck::*;
#[cfg(verus_only)]
use crate::cfcontract::*;
#[cfg(verus_only)]
use crate::cfleaf::*;
#[cfg(verus_only)]
use crate::cflens::*;
#[cfg(verus_only)]
use crate::cfmemlens::*;
#[cfg(verus_only)]
use crate::cfproofs::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[cfg(verus_only)]
use crate::cfsteps::*;
#[cfg(verus_only)]
use crate::cftemplates::*;
#[cfg(verus_only)]
use crate::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The load of the index is 8 bytes, whatever the slot.
pub proof fn lemma_brt_p0(nl: nat, h: nat)
    ensures
        brt_p0(nl, h) == 8,
{
    lemma_mem_instr_lens((nl + h - 1) as nat, 0);
    super::runseq::lemma_len1(load_slot(rax(), (nl + h - 1) as nat));
}

/// The chain from entry `k` is `13` bytes per entry left.
pub proof fn lemma_entries_len(ls: Seq<usize>, offs: Seq<int>, p0: int, k: nat)
    ensures
        code_len(brt_entries(ls, offs, p0, k)) == if k >= ls.len() {
            0nat
        } else {
            (13 * (ls.len() - k)) as nat
        },
    decreases ls.len() - k,
{
    if k < ls.len() {
        let e = brt_entry(k, brt_rel(offs, ls[k as int], p0 + (k + 1) * brt_e()));
        lemma_brt_entry_len(k, brt_rel(offs, ls[k as int], p0 + (k + 1) * brt_e()));
        lemma_entries_len(ls, offs, p0, k + 1);
        super::runseq::lemma_code_len_append(e, brt_entries(ls, offs, p0, k + 1));
    } else {
        assert(brt_entries(ls, offs, p0, k) =~= Seq::<x64::Instr>::empty());
    }
}

/// The three instructions of an entry are at offsets 0, 5 and 7.
pub proof fn lemma_entry_fetch(i: nat, rel: int)
    ensures
        fetch(brt_entry(i, rel), 0) == Some(
            x64::Instr::MovImm32 { dst: rdx(), imm_u32: i as u32 },
        ),
        fetch(brt_entry(i, rel), 5) == Some(
            x64::Instr::AluRR {
                alu: x64::AluOp::Cmp,
                sz: x64::Size::W32,
                dst: rax(),
                src: rdx(),
            },
        ),
        fetch(brt_entry(i, rel), 7) == Some(jcc_i(4, rel)),
        x64::instr_len(x64::Instr::MovImm32 { dst: rdx(), imm_u32: i as u32 }) == 5,
        x64::instr_len(
            x64::Instr::AluRR { alu: x64::AluOp::Cmp, sz: x64::Size::W32, dst: rax(), src: rdx() },
        ) == 2,
{
    lemma_jcc_len(4, rel);
    lemma_le_bytes_len(i as u32 as int, 4);
    let a = x64::Instr::MovImm32 { dst: rdx(), imm_u32: i as u32 };
    let b = x64::Instr::AluRR { alu: x64::AluOp::Cmp, sz: x64::Size::W32, dst: rax(), src: rdx() };
    let c = jcc_i(4, rel);
    assert(x64::instr_len(a) == 5);
    assert(x64::instr_len(b) == 2);
    let e = brt_entry(i, rel);
    assert(e.skip(1) =~= seq![b, c]);
    assert(seq![b, c].skip(1) =~= seq![c]);
    reveal_with_fuel(fetch, 4);
}

/// Entry `i`'s instructions are at `13 (i - k) + o` in the chain from `k`.
pub proof fn lemma_entries_fetch(ls: Seq<usize>, offs: Seq<int>, p0: int, k: nat, i: nat)
    requires
        k <= i < ls.len(),
    ensures
        ({
            let rel = brt_rel(offs, ls[i as int], p0 + (i + 1) * brt_e());
            let ch = brt_entries(ls, offs, p0, k);
            &&& fetch(ch, (13 * (i - k) + 0) as int) == fetch(brt_entry(i, rel), 0)
            &&& fetch(ch, (13 * (i - k) + 5) as int) == fetch(brt_entry(i, rel), 5)
            &&& fetch(ch, (13 * (i - k) + 7) as int) == fetch(brt_entry(i, rel), 7)
        }),
    decreases i - k,
{
    let e = brt_entry(k, brt_rel(offs, ls[k as int], p0 + (k + 1) * brt_e()));
    let rest = brt_entries(ls, offs, p0, k + 1);
    lemma_brt_entry_len(k, brt_rel(offs, ls[k as int], p0 + (k + 1) * brt_e()));
    if k == i {
        lemma_entry_fetch(i, brt_rel(offs, ls[i as int], p0 + (i + 1) * brt_e()));
        super::cfsteps::lemma_fetch_append_l(e, rest, 0);
        super::cfsteps::lemma_fetch_append_l(e, rest, 5);
        super::cfsteps::lemma_fetch_append_l(e, rest, 7);
    } else {
        lemma_entries_fetch(ls, offs, p0, k + 1, i);
        super::cfsteps::lemma_fetch_append_r(e, rest, (13 * (i - k) + 0) as int);
        super::cfsteps::lemma_fetch_append_r(e, rest, (13 * (i - k) + 5) as int);
        super::cfsteps::lemma_fetch_append_r(e, rest, (13 * (i - k) + 7) as int);
    }
}

/// **The positions in the whole code**: entry `i`'s instructions at `8 + 13 i`
/// and `+ 5`, `+ 7`; the final `jmp` at `8 + 13 len`.
pub proof fn lemma_brt_fetch(ls: Seq<usize>, d: usize, nl: nat, h: nat, offs: Seq<int>, i: nat)
    requires
        i < ls.len(),
    ensures
        ({
            let whole = brt_code(ls, d, nl, h, offs);
            let rel = brt_rel(offs, ls[i as int], (8 + (i + 1) * 13) as int);
            &&& fetch(whole, (8 + 13 * i + 0) as int) == fetch(brt_entry(i, rel), 0)
            &&& fetch(whole, (8 + 13 * i + 5) as int) == fetch(brt_entry(i, rel), 5)
            &&& fetch(whole, (8 + 13 * i + 7) as int) == fetch(brt_entry(i, rel), 7)
        }),
{
    lemma_brt_p0(nl, h);
    lemma_brt_entry_len(0, 0);
    let p0 = brt_p0(nl, h);
    let a = seq![load_slot(rax(), (nl + h - 1) as nat)];
    let ch = brt_entries(ls, offs, p0, 0);
    let jm = seq![jmp_i(brt_rel(offs, d, p0 + ls.len() * brt_e() + 5))];
    let whole = brt_code(ls, d, nl, h, offs);
    assert(whole =~= a + (ch + jm));
    lemma_entries_fetch(ls, offs, p0, 0, i);
    let rel = brt_rel(offs, ls[i as int], p0 + (i + 1) * brt_e());
    super::cfsteps::lemma_fetch_append_r(a, ch + jm, (8 + 13 * i + 0) as int);
    super::cfsteps::lemma_fetch_append_r(a, ch + jm, (8 + 13 * i + 5) as int);
    super::cfsteps::lemma_fetch_append_r(a, ch + jm, (8 + 13 * i + 7) as int);
    assert(fetch(brt_entry(i, rel), 0) is Some) by {
        lemma_entry_fetch(i, rel);
    }
    assert(fetch(brt_entry(i, rel), 5) is Some) by {
        lemma_entry_fetch(i, rel);
    }
    assert(fetch(brt_entry(i, rel), 7) is Some) by {
        lemma_entry_fetch(i, rel);
    }
    super::cfsteps::lemma_fetch_append_l(ch, jm, (13 * i + 0) as int);
    super::cfsteps::lemma_fetch_append_l(ch, jm, (13 * i + 5) as int);
    super::cfsteps::lemma_fetch_append_l(ch, jm, (13 * i + 7) as int);
}

/// The final `jmp` is at `8 + 13 len`.
pub proof fn lemma_brt_fetch_jmp(ls: Seq<usize>, d: usize, nl: nat, h: nat, offs: Seq<int>)
    ensures
        fetch(brt_code(ls, d, nl, h, offs), (8 + 13 * ls.len()) as int) == Some(
            jmp_i(brt_rel(offs, d, (8 + ls.len() * 13 + 5) as int)),
        ),
        code_len(brt_code(ls, d, nl, h, offs)) == 13 + 13 * ls.len(),
{
    lemma_brt_p0(nl, h);
    lemma_brt_entry_len(0, 0);
    let p0 = brt_p0(nl, h);
    let a = seq![load_slot(rax(), (nl + h - 1) as nat)];
    let ch = brt_entries(ls, offs, p0, 0);
    let jm = seq![jmp_i(brt_rel(offs, d, p0 + ls.len() * brt_e() + 5))];
    let whole = brt_code(ls, d, nl, h, offs);
    assert(whole =~= a + (ch + jm));
    lemma_entries_len(ls, offs, p0, 0);
    super::cfsteps::lemma_fetch_append_r(a, ch + jm, (8 + 13 * ls.len()) as int);
    super::cfsteps::lemma_fetch_append_r(ch, jm, (13 * ls.len()) as int);
    super::runseq::lemma_code_len_append(a, ch + jm);
    super::runseq::lemma_code_len_append(ch, jm);
    super::runseq::lemma_code_len_one(jmp_i(brt_rel(offs, d, p0 + ls.len() * brt_e() + 5)));
    lemma_jmp_len(brt_rel(offs, d, p0 + ls.len() * brt_e() + 5));
    super::runseq::lemma_len1(load_slot(rax(), (nl + h - 1) as nat));
    assert(fetch(jm, 0) == Some(jm[0]));
}

/// What the chain needs of the labels: in scope, within a 32-bit
/// displacement of every place in the code, canonical.
pub open spec fn brt_labels_ok(
    ls: Seq<usize>,
    d: usize,
    offs: Seq<int>,
    rip0: int,
) -> bool {
    d < offs.len() && (forall|q: int| 0 <= q < ls.len() ==> #[trigger] ls[q] < offs.len())
        && labels_fit(offs, 13 + 13 * ls.len()) && (forall|l: int|
        0 <= l < offs.len() ==> x64::canonical(rip0 + #[trigger] offs[l]))
}

/// **The final `jmp`** of the chain, to the default label.
#[verifier::rlimit(300)]
pub proof fn lemma_brt_last(
    cu: spec_fn(nat) -> nat,
    ls: Seq<usize>,
    d: usize,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    s: x64::State,
    rip0: int,
)
    requires
        ls.len() <= max_targets(),
        brt_labels_ok(ls, d, offs, rip0),
        x64::wf(s),
        s.rip == rip0 + 8 + 13 * ls.len(),
        x64::canonical(rip0 + 13 + 13 * ls.len()),
        x64::canonical(rip0),
    ensures
        ({
            let whole = brt_code(ls, d, nl, h, offs);
            exists|me: x64::State|
                #![trigger reaches(cu, whole, rip0, s, me)]
                reaches(cu, whole, rip0, s, me) && x64::wf(me) && me.mem == s.mem && me.rgf.len()
                    == 16 && me.rgf[15] == s.rgf[15] && me.rgf[4] == s.rgf[4] && me.rip == rip0
                    + offs[d as int]
        }),
{
    let whole = brt_code(ls, d, nl, h, offs);
    let n = ls.len();
    assert(reaches(cu, whole, rip0, s, s)) by {
        assert(steps(cu, whole, rip0, s, 0) == Some(s));
    }
    let end_all = rip0 + 13 + 13 * n;
    lemma_brt_fetch_jmp(ls, d, nl, h, offs);
    let rel = brt_rel(offs, d, (8 + n * 13 + 5) as int);
    assert(rel == offs[d as int] - (8 + n * 13 + 5));
    assert(-0x8000_0000 <= rel < 0x8000_0000);
    assert((rel as i32) as int == rel);
    super::runseq::lemma_canonical_between(rip0, s.rip + 5, end_all);
    super::runseq::lemma_canonical_between(rip0, s.rip, end_all);
    assert(s.rip + 5 + rel == rip0 + offs[d as int]);
    lemma_step_jmp(cu, s, rel);
    let me = x64::step(cu, s, jmp_i(rel)).unwrap();
    assert(me == x64::State { rip: rip0 + offs[d as int], ..s });
    assert(x64::canonical(rip0 + offs[d as int]));
    lemma_wf_like2(s, me);
    lemma_reach_step(cu, whole, rip0, s, s, jmp_i(rel), me);
}

/// **One entry of the chain**: `mov edx, i; cmp eax, edx; je`. The run
/// reaches the label of target `i` when `eax == i`, else the next entry.
#[verifier::rlimit(800)]
pub proof fn lemma_brt_entry(
    cu: spec_fn(nat) -> nat,
    ls: Seq<usize>,
    d: usize,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    i: nat,
    c: u32,
    s: x64::State,
    rip0: int,
)
    requires
        i < ls.len(),
        ls.len() <= max_targets(),
        c as nat >= i,
        brt_labels_ok(ls, d, offs, rip0),
        x64::wf(s),
        s.rip == rip0 + 8 + 13 * i,
        s.rgf[0] == c as u64,
        x64::canonical(rip0 + 13 + 13 * ls.len()),
        x64::canonical(rip0),
    ensures
        ({
            let whole = brt_code(ls, d, nl, h, offs);
            exists|s3: x64::State|
                #![trigger reaches(cu, whole, rip0, s, s3)]
                reaches(cu, whole, rip0, s, s3) && x64::wf(s3) && s3.mem == s.mem && s3.rgf.len()
                    == 16 && s3.rgf[15] == s.rgf[15] && s3.rgf[4] == s.rgf[4] && s3.rgf[0]
                    == s.rgf[0] && s3.rip == (if c as nat == i {
                    rip0 + offs[ls[i as int] as int]
                } else {
                    rip0 + 8 + 13 * (i + 1)
                })
        }),
{
    super::memlemmas::lemma_p2_consts();
    let whole = brt_code(ls, d, nl, h, offs);
    let n = ls.len();
    lemma_brt_entry_len(0, 0);
    assert(reaches(cu, whole, rip0, s, s)) by {
        assert(steps(cu, whole, rip0, s, 0) == Some(s));
    }
    let end_all = rip0 + 13 + 13 * n;
    lemma_brt_fetch(ls, d, nl, h, offs, i);
    let li = ls[i as int];
    assert(li < offs.len());
    let rel = brt_rel(offs, li, (8 + (i + 1) * 13) as int);
    assert(rel == offs[li as int] - ((8 + (i + 1) * 13) as int));
    assert(-0x8000_0000 <= rel < 0x8000_0000);
    assert((rel as i32) as int == rel);
    lemma_entry_fetch(i, rel);
    let e0 = x64::Instr::MovImm32 { dst: rdx(), imm_u32: i as u32 };
    let e1 = x64::Instr::AluRR {
        alu: x64::AluOp::Cmp,
        sz: x64::Size::W32,
        dst: rax(),
        src: rdx(),
    };
    let e2 = jcc_i(4, rel);
    assert(x64::instr_len(e0) == 5 && x64::instr_len(e1) == 2);
    lemma_jcc_len(4, rel);
    super::runseq::lemma_canonical_between(rip0, s.rip + 5, end_all);
    super::runseq::lemma_canonical_between(rip0, s.rip + 7, end_all);
    super::runseq::lemma_canonical_between(rip0, s.rip + 13, end_all);
    assert(i < 0x10000);
    super::steps::lemma_step_imm(cu, s, e0);
    let s1 = x64::step(cu, s, e0).unwrap();
    assert(s1.rgf == s.rgf.update(2, i as u64));
    assert(s1.mem == s.mem && s1.xmm == s.xmm && s1.rip == s.rip + 5);
    lemma_wf_like2(s, s1);
    lemma_reach_step(cu, whole, rip0, s, s, e0, s1);
    super::flags::lemma_step_cmp(cu, s1, x64::Size::W32, 0, 2);
    let s2 = x64::step(cu, s1, e1).unwrap();
    assert(s2.rgf == s1.rgf && s2.mem == s1.mem && s2.xmm == s1.xmm);
    assert(s2.rip == s1.rip + 2);
    lemma_wf_like2(s, s2);
    lemma_reach_step(cu, whole, rip0, s, s1, e1, s2);
    assert(x64::rgfi_size(s1, x64::Size::W32, 0) == c as int) by {
        assert(x64::loghead(32, c as int) == c as int);
    }
    assert(x64::rgfi_size(s1, x64::Size::W32, 2) == i as int) by {
        assert(x64::loghead(32, i as int) == i as int);
    }
    super::flags::lemma_cc_icmp(s2, lir::ICmp::Eq, 32, c as int, i as int);
    assert(super::templates::cc_of(lir::ICmp::Eq) == 4);
    assert(x64::canonical(rip0 + offs[li as int]));
    assert(x64::canonical(s2.rip + 6 + rel));
    lemma_step_jcc(cu, s2, 4, rel);
    let s3 = x64::step(cu, s2, e2).unwrap();
    assert(x64::canonical(s3.rip));
    lemma_wf_like2(s, s3);
    lemma_reach_step(cu, whole, rip0, s, s2, e2, s3);
    assert(s3.rgf == s1.rgf);
}

/// **The chain, run from entry `i`**, with `eax` holding `c >= i`: it reaches
/// the label the `br_table` selects, with memory and the context register
/// and stack pointer as they were.
#[verifier::rlimit(400)]
pub proof fn lemma_brt_chain(
    cu: spec_fn(nat) -> nat,
    ls: Seq<usize>,
    d: usize,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    i: nat,
    c: u32,
    s: x64::State,
    rip0: int,
)
    requires
        i <= ls.len(),
        ls.len() <= max_targets(),
        c as nat >= i,
        brt_labels_ok(ls, d, offs, rip0),
        x64::wf(s),
        s.rip == rip0 + 8 + 13 * i,
        s.rgf[0] == c as u64,
        x64::canonical(rip0 + 13 + 13 * ls.len()),
        x64::canonical(rip0),
    ensures
        ({
            let whole = brt_code(ls, d, nl, h, offs);
            exists|me: x64::State|
                #![trigger reaches(cu, whole, rip0, s, me)]
                reaches(cu, whole, rip0, s, me) && x64::wf(me) && me.mem == s.mem && me.rgf.len()
                    == 16 && me.rgf[15] == s.rgf[15] && me.rgf[4] == s.rgf[4] && me.rip == rip0 + (
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
        lemma_brt_last(cu, ls, d, nl, h, offs, s, rip0);
        assert(c as nat >= n);
    } else {
        lemma_brt_entry(cu, ls, d, nl, h, offs, i, c, s, rip0);
        let s3 = choose|s3: x64::State|
            reaches(cu, whole, rip0, s, s3) && x64::wf(s3) && s3.mem == s.mem && s3.rgf.len()
                == 16 && s3.rgf[15] == s.rgf[15] && s3.rgf[4] == s.rgf[4] && s3.rgf[0]
                == s.rgf[0] && s3.rip == (if c as nat == i {
                rip0 + offs[ls[i as int] as int]
            } else {
                rip0 + 8 + 13 * (i + 1)
            });
        if c as nat == i {
            assert((c as nat) < n);
        } else {
            lemma_brt_chain(cu, ls, d, nl, h, offs, i + 1, c, s3, rip0);
            let me = choose|me: x64::State|
                reaches(cu, whole, rip0, s3, me) && x64::wf(me) && me.mem == s3.mem
                    && me.rgf.len() == 16 && me.rgf[15] == s3.rgf[15] && me.rgf[4] == s3.rgf[4]
                    && me.rip == rip0 + (if (c as nat) < n {
                    offs[ls[c as int] as int]
                } else {
                    offs[d as int]
                });
            lemma_reaches_trans(cu, whole, rip0, s, s3, me);
        }
    }
}

/// A state with the memory and 16 + 16 registers of a well-formed one, and a
/// canonical `rip`, is well formed (the second form, from a state `s`).
pub proof fn lemma_wf_like2(s: x64::State, t: x64::State)
    requires
        x64::wf(s),
        t.mem == s.mem,
        t.rgf.len() == 16,
        t.xmm.len() == 16,
        x64::canonical(t.rip),
    ensures
        x64::wf(t),
{
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
        labels_fit(offs, 13 + 13 * ls@.len()),
    ensures
        cf_refines(
            Node::BrTable(ls, d)@,
            nl,
            h,
            offs,
            brt_code(ls@, d, nl, h, offs),
        ),
{
    let lsq = ls@;
    let code = brt_code(lsq, d, nl, h, offs);
    lemma_brt_fetch_jmp(lsq, d, nl, h, offs);
    lemma_brt_p0(nl, h);
    let j = (nl + h - 1) as nat;
    let i0 = load_slot(rax(), j);
    assert(code[0] == i0) by {
        assert(code =~= seq![i0] + (brt_entries(lsq, offs, brt_p0(nl, h), 0) + seq![jmp_i(
            brt_rel(offs, d, brt_p0(nl, h) + lsq.len() * brt_e() + 5),
        )]));
    }
    assert forall|
        lay: lir::Layout,
        cu: spec_fn(nat) -> nat,
        base: Seq<lir::Val>,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, code, cu, m, lir::eval(lay, Node::BrTable(ls, d)@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && stack_ok_r(lay, m)
            && cf_canon(m.rip, offs, code) implies cf_post(
        lay,
        base,
        nl,
        offs,
        code,
        cu,
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
                    super::steps::lemma_abi_consts();
                    let big = code_len(code);
                    assert(big == 13 + 13 * lsq.len());
                    assert(x64::canonical(m.rip + big));
                    assert(brt_labels_ok(lsq, d, offs, m.rip)) by {
                        assert forall|l: int| 0 <= l < offs.len() implies x64::canonical(
                            m.rip + #[trigger] offs[l],
                        ) by {}
                    }
                    super::runseq::lemma_canonical_between(m.rip, m.rip + 8, m.rip + big);
                    super::rel::lemma_load_rel(cu, lay, ac, m, 0, j, nl);
                    let m1 = x64::step(cu, m, i0).unwrap();
                    lemma_mem_instr_lens(j, 0);
                    assert(m1.rgf[0] == c as u64);
                    assert(fetch(code, 0) == Some(i0));
                    assert(reaches(cu, code, m.rip, m, m)) by {
                        assert(steps(cu, code, m.rip, m, 0) == Some(m));
                    }
                    lemma_reach_step(cu, code, m.rip, m, m, i0, m1);
                    assert(m1.rip == m.rip + 8);
                    lemma_brt_chain(cu, lsq, d, nl, h, offs, 0, c, m1, m.rip);
                    let me = choose|q: x64::State|
                        reaches(cu, code, m.rip, m1, q) && x64::wf(q) && q.mem == m1.mem
                            && q.rgf.len() == 16 && q.rgf[15] == m1.rgf[15] && q.rgf[4]
                            == m1.rgf[4] && q.rip == m.rip + (if (c as nat) < lsq.len() {
                            offs[lsq[c as int] as int]
                        } else {
                            offs[d as int]
                        });
                    lemma_reaches_trans(cu, code, m.rip, m, m1, me);
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
                    assert(me.rip == m.rip + offs[l as int]);
                    assert(me.xmm.len() == 16);
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
