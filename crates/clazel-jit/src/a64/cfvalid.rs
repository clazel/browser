//! Every instruction the control-flow templates use is in the A64 subset
//! ([`isa::valid_instr`]): the emitter's blob is decoded by the validator only
//! if it is. A branch is in the subset only if its displacement fits (26 bits
//! for `b`, 19 for the conditional ones, in words), which is why this file
//! has the leaf lemmas and [`crate::a64::cfproofs`] carries the size invariant
//! that discharges them. The A64 counterpart of [`crate::cfvalid`].

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::cffit::*;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cftemplates::*;
#[cfg(verus_only)]
use super::contract::*;
#[cfg(verus_only)]
use super::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Valid code followed by valid code is valid.
pub proof fn lemma_valid_cat(a: Seq<isa::Instr>, b: Seq<isa::Instr>)
    requires
        all_valid_instrs(a),
        all_valid_instrs(b),
    ensures
        all_valid_instrs(a + b),
{
    super::tlemmas::lemma_valid_concat(a, b);
}

/// The two powers of two the branch fields need.
pub proof fn lemma_p2_fields()
    ensures
        isa::p2(18) == 0x4_0000,
        isa::p2(25) == 0x200_0000,
{
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
}

/// `b` to a displacement that fits is valid.
pub proof fn lemma_b_valid(rel: int)
    requires
        -0x800_0000 <= rel < 0x800_0000,
    ensures
        isa::valid_instr(b_i(rel)),
{
    lemma_p2_fields();
    assert(((rel / 4) as i32) as int == rel / 4);
}

/// The condition test is valid code, when its slot is in the frame and the
/// branch reaches.
pub proof fn lemma_cond_pre_valid(nl: nat, h: nat, iszero: bool, rel: int)
    requires
        1 <= h,
        nl + h <= max_slots(),
        -0x10_0000 <= rel < 0x10_0000,
    ensures
        all_valid_instrs(cond_pre(nl, h, iszero, rel)),
{
    lemma_p2_fields();
    super::tlemmas::lemma_ls_valid(0, (nl + h - 1) as nat);
    assert(((rel / 4) as i32) as int == rel / 4);
    let c = cond_pre(nl, h, iszero, rel);
    assert forall|k: int| 0 <= k < c.len() implies isa::valid_instr(#[trigger] c[k]) by {
        assert(k == 0 || k == 1);
    }
}

/// The bounds check for any region, size and small exit displacements is
/// valid code.
pub proof fn lemma_check_valid(k: nat, n: nat, r1: int, r2: int)
    requires
        k < 16,
        1 <= n <= 8,
        0 <= r1 < 0x100,
        0 <= r2 < 0x100,
    ensures
        all_valid_instrs(clazel_codecheck::a64::spec::check_seq(mem_chk(k, n, r1, r2))),
{
    lemma_p2_fields();
    super::steps::lemma_abi_consts();
    let c = mem_chk(k, n, r1, r2);
    let s = clazel_codecheck::a64::spec::check_seq(c);
    assert forall|j: int| 0 <= j < s.len() implies isa::valid_instr(#[trigger] s[j]) by {
        assert(j == 0 || j == 1 || j == 2 || j == 3 || j == 4 || j == 5 || j == 6);
        assert(s[j] == clazel_codecheck::a64::spec::check_instr(j, c));
        assert(abi::bound_off(k as int) / 8 == 2 * k + 1);
    }
}

/// **A memory instruction's code is valid.**
pub proof fn lemma_mem_valid(m: MemOp, nl: nat, h: nat)
    requires
        nl + h <= max_slots(),
        match m {
            MemOp::BoundsCheck { region, size, code } => 1 <= h && region < 16 && 1 <= size <= 8
                && code < 0x1_0000,
            MemOp::Load { region, ty } => 1 <= h && region < 16,
            MemOp::Store { region, ty } => 2 <= h && region < 16,
        },
    ensures
        all_valid_instrs(mem_code(m, nl, h)),
{
    lemma_p2_fields();
    super::steps::lemma_abi_consts();
    let pre = mem_pre(m, nl, h);
    let tail = mem_tail(m, nl, h);
    let stub = exit_seq(mem_exit_code(m));
    let bb = seq![b_i(code_len(stub) as int + 4)];
    super::tlemmas::lemma_exit_valid(mem_exit_code(m));
    lemma_b_valid(16);
    assert(code_len(stub) == 12);
    assert(all_valid_instrs(bb)) by {
        assert forall|j: int| 0 <= j < bb.len() implies isa::valid_instr(#[trigger] bb[j]) by {
            assert(j == 0);
        }
    }
    assert(mem_r1(m, nl, h) == 6 + tail.len() && mem_r2(m, nl, h) == 4 + tail.len());
    lemma_check_valid(
        mem_region(m),
        mem_n(m),
        mem_r1(m, nl, h),
        mem_r2(m, nl, h),
    );
    let k = mem_region(m);
    assert(k < 16);
    assert(all_valid_instrs(pre)) by {
        assert forall|j: int| 0 <= j < pre.len() implies isa::valid_instr(#[trigger] pre[j]) by {
            match m {
                MemOp::BoundsCheck { .. } => {
                    super::tlemmas::lemma_ls_valid(1, (nl + h - 1) as nat);
                },
                MemOp::Load { .. } => {
                    super::tlemmas::lemma_ls_valid(1, (nl + h - 1) as nat);
                },
                MemOp::Store { .. } => {
                    super::tlemmas::lemma_ls_valid(4, (nl + h - 1) as nat);
                    super::tlemmas::lemma_ls_valid(1, (nl + h - 2) as nat);
                },
            }
        }
    }
    assert(all_valid_instrs(tail)) by {
        assert forall|j: int| 0 <= j < tail.len() implies isa::valid_instr(#[trigger] tail[j]) by {
            match m {
                MemOp::BoundsCheck { .. } => {},
                MemOp::Load { .. } => {
                    super::tlemmas::lemma_ls_valid(0, (nl + h - 1) as nat);
                },
                MemOp::Store { .. } => {},
            }
        }
    }
    lemma_valid_cat(pre, mem_check(m, nl, h));
    lemma_valid_cat(pre + mem_check(m, nl, h), tail);
    lemma_valid_cat(pre + mem_check(m, nl, h) + tail, bb);
    lemma_valid_cat(pre + mem_check(m, nl, h) + tail + bb, stub);
}

/// **`br_table`'s code is valid**, when its labels are in reach.
pub proof fn lemma_brt_valid(ls: Seq<usize>, d: usize, nl: nat, h: nat, offs: Seq<int>)
    requires
        1 <= h,
        nl + h <= max_slots(),
        ls.len() <= max_targets(),
        d < offs.len(),
        forall|q: int| 0 <= q < ls.len() ==> #[trigger] ls[q] < offs.len(),
        labels_fit(offs, 8 + 12 * ls.len()),
    ensures
        all_valid_instrs(brt_code(ls, d, nl, h, offs)),
{
    lemma_p2_fields();
    super::cfbrt::lemma_brt_shape(ls, d, nl, h, offs);
    super::tlemmas::lemma_ls_valid(0, (nl + h - 1) as nat);
    let w = brt_code(ls, d, nl, h, offs);
    let n = ls.len();
    assert forall|q: int| 0 <= q < w.len() implies isa::valid_instr(#[trigger] w[q]) by {
        if q == 0 {
        } else if q == 1 + 3 * n {
            let rel = brt_rel(offs, d, (4 + n * 12) as int);
            assert(-0x800_0000 <= rel < 0x800_0000);
            lemma_b_valid(rel);
        } else {
            let i = ((q - 1) / 3) as nat;
            let t = (q - 1) % 3;
            assert(i < n);
            assert(q == 1 + 3 * i + t);
            let rel = brt_rel(offs, ls[i as int], (4 + i * 12 + 8) as int);
            assert(-0x10_0000 <= rel < 0x10_0000);
            assert(((rel / 4) as i32) as int == rel / 4);
            assert(w[(1 + 3 * i) as int + t] == brt_entry(i, rel)[t]);
            assert(i < 0x1_0000);
            assert(t == 0 || t == 1 || t == 2);
        }
    }
}

} // verus!
