//! The code of the memory instructions and of `br_table` is in the x86-64
//! subset ([`x64::valid_instr`]) and is, for a memory instruction, accepted
//! by the validator's unit rules in its shape.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[cfg(verus_only)]
use crate::cftemplates::*;
#[cfg(verus_only)]
use crate::cfvalid::*;
#[cfg(verus_only)]
use crate::contract::*;
#[cfg(verus_only)]
use crate::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every instruction of the bounds-check sequence is in the subset.
pub proof fn lemma_check_valid(c: clazel_codecheck::spec::Chk)
    requires
        c.i == rcx() && c.t == rdx() && c.z == rax() && 0 <= c.k < 16,
    ensures
        all_valid_instrs(clazel_codecheck::spec::check_seq(c)),
{
    let cs = clazel_codecheck::spec::check_seq(c);
    assert forall|j: int| 0 <= j < cs.len() implies x64::valid_instr(#[trigger] cs[j]) by {
        assert(j == 0 || j == 1 || j == 2 || j == 3 || j == 4 || j == 5 || j == 6 || j == 7);
        assert(cs[0] == clazel_codecheck::spec::check_instr(0, c));
        assert(cs[1] == clazel_codecheck::spec::check_instr(1, c));
        assert(cs[2] == clazel_codecheck::spec::check_instr(2, c));
        assert(cs[3] == clazel_codecheck::spec::check_instr(3, c));
        assert(cs[4] == clazel_codecheck::spec::check_instr(4, c));
        assert(cs[5] == clazel_codecheck::spec::check_instr(5, c));
        assert(cs[6] == clazel_codecheck::spec::check_instr(6, c));
        assert(cs[7] == clazel_codecheck::spec::check_instr(7, c));
    }
}

/// **A memory instruction's code is in the subset.**
pub proof fn lemma_mem_valid(mo: MemOp, nl: nat, h: nat)
    requires
        cf_flow(Node::Mem(mo), nl, h, 0) is Some,
    ensures
        all_valid_instrs(mem_code(mo, nl, h)),
{
    let k = mem_region(mo);
    assert(k < 16);
    let pre = mem_pre(mo, nl, h);
    let cs = mem_check(mo, nl, h);
    let tail = mem_tail(mo, nl, h);
    let stub = exit_seq(mem_exit_code(mo));
    let jm = seq![jmp_i(code_len(stub) as int)];
    crate::tlemmas::lemma_exit_valid(mem_exit_code(mo));
    lemma_check_valid(mem_chk(k, mem_n(mo), mem_r1(mo, nl, h), mem_r2(mo, nl, h)));
    assert(all_valid_instrs(jm));
    assert(all_valid_instrs(pre)) by {
        assert forall|q: int| 0 <= q < pre.len() implies x64::valid_instr(#[trigger] pre[q]) by {
            match mo {
                MemOp::BoundsCheck { .. } => {
                    crate::tlemmas::lemma_ls_valid(rcx(), (nl + h - 1) as nat);
                    assert(q == 0);
                },
                MemOp::Load { .. } => {
                    crate::tlemmas::lemma_ls_valid(rcx(), (nl + h - 1) as nat);
                    assert(q == 0 || q == 1);
                },
                MemOp::Store { .. } => {
                    crate::tlemmas::lemma_ls_valid(rdi(), (nl + h - 1) as nat);
                    crate::tlemmas::lemma_ls_valid(rcx(), (nl + h - 2) as nat);
                    assert(q == 0 || q == 1 || q == 2);
                },
            }
        }
    }
    assert(all_valid_instrs(tail)) by {
        assert forall|q: int| 0 <= q < tail.len() implies x64::valid_instr(#[trigger] tail[q]) by {
            match mo {
                MemOp::BoundsCheck { .. } => {
                    assert(false);
                },
                MemOp::Load { .. } => {
                    crate::tlemmas::lemma_ls_valid(rax(), (nl + h - 1) as nat);
                    assert(q == 0 || q == 1);
                },
                MemOp::Store { .. } => {
                    assert(q == 0);
                },
            }
        }
    }
    lemma_valid_cat(pre, cs);
    lemma_valid_cat(pre + cs, tail);
    lemma_valid_cat(pre + cs + tail, jm);
    lemma_valid_cat(pre + cs + tail + jm, stub);
}

/// The chain's entries are in the subset.
pub proof fn lemma_entries_valid(ls: Seq<usize>, offs: Seq<int>, p0: int, i: nat)
    ensures
        all_valid_instrs(brt_entries(ls, offs, p0, i)),
    decreases ls.len() - i,
{
    if i < ls.len() {
        let e = brt_entry(i, brt_rel(offs, ls[i as int], p0 + (i + 1) * brt_e()));
        assert(all_valid_instrs(e)) by {
            assert forall|q: int| 0 <= q < e.len() implies x64::valid_instr(#[trigger] e[q]) by {
                assert(q == 0 || q == 1 || q == 2);
            }
        }
        lemma_entries_valid(ls, offs, p0, i + 1);
        lemma_valid_cat(e, brt_entries(ls, offs, p0, i + 1));
    } else {
        assert(brt_entries(ls, offs, p0, i) =~= Seq::<x64::Instr>::empty());
    }
}

/// **`br_table`'s code is in the subset.**
pub proof fn lemma_brt_valid(ls: Seq<usize>, d: usize, nl: nat, h: nat, offs: Seq<int>)
    requires
        1 <= h,
        nl + h <= max_slots(),
    ensures
        all_valid_instrs(brt_code(ls, d, nl, h, offs)),
{
    let p0 = brt_p0(nl, h);
    let a = seq![load_slot(rax(), (nl + h - 1) as nat)];
    crate::tlemmas::lemma_ls_valid(rax(), (nl + h - 1) as nat);
    assert(all_valid_instrs(a));
    lemma_entries_valid(ls, offs, p0, 0);
    let jm = seq![jmp_i(brt_rel(offs, d, p0 + ls.len() * brt_e() + 5))];
    assert(all_valid_instrs(jm));
    lemma_valid_cat(a, brt_entries(ls, offs, p0, 0));
    lemma_valid_cat(a + brt_entries(ls, offs, p0, 0), jm);
}

/// **The validator accepts the access.** After `mov rsi, [r15 + 16 k]` and
/// the bounds check of `n` bytes on `rcx`, the facts the validator holds
/// ([`clazel_codecheck::spec::check_facts`]: `rsi` is region `k`'s base, `rdx`
/// and `rax` are unknown, `rcx` is checked for `n` bytes) admit `[rsi + rcx]`
/// for an access of at most `n` bytes, a load or a store
/// ([`clazel_codecheck::spec::access_ok`]).
pub proof fn lemma_access_accepted(k: int, n: int, size: int, store: bool)
    requires
        size <= n,
    ensures
        clazel_codecheck::spec::access_ok(
            seq![
                clazel_codecheck::spec::Binding {
                    reg: 6,
                    fact: clazel_codecheck::spec::Fact::Base(k),
                },
                clazel_codecheck::spec::Binding {
                    reg: 2,
                    fact: clazel_codecheck::spec::Fact::Unknown,
                },
                clazel_codecheck::spec::Binding {
                    reg: 0,
                    fact: clazel_codecheck::spec::Fact::Unknown,
                },
                clazel_codecheck::spec::Binding {
                    reg: 1,
                    fact: clazel_codecheck::spec::Fact::Idx(k, n),
                },
            ],
            clazel_codecheck::spec::Access { mem: ix_mem(), size: size, store: store },
        ),
{
    reveal_with_fuel(clazel_codecheck::spec::fact_of, 6);
}

/// The operand size of an access writes or reads as many bytes as its type
/// has (so the access is within the `n` bytes the check admitted).
pub proof fn lemma_mty_sz_bytes(ty: MTy)
    ensures
        x64::nbytes(mty_sz(ty)) == ty.size(),
{
}

/// The access size of a type is LIR's.
pub proof fn lemma_mty_size_is_lir(ty: MTy)
    ensures
        lir::ty_size(ty.lir_ty()) == ty.size(),
{
}

/// A `bounds_check`'s stub exits with the instruction's own code.
pub proof fn lemma_bc_exit_code(region: usize, size: usize, code: u32)
    ensures
        mem_exit_code(MemOp::BoundsCheck { region, size, code }) == code,
{
}

/// The chain's entry jumps on equal (`je`: the condition code of LIR's `eq`).
pub proof fn lemma_brt_cc(i: nat, rel: int)
    ensures
        brt_entry(i, rel)[2]->Jcc_cc == crate::templates::cc_of(lir::ICmp::Eq),
{
}

} // verus!
