//! Facts proven about [`super::spec`] (docs/SPEC-STYLE.md: "prove at least one
//! property of the spec"). They are evidence that the transcription says what
//! jit.md J.6 means, not part of what the validator must meet: each one
//! restates a rule of J.6 in a form that does not mention how the spec
//! computes it (the reserved registers are the numbers 4 and 15, not
//! `abi::reserved`; the exit area is the bytes 256 to 511), and the proof is
//! that the spec implies it.
//!
//! They are also what the kill certificates of `mutations.json` cite. A
//! lemma is general (every facts list, every instruction), so a spec bug that
//! breaks it has a counterexample, and a certificate evaluates the spec on that
//! one. The examples in [`super::examples`] are kept apart, so that a mutant
//! that breaks one of them does not stop Verus before it checks a certificate
//! here.
//!
//! The concrete data for the certificates are the `cx_*` spec functions at the
//! end of this file.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The register of a memory operand's index (0 if it has none).
pub open spec fn idx_reg(m: Mem) -> u8 {
    match m.index {
        Some(ix) => ix.reg,
        None => 0,
    }
}

/// The fact is a bounds check that admits at least `size` bytes.
pub open spec fn idx_covers(f: Fact, size: int) -> bool {
    match f {
        Fact::Idx(_, n) => size <= n,
        _ => false,
    }
}

/// The two facts name one region: a base of region `k`, an index checked
/// against region `k`.
pub open spec fn same_region(base: Fact, idx: Fact) -> bool {
    match (base, idx) {
        (Fact::Base(k), Fact::Idx(k2, _)) => k == k2,
        _ => false,
    }
}

/// **A region access is a checked access** (J.6: "every load and store uses a
/// region base register plus an index register that was compared against that
/// region's bound"). If an access not through the context is permitted, its
/// index register is known to be bounds-checked ([`Fact::Idx`]), for at least
/// as many bytes as the access touches, against the same region as the base
/// register, which is known to hold that region's base; and there is no
/// displacement.
pub proof fn lemma_region_access_facts(fs: Facts, a: Access)
    requires
        access_ok(fs, a),
        a.mem.base != 15,
    ensures
        a.mem.disp == 0,
        fact_of(fs, idx_reg(a.mem)) is Idx,
        idx_covers(fact_of(fs, idx_reg(a.mem)), a.size),
        same_region(fact_of(fs, a.mem.base), fact_of(fs, idx_reg(a.mem))),
{
}

/// **The region table is never written** (J.6, and jit.md: "a fixed table of
/// (base, bound) pairs"): a store through the context register lies in the
/// exit area, bytes 256 to 511 of the 512-byte context.
pub proof fn lemma_ctx_store_in_exit_area(fs: Facts, a: Access)
    requires
        access_ok(fs, a),
        a.mem.base == 15,
        a.store,
    ensures
        256 <= a.mem.disp,
        a.mem.disp + a.size <= 512,
{
}

/// **No other instruction is a write to a reserved register or a `ret`** (J.6:
/// "reserved registers and the stack pointer are written only in the fixed
/// prologue and epilogue", empty here; "no indirect branch except the exit
/// sequence"): an instruction the scan takes alone never writes `rsp` (4) or
/// `r15` (15), and is not `ret`.
pub proof fn lemma_plain_ok_safe(fs: Facts, i: Instr)
    requires
        plain_ok(fs, i) is Some,
    ensures
        !(i is Ret),
        written_gpr(i) != Some(4u8),
        written_gpr(i) != Some(15u8),
{
}

/// **No blob runs off its end** (J.6: "every path ends in the exit sequence
/// or a branch"): an accepted instruction list is not empty, and ends in
/// `ret` (which only an exit sequence has) or `jmp`.
pub proof fn lemma_policy_ends(ins: Seq<Instr>, entries: Seq<int>)
    requires
        policy(ins, entries),
    ensures
        ins.len() > 0,
        ins.last() is Ret || ins.last() is Jmp,
{
}

/// The offsets at which the scan found units begin (empty if it refused one).
pub open spec fn unit_starts(ins: Seq<Instr>, entries: Seq<int>) -> Seq<int> {
    match scan(ins, all_targets(ins, entries), 0, no_facts()) {
        Some(starts) => starts,
        None => Seq::empty(),
    }
}

/// **Every direct target and every entry is the start of a unit** (J.6:
/// "every direct target is a decoded boundary inside the blob"; stronger here,
/// because a jump into the middle of a recognized sequence would skip part of
/// it). A unit starts at an instruction boundary of the blob, so a target that
/// is a unit start is a boundary inside the blob.
pub proof fn lemma_policy_targets_are_unit_starts(ins: Seq<Instr>, entries: Seq<int>)
    requires
        policy(ins, entries),
    ensures
        subset_of(all_targets(ins, entries), unit_starts(ins, entries)),
{
}

/// **What is known about registers does not flow into a jump target** (J.6:
/// the check is "earlier in the same basic block"): the scan from an
/// instruction whose offset is a target gives the same result whatever was
/// known before it.
pub proof fn lemma_scan_forgets_at_targets(ins: Seq<Instr>, tg: Seq<int>, j: int, fs: Facts)
    requires
        0 <= j < ins.len(),
        seq_has(tg, start_of(ins, j)),
    ensures
        scan(ins, tg, j, fs) == scan(ins, tg, j, no_facts()),
{
}

// ---- Data for the certificates ----

/// `r2` is region 3's base and `r1` is checked for 8 bytes of region 3.
pub open spec fn cx_checked() -> Facts {
    set_fact(cx_base2(), 1, Fact::Idx(3, 8))
}

/// `r2` is region 3's base.
pub open spec fn cx_base2() -> Facts {
    set_fact(no_facts(), 2, Fact::Base(3))
}

/// `r2` is region 3's base, `r1` is checked for 4 bytes of region 3.
pub open spec fn cx_idx4() -> Facts {
    set_fact(cx_base2(), 1, Fact::Idx(3, 4))
}

/// `r2` is region 3's base, `r1` is checked for 8 bytes of region 2.
pub open spec fn cx_idx_region2() -> Facts {
    set_fact(cx_base2(), 1, Fact::Idx(2, 8))
}

/// An 8-byte load `[r2 + r1]`.
pub open spec fn cx_load() -> Access {
    Access {
        mem: Mem { base: 2, index: Some(Index { reg: 1, scale: 0 }), disp: 0 },
        size: 8,
        store: false,
    }
}

/// An 8-byte store to the region table, `[r15 + 0]`.
pub open spec fn cx_table_store() -> Access {
    Access { mem: Mem { base: 15, index: None, disp: 0 }, size: 8, store: true }
}

/// `mov rsp, rax`.
pub open spec fn cx_mov_rsp() -> Instr {
    Instr::MovRR { sz: Size::W64, dst: 4, src: 0 }
}

/// A one-instruction list that is not an exit: `add rax, rbx`.
pub open spec fn cx_falls_off() -> Seq<Instr> {
    seq![Instr::AluRR { alu: AluOp::Add, sz: Size::W64, dst: 0, src: 3 }]
}

} // verus!
