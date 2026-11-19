//! One step inside a unit of the scan ([`unit_at`]): a plain instruction, one
//! of the eight of a bounds-check sequence, or one of the three of an exit
//! sequence. [`mid_ok`] is the machine invariant at instruction `m` of the
//! unit that starts at instruction `j`; [`lemma_unit_step`] says each step is
//! safe and leads to the invariant at the next position.

#[allow(unused_imports)]
use super::safety::*;
#[allow(unused_imports)]
use super::safety_chk::*;
#[allow(unused_imports)]
use super::safety_inv::*;
#[allow(unused_imports)]
use super::safety_sem::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The number of instructions of the unit at `j`.
pub open spec fn unit_len(ins: Seq<Instr>, j: int, fs0: Facts) -> int {
    unit_at(ins, j, fs0)->Some_0.len
}

/// What the scan knows after the unit at `j`.
pub open spec fn unit_facts(ins: Seq<Instr>, j: int, fs0: Facts) -> Facts {
    unit_at(ins, j, fs0)->Some_0.facts
}

/// **The machine invariant at instruction `m` of the unit at `j`**, entered
/// with facts `fs0`: for a plain instruction (`m = 0`), the facts hold; for a
/// bounds check, [`chk_mid`]; for an exit sequence, after its first
/// instruction the scratch register holds the exit code.
pub open spec fn mid_ok(s: State, h: Handed, ins: Seq<Instr>, j: int, fs0: Facts, m: int) -> bool {
    if exit_unit_at(ins, j) {
        m == 1 ==> s.rgf[ins[j]->MovImm32_dst as int] as int == ins[j]->MovImm32_imm_u32 as int
    } else if check_unit_at(ins, j) {
        chk_mid(s, h, check_params(ins, j)->Some_0, fs0, m)
    } else {
        holds(s, h, fs0)
    }
}

/// What one step at position `m` of the unit at `j` does.
pub open spec fn unit_step_post(
    h: Handed,
    blob: Seq<u8>,
    ins: Seq<Instr>,
    j: int,
    fs0: Facts,
    m: int,
    s: State,
    s2: State,
    i: Instr,
) -> bool {
    &&& step_safe(h, s, i, s2)
    &&& (i is Ret ==> exit_unit_at(ins, j) && m == 2)
    &&& (!(i is Ret) ==> ctx_inv(s2, h, blob) && s2.rgf.len() == 16)
    &&& (i is Jmp ==> s2.rip == s.rip + instr_len(i) + i->Jmp_rel)
    &&& (jumps(s, i) ==> s2.rip == s.rip + instr_len(i) + i->Jcc_rel)
    &&& (!(i is Ret) && !(i is Jmp) && !jumps(s, i) ==> s2.rip == s.rip + instr_len(i) && (
    if m + 1 < unit_len(ins, j, fs0) {
        mid_ok(s2, h, ins, j, fs0, m + 1)
    } else {
        m + 1 == unit_len(ins, j, fs0) && holds(s2, h, unit_facts(ins, j, fs0))
    }))
}

/// The exit sequence's instructions are the ones `exit_unit_at` names.
proof fn lemma_exit_step(
    u: spec_fn(nat) -> nat,
    h: Handed,
    blob: Seq<u8>,
    ins: Seq<Instr>,
    j: int,
    fs0: Facts,
    m: int,
    s: State,
    s2: State,
    i: Instr,
)
    requires
        handed_ok(h),
        ctx_inv(s, h, blob),
        all_valid(ins),
        exit_unit_at(ins, j),
        0 <= m < 3,
        i == ins[j + m],
        mid_ok(s, h, ins, j, fs0, m),
        step(u, s, i) == Some(s2),
    ensures
        unit_step_post(h, blob, ins, j, fs0, m, s, s2, i),
{
    lemma_p2_vals();
    assert(valid_instr(i));
    assert(s.rgf.len() == 16);
    lemma_step_frame(u, s, i, s2);
    lemma_mem_access_valid(i);
    let t = ins[j]->MovImm32_dst;
    assert(!abi::reserved(t));
    assert(unit_len(ins, j, fs0) == 3);
    if m == 0 {
        let imm = ins[j]->MovImm32_imm_u32;
        lemma_wr64(s, t, loghead(32, imm as int));
        assert(s2.rgf[t as int] as int == imm as int);
        assert(s2.rgf[15] == s.rgf[15] && s2.rgf[4] == s.rgf[4]);
        lemma_ctx_inv_preserved(h, blob, s, s2, i);
    } else if m == 1 {
        let a = mem_access(i)->Some_0;
        lemma_no_facts_hold(s, h);
        lemma_access_allowed(s, h, no_facts(), a);
        assert(s2.rgf[15] == s.rgf[15] && s2.rgf[4] == s.rgf[4]);
        lemma_ctx_inv_preserved(h, blob, s, s2, i);
    } else {
        assert(i is Ret);
    }
}

/// **One step inside a unit.**
#[verifier::rlimit(400)]
pub proof fn lemma_unit_step(
    u: spec_fn(nat) -> nat,
    h: Handed,
    blob: Seq<u8>,
    ins: Seq<Instr>,
    j: int,
    fs0: Facts,
    m: int,
    s: State,
    s2: State,
    i: Instr,
)
    requires
        handed_ok(h),
        ctx_inv(s, h, blob),
        all_valid(ins),
        unit_at(ins, j, fs0) is Some,
        0 <= m < unit_len(ins, j, fs0),
        0 <= j + m < ins.len(),
        i == ins[j + m],
        mid_ok(s, h, ins, j, fs0, m),
        step(u, s, i) == Some(s2),
    ensures
        unit_step_post(h, blob, ins, j, fs0, m, s, s2, i),
{
    if exit_unit_at(ins, j) {
        lemma_exit_step(u, h, blob, ins, j, fs0, m, s, s2, i);
    } else if check_unit_at(ins, j) {
        let c = check_params(ins, j)->Some_0;
        assert(unit_len(ins, j, fs0) == 8);
        assert(check_ok(c));
        assert(valid_instr(ins[j]) && valid_instr(ins[j + 5]));
        assert(i == check_instr(m, c));
        assert(chk_ok(h, c));
        lemma_chk_step(u, h, blob, c, fs0, m, s, s2, i);
        assert(!(i is Ret) && !(i is Jmp));
        assert(unit_facts(ins, j, fs0) == chk_facts(fs0, c));
    } else {
        assert(m == 0);
        assert(unit_len(ins, j, fs0) == 1);
        let fs2 = plain_ok(fs0, ins[j])->Some_0;
        assert(unit_facts(ins, j, fs0) == fs2);
        assert(valid_instr(i));
        lemma_plain_step(u, h, blob, s, s2, i, fs0, fs2);
        assert(!(i is Ret));
    }
}

} // verus!
