//! Examples: small programs, accepted and refused by the spec, proven by
//! evaluating it. They are evidence that [`super::spec`] says what jit.md
//! J.6 means, and the lemmas that `mutations.json` cites in its kill
//! certificates: each refused program is one that a particular bug in the spec
//! would accept.
//!
//! The programs are given as instruction sequences (the level of
//! [`policy`]), because that is where the checks are. The last example
//! ([`example_bytes_decode`]) ties one program to its bytes, with
//! `clazel-x64`'s canonical encoding, so the two levels meet.
//!
//! The jump displacements in the comments are worked out from the instruction
//! lengths of `clazel-x64`'s `encode`: `mov r64, [mem]` and every `r, [mem]`
//! instruction is 8 bytes, `mov r, r` 3, `add r, imm32` 7, `jcc rel32` 6,
//! `mov r32, imm32` 5, `cmovcc` 4, `jmp rel32` 5, `ret` 1; so the bounds
//! check is 47 bytes (its two jumps end 16 and 30 bytes in) and the exit
//! sequence 14.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A context operand: `[r15 + disp]`.
pub open spec fn ctxm(disp: int) -> Mem {
    Mem { base: 15, index: None, disp: disp as i32 }
}

/// The exit sequence with scratch register `t`: `mov t, code`; `mov
/// [r15 + 256], t`; `ret`.
pub open spec fn exit_seq(t: u8, code: u32) -> Seq<Instr> {
    seq![
        Instr::MovImm32 { dst: t, imm_u32: code },
        Instr::MovStore { sz: Size::W64, mem: ctxm(256), src: t },
        Instr::Ret,
    ]
}

/// `mov dst, [r15 + 16k]`: load region `k`'s base.
pub open spec fn base_load(dst: u8, k: int) -> Instr {
    Instr::MovLoad { sz: Size::W64, dst: dst, mem: ctxm(16 * k) }
}

/// `mov dst, [base + idx]`: a 64-bit load from a region.
pub open spec fn region_load(dst: u8, base: u8, idx: u8) -> Instr {
    Instr::MovLoad {
        sz: Size::W64,
        dst: dst,
        mem: Mem { base: base, index: Some(Index { reg: idx, scale: 0 }), disp: 0 },
    }
}

/// A bounds check of region `k`, `n` bytes, index `r1`, scratch `r5` and `r6`,
/// both jumps going `r1`/`r2` bytes on.
pub open spec fn chk(k: int, n: int, r1: i32, r2: i32) -> Chk {
    Chk { k: k, n: n, i: 1, t: 5, z: 6, r1: r1, r2: r2 }
}

/// Load region 3's base into `r2`, check `r1` for 8 bytes, load `[r2 + r1]`
/// into `r0`, exit with code 1. Byte offsets: the base load is at 0, the check
/// at 8 (its jumps end at 24 and 38), the access at 55, the exit at 63: so
/// the jumps are 63 - 24 = 39 and 63 - 38 = 25.
pub open spec fn prog_checked_load(c: Chk) -> Seq<Instr> {
    seq![base_load(2, 3)] + check_seq(c) + seq![region_load(0, 2, 1)] + exit_seq(7, 1)
}

/// [`prog_checked_load`] with region 3, 8 bytes: the accepted case.
pub open spec fn prog_ok() -> Seq<Instr> {
    prog_checked_load(chk(3, 8, 39, 25))
}

/// A checked load is accepted: the base is region 3's, the index was checked
/// for 8 bytes of region 3, and both jumps go to the exit sequence.
pub proof fn example_checked_load_accepted()
    ensures
        policy(prog_ok(), seq![0int]),
{
    assert(policy(prog_ok(), seq![0int])) by (compute_only);
}

/// The same load with no check in between is refused: `r1` has no fact.
pub open spec fn prog_unchecked() -> Seq<Instr> {
    seq![base_load(2, 3), region_load(0, 2, 1)] + exit_seq(7, 1)
}

/// A load whose index was never bounds-checked is refused (J.6: "an index
/// register that was compared against that region's bound").
pub proof fn example_unchecked_load_rejected()
    ensures
        !policy(prog_unchecked(), seq![0int]),
{
    assert(!policy(prog_unchecked(), seq![0int])) by (compute_only);
}

/// A check for 4 bytes licenses no 8-byte load.
pub proof fn example_short_check_rejected()
    ensures
        !policy(prog_checked_load(chk(3, 4, 39, 25)), seq![0int]),
{
    assert(!policy(prog_checked_load(chk(3, 4, 39, 25)), seq![0int])) by (compute_only);
}

/// A check against region 2's bound does not license an access through
/// region 3's base.
pub proof fn example_wrong_region_rejected()
    ensures
        !policy(prog_checked_load(chk(2, 8, 39, 25)), seq![0int]),
{
    assert(!policy(prog_checked_load(chk(2, 8, 39, 25)), seq![0int])) by (compute_only);
}

/// `mov rsp, rax` then an exit sequence: refused, the stack pointer is
/// reserved.
pub open spec fn prog_write_rsp() -> Seq<Instr> {
    seq![Instr::MovRR { sz: Size::W64, dst: 4, src: 0 }] + exit_seq(7, 1)
}

/// A write to the stack pointer is refused (J.6: "reserved registers and the
/// stack pointer are written only in the fixed prologue and epilogue", which
/// are empty here).
pub proof fn example_write_rsp_rejected()
    ensures
        !policy(prog_write_rsp(), seq![0int]),
{
    assert(!policy(prog_write_rsp(), seq![0int])) by (compute_only);
}

/// `mov r15d, 0` then an exit sequence.
pub open spec fn prog_write_ctx() -> Seq<Instr> {
    seq![Instr::MovImm32 { dst: 15, imm_u32: 0 }] + exit_seq(7, 1)
}

/// A write to the context register is refused.
pub proof fn example_write_ctx_rejected()
    ensures
        !policy(prog_write_ctx(), seq![0int]),
{
    assert(!policy(prog_write_ctx(), seq![0int])) by (compute_only);
}

/// `jmp` into the second instruction of a bounds check, which would skip the
/// first. `jmp +3` is at 0 (5 bytes) and the check at 5, whose second
/// instruction is at 8; the check's jumps end at 21 and 35 and go to the exit
/// sequence at 52.
pub open spec fn prog_jump_into_check() -> Seq<Instr> {
    seq![Instr::Jmp { rel: 3 }] + check_seq(chk(3, 8, 31, 17)) + exit_seq(7, 1)
}

/// A jump target that is not the start of a unit is refused.
pub proof fn example_jump_into_check_rejected()
    ensures
        !policy(prog_jump_into_check(), seq![0int]),
{
    assert(!policy(prog_jump_into_check(), seq![0int])) by (compute_only);
}

/// A jump from before the check to the access after it: `jmp` at 0, the base
/// load at 5, the check at 13 (its jumps end at 29 and 43), the access at 60
/// and the exit at 68.
pub open spec fn prog_jump_over_check() -> Seq<Instr> {
    seq![Instr::Jmp { rel: 55 }, base_load(2, 3)] + check_seq(chk(3, 8, 39, 25)) + seq![
        region_load(0, 2, 1),
    ] + exit_seq(7, 1)
}

/// The access is a jump target, so what the check established is forgotten
/// there: it could be reached without the check. Refused.
pub proof fn example_jump_over_check_rejected()
    ensures
        !policy(prog_jump_over_check(), seq![0int]),
{
    assert(!policy(prog_jump_over_check(), seq![0int])) by (compute_only);
}

/// A store to the region table of the context, `mov [r15 + 0], rax`.
pub open spec fn prog_store_table() -> Seq<Instr> {
    seq![Instr::MovStore { sz: Size::W64, mem: ctxm(0), src: 0 }] + exit_seq(7, 1)
}

/// The region table is never written (a store to the context must be in the
/// exit area), or code could widen its own regions.
pub proof fn example_store_table_rejected()
    ensures
        !policy(prog_store_table(), seq![0int]),
{
    assert(!policy(prog_store_table(), seq![0int])) by (compute_only);
}

/// `mov [r15 + 264], rax` (an exit operand) then the exit sequence.
pub open spec fn prog_store_operand() -> Seq<Instr> {
    seq![Instr::MovStore { sz: Size::W64, mem: ctxm(264), src: 0 }] + exit_seq(7, 1)
}

/// A store to an exit operand is accepted.
pub proof fn example_store_operand_accepted()
    ensures
        policy(prog_store_operand(), seq![0int]),
{
    assert(policy(prog_store_operand(), seq![0int])) by (compute_only);
}

/// A bare `add rax, rbx`: nothing after it, control runs off the end.
pub open spec fn prog_falls_off() -> Seq<Instr> {
    seq![Instr::AluRR { alu: AluOp::Add, sz: Size::W64, dst: 0, src: 3 }]
}

/// A blob that can run past its end is refused (J.6: "every path ends in the
/// exit sequence or a branch").
pub proof fn example_falls_off_rejected()
    ensures
        !policy(prog_falls_off(), seq![0int]),
{
    assert(!policy(prog_falls_off(), seq![0int])) by (compute_only);
}

/// A `ret` that is not the end of an exit sequence.
pub open spec fn prog_bare_ret() -> Seq<Instr> {
    seq![Instr::Ret]
}

/// `ret` outside the exit sequence is refused (J.6: "no indirect branch
/// except the exit sequence").
pub proof fn example_bare_ret_rejected()
    ensures
        !policy(prog_bare_ret(), seq![0int]),
{
    assert(!policy(prog_bare_ret(), seq![0int])) by (compute_only);
}

/// A loop: `add rax, rbx; jmp -8` (the add is 3 bytes and the jump 5, so the
/// next instruction is at 8, and the target is the add at 0: 0 - 8 = -8).
pub open spec fn prog_loop() -> Seq<Instr> {
    seq![
        Instr::AluRR { alu: AluOp::Add, sz: Size::W64, dst: 0, src: 3 },
        Instr::Jmp { rel: -8i32 },
    ]
}

/// A backward jump to the first instruction is accepted, and the blob ends in
/// a `jmp`.
pub proof fn example_loop_accepted()
    ensures
        policy(prog_loop(), seq![0int]),
{
    assert(policy(prog_loop(), seq![0int])) by (compute_only);
}

/// An entry in the middle of a unit is refused: the same program as
/// [`prog_ok`], entered at 9 (inside the bounds check).
pub proof fn example_entry_inside_unit_rejected()
    ensures
        !policy(prog_ok(), seq![9int]),
{
    assert(!policy(prog_ok(), seq![9int])) by (compute_only);
}

/// A second entry at a unit start is accepted: the exit sequence at 63.
pub proof fn example_second_entry_accepted()
    ensures
        policy(prog_ok(), seq![0int, 63int]),
{
    assert(policy(prog_ok(), seq![0int, 63int])) by (compute_only);
}

/// A jump out of the blob: `jmp +100` from a one-instruction blob.
pub proof fn example_jump_out_rejected()
    ensures
        !policy(seq![Instr::Jmp { rel: 100 }], seq![0int]),
{
    assert(!policy(seq![Instr::Jmp { rel: 100 }], seq![0int])) by (compute_only);
}
/// The exit sequence alone is accepted, entered at 0.
pub proof fn example_exit_accepted()
    ensures
        policy(exit_seq(0, 7), seq![0int]),
{
    assert(policy(exit_seq(0, 7), seq![0int])) by (compute_only);
}

/// The three instructions of an exit sequence are in the subset.
pub proof fn example_exit_valid()
    ensures
        all_valid(exit_seq(0, 7)),
{
    assert(valid_instr(exit_seq(0, 7)[0]) && valid_instr(exit_seq(0, 7)[1]) && valid_instr(
        exit_seq(0, 7)[2],
    )) by (compute_only);
    assert forall|j: int| 0 <= j < exit_seq(0, 7).len() implies valid_instr(
        #[trigger] exit_seq(0, 7)[j],
    ) by {
        assert(j == 0 || j == 1 || j == 2);
    }
}

/// The exit sequence with `r0` as scratch, as bytes: `mov eax, 7` (`B8 07 00
/// 00 00`), `mov [r15 + 256], rax` (`49 89 84 27 00 01 00 00`), `ret` (`C3`).
pub proof fn example_bytes_decode()
    ensures
        enc_all(exit_seq(0, 7)) =~= seq![
            0xB8u8, 0x07, 0x00, 0x00, 0x00, 0x49, 0x89, 0x84, 0x27, 0x00, 0x01, 0x00, 0x00, 0xC3,
        ],
        accepted(
            seq![
                0xB8u8, 0x07, 0x00, 0x00, 0x00, 0x49, 0x89, 0x84, 0x27, 0x00, 0x01, 0x00, 0x00,
                0xC3,
            ],
            seq![0int],
        ),
{
    reveal_with_fuel(le_bytes, 5);
    reveal_with_fuel(enc_all, 4);
    example_exit_accepted();
    example_exit_valid();
    let blob = seq![
        0xB8u8, 0x07, 0x00, 0x00, 0x00, 0x49, 0x89, 0x84, 0x27, 0x00, 0x01, 0x00, 0x00, 0xC3,
    ];
    assert(enc_all(exit_seq(0, 7)) =~= blob);
    assert(decodes_to(blob, exit_seq(0, 7)));
}

} // verus!
