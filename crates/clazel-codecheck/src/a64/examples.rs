//! Examples for the A64 spec: small programs, accepted and refused by
//! [`super::spec`], proven by evaluating it. They are evidence that the
//! spec says what jit.md J.6 means, and the data the kill certificates of
//! `mutations.json` cite: each refused program is one that a particular bug in
//! the spec would accept. The counterpart of [`crate::examples`].
//!
//! The programs are given as instruction sequences (the level of [`policy`]).
//! The last example ([`example_bytes_decode`]) ties one program to its bytes,
//! with `clazel-a64`'s canonical encoding, so the two levels meet.
//!
//! The branch offsets in the comments are in words (instructions): an A64
//! branch goes to its own address plus four times its immediate, so a branch at
//! instruction `p` to instruction `q` has the immediate `q - p`. The bounds
//! check is 7 instructions (its branches are its third and fifth) and the exit
//! sequence 3.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The exit sequence with scratch register `t`: `movz wt, #code`; `str xt,
/// [x28, #256]`; `ret`.
pub open spec fn exit_seq(t: u8, code: u16) -> Seq<Instr> {
    seq![
        Instr::MoveWide { sf: Width::W32, opcode: MoveWideOp::Z, d: t, imm16: code, hw: 0 },
        Instr::LoadStoreImm { sf: Width::W64, load: false, t: t, n: 28, imm12: 32 },
        Instr::Ret,
    ]
}

/// `ldr xdst, [x28, #16k]`: load region `k`'s base.
pub open spec fn base_load(dst: u8, k: int) -> Instr {
    Instr::LoadStoreImm { sf: Width::W64, load: true, t: dst, n: 28, imm12: (2 * k) as u16 }
}

/// `ldr xdst, [xbase, xidx]`: a 64-bit load from a region.
pub open spec fn region_load(dst: u8, base: u8, idx: u8) -> Instr {
    Instr::LoadStoreReg { sf: Width::W64, load: true, t: dst, n: base, m: idx, s: false }
}

/// A bounds check of region `k`, `n` bytes, index `x1`, scratch `x5` and `x6`,
/// its branches going `r1` and `r2` words on.
pub open spec fn chk(k: int, n: int, r1: i32, r2: i32) -> Chk {
    Chk { k: k, n: n, i: 1, t: 5, bnd: 6, r1: r1, r2: r2 }
}

/// Load region 3's base into `x2`, check `x1` for 8 bytes, load `[x2, x1]`
/// into `x0`, exit with code 1. Instruction numbers: the base load is 0, the
/// check 1 to 7 (its branches are 3 and 5), the access 8, the exit 9 to 11; so
/// the branches are 9 - 3 = 6 and 9 - 5 = 4.
pub open spec fn prog_checked_load(c: Chk) -> Seq<Instr> {
    seq![base_load(2, 3)] + check_seq(c) + seq![region_load(0, 2, 1)] + exit_seq(7, 1)
}

/// [`prog_checked_load`] with region 3, 8 bytes: the accepted case.
pub open spec fn prog_ok() -> Seq<Instr> {
    prog_checked_load(chk(3, 8, 6, 4))
}

/// A checked load is accepted: the base is region 3's, the index was checked
/// for 8 bytes of region 3, and both branches go to the exit sequence.
pub proof fn example_checked_load_accepted()
    ensures
        policy(prog_ok(), seq![0int]),
{
    assert(policy(prog_ok(), seq![0int])) by (compute_only);
}

/// The same load with no check in between is refused: `x1` has no fact.
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
        !policy(prog_checked_load(chk(3, 4, 6, 4)), seq![0int]),
{
    assert(!policy(prog_checked_load(chk(3, 4, 6, 4)), seq![0int])) by (compute_only);
}

/// A check against region 2's bound does not license an access through
/// region 3's base.
pub proof fn example_wrong_region_rejected()
    ensures
        !policy(prog_checked_load(chk(2, 8, 6, 4)), seq![0int]),
{
    assert(!policy(prog_checked_load(chk(2, 8, 6, 4)), seq![0int])) by (compute_only);
}

/// A shifted index is refused: the checked index is a byte index, and `S = 1`
/// would scale it by the access size.
pub open spec fn prog_scaled() -> Seq<Instr> {
    seq![base_load(2, 3)] + check_seq(chk(3, 8, 6, 4)) + seq![
        Instr::LoadStoreReg { sf: Width::W64, load: true, t: 0, n: 2, m: 1, s: true },
    ] + exit_seq(7, 1)
}

/// A shifted index is refused.
pub proof fn example_scaled_index_rejected()
    ensures
        !policy(prog_scaled(), seq![0int]),
{
    assert(!policy(prog_scaled(), seq![0int])) by (compute_only);
}

/// `add sp, x0, #0` then an exit sequence: refused, the stack pointer is
/// reserved.
pub open spec fn prog_write_sp() -> Seq<Instr> {
    seq![
        Instr::AddSubImm {
            sf: Width::W64,
            sub_op: false,
            setflags: false,
            d: 31,
            n: 0,
            imm12: 0,
            sh: false,
        },
    ] + exit_seq(7, 1)
}

/// A write to the stack pointer is refused (J.6: "reserved registers and the
/// stack pointer are written only in the fixed prologue and epilogue", which
/// are empty here).
pub proof fn example_write_sp_rejected()
    ensures
        !policy(prog_write_sp(), seq![0int]),
{
    assert(!policy(prog_write_sp(), seq![0int])) by (compute_only);
}

/// `movz x28, #0` then an exit sequence.
pub open spec fn prog_write_ctx() -> Seq<Instr> {
    seq![
        Instr::MoveWide { sf: Width::W64, opcode: MoveWideOp::Z, d: 28, imm16: 0, hw: 0 },
    ] + exit_seq(7, 1)
}

/// A write to the context register is refused.
pub proof fn example_write_ctx_rejected()
    ensures
        !policy(prog_write_ctx(), seq![0int]),
{
    assert(!policy(prog_write_ctx(), seq![0int])) by (compute_only);
}

/// `movz x30, #0` then an exit sequence.
pub open spec fn prog_write_link() -> Seq<Instr> {
    seq![
        Instr::MoveWide { sf: Width::W64, opcode: MoveWideOp::Z, d: 30, imm16: 0, hw: 0 },
    ] + exit_seq(7, 1)
}

/// A write to the link register is refused: the exit sequence's `ret` returns
/// through it.
pub proof fn example_write_link_rejected()
    ensures
        !policy(prog_write_link(), seq![0int]),
{
    assert(!policy(prog_write_link(), seq![0int])) by (compute_only);
}

/// `cmp x0, x1` (`subs xzr, x0, x1`) then an exit sequence: the destination
/// 31 is the zero register here, not `SP`.
pub open spec fn prog_cmp() -> Seq<Instr> {
    seq![
        Instr::AddSubShiftedReg {
            sf: Width::W64,
            sub_op: true,
            setflags: true,
            d: 31,
            n: 0,
            m: 1,
            shift_type: ShiftType::Lsl,
            shift_amount: 0,
        },
    ] + exit_seq(7, 1)
}

/// A compare is accepted: it writes the zero register, not the stack pointer.
pub proof fn example_cmp_accepted()
    ensures
        policy(prog_cmp(), seq![0int]),
{
    assert(policy(prog_cmp(), seq![0int])) by (compute_only);
}

/// `b +2` at 0, then a bounds check at 1 to 7 whose second instruction is 2
/// (the `b` goes to it); the check's branches (instructions 3 and 5) go to the
/// exit sequence at 8: 5 and 3.
pub open spec fn prog_jump_into_check() -> Seq<Instr> {
    seq![Instr::B { imm26: 2 }] + check_seq(chk(3, 8, 5, 3)) + exit_seq(7, 1)
}

/// A branch target that is not the start of a unit is refused.
pub proof fn example_jump_into_check_rejected()
    ensures
        !policy(prog_jump_into_check(), seq![0int]),
{
    assert(!policy(prog_jump_into_check(), seq![0int])) by (compute_only);
}

/// A branch from before the check to the access after it: `b` is 0, the base
/// load 1, the check 2 to 8 (its branches are 4 and 6), the access 9 and the
/// exit 10 to 12; the `b` is 9 - 0 = 9, the check's branches 10 - 4 = 6 and
/// 10 - 6 = 4.
pub open spec fn prog_jump_over_check() -> Seq<Instr> {
    seq![Instr::B { imm26: 9 }, base_load(2, 3)] + check_seq(chk(3, 8, 6, 4)) + seq![
        region_load(0, 2, 1),
    ] + exit_seq(7, 1)
}

/// The access is a branch target, so what the check established is forgotten
/// there: it could be reached without the check. Refused.
pub proof fn example_jump_over_check_rejected()
    ensures
        !policy(prog_jump_over_check(), seq![0int]),
{
    assert(!policy(prog_jump_over_check(), seq![0int])) by (compute_only);
}

/// A store to the region table of the context, `str x0, [x28, #0]`.
pub open spec fn prog_store_table() -> Seq<Instr> {
    seq![Instr::LoadStoreImm { sf: Width::W64, load: false, t: 0, n: 28, imm12: 0 }]
        + exit_seq(7, 1)
}

/// The region table is never written (a store to the context must be in the
/// exit area), or code could widen its own regions.
pub proof fn example_store_table_rejected()
    ensures
        !policy(prog_store_table(), seq![0int]),
{
    assert(!policy(prog_store_table(), seq![0int])) by (compute_only);
}

/// `str x0, [x28, #264]` (an exit operand) then the exit sequence.
pub open spec fn prog_store_operand() -> Seq<Instr> {
    seq![Instr::LoadStoreImm { sf: Width::W64, load: false, t: 0, n: 28, imm12: 33 }]
        + exit_seq(7, 1)
}

/// A store to an exit operand is accepted.
pub proof fn example_store_operand_accepted()
    ensures
        policy(prog_store_operand(), seq![0int]),
{
    assert(policy(prog_store_operand(), seq![0int])) by (compute_only);
}

/// `str x0, [x28, #512]` is past the end of the context (`imm12 = 64`).
pub proof fn example_store_past_context_rejected()
    ensures
        !policy(
            seq![Instr::LoadStoreImm { sf: Width::W64, load: false, t: 0, n: 28, imm12: 64 }]
                + exit_seq(7, 1),
            seq![0int],
        ),
{
    assert(!policy(
        seq![Instr::LoadStoreImm { sf: Width::W64, load: false, t: 0, n: 28, imm12: 64 }]
            + exit_seq(7, 1),
        seq![0int],
    )) by (compute_only);
}

/// A bare `add x0, x0, x3`: nothing after it, control runs off the end.
pub open spec fn prog_falls_off() -> Seq<Instr> {
    seq![
        Instr::AddSubShiftedReg {
            sf: Width::W64,
            sub_op: false,
            setflags: false,
            d: 0,
            n: 0,
            m: 3,
            shift_type: ShiftType::Lsl,
            shift_amount: 0,
        },
    ]
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

/// A loop: `add x0, x0, x3; b -1` (the branch is at 1 and goes to 0).
pub open spec fn prog_loop() -> Seq<Instr> {
    seq![
        Instr::AddSubShiftedReg {
            sf: Width::W64,
            sub_op: false,
            setflags: false,
            d: 0,
            n: 0,
            m: 3,
            shift_type: ShiftType::Lsl,
            shift_amount: 0,
        },
        Instr::B { imm26: -1i32 },
    ]
}

/// A backward branch to the first instruction is accepted, and the blob ends in
/// a `b`.
pub proof fn example_loop_accepted()
    ensures
        policy(prog_loop(), seq![0int]),
{
    assert(policy(prog_loop(), seq![0int])) by (compute_only);
}

/// A conditional branch last in the blob is refused: not taken, control runs
/// off the end. `cbz x0, +0` (to itself) is the whole blob.
pub proof fn example_cbz_last_rejected()
    ensures
        !policy(
            seq![Instr::CompareBranch { sf: Width::W64, iszero: true, t: 0, imm19: 0 }],
            seq![0int],
        ),
{
    assert(!policy(
        seq![Instr::CompareBranch { sf: Width::W64, iszero: true, t: 0, imm19: 0 }],
        seq![0int],
    )) by (compute_only);
}

/// An entry in the middle of a unit is refused: the same program as
/// [`prog_ok`], entered at byte 12 (instruction 3, inside the bounds check).
pub proof fn example_entry_inside_unit_rejected()
    ensures
        !policy(prog_ok(), seq![12int]),
{
    assert(!policy(prog_ok(), seq![12int])) by (compute_only);
}

/// An entry that is not a multiple of 4 is refused: no word starts there.
pub proof fn example_entry_unaligned_rejected()
    ensures
        !policy(prog_ok(), seq![2int]),
{
    assert(!policy(prog_ok(), seq![2int])) by (compute_only);
}

/// A second entry at a unit start is accepted: the exit sequence at
/// instruction 9, byte 36.
pub proof fn example_second_entry_accepted()
    ensures
        policy(prog_ok(), seq![0int, 36int]),
{
    assert(policy(prog_ok(), seq![0int, 36int])) by (compute_only);
}

/// A branch out of the blob: `b +100` from a one-instruction blob.
pub proof fn example_jump_out_rejected()
    ensures
        !policy(seq![Instr::B { imm26: 100 }], seq![0int]),
{
    assert(!policy(seq![Instr::B { imm26: 100 }], seq![0int])) by (compute_only);
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

/// The exit sequence with `x0` as scratch, as bytes (each word little-endian):
/// `movz w0, #7` (`0x528000E0`), `str x0, [x28, #256]` (`0xF9008380`), `ret`
/// (`0xD65F03C0`).
pub open spec fn exit_blob() -> Seq<u8> {
    seq![0xE0u8, 0x00, 0x80, 0x52, 0x80, 0x83, 0x00, 0xF9, 0xC0, 0x03, 0x5F, 0xD6]
}

/// The bytes are the canonical encodings of [`exit_seq`], and the blob is
/// accepted.
pub proof fn example_bytes_decode()
    ensures
        decodes_to(exit_blob(), exit_seq(0, 7)),
        accepted(exit_blob(), seq![0int]),
{
    example_exit_accepted();
    example_exit_valid();
    assert(exit_blob().subrange(0, 4) =~= word_bytes(encode(exit_seq(0, 7)[0]))) by (compute_only);
    assert(exit_blob().subrange(4, 8) =~= word_bytes(encode(exit_seq(0, 7)[1]))) by (compute_only);
    assert(exit_blob().subrange(8, 12) =~= word_bytes(encode(exit_seq(0, 7)[2]))) by (
        compute_only
    );
    assert forall|j: int| 0 <= j < exit_seq(0, 7).len() implies exit_blob().subrange(
        4 * j,
        4 * j + 4,
    ) == word_bytes(encode(#[trigger] exit_seq(0, 7)[j])) by {
        assert(j == 0 || j == 1 || j == 2);
    }
    assert(exit_blob().len() == 12) by (compute_only);
    assert(decodes_to(exit_blob(), exit_seq(0, 7)));
}

} // verus!
