//! The **executable decoder**: [`decode_instr`] reads one word and is proven
//! to meet [`crate::contract::decode_ensures`] (jit.md J.4, J.6): it returns
//! `Some(i)` only for the canonical encoding of a valid instruction `i`, and
//! `None` only if the word is no valid instruction's canonical encoding.
//!
//! How it works:
//!
//! 1. [`classify`] finds the variant from the word's fixed bits
//!    ([`super::classes`]).
//! 2. `try_*` reads that variant's fields from the word (`cand_*` is the same
//!    read as a spec function), and accepts the result only if
//!    [`valid_exec`] holds and [`encode_instr`] gives the word back.
//!
//! **Soundness is by construction**: an accepted instruction is valid and
//! encodes to the word, by `encode_instr`'s own ensures. **Completeness is
//! the lemma** `lemma_cand_*`: for a valid instruction `i` of the variant,
//! reading the fields of `encode(i)` gives `i` back, so the re-encoding check
//! passes.

#[cfg(verus_only)]
use super::classes::*;
#[cfg(verus_only)]
use super::contract::decode_ensures;
use super::encoder::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---- field readers (spec) ----

/// `DecodeShift`.
pub open spec fn shift_of(v: int) -> ShiftType {
    if v == 0 {
        ShiftType::Lsl
    } else if v == 1 {
        ShiftType::Lsr
    } else if v == 2 {
        ShiftType::Asr
    } else {
        ShiftType::Ror
    }
}

/// The `opc` field of the logical shifted-register forms, read.
pub open spec fn logical_opc_of(v: int) -> LogicalOpc {
    if v == 0 {
        LogicalOpc::And
    } else if v == 1 {
        LogicalOpc::Orr
    } else if v == 2 {
        LogicalOpc::Eor
    } else {
        LogicalOpc::Ands
    }
}

/// The `opc` field of the one-source floating-point forms, read.
pub open spec fn fp_unary_opc_of(v: int) -> FPUnaryOp {
    if v == 0 {
        FPUnaryOp::Mov
    } else if v == 1 {
        FPUnaryOp::Abs
    } else if v == 2 {
        FPUnaryOp::Neg
    } else {
        FPUnaryOp::Sqrt
    }
}

/// A 26-bit field read as a signed number.
pub open spec fn sext26(v: int) -> int {
    if v >= 0x200_0000 {
        v - 0x400_0000
    } else {
        v
    }
}

/// A 19-bit field read as a signed number.
pub open spec fn sext19(v: int) -> int {
    if v >= 0x4_0000 {
        v - 0x8_0000
    } else {
        v
    }
}

// ---- field readers (exec) ----

/// The `sf` bit read.
pub fn width_of(f: u32) -> (r: Width)
    ensures
        r == (if f == 1 {
            Width::W64
        } else {
            Width::W32
        }),
{
    if f == 1 {
        Width::W64
    } else {
        Width::W32
    }
}

/// The `K` bit of the move-wide forms, read.
pub fn move_wide_of(f: u32) -> (r: MoveWideOp)
    ensures
        r == (if f == 1 {
            MoveWideOp::K
        } else {
            MoveWideOp::Z
        }),
{
    if f == 1 {
        MoveWideOp::K
    } else {
        MoveWideOp::Z
    }
}

/// A `shift` field read.
pub fn shift_of_u32(f: u32) -> (r: ShiftType)
    ensures
        r == shift_of(f as int),
{
    if f == 0 {
        ShiftType::Lsl
    } else if f == 1 {
        ShiftType::Lsr
    } else if f == 2 {
        ShiftType::Asr
    } else {
        ShiftType::Ror
    }
}

/// A logical `opc` field read.
pub fn logical_opc_of_u32(f: u32) -> (r: LogicalOpc)
    ensures
        r == logical_opc_of(f as int),
{
    if f == 0 {
        LogicalOpc::And
    } else if f == 1 {
        LogicalOpc::Orr
    } else if f == 2 {
        LogicalOpc::Eor
    } else {
        LogicalOpc::Ands
    }
}

/// A floating-point `opc` field read.
pub fn fp_unary_opc_of_u32(f: u32) -> (r: FPUnaryOp)
    ensures
        r == fp_unary_opc_of(f as int),
{
    if f == 0 {
        FPUnaryOp::Mov
    } else if f == 1 {
        FPUnaryOp::Abs
    } else if f == 2 {
        FPUnaryOp::Neg
    } else {
        FPUnaryOp::Sqrt
    }
}

/// A 26-bit field read as a signed number.
pub fn sext26_u32(f: u32) -> (r: i32)
    requires
        f < 0x400_0000,
    ensures
        r as int == sext26(f as int),
{
    if f >= 0x200_0000 {
        (f as i32).wrapping_sub(0x400_0000)
    } else {
        f as i32
    }
}

/// A 19-bit field read as a signed number.
pub fn sext19_u32(f: u32) -> (r: i32)
    requires
        f < 0x8_0000,
    ensures
        r as int == sext19(f as int),
{
    if f >= 0x4_0000 {
        (f as i32).wrapping_sub(0x8_0000)
    } else {
        f as i32
    }
}

// ---- validity (exec) ----

/// `shifted_reg_ok`, computed.
pub fn shifted_reg_ok_exec(sf: &Width, shift_type: &ShiftType, shift_amount: u8) -> (ok: bool)
    ensures
        ok == shifted_reg_ok(*sf, *shift_type, shift_amount),
{
    let limit: u8 = match sf {
        Width::W32 => 32,
        Width::W64 => 64,
    };
    let lsl = matches!(shift_type, ShiftType::Lsl);
    shift_amount < limit && (shift_amount != 0 || lsl)
}

/// `datasize`, as a `u8`.
pub fn datasize_u8(sf: &Width) -> (r: u8)
    ensures
        r as int == datasize(*sf),
{
    match sf {
        Width::W32 => 32,
        Width::W64 => 64,
    }
}

/// `!(s is Ror)`.
pub fn not_ror(s: &ShiftType) -> (ok: bool)
    ensures
        ok == !(*s is Ror),
{
    !matches!(s, ShiftType::Ror)
}

/// `opcode is Z`.
pub fn is_movz(o: &MoveWideOp) -> (ok: bool)
    ensures
        ok == (*o is Z),
{
    match o {
        MoveWideOp::Z => true,
        MoveWideOp::K => false,
    }
}

/// [`valid_instr`], computed.
pub fn valid_exec(i: &Instr) -> (ok: bool)
    ensures
        ok == valid_instr(*i),
{
    proof {
        lemma_signed_fits();
    }
    match i {
        Instr::AddSubShiftedReg { sf, d, n, m, shift_type, shift_amount, .. } => *d < 32 && *n < 32 && *m < 32 && not_ror(shift_type) && shifted_reg_ok_exec(sf, shift_type, *shift_amount),
        Instr::AddSubImm { d, n, imm12, sh, .. } => *d < 32 && *n < 32 && *imm12 < 4096 && (!*sh || *imm12 != 0),
        Instr::MulAddSub { d, n, m, a, .. } => *d < 32 && *n < 32 && *m < 32 && *a < 32,
        Instr::Div { d, n, m, .. } => *d < 32 && *n < 32 && *m < 32,
        Instr::LogicalShiftedReg { sf, d, n, m, shift_type, shift_amount, .. } => *d < 32 && *n < 32 && *m < 32 && shifted_reg_ok_exec(sf, shift_type, *shift_amount),
        Instr::ShiftVariable { shift_type, d, n, m, .. } => *d < 32 && *n < 32 && *m < 32 && not_ror(shift_type),
        Instr::Bitfield { sf, d, n, immr, imms, .. } => *d < 32 && *n < 32 && *immr < datasize_u8(sf) && *imms < datasize_u8(sf),
        Instr::MoveWide { sf, opcode, d, imm16, hw } => *d < 32 && *hw < datasize_u8(sf) / 16 && (!(is_movz(opcode) && *imm16 == 0) || *hw == 0),
        Instr::CondSelect { d, n, m, cond, .. } => *d < 32 && *n < 32 && *m < 32 && *cond < 14,
        Instr::LoadStoreImm { t, n, imm12, .. } => *t < 32 && *n < 32 && *n != 31 && *imm12 < 4096,
        Instr::LoadStoreReg { t, n, m, .. } => *t < 32 && *n < 32 && *n != 31 && *m < 32,
        Instr::FpLoadStoreImm { t, n, imm12, .. } => *t < 32 && *n < 32 && *n != 31 && *imm12 < 4096,
        Instr::FpLoadStoreReg { t, n, m, .. } => *t < 32 && *n < 32 && *n != 31 && *m < 32,
        Instr::B { imm26 } => -0x200_0000 <= *imm26 && *imm26 < 0x200_0000,
        Instr::BCond { cond, imm19 } => *cond < 14 && -0x4_0000 <= *imm19 && *imm19 < 0x4_0000,
        Instr::CompareBranch { t, imm19, .. } => *t < 32 && -0x4_0000 <= *imm19 && *imm19 < 0x4_0000,
        Instr::Ret => true,
        Instr::FAddSub { d, n, m, .. } => *d < 32 && *n < 32 && *m < 32,
        Instr::FMul { d, n, m } => *d < 32 && *n < 32 && *m < 32,
        Instr::FDiv { d, n, m } => *d < 32 && *n < 32 && *m < 32,
        Instr::FUnary { d, n, .. } => *d < 32 && *n < 32,
        Instr::FCmp { n, m } => *n < 32 && *m < 32,
        Instr::FMovGen { d, n, .. } => *d < 32 && *n < 32,
        Instr::Scvtf { d, n, .. } => *d < 32 && *n < 32,
        Instr::Fcvtzs { d, n, .. } => *d < 32 && *n < 32,
    }
}

// ---- the decoder ----

/// What a `try_*` function for class `k` guarantees about its result `r` on the word `w`:
/// it is only ever a canonical encoding's instruction, and it is `Some(i)` for the
/// valid instruction `i` of class `k` that `w` encodes.
pub open spec fn try_ok(w: u32, r: Option<Instr>, k: int) -> bool {
    &&& match r {
        Some(x) => is_canonical_encoding(w, x),
        None => true,
    }
    &&& forall|i: Instr|
        valid_instr(i) && #[trigger] encode(i) == w as int && class_of(i) == k ==> r == Some(i)
}

/// The decoder is correct if the class it dispatched on is the class of every
/// instruction `w` is the canonical encoding of, and the `try_*` of that class is
/// correct.
pub proof fn lemma_dispatch(w: u32, c: int, r: Option<Instr>)
    requires
        forall|i: Instr| valid_instr(i) && #[trigger] encode(i) == w as int ==> c == class_of(i),
        try_ok(w, r, c),
    ensures
        decode_ensures(w, r),
{
    match r {
        Some(x) => {},
        None => {
            assert forall|i: Instr| !is_canonical_encoding(w, i) by {
                if is_canonical_encoding(w, i) {
                    assert(valid_instr(i) && encode(i) == w as int);
                    assert(c == class_of(i));
                    assert(r == Some(i));
                }
            }
        },
    }
}

/// No instruction's encoding is in no class.
pub proof fn lemma_no_class(w: u32, c: int)
    requires
        forall|i: Instr| valid_instr(i) && #[trigger] encode(i) == w as int ==> c == class_of(i),
        c >= class_count(),
    ensures
        decode_ensures(w, None),
{
    assert forall|i: Instr| !is_canonical_encoding(w, i) by {
        if is_canonical_encoding(w, i) {
            assert(valid_instr(i) && encode(i) == w as int);
            assert(c == class_of(i));
            assert(class_of(i) < class_count());
        }
    }
}

/// The fields of a `AddSubShiftedReg` read from `w` (any word).
pub open spec fn cand_add_sub_shifted_reg(w: u32) -> Instr {
    let x = w as int;
    Instr::AddSubShiftedReg {
        sf: if (x / 0x8000_0000) % 0x2 == 1 {
                Width::W64
            } else {
                Width::W32
            },
        sub_op: (x / 0x4000_0000) % 0x2 == 1,
        setflags: (x / 0x2000_0000) % 0x2 == 1,
        d: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
        m: ((x / 0x1_0000) % 0x20) as u8,
        shift_type: shift_of((x / 0x40_0000) % 0x4),
        shift_amount: ((x / 0x400) % 0x40) as u8,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_add_sub_shifted_reg(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32, t5: u32, t6: u32, t7: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x2,
        t2 < 0x2,
        t3 < 0x4,
        t4 < 0x20,
        t5 < 0x40,
        t6 < 0x20,
        t7 < 0x20,
        w == 0xb00_0000u32 + t0 * 0x4000_0000u32 + t1 * 0x2000_0000u32 + t2 * 0x8000_0000u32 + t3 * 0x40_0000u32 + t4 * 0x1_0000u32 + t5 * 0x400u32 + t6 * 0x20u32 + t7,
    ensures
        (w / 0x4000_0000) % 0x2 == t0,
        (w / 0x2000_0000) % 0x2 == t1,
        (w / 0x8000_0000) % 0x2 == t2,
        (w / 0x40_0000) % 0x4 == t3,
        (w / 0x1_0000) % 0x20 == t4,
        (w / 0x400) % 0x40 == t5,
        (w / 0x20) % 0x20 == t6,
        w % 0x20 == t7,
{
}

/// For a valid `AddSubShiftedReg` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_add_sub_shifted_reg(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is AddSubShiftedReg,
        w as int == encode(i),
    ensures
        cand_add_sub_shifted_reg(w) == i,
{
    lemma_signed_fits();
    if let Instr::AddSubShiftedReg { sf, sub_op, setflags, d, n, m, shift_type, shift_amount } = i {
        let t0 = b(sub_op) as u32;
        let t1 = b(setflags) as u32;
        let t2 = sf_bit(sf) as u32;
        let t3 = shift_field(shift_type) as u32;
        let t4 = (m as int) as u32;
        let t5 = (shift_amount as int) as u32;
        let t6 = (n as int) as u32;
        let t7 = (d as int) as u32;
        assert(b(sub_op) < 0x2);
        assert(b(setflags) < 0x2);
        assert(sf_bit(sf) < 0x2);
        assert(shift_field(shift_type) < 0x4);
        assert((m as int) < 0x20);
        assert((shift_amount as int) < 0x40);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0xb00_0000u32 + t0 * 0x4000_0000u32 + t1 * 0x2000_0000u32 + t2 * 0x8000_0000u32 + t3 * 0x40_0000u32 + t4 * 0x1_0000u32 + t5 * 0x400u32 + t6 * 0x20u32 + t7);
        bvx_add_sub_shifted_reg(w, t0, t1, t2, t3, t4, t5, t6, t7);
        assert(cand_add_sub_shifted_reg(w) == i);
    }
}

/// The fields of a `AddSubImm` read from `w` (any word).
pub open spec fn cand_add_sub_imm(w: u32) -> Instr {
    let x = w as int;
    Instr::AddSubImm {
        sf: if (x / 0x8000_0000) % 0x2 == 1 {
                Width::W64
            } else {
                Width::W32
            },
        sub_op: (x / 0x4000_0000) % 0x2 == 1,
        setflags: (x / 0x2000_0000) % 0x2 == 1,
        d: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
        imm12: ((x / 0x400) % 0x1000) as u16,
        sh: (x / 0x40_0000) % 0x2 == 1,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_add_sub_imm(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32, t5: u32, t6: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x2,
        t2 < 0x2,
        t3 < 0x2,
        t4 < 0x1000,
        t5 < 0x20,
        t6 < 0x20,
        w == 0x1100_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x4000_0000u32 + t2 * 0x2000_0000u32 + t3 * 0x40_0000u32 + t4 * 0x400u32 + t5 * 0x20u32 + t6,
    ensures
        (w / 0x8000_0000) % 0x2 == t0,
        (w / 0x4000_0000) % 0x2 == t1,
        (w / 0x2000_0000) % 0x2 == t2,
        (w / 0x40_0000) % 0x2 == t3,
        (w / 0x400) % 0x1000 == t4,
        (w / 0x20) % 0x20 == t5,
        w % 0x20 == t6,
{
}

/// For a valid `AddSubImm` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_add_sub_imm(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is AddSubImm,
        w as int == encode(i),
    ensures
        cand_add_sub_imm(w) == i,
{
    lemma_signed_fits();
    if let Instr::AddSubImm { sf, sub_op, setflags, d, n, imm12, sh } = i {
        let t0 = sf_bit(sf) as u32;
        let t1 = b(sub_op) as u32;
        let t2 = b(setflags) as u32;
        let t3 = b(sh) as u32;
        let t4 = (imm12 as int) as u32;
        let t5 = (n as int) as u32;
        let t6 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert(b(sub_op) < 0x2);
        assert(b(setflags) < 0x2);
        assert(b(sh) < 0x2);
        assert((imm12 as int) < 0x1000);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1100_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x4000_0000u32 + t2 * 0x2000_0000u32 + t3 * 0x40_0000u32 + t4 * 0x400u32 + t5 * 0x20u32 + t6);
        bvx_add_sub_imm(w, t0, t1, t2, t3, t4, t5, t6);
        assert(cand_add_sub_imm(w) == i);
    }
}

/// The fields of a `MulAddSub` read from `w` (any word).
pub open spec fn cand_mul_add_sub(w: u32) -> Instr {
    let x = w as int;
    Instr::MulAddSub {
        sf: if (x / 0x8000_0000) % 0x2 == 1 {
                Width::W64
            } else {
                Width::W32
            },
        sub_op: (x / 0x8000) % 0x2 == 1,
        d: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
        m: ((x / 0x1_0000) % 0x20) as u8,
        a: ((x / 0x400) % 0x20) as u8,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_mul_add_sub(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32, t5: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x20,
        t2 < 0x2,
        t3 < 0x20,
        t4 < 0x20,
        t5 < 0x20,
        w == 0x1b00_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x1_0000u32 + t2 * 0x8000u32 + t3 * 0x400u32 + t4 * 0x20u32 + t5,
    ensures
        (w / 0x8000_0000) % 0x2 == t0,
        (w / 0x1_0000) % 0x20 == t1,
        (w / 0x8000) % 0x2 == t2,
        (w / 0x400) % 0x20 == t3,
        (w / 0x20) % 0x20 == t4,
        w % 0x20 == t5,
{
}

/// For a valid `MulAddSub` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_mul_add_sub(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is MulAddSub,
        w as int == encode(i),
    ensures
        cand_mul_add_sub(w) == i,
{
    lemma_signed_fits();
    if let Instr::MulAddSub { sf, sub_op, d, n, m, a } = i {
        let t0 = sf_bit(sf) as u32;
        let t1 = (m as int) as u32;
        let t2 = b(sub_op) as u32;
        let t3 = (a as int) as u32;
        let t4 = (n as int) as u32;
        let t5 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert((m as int) < 0x20);
        assert(b(sub_op) < 0x2);
        assert((a as int) < 0x20);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1b00_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x1_0000u32 + t2 * 0x8000u32 + t3 * 0x400u32 + t4 * 0x20u32 + t5);
        bvx_mul_add_sub(w, t0, t1, t2, t3, t4, t5);
        assert(cand_mul_add_sub(w) == i);
    }
}

/// The fields of a `Div` read from `w` (any word).
pub open spec fn cand_div(w: u32) -> Instr {
    let x = w as int;
    Instr::Div {
        sf: if (x / 0x8000_0000) % 0x2 == 1 {
                Width::W64
            } else {
                Width::W32
            },
        is_unsigned: (x / 0x400) % 0x2 == 0,
        d: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
        m: ((x / 0x1_0000) % 0x20) as u8,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_div(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x20,
        t2 < 0x2,
        t3 < 0x20,
        t4 < 0x20,
        w == 0x1ac0_0800u32 + t0 * 0x8000_0000u32 + t1 * 0x1_0000u32 + t2 * 0x400u32 + t3 * 0x20u32 + t4,
    ensures
        (w / 0x8000_0000) % 0x2 == t0,
        (w / 0x1_0000) % 0x20 == t1,
        (w / 0x400) % 0x2 == t2,
        (w / 0x20) % 0x20 == t3,
        w % 0x20 == t4,
{
}

/// For a valid `Div` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_div(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is Div,
        w as int == encode(i),
    ensures
        cand_div(w) == i,
{
    lemma_signed_fits();
    if let Instr::Div { sf, is_unsigned, d, n, m } = i {
        let t0 = sf_bit(sf) as u32;
        let t1 = (m as int) as u32;
        let t2 = b(!is_unsigned) as u32;
        let t3 = (n as int) as u32;
        let t4 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert((m as int) < 0x20);
        assert(b(!is_unsigned) < 0x2);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1ac0_0800u32 + t0 * 0x8000_0000u32 + t1 * 0x1_0000u32 + t2 * 0x400u32 + t3 * 0x20u32 + t4);
        bvx_div(w, t0, t1, t2, t3, t4);
        assert(cand_div(w) == i);
    }
}

/// The fields of a `LogicalShiftedReg` read from `w` (any word).
pub open spec fn cand_logical_shifted_reg(w: u32) -> Instr {
    let x = w as int;
    Instr::LogicalShiftedReg {
        sf: if (x / 0x8000_0000) % 0x2 == 1 {
                Width::W64
            } else {
                Width::W32
            },
        opc: logical_opc_of((x / 0x2000_0000) % 0x4),
        d: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
        m: ((x / 0x1_0000) % 0x20) as u8,
        shift_type: shift_of((x / 0x40_0000) % 0x4),
        shift_amount: ((x / 0x400) % 0x40) as u8,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_logical_shifted_reg(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32, t5: u32, t6: u32)
    by (bit_vector)
    requires
        t0 < 0x4,
        t1 < 0x2,
        t2 < 0x4,
        t3 < 0x20,
        t4 < 0x40,
        t5 < 0x20,
        t6 < 0x20,
        w == 0xa00_0000u32 + t0 * 0x2000_0000u32 + t1 * 0x8000_0000u32 + t2 * 0x40_0000u32 + t3 * 0x1_0000u32 + t4 * 0x400u32 + t5 * 0x20u32 + t6,
    ensures
        (w / 0x2000_0000) % 0x4 == t0,
        (w / 0x8000_0000) % 0x2 == t1,
        (w / 0x40_0000) % 0x4 == t2,
        (w / 0x1_0000) % 0x20 == t3,
        (w / 0x400) % 0x40 == t4,
        (w / 0x20) % 0x20 == t5,
        w % 0x20 == t6,
{
}

/// For a valid `LogicalShiftedReg` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_logical_shifted_reg(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is LogicalShiftedReg,
        w as int == encode(i),
    ensures
        cand_logical_shifted_reg(w) == i,
{
    lemma_signed_fits();
    if let Instr::LogicalShiftedReg { sf, opc, d, n, m, shift_type, shift_amount } = i {
        let t0 = logical_opc_field(opc) as u32;
        let t1 = sf_bit(sf) as u32;
        let t2 = shift_field(shift_type) as u32;
        let t3 = (m as int) as u32;
        let t4 = (shift_amount as int) as u32;
        let t5 = (n as int) as u32;
        let t6 = (d as int) as u32;
        assert(logical_opc_field(opc) < 0x4);
        assert(sf_bit(sf) < 0x2);
        assert(shift_field(shift_type) < 0x4);
        assert((m as int) < 0x20);
        assert((shift_amount as int) < 0x40);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0xa00_0000u32 + t0 * 0x2000_0000u32 + t1 * 0x8000_0000u32 + t2 * 0x40_0000u32 + t3 * 0x1_0000u32 + t4 * 0x400u32 + t5 * 0x20u32 + t6);
        bvx_logical_shifted_reg(w, t0, t1, t2, t3, t4, t5, t6);
        assert(cand_logical_shifted_reg(w) == i);
    }
}

/// The fields of a `ShiftVariable` read from `w` (any word).
pub open spec fn cand_shift_variable(w: u32) -> Instr {
    let x = w as int;
    Instr::ShiftVariable {
        sf: if (x / 0x8000_0000) % 0x2 == 1 {
                Width::W64
            } else {
                Width::W32
            },
        shift_type: shift_of((x / 0x400) % 0x4),
        d: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
        m: ((x / 0x1_0000) % 0x20) as u8,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_shift_variable(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x20,
        t2 < 0x4,
        t3 < 0x20,
        t4 < 0x20,
        w == 0x1ac0_2000u32 + t0 * 0x8000_0000u32 + t1 * 0x1_0000u32 + t2 * 0x400u32 + t3 * 0x20u32 + t4,
    ensures
        (w / 0x8000_0000) % 0x2 == t0,
        (w / 0x1_0000) % 0x20 == t1,
        (w / 0x400) % 0x4 == t2,
        (w / 0x20) % 0x20 == t3,
        w % 0x20 == t4,
{
}

/// For a valid `ShiftVariable` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_shift_variable(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is ShiftVariable,
        w as int == encode(i),
    ensures
        cand_shift_variable(w) == i,
{
    lemma_signed_fits();
    if let Instr::ShiftVariable { sf, shift_type, d, n, m } = i {
        let t0 = sf_bit(sf) as u32;
        let t1 = (m as int) as u32;
        let t2 = shift_field(shift_type) as u32;
        let t3 = (n as int) as u32;
        let t4 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert((m as int) < 0x20);
        assert(shift_field(shift_type) < 0x4);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1ac0_2000u32 + t0 * 0x8000_0000u32 + t1 * 0x1_0000u32 + t2 * 0x400u32 + t3 * 0x20u32 + t4);
        bvx_shift_variable(w, t0, t1, t2, t3, t4);
        assert(cand_shift_variable(w) == i);
    }
}

/// The fields of a `Bitfield` read from `w` (any word).
pub open spec fn cand_bitfield(w: u32) -> Instr {
    let x = w as int;
    Instr::Bitfield {
        sf: if (x / 0x8000_0000) % 0x2 == 1 {
                Width::W64
            } else {
                Width::W32
            },
        signed: (x / 0x4000_0000) % 0x2 == 0,
        d: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
        immr: ((x / 0x1_0000) % 0x40) as u8,
        imms: ((x / 0x400) % 0x40) as u8,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_bitfield(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32, t5: u32, t6: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x2,
        t2 < 0x2,
        t3 < 0x40,
        t4 < 0x40,
        t5 < 0x20,
        t6 < 0x20,
        w == 0x1300_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x4000_0000u32 + t2 * 0x40_0000u32 + t3 * 0x1_0000u32 + t4 * 0x400u32 + t5 * 0x20u32 + t6,
    ensures
        (w / 0x8000_0000) % 0x2 == t0,
        (w / 0x4000_0000) % 0x2 == t1,
        (w / 0x40_0000) % 0x2 == t2,
        (w / 0x1_0000) % 0x40 == t3,
        (w / 0x400) % 0x40 == t4,
        (w / 0x20) % 0x20 == t5,
        w % 0x20 == t6,
{
}

/// For a valid `Bitfield` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_bitfield(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is Bitfield,
        w as int == encode(i),
    ensures
        cand_bitfield(w) == i,
{
    lemma_signed_fits();
    if let Instr::Bitfield { sf, signed, d, n, immr, imms } = i {
        let t0 = sf_bit(sf) as u32;
        let t1 = b(!signed) as u32;
        let t2 = sf_bit(sf) as u32;
        let t3 = (immr as int) as u32;
        let t4 = (imms as int) as u32;
        let t5 = (n as int) as u32;
        let t6 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert(b(!signed) < 0x2);
        assert(sf_bit(sf) < 0x2);
        assert((immr as int) < 0x40);
        assert((imms as int) < 0x40);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1300_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x4000_0000u32 + t2 * 0x40_0000u32 + t3 * 0x1_0000u32 + t4 * 0x400u32 + t5 * 0x20u32 + t6);
        bvx_bitfield(w, t0, t1, t2, t3, t4, t5, t6);
        assert(cand_bitfield(w) == i);
    }
}

/// The fields of a `MoveWide` read from `w` (any word).
pub open spec fn cand_move_wide(w: u32) -> Instr {
    let x = w as int;
    Instr::MoveWide {
        sf: if (x / 0x8000_0000) % 0x2 == 1 {
                Width::W64
            } else {
                Width::W32
            },
        opcode: if (x / 0x2000_0000) % 0x2 == 1 {
                MoveWideOp::K
            } else {
                MoveWideOp::Z
            },
        d: (x % 0x20) as u8,
        imm16: ((x / 0x20) % 0x1_0000) as u16,
        hw: ((x / 0x20_0000) % 0x4) as u8,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_move_wide(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x2,
        t2 < 0x4,
        t3 < 0x1_0000,
        t4 < 0x20,
        w == 0x5280_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x2000_0000u32 + t2 * 0x20_0000u32 + t3 * 0x20u32 + t4,
    ensures
        (w / 0x8000_0000) % 0x2 == t0,
        (w / 0x2000_0000) % 0x2 == t1,
        (w / 0x20_0000) % 0x4 == t2,
        (w / 0x20) % 0x1_0000 == t3,
        w % 0x20 == t4,
{
}

/// For a valid `MoveWide` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_move_wide(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is MoveWide,
        w as int == encode(i),
    ensures
        cand_move_wide(w) == i,
{
    lemma_signed_fits();
    if let Instr::MoveWide { sf, opcode, d, imm16, hw } = i {
        let t0 = sf_bit(sf) as u32;
        let t1 = b(opcode is K) as u32;
        let t2 = (hw as int) as u32;
        let t3 = (imm16 as int) as u32;
        let t4 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert(b(opcode is K) < 0x2);
        assert((hw as int) < 0x4);
        assert((imm16 as int) < 0x1_0000);
        assert((d as int) < 0x20);
        assert(w == 0x5280_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x2000_0000u32 + t2 * 0x20_0000u32 + t3 * 0x20u32 + t4);
        bvx_move_wide(w, t0, t1, t2, t3, t4);
        assert(cand_move_wide(w) == i);
    }
}

/// The fields of a `CondSelect` read from `w` (any word).
pub open spec fn cand_cond_select(w: u32) -> Instr {
    let x = w as int;
    Instr::CondSelect {
        sf: if (x / 0x8000_0000) % 0x2 == 1 {
                Width::W64
            } else {
                Width::W32
            },
        else_inv: (x / 0x4000_0000) % 0x2 == 1,
        else_inc: (x / 0x400) % 0x2 == 1,
        d: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
        m: ((x / 0x1_0000) % 0x20) as u8,
        cond: ((x / 0x1000) % 0x10) as u8,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_cond_select(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32, t5: u32, t6: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x2,
        t2 < 0x20,
        t3 < 0x10,
        t4 < 0x2,
        t5 < 0x20,
        t6 < 0x20,
        w == 0x1a80_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x4000_0000u32 + t2 * 0x1_0000u32 + t3 * 0x1000u32 + t4 * 0x400u32 + t5 * 0x20u32 + t6,
    ensures
        (w / 0x8000_0000) % 0x2 == t0,
        (w / 0x4000_0000) % 0x2 == t1,
        (w / 0x1_0000) % 0x20 == t2,
        (w / 0x1000) % 0x10 == t3,
        (w / 0x400) % 0x2 == t4,
        (w / 0x20) % 0x20 == t5,
        w % 0x20 == t6,
{
}

/// For a valid `CondSelect` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_cond_select(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is CondSelect,
        w as int == encode(i),
    ensures
        cand_cond_select(w) == i,
{
    lemma_signed_fits();
    if let Instr::CondSelect { sf, else_inv, else_inc, d, n, m, cond } = i {
        let t0 = sf_bit(sf) as u32;
        let t1 = b(else_inv) as u32;
        let t2 = (m as int) as u32;
        let t3 = (cond as int) as u32;
        let t4 = b(else_inc) as u32;
        let t5 = (n as int) as u32;
        let t6 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert(b(else_inv) < 0x2);
        assert((m as int) < 0x20);
        assert((cond as int) < 0x10);
        assert(b(else_inc) < 0x2);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1a80_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x4000_0000u32 + t2 * 0x1_0000u32 + t3 * 0x1000u32 + t4 * 0x400u32 + t5 * 0x20u32 + t6);
        bvx_cond_select(w, t0, t1, t2, t3, t4, t5, t6);
        assert(cand_cond_select(w) == i);
    }
}

/// The fields of a `LoadStoreImm` read from `w` (any word).
pub open spec fn cand_load_store_imm(w: u32) -> Instr {
    let x = w as int;
    Instr::LoadStoreImm {
        sf: if (x / 0x4000_0000) % 0x2 == 1 {
                Width::W64
            } else {
                Width::W32
            },
        load: (x / 0x40_0000) % 0x2 == 1,
        t: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
        imm12: ((x / 0x400) % 0x1000) as u16,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_load_store_imm(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x2,
        t2 < 0x1000,
        t3 < 0x20,
        t4 < 0x20,
        w == 0xb900_0000u32 + t0 * 0x4000_0000u32 + t1 * 0x40_0000u32 + t2 * 0x400u32 + t3 * 0x20u32 + t4,
    ensures
        (w / 0x4000_0000) % 0x2 == t0,
        (w / 0x40_0000) % 0x2 == t1,
        (w / 0x400) % 0x1000 == t2,
        (w / 0x20) % 0x20 == t3,
        w % 0x20 == t4,
{
}

/// For a valid `LoadStoreImm` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_load_store_imm(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is LoadStoreImm,
        w as int == encode(i),
    ensures
        cand_load_store_imm(w) == i,
{
    lemma_signed_fits();
    if let Instr::LoadStoreImm { sf, load, t, n, imm12 } = i {
        let t0 = sf_bit(sf) as u32;
        let t1 = b(load) as u32;
        let t2 = (imm12 as int) as u32;
        let t3 = (n as int) as u32;
        let t4 = (t as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert(b(load) < 0x2);
        assert((imm12 as int) < 0x1000);
        assert((n as int) < 0x20);
        assert((t as int) < 0x20);
        assert(w == 0xb900_0000u32 + t0 * 0x4000_0000u32 + t1 * 0x40_0000u32 + t2 * 0x400u32 + t3 * 0x20u32 + t4);
        bvx_load_store_imm(w, t0, t1, t2, t3, t4);
        assert(cand_load_store_imm(w) == i);
    }
}

/// The fields of a `LoadStoreReg` read from `w` (any word).
pub open spec fn cand_load_store_reg(w: u32) -> Instr {
    let x = w as int;
    Instr::LoadStoreReg {
        sf: if (x / 0x4000_0000) % 0x2 == 1 {
                Width::W64
            } else {
                Width::W32
            },
        load: (x / 0x40_0000) % 0x2 == 1,
        t: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
        m: ((x / 0x1_0000) % 0x20) as u8,
        s: (x / 0x1000) % 0x2 == 1,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_load_store_reg(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32, t5: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x2,
        t2 < 0x20,
        t3 < 0x2,
        t4 < 0x20,
        t5 < 0x20,
        w == 0xb820_6800u32 + t0 * 0x4000_0000u32 + t1 * 0x40_0000u32 + t2 * 0x1_0000u32 + t3 * 0x1000u32 + t4 * 0x20u32 + t5,
    ensures
        (w / 0x4000_0000) % 0x2 == t0,
        (w / 0x40_0000) % 0x2 == t1,
        (w / 0x1_0000) % 0x20 == t2,
        (w / 0x1000) % 0x2 == t3,
        (w / 0x20) % 0x20 == t4,
        w % 0x20 == t5,
{
}

/// For a valid `LoadStoreReg` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_load_store_reg(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is LoadStoreReg,
        w as int == encode(i),
    ensures
        cand_load_store_reg(w) == i,
{
    lemma_signed_fits();
    if let Instr::LoadStoreReg { sf, load, t, n, m, s } = i {
        let t0 = sf_bit(sf) as u32;
        let t1 = b(load) as u32;
        let t2 = (m as int) as u32;
        let t3 = b(s) as u32;
        let t4 = (n as int) as u32;
        let t5 = (t as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert(b(load) < 0x2);
        assert((m as int) < 0x20);
        assert(b(s) < 0x2);
        assert((n as int) < 0x20);
        assert((t as int) < 0x20);
        assert(w == 0xb820_6800u32 + t0 * 0x4000_0000u32 + t1 * 0x40_0000u32 + t2 * 0x1_0000u32 + t3 * 0x1000u32 + t4 * 0x20u32 + t5);
        bvx_load_store_reg(w, t0, t1, t2, t3, t4, t5);
        assert(cand_load_store_reg(w) == i);
    }
}

/// The fields of a `FpLoadStoreImm` read from `w` (any word).
pub open spec fn cand_fp_load_store_imm(w: u32) -> Instr {
    let x = w as int;
    Instr::FpLoadStoreImm {
        load: (x / 0x40_0000) % 0x2 == 1,
        t: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
        imm12: ((x / 0x400) % 0x1000) as u16,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_fp_load_store_imm(w: u32, t0: u32, t1: u32, t2: u32, t3: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x1000,
        t2 < 0x20,
        t3 < 0x20,
        w == 0xfd00_0000u32 + t0 * 0x40_0000u32 + t1 * 0x400u32 + t2 * 0x20u32 + t3,
    ensures
        (w / 0x40_0000) % 0x2 == t0,
        (w / 0x400) % 0x1000 == t1,
        (w / 0x20) % 0x20 == t2,
        w % 0x20 == t3,
{
}

/// For a valid `FpLoadStoreImm` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_fp_load_store_imm(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is FpLoadStoreImm,
        w as int == encode(i),
    ensures
        cand_fp_load_store_imm(w) == i,
{
    lemma_signed_fits();
    if let Instr::FpLoadStoreImm { load, t, n, imm12 } = i {
        let t0 = b(load) as u32;
        let t1 = (imm12 as int) as u32;
        let t2 = (n as int) as u32;
        let t3 = (t as int) as u32;
        assert(b(load) < 0x2);
        assert((imm12 as int) < 0x1000);
        assert((n as int) < 0x20);
        assert((t as int) < 0x20);
        assert(w == 0xfd00_0000u32 + t0 * 0x40_0000u32 + t1 * 0x400u32 + t2 * 0x20u32 + t3);
        bvx_fp_load_store_imm(w, t0, t1, t2, t3);
        assert(cand_fp_load_store_imm(w) == i);
    }
}

/// The fields of a `FpLoadStoreReg` read from `w` (any word).
pub open spec fn cand_fp_load_store_reg(w: u32) -> Instr {
    let x = w as int;
    Instr::FpLoadStoreReg {
        load: (x / 0x40_0000) % 0x2 == 1,
        t: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
        m: ((x / 0x1_0000) % 0x20) as u8,
        s: (x / 0x1000) % 0x2 == 1,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_fp_load_store_reg(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x20,
        t2 < 0x2,
        t3 < 0x20,
        t4 < 0x20,
        w == 0xfc20_6800u32 + t0 * 0x40_0000u32 + t1 * 0x1_0000u32 + t2 * 0x1000u32 + t3 * 0x20u32 + t4,
    ensures
        (w / 0x40_0000) % 0x2 == t0,
        (w / 0x1_0000) % 0x20 == t1,
        (w / 0x1000) % 0x2 == t2,
        (w / 0x20) % 0x20 == t3,
        w % 0x20 == t4,
{
}

/// For a valid `FpLoadStoreReg` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_fp_load_store_reg(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is FpLoadStoreReg,
        w as int == encode(i),
    ensures
        cand_fp_load_store_reg(w) == i,
{
    lemma_signed_fits();
    if let Instr::FpLoadStoreReg { load, t, n, m, s } = i {
        let t0 = b(load) as u32;
        let t1 = (m as int) as u32;
        let t2 = b(s) as u32;
        let t3 = (n as int) as u32;
        let t4 = (t as int) as u32;
        assert(b(load) < 0x2);
        assert((m as int) < 0x20);
        assert(b(s) < 0x2);
        assert((n as int) < 0x20);
        assert((t as int) < 0x20);
        assert(w == 0xfc20_6800u32 + t0 * 0x40_0000u32 + t1 * 0x1_0000u32 + t2 * 0x1000u32 + t3 * 0x20u32 + t4);
        bvx_fp_load_store_reg(w, t0, t1, t2, t3, t4);
        assert(cand_fp_load_store_reg(w) == i);
    }
}

/// The fields of a `B` read from `w` (any word).
pub open spec fn cand_b(w: u32) -> Instr {
    let x = w as int;
    Instr::B {
        imm26: sext26(x % 0x400_0000) as i32,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_b(w: u32, t0: u32)
    by (bit_vector)
    requires
        t0 < 0x400_0000,
        w == 0x1400_0000u32 + t0,
    ensures
        w % 0x400_0000 == t0,
{
}

/// For a valid `B` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_b(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is B,
        w as int == encode(i),
    ensures
        cand_b(w) == i,
{
    lemma_signed_fits();
    if let Instr::B { imm26 } = i {
        let t0 = ((imm26 as int) % 0x400_0000) as u32;
        assert(((imm26 as int) % 0x400_0000) < 0x400_0000);
        assert(w == 0x1400_0000u32 + t0);
        bvx_b(w, t0);
        assert(cand_b(w) == i);
    }
}

/// The fields of a `BCond` read from `w` (any word).
pub open spec fn cand_b_cond(w: u32) -> Instr {
    let x = w as int;
    Instr::BCond {
        cond: (x % 0x10) as u8,
        imm19: sext19((x / 0x20) % 0x8_0000) as i32,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_b_cond(w: u32, t0: u32, t1: u32)
    by (bit_vector)
    requires
        t0 < 0x8_0000,
        t1 < 0x10,
        w == 0x5400_0000u32 + t0 * 0x20u32 + t1,
    ensures
        (w / 0x20) % 0x8_0000 == t0,
        w % 0x10 == t1,
{
}

/// For a valid `BCond` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_b_cond(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is BCond,
        w as int == encode(i),
    ensures
        cand_b_cond(w) == i,
{
    lemma_signed_fits();
    if let Instr::BCond { cond, imm19 } = i {
        let t0 = ((imm19 as int) % 0x8_0000) as u32;
        let t1 = (cond as int) as u32;
        assert(((imm19 as int) % 0x8_0000) < 0x8_0000);
        assert((cond as int) < 0x10);
        assert(w == 0x5400_0000u32 + t0 * 0x20u32 + t1);
        bvx_b_cond(w, t0, t1);
        assert(cand_b_cond(w) == i);
    }
}

/// The fields of a `CompareBranch` read from `w` (any word).
pub open spec fn cand_compare_branch(w: u32) -> Instr {
    let x = w as int;
    Instr::CompareBranch {
        sf: if (x / 0x8000_0000) % 0x2 == 1 {
                Width::W64
            } else {
                Width::W32
            },
        iszero: (x / 0x100_0000) % 0x2 == 0,
        t: (x % 0x20) as u8,
        imm19: sext19((x / 0x20) % 0x8_0000) as i32,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_compare_branch(w: u32, t0: u32, t1: u32, t2: u32, t3: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x2,
        t2 < 0x8_0000,
        t3 < 0x20,
        w == 0x3400_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x100_0000u32 + t2 * 0x20u32 + t3,
    ensures
        (w / 0x8000_0000) % 0x2 == t0,
        (w / 0x100_0000) % 0x2 == t1,
        (w / 0x20) % 0x8_0000 == t2,
        w % 0x20 == t3,
{
}

/// For a valid `CompareBranch` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_compare_branch(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is CompareBranch,
        w as int == encode(i),
    ensures
        cand_compare_branch(w) == i,
{
    lemma_signed_fits();
    if let Instr::CompareBranch { sf, iszero, t, imm19 } = i {
        let t0 = sf_bit(sf) as u32;
        let t1 = b(!iszero) as u32;
        let t2 = ((imm19 as int) % 0x8_0000) as u32;
        let t3 = (t as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert(b(!iszero) < 0x2);
        assert(((imm19 as int) % 0x8_0000) < 0x8_0000);
        assert((t as int) < 0x20);
        assert(w == 0x3400_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x100_0000u32 + t2 * 0x20u32 + t3);
        bvx_compare_branch(w, t0, t1, t2, t3);
        assert(cand_compare_branch(w) == i);
    }
}

/// The fields of a `Ret` read from `w` (any word).
pub open spec fn cand_ret(w: u32) -> Instr {
    Instr::Ret
}

/// For a valid `Ret` with encoding `w`, `cand_ret(w)` is it.
pub proof fn lemma_cand_ret(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is Ret,
        w as int == encode(i),
    ensures
        cand_ret(w) == i,
{
}

/// The fields of a `FAddSub` read from `w` (any word).
pub open spec fn cand_f_add_sub(w: u32) -> Instr {
    let x = w as int;
    Instr::FAddSub {
        sub_op: (x / 0x1000) % 0x2 == 1,
        d: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
        m: ((x / 0x1_0000) % 0x20) as u8,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_f_add_sub(w: u32, t0: u32, t1: u32, t2: u32, t3: u32)
    by (bit_vector)
    requires
        t0 < 0x20,
        t1 < 0x2,
        t2 < 0x20,
        t3 < 0x20,
        w == 0x1e60_2800u32 + t0 * 0x1_0000u32 + t1 * 0x1000u32 + t2 * 0x20u32 + t3,
    ensures
        (w / 0x1_0000) % 0x20 == t0,
        (w / 0x1000) % 0x2 == t1,
        (w / 0x20) % 0x20 == t2,
        w % 0x20 == t3,
{
}

/// For a valid `FAddSub` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_f_add_sub(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is FAddSub,
        w as int == encode(i),
    ensures
        cand_f_add_sub(w) == i,
{
    lemma_signed_fits();
    if let Instr::FAddSub { sub_op, d, n, m } = i {
        let t0 = (m as int) as u32;
        let t1 = b(sub_op) as u32;
        let t2 = (n as int) as u32;
        let t3 = (d as int) as u32;
        assert((m as int) < 0x20);
        assert(b(sub_op) < 0x2);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1e60_2800u32 + t0 * 0x1_0000u32 + t1 * 0x1000u32 + t2 * 0x20u32 + t3);
        bvx_f_add_sub(w, t0, t1, t2, t3);
        assert(cand_f_add_sub(w) == i);
    }
}

/// The fields of a `FMul` read from `w` (any word).
pub open spec fn cand_f_mul(w: u32) -> Instr {
    let x = w as int;
    Instr::FMul {
        d: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
        m: ((x / 0x1_0000) % 0x20) as u8,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_f_mul(w: u32, t0: u32, t1: u32, t2: u32)
    by (bit_vector)
    requires
        t0 < 0x20,
        t1 < 0x20,
        t2 < 0x20,
        w == 0x1e60_0800u32 + t0 * 0x1_0000u32 + t1 * 0x20u32 + t2,
    ensures
        (w / 0x1_0000) % 0x20 == t0,
        (w / 0x20) % 0x20 == t1,
        w % 0x20 == t2,
{
}

/// For a valid `FMul` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_f_mul(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is FMul,
        w as int == encode(i),
    ensures
        cand_f_mul(w) == i,
{
    lemma_signed_fits();
    if let Instr::FMul { d, n, m } = i {
        let t0 = (m as int) as u32;
        let t1 = (n as int) as u32;
        let t2 = (d as int) as u32;
        assert((m as int) < 0x20);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1e60_0800u32 + t0 * 0x1_0000u32 + t1 * 0x20u32 + t2);
        bvx_f_mul(w, t0, t1, t2);
        assert(cand_f_mul(w) == i);
    }
}

/// The fields of a `FDiv` read from `w` (any word).
pub open spec fn cand_f_div(w: u32) -> Instr {
    let x = w as int;
    Instr::FDiv {
        d: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
        m: ((x / 0x1_0000) % 0x20) as u8,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_f_div(w: u32, t0: u32, t1: u32, t2: u32)
    by (bit_vector)
    requires
        t0 < 0x20,
        t1 < 0x20,
        t2 < 0x20,
        w == 0x1e60_1800u32 + t0 * 0x1_0000u32 + t1 * 0x20u32 + t2,
    ensures
        (w / 0x1_0000) % 0x20 == t0,
        (w / 0x20) % 0x20 == t1,
        w % 0x20 == t2,
{
}

/// For a valid `FDiv` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_f_div(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is FDiv,
        w as int == encode(i),
    ensures
        cand_f_div(w) == i,
{
    lemma_signed_fits();
    if let Instr::FDiv { d, n, m } = i {
        let t0 = (m as int) as u32;
        let t1 = (n as int) as u32;
        let t2 = (d as int) as u32;
        assert((m as int) < 0x20);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1e60_1800u32 + t0 * 0x1_0000u32 + t1 * 0x20u32 + t2);
        bvx_f_div(w, t0, t1, t2);
        assert(cand_f_div(w) == i);
    }
}

/// The fields of a `FUnary` read from `w` (any word).
pub open spec fn cand_f_unary(w: u32) -> Instr {
    let x = w as int;
    Instr::FUnary {
        fpop: fp_unary_opc_of((x / 0x8000) % 0x4),
        d: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_f_unary(w: u32, t0: u32, t1: u32, t2: u32)
    by (bit_vector)
    requires
        t0 < 0x4,
        t1 < 0x20,
        t2 < 0x20,
        w == 0x1e60_4000u32 + t0 * 0x8000u32 + t1 * 0x20u32 + t2,
    ensures
        (w / 0x8000) % 0x4 == t0,
        (w / 0x20) % 0x20 == t1,
        w % 0x20 == t2,
{
}

/// For a valid `FUnary` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_f_unary(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is FUnary,
        w as int == encode(i),
    ensures
        cand_f_unary(w) == i,
{
    lemma_signed_fits();
    if let Instr::FUnary { fpop, d, n } = i {
        let t0 = fp_unary_opc_field(fpop) as u32;
        let t1 = (n as int) as u32;
        let t2 = (d as int) as u32;
        assert(fp_unary_opc_field(fpop) < 0x4);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1e60_4000u32 + t0 * 0x8000u32 + t1 * 0x20u32 + t2);
        bvx_f_unary(w, t0, t1, t2);
        assert(cand_f_unary(w) == i);
    }
}

/// The fields of a `FCmp` read from `w` (any word).
pub open spec fn cand_f_cmp(w: u32) -> Instr {
    let x = w as int;
    Instr::FCmp {
        n: ((x / 0x20) % 0x20) as u8,
        m: ((x / 0x1_0000) % 0x20) as u8,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_f_cmp(w: u32, t0: u32, t1: u32)
    by (bit_vector)
    requires
        t0 < 0x20,
        t1 < 0x20,
        w == 0x1e60_2000u32 + t0 * 0x1_0000u32 + t1 * 0x20u32,
    ensures
        (w / 0x1_0000) % 0x20 == t0,
        (w / 0x20) % 0x20 == t1,
{
}

/// For a valid `FCmp` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_f_cmp(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is FCmp,
        w as int == encode(i),
    ensures
        cand_f_cmp(w) == i,
{
    lemma_signed_fits();
    if let Instr::FCmp { n, m } = i {
        let t0 = (m as int) as u32;
        let t1 = (n as int) as u32;
        assert((m as int) < 0x20);
        assert((n as int) < 0x20);
        assert(w == 0x1e60_2000u32 + t0 * 0x1_0000u32 + t1 * 0x20u32);
        bvx_f_cmp(w, t0, t1);
        assert(cand_f_cmp(w) == i);
    }
}

/// The fields of a `FMovGen` read from `w` (any word).
pub open spec fn cand_f_mov_gen(w: u32) -> Instr {
    let x = w as int;
    Instr::FMovGen {
        to_fp: (x / 0x1_0000) % 0x2 == 1,
        d: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_f_mov_gen(w: u32, t0: u32, t1: u32, t2: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x20,
        t2 < 0x20,
        w == 0x9e66_0000u32 + t0 * 0x1_0000u32 + t1 * 0x20u32 + t2,
    ensures
        (w / 0x1_0000) % 0x2 == t0,
        (w / 0x20) % 0x20 == t1,
        w % 0x20 == t2,
{
}

/// For a valid `FMovGen` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_f_mov_gen(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is FMovGen,
        w as int == encode(i),
    ensures
        cand_f_mov_gen(w) == i,
{
    lemma_signed_fits();
    if let Instr::FMovGen { to_fp, d, n } = i {
        let t0 = b(to_fp) as u32;
        let t1 = (n as int) as u32;
        let t2 = (d as int) as u32;
        assert(b(to_fp) < 0x2);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x9e66_0000u32 + t0 * 0x1_0000u32 + t1 * 0x20u32 + t2);
        bvx_f_mov_gen(w, t0, t1, t2);
        assert(cand_f_mov_gen(w) == i);
    }
}

/// The fields of a `Scvtf` read from `w` (any word).
pub open spec fn cand_scvtf(w: u32) -> Instr {
    let x = w as int;
    Instr::Scvtf {
        sf: if (x / 0x8000_0000) % 0x2 == 1 {
                Width::W64
            } else {
                Width::W32
            },
        d: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_scvtf(w: u32, t0: u32, t1: u32, t2: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x20,
        t2 < 0x20,
        w == 0x1e62_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x20u32 + t2,
    ensures
        (w / 0x8000_0000) % 0x2 == t0,
        (w / 0x20) % 0x20 == t1,
        w % 0x20 == t2,
{
}

/// For a valid `Scvtf` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_scvtf(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is Scvtf,
        w as int == encode(i),
    ensures
        cand_scvtf(w) == i,
{
    lemma_signed_fits();
    if let Instr::Scvtf { sf, d, n } = i {
        let t0 = sf_bit(sf) as u32;
        let t1 = (n as int) as u32;
        let t2 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1e62_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x20u32 + t2);
        bvx_scvtf(w, t0, t1, t2);
        assert(cand_scvtf(w) == i);
    }
}

/// The fields of a `Fcvtzs` read from `w` (any word).
pub open spec fn cand_fcvtzs(w: u32) -> Instr {
    let x = w as int;
    Instr::Fcvtzs {
        sf: if (x / 0x8000_0000) % 0x2 == 1 {
                Width::W64
            } else {
                Width::W32
            },
        d: (x % 0x20) as u8,
        n: ((x / 0x20) % 0x20) as u8,
    }
}

/// Bit-vector fact: reading the fields back from a word built from them gives them.
proof fn bvx_fcvtzs(w: u32, t0: u32, t1: u32, t2: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x20,
        t2 < 0x20,
        w == 0x1e78_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x20u32 + t2,
    ensures
        (w / 0x8000_0000) % 0x2 == t0,
        (w / 0x20) % 0x20 == t1,
        w % 0x20 == t2,
{
}

/// For a valid `Fcvtzs` with encoding `w`, the fields read from `w` are its fields.
pub proof fn lemma_cand_fcvtzs(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is Fcvtzs,
        w as int == encode(i),
    ensures
        cand_fcvtzs(w) == i,
{
    lemma_signed_fits();
    if let Instr::Fcvtzs { sf, d, n } = i {
        let t0 = sf_bit(sf) as u32;
        let t1 = (n as int) as u32;
        let t2 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1e78_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x20u32 + t2);
        bvx_fcvtzs(w, t0, t1, t2);
        assert(cand_fcvtzs(w) == i);
    }
}

/// The instruction of class `k` read from `w`.
pub open spec fn cand_of_class(w: u32, k: int) -> Instr {
    if k == 0 {
        cand_add_sub_shifted_reg(w)
    } else
    if k == 1 {
        cand_add_sub_imm(w)
    } else
    if k == 2 {
        cand_mul_add_sub(w)
    } else
    if k == 3 {
        cand_div(w)
    } else
    if k == 4 {
        cand_logical_shifted_reg(w)
    } else
    if k == 5 {
        cand_shift_variable(w)
    } else
    if k == 6 {
        cand_bitfield(w)
    } else
    if k == 7 {
        cand_move_wide(w)
    } else
    if k == 8 {
        cand_cond_select(w)
    } else
    if k == 9 {
        cand_load_store_imm(w)
    } else
    if k == 10 {
        cand_load_store_reg(w)
    } else
    if k == 11 {
        cand_fp_load_store_imm(w)
    } else
    if k == 12 {
        cand_fp_load_store_reg(w)
    } else
    if k == 13 {
        cand_b(w)
    } else
    if k == 14 {
        cand_b_cond(w)
    } else
    if k == 15 {
        cand_compare_branch(w)
    } else
    if k == 16 {
        cand_ret(w)
    } else
    if k == 17 {
        cand_f_add_sub(w)
    } else
    if k == 18 {
        cand_f_mul(w)
    } else
    if k == 19 {
        cand_f_div(w)
    } else
    if k == 20 {
        cand_f_unary(w)
    } else
    if k == 21 {
        cand_f_cmp(w)
    } else
    if k == 22 {
        cand_f_mov_gen(w)
    } else
    if k == 23 {
        cand_scvtf(w)
    } else
    if k == 24 {
        cand_fcvtzs(w)
    } else {
        Instr::Ret
    }
}

/// For a valid instruction, the instruction of its class read from its encoding is itself.
pub proof fn lemma_cand_class(w: u32, i: Instr)
    requires
        valid_instr(i),
        w as int == encode(i),
    ensures
        cand_of_class(w, class_of(i)) == i,
{
    match i {
        Instr::AddSubShiftedReg { .. } => lemma_cand_add_sub_shifted_reg(w, i),
        Instr::AddSubImm { .. } => lemma_cand_add_sub_imm(w, i),
        Instr::MulAddSub { .. } => lemma_cand_mul_add_sub(w, i),
        Instr::Div { .. } => lemma_cand_div(w, i),
        Instr::LogicalShiftedReg { .. } => lemma_cand_logical_shifted_reg(w, i),
        Instr::ShiftVariable { .. } => lemma_cand_shift_variable(w, i),
        Instr::Bitfield { .. } => lemma_cand_bitfield(w, i),
        Instr::MoveWide { .. } => lemma_cand_move_wide(w, i),
        Instr::CondSelect { .. } => lemma_cand_cond_select(w, i),
        Instr::LoadStoreImm { .. } => lemma_cand_load_store_imm(w, i),
        Instr::LoadStoreReg { .. } => lemma_cand_load_store_reg(w, i),
        Instr::FpLoadStoreImm { .. } => lemma_cand_fp_load_store_imm(w, i),
        Instr::FpLoadStoreReg { .. } => lemma_cand_fp_load_store_reg(w, i),
        Instr::B { .. } => lemma_cand_b(w, i),
        Instr::BCond { .. } => lemma_cand_b_cond(w, i),
        Instr::CompareBranch { .. } => lemma_cand_compare_branch(w, i),
        Instr::Ret => lemma_cand_ret(w, i),
        Instr::FAddSub { .. } => lemma_cand_f_add_sub(w, i),
        Instr::FMul { .. } => lemma_cand_f_mul(w, i),
        Instr::FDiv { .. } => lemma_cand_f_div(w, i),
        Instr::FUnary { .. } => lemma_cand_f_unary(w, i),
        Instr::FCmp { .. } => lemma_cand_f_cmp(w, i),
        Instr::FMovGen { .. } => lemma_cand_f_mov_gen(w, i),
        Instr::Scvtf { .. } => lemma_cand_scvtf(w, i),
        Instr::Fcvtzs { .. } => lemma_cand_fcvtzs(w, i),
    }
}

/// The class of `w` by its fixed bits ([`chain_class`]), which for the canonical
/// encoding of a valid instruction is the instruction's own class.
pub fn classify(w: u32) -> (c: u8)
    ensures
        c as int == chain_class(w),
        forall|i: Instr| valid_instr(i) && encode(i) == w as int ==> c as int == class_of(i),
{
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int implies chain_class(w) == class_of(i) by {
            lemma_class_exact(w, i);
        }
    }
    if w & 0x1f20_0000 == 0xb00_0000 {
        0
    } else     if w & 0x1f80_0000 == 0x1100_0000 {
        1
    } else     if w & 0x7fe0_0000 == 0x1b00_0000 {
        2
    } else     if w & 0x7fe0_f800 == 0x1ac0_0800 {
        3
    } else     if w & 0x1f20_0000 == 0xa00_0000 {
        4
    } else     if w & 0x7fe0_f000 == 0x1ac0_2000 {
        5
    } else     if w & 0x3f80_0000 == 0x1300_0000 {
        6
    } else     if w & 0x5f80_0000 == 0x5280_0000 {
        7
    } else     if w & 0x3fe0_0800 == 0x1a80_0000 {
        8
    } else     if w & 0xbf80_0000 == 0xb900_0000 {
        9
    } else     if w & 0xbfa0_ec00 == 0xb820_6800 {
        10
    } else     if w & 0xff80_0000 == 0xfd00_0000 {
        11
    } else     if w & 0xffa0_ec00 == 0xfc20_6800 {
        12
    } else     if w & 0xfc00_0000 == 0x1400_0000 {
        13
    } else     if w & 0xff00_0010 == 0x5400_0000 {
        14
    } else     if w & 0x7e00_0000 == 0x3400_0000 {
        15
    } else     if w == 0xd65f_03c0 {
        16
    } else     if w & 0xffe0_ec00 == 0x1e60_2800 {
        17
    } else     if w & 0xffe0_fc00 == 0x1e60_0800 {
        18
    } else     if w & 0xffe0_fc00 == 0x1e60_1800 {
        19
    } else     if w & 0xfffe_7c00 == 0x1e60_4000 {
        20
    } else     if w & 0xffe0_fc1f == 0x1e60_2000 {
        21
    } else     if w & 0xfffe_fc00 == 0x9e66_0000 {
        22
    } else     if w & 0x7fff_fc00 == 0x1e62_0000 {
        23
    } else     if w & 0x7fff_fc00 == 0x1e78_0000 {
        24
    } else {
        25
    }
}

/// Reads the fields of a `AddSubShiftedReg` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_add_sub_shifted_reg(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 0),
{
    let cand = Instr::AddSubShiftedReg {
        sf: width_of((w / 0x8000_0000) % 0x2),
        sub_op: (w / 0x4000_0000) % 0x2 == 1,
        setflags: (w / 0x2000_0000) % 0x2 == 1,
        d: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
        m: ((w / 0x1_0000) % 0x20) as u8,
        shift_type: shift_of_u32((w / 0x40_0000) % 0x4),
        shift_amount: ((w / 0x400) % 0x40) as u8,
    };
    proof {
        assert(cand == cand_add_sub_shifted_reg(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 0 implies cand == i by {
            lemma_cand_add_sub_shifted_reg(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `AddSubImm` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_add_sub_imm(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 1),
{
    let cand = Instr::AddSubImm {
        sf: width_of((w / 0x8000_0000) % 0x2),
        sub_op: (w / 0x4000_0000) % 0x2 == 1,
        setflags: (w / 0x2000_0000) % 0x2 == 1,
        d: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
        imm12: ((w / 0x400) % 0x1000) as u16,
        sh: (w / 0x40_0000) % 0x2 == 1,
    };
    proof {
        assert(cand == cand_add_sub_imm(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 1 implies cand == i by {
            lemma_cand_add_sub_imm(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `MulAddSub` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_mul_add_sub(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 2),
{
    let cand = Instr::MulAddSub {
        sf: width_of((w / 0x8000_0000) % 0x2),
        sub_op: (w / 0x8000) % 0x2 == 1,
        d: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
        m: ((w / 0x1_0000) % 0x20) as u8,
        a: ((w / 0x400) % 0x20) as u8,
    };
    proof {
        assert(cand == cand_mul_add_sub(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 2 implies cand == i by {
            lemma_cand_mul_add_sub(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `Div` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_div(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 3),
{
    let cand = Instr::Div {
        sf: width_of((w / 0x8000_0000) % 0x2),
        is_unsigned: (w / 0x400) % 0x2 != 1,
        d: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
        m: ((w / 0x1_0000) % 0x20) as u8,
    };
    proof {
        assert(cand == cand_div(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 3 implies cand == i by {
            lemma_cand_div(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `LogicalShiftedReg` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_logical_shifted_reg(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 4),
{
    let cand = Instr::LogicalShiftedReg {
        sf: width_of((w / 0x8000_0000) % 0x2),
        opc: logical_opc_of_u32((w / 0x2000_0000) % 0x4),
        d: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
        m: ((w / 0x1_0000) % 0x20) as u8,
        shift_type: shift_of_u32((w / 0x40_0000) % 0x4),
        shift_amount: ((w / 0x400) % 0x40) as u8,
    };
    proof {
        assert(cand == cand_logical_shifted_reg(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 4 implies cand == i by {
            lemma_cand_logical_shifted_reg(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `ShiftVariable` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_shift_variable(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 5),
{
    let cand = Instr::ShiftVariable {
        sf: width_of((w / 0x8000_0000) % 0x2),
        shift_type: shift_of_u32((w / 0x400) % 0x4),
        d: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
        m: ((w / 0x1_0000) % 0x20) as u8,
    };
    proof {
        assert(cand == cand_shift_variable(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 5 implies cand == i by {
            lemma_cand_shift_variable(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `Bitfield` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_bitfield(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 6),
{
    let cand = Instr::Bitfield {
        sf: width_of((w / 0x8000_0000) % 0x2),
        signed: (w / 0x4000_0000) % 0x2 != 1,
        d: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
        immr: ((w / 0x1_0000) % 0x40) as u8,
        imms: ((w / 0x400) % 0x40) as u8,
    };
    proof {
        assert(cand == cand_bitfield(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 6 implies cand == i by {
            lemma_cand_bitfield(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `MoveWide` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_move_wide(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 7),
{
    let cand = Instr::MoveWide {
        sf: width_of((w / 0x8000_0000) % 0x2),
        opcode: move_wide_of((w / 0x2000_0000) % 0x2),
        d: (w % 0x20) as u8,
        imm16: ((w / 0x20) % 0x1_0000) as u16,
        hw: ((w / 0x20_0000) % 0x4) as u8,
    };
    proof {
        assert(cand == cand_move_wide(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 7 implies cand == i by {
            lemma_cand_move_wide(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `CondSelect` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_cond_select(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 8),
{
    let cand = Instr::CondSelect {
        sf: width_of((w / 0x8000_0000) % 0x2),
        else_inv: (w / 0x4000_0000) % 0x2 == 1,
        else_inc: (w / 0x400) % 0x2 == 1,
        d: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
        m: ((w / 0x1_0000) % 0x20) as u8,
        cond: ((w / 0x1000) % 0x10) as u8,
    };
    proof {
        assert(cand == cand_cond_select(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 8 implies cand == i by {
            lemma_cand_cond_select(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `LoadStoreImm` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_load_store_imm(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 9),
{
    let cand = Instr::LoadStoreImm {
        sf: width_of((w / 0x4000_0000) % 0x2),
        load: (w / 0x40_0000) % 0x2 == 1,
        t: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
        imm12: ((w / 0x400) % 0x1000) as u16,
    };
    proof {
        assert(cand == cand_load_store_imm(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 9 implies cand == i by {
            lemma_cand_load_store_imm(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `LoadStoreReg` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_load_store_reg(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 10),
{
    let cand = Instr::LoadStoreReg {
        sf: width_of((w / 0x4000_0000) % 0x2),
        load: (w / 0x40_0000) % 0x2 == 1,
        t: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
        m: ((w / 0x1_0000) % 0x20) as u8,
        s: (w / 0x1000) % 0x2 == 1,
    };
    proof {
        assert(cand == cand_load_store_reg(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 10 implies cand == i by {
            lemma_cand_load_store_reg(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `FpLoadStoreImm` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_fp_load_store_imm(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 11),
{
    let cand = Instr::FpLoadStoreImm {
        load: (w / 0x40_0000) % 0x2 == 1,
        t: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
        imm12: ((w / 0x400) % 0x1000) as u16,
    };
    proof {
        assert(cand == cand_fp_load_store_imm(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 11 implies cand == i by {
            lemma_cand_fp_load_store_imm(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `FpLoadStoreReg` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_fp_load_store_reg(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 12),
{
    let cand = Instr::FpLoadStoreReg {
        load: (w / 0x40_0000) % 0x2 == 1,
        t: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
        m: ((w / 0x1_0000) % 0x20) as u8,
        s: (w / 0x1000) % 0x2 == 1,
    };
    proof {
        assert(cand == cand_fp_load_store_reg(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 12 implies cand == i by {
            lemma_cand_fp_load_store_reg(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `B` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_b(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 13),
{
    let cand = Instr::B {
        imm26: sext26_u32(w % 0x400_0000),
    };
    proof {
        assert(cand == cand_b(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 13 implies cand == i by {
            lemma_cand_b(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `BCond` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_b_cond(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 14),
{
    let cand = Instr::BCond {
        cond: (w % 0x10) as u8,
        imm19: sext19_u32((w / 0x20) % 0x8_0000),
    };
    proof {
        assert(cand == cand_b_cond(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 14 implies cand == i by {
            lemma_cand_b_cond(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `CompareBranch` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_compare_branch(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 15),
{
    let cand = Instr::CompareBranch {
        sf: width_of((w / 0x8000_0000) % 0x2),
        iszero: (w / 0x100_0000) % 0x2 != 1,
        t: (w % 0x20) as u8,
        imm19: sext19_u32((w / 0x20) % 0x8_0000),
    };
    proof {
        assert(cand == cand_compare_branch(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 15 implies cand == i by {
            lemma_cand_compare_branch(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `Ret` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_ret(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 16),
{
    let cand = Instr::Ret;
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 16 implies cand == i by {
            lemma_cand_ret(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `FAddSub` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_f_add_sub(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 17),
{
    let cand = Instr::FAddSub {
        sub_op: (w / 0x1000) % 0x2 == 1,
        d: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
        m: ((w / 0x1_0000) % 0x20) as u8,
    };
    proof {
        assert(cand == cand_f_add_sub(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 17 implies cand == i by {
            lemma_cand_f_add_sub(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `FMul` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_f_mul(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 18),
{
    let cand = Instr::FMul {
        d: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
        m: ((w / 0x1_0000) % 0x20) as u8,
    };
    proof {
        assert(cand == cand_f_mul(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 18 implies cand == i by {
            lemma_cand_f_mul(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `FDiv` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_f_div(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 19),
{
    let cand = Instr::FDiv {
        d: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
        m: ((w / 0x1_0000) % 0x20) as u8,
    };
    proof {
        assert(cand == cand_f_div(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 19 implies cand == i by {
            lemma_cand_f_div(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `FUnary` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_f_unary(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 20),
{
    let cand = Instr::FUnary {
        fpop: fp_unary_opc_of_u32((w / 0x8000) % 0x4),
        d: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
    };
    proof {
        assert(cand == cand_f_unary(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 20 implies cand == i by {
            lemma_cand_f_unary(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `FCmp` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_f_cmp(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 21),
{
    let cand = Instr::FCmp {
        n: ((w / 0x20) % 0x20) as u8,
        m: ((w / 0x1_0000) % 0x20) as u8,
    };
    proof {
        assert(cand == cand_f_cmp(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 21 implies cand == i by {
            lemma_cand_f_cmp(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `FMovGen` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_f_mov_gen(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 22),
{
    let cand = Instr::FMovGen {
        to_fp: (w / 0x1_0000) % 0x2 == 1,
        d: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
    };
    proof {
        assert(cand == cand_f_mov_gen(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 22 implies cand == i by {
            lemma_cand_f_mov_gen(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `Scvtf` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_scvtf(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 23),
{
    let cand = Instr::Scvtf {
        sf: width_of((w / 0x8000_0000) % 0x2),
        d: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
    };
    proof {
        assert(cand == cand_scvtf(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 23 implies cand == i by {
            lemma_cand_scvtf(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Reads the fields of a `Fcvtzs` from `w` and accepts them if they are a valid
/// instruction whose canonical encoding is `w`.
pub fn try_fcvtzs(w: u32) -> (r: Option<Instr>)
    ensures
        try_ok(w, r, 24),
{
    let cand = Instr::Fcvtzs {
        sf: width_of((w / 0x8000_0000) % 0x2),
        d: (w % 0x20) as u8,
        n: ((w / 0x20) % 0x20) as u8,
    };
    proof {
        assert(cand == cand_fcvtzs(w));
    }
    proof {
        assert forall|i: Instr| valid_instr(i) && encode(i) == w as int && class_of(i) == 24 implies cand == i by {
            lemma_cand_fcvtzs(w, i);
        }
    }
    if valid_exec(&cand) {
        let e = encode_instr(&cand);
        if e == w {
            Some(cand)
        } else {
            None
        }
    } else {
        None
    }
}

/// Decodes one instruction word: the instruction, or `None` if the word is
/// not the canonical encoding of an instruction of the subset.
///
/// A64 words have a fixed size and no prefixes, so the decoder takes one word;
/// the caller makes it from four bytes with `u32::from_le_bytes`.
pub fn decode_instr(w: u32) -> (r: Option<Instr>)
    ensures
        decode_ensures(w, r),
{
    let c = classify(w);    if c == 0 {
        let r = try_add_sub_shifted_reg(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 1 {
        let r = try_add_sub_imm(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 2 {
        let r = try_mul_add_sub(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 3 {
        let r = try_div(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 4 {
        let r = try_logical_shifted_reg(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 5 {
        let r = try_shift_variable(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 6 {
        let r = try_bitfield(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 7 {
        let r = try_move_wide(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 8 {
        let r = try_cond_select(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 9 {
        let r = try_load_store_imm(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 10 {
        let r = try_load_store_reg(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 11 {
        let r = try_fp_load_store_imm(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 12 {
        let r = try_fp_load_store_reg(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 13 {
        let r = try_b(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 14 {
        let r = try_b_cond(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 15 {
        let r = try_compare_branch(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 16 {
        let r = try_ret(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 17 {
        let r = try_f_add_sub(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 18 {
        let r = try_f_mul(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 19 {
        let r = try_f_div(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 20 {
        let r = try_f_unary(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 21 {
        let r = try_f_cmp(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 22 {
        let r = try_f_mov_gen(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 23 {
        let r = try_scvtf(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else     if c == 24 {
        let r = try_fcvtzs(w);
        proof {
            lemma_dispatch(w, c as int, r);
        }
        r
    } else {
        proof {
            lemma_no_class(w, c as int);
        }
        None
    }
}

} // verus!
