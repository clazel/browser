//! Facts proven about the spec (docs/SPEC-STYLE.md): evidence that the
//! transcription is coherent, not part of what the implementation must meet.
//!
//! - [`lemma_decode_enc_int32`], [`lemma_decode_enc_ref`],
//!   [`lemma_decode_enc_double`] and [`lemma_encode_decode`]: the NaN-boxing
//!   round-trips, so a value has exactly one encoding and no two kinds of
//!   value share a bit pattern.
//! - [`lemma_core_always_fast`] and [`lemma_handler_never_fast`]: the op
//!   classes mean what [`crate::ops`] says, which is what lets the JIT map
//!   handler ops to exits and core ops to straight-line code.
//! - [`lemma_core_step_wf`]: a core op keeps the machine well-formed, so the
//!   region window, the callee and `pc` stay in bounds without a check.
//! - [`lemma_less_than_asymmetric`] and [`lemma_number_equal_key`]: two
//!   properties the standard implies of Number comparison, which the integer
//!   ordering key of `f64_key` must satisfy.
//! - [`lemma_examples`]: the value of a few conversions, evaluated.


#[allow(unused_imports)]
use super::spec::*;

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// NaN-boxing
// ---------------------------------------------------------------------

proof fn bv_int32(i: i32)
    ensures
        ((0xFFF9_0000_0000_0000u64 | (((i as u32) as u64) & 0xFFFF_FFFF)) >> 48) == 0xFFF9u64,
        (((0xFFF9_0000_0000_0000u64 | (((i as u32) as u64) & 0xFFFF_FFFF)) >> 32) & 0xFFFF) == 0u64,
        (((0xFFF9_0000_0000_0000u64 | (((i as u32) as u64) & 0xFFFF_FFFF)) & 0xFFFF_FFFF) as u32) as i32 == i,
{
    assert(((0xFFF9_0000_0000_0000u64 | (((i as u32) as u64) & 0xFFFF_FFFF)) >> 48) == 0xFFF9u64) by (bit_vector);
    assert((((0xFFF9_0000_0000_0000u64 | (((i as u32) as u64) & 0xFFFF_FFFF)) >> 32) & 0xFFFF) == 0u64) by (bit_vector);
    assert((((0xFFF9_0000_0000_0000u64 | (((i as u32) as u64) & 0xFFFF_FFFF)) & 0xFFFF_FFFF) as u32) as i32 == i) by (bit_vector);
}

/// An int32 decodes back to itself.
pub proof fn lemma_decode_enc_int32(i: i32)
    ensures
        decode(enc_int32(i)) == Val::Int32(i),
{
    bv_int32(i);
}

proof fn bv_ref(index: u32, generation: u16)
    ensures
        ((0xFFFB_0000_0000_0000u64 | ((generation as u64) << 32) | (index as u64)) >> 48) == 0xFFFBu64,
        (((0xFFFB_0000_0000_0000u64 | ((generation as u64) << 32) | (index as u64)) & 0xFFFF_FFFF) as u32) == index,
        (((((0xFFFB_0000_0000_0000u64 | ((generation as u64) << 32) | (index as u64)) >> 32) & 0xFFFF) as u16)) == generation,
{
    assert(((0xFFFB_0000_0000_0000u64 | ((generation as u64) << 32) | (index as u64)) >> 48) == 0xFFFBu64) by (bit_vector);
    assert((((0xFFFB_0000_0000_0000u64 | ((generation as u64) << 32) | (index as u64)) & 0xFFFF_FFFF) as u32) == index) by (bit_vector);
    assert((((((0xFFFB_0000_0000_0000u64 | ((generation as u64) << 32) | (index as u64)) >> 32) & 0xFFFF) as u16)) == generation) by (bit_vector);
}

/// A heap reference decodes back to its index and generation.
pub proof fn lemma_decode_enc_ref(index: u32, generation: u16)
    ensures
        decode(enc_ref(index, generation)) == Val::Ref(index, generation),
{
    bv_ref(index, generation);
}

proof fn bv_double(b: u64)
    ensures
        !(((b >> 52) & 0x7FF) == 0x7FF && (b & 0xF_FFFF_FFFF_FFFF) != 0) ==> (b >> 48) < 0xFFF9u64,
{
    assert(!(((b >> 52) & 0x7FF) == 0x7FF && (b & 0xF_FFFF_FFFF_FFFF) != 0) ==> (b >> 48) < 0xFFF9u64) by (bit_vector);
}

proof fn bv_canon_nan()
    ensures
        (0x7FF8_0000_0000_0000u64 >> 48) < 0xFFF9u64,
        ((0x7FF8_0000_0000_0000u64 >> 52) & 0x7FF) == 0x7FFu64,
        (0x7FF8_0000_0000_0000u64 & 0xF_FFFF_FFFF_FFFFu64) != 0u64,
{
    assert((0x7FF8_0000_0000_0000u64 >> 48) < 0xFFF9u64) by (bit_vector);
    assert(((0x7FF8_0000_0000_0000u64 >> 52) & 0x7FF) == 0x7FFu64) by (bit_vector);
    assert((0x7FF8_0000_0000_0000u64 & 0xF_FFFF_FFFF_FFFFu64) != 0u64) by (bit_vector);
}

/// The encoding of a double is a double value, and a double value decodes to
/// itself.
pub proof fn lemma_decode_enc_double(bits: u64)
    ensures
        is_double(enc_double(bits)),
        decode(enc_double(bits)) == Val::Double(enc_double(bits)),
{
    bv_double(bits);
    bv_canon_nan();
}

proof fn bv_special(v: u64, k: u64)
    requires
        (v >> 48) == 0xFFFAu64,
        (v & 0xFFFF_FFFF_FFFF) == k,
    ensures
        v == 0xFFFA_0000_0000_0000u64 + k,
{
    assert(((v >> 48) == 0xFFFAu64 && (v & 0xFFFF_FFFF_FFFF) == k) ==> v == 0xFFFA_0000_0000_0000u64 + k) by (bit_vector);
}

proof fn bv_int32_inv(v: u64)
    requires
        (v >> 48) == 0xFFF9u64,
        ((v >> 32) & 0xFFFF) == 0u64,
    ensures
        (0xFFF9_0000_0000_0000u64 | ((((v & 0xFFFF_FFFF) as u32) as i32 as u32) as u64) & 0xFFFF_FFFF) == v,
{
    assert(((v >> 48) == 0xFFF9u64 && ((v >> 32) & 0xFFFF) == 0u64)
        ==> (0xFFF9_0000_0000_0000u64 | ((((v & 0xFFFF_FFFF) as u32) as i32 as u32) as u64) & 0xFFFF_FFFF) == v) by (bit_vector);
}

proof fn bv_ref_inv(v: u64)
    requires
        (v >> 48) == 0xFFFBu64,
    ensures
        (0xFFFB_0000_0000_0000u64 | ((((v >> 32) & 0xFFFF) as u16 as u64) << 32) | ((v & 0xFFFF_FFFF) as u32 as u64)) == v,
{
    assert((v >> 48) == 0xFFFBu64
        ==> (0xFFFB_0000_0000_0000u64 | ((((v >> 32) & 0xFFFF) as u16 as u64) << 32) | ((v & 0xFFFF_FFFF) as u32 as u64)) == v) by (bit_vector);
}

proof fn bv_raw_inv(v: u64)
    requires
        (v >> 48) == 0xFFFCu64,
    ensures
        (0xFFFC_0000_0000_0000u64 | ((v & 0xFFFF_FFFF_FFFF) & 0xFFFF_FFFF_FFFF)) == v,
{
    assert((v >> 48) == 0xFFFCu64
        ==> (0xFFFC_0000_0000_0000u64 | ((v & 0xFFFF_FFFF_FFFF) & 0xFFFF_FFFF_FFFF)) == v) by (bit_vector);
}

/// Every value re-encodes to the same bits: no two bit patterns decode to
/// one value.
pub proof fn lemma_encode_decode(v: u64)
    requires
        value_wf(v),
    ensures
        encode(decode(v)) == v,
{
    let tag = v >> 48;
    if tag < 0xFFF9 {
        assert(is_double(v));
        if is_nan(v) {
            assert(v == CANON_NAN);
        }
    } else if tag == 0xFFF9 {
        bv_int32_inv(v);
    } else if tag == 0xFFFA {
        let k = v & 0xFFFF_FFFF_FFFF;
        bv_special(v, k);
    } else if tag == 0xFFFB {
        bv_ref_inv(v);
    } else if tag == 0xFFFC {
        bv_raw_inv(v);
    }
}

/// The five specials are values and decode as named.
pub proof fn lemma_specials()
    ensures
        decode(UNDEFINED) == Val::Undefined,
        decode(NULL) == Val::Null,
        decode(FALSE) == Val::Bool(false),
        decode(TRUE) == Val::Bool(true),
        decode(HOLE) == Val::Hole,
        decode(CANON_NAN) == Val::Double(CANON_NAN),
{
    assert((UNDEFINED >> 48) == 0xFFFAu64) by (bit_vector);
    assert((NULL >> 48) == 0xFFFAu64) by (bit_vector);
    assert((FALSE >> 48) == 0xFFFAu64) by (bit_vector);
    assert((TRUE >> 48) == 0xFFFAu64) by (bit_vector);
    assert((HOLE >> 48) == 0xFFFAu64) by (bit_vector);
    assert((UNDEFINED & 0xFFFF_FFFF_FFFF) == 0u64) by (bit_vector);
    assert((NULL & 0xFFFF_FFFF_FFFF) == 1u64) by (bit_vector);
    assert((FALSE & 0xFFFF_FFFF_FFFF) == 2u64) by (bit_vector);
    assert((TRUE & 0xFFFF_FFFF_FFFF) == 3u64) by (bit_vector);
    assert((HOLE & 0xFFFF_FFFF_FFFF) == 4u64) by (bit_vector);
    lemma_decode_enc_double(CANON_NAN);
    assert(enc_double(CANON_NAN) == CANON_NAN);
}

// ---------------------------------------------------------------------
// Op classes
// ---------------------------------------------------------------------

/// A core op takes its fast path in every state: it never calls a handler.
pub proof fn lemma_core_always_fast(s: State, op: Op)
    requires
        op_class(op) is Core,
    ensures
        fast_path(s, op),
        step(s, op) == fast_step(s, op),
{
}

/// A handler op never takes a fast path: it always calls its handler.
pub proof fn lemma_handler_never_fast(s: State, op: Op)
    requires
        op_class(op) is Handler,
    ensures
        !fast_path(s, op),
        step(s, op) == handler(op_handler(op), s, op),
{
}

// ---------------------------------------------------------------------
// Core ops keep the machine well-formed
// ---------------------------------------------------------------------

/// Setting a register of the current frame keeps the machine well-formed
/// (the callee slot is below every register, so the frame's code is the same).
proof fn lemma_set_reg_wf(s: State, r: nat, v: u64)
    requires
        state_wf(s),
        reg_ok(cur_code(s), r),
    ensures
        state_wf(set_reg(s, r, v)),
        set_reg(s, r, v).region.len() == s.region.len(),
        set_reg(s, r, v).fp == s.fp,
        set_reg(s, r, v).pc == s.pc,
{
    let t = set_reg(s, r, v);
    assert(frame_wf(s, s.fp));
    assert(reg_slot(s.fp, r) >= s.fp + hdr_slots());
    assert(t.region[(s.fp + hdr_callee()) as int] == s.region[(s.fp + hdr_callee()) as int]);
    assert(t.heap == s.heap);
    assert(frame_wf(t, t.fp));
    assert(cur_code(t) == cur_code(s));
}

/// `pc` moved to an op inside the function keeps the machine well-formed.
proof fn lemma_pc_wf(s: State, pc: nat)
    requires
        state_wf(s),
        pc < cur_code(s).ops.len(),
    ensures
        state_wf(State { pc: pc, ..s }),
{
    let t = State { pc: pc, ..s };
    assert(cur_code(t) == cur_code(s));
}

/// A core op keeps the machine well-formed, and the region keeps its size:
/// no core op moves the frame, touches the heap or leaves the function.
pub proof fn lemma_core_step_wf(s: State, op: Op)
    requires
        state_wf(s),
        op == fetch(s),
        op_wf(cur_code(s), op),
        op_class(op) is Core,
    ensures
        state_wf(step(s, op)),
        step(s, op).region.len() == s.region.len(),
        step(s, op).fp == s.fp,
        step(s, op).heap == s.heap,
{
    let c = cur_code(s);
    assert(code_wf(c));
    assert(op_wf(c, c.ops[s.pc as int]));
    lemma_core_always_fast(s, op);
    // Every op that can continue is not the last (`code_wf`).
    if falls_through(op) {
        assert(s.pc + 1 < c.ops.len());
    }
    match op {
        Op::Nop => { lemma_pc_wf(s, s.pc + 1); },
        Op::Move { dst, src } => {
            lemma_set_reg_wf(s, dst, reg(s, src));
            lemma_pc_wf(set_reg(s, dst, reg(s, src)), s.pc + 1);
        },
        Op::LoadConst { dst, k } => {
            lemma_set_reg_wf(s, dst, c.consts[k as int]);
            lemma_pc_wf(set_reg(s, dst, c.consts[k as int]), s.pc + 1);
        },
        Op::LoadInt { dst, imm } => {
            lemma_set_reg_wf(s, dst, enc_int32(imm));
            lemma_pc_wf(set_reg(s, dst, enc_int32(imm)), s.pc + 1);
        },
        Op::LoadUndefined { dst } => {
            lemma_set_reg_wf(s, dst, UNDEFINED);
            lemma_pc_wf(set_reg(s, dst, UNDEFINED), s.pc + 1);
        },
        Op::LoadNull { dst } => {
            lemma_set_reg_wf(s, dst, NULL);
            lemma_pc_wf(set_reg(s, dst, NULL), s.pc + 1);
        },
        Op::LoadBool { dst, flag } => {
            lemma_set_reg_wf(s, dst, enc_bool(flag));
            lemma_pc_wf(set_reg(s, dst, enc_bool(flag)), s.pc + 1);
        },
        Op::LoadHole { dst } => {
            lemma_set_reg_wf(s, dst, HOLE);
            lemma_pc_wf(set_reg(s, dst, HOLE), s.pc + 1);
        },
        Op::GetThis { dst } => {
            let v = s.region[(s.fp + hdr_this()) as int];
            lemma_set_reg_wf(s, dst, v);
            lemma_pc_wf(set_reg(s, dst, v), s.pc + 1);
        },
        Op::GetCallee { dst } => {
            let v = s.region[(s.fp + hdr_callee()) as int];
            lemma_set_reg_wf(s, dst, v);
            lemma_pc_wf(set_reg(s, dst, v), s.pc + 1);
        },
        Op::GetArgc { dst } => {
            let v = enc_int32(argc_of(s.region[(s.fp + hdr_argc()) as int]) as i32);
            lemma_set_reg_wf(s, dst, v);
            lemma_pc_wf(set_reg(s, dst, v), s.pc + 1);
        },
        Op::GetException { dst } => {
            lemma_set_reg_wf(s, dst, s.exception);
            lemma_pc_wf(set_reg(s, dst, s.exception), s.pc + 1);
        },
        Op::Jump { target } => { lemma_pc_wf(s, target); },
        Op::JumpIfUndefined { src, target } => {
            lemma_pc_wf(s, target);
            lemma_pc_wf(s, s.pc + 1);
        },
        Op::JumpIfNotUndefined { src, target } => {
            lemma_pc_wf(s, target);
            lemma_pc_wf(s, s.pc + 1);
        },
        Op::JumpIfNullish { src, target } => {
            lemma_pc_wf(s, target);
            lemma_pc_wf(s, s.pc + 1);
        },
        Op::JumpIfNotNullish { src, target } => {
            lemma_pc_wf(s, target);
            lemma_pc_wf(s, s.pc + 1);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------
// Numbers
// ---------------------------------------------------------------------

/// For finite Numbers, `number_equal` is equality of the integer ordering
/// key: the justification for `f64_key` standing for `ℝ(x) = ℝ(y)`.
pub proof fn lemma_number_equal_key(x: u64, y: u64)
    requires
        is_finite(x),
        is_finite(y),
    ensures
        number_equal(x, y) <==> f64_key(x) == f64_key(y),
{
    assert(!is_nan(x) && !is_nan(y));
    bv_key_facts(x);
    bv_key_facts(y);
    bv_same_key(x, y);
}

/// The facts about sign-magnitude bits the key lemma uses.
proof fn bv_key_facts(x: u64)
    ensures
        (x >> 63) == 0u64 || (x >> 63) == 1u64,
        (x & 0x7FFF_FFFF_FFFF_FFFFu64) == 0u64 <==> (x == 0u64 || x == 0x8000_0000_0000_0000u64),
{
    assert((x >> 63) == 0u64 || (x >> 63) == 1u64) by (bit_vector);
    assert(((x & 0x7FFF_FFFF_FFFF_FFFFu64) == 0u64) <==> (x == 0u64 || x == 0x8000_0000_0000_0000u64)) by (bit_vector);
}

/// Same sign and same magnitude is the same bits.
proof fn bv_same_key(x: u64, y: u64)
    ensures
        ((x >> 63) == (y >> 63) && (x & 0x7FFF_FFFF_FFFF_FFFFu64) == (y & 0x7FFF_FFFF_FFFF_FFFFu64)) ==> x == y,
{
    assert(((x >> 63) == (y >> 63) && (x & 0x7FFF_FFFF_FFFF_FFFFu64) == (y & 0x7FFF_FFFF_FFFF_FFFFu64)) ==> x == y) by (bit_vector);
}

/// `x < y` and `y < x` are never both true (asymmetry of Number::lessThan).
pub proof fn lemma_less_than_asymmetric(x: u64, y: u64)
    ensures
        number_less_than(x, y) == Some(true) ==> number_less_than(y, x) == Some(false),
{
    if number_less_than(x, y) == Some(true) {
        assert(!is_nan(x) && !is_nan(y));
        assert(x != y);
        // Which of the infinity and zero steps fired.
        if is_pos_inf(y) {
            assert(!is_pos_inf(x));
        } else if is_neg_inf(x) {
            assert(!is_neg_inf(y));
        } else {
            assert(f64_key(x) < f64_key(y));
        }
    }
}

/// A few conversions, evaluated.
pub proof fn lemma_examples()
    ensures
        f64_of_int(0) == 0u64,
        to_int32(0x41F0_0000_0000_0000u64) == 0i32,
        to_uint32(0xBFF0_0000_0000_0000u64) == 4294967295u32,
{
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    reveal_with_fuel(ilog2, 40);
    assert(f64_exp(0x41F0_0000_0000_0000u64) == 1055u64) by (bit_vector);
    assert(f64_frac(0x41F0_0000_0000_0000u64) == 0u64) by (bit_vector);
    assert(f64_sign(0x41F0_0000_0000_0000u64) == 0u64) by (bit_vector);
    assert(f64_exp(0x41E0_0000_0000_0000u64) == 1054u64) by (bit_vector);
    assert(f64_frac(0x41E0_0000_0000_0000u64) == 0u64) by (bit_vector);
    assert(f64_sign(0x41E0_0000_0000_0000u64) == 0u64) by (bit_vector);
    assert(f64_exp(0xBFF0_0000_0000_0000u64) == 1023u64) by (bit_vector);
    assert(f64_frac(0xBFF0_0000_0000_0000u64) == 0u64) by (bit_vector);
    assert(f64_sign(0xBFF0_0000_0000_0000u64) == 1u64) by (bit_vector);
    assert(vstd::arithmetic::power2::pow2(52) / vstd::arithmetic::power2::pow2(52) == 1) by {
        vstd::arithmetic::div_mod::lemma_div_by_self(vstd::arithmetic::power2::pow2(52) as int);
    }
    assert(f64_trunc_abs(0xBFF0_0000_0000_0000u64) == 1nat);
    assert(f64_int32bit(0xBFF0_0000_0000_0000u64) == 4294967295nat);
    assert(vstd::arithmetic::power2::pow2(52) / vstd::arithmetic::power2::pow2(20) == 4294967296) by {
        vstd::arithmetic::div_mod::lemma_div_by_multiple(4294967296int, vstd::arithmetic::power2::pow2(20) as int);
    }
    assert(f64_trunc_abs(0x41F0_0000_0000_0000u64) == 4294967296nat);
    assert(f64_int32bit(0x41F0_0000_0000_0000u64) == 0nat);
    assert(to_int32(0x41F0_0000_0000_0000u64) == 0i32);
    assert(to_uint32(0xBFF0_0000_0000_0000u64) == 4294967295u32);
}

} // verus!
