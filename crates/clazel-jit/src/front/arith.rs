//! The arithmetic of the small-integer lowerings: what LIR's operators
//! compute on NaN-boxed int32s, shown equal to the bytecode semantics'
//! `arith_add`, `arith_sub` and `arith_mul`. The lowerings work on the
//! 64-bit words: test the tag, take each payload and sign-extend it, do the
//! operation in 64 bits (where an int32 operation cannot overflow), check
//! that the result is still an int32, and re-tag it.
//!
//! `k` is the operation: 0 add, 1 subtract, 2 multiply.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The low 32 bits of a word (`i32.wrap_i64`).
pub open spec fn lo32(v: u64) -> u32 {
    (v & 0xFFFF_FFFF) as u32
}

/// An `i32` sign-extended to 64 bits, as a word (`i64.extend_i32_s`).
pub open spec fn sext(x: u32) -> u64 {
    ((x as i32) as i64) as u64
}

/// The tag bits of an int32 value.
pub open spec fn tag_bits() -> u64 {
    0xFFF9_0000_0000_0000
}

/// The value of `v >> 32` for an int32 value: the tag and 16 zero bits.
pub open spec fn tag_hi() -> u64 {
    0xFFF9_0000
}

/// The 64-bit operation of `k`.
pub open spec fn ibin_of(k: nat) -> lir::IBin {
    if k == 0 {
        lir::IBin::Add
    } else if k == 1 {
        lir::IBin::Sub
    } else {
        lir::IBin::Mul
    }
}

/// The exact integer result of `k` on two int32s.
pub open spec fn int_result(k: nat, ia: int, ib: int) -> int {
    if k == 0 {
        ia + ib
    } else if k == 1 {
        ia - ib
    } else {
        ia * ib
    }
}

/// The int32 result is the encoding the bytecode semantics picks: it fits,
/// and (for a product) it is not a zero that should be `-0`.
pub open spec fn int_ok(k: nat, ia: int, ib: int) -> bool {
    let n = int_result(k, ia, ib);
    js::fits_i32(n) && !(k == 2 && n == 0 && (ia < 0 || ib < 0))
}

/// The bytecode semantics' result of `k` on two Numbers.
pub open spec fn spec_arith(k: nat, a: u64, b: u64) -> u64 {
    if k == 0 {
        js::arith_add(a, b)
    } else if k == 1 {
        js::arith_sub(a, b)
    } else {
        js::arith_mul(a, b)
    }
}

/// The 64-bit result the lowering computes, from the two operand words.
pub open spec fn s64(k: nat, va: u64, vb: u64) -> u64 {
    lir::ibin64(ibin_of(k), sext(lo32(va)), sext(lo32(vb)))
}

/// `1` if the 64-bit word `s` is the sign extension of its low 32 bits.
pub open spec fn fits_flag(s: u64) -> u32 {
    lir::bool_i32(sext(lo32(s)) == s)
}

/// The test of a product being a zero from a negative operand
/// (`+0 × -5` is `-0`, not an int32): non-zero exactly then.
pub open spec fn zneg_flag(va: u64, vb: u64, s: u64) -> u32 {
    lir::ibin32(
        lir::IBin::And,
        lir::bool_i32(s == 0),
        lir::bool_i32(
            lir::signed_of(64, (sext(lo32(va)) | sext(lo32(vb))) as int) < lir::signed_of(64, 0),
        ),
    )
}

/// The second guard's value: non-zero when the result is an int32 the
/// semantics encodes as one.
pub open spec fn guard2(k: nat, va: u64, vb: u64) -> u32 {
    let s = s64(k, va, vb);
    if k == 2 {
        lir::ibin32(lir::IBin::And, fits_flag(s), lir::bool_i32(zneg_flag(va, vb, s) == 0))
    } else {
        fits_flag(s)
    }
}

/// The word the lowering stores: the low 32 bits of `s`, tagged.
pub open spec fn tagged(s: u64) -> u64 {
    (s & 0xFFFF_FFFF) | tag_bits()
}

/// `i64.extend_i32_s (i32.wrap_i64 v)` computes [`sext`] of [`lo32`].
pub proof fn lemma_sx(y: u32)
    ensures
        lir::wrap(64, lir::signed_of(32, y as int)) as u64 == sext(y),
{
    vstd::arithmetic::power2::lemma2_to64();
    assert(lir::pow2(32) == 0x1_0000_0000);
    assert(lir::pow2(64) == 0x1_0000_0000_0000_0000);
    if y < 0x8000_0000 {
        assert(sext(y) == y as u64) by (bit_vector)
            requires
                y < 0x8000_0000u32,
        ;
    } else {
        assert(sext(y) == (y as u64) + 0xFFFF_FFFF_0000_0000u64) by (bit_vector)
            requires
                y >= 0x8000_0000u32,
        ;
    }
}

/// The 64-bit operators are the wrapping machine operations.
pub proof fn lemma_ibin64(k: nat, x: u64, y: u64)
    requires
        k <= 2,
    ensures
        lir::ibin64(ibin_of(k), x, y) == (if k == 0 {
            x.wrapping_add(y)
        } else if k == 1 {
            x.wrapping_sub(y)
        } else {
            x.wrapping_mul(y)
        }),
{
    vstd::arithmetic::power2::lemma2_to64();
    assert(lir::pow2(64) == 0x1_0000_0000_0000_0000);
    if k == 0 {
        assert((((x as int) + (y as int)) % 0x1_0000_0000_0000_0000int) as u64 == x.wrapping_add(y))
            by (bit_vector);
    } else if k == 1 {
        assert((((x as int) - (y as int)) % 0x1_0000_0000_0000_0000int) as u64 == x.wrapping_sub(y))
            by (bit_vector);
    } else {
        assert((((x as int) * (y as int)) % 0x1_0000_0000_0000_0000int) as u64 == x.wrapping_mul(y))
            by (bit_vector);
    }
}


/// `signed_of(64, x)` is the machine's signed reading.
pub proof fn lemma_signed64(x: u64)
    ensures
        lir::signed_of(64, x as int) == (x as i64) as int,
{
    vstd::arithmetic::power2::lemma2_to64();
    assert(lir::pow2(64) == 0x1_0000_0000_0000_0000);
    if x < 0x8000_0000_0000_0000 {
        assert((x as i64) as int == x as int) by (bit_vector)
            requires
                x < 0x8000_0000_0000_0000u64,
        ;
    } else {
        assert((x as i64) as int == (x as int) - 0x1_0000_0000_0000_0000int) by (bit_vector)
            requires
                x >= 0x8000_0000_0000_0000u64,
        ;
    }
}

/// An int32 value's payload, and its sign extension.
pub proof fn lemma_payload(v: u64)
    requires
        js::is_int32(v),
    ensures
        js::int32_of(v) == (lo32(v) as i32),
        sext(lo32(v)) == (js::int32_of(v) as i64) as u64,
{
}

/// `bool_i32` is 0 or 1.
pub proof fn lemma_bool_i32(b: bool)
    ensures
        lir::bool_i32(b) == (if b { 1u32 } else { 0u32 }),
{
}


/// `sext (lo32 s) == s` exactly when the signed reading of `s` is an int32.
pub proof fn lemma_fits_bv(m: i64)
    ensures
        (sext(lo32(m as u64)) == (m as u64)) <==> (-2147483648 <= m && m <= 2147483647),
        (-2147483648 <= m && m <= 2147483647) ==> tagged(m as u64) == js::enc_int32(m as i32),
{
    assert(((((((m as u64) & 0xFFFF_FFFFu64) as u32) as i32) as i64) as u64 == (m as u64))
        <==> (-2147483648 <= m && m <= 2147483647)) by (bit_vector);
    assert((-2147483648 <= m && m <= 2147483647) ==> (((m as u64) & 0xFFFF_FFFFu64) | 0xFFF9_0000_0000_0000u64)
        == (0xFFF9_0000_0000_0000u64 | ((((m as i32) as u32) as u64) & 0xFFFF_FFFFu64))) by (bit_vector);
}

/// The sign of the or of two sign-extended int32s.
pub proof fn lemma_neg_or_bv(ia: i32, ib: i32)
    ensures
        (((((ia as i64) as u64) | ((ib as i64) as u64)) as i64) < 0) <==> (ia < 0 || ib < 0),
{
    assert((((((ia as i64) as u64) | ((ib as i64) as u64)) as i64) < 0) <==> (ia < 0 || ib < 0))
        by (bit_vector);
}

/// The generic part of [`lemma_arith_facts`], once the 64-bit result is
/// known to be the exact integer result `m`.
pub proof fn lemma_arith_generic(k: nat, va: u64, vb: u64, m: i64)
    requires
        k <= 2,
        js::is_int32(va),
        js::is_int32(vb),
        s64(k, va, vb) == (m as u64),
        m as int == int_result(k, js::int32_of(va) as int, js::int32_of(vb) as int),
    ensures
        (guard2(k, va, vb) != 0) <==> int_ok(k, js::int32_of(va) as int, js::int32_of(vb) as int),
        int_ok(k, js::int32_of(va) as int, js::int32_of(vb) as int) ==> tagged(s64(k, va, vb))
            == spec_arith(k, va, vb),
{
    lemma_payload(va);
    lemma_payload(vb);
    let ia = js::int32_of(va);
    let ib = js::int32_of(vb);
    let s = s64(k, va, vb);
    lemma_fits_bv(m);
    assert(fits_flag(s) == (if js::fits_i32(m as int) { 1u32 } else { 0u32 }));
    if k == 2 {
        lemma_signed64((sext(lo32(va)) | sext(lo32(vb))));
        lemma_neg_or_bv(ia, ib);
        assert(sext(lo32(va)) == (ia as i64) as u64);
        assert(sext(lo32(vb)) == (ib as i64) as u64);
        let z = zneg_flag(va, vb, s);
        let xo = sext(lo32(va)) | sext(lo32(vb));
        lemma_signed64(0);
        assert(lir::signed_of(64, 0) == 0);
        assert(xo == (((ia as i64) as u64) | ((ib as i64) as u64)));
        assert((lir::signed_of(64, xo as int) < lir::signed_of(64, 0)) <==> (ia < 0 || ib < 0));
        assert((s == 0) <==> (m == 0)) by (bit_vector)
            requires
                s == (m as u64),
        ;
        let e1 = lir::bool_i32(s == 0);
        let e2 = lir::bool_i32(lir::signed_of(64, xo as int) < lir::signed_of(64, 0));
        assert(z == lir::ibin32(lir::IBin::And, e1, e2));
        assert(e1 == 0 || e1 == 1);
        assert(e2 == 0 || e2 == 1);
        assert(((e1 & e2) != 0) <==> (e1 == 1 && e2 == 1)) by (bit_vector)
            requires
                e1 == 0 || e1 == 1,
                e2 == 0 || e2 == 1,
        ;
        assert((z != 0) <==> (m == 0 && (ia < 0 || ib < 0)));
        assert((guard2(k, va, vb) != 0) <==> int_ok(k, ia as int, ib as int)) by {
            assert(guard2(k, va, vb) == lir::ibin32(
                lir::IBin::And,
                fits_flag(s),
                lir::bool_i32(z == 0),
            ));
            assert(fits_flag(s) == 0 || fits_flag(s) == 1);
            assert(lir::bool_i32(z == 0) == 0 || lir::bool_i32(z == 0) == 1);
            let f = fits_flag(s);
            let g = lir::bool_i32(z == 0);
            assert(((f & g) != 0) <==> (f == 1 && g == 1)) by (bit_vector)
                requires
                    f == 0 || f == 1,
                    g == 0 || g == 1,
            ;
        }
    } else {
        assert(fits_flag(s) == 0 || fits_flag(s) == 1);
    }
    if int_ok(k, ia as int, ib as int) {
        assert(m as int == int_result(k, ia as int, ib as int));
        assert(tagged(s) == js::enc_int32(m as i32));
        assert(spec_arith(k, va, vb) == js::enc_int32(m as i32));
    }
}

/// The facts the lowering's proof needs, for two int32 words: the second
/// guard is non-zero exactly when the result is an int32 the semantics
/// encodes as one, and then the tagged low half of the 64-bit result is the
/// semantics' result.
pub proof fn lemma_arith_facts(k: nat, va: u64, vb: u64)
    requires
        k <= 2,
        js::is_int32(va),
        js::is_int32(vb),
    ensures
        (guard2(k, va, vb) != 0) <==> int_ok(k, js::int32_of(va) as int, js::int32_of(vb) as int),
        int_ok(k, js::int32_of(va) as int, js::int32_of(vb) as int) ==> tagged(s64(k, va, vb))
            == spec_arith(k, va, vb),
{
    lemma_payload(va);
    lemma_payload(vb);
    let ia = js::int32_of(va);
    let ib = js::int32_of(vb);
    let xa = sext(lo32(va));
    let xb = sext(lo32(vb));
    lemma_ibin64(k, xa, xb);
    let s = s64(k, va, vb);
    assert(xa == (ia as i64) as u64);
    assert(xb == (ib as i64) as u64);
    let n = int_result(k, ia as int, ib as int);
    assert(-0x4000_0000_0000_0000int <= n <= 0x4000_0000_0000_0000int) by (nonlinear_arith)
        requires
            n == int_result(k, ia as int, ib as int),
            -2147483648 <= ia <= 2147483647,
            -2147483648 <= ib <= 2147483647,
    ;
    let m = n as i64;
    assert(m as int == n);
    if k == 0 {
        assert(s == (((ia as i64) + (ib as i64)) as u64)) by (bit_vector)
            requires
                s == xa.wrapping_add(xb),
                xa == (ia as i64) as u64,
                xb == (ib as i64) as u64,
        ;
        assert(s == (m as u64));
    } else if k == 1 {
        assert(s == (((ia as i64) - (ib as i64)) as u64)) by (bit_vector)
            requires
                s == xa.wrapping_sub(xb),
                xa == (ia as i64) as u64,
                xb == (ib as i64) as u64,
        ;
        assert(s == (m as u64));
    } else {
        assert(s == (((ia as i64) * (ib as i64)) as u64)) by (bit_vector)
            requires
                s == xa.wrapping_mul(xb),
                xa == (ia as i64) as u64,
                xb == (ib as i64) as u64,
        ;
        assert(s == (m as u64));
    }
    lemma_arith_generic(k, va, vb, m);
}

} // verus!
