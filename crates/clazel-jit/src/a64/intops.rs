//! The one-instruction middle of an integer binary operator computes LIR's
//! result: for every supported operator and both widths, `int_op_instr(o, sf)`
//! run from a state whose `x0` and `x1` hold the operands leaves
//! [`lir::ibin32`] or [`lir::ibin64`] of them in `x0`. Built on [`super::alu`]'s
//! per-form lemmas.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// LIR's result of integer binary operator `o` on `x` and `y`, as the word
/// the machine holds: for an `i32` the operands are the low halves.
pub open spec fn ibin_w(o: lir::IBin, sf: isa::Width, x: u64, y: u64) -> int {
    if sf is W32 {
        lir::ibin32(o, x as u32, y as u32) as int
    } else {
        lir::ibin64(o, x, y) as int
    }
}

/// The result of an integer operator is a word of the operator's width.
pub proof fn lemma_ibin_w_bound(o: lir::IBin, sf: isa::Width, x: u64, y: u64)
    ensures
        0 <= ibin_w(o, sf, x, y) < isa::p2(super::alu::bits(sf)),
{
    super::memlemmas::lemma_p2_consts();
}

/// A signed reading of a word below `2^n` is `SInt`.
pub proof fn lemma_signed_of_sint(n: nat, x: int)
    requires
        n == 32 || n == 64,
        0 <= x < isa::p2(n),
    ensures
        lir::signed_of(n, x) == isa::sint(n, x),
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    super::alu::lemma_trunc_small(n, x);
    if n == 32 {
        assert(lir::pow2(32) == 0x1_0000_0000);
        assert(isa::p2(31) == 0x8000_0000);
    } else {
        assert(lir::pow2(64) == 0x1_0000_0000_0000_0000);
        assert(isa::p2(63) == 0x8000_0000_0000_0000);
    }
}

/// **`int_op_instr(o, sf)` computes LIR's operator.**
#[verifier::rlimit(500)]
pub proof fn lemma_step_int_op(s: isa::State, sf: isa::Width, o: lir::IBin, x: u64, y: u64)
    requires
        isa::wf(s),
        crate::spec::ibin_supported(o),
        s.r[0] == x,
        s.r[1] == y,
        x < isa::p2(super::alu::bits(sf)),
        y < isa::p2(super::alu::bits(sf)),
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(s, super::templates::int_op_instr(o, sf)) == Some(
            super::alu::wrote_x0(s, ibin_w(o, sf, x, y), super::alu::bits(sf)),
        ),
{
    let n = super::alu::bits(sf);
    super::alu::lemma_bits(sf);
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    lemma_ibin_w_bound(o, sf, x, y);
    let p = isa::p2(n);
    assert(lir::pow2(32) == 0x1_0000_0000);
    assert(lir::pow2(64) == 0x1_0000_0000_0000_0000);
    // the operands as the LIR values
    if n == 32 {
        assert((x as u32) as int == x as int);
        assert((y as u32) as int == y as int);
    }
    match o {
        lir::IBin::Add => {
            super::alu::lemma_step_addsub(s, sf, false, x, y);
            assert(ibin_w(o, sf, x, y) == (x as int + y as int) % p);
        },
        lir::IBin::Sub => {
            super::alu::lemma_step_addsub(s, sf, true, x, y);
            assert(ibin_w(o, sf, x, y) == (x as int - y as int) % p);
        },
        lir::IBin::Mul => {
            super::alu::lemma_step_mul(s, sf, x, y);
            assert(ibin_w(o, sf, x, y) == (x as int * y as int) % p);
        },
        lir::IBin::And | lir::IBin::Or | lir::IBin::Xor => {
            super::alu::lemma_step_logic(s, sf, o, x, y);
            if n == 32 {
                assert(((x as u32) & (y as u32)) as u64 == (x & y)) by (bit_vector)
                    requires
                        x < 0x1_0000_0000u64,
                        y < 0x1_0000_0000u64,
                ;
                assert(((x as u32) | (y as u32)) as u64 == (x | y)) by (bit_vector)
                    requires
                        x < 0x1_0000_0000u64,
                        y < 0x1_0000_0000u64,
                ;
                assert(((x as u32) ^ (y as u32)) as u64 == (x ^ y)) by (bit_vector)
                    requires
                        x < 0x1_0000_0000u64,
                        y < 0x1_0000_0000u64,
                ;
            }
            assert(ibin_w(o, sf, x, y) == super::alu::logic_val(o, x, y) as int);
        },
        lir::IBin::Shl | lir::IBin::ShrU | lir::IBin::ShrS => {
            super::alu::lemma_step_shift(s, sf, o, x, y);
            let k = (y as int % n as int) as nat;
            match o {
                lir::IBin::Shl => {
                    assert(ibin_w(o, sf, x, y) == (x as int * isa::p2(k)) % p);
                },
                lir::IBin::ShrU => {
                    assert(ibin_w(o, sf, x, y) == x as int / isa::p2(k));
                },
                _ => {
                    lemma_signed_of_sint(n, x as int);
                    assert(ibin_w(o, sf, x, y) == isa::trunc(n, isa::sint(n, x as int) / isa::p2(k)));
                },
            }
        },
        lir::IBin::Rotl => {
            assert(false);
        },
        lir::IBin::Rotr => {
            assert(false);
        },
    }
}

} // verus!
