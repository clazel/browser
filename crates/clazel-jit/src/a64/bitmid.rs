//! The middles that are constants and bit operations: `movz`/`movk` chains
//! (`t.const`), `movz; eor` (`f64.neg`), `ubfm` (`f64.abs`), `sbfm`
//! (`i64.extend_i32_s`) and `orr w0, wzr, w0` (`i32.wrap_i64`). With
//! [`super::mid`], these are every register-only middle of the first slice.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `imm16 << (16 hw)` for `hw` at most 3, with literal multipliers.
pub open spec fn chunk_val(imm16: u16, hw: u8) -> int {
    if hw == 0 {
        imm16 as int
    } else if hw == 1 {
        imm16 as int * 0x1_0000
    } else if hw == 2 {
        imm16 as int * 0x1_0000_0000
    } else {
        imm16 as int * 0x1_0000_0000_0000
    }
}

/// The power of two `movz` and `movk` scale by.
pub proof fn lemma_p2_hw(hw: u8)
    requires
        hw <= 3,
    ensures
        isa::p2((hw as nat) * 16) == (if hw == 0 {
            1int
        } else if hw == 1 {
            0x1_0000int
        } else if hw == 2 {
            0x1_0000_0000int
        } else {
            0x1_0000_0000_0000int
        }),
{
    super::memlemmas::lemma_p2_consts();
}

/// `movz x0, #imm16, lsl #(16 hw)` at width `sf` sets `x0` to the shifted
/// immediate.
#[verifier::rlimit(200)]
pub proof fn lemma_step_movz(s: isa::State, sf: isa::Width, d: u8, imm16: u16, hw: u8)
    requires
        isa::wf(s),
        d < 31,
        hw <= 3,
        (hw as nat) * 16 < super::alu::bits(sf),
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        0 <= chunk_val(imm16, hw) < isa::p2(super::alu::bits(sf)),
        isa::step(
            s,
            isa::Instr::MoveWide { sf, opcode: isa::MoveWideOp::Z, d, imm16, hw },
        ) == Some(
            isa::State {
                r: s.r.update(d as int, chunk_val(imm16, hw) as u64),
                pc: (s.pc + 4) as u64,
                ..s
            },
        ),
{
    let n = super::alu::bits(sf);
    super::alu::lemma_bits(sf);
    super::memlemmas::lemma_p2_consts();
    super::alu::lemma_pc4(s.pc);
    lemma_p2_hw(hw);
    let pos = (hw as nat) * 16;
    let pp = isa::p2(pos);
    vstd::arithmetic::power2::lemma_pow2_pos(pos);
    vstd::arithmetic::div_mod::lemma_basic_div(0, pp);
    assert(0int / pp == 0);
    assert(0 <= chunk_val(imm16, hw) < isa::p2(n));
    super::alu::lemma_trunc_small(n, chunk_val(imm16, hw));
    assert(chunk_val(imm16, hw) == imm16 as int * pp);
}

/// `movk x0, #imm16, lsl #(16 hw)` (`hw` from 1) at width `sf`, when `x0` is
/// below `2^(16 hw)`, adds the shifted immediate.
#[verifier::rlimit(200)]
pub proof fn lemma_step_movk(s: isa::State, sf: isa::Width, d: u8, imm16: u16, hw: u8)
    requires
        isa::wf(s),
        d < 31,
        1 <= hw <= 3,
        (hw as nat) * 16 < super::alu::bits(sf),
        s.r[d as int] < isa::p2((hw as nat) * 16),
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        0 <= s.r[d as int] as int + chunk_val(imm16, hw) < isa::p2(super::alu::bits(sf)),
        isa::step(
            s,
            isa::Instr::MoveWide { sf, opcode: isa::MoveWideOp::K, d, imm16, hw },
        ) == Some(
            isa::State {
                r: s.r.update(d as int, (s.r[d as int] as int + chunk_val(imm16, hw)) as u64),
                pc: (s.pc + 4) as u64,
                ..s
            },
        ),
{
    let n = super::alu::bits(sf);
    super::alu::lemma_bits(sf);
    super::memlemmas::lemma_p2_consts();
    super::alu::lemma_pc4(s.pc);
    lemma_p2_hw(hw);
    let pos = (hw as nat) * 16;
    let pp = isa::p2(pos);
    let old = s.r[d as int] as int;
    vstd::arithmetic::power2::lemma_pow2_pos(pos);
    // x_read of the old value (below 2^pos, so below 2^n)
    assert(pp <= isa::p2(n)) by {
        if hw == 1 {
            assert(pp == 0x1_0000);
        } else if hw == 2 {
            assert(pp == 0x1_0000_0000);
        } else {
            assert(pp == 0x1_0000_0000_0000);
        }
    }
    super::alu::lemma_trunc_small(n, old);
    vstd::arithmetic::div_mod::lemma_basic_div(old, pp);
    assert(old / pp == 0);
    assert(chunk_val(imm16, hw) == imm16 as int * pp);
    // the new value is below 2^n
    assert(old + chunk_val(imm16, hw) < isa::p2(n)) by {
        if hw == 1 {
            assert(old + imm16 as int * 0x1_0000 < 0x1_0000_0000);
        } else if hw == 2 {
            assert(old + imm16 as int * 0x1_0000_0000 < 0x1_0000_0000_0000);
        } else {
            assert(old + imm16 as int * 0x1_0000_0000_0000 < 0x1_0000_0000_0000_0000);
        }
    }
    super::alu::lemma_trunc_small(n, old + chunk_val(imm16, hw));
}

/// The four chunks of a 64-bit word add up to it.
pub proof fn lemma_chunks(c: u64)
    ensures
        c as int == super::templates::chunk(c, 0) as int + 0x1_0000 * super::templates::chunk(
            c,
            1,
        ) as int + 0x1_0000_0000 * super::templates::chunk(c, 2) as int + 0x1_0000_0000_0000
            * super::templates::chunk(c, 3) as int,
{
    let c0 = c as int % 0x1_0000;
    let c1 = (c as int / 0x1_0000) % 0x1_0000;
    let c2 = (c as int / 0x1_0000_0000) % 0x1_0000;
    let c3 = c as int / 0x1_0000_0000_0000;
    assert(c3 < 0x1_0000);
    assert(super::templates::chunk(c, 0) as int == c0);
    assert(super::templates::chunk(c, 1) as int == c1);
    assert(super::templates::chunk(c, 2) as int == c2);
    assert(super::templates::chunk(c, 3) as int == c3);
}

/// **A constant** is loaded into `x0`: the middle of `t.const`.
#[verifier::rlimit(500)]
pub proof fn lemma_mid_const(s: isa::State, v: lir::Val)
    requires
        isa::wf(s),
        s.pc as int + 4 * super::templates::const_mid(v).len() < 0x1_0000_0000_0000_0000,
    ensures
        run_seq(s, super::templates::const_mid(v)) is Some,
        super::mid::mid_post(
            s,
            run_seq(s, super::templates::const_mid(v)).unwrap(),
            0,
            lir::val_bits(v),
            4 * super::templates::const_mid(v).len(),
        ),
{
    super::memlemmas::lemma_p2_consts();
    match v {
        lir::Val::I32(c) => {
            let lo = super::templates::chunk(c as u64, 0);
            let hi = super::templates::chunk(c as u64, 1);
            let i1 = super::templates::movz0(isa::Width::W32, lo, 0);
            let i2 = super::templates::movk0(isa::Width::W32, hi, 1);
            assert(super::templates::const_mid(v) == seq![i1, i2]);
            assert(super::alu::bits(isa::Width::W32) == 32);
            lemma_step_movz(s, isa::Width::W32, 0, lo, 0);
            let s1 = isa::State {
                r: s.r.update(0, chunk_val(lo, 0) as u64),
                pc: (s.pc + 4) as u64,
                ..s
            };
            assert(isa::step(s, i1) == Some(s1));
            super::alu::lemma_pc4(s.pc);
            assert(isa::wf(s1));
            assert(s1.r[0] == lo as u64);
            lemma_step_movk(s1, isa::Width::W32, 0, hi, 1);
            let s2 = isa::State {
                r: s1.r.update(0, (s1.r[0] as int + chunk_val(hi, 1)) as u64),
                pc: (s1.pc + 4) as u64,
                ..s1
            };
            assert(isa::step(s1, i2) == Some(s2));
            super::runseq::run2(s, i1, i2, s1, s2);
            // lo + 65536 hi == c
            assert(lo as int == c as int % 0x1_0000);
            assert(hi as int == (c as int / 0x1_0000) % 0x1_0000);
            assert(lo as int + 0x1_0000 * hi as int == c as int);
            assert(s2.r[0] as nat == c as nat);
        },
        lir::Val::I64(c) => {
            lemma_const64(s, c);
        },
        lir::Val::F64(c) => {
            lemma_const64(s, c);
        },
    }
}

/// The four-instruction load of a 64-bit word.
#[verifier::rlimit(500)]
pub proof fn lemma_const64(s: isa::State, c: u64)
    requires
        isa::wf(s),
        s.pc as int + 16 < 0x1_0000_0000_0000_0000,
    ensures
        ({
            let code = seq![
                super::templates::movz0(isa::Width::W64, super::templates::chunk(c, 0), 0),
                super::templates::movk0(isa::Width::W64, super::templates::chunk(c, 1), 1),
                super::templates::movk0(isa::Width::W64, super::templates::chunk(c, 2), 2),
                super::templates::movk0(isa::Width::W64, super::templates::chunk(c, 3), 3),
            ];
            &&& run_seq(s, code) is Some
            &&& super::mid::mid_post(s, run_seq(s, code).unwrap(), 0, c as nat, 16)
        }),
{
    super::memlemmas::lemma_p2_consts();
    super::alu::lemma_pc4(s.pc);
    lemma_chunks(c);
    let c0 = super::templates::chunk(c, 0);
    let c1 = super::templates::chunk(c, 1);
    let c2 = super::templates::chunk(c, 2);
    let c3 = super::templates::chunk(c, 3);
    let w = isa::Width::W64;
    assert(super::alu::bits(w) == 64);
    let i1 = super::templates::movz0(w, c0, 0);
    let i2 = super::templates::movk0(w, c1, 1);
    let i3 = super::templates::movk0(w, c2, 2);
    let i4 = super::templates::movk0(w, c3, 3);
    lemma_step_movz(s, w, 0, c0, 0);
    let s1 = isa::State { r: s.r.update(0, chunk_val(c0, 0) as u64), pc: (s.pc + 4) as u64, ..s };
    assert(isa::step(s, i1) == Some(s1));
    assert(isa::wf(s1));
    assert(s1.r[0] == c0 as u64);
    lemma_step_movk(s1, w, 0, c1, 1);
    let v2 = s1.r[0] as int + chunk_val(c1, 1);
    let s2 = isa::State { r: s1.r.update(0, v2 as u64), pc: (s1.pc + 4) as u64, ..s1 };
    assert(isa::step(s1, i2) == Some(s2));
    assert(isa::wf(s2));
    assert(v2 < 0x1_0000_0000);
    assert(s2.r[0] == v2 as u64);
    lemma_step_movk(s2, w, 0, c2, 2);
    let v3 = s2.r[0] as int + chunk_val(c2, 2);
    let s3 = isa::State { r: s2.r.update(0, v3 as u64), pc: (s2.pc + 4) as u64, ..s2 };
    assert(isa::step(s2, i3) == Some(s3));
    assert(isa::wf(s3));
    assert(v3 < 0x1_0000_0000_0000);
    assert(s3.r[0] == v3 as u64);
    lemma_step_movk(s3, w, 0, c3, 3);
    let v4 = s3.r[0] as int + chunk_val(c3, 3);
    let s4 = isa::State { r: s3.r.update(0, v4 as u64), pc: (s3.pc + 4) as u64, ..s3 };
    assert(isa::step(s3, i4) == Some(s4));
    assert(v4 == c as int);
    super::runseq::run4(s, i1, i2, i3, i4, s1, s2, s3, s4);
    assert(s4.r[0] as nat == c as nat);
}

/// **`f64.neg`**: `movz x1, #0x8000, lsl #48; eor x0, x0, x1` flips the sign bit.
#[verifier::rlimit(300)]
pub proof fn lemma_mid_neg(s: isa::State, x: u64)
    requires
        isa::wf(s),
        s.r[0] == x,
        s.pc as int + 8 < 0x1_0000_0000_0000_0000,
    ensures
        run_seq(s, super::templates::neg_mid()) is Some,
        super::mid::mid_post(
            s,
            run_seq(s, super::templates::neg_mid()).unwrap(),
            0,
            (x ^ 0x8000_0000_0000_0000u64) as nat,
            8,
        ),
{
    super::memlemmas::lemma_p2_consts();
    let i1 = super::templates::neg_mid()[0];
    let i2 = super::templates::neg_mid()[1];
    assert(super::templates::neg_mid() == seq![i1, i2]);
    assert(super::alu::bits(isa::Width::W64) == 64);
    lemma_step_movz(s, isa::Width::W64, 1, 0x8000, 3);
    assert(chunk_val(0x8000, 3) == 0x8000_0000_0000_0000int);
    let s1 = isa::State { r: s.r.update(1, 0x8000_0000_0000_0000u64), pc: (s.pc + 4) as u64, ..s };
    assert(isa::step(s, i1) == Some(s1));
    super::alu::lemma_pc4(s.pc);
    assert(isa::wf(s1));
    assert(s1.r[0] == x && s1.r[1] == 0x8000_0000_0000_0000u64);
    super::alu::lemma_step_logic(s1, isa::Width::W64, lir::IBin::Xor, x, 0x8000_0000_0000_0000u64);
    let s2 = super::alu::wrote_x0(s1, (x ^ 0x8000_0000_0000_0000u64) as int, 64);
    assert(isa::step(s1, i2) == Some(s2));
    super::runseq::run2(s, i1, i2, s1, s2);
    super::mid::lemma_wrote_post(s1, (x ^ 0x8000_0000_0000_0000u64) as int, 64);
    assert(s2.mem == s.mem && s2.sp == s.sp && s2.vreg == s.vreg);
}

/// **`f64.abs`**: `ubfm x0, x0, #0, #62` clears the sign bit.
pub proof fn lemma_mid_abs(s: isa::State, x: u64)
    requires
        isa::wf(s),
        s.r[0] == x,
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        run_seq(s, super::templates::abs_mid()) is Some,
        super::mid::mid_post(
            s,
            run_seq(s, super::templates::abs_mid()).unwrap(),
            0,
            (x & 0x7FFF_FFFF_FFFF_FFFFu64) as nat,
            4,
        ),
{
    super::memlemmas::lemma_p2_consts();
    super::bitfield::lemma_step_abs(s, x);
    let i = super::templates::abs_mid()[0];
    assert(super::templates::abs_mid() == seq![i]);
    super::runseq::lemma_run_seq_one(s, i);
    let v = (x & 0x7FFF_FFFF_FFFF_FFFFu64) as int;
    assert(0 <= v < isa::p2(64));
    super::mid::lemma_wrote_post(s, v, 64);
}

/// **`i64.extend_i32_s`**: `sbfm x0, x0, #0, #31` sign-extends.
pub proof fn lemma_mid_exts(s: isa::State, x: u32)
    requires
        isa::wf(s),
        s.r[0] == x as u64,
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        run_seq(s, super::templates::exts_mid()) is Some,
        super::mid::mid_post(
            s,
            run_seq(s, super::templates::exts_mid()).unwrap(),
            0,
            lir::wrap(64, lir::signed_of(32, x as int)) as u64 as nat,
            4,
        ),
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    super::bitfield::lemma_step_exts(s, x as u64);
    let i = super::templates::exts_mid()[0];
    assert(super::templates::exts_mid() == seq![i]);
    super::runseq::lemma_run_seq_one(s, i);
    let v = if x as u64 >= 0x8000_0000 {
        x as int + 0xFFFF_FFFF_0000_0000int
    } else {
        x as int
    };
    assert(0 <= v < isa::p2(64));
    super::mid::lemma_wrote_post(s, v, 64);
    // LIR: wrap(64, signed_of(32, x)) = (x - 2^32 if x >= 2^31) mod 2^64
    assert(lir::pow2(32) == 0x1_0000_0000);
    assert(lir::pow2(64) == 0x1_0000_0000_0000_0000);
    assert(lir::wrap(64, lir::signed_of(32, x as int)) == v);
    assert(v as u64 as nat == v as nat);
}

/// **`i32.wrap_i64`**: `orr w0, wzr, w0` keeps the low 32 bits.
pub proof fn lemma_mid_wrap(s: isa::State, x: u64)
    requires
        isa::wf(s),
        s.r[0] == x,
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        run_seq(s, super::templates::wrap_mid()) is Some,
        super::mid::mid_post(
            s,
            run_seq(s, super::templates::wrap_mid()).unwrap(),
            0,
            ((x & 0xFFFF_FFFFu64) as u32) as nat,
            4,
        ),
{
    super::memlemmas::lemma_p2_consts();
    super::alu::lemma_pc4(s.pc);
    let i = super::templates::wrap_mid()[0];
    assert(super::templates::wrap_mid() == seq![i]);
    // x_read(0, 32) is the low half, or_vec(0, h) = h
    let h = isa::trunc(32, x as int);
    super::alu::lemma_trunc_bound(32, x as int);
    assert(isa::lsl(32, x as int, 0) == h) by {
        assert(isa::p2(0) == 1);
        assert(isa::trunc(32, h) == h) by {
            super::alu::lemma_trunc_small(32, h);
        }
    }
    assert(isa::or_vec(0, h) == h) by {
        assert((0u64 | (h as u64)) == (h as u64)) by (bit_vector);
    }
    assert(isa::trunc(32, h) == h) by {
        super::alu::lemma_trunc_small(32, h);
    }
    assert(isa::step(s, i) == Some(super::alu::wrote_x0(s, h, 32)));
    assert(h == ((x & 0xFFFF_FFFFu64) as u32) as int) by {
        assert(((x & 0xFFFF_FFFFu64) as u32) as u64 == x % 0x1_0000_0000u64) by (bit_vector);
    }
    super::runseq::lemma_run_seq_one(s, i);
    super::mid::lemma_wrote_post(s, h, 32);
}

} // verus!
