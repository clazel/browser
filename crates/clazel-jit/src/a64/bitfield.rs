//! The bit-field instructions the templates use: `ubfm x0, x0, #0, #62`
//! (`f64.abs`) and `sbfm x0, x0, #0, #31` (`i64.extend_i32_s`), as numbers. The
//! bit masks come from `DecodeBitMasks`, evaluated here for these two
//! encodings.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `DecodeBitMasks(1, 62, 0, 64)` (the masks of `ubfm x, x, #0, #62`) are both
/// the low 63 bits.
pub proof fn lemma_masks_62()
    ensures
        isa::decode_bit_masks(1, 62, 0, 64) == (0x7FFF_FFFF_FFFF_FFFFint, 0x7FFF_FFFF_FFFF_FFFFint),
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    assert(isa::p2(6) == 64);
    assert(isa::not_vec(6, 62) == 1) by {
        assert(isa::trunc(6, 62) == 62);
        assert(isa::ones(6) == 63);
    }
    assert(isa::highest_set_bit(7, 65int) == 6) by {
        assert(isa::bit(65, 6) == 1);
    }
    assert(isa::and_vec(62, 63) == 62) by (bit_vector);
    assert(isa::and_vec(0, 63) == 0) by (bit_vector);
    assert(isa::ones(63) == 0x7FFF_FFFF_FFFF_FFFF);
    assert(isa::ror(64, 0x7FFF_FFFF_FFFF_FFFF, 0) == 0x7FFF_FFFF_FFFF_FFFFint);
    assert(isa::trunc(6, 62 - 0) == 62);
}

/// `DecodeBitMasks(1, 31, 0, 64)` (the masks of `sbfm x, x, #0, #31`) are both
/// the low 32 bits.
pub proof fn lemma_masks_31()
    ensures
        isa::decode_bit_masks(1, 31, 0, 64) == (0xFFFF_FFFFint, 0xFFFF_FFFFint),
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    assert(isa::p2(6) == 64);
    assert(isa::not_vec(6, 31) == 32) by {
        assert(isa::trunc(6, 31) == 31);
        assert(isa::ones(6) == 63);
    }
    assert(isa::highest_set_bit(7, 96int) == 6) by {
        assert(isa::bit(96, 6) == 1);
    }
    assert(isa::and_vec(31, 63) == 31) by (bit_vector);
    assert(isa::and_vec(0, 63) == 0) by (bit_vector);
    assert(isa::ones(32) == 0xFFFF_FFFF);
    assert(isa::ror(64, 0xFFFF_FFFF, 0) == 0xFFFF_FFFFint);
    assert(isa::trunc(6, 31 - 0) == 31);
}

/// `ubfm x0, x0, #0, #62` clears the sign bit: `x0` becomes `x & (2^63 - 1)`.
#[verifier::rlimit(300)]
pub proof fn lemma_step_abs(s: isa::State, x: u64)
    requires
        isa::wf(s),
        s.r[0] == x,
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(s, super::templates::abs_mid()[0]) == Some(
            super::alu::wrote_x0(s, (x & 0x7FFF_FFFF_FFFF_FFFFu64) as int, 64),
        ),
        (x & 0x7FFF_FFFF_FFFF_FFFFu64) as int <= 0x7FFF_FFFF_FFFF_FFFF,
{
    super::memlemmas::lemma_p2_consts();
    super::alu::lemma_pc4(s.pc);
    lemma_masks_62();
    super::alu::lemma_trunc_small(64, x as int);
    let m: u64 = 0x7FFF_FFFF_FFFF_FFFF;
    let nm = isa::not_vec(64, m as int);
    assert(nm == 0x8000_0000_0000_0000int) by {
        assert(isa::trunc(64, m as int) == m as int);
        assert(isa::ones(64) == 0xFFFF_FFFF_FFFF_FFFF);
    }
    assert(isa::and_vec(0, nm) == 0) by {
        assert(0u64 & (nm as u64) == 0u64) by (bit_vector);
    }
    assert(isa::ror(64, x as int, 0) == x as int);
    assert(isa::and_vec(x as int, m as int) == (x & m) as int);
    assert(isa::or_vec(0, (x & m) as int) == (x & m) as int) by (bit_vector);
    assert(isa::and_vec((x & m) as int, m as int) == (x & m) as int) by {
        assert(((x & m) & m) == (x & m)) by (bit_vector);
    }
    assert(isa::or_vec(0, (x & m) as int) == (x & m) as int) by {
        assert((0u64 | (x & m)) == (x & m)) by (bit_vector);
    }
    super::alu::lemma_trunc_small(64, (x & m) as int);
    assert((x & 0x7FFF_FFFF_FFFF_FFFFu64) <= 0x7FFF_FFFF_FFFF_FFFFu64) by (bit_vector);
}

/// `sbfm x0, x0, #0, #31` sign-extends the low 32 bits: for `x < 2^32`, `x0`
/// becomes `x` or `x + (2^64 - 2^32)` by the top bit.
#[verifier::rlimit(300)]
pub proof fn lemma_step_exts(s: isa::State, x: u64)
    requires
        isa::wf(s),
        s.r[0] == x,
        x < 0x1_0000_0000,
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(s, super::templates::exts_mid()[0]) == Some(
            super::alu::wrote_x0(
                s,
                if x >= 0x8000_0000 {
                    x as int + 0xFFFF_FFFF_0000_0000int
                } else {
                    x as int
                },
                64,
            ),
        ),
{
    super::memlemmas::lemma_p2_consts();
    super::alu::lemma_pc4(s.pc);
    lemma_masks_31();
    super::alu::lemma_trunc_small(64, x as int);
    let m: u64 = 0xFFFF_FFFF;
    let nm = isa::not_vec(64, m as int);
    assert(nm == 0xFFFF_FFFF_0000_0000int) by {
        assert(isa::trunc(64, m as int) == m as int);
        assert(isa::ones(64) == 0xFFFF_FFFF_FFFF_FFFF);
    }
    assert(isa::and_vec(0, nm) == 0) by {
        assert(0u64 & (nm as u64) == 0u64) by (bit_vector);
    }
    assert(isa::ror(64, x as int, 0) == x as int);
    assert((x & 0xFFFF_FFFFu64) == x) by (bit_vector)
        requires
            x < 0x1_0000_0000u64,
    ;
    assert(isa::and_vec(x as int, m as int) == x as int);
    assert(isa::or_vec(0, x as int) == x as int) by {
        assert((0u64 | x) == x) by (bit_vector);
    }
    // the sign bit and the top
    assert(isa::bit(x as int, 31) == (x as int / 0x8000_0000) % 2);
    let top = isa::replicate_bit(64, isa::bit(x as int, 31));
    if x >= 0x8000_0000 {
        assert(isa::bit(x as int, 31) == 1);
        assert(top == 0xFFFF_FFFF_FFFF_FFFFint);
        assert(isa::and_vec(top, nm) == 0xFFFF_FFFF_0000_0000int) by {
            assert((0xFFFF_FFFF_FFFF_FFFFu64 & 0xFFFF_FFFF_0000_0000u64) == 0xFFFF_FFFF_0000_0000u64)
                by (bit_vector);
        }
        assert(isa::or_vec(0xFFFF_FFFF_0000_0000int, x as int) == x as int + 0xFFFF_FFFF_0000_0000int) by {
            assert((0xFFFF_FFFF_0000_0000u64 | x) == 0xFFFF_FFFF_0000_0000u64 + x) by (bit_vector)
                requires
                    x < 0x1_0000_0000u64,
            ;
        }
        super::alu::lemma_trunc_small(64, x as int + 0xFFFF_FFFF_0000_0000int);
    } else {
        assert(isa::bit(x as int, 31) == 0);
        assert(top == 0);
        assert(isa::and_vec(top, nm) == 0) by {
            assert(0u64 & (nm as u64) == 0u64) by (bit_vector);
        }
        assert(isa::or_vec(0, x as int) == x as int) by {
            assert((0u64 | x) == x) by (bit_vector);
        }
    }
}

} // verus!
