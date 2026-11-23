//! **Arithmetic and flag lemmas** of the x86-64 semantics the bounds-check
//! part of the confinement proof needs: the powers of two it uses, that
//! `logext 64` is the identity on small non-negative numbers, and what the
//! carry and zero flags are after an `add` and a `cmp` (the instructions of
//! the bounds-check sequence).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The powers of two used here, as numbers.
pub proof fn lemma_p2()
    ensures
        p2(0) == 1,
        p2(1) == 2,
        p2(2) == 4,
        p2(3) == 8,
        p2(4) == 16,
        p2(5) == 32,
        p2(6) == 64,
        p2(7) == 128,
        p2(8) == 256,
        p2(9) == 512,
        p2(10) == 1024,
        p2(11) == 2048,
        p2(32) == 4294967296,
        p2(47) == 140737488355328,
        p2(63) == 9223372036854775808,
        p2(64) == 18446744073709551616,
{
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
}

/// `logext 64` of a number below `2^63` is the number.
pub proof fn lemma_logext64_id(x: int)
    requires
        0 <= x < 9223372036854775808,
    ensures
        logext(64, x) == x,
{
    lemma_p2();
}

/// `loghead 64` of a number below `2^64` is the number.
pub proof fn lemma_loghead64_id(x: int)
    requires
        0 <= x < 18446744073709551616,
    ensures
        loghead(64, x) == x,
{
    lemma_p2();
}

/// A position of a flag the subset writes.
pub open spec fn flag_pos(k: nat) -> bool {
    k == 0 || k == 2 || k == 4 || k == 6 || k == 7 || k == 11
}

/// `bit` with the power of two given as the number.
pub proof fn lemma_bit_lit(x: int, k: nat, p: int)
    requires
        p == p2(k),
    ensures
        bit(x, k) == (x / p) % 2,
{
}

/// The value of a flag-bit update at position `k` with `P = 2^k`, given that
/// the arithmetic stays in 32 bits.
pub proof fn lemma_set_bit_val_p(w: u32, k: nat, v: int, p: int)
    requires
        p == p2(k),
        0 <= (w as int) - bit(w as int, k) * p + (v % 2) * p < 4294967296,
    ensures
        set_bit32(w, k, v) as int == (w as int) - bit(w as int, k) * p + (v % 2) * p,
{
}

/// The value of a flag-bit update is the arithmetic one, with the divisions
/// by literals (the cast to 32 bits loses nothing).
pub proof fn lemma_set_bit_val(w: u32, k: nat, v: int)
    requires
        flag_pos(k),
    ensures
        ({
            let x = set_bit32(w, k, v) as int;
            0 <= x < 4294967296 && (k == 0 ==> x == (w as int) - ((w as int) / 1) % 2 + (v % 2))
                && (k == 2 ==> x == (w as int) - (((w as int) / 4) % 2) * 4 + (v % 2) * 4) && (k
                == 4 ==> x == (w as int) - (((w as int) / 16) % 2) * 16 + (v % 2) * 16) && (k == 6
                ==> x == (w as int) - (((w as int) / 64) % 2) * 64 + (v % 2) * 64) && (k == 7
                ==> x == (w as int) - (((w as int) / 128) % 2) * 128 + (v % 2) * 128) && (k == 11
                ==> x == (w as int) - (((w as int) / 2048) % 2) * 2048 + (v % 2) * 2048)
        }),
{
    lemma_p2();
    if k == 0 {
        lemma_bit_lit(w as int, 0, 1);
        assert(0 <= (w as int) - (((w as int) / 1) % 2) * 1 + (v % 2) * 1 < 4294967296);
        lemma_set_bit_val_p(w, 0, v, 1);
    } else if k == 2 {
        lemma_bit_lit(w as int, 2, 4);
        assert(0 <= (w as int) - (((w as int) / 4) % 2) * 4 + (v % 2) * 4 < 4294967296);
        lemma_set_bit_val_p(w, 2, v, 4);
    } else if k == 4 {
        lemma_bit_lit(w as int, 4, 16);
        assert(0 <= (w as int) - (((w as int) / 16) % 2) * 16 + (v % 2) * 16 < 4294967296);
        lemma_set_bit_val_p(w, 4, v, 16);
    } else if k == 6 {
        lemma_bit_lit(w as int, 6, 64);
        assert(0 <= (w as int) - (((w as int) / 64) % 2) * 64 + (v % 2) * 64 < 4294967296);
        lemma_set_bit_val_p(w, 6, v, 64);
    } else if k == 7 {
        lemma_bit_lit(w as int, 7, 128);
        assert(0 <= (w as int) - (((w as int) / 128) % 2) * 128 + (v % 2) * 128 < 4294967296);
        lemma_set_bit_val_p(w, 7, v, 128);
    } else if k == 11 {
        lemma_bit_lit(w as int, 11, 2048);
        assert(0 <= (w as int) - (((w as int) / 2048) % 2) * 2048 + (v % 2) * 2048 < 4294967296);
        lemma_set_bit_val_p(w, 11, v, 2048);
    }
}

/// Setting flag bit 0 leaves flag bit 2 alone.
pub proof fn lemma_sbo_0_2(w: u32, v: int)
    ensures
        bit(set_bit32(w, 0, v) as int, 2) == bit(w as int, 2),
{
    lemma_p2();
    lemma_set_bit_val(w, 0, v);
    let x = set_bit32(w, 0, v) as int;
    lemma_bit_lit(x, 2, 4);
    lemma_bit_lit(w as int, 2, 4);
}

/// Setting flag bit 0 leaves flag bit 4 alone.
pub proof fn lemma_sbo_0_4(w: u32, v: int)
    ensures
        bit(set_bit32(w, 0, v) as int, 4) == bit(w as int, 4),
{
    lemma_p2();
    lemma_set_bit_val(w, 0, v);
    let x = set_bit32(w, 0, v) as int;
    lemma_bit_lit(x, 4, 16);
    lemma_bit_lit(w as int, 4, 16);
}

/// Setting flag bit 0 leaves flag bit 6 alone.
pub proof fn lemma_sbo_0_6(w: u32, v: int)
    ensures
        bit(set_bit32(w, 0, v) as int, 6) == bit(w as int, 6),
{
    lemma_p2();
    lemma_set_bit_val(w, 0, v);
    let x = set_bit32(w, 0, v) as int;
    lemma_bit_lit(x, 6, 64);
    lemma_bit_lit(w as int, 6, 64);
}

/// Setting flag bit 0 leaves flag bit 7 alone.
pub proof fn lemma_sbo_0_7(w: u32, v: int)
    ensures
        bit(set_bit32(w, 0, v) as int, 7) == bit(w as int, 7),
{
    lemma_p2();
    lemma_set_bit_val(w, 0, v);
    let x = set_bit32(w, 0, v) as int;
    lemma_bit_lit(x, 7, 128);
    lemma_bit_lit(w as int, 7, 128);
}

/// Setting flag bit 0 leaves flag bit 11 alone.
pub proof fn lemma_sbo_0_11(w: u32, v: int)
    ensures
        bit(set_bit32(w, 0, v) as int, 11) == bit(w as int, 11),
{
    lemma_p2();
    lemma_set_bit_val(w, 0, v);
    let x = set_bit32(w, 0, v) as int;
    lemma_bit_lit(x, 11, 2048);
    lemma_bit_lit(w as int, 11, 2048);
}

/// Setting flag bit 2 leaves flag bit 0 alone.
pub proof fn lemma_sbo_2_0(w: u32, v: int)
    ensures
        bit(set_bit32(w, 2, v) as int, 0) == bit(w as int, 0),
{
    lemma_p2();
    lemma_set_bit_val(w, 2, v);
    let x = set_bit32(w, 2, v) as int;
    lemma_bit_lit(x, 0, 1);
    lemma_bit_lit(w as int, 0, 1);
    lemma_bit_lit(w as int, 2, 4);
}

/// Setting flag bit 2 leaves flag bit 4 alone.
pub proof fn lemma_sbo_2_4(w: u32, v: int)
    ensures
        bit(set_bit32(w, 2, v) as int, 4) == bit(w as int, 4),
{
    lemma_p2();
    lemma_set_bit_val(w, 2, v);
    let x = set_bit32(w, 2, v) as int;
    lemma_bit_lit(x, 4, 16);
    lemma_bit_lit(w as int, 4, 16);
    lemma_bit_lit(w as int, 2, 4);
}

/// Setting flag bit 2 leaves flag bit 6 alone.
pub proof fn lemma_sbo_2_6(w: u32, v: int)
    ensures
        bit(set_bit32(w, 2, v) as int, 6) == bit(w as int, 6),
{
    lemma_p2();
    lemma_set_bit_val(w, 2, v);
    let x = set_bit32(w, 2, v) as int;
    lemma_bit_lit(x, 6, 64);
    lemma_bit_lit(w as int, 6, 64);
    lemma_bit_lit(w as int, 2, 4);
}

/// Setting flag bit 2 leaves flag bit 7 alone.
pub proof fn lemma_sbo_2_7(w: u32, v: int)
    ensures
        bit(set_bit32(w, 2, v) as int, 7) == bit(w as int, 7),
{
    lemma_p2();
    lemma_set_bit_val(w, 2, v);
    let x = set_bit32(w, 2, v) as int;
    lemma_bit_lit(x, 7, 128);
    lemma_bit_lit(w as int, 7, 128);
    lemma_bit_lit(w as int, 2, 4);
}

/// Setting flag bit 2 leaves flag bit 11 alone.
pub proof fn lemma_sbo_2_11(w: u32, v: int)
    ensures
        bit(set_bit32(w, 2, v) as int, 11) == bit(w as int, 11),
{
    lemma_p2();
    lemma_set_bit_val(w, 2, v);
    let x = set_bit32(w, 2, v) as int;
    lemma_bit_lit(x, 11, 2048);
    lemma_bit_lit(w as int, 11, 2048);
    lemma_bit_lit(w as int, 2, 4);
}

/// Setting flag bit 4 leaves flag bit 0 alone.
pub proof fn lemma_sbo_4_0(w: u32, v: int)
    ensures
        bit(set_bit32(w, 4, v) as int, 0) == bit(w as int, 0),
{
    lemma_p2();
    lemma_set_bit_val(w, 4, v);
    let x = set_bit32(w, 4, v) as int;
    lemma_bit_lit(x, 0, 1);
    lemma_bit_lit(w as int, 0, 1);
    lemma_bit_lit(w as int, 4, 16);
}

/// Setting flag bit 4 leaves flag bit 2 alone.
pub proof fn lemma_sbo_4_2(w: u32, v: int)
    ensures
        bit(set_bit32(w, 4, v) as int, 2) == bit(w as int, 2),
{
    lemma_p2();
    lemma_set_bit_val(w, 4, v);
    let x = set_bit32(w, 4, v) as int;
    lemma_bit_lit(x, 2, 4);
    lemma_bit_lit(w as int, 2, 4);
    lemma_bit_lit(w as int, 4, 16);
}

/// Setting flag bit 4 leaves flag bit 6 alone.
pub proof fn lemma_sbo_4_6(w: u32, v: int)
    ensures
        bit(set_bit32(w, 4, v) as int, 6) == bit(w as int, 6),
{
    lemma_p2();
    lemma_set_bit_val(w, 4, v);
    let x = set_bit32(w, 4, v) as int;
    lemma_bit_lit(x, 6, 64);
    lemma_bit_lit(w as int, 6, 64);
    lemma_bit_lit(w as int, 4, 16);
}

/// Setting flag bit 4 leaves flag bit 7 alone.
pub proof fn lemma_sbo_4_7(w: u32, v: int)
    ensures
        bit(set_bit32(w, 4, v) as int, 7) == bit(w as int, 7),
{
    lemma_p2();
    lemma_set_bit_val(w, 4, v);
    let x = set_bit32(w, 4, v) as int;
    lemma_bit_lit(x, 7, 128);
    lemma_bit_lit(w as int, 7, 128);
    lemma_bit_lit(w as int, 4, 16);
}

/// Setting flag bit 4 leaves flag bit 11 alone.
pub proof fn lemma_sbo_4_11(w: u32, v: int)
    ensures
        bit(set_bit32(w, 4, v) as int, 11) == bit(w as int, 11),
{
    lemma_p2();
    lemma_set_bit_val(w, 4, v);
    let x = set_bit32(w, 4, v) as int;
    lemma_bit_lit(x, 11, 2048);
    lemma_bit_lit(w as int, 11, 2048);
    lemma_bit_lit(w as int, 4, 16);
}

/// Setting flag bit 6 leaves flag bit 0 alone.
pub proof fn lemma_sbo_6_0(w: u32, v: int)
    ensures
        bit(set_bit32(w, 6, v) as int, 0) == bit(w as int, 0),
{
    lemma_p2();
    lemma_set_bit_val(w, 6, v);
    let x = set_bit32(w, 6, v) as int;
    lemma_bit_lit(x, 0, 1);
    lemma_bit_lit(w as int, 0, 1);
    lemma_bit_lit(w as int, 6, 64);
}

/// Setting flag bit 6 leaves flag bit 2 alone.
pub proof fn lemma_sbo_6_2(w: u32, v: int)
    ensures
        bit(set_bit32(w, 6, v) as int, 2) == bit(w as int, 2),
{
    lemma_p2();
    lemma_set_bit_val(w, 6, v);
    let x = set_bit32(w, 6, v) as int;
    lemma_bit_lit(x, 2, 4);
    lemma_bit_lit(w as int, 2, 4);
    lemma_bit_lit(w as int, 6, 64);
}

/// Setting flag bit 6 leaves flag bit 4 alone.
pub proof fn lemma_sbo_6_4(w: u32, v: int)
    ensures
        bit(set_bit32(w, 6, v) as int, 4) == bit(w as int, 4),
{
    lemma_p2();
    lemma_set_bit_val(w, 6, v);
    let x = set_bit32(w, 6, v) as int;
    lemma_bit_lit(x, 4, 16);
    lemma_bit_lit(w as int, 4, 16);
    lemma_bit_lit(w as int, 6, 64);
}

/// Setting flag bit 6 leaves flag bit 7 alone.
pub proof fn lemma_sbo_6_7(w: u32, v: int)
    ensures
        bit(set_bit32(w, 6, v) as int, 7) == bit(w as int, 7),
{
    lemma_p2();
    lemma_set_bit_val(w, 6, v);
    let x = set_bit32(w, 6, v) as int;
    lemma_bit_lit(x, 7, 128);
    lemma_bit_lit(w as int, 7, 128);
    lemma_bit_lit(w as int, 6, 64);
}

/// Setting flag bit 6 leaves flag bit 11 alone.
pub proof fn lemma_sbo_6_11(w: u32, v: int)
    ensures
        bit(set_bit32(w, 6, v) as int, 11) == bit(w as int, 11),
{
    lemma_p2();
    lemma_set_bit_val(w, 6, v);
    let x = set_bit32(w, 6, v) as int;
    lemma_bit_lit(x, 11, 2048);
    lemma_bit_lit(w as int, 11, 2048);
    lemma_bit_lit(w as int, 6, 64);
}

/// Setting flag bit 7 leaves flag bit 0 alone.
pub proof fn lemma_sbo_7_0(w: u32, v: int)
    ensures
        bit(set_bit32(w, 7, v) as int, 0) == bit(w as int, 0),
{
    lemma_p2();
    lemma_set_bit_val(w, 7, v);
    let x = set_bit32(w, 7, v) as int;
    lemma_bit_lit(x, 0, 1);
    lemma_bit_lit(w as int, 0, 1);
    lemma_bit_lit(w as int, 7, 128);
}

/// Setting flag bit 7 leaves flag bit 2 alone.
pub proof fn lemma_sbo_7_2(w: u32, v: int)
    ensures
        bit(set_bit32(w, 7, v) as int, 2) == bit(w as int, 2),
{
    lemma_p2();
    lemma_set_bit_val(w, 7, v);
    let x = set_bit32(w, 7, v) as int;
    lemma_bit_lit(x, 2, 4);
    lemma_bit_lit(w as int, 2, 4);
    lemma_bit_lit(w as int, 7, 128);
}

/// Setting flag bit 7 leaves flag bit 4 alone.
pub proof fn lemma_sbo_7_4(w: u32, v: int)
    ensures
        bit(set_bit32(w, 7, v) as int, 4) == bit(w as int, 4),
{
    lemma_p2();
    lemma_set_bit_val(w, 7, v);
    let x = set_bit32(w, 7, v) as int;
    lemma_bit_lit(x, 4, 16);
    lemma_bit_lit(w as int, 4, 16);
    lemma_bit_lit(w as int, 7, 128);
}

/// Setting flag bit 7 leaves flag bit 6 alone.
pub proof fn lemma_sbo_7_6(w: u32, v: int)
    ensures
        bit(set_bit32(w, 7, v) as int, 6) == bit(w as int, 6),
{
    lemma_p2();
    lemma_set_bit_val(w, 7, v);
    let x = set_bit32(w, 7, v) as int;
    lemma_bit_lit(x, 6, 64);
    lemma_bit_lit(w as int, 6, 64);
    lemma_bit_lit(w as int, 7, 128);
}

/// Setting flag bit 7 leaves flag bit 11 alone.
pub proof fn lemma_sbo_7_11(w: u32, v: int)
    ensures
        bit(set_bit32(w, 7, v) as int, 11) == bit(w as int, 11),
{
    lemma_p2();
    lemma_set_bit_val(w, 7, v);
    let x = set_bit32(w, 7, v) as int;
    lemma_bit_lit(x, 11, 2048);
    lemma_bit_lit(w as int, 11, 2048);
    lemma_bit_lit(w as int, 7, 128);
}

/// Setting flag bit 11 leaves flag bit 0 alone.
pub proof fn lemma_sbo_11_0(w: u32, v: int)
    ensures
        bit(set_bit32(w, 11, v) as int, 0) == bit(w as int, 0),
{
    lemma_p2();
    lemma_set_bit_val(w, 11, v);
    let x = set_bit32(w, 11, v) as int;
    lemma_bit_lit(x, 0, 1);
    lemma_bit_lit(w as int, 0, 1);
    lemma_bit_lit(w as int, 11, 2048);
}

/// Setting flag bit 11 leaves flag bit 2 alone.
pub proof fn lemma_sbo_11_2(w: u32, v: int)
    ensures
        bit(set_bit32(w, 11, v) as int, 2) == bit(w as int, 2),
{
    lemma_p2();
    lemma_set_bit_val(w, 11, v);
    let x = set_bit32(w, 11, v) as int;
    lemma_bit_lit(x, 2, 4);
    lemma_bit_lit(w as int, 2, 4);
    lemma_bit_lit(w as int, 11, 2048);
}

/// Setting flag bit 11 leaves flag bit 4 alone.
pub proof fn lemma_sbo_11_4(w: u32, v: int)
    ensures
        bit(set_bit32(w, 11, v) as int, 4) == bit(w as int, 4),
{
    lemma_p2();
    lemma_set_bit_val(w, 11, v);
    let x = set_bit32(w, 11, v) as int;
    lemma_bit_lit(x, 4, 16);
    lemma_bit_lit(w as int, 4, 16);
    lemma_bit_lit(w as int, 11, 2048);
}

/// Setting flag bit 11 leaves flag bit 6 alone.
pub proof fn lemma_sbo_11_6(w: u32, v: int)
    ensures
        bit(set_bit32(w, 11, v) as int, 6) == bit(w as int, 6),
{
    lemma_p2();
    lemma_set_bit_val(w, 11, v);
    let x = set_bit32(w, 11, v) as int;
    lemma_bit_lit(x, 6, 64);
    lemma_bit_lit(w as int, 6, 64);
    lemma_bit_lit(w as int, 11, 2048);
}

/// Setting flag bit 11 leaves flag bit 7 alone.
pub proof fn lemma_sbo_11_7(w: u32, v: int)
    ensures
        bit(set_bit32(w, 11, v) as int, 7) == bit(w as int, 7),
{
    lemma_p2();
    lemma_set_bit_val(w, 11, v);
    let x = set_bit32(w, 11, v) as int;
    lemma_bit_lit(x, 7, 128);
    lemma_bit_lit(w as int, 7, 128);
    lemma_bit_lit(w as int, 11, 2048);
}

/// Setting a flag bit to `v` leaves every other flag bit alone.
pub proof fn lemma_set_bit_other(w: u32, k: nat, v: int, j: nat)
    requires
        flag_pos(k),
        flag_pos(j),
        k != j,
    ensures
        bit(set_bit32(w, k, v) as int, j) == bit(w as int, j),
{
    if k == 0 {
        if j == 2 {
            lemma_sbo_0_2(w, v);
        } else if j == 4 {
            lemma_sbo_0_4(w, v);
        } else if j == 6 {
            lemma_sbo_0_6(w, v);
        } else if j == 7 {
            lemma_sbo_0_7(w, v);
        } else if j == 11 {
            lemma_sbo_0_11(w, v);
        }
    } else if k == 2 {
        if j == 0 {
            lemma_sbo_2_0(w, v);
        } else if j == 4 {
            lemma_sbo_2_4(w, v);
        } else if j == 6 {
            lemma_sbo_2_6(w, v);
        } else if j == 7 {
            lemma_sbo_2_7(w, v);
        } else if j == 11 {
            lemma_sbo_2_11(w, v);
        }
    } else if k == 4 {
        if j == 0 {
            lemma_sbo_4_0(w, v);
        } else if j == 2 {
            lemma_sbo_4_2(w, v);
        } else if j == 6 {
            lemma_sbo_4_6(w, v);
        } else if j == 7 {
            lemma_sbo_4_7(w, v);
        } else if j == 11 {
            lemma_sbo_4_11(w, v);
        }
    } else if k == 6 {
        if j == 0 {
            lemma_sbo_6_0(w, v);
        } else if j == 2 {
            lemma_sbo_6_2(w, v);
        } else if j == 4 {
            lemma_sbo_6_4(w, v);
        } else if j == 7 {
            lemma_sbo_6_7(w, v);
        } else if j == 11 {
            lemma_sbo_6_11(w, v);
        }
    } else if k == 7 {
        if j == 0 {
            lemma_sbo_7_0(w, v);
        } else if j == 2 {
            lemma_sbo_7_2(w, v);
        } else if j == 4 {
            lemma_sbo_7_4(w, v);
        } else if j == 6 {
            lemma_sbo_7_6(w, v);
        } else if j == 11 {
            lemma_sbo_7_11(w, v);
        }
    } else if k == 11 {
        if j == 0 {
            lemma_sbo_11_0(w, v);
        } else if j == 2 {
            lemma_sbo_11_2(w, v);
        } else if j == 4 {
            lemma_sbo_11_4(w, v);
        } else if j == 6 {
            lemma_sbo_11_6(w, v);
        } else if j == 7 {
            lemma_sbo_11_7(w, v);
        }
    }
}

/// Setting flag bit 0 to `v` makes it `v`.
pub proof fn lemma_sbs_0(w: u32, v: int)
    requires
        v == 0 || v == 1,
    ensures
        bit(set_bit32(w, 0, v) as int, 0) == v,
{
    lemma_p2();
    lemma_set_bit_val(w, 0, v);
    let x = set_bit32(w, 0, v) as int;
    lemma_bit_lit(x, 0, 1);
    lemma_bit_lit(w as int, 0, 1);
}

/// Setting flag bit 2 to `v` makes it `v`.
pub proof fn lemma_sbs_2(w: u32, v: int)
    requires
        v == 0 || v == 1,
    ensures
        bit(set_bit32(w, 2, v) as int, 2) == v,
{
    lemma_p2();
    lemma_set_bit_val(w, 2, v);
    let x = set_bit32(w, 2, v) as int;
    lemma_bit_lit(x, 2, 4);
    lemma_bit_lit(w as int, 2, 4);
}

/// Setting flag bit 4 to `v` makes it `v`.
pub proof fn lemma_sbs_4(w: u32, v: int)
    requires
        v == 0 || v == 1,
    ensures
        bit(set_bit32(w, 4, v) as int, 4) == v,
{
    lemma_p2();
    lemma_set_bit_val(w, 4, v);
    let x = set_bit32(w, 4, v) as int;
    lemma_bit_lit(x, 4, 16);
    lemma_bit_lit(w as int, 4, 16);
}

/// Setting flag bit 6 to `v` makes it `v`.
pub proof fn lemma_sbs_6(w: u32, v: int)
    requires
        v == 0 || v == 1,
    ensures
        bit(set_bit32(w, 6, v) as int, 6) == v,
{
    lemma_p2();
    lemma_set_bit_val(w, 6, v);
    let x = set_bit32(w, 6, v) as int;
    lemma_bit_lit(x, 6, 64);
    lemma_bit_lit(w as int, 6, 64);
}

/// Setting flag bit 7 to `v` makes it `v`.
pub proof fn lemma_sbs_7(w: u32, v: int)
    requires
        v == 0 || v == 1,
    ensures
        bit(set_bit32(w, 7, v) as int, 7) == v,
{
    lemma_p2();
    lemma_set_bit_val(w, 7, v);
    let x = set_bit32(w, 7, v) as int;
    lemma_bit_lit(x, 7, 128);
    lemma_bit_lit(w as int, 7, 128);
}

/// Setting flag bit 11 to `v` makes it `v`.
pub proof fn lemma_sbs_11(w: u32, v: int)
    requires
        v == 0 || v == 1,
    ensures
        bit(set_bit32(w, 11, v) as int, 11) == v,
{
    lemma_p2();
    lemma_set_bit_val(w, 11, v);
    let x = set_bit32(w, 11, v) as int;
    lemma_bit_lit(x, 11, 2048);
    lemma_bit_lit(w as int, 11, 2048);
}

/// Setting a flag bit to `v` (0 or 1) makes it `v`.
pub proof fn lemma_set_bit_same(w: u32, k: nat, v: int)
    requires
        flag_pos(k),
        v == 0 || v == 1,
    ensures
        bit(set_bit32(w, k, v) as int, k) == v,
{
    if k == 0 {
        lemma_sbs_0(w, v);
    } else if k == 2 {
        lemma_sbs_2(w, v);
    } else if k == 4 {
        lemma_sbs_4(w, v);
    } else if k == 6 {
        lemma_sbs_6(w, v);
    } else if k == 7 {
        lemma_sbs_7(w, v);
    } else if k == 11 {
        lemma_sbs_11(w, v);
    }
}

/// A flag update that sets all six flags to 0/1 values, as
/// `gpr_add_spec` and `gpr_sub_spec` build them.
pub open spec fn full_upd(cf: int, pf: int, af: int, zf: int, sf: int, of: int) -> FlagUpd {
    FlagUpd { cf: Some(cf), pf: Some(pf), af: Some(af), zf: Some(zf), sf: Some(sf), of: Some(of) }
}

/// After a full flag update, `cf` and `zf` are the ones given.
pub proof fn lemma_change_rflags_cf_zf(w: u32, cf: int, pf: int, af: int, zf: int, sf: int, of: int)
    requires
        cf == 0 || cf == 1,
        pf == 0 || pf == 1,
        af == 0 || af == 1,
        zf == 0 || zf == 1,
        sf == 0 || sf == 1,
        of == 0 || of == 1,
    ensures
        bit(change_rflags(w, full_upd(cf, pf, af, zf, sf, of)) as int, cf_bit()) == cf,
        bit(change_rflags(w, full_upd(cf, pf, af, zf, sf, of)) as int, zf_bit()) == zf,
{
    let f = full_upd(cf, pf, af, zf, sf, of);
    let w1 = opt_set_bit(w, cf_bit(), f.cf);
    let w2 = opt_set_bit(w1, pf_bit(), f.pf);
    let w3 = opt_set_bit(w2, af_bit(), f.af);
    let w4 = opt_set_bit(w3, zf_bit(), f.zf);
    let w5 = opt_set_bit(w4, sf_bit(), f.sf);
    let w6 = opt_set_bit(w5, of_bit(), f.of);
    assert(w6 == change_rflags(w, f));
    lemma_set_bit_same(w, cf_bit(), cf);
    lemma_set_bit_other(w1, pf_bit(), pf, cf_bit());
    lemma_set_bit_other(w2, af_bit(), af, cf_bit());
    lemma_set_bit_other(w3, zf_bit(), zf, cf_bit());
    lemma_set_bit_other(w4, sf_bit(), sf, cf_bit());
    lemma_set_bit_other(w5, of_bit(), of, cf_bit());
    lemma_set_bit_same(w3, zf_bit(), zf);
    lemma_set_bit_other(w4, sf_bit(), sf, zf_bit());
    lemma_set_bit_other(w5, of_bit(), of, zf_bit());
}

/// `write_user_rflags` with nothing undefined sets the flag bits from the
/// vector: `cf` and `zf` are the vector's.
pub proof fn lemma_wur_cf_zf(cu: spec_fn(nat) -> nat, s: State, u: u32)
    ensures
        flgi(write_user_rflags(cu, s, u, 0), cf_bit()) == bit(u as int, cf_bit()),
        flgi(write_user_rflags(cu, s, u, 0), zf_bit()) == bit(u as int, zf_bit()),
{
    lemma_p2();
    let s1 = write_flag_or_undefined(cu, s, cf_bit(), u, 0);
    let s2 = write_flag_or_undefined(cu, s1, pf_bit(), u, 0);
    let s3 = write_flag_or_undefined(cu, s2, af_bit(), u, 0);
    let s4 = write_flag_or_undefined(cu, s3, zf_bit(), u, 0);
    let s5 = write_flag_or_undefined(cu, s4, sf_bit(), u, 0);
    let s6 = write_flag_or_undefined(cu, s5, of_bit(), u, 0);
    assert(s6 == write_user_rflags(cu, s, u, 0));
    assert(bit(0int, 0) == 0 && bit(0int, 2) == 0 && bit(0int, 4) == 0);
    assert(bit(0int, 6) == 0 && bit(0int, 7) == 0 && bit(0int, 11) == 0);
    assert(s1.rflags == set_bit32(s.rflags, 0, bit(u as int, 0)));
    assert(s2.rflags == set_bit32(s1.rflags, 2, bit(u as int, 2)));
    assert(s3.rflags == set_bit32(s2.rflags, 4, bit(u as int, 4)));
    assert(s4.rflags == set_bit32(s3.rflags, 6, bit(u as int, 6)));
    assert(s5.rflags == set_bit32(s4.rflags, 7, bit(u as int, 7)));
    assert(s6.rflags == set_bit32(s5.rflags, 11, bit(u as int, 11)));
    lemma_set_bit_same(s.rflags, 0, bit(u as int, 0));
    lemma_set_bit_other(s1.rflags, 2, bit(u as int, 2), 0);
    lemma_set_bit_other(s2.rflags, 4, bit(u as int, 4), 0);
    lemma_set_bit_other(s3.rflags, 6, bit(u as int, 6), 0);
    lemma_set_bit_other(s4.rflags, 7, bit(u as int, 7), 0);
    lemma_set_bit_other(s5.rflags, 11, bit(u as int, 11), 0);
    lemma_set_bit_same(s3.rflags, 6, bit(u as int, 6));
    lemma_set_bit_other(s4.rflags, 7, bit(u as int, 7), 6);
    lemma_set_bit_other(s5.rflags, 11, bit(u as int, 11), 6);
}

/// **The flags after `add dst, src` on 64 bits**, as the bounds check reads
/// them: `cf` is the carry out.
pub proof fn lemma_add64_flags(cu: spec_fn(nat) -> nat, s: State, dst: int, src: int)
    requires
        0 <= dst < 18446744073709551616,
        0 <= src < 18446744073709551616,
    ensures
        ({
            let r = gpr_add_spec(64, dst, src, s.rflags);
            r.undef == 0 && r.result == (dst + src) % 18446744073709551616 && flgi(
                write_user_rflags(cu, s, r.rflags, r.undef),
                cf_bit(),
            ) == (if dst + src >= 18446744073709551616 {
                1int
            } else {
                0int
            })
        }),
{
    lemma_p2();
    let d = loghead(64, dst);
    let sr = loghead(64, src);
    assert(d == dst && sr == src);
    let raw = d + sr;
    let result = loghead(64, raw);
    let cf = cf_spec(64, raw);
    let pf = pf_spec(result);
    let af = add_af_spec(d, sr);
    let zf = zf_spec(result);
    let sf = sf_spec(64, result);
    let of = of_spec(64, logext(64, d) + logext(64, sr));
    assert(cf == 0 || cf == 1);
    assert(pf == 0 || pf == 1);
    assert(af == 0 || af == 1);
    assert(zf == 0 || zf == 1);
    assert(sf == 0 || sf == 1) by {
        assert(sf == (result / p2(63)) % 2);
    }
    assert(of == 0 || of == 1);
    let r = gpr_add_spec(64, dst, src, s.rflags);
    assert(r.rflags == change_rflags(s.rflags, full_upd(cf, pf, af, zf, sf, of)));
    lemma_change_rflags_cf_zf(s.rflags, cf, pf, af, zf, sf, of);
    lemma_wur_cf_zf(cu, s, r.rflags);
}

/// **The flags after `cmp dst, src` on 64 bits**: `cf` is set exactly when
/// `dst < src` and `zf` exactly when they are equal.
pub proof fn lemma_cmp64_flags(cu: spec_fn(nat) -> nat, s: State, dst: int, src: int)
    requires
        0 <= dst < 18446744073709551616,
        0 <= src < 18446744073709551616,
    ensures
        ({
            let r = gpr_sub_spec(64, dst, src, s.rflags);
            let t = write_user_rflags(cu, s, r.rflags, r.undef);
            r.undef == 0 && flgi(t, cf_bit()) == (if dst < src {
                1int
            } else {
                0int
            }) && flgi(t, zf_bit()) == (if dst == src {
                1int
            } else {
                0int
            })
        }),
{
    lemma_p2();
    let d = loghead(64, dst);
    let sr = loghead(64, src);
    assert(d == dst && sr == src);
    let signed_raw = logext(64, d) - logext(64, sr);
    let result = loghead(64, signed_raw);
    let cf = bool_to_bit(d < sr);
    let pf = pf_spec(result);
    let af = sub_af_spec(d, sr);
    let zf = zf_spec(result);
    let sf = sf_spec(64, result);
    let of = of_spec(64, signed_raw);
    assert(result == 0 <==> dst == src);
    assert(pf == 0 || pf == 1);
    assert(af == 0 || af == 1);
    assert(sf == 0 || sf == 1) by {
        assert(sf == (result / p2(63)) % 2);
    }
    assert(of == 0 || of == 1);
    let r = gpr_sub_spec(64, dst, src, s.rflags);
    assert(r.rflags == change_rflags(s.rflags, full_upd(cf, pf, af, zf, sf, of)));
    lemma_change_rflags_cf_zf(s.rflags, cf, pf, af, zf, sf, of);
    lemma_wur_cf_zf(cu, s, r.rflags);
}

} // verus!
