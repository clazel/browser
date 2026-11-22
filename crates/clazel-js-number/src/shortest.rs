//! The shortest decimal digits that round-trip a double, by Ryū.
//!
//! Spec: Number::toString (§6.1.6.1.20†) step 5: "let n, k, and s be
//! integers such that k >= 1, 10^(k-1) <= s < 10^k, 𝔽(s x 10^(n-k)) is x,
//! and k is as small as possible. ... If there are multiple possibilities
//! for s, choose the value of s for which s x 10^(n-k) is closest in value
//! to ℝ(x). If there are two such possible values of s, choose the one that
//! is even." The section number (†) is from `phase-7.md` and unchecked
//! against the pin (see `parse.rs`).
//!
//! Algorithm: Ulf Adams, "Ryu: fast float-to-string conversion", PLDI 2018,
//! in the form of the reference implementation's `d2s.c` (function `d2d`,
//! with 125-bit table entries). It finds the interval of decimals that read
//! back as `x` (closed when the mantissa is even, because the reader rounds
//! ties to even), scales it by a power of ten with one 128-bit
//! multiplication, and strips digits while the interval still contains
//! more than one candidate. The few cases that are exact ties are tracked
//! by the `*_is_trailing_zeros` flags.
//!
//! Modelling choices: none beyond the algorithm. The tables are computed
//! ([`crate::tables`]); the reference's `div5`, `div10` and `div100`
//! helpers are plain division.

use crate::tables::{POW5_BITCOUNT, Tables, pow5bits, tables};

const MANTISSA_BITS: i64 = 52;
const BIAS: i64 = 1023;

/// `floor(log10(2^e))` for `0 <= e <= 1650`.
#[must_use]
pub fn log10_pow2(e: i64) -> i64 {
    e.saturating_mul(78_913) >> 18
}

/// `floor(log10(5^e))` for `0 <= e <= 2620`.
#[must_use]
pub fn log10_pow5(e: i64) -> i64 {
    e.saturating_mul(732_923) >> 20
}

/// `(m * mul) >> j` for a 128-bit `mul` below `2^125` and `64 <= j <= 191`
/// (a shift that does not apply, or an overflowing result, gives 0 or the
/// low 64 bits, so the function is total).
#[must_use]
pub fn mul_shift(m: u64, mul: u128, j: i64) -> u64 {
    let lo = u128::from(mul as u64);
    let hi = mul >> 64;
    let b0 = u128::from(m).wrapping_mul(lo);
    let b2 = u128::from(m).wrapping_mul(hi);
    let s = (b0 >> 64).wrapping_add(b2);
    let sh = u32::try_from(j.saturating_sub(64)).unwrap_or(u32::MAX);
    s.checked_shr(sh).unwrap_or(0) as u64
}

/// The number of times 5 divides `v` (0 for `v = 0`).
fn pow5_factor(v: u64) -> i64 {
    let mut v = v;
    let mut c = 0i64;
    while v != 0 && v.is_multiple_of(5) {
        v /= 5;
        c = c.saturating_add(1);
    }
    c
}

fn multiple_of_pow5(v: u64, p: i64) -> bool {
    pow5_factor(v) >= p
}

fn multiple_of_pow2(v: u64, p: i64) -> bool {
    match 1u64.checked_shl(u32::try_from(p).unwrap_or(u32::MAX)) {
        Some(b) => v & b.wrapping_sub(1) == 0,
        None => v == 0,
    }
}

/// The shortest decimal `(digits, exp10)` with `digits * 10^exp10` reading
/// back as the double with this biased exponent field and fraction. The
/// double must be finite and nonzero (`ieee_exponent < 2047`, and not both
/// fields zero); other inputs give an arbitrary but defined answer.
#[must_use]
pub fn d2d(ieee_mantissa: u64, ieee_exponent: u32, t: &Tables) -> (u64, i32) {
    d2d_with(
        ieee_mantissa,
        ieee_exponent,
        |q| t.pow5_inv_split.get(q).copied().unwrap_or(0),
        |i| t.pow5_split.get(i).copied().unwrap_or(0),
    )
}

/// [`d2d`] with the two tables as lookup functions (the Kani harness gives
/// them arbitrary entries).
#[must_use]
pub fn d2d_with(
    ieee_mantissa: u64,
    ieee_exponent: u32,
    inv_split: impl Fn(usize) -> u128,
    split: impl Fn(usize) -> u128,
) -> (u64, i32) {
    let (e2, m2) = if ieee_exponent == 0 {
        (1 - (BIAS + MANTISSA_BITS + 2), ieee_mantissa)
    } else {
        (
            i64::from(ieee_exponent).saturating_sub(BIAS + MANTISSA_BITS + 2),
            (1u64 << MANTISSA_BITS) | ieee_mantissa,
        )
    };
    let accept_bounds = m2 & 1 == 0;
    let mv = m2.saturating_mul(4);
    let mm_shift = u64::from(ieee_mantissa != 0 || ieee_exponent <= 1);
    let (mut vr, mut vp, mut vm);
    let e10: i64;
    let mut vm_trailing = false;
    let mut vr_trailing = false;
    let mm = mv.saturating_sub(1).saturating_sub(mm_shift);
    if e2 >= 0 {
        let q = log10_pow2(e2).saturating_sub(i64::from(e2 > 3));
        e10 = q;
        let qu = u32::try_from(q).unwrap_or(0);
        let k = i64::from(POW5_BITCOUNT)
            .saturating_add(i64::from(pow5bits(qu)))
            .saturating_sub(1);
        let i = q.saturating_add(k).saturating_sub(e2);
        let mul = inv_split(qu as usize);
        vr = mul_shift(mv, mul, i);
        vp = mul_shift(mv.saturating_add(2), mul, i);
        vm = mul_shift(mm, mul, i);
        if q <= 21 {
            if mv.is_multiple_of(5) {
                vr_trailing = multiple_of_pow5(mv, q);
            } else if accept_bounds {
                vm_trailing = multiple_of_pow5(mm, q);
            } else {
                vp = vp.saturating_sub(u64::from(multiple_of_pow5(mv.saturating_add(2), q)));
            }
        }
    } else {
        let ne2 = e2.saturating_neg();
        let q = log10_pow5(ne2).saturating_sub(i64::from(ne2 > 1));
        e10 = q.saturating_add(e2);
        let i = ne2.saturating_sub(q);
        let iu = u32::try_from(i).unwrap_or(0);
        let k = i64::from(pow5bits(iu)).saturating_sub(i64::from(POW5_BITCOUNT));
        let j = q.saturating_sub(k);
        let mul = split(iu as usize);
        vr = mul_shift(mv, mul, j);
        vp = mul_shift(mv.saturating_add(2), mul, j);
        vm = mul_shift(mm, mul, j);
        if q <= 1 {
            vr_trailing = true;
            if accept_bounds {
                vm_trailing = mm_shift == 1;
            } else {
                vp = vp.saturating_sub(1);
            }
        } else if q < 63 {
            vr_trailing = multiple_of_pow2(mv, q);
        }
    }

    // Step 4: the shortest representation in the interval.
    let mut removed: i64 = 0;
    let mut last_removed: u64 = 0;
    let output = if vm_trailing || vr_trailing {
        loop {
            let vp10 = vp / 10;
            let vm10 = vm / 10;
            if vp10 <= vm10 {
                break;
            }
            let vr10 = vr / 10;
            vm_trailing &= vm % 10 == 0;
            vr_trailing &= last_removed == 0;
            last_removed = vr % 10;
            vr = vr10;
            vp = vp10;
            vm = vm10;
            removed = removed.saturating_add(1);
        }
        if vm_trailing {
            loop {
                let vm10 = vm / 10;
                if vm % 10 != 0 {
                    break;
                }
                let vp10 = vp / 10;
                let vr10 = vr / 10;
                vr_trailing &= last_removed == 0;
                last_removed = vr % 10;
                vr = vr10;
                vp = vp10;
                vm = vm10;
                removed = removed.saturating_add(1);
            }
        }
        if vr_trailing && last_removed == 5 && vr % 2 == 0 {
            // Exactly halfway: round to even.
            last_removed = 4;
        }
        let up = (vr == vm && (!accept_bounds || !vm_trailing)) || last_removed >= 5;
        vr.saturating_add(u64::from(up))
    } else {
        let mut round_up = false;
        let vp100 = vp / 100;
        let vm100 = vm / 100;
        if vp100 > vm100 {
            round_up = vr % 100 >= 50;
            vr /= 100;
            vp = vp100;
            vm = vm100;
            removed = removed.saturating_add(2);
        }
        loop {
            let vp10 = vp / 10;
            let vm10 = vm / 10;
            if vp10 <= vm10 {
                break;
            }
            round_up = vr % 10 >= 5;
            vr /= 10;
            vp = vp10;
            vm = vm10;
            removed = removed.saturating_add(1);
        }
        vr.saturating_add(u64::from(vr == vm || round_up))
    };
    (
        output,
        i32::try_from(e10.saturating_add(removed)).unwrap_or(0),
    )
}

/// The shortest round-tripping digits of `x`, a finite positive number:
/// `(digits, exp10)` with `x = digits * 10^exp10` (as a real number read
/// back to nearest). `None` for zero, negative, infinite or NaN.
#[must_use]
pub fn shortest_digits(x: f64) -> Option<(u64, i32)> {
    let bits = x.to_bits();
    if !x.is_finite() || x <= 0.0 {
        return None;
    }
    let frac = bits & ((1u64 << MANTISSA_BITS) - 1);
    let exp = ((bits >> MANTISSA_BITS) & 0x7FF) as u32;
    Some(d2d(frac, exp, tables()))
}
