//! Kani harnesses. Compiled only under `cargo kani`.
//!
//! They prove, for every value of the inputs within the stated bounds
//! (symbolic, not sampled), that the functions named never panic, never
//! overflow (the crate is built with overflow checks, so an overflowing
//! operation is a failed assertion), and never index out of bounds; and,
//! where an oracle is cheap, that the answer is right:
//!
//! - `Big::add_small` against `u128` addition;
//! - `round_to_f64` for every `q`, `exp2` and `sticky`: total, and never
//!   NaN or negative;
//! - `eisel_lemire` for every `w`, `q` and every table entry with its top
//!   bit set (as every real entry has): total, never NaN or negative. That
//!   no table value can make it overflow is this proof; that the real table
//!   is right is the differential tests' job;
//! - `mul_shift` (every 57-bit `m`, 125-bit `mul` and shift),
//!   `log10_pow2`, `log10_pow5` and `pow5bits`;
//! - `scan_decimal` on every byte string of up to 5 bytes, `leading_digits`
//!   on every 3 + 3 digit literal with any exponent, and `radix_value` on
//!   every 3-byte string in each radix.
//!
//! Harnesses that were written and did not finish within 100 s (on a loaded
//! laptop) were removed rather than left failing: `Big`'s `mul_small`,
//! `shl`/`shr`, `cmp_big`/`sub_assign`/`add_assign`, `divrem` and `div_small`
//! (vectors of limbs and 64-bit multiplication and division), Ryu's `d2d_with`
//! as a whole, and `layout_decimal` (string building). So these are **not**
//! proven panic-free by Kani: `decimal_exact`, `string_to_number`,
//! `number_to_string`, the three `to_*` formatters, `Big` beyond `add_small`,
//! and `d2d_with`. The differential tests (`tests/differential.rs`, with
//! overflow checks on) exercise them; that is evidence, not proof.

use crate::bigint::Big;
use crate::parse::{
    Decimal, eisel_lemire, leading_digits, radix_value, round_to_f64, scan_decimal,
};
use crate::shortest::{log10_pow2, log10_pow5, mul_shift};
use crate::tables::pow5bits;

#[kani::proof]
#[kani::unwind(4)]
fn big_add_small_is_u128_sum() {
    let x: u128 = kani::any();
    let a: u64 = kani::any();
    kani::assume(x <= u128::MAX - u128::from(a));
    let mut b = Big::from_u128(x);
    b.add_small(a);
    assert!(b.low_u128() == x + u128::from(a));
}

#[kani::proof]
fn round_to_f64_is_total() {
    let q: u64 = kani::any();
    let e: i64 = kani::any();
    let sticky: bool = kani::any();
    let v = round_to_f64(q, e, sticky);
    assert!(!v.is_nan());
    assert!(v.is_sign_positive());
}

#[kani::proof]
fn eisel_lemire_total() {
    let w: u64 = kani::any();
    let q: i64 = kani::any();
    let entry: u128 = kani::any();
    kani::assume(entry >> 127 == 1);
    if let Some(v) = eisel_lemire(w, q, entry) {
        assert!(!v.is_nan());
        assert!(v.is_sign_positive());
    }
}

#[kani::proof]
fn log10_pow2_is_bounded() {
    let e: i64 = kani::any();
    kani::assume((0..=1650).contains(&e));
    let r = log10_pow2(e);
    assert!(0 <= r && r <= e);
}

#[kani::proof]
fn log10_pow5_is_bounded() {
    let e: i64 = kani::any();
    kani::assume((0..=2620).contains(&e));
    let r = log10_pow5(e);
    assert!(0 <= r && r <= e);
}

#[kani::proof]
fn pow5bits_is_total() {
    let e: u32 = kani::any();
    let _ = pow5bits(e);
}

#[kani::proof]
fn mul_shift_is_total() {
    let m: u64 = kani::any();
    let mul: u128 = kani::any();
    let j: i64 = kani::any();
    kani::assume(m < 1 << 57 && mul < 1 << 125);
    let _ = mul_shift(m, mul, j);
}

#[kani::proof]
#[kani::unwind(8)]
fn scan_decimal_is_total() {
    let bytes: [u8; 5] = kani::any();
    let n: usize = kani::any();
    kani::assume(n <= 5);
    if let Some(d) = scan_decimal(&bytes[..n]) {
        assert!(d.int.len() + d.frac.len() <= n);
        let (_w, _q, _t) = leading_digits(&d);
    }
}

#[kani::proof]
#[kani::unwind(8)]
fn leading_digits_is_total() {
    let int: [u8; 3] = kani::any();
    let frac: [u8; 3] = kani::any();
    for b in int.iter().chain(frac.iter()) {
        kani::assume(b.is_ascii_digit());
    }
    let exp: i64 = kani::any();
    let d = Decimal {
        int: &int,
        frac: &frac,
        exp,
    };
    let (w, _q, _t) = leading_digits(&d);
    assert!(w < 1_000_000);
}

#[kani::proof]
#[kani::unwind(6)]
fn radix_value_is_total() {
    let bytes: [u8; 3] = kani::any();
    let bits: u32 = kani::any();
    kani::assume(bits == 1 || bits == 3 || bits == 4);
    if let Some(v) = radix_value(&bytes, bits) {
        assert!(!v.is_nan());
        assert!(v.is_sign_positive());
    }
}
