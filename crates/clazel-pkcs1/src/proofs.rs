//! Kani harnesses. Compiled only under `cargo kani`.
//!
//! They check the limb arithmetic exhaustively, for every value of its
//! inputs (symbolic, not sampled), against the machine's own `u128`
//! arithmetic as an independent oracle:
//!
//! - `adc` and `sbb` for every pair of limbs and carry;
//! - `add`, `sub` and `lt` for every pair of 2-limb numbers (128 bits);
//! - `shl8_add` (multiply by 256 and add an octet, the step of OS2IP) for
//!   every 2-limb number and octet whose result fits;
//! - `mod_add` for every 2-limb modulus and every pair of residues.
//!
//! Verus proves these functions for numbers of any length; Kani is a second
//! tool on the same code, over a machine model that does not share Verus's
//! encoding of `u64` arithmetic. Not covered here: `mod_mul` and `mod_exp`
//! (their loops run 64 times per limb, beyond what CBMC unrolls in
//! reasonable time).

use crate::bignum::arith::{add, lt, sub};
use crate::bignum::convert::shl8_add;
use crate::bignum::limb::{adc, sbb};
use crate::bignum::modular::mod_add;

/// A two-limb little-endian number as a `u128`.
fn val(a: &[u64]) -> u128 {
    let lo = a.first().copied().unwrap_or(0);
    let hi = a.get(1).copied().unwrap_or(0);
    u128::from(lo) | (u128::from(hi) << 64)
}

#[kani::proof]
fn adc_is_addition_with_carry() {
    let x: u64 = kani::any();
    let y: u64 = kani::any();
    let c: bool = kani::any();
    let (s, co) = adc(x, y, c);
    let wide = u128::from(x) + u128::from(y) + u128::from(c);
    assert!(u128::from(s) == wide & u128::from(u64::MAX));
    assert!(u128::from(co) == wide >> 64);
}

#[kani::proof]
fn sbb_is_subtraction_with_borrow() {
    let x: u64 = kani::any();
    let y: u64 = kani::any();
    let b: bool = kani::any();
    let (d, bo) = sbb(x, y, b);
    // x - y - b + bo * 2^64 = d, in 128-bit two's complement.
    let wide = (u128::from(x))
        .wrapping_sub(u128::from(y))
        .wrapping_sub(u128::from(b))
        .wrapping_add(u128::from(bo) << 64);
    assert!(wide == u128::from(d));
}

#[kani::proof]
#[kani::unwind(4)]
fn add_two_limbs() {
    let a: [u64; 2] = kani::any();
    let b: [u64; 2] = kani::any();
    let (s, carry) = add(&a, &b);
    let (sum, overflow) = val(&a).overflowing_add(val(&b));
    assert!(s.len() == 2);
    assert!(val(&s) == sum);
    assert!(carry == overflow);
}

#[kani::proof]
#[kani::unwind(4)]
fn sub_two_limbs() {
    let a: [u64; 2] = kani::any();
    let b: [u64; 2] = kani::any();
    let (d, borrow) = sub(&a, &b);
    let (diff, underflow) = val(&a).overflowing_sub(val(&b));
    assert!(d.len() == 2);
    assert!(val(&d) == diff);
    assert!(borrow == underflow);
}

#[kani::proof]
#[kani::unwind(4)]
fn compare_two_limbs() {
    let a: [u64; 2] = kani::any();
    let b: [u64; 2] = kani::any();
    assert!(lt(&a, &b) == (val(&a) < val(&b)));
}

#[kani::proof]
#[kani::unwind(4)]
fn shl8_add_two_limbs() {
    let a: [u64; 2] = kani::any();
    let byte: u8 = kani::any();
    // The precondition of `shl8_add`: the result fits in two limbs.
    let wide = val(&a)
        .checked_mul(256)
        .and_then(|v| v.checked_add(u128::from(byte)));
    kani::assume(wide.is_some());
    let r = shl8_add(&a, byte);
    assert!(r.len() == 2);
    assert!(Some(val(&r)) == wide);
}

#[kani::proof]
#[kani::unwind(6)]
fn mod_add_two_limbs() {
    let n: [u64; 2] = kani::any();
    let a: [u64; 2] = kani::any();
    let b: [u64; 2] = kani::any();
    kani::assume(val(&a) < val(&n));
    kani::assume(val(&b) < val(&n));
    let r = mod_add(&a, &b, &n);
    // (a + b) mod n without overflowing 128 bits: a + b < 2 n, so subtract
    // n once if a >= n - b.
    let (vn, va, vb) = (val(&n), val(&a), val(&b));
    let expect = if va >= vn - vb {
        va - (vn - vb)
    } else {
        va + vb
    };
    assert!(r.len() == 2);
    assert!(val(&r) == expect);
}
