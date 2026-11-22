//! Kani harnesses. Compiled only under `cargo kani`.
//!
//! They prove, for every value of the inputs within the stated bounds
//! (symbolic, not sampled), that the functions named never panic, never
//! overflow (the crate is built with overflow checks, so an overflowing
//! operation is a failed assertion), and never index out of bounds; and,
//! where an oracle is cheap, that the answer is right.
//!
//! # `FixedBig<N>`, the array-backed big integer of the Number conversions
//!
//! `FixedBig<N>` (`fixed.rs`) holds `N` limbs in an array and the count in
//! use; an operation whose result needs more limbs drops them and sets a
//! `lost` flag, so every operation is total at every `N`. The harnesses run
//! it at `N` = 1, 2 and 3, not at the real sizes (64 limbs for StringToNumber's
//! exact path, 32 for the formatters and tables: they were sized by argument
//! and by measurement, see `fixed.rs`). The code is the same generic code at
//! every `N`: every limb access is a `get`, `take` or `zip`, and `N` appears
//! only as the array length and in `min(N)`, so what is shown at `N` = 2 or 3
//! for totality holds at `N` = 64. That is an argument, not a Kani result, and
//! the differential tests (`tests/fixed.rs` against `u128` with `N` = 2,
//! `tests/differential.rs` at the real sizes) are the evidence behind it.
//!
//! Proven on symbolic contents, each keeping the representation invariant
//! (`FixedBig::invariant`: `len <= N`, limbs from `len` on zero, top limb
//! nonzero):
//!
//! - `from_u128`, `low_u128`, `bit_len`, `bit` against `u128` (`N` = 2);
//!   `cmp_big` is `u128` order;
//! - `add_small`, `add_assign` against `u128` addition, and `lost` exactly on
//!   carry out; `sub_assign` against saturating `u128` subtraction;
//! - `mul_small`: one-limb value times a word equals the `u128` product;
//!   total on any three limbs times any word;
//! - `div_small`: total on any three limbs and any word, zero included, with
//!   the remainder below the divisor;
//! - `shl` (any shift of a `u64`, equal to the `u128` shift when it is below
//!   64) and `shr` (any shift of a `u128`, with the sticky bit); both total
//!   on any three limbs and any shift.
//!
//! Kani found one real bug here: `add_small` with a carry out of the top limb
//! left a zero top limb (invariant broken, only when the value did not fit).
//! Fixed by trimming.
//!
//! **Not proven by Kani**: `divrem` (its loop runs once per bit of the
//! dividend; one limb with a free dividend did not finish in 12 minutes, and
//! one limb with a dividend under 2^12 did not in 8), `mul_pow10`,
//! `mul_pow5`, `div_pow5` (each is a loop whose counter falls by saturating
//! subtraction around `mul_small`/`div_small`, but at `N` = 2 with `k` up to
//! 40 the multiplications did not finish in 7 minutes), `to_decimal`. They are
//! checked by `tests/fixed.rs` (`divrem`, against `u128`) and the
//! differential tests.
//!
//! # StringToNumber
//!
//! `string_to_number(&str)` is `string_to_number_bytes(s.as_bytes(), tables())`,
//! on bytes: the old `&str` version crashed the Kani compiler in `char`
//! decoding (`trim_matches` over `char`s and `char::to_digit`), so trimming is
//! now `trim_str_whitespace` on UTF-8 bytes and radix digits are
//! `digit_in_radix` (`tests/trim.rs` compares the trimmer with
//! `trim_matches(is_str_whitespace)` on every Unicode scalar value).
//!
//! - `string_to_number_bytes::<2>` with a table that has no Eisel-Lemire
//!   entry: total on every byte string of up to 3 bytes over a 12-byte
//!   alphabet (digits 0, 1, 9; both signs; `.`; `e`; space; `x`; `I`; the
//!   bytes `E2` and `80`). That covers whitespace trimming, signs, the radix
//!   prefix, `Infinity`'s first letter, `scan_decimal` and Clinger's fast
//!   path. A three-byte literal never reaches the exact path (`decimal_exact`
//!   needs a decimal exponent beyond 22 or more than 15 significant digits),
//!   so that path is not covered by this harness.
//! - Also: `round_to_f64` (every `q`, `exp2`, `sticky`), `eisel_lemire` (every
//!   `w`, `q` and every table entry with its top bit set), `scan_decimal` on
//!   every byte string of up to 5 bytes, `leading_digits` on every 3 + 3 digit
//!   literal with any exponent, and `radix_value` on every 3-byte string in
//!   each radix.
//!
//! **Not proven by Kani**: `decimal_exact` (the exact fallback): a harness for
//! one digit times `10^exp`, `exp` in 0..=400 on two limbs, did not finish in
//! 12 minutes; neither did 0..=40 nor 0..=18. Negative exponents also need
//! `divrem`. So `string_to_number` is **not** proven panic-free overall.
//! `tables()` (the powers-of-five tables, built once from `FixedBig` by
//! loops over about 700 entries) is not proven either. A CBMC timeout is
//! reported by Kani as FAILED, not as a counterexample; none of the harnesses
//! that were dropped produced a counterexample.
//!
//! # Number to string, `toFixed`, `toExponential`, `toPrecision`
//!
//! Proven: `mul_shift` (every 57-bit `m`, 125-bit `mul` and shift),
//! `log10_pow2`, `log10_pow5` and `pow5bits`.
//!
//! **Not proven by Kani**: `number_to_string`, `to_fixed`, `to_exponential`,
//! `to_precision`, `scaled_round`, `exponent_digits`, `layout_decimal`
//! (`String` building), and Ryu's `d2d_with` as a whole (written and stopped
//! after more than 400 s). A harness for `scaled_round` at two limbs with
//! `divrem` replaced by a stub that returns any value (Kani's unstable
//! stubbing, which `cargo kani -p` does not enable) did not finish in 6
//! minutes. The differential tests (`tests/differential.rs`: every `f32`
//! widened, 300,000 random doubles, `toFixed`/`toExponential`/`toPrecision`
//! against Rust's `{:.*}` and `{:.*e}`, with overflow checks on) exercise them;
//! that is evidence, not proof.
//!
//! # BigInt (`js_bigint`, the `Vec`-backed `bigint::Big`)
//!
//! Proven: `digit_value` and `digit_char` (total, below 36, mutually inverse,
//! exactly the ASCII alphanumerics), `chunk_power` (the largest power of each
//! radix 2 to 36 in a `u64`), `Big`'s `mul_small` and `div_small` total on any
//! two limbs, `cmp_big` is `u128` order and `bit_len`/`bit` match `u128`, and
//! one-limb `mul_small` then `add_small` against `u128` arithmetic.
//! `Big::add_small` against `u128` addition. BigInt magnitudes are unbounded,
//! so `Big` stays `Vec`-backed, and Kani cannot grow a `Vec` symbolically:
//! `parse_magnitude`, `magnitude_digits`, `string_to_bigint`,
//! `bigint_literal_value` and `BigInt::to_string_radix` are **not** proven;
//! `tests/bigint.rs` exercises them against an independent reference.
//! One-limb `div_small` against `u64` division and `push_chunk` (a 64-step
//! loop of `u64` division) were stopped after more than 3 minutes.
//!
//! So `clazel-js-number` stays at tier 0: no public conversion is proven free
//! of panics and overflow.

use crate::bigint::Big;
use crate::fixed::FixedBig;
use crate::js_bigint::{chunk_power, digit_char, digit_value};
use crate::parse::{
    Decimal, eisel_lemire, leading_digits, radix_value, round_to_f64, scan_decimal,
    string_to_number_bytes,
};
use crate::shortest::{log10_pow2, log10_pow5, mul_shift};
use crate::tables::{Tables, pow5bits};

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

// ---- BigInt parsing and printing (`js_bigint`): the small, bounded pieces ----

#[kani::proof]
fn digit_value_is_below_36_and_inverts_digit_char() {
    let b: u8 = kani::any();
    if let Some(d) = digit_value(b) {
        assert!(d < 36);
        // Re-printing gives the lowercase form of the same digit.
        let c = digit_char(d);
        assert!(c.is_some());
        assert!(c.map(|c| c.to_ascii_lowercase()) == Some(b.to_ascii_lowercase()));
        // Exactly the ASCII alphanumerics are digits.
        assert!(b.is_ascii_alphanumeric());
    } else {
        assert!(!b.is_ascii_alphanumeric());
    }
}

#[kani::proof]
fn digit_char_is_total_and_inverts_digit_value() {
    let d: u32 = kani::any();
    match digit_char(d) {
        Some(c) => {
            assert!(d < 36);
            assert!(digit_value(c) == Some(d));
            assert!(c.is_ascii_digit() || c.is_ascii_lowercase());
        }
        None => assert!(d >= 36),
    }
}

#[kani::proof]
#[kani::unwind(66)]
fn chunk_power_is_the_largest_power_in_a_word() {
    let radix: u32 = kani::any();
    kani::assume((2..=36).contains(&radix));
    let (p, k) = chunk_power(radix);
    assert!(k >= 1 && k <= 63);
    assert!(p >= u64::from(radix));
    // The largest: one more factor of the radix would not fit.
    assert!(p.checked_mul(u64::from(radix)).is_none());
}

#[kani::proof]
#[kani::unwind(6)]
fn single_limb_mul_add_is_u128_arithmetic() {
    // The step `parse_magnitude` takes: `mag = mag * m + a`, for a one-limb
    // magnitude (the product spills into a second limb).
    let x: u64 = kani::any();
    let m: u64 = kani::any();
    let a: u64 = kani::any();
    let mut b = Big::from_u64(x);
    b.mul_small(m);
    b.add_small(a);
    let want = u128::from(x) * u128::from(m);
    kani::assume(want <= u128::MAX - u128::from(a));
    assert!(b.low_u128() == want + u128::from(a));
}

// ---- `Big` on up to two limbs: the operations that finish ----

#[kani::proof]
#[kani::unwind(5)]
fn big_mul_small_two_limbs_is_total() {
    // Any two-limb value times any word: no panic, no overflow, no
    // out-of-bounds access. (The value is not checked: a 128-bit
    // multiplication against `u128` does not finish.)
    let x: u128 = kani::any();
    let m: u64 = kani::any();
    let mut b = Big::from_u128(x);
    b.mul_small(m);
}

#[kani::proof]
#[kani::unwind(5)]
fn big_div_small_two_limbs_is_total() {
    // Likewise for division by any word, zero included.
    let x: u128 = kani::any();
    let m: u64 = kani::any();
    let mut b = Big::from_u128(x);
    let _ = b.div_small(m);
}

#[kani::proof]
#[kani::unwind(5)]
fn big_cmp_is_u128_order() {
    let x: u128 = kani::any();
    let y: u128 = kani::any();
    assert!(Big::from_u128(x).cmp_big(&Big::from_u128(y)) == x.cmp(&y));
}

#[kani::proof]
#[kani::unwind(5)]
fn big_bit_len_and_bit_match_u128() {
    let x: u128 = kani::any();
    let i: u64 = kani::any();
    let b = Big::from_u128(x);
    assert!(b.bit_len() == u64::from(128 - x.leading_zeros()));
    let want = i < 128 && (x >> i) & 1 == 1;
    assert!(b.bit(i) == want);
}

// ---- `FixedBig<N>` (array-backed): the same generic code at small `N` ----

type B1 = FixedBig<1>;
type B2 = FixedBig<2>;
type B3 = FixedBig<3>;

#[kani::proof]
#[kani::unwind(5)]
fn fixed_from_u128_is_u128() {
    let x: u128 = kani::any();
    let i: u64 = kani::any();
    let b = B2::from_u128(x);
    assert!(b.invariant() && !b.lost());
    assert!(b.low_u128() == x);
    assert!(b.bit_len() == u64::from(128 - x.leading_zeros()));
    assert!(b.bit(i) == (i < 128 && (x >> i) & 1 == 1));
    assert!(b.is_zero() == (x == 0));
}

#[kani::proof]
#[kani::unwind(5)]
fn fixed_cmp_is_u128_order() {
    let x: u128 = kani::any();
    let y: u128 = kani::any();
    assert!(B2::from_u128(x).cmp_big(&B2::from_u128(y)) == x.cmp(&y));
}

#[kani::proof]
#[kani::unwind(5)]
fn fixed_add_small_is_u128_sum() {
    let x: u128 = kani::any();
    let a: u64 = kani::any();
    let mut b = B2::from_u128(x);
    b.add_small(a);
    assert!(b.invariant());
    assert!(b.low_u128() == x.wrapping_add(u128::from(a)));
    assert!(b.lost() == x.checked_add(u128::from(a)).is_none());
}

#[kani::proof]
#[kani::unwind(5)]
fn fixed_mul_small_is_total() {
    // Three limbs of any value times any word: total, invariant kept.
    let x: [u64; 3] = kani::any();
    let m: u64 = kani::any();
    let mut b = B3::from_limbs(x);
    b.mul_small(m);
    assert!(b.invariant());
}

#[kani::proof]
#[kani::unwind(5)]
fn fixed_mul_small_one_limb_is_u128_product() {
    let x: u64 = kani::any();
    let m: u64 = kani::any();
    let mut b = B2::from_u64(x);
    b.mul_small(m);
    assert!(b.invariant() && !b.lost());
    assert!(b.low_u128() == u128::from(x) * u128::from(m));
}

#[kani::proof]
#[kani::unwind(5)]
fn fixed_div_small_is_total() {
    let x: [u64; 3] = kani::any();
    let d: u64 = kani::any();
    let mut b = B3::from_limbs(x);
    let r = b.div_small(d);
    assert!(b.invariant());
    assert!(d == 0 || r < d);
}

#[kani::proof]
#[kani::unwind(5)]
fn fixed_shl_is_total_and_u128_shift() {
    let x: u64 = kani::any();
    let bits: u64 = kani::any();
    let b = B2::from_u64(x);
    let s = b.shl(bits);
    assert!(s.invariant());
    if bits < 64 {
        assert!(s.low_u128() == u128::from(x) << bits);
        assert!(!s.lost());
    }
}

#[kani::proof]
#[kani::unwind(5)]
fn fixed_shl_three_limbs_is_total() {
    let x: [u64; 3] = kani::any();
    let bits: u64 = kani::any();
    let s = B3::from_limbs(x).shl(bits);
    assert!(s.invariant());
}

#[kani::proof]
#[kani::unwind(5)]
fn fixed_shr_is_u128_shift() {
    let x: u128 = kani::any();
    let bits: u64 = kani::any();
    let (s, sticky) = B2::from_u128(x).shr(bits);
    assert!(s.invariant() && !s.lost());
    if bits < 128 {
        assert!(s.low_u128() == x >> bits);
        assert!(sticky == (x & ((1u128 << bits) - 1) != 0));
    } else {
        assert!(s.is_zero() && sticky == (x != 0));
    }
}

#[kani::proof]
#[kani::unwind(5)]
fn fixed_shr_three_limbs_is_total() {
    let x: [u64; 3] = kani::any();
    let bits: u64 = kani::any();
    let (s, _) = B3::from_limbs(x).shr(bits);
    assert!(s.invariant());
}

#[kani::proof]
#[kani::unwind(5)]
fn fixed_add_assign_is_u128_sum() {
    let x: u128 = kani::any();
    let y: u128 = kani::any();
    let mut b = B2::from_u128(x);
    b.add_assign(&B2::from_u128(y));
    assert!(b.invariant());
    assert!(b.low_u128() == x.wrapping_add(y));
    assert!(b.lost() == x.checked_add(y).is_none());
}

#[kani::proof]
#[kani::unwind(5)]
fn fixed_add_assign_three_limbs_is_total() {
    let x: [u64; 3] = kani::any();
    let y: [u64; 3] = kani::any();
    let mut b = B3::from_limbs(x);
    b.add_assign(&B3::from_limbs(y));
    assert!(b.invariant());
}

#[kani::proof]
#[kani::unwind(5)]
fn fixed_sub_assign_is_u128_difference() {
    let x: u128 = kani::any();
    let y: u128 = kani::any();
    let mut b = B2::from_u128(x);
    b.sub_assign(&B2::from_u128(y));
    assert!(b.invariant() && !b.lost());
    assert!(b.low_u128() == x.saturating_sub(y));
}

#[kani::proof]
#[kani::unwind(5)]
fn fixed_sub_assign_three_limbs_is_total() {
    let x: [u64; 3] = kani::any();
    let y: [u64; 3] = kani::any();
    let mut b = B3::from_limbs(x);
    b.sub_assign(&B3::from_limbs(y));
    assert!(b.invariant());
}

// ---- StringToNumber on bytes ----

/// Tables with no Eisel-Lemire entry: every decimal that Clinger's fast path
/// does not take goes to the exact path.
fn no_tables() -> Tables {
    Tables {
        el: Vec::new(),
        pow5_split: Vec::new(),
        pow5_inv_split: Vec::new(),
    }
}

#[kani::proof]
#[kani::unwind(6)]
fn string_to_number_bytes_three_bytes_is_total() {
    // Every byte string of up to 3 bytes over an alphabet that has a digit,
    // each sign, the point, both exponent letters, the radix letter, a space,
    // two bytes of a multi-byte whitespace character, and `I`.
    let bytes: [u8; 3] = kani::any();
    let n: usize = kani::any();
    kani::assume(n <= 3);
    for b in &bytes {
        kani::assume(matches!(
            *b,
            b'0' | b'1' | b'9' | b'.' | b'e' | b'-' | b'+' | b' ' | b'x' | b'I' | 0xE2 | 0x80
        ));
    }
    let _ = string_to_number_bytes::<2>(&bytes[..n], &no_tables());
}
