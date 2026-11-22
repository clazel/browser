//! Number to string: Number::toString (radix 10), `toFixed`, `toExponential`
//! and `toPrecision`.
//!
//! Spec: Number::toString (§6.1.6.1.20†), Number.prototype.toFixed
//! (§21.1.3.3†), toExponential (§21.1.3.2†), toPrecision (§21.1.3.5†). The
//! section numbers (†) are from `phase-7.md` and unchecked against the pin
//! (see `parse.rs`).
//!
//! Modelling choices:
//!
//! - The functions take the Number value `x` and the already-converted
//!   argument as an `i64` (or `None` for `undefined`); ToIntegerOrInfinity is
//!   the caller's (an infinite argument is passed as `i64::MAX` or
//!   `i64::MIN`, which the range checks reject as the spec's do). "Throw a
//!   RangeError" is `Err(RangeError)`.
//! - Where the spec says "let n be an integer for which n / 10^f - x is as
//!   close to zero as possible; if there are two such n, pick the larger",
//!   the integer is computed exactly: `x` is `m * 2^e`, so `n` is
//!   `floor((2 * m * 2^e * 10^f + 1) / 2)` as a ratio of big integers, with
//!   no rounding error to argue about. (`toFixed`, `toExponential` and
//!   `toPrecision` are slow paths, not the hot path of number printing.)
//! - Number::toString's shortest digits come from [`crate::shortest`].

use crate::bigint::push_u64;
use crate::fixed::{BIG_LIMBS_FORMAT, FixedBig};

/// The big integer of the exact formatting arithmetic.
type Big = FixedBig<BIG_LIMBS_FORMAT>;
use crate::shortest::{log10_pow2, shortest_digits};

/// A `RangeError`: an argument outside the range the spec allows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RangeError;

/// Lay out the digits of Number::toString (§6.1.6.1.20† steps 5 to 12):
/// the value is `digits * 10^(n - k)`, `k = digits.len()`, and `digits` has
/// no trailing zero. `neg` adds the leading "-".
#[must_use]
pub fn layout_decimal(neg: bool, digits: &str, n: i64) -> String {
    let mut s = String::new();
    if neg {
        s.push('-');
    }
    let k = digits.len() as i64;
    if k <= n && n <= 21 {
        // 6. "If k <= n <= 21": the digits, then n - k zeros.
        s.push_str(digits);
        for _ in 0..n.saturating_sub(k) {
            s.push('0');
        }
    } else if 0 < n && n <= 21 {
        // 7. "If 0 < n <= 21": the first n digits, ".", the rest.
        let at = usize::try_from(n).unwrap_or(0);
        s.push_str(digits.get(..at).unwrap_or(""));
        s.push('.');
        s.push_str(digits.get(at..).unwrap_or(""));
    } else if -6 < n && n <= 0 {
        // 8. "If -6 < n <= 0": "0.", -n zeros, the digits.
        s.push_str("0.");
        for _ in 0..n.saturating_neg() {
            s.push('0');
        }
        s.push_str(digits);
    } else {
        // 9. and 10.: scientific notation.
        s.push_str(digits.get(..1).unwrap_or(""));
        if k != 1 {
            s.push('.');
            s.push_str(digits.get(1..).unwrap_or(""));
        }
        push_exponent(&mut s, n.saturating_sub(1));
    }
    s
}

/// Append `e`, a sign and the decimal exponent.
fn push_exponent(s: &mut String, e: i64) {
    s.push('e');
    s.push(if e < 0 { '-' } else { '+' });
    push_u64(s, e.unsigned_abs(), 0);
}

/// Number::toString (§6.1.6.1.20†) with radix 10.
#[must_use]
pub fn number_to_string(x: f64) -> String {
    // 1. "If x is NaN, return "NaN"."
    if x.is_nan() {
        return "NaN".to_string();
    }
    // 2. "If x is either +0 or -0, return "0"."
    if x == 0.0 {
        return "0".to_string();
    }
    // 3. "If x < 0, return the string-concatenation of "-" and
    //    Number::toString(-x, 10)."
    let neg = x < 0.0;
    let x = x.abs();
    // 4. "If x is +infinity, return "Infinity"."
    if x.is_infinite() {
        return if neg { "-Infinity" } else { "Infinity" }.to_string();
    }
    // 5. The shortest digits.
    match shortest_digits(x) {
        Some((digits, e10)) => {
            let mut ds = String::new();
            push_u64(&mut ds, digits, 0);
            let n = i64::from(e10).saturating_add(ds.len() as i64);
            layout_decimal(neg, &ds, n)
        }
        None => "NaN".to_string(),
    }
}

/// `x = m * 2^e` exactly, for a finite nonnegative `x`.
fn decompose(x: f64) -> (u64, i64) {
    let bits = x.to_bits();
    let frac = bits & ((1u64 << 52) - 1);
    let exp = ((bits >> 52) & 0x7FF) as i64;
    if exp == 0 {
        (frac, -1074)
    } else {
        (frac | (1u64 << 52), exp.saturating_sub(1075))
    }
}

/// The integer nearest to `x * 10^scale`, the larger one on a tie.
///
/// Generic in the limb count `N` so that the Kani harnesses run the same code
/// at a small `N` (too few limbs gives a wrong but defined answer).
pub(crate) fn scaled_round<const N: usize>(x: f64, scale: i64) -> FixedBig<N> {
    let (m, e2) = decompose(x);
    let mut num = FixedBig::<N>::from_u64(m);
    let mut den = FixedBig::<N>::from_u64(1);
    if e2 >= 0 {
        num = num.shl(e2.unsigned_abs());
    } else {
        den = den.shl(e2.unsigned_abs());
    }
    let k = u32::try_from(scale.unsigned_abs()).unwrap_or(u32::MAX);
    if scale >= 0 {
        num.mul_pow10(k);
    } else {
        den.mul_pow10(k);
    }
    // floor((2 num + den) / (2 den)) is round-half-up of num / den.
    let mut twice = num.shl(1);
    twice.add_assign(&den);
    FixedBig::<N>::divrem(&twice, &den.shl(1)).0
}

/// The `p` digits `n` and the exponent `e` of the spec's "let e and n be
/// integers such that 10^(p-1) <= n < 10^p and n * 10^(e-p+1) - x is as
/// close to zero as possible; if there are two such sets, pick the larger
/// n * 10^(e-p+1)", for finite `x > 0` and `1 <= p <= 101`.
fn exponent_digits(x: f64, p: u32) -> (String, i64) {
    let (m, e2) = decompose(x);
    let top = e2
        .saturating_add(Big::from_u64(m).bit_len() as i64)
        .saturating_sub(1);
    // `log10_pow2` is exact enough that the true e is within one of this.
    let mut e = log10_pow2(top);
    let lo = Big::pow10(p.saturating_sub(1));
    let hi = Big::pow10(p);
    let mut last = String::new();
    for _ in 0..8 {
        let n = scaled_round(x, i64::from(p).saturating_sub(1).saturating_sub(e));
        if n.cmp_big(&lo) == std::cmp::Ordering::Less {
            e = e.saturating_sub(1);
        } else if n.cmp_big(&hi) != std::cmp::Ordering::Less {
            e = e.saturating_add(1);
        } else {
            return (n.to_decimal(), e);
        }
        last = n.to_decimal();
    }
    (last, e)
}

/// Number.prototype.toFixed (§21.1.3.3†) of the Number value `x`, with
/// `fraction_digits` the integer `f` of step 3.
///
/// # Errors
///
/// `RangeError` when `f` is not in `0..=100` (step 5).
pub fn to_fixed(x: f64, fraction_digits: i64) -> Result<String, RangeError> {
    let f = fraction_digits;
    // 4. and 5.: "If f is not finite, throw a RangeError"; "If f < 0 or
    //    f > 100, throw a RangeError".
    if !(0..=100).contains(&f) {
        return Err(RangeError);
    }
    // 6. "If x is not finite, return Number::toString(x, 10)."
    if !x.is_finite() {
        return Ok(number_to_string(x));
    }
    // 8. "If x < 0, then set s to "-" and x to -x."
    let neg = x < 0.0;
    let x = x.abs();
    // 9.b. "If x >= 10^21, then let m be ToString(𝔽(x))."
    if x >= 1e21 {
        return Ok(layout_sign(neg, &number_to_string(x)));
    }
    // 9.a.: "let n be an integer for which n / 10^f - x is as close to zero
    //    as possible. If there are two such n, pick the larger n."
    let n = scaled_round::<BIG_LIMBS_FORMAT>(x, f);
    let mut m = n.to_decimal();
    let f = usize::try_from(f).unwrap_or(0);
    // 10. "If f != 0, then let k be the length of m; if k <= f, then let z
    //     be f + 1 - k zeros and m = z + m (k = f + 1); let a be the first
    //     k - f code units of m and b the other f; m = a + "." + b."
    if f != 0 {
        let k = m.len();
        if k <= f {
            let zeros = "0".repeat(f.saturating_add(1).saturating_sub(k));
            m = format!("{zeros}{m}");
        }
        let split = m.len().saturating_sub(f);
        let a = m.get(..split).unwrap_or("");
        let b = m.get(split..).unwrap_or("");
        m = format!("{a}.{b}");
    }
    Ok(layout_sign(neg, &m))
}

fn layout_sign(neg: bool, m: &str) -> String {
    if neg { format!("-{m}") } else { m.to_string() }
}

/// Number.prototype.toExponential (§21.1.3.2†) of `x`, with
/// `fraction_digits` the integer `f` of step 2 (`None` for `undefined`).
///
/// # Errors
///
/// `RangeError` when `x` is finite and `f` is not in `0..=100` (step 5).
pub fn to_exponential(x: f64, fraction_digits: Option<i64>) -> Result<String, RangeError> {
    // 4. "If x is not finite, return Number::toString(x, 10)."
    if !x.is_finite() {
        return Ok(number_to_string(x));
    }
    let f = fraction_digits.unwrap_or(0);
    // 5. "If f < 0 or f > 100, throw a RangeError."
    if !(0..=100).contains(&f) {
        return Err(RangeError);
    }
    let neg = x < 0.0;
    let x = x.abs();
    let fu = usize::try_from(f).unwrap_or(0);
    let (m, e) = if x == 0.0 {
        // 9.a. "Let m be f + 1 occurrences of "0"." 9.b. "Let e be 0."
        ("0".repeat(fu.saturating_add(1)), 0)
    } else if fraction_digits.is_none() {
        // 10.b. "f is as small as possible": the shortest digits.
        match shortest_digits(x) {
            Some((d, e10)) => {
                let mut ds = String::new();
                push_u64(&mut ds, d, 0);
                let e = i64::from(e10)
                    .saturating_add(ds.len() as i64)
                    .saturating_sub(1);
                (ds, e)
            }
            None => return Ok("NaN".to_string()),
        }
    } else {
        // 10.a. the exact n and e.
        exponent_digits(x, u32::try_from(f.saturating_add(1)).unwrap_or(1))
    };
    let mut s = String::new();
    if neg {
        s.push('-');
    }
    // 11. "If f != 0, then let a be the first code unit of m and b the
    //     remaining f; m = a + "." + b."
    s.push_str(m.get(..1).unwrap_or(""));
    if f != 0 || (fraction_digits.is_none() && m.len() > 1) {
        s.push('.');
        s.push_str(m.get(1..).unwrap_or(""));
    }
    // 12. and 13.: "If e = 0, c is "+" and d is "0"; otherwise c is "+" or
    //     "-" and d the decimal digits of abs(e)." Then m + "e" + c + d.
    push_exponent(&mut s, e);
    Ok(s)
}

/// Number.prototype.toPrecision (§21.1.3.5†) of `x`, with `precision` the
/// integer `p` of step 4 (`None` for `undefined`, step 2).
///
/// # Errors
///
/// `RangeError` when `x` is finite and `p` is not in `1..=100` (step 6).
pub fn to_precision(x: f64, precision: Option<i64>) -> Result<String, RangeError> {
    // 2. "If precision is undefined, return ! ToString(x)."
    let Some(p) = precision else {
        return Ok(number_to_string(x));
    };
    // 5. "If x is not finite, return Number::toString(x, 10)."
    if !x.is_finite() {
        return Ok(number_to_string(x));
    }
    // 6. "If p < 1 or p > 100, throw a RangeError."
    if !(1..=100).contains(&p) {
        return Err(RangeError);
    }
    let neg = x < 0.0;
    let x = x.abs();
    let pu = usize::try_from(p).unwrap_or(1);
    let (m, e) = if x == 0.0 {
        // 9.a. "Let m be p occurrences of "0"." 9.b. "Let e be 0."
        ("0".repeat(pu), 0)
    } else {
        exponent_digits(x, u32::try_from(p).unwrap_or(1))
    };
    let mut s = String::new();
    if neg {
        s.push('-');
    }
    // 10.c. "If e < -6 or e >= p": exponential notation.
    if e < -6 || e >= p {
        s.push_str(m.get(..1).unwrap_or(""));
        if pu != 1 {
            s.push('.');
            s.push_str(m.get(1..).unwrap_or(""));
        }
        push_exponent(&mut s, e);
        return Ok(s);
    }
    // 11. "If e = p - 1, return s + m."
    if e == p.saturating_sub(1) {
        s.push_str(&m);
        return Ok(s);
    }
    if e >= 0 {
        // 12. "If e >= 0, m = the first e + 1 code units, ".", the rest."
        let at = usize::try_from(e.saturating_add(1)).unwrap_or(0);
        s.push_str(m.get(..at).unwrap_or(""));
        s.push('.');
        s.push_str(m.get(at..).unwrap_or(""));
    } else {
        // 13. "Else, m = "0." + -(e + 1) zeros + m."
        s.push_str("0.");
        for _ in 0..e.saturating_add(1).saturating_neg() {
            s.push('0');
        }
        s.push_str(&m);
    }
    Ok(s)
}
