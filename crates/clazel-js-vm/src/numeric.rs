//! The fast paths on Numbers: `spec::arith_*`, the bitwise and shift ops and
//! the relational ops of [`crate::spec`], written as executable code over
//! [`Value`].
//!
//! The encoding rule is the spec's ("int32 and double encodings of one Number
//! are both Numbers"): an arithmetic op returns an int32 exactly when both
//! operands are int32 and the exact result is an int32 and not `-0`, and a
//! double otherwise; the bitwise ops return an int32, `>>>` the int32 when
//! the result fits and a double otherwise, `/` always a double.

use clazel_js_heap::value::{Decoded, Value};

/// A Number operand, in the encoding it has in a register.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Num {
    /// An int32 value.
    I(i32),
    /// A double value.
    D(f64),
}

impl Num {
    /// The Number as a double (`spec::num_bits`).
    #[must_use]
    pub fn to_f64(self) -> f64 {
        match self {
            Num::I(i) => f64::from(i),
            Num::D(d) => d,
        }
    }
}

/// The Number a value is, if it is one (`spec::is_number`).
#[must_use]
pub fn num(v: Value) -> Option<Num> {
    match v.decode() {
        Decoded::Int32(i) => Some(Num::I(i)),
        Decoded::Double(d) => Some(Num::D(d)),
        _ => None,
    }
}

/// The value for an integral result: an int32 when it fits, else the double
/// (`spec::enc_number_int`, for `|n| < 2^53`).
#[must_use]
pub fn number_from_i64(n: i64) -> Value {
    match i32::try_from(n) {
        Ok(i) => Value::int32(i),
        // Exact: callers pass |n| < 2^53.
        Err(_) => Value::double(n as f64),
    }
}

/// The Number `d` as an int32 encoding when it is an integer in range other
/// than `-0` (the same Number, in the encoding the arithmetic ops keep
/// narrow), else a double.
#[must_use]
pub fn narrow(d: f64) -> Num {
    if d == d.trunc() && d.abs() < 2_147_483_648.0 && !(d == 0.0 && d.is_sign_negative()) {
        // Integral, in range and not -0: exact.
        Num::I(d as i32)
    } else {
        Num::D(d)
    }
}

/// `a + b` (`spec::arith_add`).
#[must_use]
pub fn add(a: Num, b: Num) -> Value {
    if let (Num::I(x), Num::I(y)) = (a, b)
        && let Some(r) = x.checked_add(y)
    {
        return Value::int32(r);
    }
    Value::double(a.to_f64() + b.to_f64())
}

/// `a - b` (`spec::arith_sub`).
#[must_use]
pub fn sub(a: Num, b: Num) -> Value {
    if let (Num::I(x), Num::I(y)) = (a, b)
        && let Some(r) = x.checked_sub(y)
    {
        return Value::int32(r);
    }
    Value::double(a.to_f64() - b.to_f64())
}

/// `a * b` (`spec::arith_mul`): a zero product with a negative operand is
/// `-0`, which no int32 is.
#[must_use]
pub fn mul(a: Num, b: Num) -> Value {
    if let (Num::I(x), Num::I(y)) = (a, b)
        && let Some(r) = x.checked_mul(y)
        && !(r == 0 && (x < 0 || y < 0))
    {
        return Value::int32(r);
    }
    Value::double(a.to_f64() * b.to_f64())
}

/// `a / b` (`spec::arith_div`): always a double.
#[must_use]
pub fn div(a: Num, b: Num) -> Value {
    Value::double(a.to_f64() / b.to_f64())
}

/// `a % b` (`spec::arith_mod`): the int32 remainder unless the divisor is
/// zero or the result is a zero from a negative dividend (`-0`); a double is
/// C's `fmod`, which is Rust's `%` on `f64`.
#[must_use]
pub fn rem(a: Num, b: Num) -> Value {
    if let (Num::I(x), Num::I(y)) = (a, b)
        && let Some(r) = x.checked_rem(y)
        && !(r == 0 && x < 0)
    {
        return Value::int32(r);
    }
    Value::double(a.to_f64() % b.to_f64())
}

/// `-a` (`spec::arith_neg`): `-0` is not an int32 and `-(-2^31)` does not fit.
#[must_use]
pub fn neg(a: Num) -> Value {
    if let Num::I(x) = a
        && x != 0
        && let Some(r) = x.checked_neg()
    {
        return Value::int32(r);
    }
    Value::double(-a.to_f64())
}

/// `a + 1` (`spec::arith_inc`).
#[must_use]
pub fn inc(a: Num) -> Value {
    add(a, Num::I(1))
}

/// `a - 1` (`spec::arith_dec`).
#[must_use]
pub fn dec(a: Num) -> Value {
    sub(a, Num::I(1))
}

/// ToInt32, §7.1.6 (`spec::to_int32`).
#[must_use]
pub fn to_int32(a: Num) -> i32 {
    match a {
        Num::I(i) => i,
        Num::D(d) => {
            if !d.is_finite() || d == 0.0 {
                return 0;
            }
            // The integral part modulo 2^32, exactly (a remainder of integers
            // below 2^53 in magnitude), as an unsigned 32-bit pattern.
            let m = d.trunc().rem_euclid(4_294_967_296.0);
            // 0 <= m < 2^32, so the conversion is exact.
            (m as u32) as i32
        }
    }
}

/// ToUint32, §7.1.7 (`spec::to_uint32`).
#[must_use]
pub fn to_uint32(a: Num) -> u32 {
    to_int32(a) as u32
}

/// `a & b`.
#[must_use]
pub fn bit_and(a: Num, b: Num) -> Value {
    Value::int32(to_int32(a) & to_int32(b))
}

/// `a | b`.
#[must_use]
pub fn bit_or(a: Num, b: Num) -> Value {
    Value::int32(to_int32(a) | to_int32(b))
}

/// `a ^ b`.
#[must_use]
pub fn bit_xor(a: Num, b: Num) -> Value {
    Value::int32(to_int32(a) ^ to_int32(b))
}

/// `a << b`: the shift count is `ToUint32(b) mod 32`.
#[must_use]
pub fn shl(a: Num, b: Num) -> Value {
    let n = to_uint32(b) & 31;
    Value::int32(to_int32(a).wrapping_shl(n))
}

/// `a >> b`, sign-extending.
#[must_use]
pub fn shr(a: Num, b: Num) -> Value {
    let n = to_uint32(b) & 31;
    Value::int32(to_int32(a).wrapping_shr(n))
}

/// `a >>> b`, zero-filling: the int32 when the result fits, else a double.
#[must_use]
pub fn ushr(a: Num, b: Num) -> Value {
    let n = to_uint32(b) & 31;
    number_from_i64(i64::from(to_uint32(a).wrapping_shr(n)))
}

/// `~a`.
#[must_use]
pub fn bit_not(a: Num) -> Value {
    Value::int32(!to_int32(a))
}

/// `a < b` on Numbers (`spec::rel_lt`): false when either is NaN.
#[must_use]
pub fn lt(a: Num, b: Num) -> bool {
    a.to_f64() < b.to_f64()
}

/// `a <= b` (`spec::rel_le`).
#[must_use]
pub fn le(a: Num, b: Num) -> bool {
    a.to_f64() <= b.to_f64()
}

/// `a > b` (`spec::rel_gt`).
#[must_use]
pub fn gt(a: Num, b: Num) -> bool {
    a.to_f64() > b.to_f64()
}

/// `a >= b` (`spec::rel_ge`).
#[must_use]
pub fn ge(a: Num, b: Num) -> bool {
    a.to_f64() >= b.to_f64()
}

/// Number::equal, §6.1.6.1.13: `-0` equals `+0`, NaN equals nothing.
#[must_use]
pub fn equal(a: Num, b: Num) -> bool {
    a.to_f64() == b.to_f64()
}

/// Number::exponentiate, §6.1.6.1.3.
#[must_use]
pub fn exponentiate(base: f64, exponent: f64) -> f64 {
    if exponent.is_nan() {
        return f64::NAN;
    }
    if exponent == 0.0 {
        return 1.0;
    }
    // Step 6 and 9: a base of magnitude 1 with an infinite exponent is NaN
    // (`powf` gives 1).
    if exponent.is_infinite() && base.abs() == 1.0 {
        return f64::NAN;
    }
    base.powf(exponent)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn int32_overflow_goes_to_double() {
        let max = Num::I(i32::MAX);
        assert_eq!(add(max, Num::I(1)), Value::double(2_147_483_648.0));
        assert_eq!(
            sub(Num::I(i32::MIN), Num::I(1)),
            Value::double(-2_147_483_649.0)
        );
        assert_eq!(mul(max, Num::I(2)), Value::double(4_294_967_294.0));
        assert_eq!(neg(Num::I(i32::MIN)), Value::double(2_147_483_648.0));
        assert_eq!(add(Num::I(2), Num::I(3)), Value::int32(5));
    }

    #[test]
    fn negative_zero_is_a_double() {
        assert_eq!(mul(Num::I(0), Num::I(-5)), Value::double(-0.0));
        assert_eq!(mul(Num::I(-5), Num::I(0)), Value::double(-0.0));
        assert_eq!(mul(Num::I(0), Num::I(5)), Value::int32(0));
        assert_eq!(neg(Num::I(0)), Value::double(-0.0));
        assert_eq!(rem(Num::I(-4), Num::I(2)), Value::double(-0.0));
        assert_eq!(rem(Num::I(i32::MIN), Num::I(-1)), Value::double(-0.0));
        assert_eq!(rem(Num::I(5), Num::I(0)), Value::double(f64::NAN));
    }

    #[test]
    fn the_bitwise_ops_follow_to_int32() {
        assert_eq!(to_int32(Num::D(4_294_967_296.0 + 5.0)), 5);
        assert_eq!(to_int32(Num::D(-1.5)), -1);
        assert_eq!(to_int32(Num::D(f64::NAN)), 0);
        assert_eq!(to_int32(Num::D(2_147_483_648.0)), i32::MIN);
        assert_eq!(shl(Num::I(1), Num::I(33)), Value::int32(2));
        assert_eq!(shr(Num::I(-8), Num::I(1)), Value::int32(-4));
        assert_eq!(ushr(Num::I(-1), Num::I(0)), Value::double(4_294_967_295.0));
        assert_eq!(ushr(Num::I(-1), Num::I(1)), Value::int32(i32::MAX));
        assert_eq!(bit_not(Num::I(0)), Value::int32(-1));
    }

    #[test]
    #[cfg_attr(miri, ignore = "Miri deliberately perturbs libm results such as powf")]
    fn exponentiation_special_cases() {
        assert!(exponentiate(1.0, f64::INFINITY).is_nan());
        assert_eq!(exponentiate(f64::NAN, 0.0), 1.0);
        assert_eq!(exponentiate(2.0, 10.0), 1024.0);
    }
}
