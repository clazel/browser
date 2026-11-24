//! `Math` (§21.3†): the constants and the pure functions `abs`, `floor`,
//! `ceil`, `round`, `trunc`, `sign`, `min`, `max`, `pow`, `sqrt`.
//!
//! Each result is exact or the correctly rounded value, as Rust's `f64`
//! methods are: `floor`, `ceil`, `trunc` and `abs` are exact, and `sqrt` is
//! the IEEE 754 correctly rounded square root. `pow` is
//! `Number::exponentiate` (§6.1.6.1.3†) as the VM's `numeric` module has
//! it, over the C library's `pow`, which is not specified to be correctly
//! rounded (§21.3†: "the choice of algorithms is implementation-approximated"
//! for these).

use crate::util::{CONSTANT, arg, define, method, new_plain, number};
use clazel_js_heap::value::Value;
use clazel_js_vm::interp::{Abrupt, Vm};
use clazel_js_vm::numeric::exponentiate;

/// Installs `Math`.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    let math = new_plain(vm)?;
    // §21.3.1†: value properties, not writable, enumerable or configurable.
    for (name, v) in [
        ("E", std::f64::consts::E),
        ("LN10", std::f64::consts::LN_10),
        ("LN2", std::f64::consts::LN_2),
        ("LOG10E", std::f64::consts::LOG10_E),
        ("LOG2E", std::f64::consts::LOG2_E),
        ("PI", std::f64::consts::PI),
        ("SQRT1_2", std::f64::consts::FRAC_1_SQRT_2),
        ("SQRT2", std::f64::consts::SQRT_2),
    ] {
        define(vm, math, name, number(v), CONSTANT)?;
    }
    method(vm, math, "abs", 1, abs)?;
    method(vm, math, "ceil", 1, ceil)?;
    method(vm, math, "floor", 1, floor)?;
    method(vm, math, "max", 2, max)?;
    method(vm, math, "min", 2, min)?;
    method(vm, math, "pow", 2, pow)?;
    method(vm, math, "round", 1, round)?;
    method(vm, math, "sign", 1, sign)?;
    method(vm, math, "sqrt", 1, sqrt)?;
    method(vm, math, "trunc", 1, trunc)?;
    crate::util::global(vm, "Math", math)
}

/// The first argument as a Number: `Let n be ? ToNumber(x)`.
fn arg_number(vm: &mut Vm, args: &[Value]) -> Result<f64, Abrupt> {
    vm.to_number(arg(args, 0))
}

/// `Math.abs ( x )`, §21.3.2.1†: the magnitude of n; `abs(-0)` is `+0`.
fn abs(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    Ok(number(arg_number(vm, args)?.abs()))
}

/// `Math.ceil ( x )`, §21.3.2.10†: the smallest integral Number not less
/// than n; NaN, the infinities and the zeros are themselves.
fn ceil(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    Ok(number(arg_number(vm, args)?.ceil()))
}

/// `Math.floor ( x )`, §21.3.2.16†: the greatest integral Number not greater
/// than n.
fn floor(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    Ok(number(arg_number(vm, args)?.floor()))
}

/// `Math.trunc ( x )`, §21.3.2.35†: the integral part, toward zero.
fn trunc(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    Ok(number(arg_number(vm, args)?.trunc()))
}

/// `Math.sqrt ( x )`, §21.3.2.32†: NaN for NaN and a negative n, `-0` for
/// `-0`, else the square root.
fn sqrt(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    Ok(number(arg_number(vm, args)?.sqrt()))
}

/// `Math.sign ( x )`, §21.3.2.29†:
/// 3. If n is one of NaN, +0𝔽, or -0𝔽, return n.
/// 4. If n < -0𝔽, return -1𝔽.
/// 5. Return 1𝔽.
fn sign(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let n = arg_number(vm, args)?;
    Ok(number(if n.is_nan() || n == 0.0 {
        n
    } else if n < 0.0 {
        -1.0
    } else {
        1.0
    }))
}

/// `Math.round ( x )`, §21.3.2.28†:
/// 3. If n is not finite or n is an integral Number, return n.
/// 4. If n < 0.5𝔽 and n > +0𝔽, return +0𝔽.
/// 5. If n < -0𝔽 and n ≥ -0.5𝔽, return -0𝔽.
/// 6. Return the integral Number closest to n, preferring the one closer to
///    +∞ in the case of a tie.
///
/// `n - floor(n)` is exact for a Number that is not integral, so the tie
/// test is exact (`floor(n + 0.5)` is not: it rounds `0.49999999999999994`
/// up).
fn round(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let n = arg_number(vm, args)?;
    if !n.is_finite() || n.trunc() == n {
        return Ok(number(n));
    }
    let r = n.floor();
    let rounded = if n - r >= 0.5 { r + 1.0 } else { r };
    // A negative Number that rounds to zero is -0 (step 5).
    Ok(number(if rounded == 0.0 && n < 0.0 {
        -0.0
    } else {
        rounded
    }))
}

/// `Math.pow ( base, exponent )`, §21.3.2.26†:
/// 1. Set base to ? ToNumber(base).
/// 2. Set exponent to ? ToNumber(exponent).
/// 3. Return Number::exponentiate(base, exponent).
fn pow(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let base = vm.to_number(arg(args, 0))?;
    let exponent = vm.to_number(arg(args, 1))?;
    Ok(number(exponentiate(base, exponent)))
}

/// `Math.max ( ...args )`, §21.3.2.24†:
/// 1. Let coerced be a new empty List.
/// 2. For each element arg of args, do
///    a. Let n be ? ToNumber(arg).
///    b. Append n to coerced.
/// 3. Let highest be -∞𝔽.
/// 4. For each element number of coerced, do
///    a. If number is NaN, return NaN.
///    b. If number is +0𝔽 and highest is -0𝔽, set highest to +0𝔽.
///    c. If number > highest, set highest to number.
/// 5. Return highest.
fn max(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let mut coerced = Vec::with_capacity(args.len());
    for a in args {
        coerced.push(vm.to_number(*a)?);
    }
    let mut highest = f64::NEG_INFINITY;
    for n in coerced {
        if n.is_nan() {
            return Ok(Value::double(f64::NAN));
        }
        if n == 0.0 && n.is_sign_positive() && highest == 0.0 && highest.is_sign_negative() {
            highest = 0.0;
        }
        if n > highest {
            highest = n;
        }
    }
    Ok(number(highest))
}

/// `Math.min ( ...args )`, §21.3.2.25†: as `max`, with `+∞` to start, `-0`
/// preferred over `+0`, and the lesser Number kept.
fn min(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let mut coerced = Vec::with_capacity(args.len());
    for a in args {
        coerced.push(vm.to_number(*a)?);
    }
    let mut lowest = f64::INFINITY;
    for n in coerced {
        if n.is_nan() {
            return Ok(Value::double(f64::NAN));
        }
        if n == 0.0 && n.is_sign_negative() && lowest == 0.0 {
            lowest = -0.0;
        }
        if n < lowest {
            lowest = n;
        }
    }
    Ok(number(lowest))
}
