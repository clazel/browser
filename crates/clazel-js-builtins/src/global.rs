//! The function and value properties of the global object (§19†):
//! `globalThis`, `isNaN`, `isFinite`, `parseInt`, `parseFloat`. (`undefined`,
//! `NaN` and `Infinity` are made by the VM.)

use crate::util::{METHOD, arg, define, method, number};
use clazel_js_heap::value::Value;
use clazel_js_number::parse::is_str_whitespace;
use clazel_js_vm::interp::{Abrupt, Vm};
use clazel_js_vm::numeric::{narrow, to_int32};

/// Installs the global functions.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    let g = vm.global();
    // §19.1.1†: `globalThis` is writable, not enumerable, configurable.
    define(vm, g, "globalThis", g, METHOD)?;
    method(vm, g, "isFinite", 1, is_finite)?;
    method(vm, g, "isNaN", 1, is_nan)?;
    let parse_float_fn = method(vm, g, "parseFloat", 1, parse_float)?;
    let parse_int_fn = method(vm, g, "parseInt", 2, parse_int)?;
    crate::number::share_parse_functions(vm, parse_float_fn, parse_int_fn)
}

/// `isNaN ( number )`, §19.2.3†:
/// 1. Let num be ? ToNumber(number).
/// 2. If num is NaN, return true.
/// 3. Otherwise, return false.
fn is_nan(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    Ok(Value::boolean(vm.to_number(arg(args, 0))?.is_nan()))
}

/// `isFinite ( number )`, §19.2.2†:
/// 1. Let num be ? ToNumber(number).
/// 2. If num is not finite, return false.
/// 3. Otherwise, return true.
fn is_finite(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    Ok(Value::boolean(vm.to_number(arg(args, 0))?.is_finite()))
}

/// TrimString ( string, start ), §22.1.3.32.1†, for the start only: the
/// text without its leading white space and line terminators
/// (`StrWhiteSpaceChar`).
fn trim_start(s: &str) -> &str {
    s.trim_start_matches(is_str_whitespace)
}

/// `parseFloat ( string )`, §19.2.4†:
/// 1. Let inputString be ? ToString(string).
/// 2. Let trimmedString be ! TrimString(inputString, start).
/// 3. Let trimmed be StringToCodePoints(trimmedString).
/// 4. Let trimmedPrefix be the longest prefix of trimmed that satisfies the
///    syntax of a StrDecimalLiteral, which might be trimmed itself. If there
///    is no such prefix, return NaN.
/// 5. Let parsedNumber be ParseText(trimmedPrefix, StrDecimalLiteral).
/// 6. Assert: parsedNumber is a Parse Node.
/// 7. Return StringNumericValue of parsedNumber.
fn parse_float(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let input = vm.to_js_string(arg(args, 0))?.to_string_lossy();
    let trimmed = trim_start(&input);
    let Some(prefix) = decimal_literal_prefix(trimmed) else {
        return Ok(Value::double(f64::NAN));
    };
    Ok(number(clazel_js_number::string_to_number(prefix)))
}

/// The longest prefix of `s` that is a StrDecimalLiteral (§7.1.4.1†): an
/// optional sign, then `Infinity`, or decimal digits with an optional point
/// and fraction (at least one digit in all) and an optional exponent that
/// has digits.
fn decimal_literal_prefix(s: &str) -> Option<&str> {
    let b = s.as_bytes();
    let mut i = 0usize;
    if matches!(b.first(), Some(b'+' | b'-')) {
        i = i.checked_add(1)?;
    }
    let rest = s.get(i..)?;
    if rest.starts_with("Infinity") {
        return s.get(..i.checked_add("Infinity".len())?);
    }
    let digits = |from: usize| -> usize {
        let mut j = from;
        while b.get(j).is_some_and(u8::is_ascii_digit) {
            j = j.saturating_add(1);
        }
        j
    };
    let int_end = digits(i);
    let mut end = int_end;
    let mut mantissa_digits = int_end.saturating_sub(i);
    if b.get(end) == Some(&b'.') {
        let frac_end = digits(end.saturating_add(1));
        let frac_digits = frac_end.saturating_sub(end.saturating_add(1));
        if mantissa_digits > 0 || frac_digits > 0 {
            end = frac_end;
            mantissa_digits = mantissa_digits.saturating_add(frac_digits);
        }
    }
    if mantissa_digits == 0 {
        return None;
    }
    if matches!(b.get(end), Some(b'e' | b'E')) {
        let mut j = end.saturating_add(1);
        if matches!(b.get(j), Some(b'+' | b'-')) {
            j = j.saturating_add(1);
        }
        let exp_end = digits(j);
        if exp_end > j {
            end = exp_end;
        }
    }
    s.get(..end)
}

/// `parseInt ( string, radix )`, §19.2.5†:
/// 1. Let inputString be ? ToString(string).
/// 2. Let S be ! TrimString(inputString, start).
/// 3. Let sign be 1.
/// 4. If S is not empty and the first code unit of S is the code unit
///    0x002D (HYPHEN-MINUS), set sign to -1.
/// 5. If S is not empty and the first code unit of S is either 0x002B (PLUS
///    SIGN) or 0x002D (HYPHEN-MINUS), set S to the substring of S from index 1.
/// 6. Let R be ℝ(? ToInt32(radix)).
/// 7. Let stripPrefix be true.
/// 8. If R ≠ 0, then
///    a. If R < 2 or R > 36, return NaN.
///    b. If R ≠ 16, set stripPrefix to false.
/// 9. Else, set R to 10.
/// 10. If stripPrefix is true, then
///     a. If the length of S is at least 2 and the first two code units of S
///     are either "0x" or "0X", then i. Set S to the substring of S from
///     index 2. ii. Set R to 16.
/// 11. If S contains a code unit that is not a radix-R digit, let end be the
///     index within S of the first such code unit; otherwise, let end be the
///     length of S.
/// 12. Let Z be the substring of S from 0 to end.
/// 13. If Z is empty, return NaN.
/// 14. Let mathInt be the integer value that is represented by Z in radix-R
///     notation.
/// 15. If mathInt = 0, then a. If sign = -1, return -0𝔽. b. Return +0𝔽.
/// 16. Return 𝔽(sign × mathInt).
///
/// The integer is exact (correctly rounded to a Number) up to 2^128; beyond
/// that digits accumulate in an `f64`, which §19.2.5† permits for radixes
/// other than 2, 4, 8, 10, 16 and 32 after 20 significant digits and
/// this slice accepts for the rest.
fn parse_int(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let input = vm.to_js_string(arg(args, 0))?.to_string_lossy();
    let mut s = trim_start(&input);
    let mut sign = 1.0_f64;
    if s.starts_with('-') {
        sign = -1.0;
    }
    if s.starts_with(['+', '-']) {
        s = s.get(1..).unwrap_or("");
    }
    let radix_arg = vm.to_number(arg(args, 1))?;
    let mut r = to_int32(narrow(radix_arg));
    let mut strip_prefix = true;
    if r != 0 {
        if !(2..=36).contains(&r) {
            return Ok(Value::double(f64::NAN));
        }
        if r != 16 {
            strip_prefix = false;
        }
    } else {
        r = 10;
    }
    if strip_prefix && (s.starts_with("0x") || s.starts_with("0X")) {
        s = s.get(2..).unwrap_or("");
        r = 16;
    }
    let radix = u32::try_from(r).unwrap_or(10);
    let end = s
        .char_indices()
        .find(|(_, c)| !c.is_digit(radix))
        .map_or(s.len(), |(i, _)| i);
    let z = s.get(..end).unwrap_or("");
    if z.is_empty() {
        return Ok(Value::double(f64::NAN));
    }
    let math_int = if radix == 10 {
        // Correctly rounded for any number of digits.
        clazel_js_number::string_to_number(z)
    } else {
        let mut exact: Option<u128> = Some(0);
        let mut approx = 0.0_f64;
        for c in z.chars() {
            let d = c.to_digit(radix).unwrap_or(0);
            exact =
                exact.and_then(|v| v.checked_mul(u128::from(radix))?.checked_add(u128::from(d)));
            approx = approx * f64::from(radix) + f64::from(d);
        }
        exact.map_or(approx, |v| v as f64)
    };
    if math_int == 0.0 {
        return Ok(number(if sign < 0.0 { -0.0 } else { 0.0 }));
    }
    Ok(number(sign * math_int))
}
