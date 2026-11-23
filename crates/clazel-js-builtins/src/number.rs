//! `Number` (§21.1†): the constructor, its constants and predicates, and
//! `Number.prototype.toString`, `toFixed`, `valueOf`.

use crate::util::{
    CONSTANT, arg, as_number, constructor, define, method, number, string, to_integer_or_infinity,
};
use clazel_js_heap::value::Value;
use clazel_js_vm::heap::ObjKind;
use clazel_js_vm::interp::{Abrupt, Intrinsic, Vm};

/// Installs `Number` and `Number.prototype`.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    // §21.1.4†: the prototype is itself a Number object whose [[NumberData]]
    // is +0.
    let object_proto = vm.intrinsic(Intrinsic::ObjectPrototype);
    let proto = vm.new_wrapper(Value::int32(0), object_proto)?;
    vm.set_intrinsic(Intrinsic::NumberPrototype, proto);
    let ctor = constructor(vm, "Number", 1, number_constructor, proto)?;
    // §21.1.2† value properties: not writable, not enumerable, not
    // configurable.
    for (name, v) in [
        ("EPSILON", f64::EPSILON),
        ("MAX_SAFE_INTEGER", 9_007_199_254_740_991.0),
        ("MAX_VALUE", f64::MAX),
        ("MIN_SAFE_INTEGER", -9_007_199_254_740_991.0),
        // 5e-324, the smallest positive subnormal.
        ("MIN_VALUE", f64::from_bits(1)),
        ("NaN", f64::NAN),
        ("NEGATIVE_INFINITY", f64::NEG_INFINITY),
        ("POSITIVE_INFINITY", f64::INFINITY),
    ] {
        define(vm, ctor, name, number(v), CONSTANT)?;
    }
    method(vm, ctor, "isFinite", 1, is_finite)?;
    method(vm, ctor, "isInteger", 1, is_integer)?;
    method(vm, ctor, "isNaN", 1, is_nan)?;
    method(vm, ctor, "isSafeInteger", 1, is_safe_integer)?;
    method(vm, proto, "toFixed", 1, to_fixed)?;
    method(vm, proto, "toString", 1, to_string)?;
    method(vm, proto, "valueOf", 0, value_of)?;
    crate::util::global(vm, "Number", ctor)
}

/// Makes `Number.parseFloat` and `Number.parseInt` the same function
/// objects as the globals (§21.1.2.12†, §21.1.2.13†); [`crate::global`] calls
/// it once those exist.
///
/// # Errors
/// As [`crate::install`].
pub fn share_parse_functions(
    vm: &mut Vm,
    parse_float: Value,
    parse_int: Value,
) -> Result<(), Abrupt> {
    let g = vm.global();
    let kn = crate::util::key(vm, "Number")?;
    let ctor = vm.get_value(g, kn)?;
    crate::util::define(vm, ctor, "parseFloat", parse_float, crate::util::METHOD)?;
    crate::util::define(vm, ctor, "parseInt", parse_int, crate::util::METHOD)
}

/// `Number ( value )`, §21.1.1.1†:
/// 1. If value is present, then
///    a. Let prim be ? ToNumeric(value).
///    b. If prim is a BigInt, let n be 𝔽(ℝ(prim)). (No BigInt yet.)
///    c. Otherwise, let n be prim.
/// 2. Else, let n be +0𝔽.
/// 3. If NewTarget is undefined, return n.
/// 4. Let O be ? OrdinaryCreateFromConstructor(NewTarget,
///    "%Number.prototype%", « [[NumberData]] »).
/// 5. Set O.[[NumberData]] to n.
/// 6. Return O.
fn number_constructor(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let n = match args.first() {
        Some(v) => number(vm.to_number(*v)?),
        None => Value::int32(0),
    };
    let nt = vm.new_target();
    if nt == Value::UNDEFINED {
        return Ok(n);
    }
    vm.create_from_constructor(nt, Intrinsic::NumberPrototype, ObjKind::Primitive(n))
}

/// `Number.isFinite ( number )`, §21.1.2.2†: a Number that is neither NaN nor
/// an infinity.
fn is_finite(_vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    Ok(Value::boolean(
        as_number(arg(args, 0)).is_some_and(f64::is_finite),
    ))
}

/// `Number.isInteger ( number )`, §21.1.2.3†: IsIntegralNumber, §7.2.6†: a
/// finite Number equal to its truncation.
fn is_integer(_vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    Ok(Value::boolean(
        as_number(arg(args, 0)).is_some_and(|n| n.is_finite() && n.trunc() == n),
    ))
}

/// `Number.isNaN ( number )`, §21.1.2.4†: a Number that is NaN.
fn is_nan(_vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    Ok(Value::boolean(
        as_number(arg(args, 0)).is_some_and(f64::is_nan),
    ))
}

/// `Number.isSafeInteger ( number )`, §21.1.2.5†: an integral Number whose
/// magnitude is at most 2^53 - 1.
fn is_safe_integer(_vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    Ok(Value::boolean(as_number(arg(args, 0)).is_some_and(|n| {
        n.is_finite() && n.trunc() == n && n.abs() <= 9_007_199_254_740_991.0
    })))
}

/// thisNumberValue ( value ), §21.1.3.7.1†:
/// 1. If value is a Number, return value.
/// 2. If value is an Object and value has a [[NumberData]] internal slot,
///    then return value.[[NumberData]].
/// 3. Throw a TypeError exception.
fn this_number_value(vm: &mut Vm, v: Value) -> Result<f64, Abrupt> {
    if let Some(n) = as_number(v) {
        return Ok(n);
    }
    if let Some(ObjKind::Primitive(p)) = vm.heap().obj(v).map(|o| o.kind)
        && let Some(n) = as_number(p)
    {
        return Ok(n);
    }
    Err(vm.type_error("not a Number"))
}

/// `Number.prototype.valueOf ( )`, §21.1.3.7†:
/// 1. Return ? thisNumberValue(this value).
fn value_of(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    Ok(number(this_number_value(vm, this)?))
}

/// `Number.prototype.toFixed ( fractionDigits )`, §21.1.3.3†:
/// 1. Let x be ? thisNumberValue(this value).
/// 2. Let f be ? ToIntegerOrInfinity(fractionDigits).
/// 3. Assert: If fractionDigits is undefined, then f is 0.
/// 4. If f is not finite, throw a RangeError exception.
/// 5. If f < 0 or f > 100, throw a RangeError exception.
/// 6. If x is not finite, return Number::toString(x, 10).
/// - Steps 7 to 13, the digits: `clazel-js-number`'s `to_fixed`.
fn to_fixed(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let x = this_number_value(vm, this)?;
    let f = to_integer_or_infinity(vm, arg(args, 0))?;
    if !f.is_finite() || !(0.0..=100.0).contains(&f) {
        return Err(vm.range_error("toFixed() digits argument must be between 0 and 100"));
    }
    if !x.is_finite() {
        return string(vm, &clazel_js_number::number_to_string(x));
    }
    match clazel_js_number::to_fixed(x, f as i64) {
        Ok(s) => string(vm, &s),
        Err(_) => Err(vm.range_error("toFixed() digits argument must be between 0 and 100")),
    }
}

/// `Number.prototype.toString ( [ radix ] )`, §21.1.3.6†:
/// 1. Let x be ? thisNumberValue(this value).
/// 2. If radix is undefined, let radixMV be 10.
/// 3. Else, let radixMV be ? ToIntegerOrInfinity(radix).
/// 4. If radixMV is not in the inclusive interval from 2 to 36, throw a
///    RangeError exception.
/// 5. Return Number::toString(x, radixMV).
fn to_string(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let x = this_number_value(vm, this)?;
    let radix = match arg(args, 0) {
        r if r == Value::UNDEFINED => 10.0,
        r => to_integer_or_infinity(vm, r)?,
    };
    if !(2.0..=36.0).contains(&radix) {
        return Err(vm.range_error("toString() radix must be between 2 and 36"));
    }
    let text = if radix == 10.0 {
        clazel_js_number::number_to_string(x)
    } else {
        radix_string(x, radix as u32)
    };
    string(vm, &text)
}

/// Number::toString ( x, radix ), §6.1.6.1.20†, for a radix other than 10:
/// NaN, the zeros and the infinities as for radix 10; otherwise the sign,
/// the integer part's digits and, for a fraction, a point and its digits.
/// The standard leaves the digits of radixes other than 10 to the
/// implementation ("the algorithm is implementation-approximated"); here the
/// integer part is divided down exactly (`fmod` is exact, and the quotient is
/// exact for the power-of-two radixes) and the fraction takes digits until it
/// is spent or 52 have been produced.
fn radix_string(x: f64, radix: u32) -> String {
    if x.is_nan() || x.is_infinite() || x == 0.0 {
        return clazel_js_number::number_to_string(x);
    }
    let digit = |d: u32| char::from_digit(d, 36).unwrap_or('0');
    let r = f64::from(radix);
    let neg = x < 0.0;
    let x = x.abs();
    let mut int = x.trunc();
    let mut frac = x - int;
    let mut int_digits: Vec<char> = Vec::new();
    if int == 0.0 {
        int_digits.push('0');
    }
    while int > 0.0 {
        let d = int % r;
        int_digits.push(digit(d as u32));
        int = ((int - d) / r).trunc();
    }
    int_digits.reverse();
    let mut out = String::new();
    if neg {
        out.push('-');
    }
    out.extend(int_digits);
    if frac > 0.0 {
        out.push('.');
        for _ in 0..52 {
            frac *= r;
            let d = frac.trunc();
            out.push(digit(d as u32));
            frac -= d;
            if frac <= 0.0 {
                break;
            }
        }
    }
    out
}
