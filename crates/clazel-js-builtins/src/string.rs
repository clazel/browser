//! `String` (§22.1†): the constructor, `String.fromCharCode`, and
//! `String.prototype.toString`, `valueOf`, `charAt`, `charCodeAt`,
//! `indexOf`, `slice`, `substring`.

use crate::util::{
    CONSTANT, arg, constructor, define, js_string, method, number, require_object_coercible,
    string, to_integer_or_infinity,
};
use clazel_js_heap::string::JsString;
use clazel_js_heap::value::Value;
use clazel_js_vm::heap::ObjKind;
use clazel_js_vm::interp::{Abrupt, Intrinsic, Vm};

/// Installs `String` and `String.prototype`.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    // §22.1.3†: the prototype is itself a String object whose [[StringData]]
    // is the empty String.
    let object_proto = vm.intrinsic(Intrinsic::ObjectPrototype);
    let empty = string(vm, "")?;
    let proto = vm.new_wrapper(empty, object_proto)?;
    vm.set_intrinsic(Intrinsic::StringPrototype, proto);
    let ctor = constructor(vm, "String", 1, string_constructor, proto)?;
    method(vm, ctor, "fromCharCode", 1, from_char_code)?;
    method(vm, proto, "charAt", 1, char_at)?;
    method(vm, proto, "charCodeAt", 1, char_code_at)?;
    method(vm, proto, "indexOf", 1, index_of)?;
    method(vm, proto, "slice", 2, slice)?;
    method(vm, proto, "substring", 2, substring)?;
    method(vm, proto, "toString", 0, to_string)?;
    method(vm, proto, "valueOf", 0, value_of)?;
    crate::util::global(vm, "String", ctor)
}

/// `String ( value )`, §22.1.1.1†:
/// 1. If value is not present, let s be the empty String.
/// 2. Else,
///    a. If NewTarget is undefined and value is a Symbol, return
///    SymbolDescriptiveString(value). (No Symbols yet.)
///    b. Let s be ? ToString(value).
/// 3. If NewTarget is undefined, return s.
/// 4. Return StringCreate(s, ? GetPrototypeFromConstructor(NewTarget,
///    "%String.prototype%")).
fn string_constructor(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = match args.first() {
        Some(v) => {
            let s = vm.to_js_string(*v)?;
            js_string(vm, s)?
        }
        None => string(vm, "")?,
    };
    let nt = vm.new_target();
    if nt == Value::UNDEFINED {
        return Ok(s);
    }
    // StringCreate, §10.4.3.4†: the String exotic object, with `length`.
    let o = vm.create_from_constructor(nt, Intrinsic::StringPrototype, ObjKind::Primitive(s))?;
    let len = vm.heap().string(s).map_or(0, JsString::len);
    let len = i32::try_from(len).map_err(|_| Abrupt::OutOfMemory)?;
    define(vm, o, "length", Value::int32(len), CONSTANT)?;
    Ok(o)
}

/// `String.fromCharCode ( ...codeUnits )`, §22.1.2.1†:
/// 1. Let result be the empty String.
/// 2. For each element next of codeUnits, do
///    a. Let nextCU be the code unit whose numeric value is ℝ(? ToUint16(next)).
///    b. Set result to the string-concatenation of result and nextCU.
/// 3. Return result.
fn from_char_code(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let mut units = Vec::with_capacity(args.len());
    for a in args {
        let n = vm.to_number(*a)?;
        // ToUint16, §7.1.9†: truncate, then modulo 2^16.
        let unit = if n.is_finite() {
            (n.trunc().rem_euclid(65536.0)) as u16
        } else {
            0
        };
        units.push(unit);
    }
    let s = JsString::from_units(&units).map_err(|_| Abrupt::OutOfMemory)?;
    js_string(vm, s)
}

/// thisStringValue ( value ), §22.1.3.35.1†:
/// 1. If value is a String, return value.
/// 2. If value is an Object and value has a [[StringData]] internal slot,
///    then return value.[[StringData]].
/// 3. Throw a TypeError exception.
fn this_string_value(vm: &mut Vm, v: Value) -> Result<Value, Abrupt> {
    if vm.heap().is_string(v) {
        return Ok(v);
    }
    if let Some(ObjKind::Primitive(p)) = vm.heap().obj(v).map(|o| o.kind)
        && vm.heap().is_string(p)
    {
        return Ok(p);
    }
    Err(vm.type_error("not a String"))
}

/// `String.prototype.toString ( )`, §22.1.3.28†:
/// 1. Return ? thisStringValue(this value).
fn to_string(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    this_string_value(vm, this)
}

/// `String.prototype.valueOf ( )`, §22.1.3.35†:
/// 1. Return ? thisStringValue(this value).
fn value_of(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    this_string_value(vm, this)
}

/// The first steps of every method below:
/// 1. Let O be ? RequireObjectCoercible(this value).
/// 2. Let S be ? ToString(O).
fn this_string(vm: &mut Vm, this: Value, method: &str) -> Result<JsString, Abrupt> {
    require_object_coercible(vm, this, &format!("String.prototype.{method}"))?;
    vm.to_js_string(this)
}

/// The length of a string as `f64`.
fn len_of(s: &JsString) -> f64 {
    s.len() as f64
}

/// `String.prototype.charAt ( pos )`, §22.1.3.2†:
/// 1 and 2. As above.
/// 3. Let position be ? ToIntegerOrInfinity(pos).
/// 4. Let size be the length of S.
/// 5. If position < 0 or position ≥ size, return the empty String.
/// 6. Return the substring of S from position to position + 1.
fn char_at(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "charAt")?;
    let position = to_integer_or_infinity(vm, arg(args, 0))?;
    if position < 0.0 || position >= len_of(&s) {
        return string(vm, "");
    }
    let i = position as usize;
    js_string(vm, s.substring(i, i.saturating_add(1)))
}

/// `String.prototype.charCodeAt ( pos )`, §22.1.3.3†:
/// 1 and 2. As above.
/// 3. Let position be ? ToIntegerOrInfinity(pos).
/// 4. Let size be the length of S.
/// 5. If position < 0 or position ≥ size, return NaN.
/// 6. Return the Number value for the numeric value of the code unit at
///    index position within the String S.
fn char_code_at(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "charCodeAt")?;
    let position = to_integer_or_infinity(vm, arg(args, 0))?;
    if position < 0.0 || position >= len_of(&s) {
        return Ok(Value::double(f64::NAN));
    }
    let unit = s.unit(position as usize).unwrap_or(0);
    Ok(Value::int32(i32::from(unit)))
}

/// `String.prototype.indexOf ( searchString [ , position ] )`, §22.1.3.9†:
/// 1 and 2. As above.
/// 3. Let searchStr be ? ToString(searchString).
/// 4. Let pos be ? ToIntegerOrInfinity(position).
/// 5. Assert: If position is undefined, then pos is 0.
/// 6. Let len be the length of S.
/// 7. Let start be the result of clamping pos between 0 and len.
/// 8. Let result be StringIndexOf(S, searchStr, start).
/// 9. If result is not-found, return -1𝔽.
/// 10. Return 𝔽(result).
///
/// StringIndexOf ( string, searchValue, fromIndex ), §22.1.3.?†:
/// 3. If searchValue is the empty String and fromIndex ≤ len, return
///    fromIndex.
/// 5 to 8. For each i from fromIndex to len - searchLen, if the substring of
///    string from i to i + searchLen is searchValue, return i.
/// 9. Return not-found.
fn index_of(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "indexOf")?;
    let search = vm.to_js_string(arg(args, 0))?;
    let pos = to_integer_or_infinity(vm, arg(args, 1))?;
    let start = pos.clamp(0.0, len_of(&s)) as usize;
    let hay: Vec<u16> = s.units().collect();
    let needle: Vec<u16> = search.units().collect();
    if needle.is_empty() {
        return Ok(number(start as f64));
    }
    let Some(last) = hay.len().checked_sub(needle.len()) else {
        return Ok(Value::int32(-1));
    };
    for i in start..=last {
        let end = i.saturating_add(needle.len());
        if hay.get(i..end) == Some(needle.as_slice()) {
            return Ok(number(i as f64));
        }
    }
    Ok(Value::int32(-1))
}

/// `String.prototype.slice ( start, end )`, §22.1.3.24†:
/// 1 and 2. As above.
/// 3. Let len be the length of S.
/// 4. Let intStart be ? ToIntegerOrInfinity(start).
/// 5. If intStart = -∞, let from be 0.
/// 6. Else if intStart < 0, let from be max(len + intStart, 0).
/// 7. Else, let from be min(intStart, len).
/// 8. If end is undefined, let intEnd be len; else let intEnd be ?
///    ToIntegerOrInfinity(end).
/// 9. If intEnd = -∞, let to be 0.
/// 10. Else if intEnd < 0, let to be max(len + intEnd, 0).
/// 11. Else, let to be min(intEnd, len).
/// 12. If from ≥ to, return the empty String.
/// 13. Return the substring of S from from to to.
fn slice(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "slice")?;
    let len = len_of(&s);
    let relative = |n: f64| -> f64 {
        if n == f64::NEG_INFINITY {
            0.0
        } else if n < 0.0 {
            (len + n).max(0.0)
        } else {
            n.min(len)
        }
    };
    let int_start = to_integer_or_infinity(vm, arg(args, 0))?;
    let from = relative(int_start);
    let end = arg(args, 1);
    let to = if end == Value::UNDEFINED {
        len
    } else {
        relative(to_integer_or_infinity(vm, end)?)
    };
    if from >= to {
        return string(vm, "");
    }
    js_string(vm, s.substring(from as usize, to as usize))
}

/// `String.prototype.substring ( start, end )`, §22.1.3.25†:
/// 1 and 2. As above.
/// 3. Let len be the length of S.
/// 4. Let intStart be ? ToIntegerOrInfinity(start).
/// 5. If end is undefined, let intEnd be len; else let intEnd be ?
///    ToIntegerOrInfinity(end).
/// 6. Let finalStart be the result of clamping intStart between 0 and len.
/// 7. Let finalEnd be the result of clamping intEnd between 0 and len.
/// 8. Let from be min(finalStart, finalEnd).
/// 9. Let to be max(finalStart, finalEnd).
/// 10. Return the substring of S from from to to.
fn substring(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "substring")?;
    let len = len_of(&s);
    let int_start = to_integer_or_infinity(vm, arg(args, 0))?;
    let end = arg(args, 1);
    let int_end = if end == Value::UNDEFINED {
        len
    } else {
        to_integer_or_infinity(vm, end)?
    };
    let final_start = int_start.clamp(0.0, len);
    let final_end = int_end.clamp(0.0, len);
    let (from, to) = (final_start.min(final_end), final_start.max(final_end));
    js_string(vm, s.substring(from as usize, to as usize))
}
