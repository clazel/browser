//! Helpers the built-ins share: arguments, defining properties, the
//! conversions of §7.1 that need no more than the VM's, and `SameValue`.

use clazel_js_heap::shape::Attrs;
use clazel_js_heap::string::{JsString, Key};
use clazel_js_heap::value::Value;
use clazel_js_vm::heap::ObjKind;
use clazel_js_vm::interp::{Abrupt, Intrinsic, NativeFn, Vm};
use clazel_js_vm::numeric::{Num, narrow, num};

/// `[[Writable]]` and `[[Configurable]]`: the attributes of a built-in
/// function property (§17†: "Every other data property described in clauses
/// 19 through 28 ... has the attributes { [[Writable]]: true,
/// [[Enumerable]]: false, [[Configurable]]: true }").
pub const METHOD: Attrs = Attrs(Attrs::WRITABLE | Attrs::CONFIGURABLE);
/// No attribute: a constant such as `Math.PI` or `Number.MAX_VALUE`.
pub const CONSTANT: Attrs = Attrs(0);
/// `[[Configurable]]` only: `length` and `name` of a function (§10.2.9†).
pub const CONFIGURABLE_ONLY: Attrs = Attrs(Attrs::CONFIGURABLE);

/// Argument `i`, `undefined` if there are fewer (§10.4.1.1†'s convention for
/// built-ins: a missing argument is `undefined`).
#[must_use]
pub fn arg(args: &[Value], i: usize) -> Value {
    args.get(i).copied().unwrap_or(Value::UNDEFINED)
}

/// The interned key for a name.
///
/// # Errors
/// [`Abrupt::OutOfMemory`] if the name is too long.
pub fn key(vm: &mut Vm, name: &str) -> Result<Key, Abrupt> {
    Ok(vm.heap_mut().intern_str(name)?)
}

/// A new string value.
///
/// # Errors
/// [`Abrupt::OutOfMemory`].
pub fn string(vm: &mut Vm, s: &str) -> Result<Value, Abrupt> {
    vm.new_string(s)
}

/// A new string value from a [`JsString`].
///
/// # Errors
/// [`Abrupt::OutOfMemory`].
pub fn js_string(vm: &mut Vm, s: JsString) -> Result<Value, Abrupt> {
    Ok(vm.heap_mut().new_string(s)?)
}

/// A Number value, in the encoding the interpreter keeps (an int32 when the
/// Number is an integer in range other than `-0`).
#[must_use]
pub fn number(d: f64) -> Value {
    match narrow(d) {
        Num::I(i) => Value::int32(i),
        Num::D(d) => Value::double(d),
    }
}

/// Defines the own data property `name` of `obj` with `attrs`.
///
/// # Errors
/// [`Abrupt::OutOfMemory`], or [`Abrupt::Internal`] if `obj` is not an
/// object.
pub fn define(vm: &mut Vm, obj: Value, name: &str, v: Value, attrs: Attrs) -> Result<(), Abrupt> {
    let k = key(vm, name)?;
    Ok(vm.heap_mut().define(obj, k, v, attrs)?)
}

/// Defines a built-in method of `obj`: a native function with `length` and
/// `name`, as a writable, non-enumerable, configurable property.
///
/// # Errors
/// As [`define`].
pub fn method(
    vm: &mut Vm,
    obj: Value,
    name: &str,
    length: i32,
    f: NativeFn,
) -> Result<Value, Abrupt> {
    let func = vm.new_native(name, length, f)?;
    define(vm, obj, name, func, METHOD)?;
    Ok(func)
}

/// Makes a constructor: a native constructor `name` with `proto` as its
/// `prototype` (no attributes, §17†) and `proto.constructor` pointing back
/// (writable, configurable).
///
/// # Errors
/// As [`define`].
pub fn constructor(
    vm: &mut Vm,
    name: &str,
    length: i32,
    f: NativeFn,
    proto: Value,
) -> Result<Value, Abrupt> {
    let ctor = vm.new_native_constructor(name, length, f)?;
    define(vm, ctor, "prototype", proto, CONSTANT)?;
    define(vm, proto, "constructor", ctor, METHOD)?;
    Ok(ctor)
}

/// Defines `name` of the global object as a writable, non-enumerable,
/// configurable property (§19†, "Function Properties of the Global Object"
/// and §19.3†, "Constructor Properties").
///
/// # Errors
/// As [`define`].
pub fn global(vm: &mut Vm, name: &str, v: Value) -> Result<(), Abrupt> {
    let g = vm.global();
    define(vm, g, name, v, METHOD)
}

/// A new ordinary object with the intrinsic `%Object.prototype%`.
///
/// # Errors
/// [`Abrupt::OutOfMemory`].
pub fn new_plain(vm: &mut Vm) -> Result<Value, Abrupt> {
    vm.new_object()
}

/// A new ordinary object with `proto` as its prototype and `kind`.
///
/// # Errors
/// [`Abrupt::OutOfMemory`].
pub fn new_object_with(vm: &mut Vm, proto: Value, kind: ObjKind) -> Result<Value, Abrupt> {
    Ok(vm.heap_mut().new_object(proto, kind)?)
}

/// The list of values as an array: CreateArrayFromList, §7.3.18†.
///
/// # Errors
/// [`Abrupt::OutOfMemory`].
pub fn new_array_like(vm: &mut Vm, items: &[Value]) -> Result<Value, Abrupt> {
    vm.create_array_from_list(items)
}

/// The Number a value is, if it is one.
#[must_use]
pub fn as_number(v: Value) -> Option<f64> {
    num(v).map(Num::to_f64)
}

/// RequireObjectCoercible, §7.2.1†: `undefined` and `null` are a TypeError.
///
/// # Errors
/// A `TypeError`.
pub fn require_object_coercible(vm: &mut Vm, v: Value, what: &str) -> Result<(), Abrupt> {
    if v == Value::UNDEFINED || v == Value::NULL {
        return Err(vm.type_error(&format!("{what} called on null or undefined")));
    }
    Ok(())
}

/// ToIntegerOrInfinity, §7.1.5†: NaN and the zeros are `+0`, the infinities
/// stay, any other Number is truncated.
///
/// # Errors
/// The exceptions of ToNumber.
pub fn to_integer_or_infinity(vm: &mut Vm, v: Value) -> Result<f64, Abrupt> {
    let n = vm.to_number(v)?;
    if n.is_nan() {
        return Ok(0.0);
    }
    // `+ 0.0` turns `-0` into `+0` (step 4: "return 0" for a zero).
    Ok(n.trunc() + 0.0)
}

/// SameValue, §7.2.10†: Numbers by value with NaN equal to itself and `+0`
/// distinct from `-0`, Strings by code units, everything else by identity.
#[must_use]
pub fn same_value(vm: &Vm, a: Value, b: Value) -> bool {
    if let (Some(x), Some(y)) = (as_number(a), as_number(b)) {
        return if x.is_nan() || y.is_nan() {
            x.is_nan() && y.is_nan()
        } else {
            x.to_bits() == y.to_bits()
        };
    }
    if let (Some(x), Some(y)) = (vm.heap().string(a), vm.heap().string(b)) {
        return x == y;
    }
    a == b
}

/// HasProperty, §7.3.12†, for an object: an own or inherited property.
///
/// # Errors
/// [`Abrupt::Internal`] if the prototype chain is corrupt.
pub fn has_property(vm: &Vm, obj: Value, k: Key) -> Result<bool, Abrupt> {
    Ok(vm.heap().find(obj, k)?.is_some())
}

/// The own-property test of `[[GetOwnProperty]]` for the objects this slice
/// has (§10.1.5†).
///
/// # Errors
/// [`Abrupt::Internal`] if the prototype chain is corrupt.
pub fn has_own_property(vm: &Vm, obj: Value, k: Key) -> Result<bool, Abrupt> {
    Ok(vm.heap().find(obj, k)?.is_some_and(|f| f.own))
}

/// The prototype a native error, wrapper or other object gets: the intrinsic
/// if the realm has it installed.
#[must_use]
pub fn intrinsic(vm: &Vm, which: Intrinsic) -> Value {
    vm.intrinsic(which)
}
