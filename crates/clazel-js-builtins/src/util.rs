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

/// `Get ( O, name )`, §7.3.2†, for a string key.
///
/// # Errors
/// As [`Vm::get_value`].
pub fn get(vm: &mut Vm, o: Value, name: &str) -> Result<Value, Abrupt> {
    let k = key(vm, name)?;
    vm.get_value(o, k)
}

/// `Set ( O, name, V, true )`, §7.3.4†, for a string key.
///
/// # Errors
/// A `TypeError` if the property is read-only.
pub fn set(vm: &mut Vm, o: Value, name: &str, v: Value) -> Result<(), Abrupt> {
    let k = key(vm, name)?;
    vm.put_value(o, k, v, true)
}

/// `Invoke ( V, P, argumentsList )`, §7.3.20†: `V[P]` called with `V` as
/// `this`.
///
/// # Errors
/// What the lookup or the call throws, or a `TypeError` if `V[P]` is not
/// callable.
pub fn invoke(vm: &mut Vm, v: Value, name: &str, args: &[Value]) -> Result<Value, Abrupt> {
    let f = get(vm, v, name)?;
    if !vm.heap().is_callable(f) {
        return Err(vm.type_error(&format!("{name} is not a function")));
    }
    vm.call(f, v, args)
}

/// The value of a JS exception: `Ok(v)` for `Abrupt::Throw(v)`, and any
/// other abrupt completion (which JS cannot catch) as the error. A native
/// uses it where the standard says "Completion(...)" and then tests for an
/// abrupt completion.
///
/// # Errors
/// `e` itself, unless it is a thrown value.
pub fn caught(e: Abrupt) -> Result<Value, Abrupt> {
    match e {
        Abrupt::Throw(v) => Ok(v),
        other => Err(other),
    }
}

/// SpeciesConstructor ( O, defaultConstructor ), §7.3.22†:
/// 1. Let C be ? Get(O, "constructor").
/// 2. If C is undefined, return defaultConstructor.
/// 3. If C is not an Object, throw a TypeError exception.
/// 4. Let S be ? Get(C, @@species).
/// 5. If S is either undefined or null, return defaultConstructor.
/// 6. If IsConstructor(S) is true, return S.
/// 7. Throw a TypeError exception.
///
/// # Errors
/// As the steps say.
pub fn species_constructor(vm: &mut Vm, o: Value, default: Value) -> Result<Value, Abrupt> {
    let c = get(vm, o, "constructor")?;
    if c == Value::UNDEFINED {
        return Ok(default);
    }
    if !vm.heap().is_object(c) {
        return Err(vm.type_error("object.constructor is not an object"));
    }
    let ks = vm.well_known_key(clazel_js_heap::symbol::SPECIES)?;
    let s = vm.get_value(c, ks)?;
    if s == Value::UNDEFINED || s == Value::NULL {
        return Ok(default);
    }
    if vm.is_constructor(s) {
        return Ok(s);
    }
    Err(vm.type_error("object.constructor[Symbol.species] is not a constructor"))
}

/// The own property keys of an object in `[[OwnPropertyKeys]]` order
/// (OrdinaryOwnPropertyKeys, §10.1.11.1†): the array indices in ascending
/// order, then the other String keys in creation order, then the Symbol keys
/// in creation order.
#[must_use]
pub fn own_property_keys(vm: &Vm, obj: Value) -> Vec<Key> {
    let mut keys: Vec<Key> = vm
        .heap()
        .own_properties(obj)
        .into_iter()
        .map(|(k, _, _)| k)
        .collect();
    keys.extend(
        vm.heap()
            .own_symbol_properties(obj)
            .into_iter()
            .map(|(k, _, _)| k),
    );
    keys
}

/// Defines an accessor property of `obj` that is not enumerable and is
/// configurable (the attributes of the standard's accessor properties, §17†):
/// its getter and setter are native functions named `get name` and `set name`
/// (`name` is the key's text, or `[description]` for a Symbol).
///
/// # Errors
/// As [`define`].
pub fn accessor(
    vm: &mut Vm,
    obj: Value,
    k: Key,
    name: &str,
    getter: Option<NativeFn>,
    setter: Option<NativeFn>,
) -> Result<(), Abrupt> {
    let get = match getter {
        Some(f) => vm.new_native(&format!("get {name}"), 0, f)?,
        None => Value::UNDEFINED,
    };
    let set = match setter {
        Some(f) => vm.new_native(&format!("set {name}"), 1, f)?,
        None => Value::UNDEFINED,
    };
    let d = clazel_js_vm::props::PropDesc::accessor(get, set, Attrs(Attrs::CONFIGURABLE));
    vm.define_property_or_throw(obj, k, &d)
}
