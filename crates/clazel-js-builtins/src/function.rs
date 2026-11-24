//! `Function` (§20.2†): the constructor and `Function.prototype.call`,
//! `apply`, `bind` and `@@hasInstance`.

use crate::util::{
    CONFIGURABLE_ONLY, arg, constructor, define, has_own_property, key, method, number, string,
    to_integer_or_infinity,
};
use clazel_js_heap::value::Value;
use clazel_js_vm::interp::{Abrupt, Intrinsic, Vm};

/// Installs `Function` and the methods of `Function.prototype`.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    let proto = vm.intrinsic(Intrinsic::FunctionPrototype);
    // §20.2.3†: `length` is 0 and `name` is "" (the prototype is an ordinary
    // object here, not a function: a listed deviation).
    define(vm, proto, "length", Value::int32(0), CONFIGURABLE_ONLY)?;
    let empty = string(vm, "")?;
    define(vm, proto, "name", empty, CONFIGURABLE_ONLY)?;
    let ctor = constructor(vm, "Function", 1, function, proto)?;
    method(vm, proto, "apply", 2, apply)?;
    method(vm, proto, "bind", 1, bind)?;
    method(vm, proto, "call", 1, call)?;
    // §20.2.3.6† `Function.prototype [ @@hasInstance ] ( V )`: its `name` is
    // "[Symbol.hasInstance]"; { [[Writable]]: false, [[Enumerable]]: false,
    // [[Configurable]]: false }.
    let hi = vm.new_native("[Symbol.hasInstance]", 1, has_instance)?;
    let k = vm.well_known_key(clazel_js_heap::symbol::HAS_INSTANCE)?;
    vm.heap_mut()
        .define(proto, k, hi, clazel_js_heap::shape::Attrs(0))?;
    crate::util::global(vm, "Function", ctor)
}

/// `Function ( ...parameterArgs, bodyArg )`, §20.2.1.1†: CreateDynamicFunction
/// compiles source text, which needs the compiler; `NotYet`.
fn function(_vm: &mut Vm, _this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    Err(Abrupt::NotYet(
        "the Function constructor (CreateDynamicFunction needs the compiler)".into(),
    ))
}

/// `Function.prototype [ @@hasInstance ] ( V )`, §20.2.3.6†:
/// 1. Let F be the this value.
/// 2. Return ? OrdinaryHasInstance(F, V).
fn has_instance(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    Ok(Value::boolean(
        vm.ordinary_has_instance(this, arg(args, 0))?,
    ))
}

/// `Function.prototype.call ( thisArg, ...args )`, §20.2.3.3†:
/// 1. Let func be the this value.
/// 2. If IsCallable(func) is false, throw a TypeError exception.
/// 3. Perform PrepareForTailCall().
/// 4. Return ? Call(func, thisArg, args).
fn call(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    if !vm.heap().is_callable(this) {
        return Err(vm.type_error("Function.prototype.call called on a non-function"));
    }
    let rest = args.get(1..).unwrap_or(&[]);
    vm.call(this, arg(args, 0), rest)
}

/// `Function.prototype.apply ( thisArg, argArray )`, §20.2.3.1†:
/// 1. Let func be the this value.
/// 2. If IsCallable(func) is false, throw a TypeError exception.
/// 3. If argArray is either undefined or null, then
///    a. Perform PrepareForTailCall().
///    b. Return ? Call(func, thisArg).
/// 4. Let argList be ? CreateListFromArrayLike(argArray).
/// 5. Perform PrepareForTailCall().
/// 6. Return ? Call(func, thisArg, argList).
fn apply(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    if !vm.heap().is_callable(this) {
        return Err(vm.type_error("Function.prototype.apply called on a non-function"));
    }
    let array = arg(args, 1);
    if array == Value::UNDEFINED || array == Value::NULL {
        return vm.call(this, arg(args, 0), &[]);
    }
    let list = create_list_from_array_like(vm, array)?;
    vm.call(this, arg(args, 0), &list)
}

/// The most elements `apply` accepts: the frame region's limit is far lower,
/// but the list is built before the call, so it is bounded here.
const MAX_APPLY_ARGS: f64 = 1_048_576.0;

/// CreateListFromArrayLike ( obj ), §7.3.19†:
/// 2. If obj is not an Object, throw a TypeError exception.
/// 3. Let len be ? LengthOfArrayLike(obj).
/// 4 to 6. For each index from 0 to len - 1, append ? Get(obj, ToString(index)).
fn create_list_from_array_like(vm: &mut Vm, obj: Value) -> Result<Vec<Value>, Abrupt> {
    if !vm.heap().is_object(obj) {
        return Err(vm.type_error("CreateListFromArrayLike called on non-object"));
    }
    let kl = key(vm, "length")?;
    let len = vm.get_value(obj, kl)?;
    // LengthOfArrayLike: ToLength(? Get(obj, "length")), §7.1.20†.
    let len = to_integer_or_infinity(vm, len)?.clamp(0.0, 9_007_199_254_740_991.0);
    if len > MAX_APPLY_ARGS {
        return Err(vm.range_error("Too many arguments in function application"));
    }
    let mut out = Vec::new();
    let n = len as usize;
    for i in 0..n {
        let k = key(vm, &i.to_string())?;
        out.push(vm.get_value(obj, k)?);
    }
    Ok(out)
}

/// `Function.prototype.bind ( thisArg, ...args )`, §20.2.3.2†:
/// 1. Let Target be the this value.
/// 2. If IsCallable(Target) is false, throw a TypeError exception.
/// 3. Let F be ? BoundFunctionCreate(Target, thisArg, args).
/// 4. Let L be 0.
/// 5. Let targetHasLength be ? HasOwnProperty(Target, "length").
/// 6. If targetHasLength is true, then
///    a. Let targetLen be ? Get(Target, "length").
///    b. If targetLen is a Number, then
///    i. If targetLen is +∞, set L to +∞.
///    ii. Else if targetLen is -∞, set L to 0.
///    iii. Else, let targetLenAsInt be ! ToIntegerOrInfinity(targetLen);
///    set L to max(targetLenAsInt - argCount, 0).
/// 7. Perform SetFunctionLength(F, L).
/// 8. Let targetName be ? Get(Target, "name").
/// 9. If targetName is not a String, set targetName to the empty String.
/// 10. Perform SetFunctionName(F, targetName, "bound").
/// 11. Return F.
fn bind(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    if !vm.heap().is_callable(this) {
        return Err(vm.type_error("Bind must be called on a function"));
    }
    let bound_args: Vec<Value> = args.get(1..).unwrap_or(&[]).to_vec();
    let arg_count = bound_args.len() as f64;
    let f = vm.new_bound_function(this, arg(args, 0), bound_args)?;
    let mut l = 0.0_f64;
    let kl = key(vm, "length")?;
    if has_own_property(vm, this, kl)? {
        let target_len = vm.get_value(this, kl)?;
        if let Some(n) = crate::util::as_number(target_len) {
            if n == f64::INFINITY {
                l = f64::INFINITY;
            } else if n == f64::NEG_INFINITY || n.is_nan() {
                l = 0.0;
            } else {
                l = (n.trunc() - arg_count).max(0.0);
            }
        }
    }
    define(vm, f, "length", number(l), CONFIGURABLE_ONLY)?;
    let kn = key(vm, "name")?;
    let target_name = vm.get_value(this, kn)?;
    let name = vm
        .string_text(target_name)
        .map(|s| format!("bound {s}"))
        .unwrap_or_else(|| "bound ".to_string());
    let name = string(vm, &name)?;
    define(vm, f, "name", name, CONFIGURABLE_ONLY)?;
    Ok(f)
}
