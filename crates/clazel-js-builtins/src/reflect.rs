//! `Reflect` (§28.1†): `apply`, `construct`, `defineProperty`,
//! `deleteProperty`, `get`, `getOwnPropertyDescriptor`, `getPrototypeOf`,
//! `has`, `isExtensible`, `ownKeys`, `preventExtensions`, `set`,
//! `setPrototypeOf` and `@@toStringTag`.
//!
//! Each function is the standard's call of the object's internal method. There
//! is no Proxy yet, so the internal methods are the ordinary ones (§10.1†)
//! and the Array exotic `[[DefineOwnProperty]]` (§10.4.2.1†); when Proxy
//! arrives the same functions see its traps through the VM's operations.

use crate::object::{from_property_descriptor, to_prop_desc, to_property_descriptor};
use crate::symbol::to_string_tag;
use crate::util::{arg, method, new_array_like, own_property_keys};
use clazel_js_heap::string::Key;
use clazel_js_heap::value::Value;
use clazel_js_vm::interp::{Abrupt, Vm};

/// Installs `Reflect`.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    let object_proto = vm.intrinsic(clazel_js_vm::interp::Intrinsic::ObjectPrototype);
    let reflect =
        crate::util::new_object_with(vm, object_proto, clazel_js_vm::heap::ObjKind::Plain)?;
    let methods: [(&str, i32, clazel_js_vm::interp::NativeFn); 13] = [
        ("apply", 3, apply),
        ("construct", 2, construct),
        ("defineProperty", 3, define_property),
        ("deleteProperty", 2, delete_property),
        ("get", 2, get),
        ("getOwnPropertyDescriptor", 2, get_own_property_descriptor),
        ("getPrototypeOf", 1, get_prototype_of),
        ("has", 2, has),
        ("isExtensible", 1, is_extensible),
        ("ownKeys", 1, own_keys),
        ("preventExtensions", 1, prevent_extensions),
        ("set", 3, set),
        ("setPrototypeOf", 2, set_prototype_of),
    ];
    for (name, len, f) in methods {
        method(vm, reflect, name, len, f)?;
    }
    to_string_tag(vm, reflect, "Reflect")?;
    crate::util::global(vm, "Reflect", reflect)
}

/// The first step of most functions: "If target is not an Object, throw a
/// TypeError exception".
fn target_object(vm: &mut Vm, v: Value, what: &str) -> Result<Value, Abrupt> {
    if vm.heap().is_object(v) {
        Ok(v)
    } else {
        Err(vm.type_error(&format!("Reflect.{what} called on non-object")))
    }
}

/// CreateListFromArrayLike ( obj ), §7.3.19†:
/// 1. If elementTypes is not present, set elementTypes to « Undefined, Null,
///    Boolean, String, Symbol, Number, BigInt, Object ».
/// 2. If obj is not an Object, throw a TypeError exception.
/// 3. Let len be ? LengthOfArrayLike(obj).
/// 4. Let list be a new empty List.
/// 5. Let index be 0.
/// 6. Repeat, while index < len,
///    a. Let indexName be ! ToString(𝔽(index)).
///    b. Let next be ? Get(obj, indexName).
///    c. If elementTypes does not contain Type(next), throw a TypeError
///    exception.
///    d. Append next to list.
///    e. Set index to index + 1.
/// 7. Return list.
pub fn create_list_from_array_like(vm: &mut Vm, obj: Value) -> Result<Vec<Value>, Abrupt> {
    if !vm.heap().is_object(obj) {
        return Err(vm.type_error("CreateListFromArrayLike called on non-object"));
    }
    let len = crate::util::get(vm, obj, "length")?;
    let len = crate::util::to_integer_or_infinity(vm, len)?.clamp(0.0, 9_007_199_254_740_991.0);
    let mut list = Vec::new();
    let mut index: u32 = 0;
    while f64::from(index) < len {
        vm.charge_step()?;
        let k = vm.index_key(u64::from(index))?;
        list.push(vm.get_value(obj, k)?);
        index = index
            .checked_add(1)
            .ok_or_else(|| vm.range_error("Invalid array length"))?;
    }
    Ok(list)
}

/// `Reflect.apply ( target, thisArgument, argumentsList )`, §28.1.1†:
/// 1. If IsCallable(target) is false, throw a TypeError exception.
/// 2. Let args be ? CreateListFromArrayLike(argumentsList).
/// 3. Perform PrepareForTailCall().
/// 4. Return ? Call(target, thisArgument, args).
fn apply(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let target = arg(args, 0);
    if !vm.heap().is_callable(target) {
        return Err(vm.type_error("Reflect.apply target is not callable"));
    }
    let list = create_list_from_array_like(vm, arg(args, 2))?;
    vm.call(target, arg(args, 1), &list)
}

/// `Reflect.construct ( target, argumentsList [ , newTarget ] )`, §28.1.2†:
/// 1. If IsConstructor(target) is false, throw a TypeError exception.
/// 2. If newTarget is not present, set newTarget to target.
/// 3. Else if IsConstructor(newTarget) is false, throw a TypeError exception.
/// 4. Let args be ? CreateListFromArrayLike(argumentsList).
/// 5. Return ? Construct(target, args, newTarget).
fn construct(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let target = arg(args, 0);
    if !vm.is_constructor(target) {
        return Err(vm.type_error("Reflect.construct target is not a constructor"));
    }
    let new_target = args.get(2).copied().unwrap_or(target);
    if args.len() >= 3 && !vm.is_constructor(new_target) {
        return Err(vm.type_error("Reflect.construct newTarget is not a constructor"));
    }
    let list = create_list_from_array_like(vm, arg(args, 1))?;
    vm.construct_with_target(target, &list, new_target)
}

/// `Reflect.defineProperty ( target, propertyKey, attributes )`, §28.1.3†:
/// 1. If target is not an Object, throw a TypeError exception.
/// 2. Let key be ? ToPropertyKey(propertyKey).
/// 3. Let desc be ? ToPropertyDescriptor(attributes).
/// 4. Return ? target.[[DefineOwnProperty]](key, desc).
fn define_property(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let target = target_object(vm, arg(args, 0), "defineProperty")?;
    let k = vm.coerce_property_key(arg(args, 1))?;
    let desc = to_property_descriptor(vm, arg(args, 2))?;
    Ok(Value::boolean(vm.define_own_property(
        target,
        k,
        &to_prop_desc(&desc),
    )?))
}

/// `Reflect.deleteProperty ( target, propertyKey )`, §28.1.4†:
/// 1. If target is not an Object, throw a TypeError exception.
/// 2. Let key be ? ToPropertyKey(propertyKey).
/// 3. Return ? target.[[Delete]](key).
fn delete_property(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let target = target_object(vm, arg(args, 0), "deleteProperty")?;
    let k = vm.coerce_property_key(arg(args, 1))?;
    Ok(Value::boolean(vm.delete_property(target, k)?))
}

/// `Reflect.get ( target, propertyKey [ , receiver ] )`, §28.1.5†:
/// 1. If target is not an Object, throw a TypeError exception.
/// 2. Let key be ? ToPropertyKey(propertyKey).
/// 3. If receiver is not present, then a. Set receiver to target.
/// 4. Return ? target.[[Get]](key, receiver).
fn get(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let target = target_object(vm, arg(args, 0), "get")?;
    let k = vm.coerce_property_key(arg(args, 1))?;
    let receiver = args.get(2).copied().unwrap_or(target);
    vm.get_with_receiver(target, k, receiver)
}

/// `Reflect.getOwnPropertyDescriptor ( target, propertyKey )`, §28.1.6†:
/// 1. If target is not an Object, throw a TypeError exception.
/// 2. Let key be ? ToPropertyKey(propertyKey).
/// 3. Let desc be ? target.[[GetOwnProperty]](key).
/// 4. Return FromPropertyDescriptor(desc).
fn get_own_property_descriptor(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let target = target_object(vm, arg(args, 0), "getOwnPropertyDescriptor")?;
    let k = vm.coerce_property_key(arg(args, 1))?;
    let desc = vm.own_property_descriptor(target, k)?;
    from_property_descriptor(vm, desc)
}

/// `Reflect.getPrototypeOf ( target )`, §28.1.7†:
/// 1. If target is not an Object, throw a TypeError exception.
/// 2. Return ? target.[[GetPrototypeOf]]().
fn get_prototype_of(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let target = target_object(vm, arg(args, 0), "getPrototypeOf")?;
    Ok(vm.heap().proto_of(target).unwrap_or(Value::NULL))
}

/// `Reflect.has ( target, propertyKey )`, §28.1.8†:
/// 1. If target is not an Object, throw a TypeError exception.
/// 2. Let key be ? ToPropertyKey(propertyKey).
/// 3. Return ? target.[[HasProperty]](key).
fn has(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let target = target_object(vm, arg(args, 0), "has")?;
    let k: Key = vm.coerce_property_key(arg(args, 1))?;
    Ok(Value::boolean(vm.heap().find(target, k)?.is_some()))
}

/// `Reflect.isExtensible ( target )`, §28.1.9†:
/// 1. If target is not an Object, throw a TypeError exception.
/// 2. Return ? target.[[IsExtensible]]().
fn is_extensible(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let target = target_object(vm, arg(args, 0), "isExtensible")?;
    Ok(Value::boolean(vm.heap().is_extensible(target)))
}

/// `Reflect.ownKeys ( target )`, §28.1.10†:
/// 1. If target is not an Object, throw a TypeError exception.
/// 2. Let keys be ? target.[[OwnPropertyKeys]]().
/// 3. Return CreateArrayFromList(keys).
fn own_keys(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let target = target_object(vm, arg(args, 0), "ownKeys")?;
    let mut items = Vec::new();
    for k in own_property_keys(vm, target) {
        items.push(vm.key_value(k)?);
    }
    new_array_like(vm, &items)
}

/// `Reflect.preventExtensions ( target )`, §28.1.11†:
/// 1. If target is not an Object, throw a TypeError exception.
/// 2. Return ? target.[[PreventExtensions]]().
fn prevent_extensions(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let target = target_object(vm, arg(args, 0), "preventExtensions")?;
    Ok(Value::boolean(vm.prevent_extensions(target)?))
}

/// `Reflect.set ( target, propertyKey, V [ , receiver ] )`, §28.1.12†:
/// 1. If target is not an Object, throw a TypeError exception.
/// 2. Let key be ? ToPropertyKey(propertyKey).
/// 3. If receiver is not present, then a. Set receiver to target.
/// 4. Return ? target.[[Set]](key, V, receiver).
fn set(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let target = target_object(vm, arg(args, 0), "set")?;
    let k = vm.coerce_property_key(arg(args, 1))?;
    let receiver = args.get(3).copied().unwrap_or(target);
    Ok(Value::boolean(vm.ordinary_set(
        target,
        k,
        arg(args, 2),
        receiver,
    )?))
}

/// `Reflect.setPrototypeOf ( target, proto )`, §28.1.13†:
/// 1. If target is not an Object, throw a TypeError exception.
/// 2. If proto is not an Object and proto is not null, throw a TypeError
///    exception.
/// 3. Return ? target.[[SetPrototypeOf]](proto).
fn set_prototype_of(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let target = target_object(vm, arg(args, 0), "setPrototypeOf")?;
    let proto = arg(args, 1);
    if proto != Value::NULL && !vm.heap().is_object(proto) {
        return Err(vm.type_error("Object prototype may only be an Object or null"));
    }
    Ok(Value::boolean(vm.set_prototype_of(target, proto)?))
}
