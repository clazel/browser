//! `Object` (§20.1†): the constructor, `Object.prototype.toString`,
//! `hasOwnProperty`, `valueOf`, and `Object.keys`, `defineProperty`,
//! `getPrototypeOf`, `create`.

use crate::util::{
    arg, constructor, has_own_property, has_property, key, method, new_array_like, new_object_with,
    string,
};
use clazel_js_heap::shape::Attrs;
use clazel_js_heap::value::{Decoded, Value};
use clazel_js_vm::heap::ObjKind;
use clazel_js_vm::interp::{Abrupt, Intrinsic, Vm};
use clazel_js_vm::props::PropDesc;

/// Installs `Object`, `Object.prototype` and their methods.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    let proto = vm.intrinsic(Intrinsic::ObjectPrototype);
    let ctor = constructor(vm, "Object", 1, object, proto)?;
    method(vm, proto, "hasOwnProperty", 1, has_own_property_fn)?;
    method(vm, proto, "toString", 0, to_string)?;
    method(vm, proto, "valueOf", 0, value_of)?;
    method(vm, ctor, "keys", 1, keys)?;
    method(vm, ctor, "defineProperty", 3, define_property)?;
    method(vm, ctor, "getPrototypeOf", 1, get_prototype_of)?;
    method(vm, ctor, "create", 2, create)?;
    crate::util::global(vm, "Object", ctor)
}

/// `Object ( [ value ] )`, §20.1.1.1†:
/// 1. If NewTarget is neither undefined nor the active function object, then
///    a. Return ? OrdinaryCreateFromConstructor(NewTarget,
///    "%Object.prototype%").
/// 2. If value is either undefined or null, return
///    OrdinaryObjectCreate(%Object.prototype%).
/// 3. Return ! ToObject(value).
fn object(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let nt = vm.new_target();
    if nt != Value::UNDEFINED && nt != vm.active_function() {
        return vm.create_from_constructor(nt, Intrinsic::ObjectPrototype, ObjKind::Plain);
    }
    let value = arg(args, 0);
    if value == Value::UNDEFINED || value == Value::NULL {
        return vm.new_object();
    }
    vm.to_object(value)
}

/// `Object.prototype.hasOwnProperty ( V )`, §20.1.3.2†:
/// 1. Let P be ? ToPropertyKey(V).
/// 2. Let O be ? ToObject(this value).
/// 3. Return ? HasOwnProperty(O, P).
fn has_own_property_fn(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let k = vm.coerce_property_key(arg(args, 0))?;
    let o = vm.to_object(this)?;
    Ok(Value::boolean(has_own_property(vm, o, k)?))
}

/// `Object.prototype.toString ( )`, §20.1.3.6†:
/// 1. If the this value is undefined, return "[object Undefined]".
/// 2. If the this value is null, return "[object Null]".
/// 3. Let O be ! ToObject(this value).
/// 4. Let isArray be ? IsArray(O).
/// 5. If isArray is true, let builtinTag be "Array".
/// 6. to 14. Otherwise builtinTag is "Arguments", "Function" (O has
///    [[Call]]), "Error" ([[ErrorData]]), "Boolean", "Number" or "String"
///    ([[BooleanData]], [[NumberData]], [[StringData]]), "Date", "RegExp",
///    or else "Object".
/// 15. and 16. `@@toStringTag` is not consulted (no Symbols yet).
/// 17. Return the string-concatenation of "[object ", tag, and "]".
fn to_string(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    if this == Value::UNDEFINED {
        return string(vm, "[object Undefined]");
    }
    if this == Value::NULL {
        return string(vm, "[object Null]");
    }
    let o = vm.to_object(this)?;
    let tag = if vm.heap().is_callable(o) {
        "Function"
    } else {
        match vm.heap().obj(o).map(|o| o.kind) {
            Some(ObjKind::Array) => "Array",
            Some(ObjKind::Error) => "Error",
            Some(ObjKind::Primitive(p)) => match p.decode() {
                Decoded::Bool(_) => "Boolean",
                Decoded::Int32(_) | Decoded::Double(_) => "Number",
                _ => "String",
            },
            _ => "Object",
        }
    };
    string(vm, &format!("[object {tag}]"))
}

/// `Object.prototype.valueOf ( )`, §20.1.3.7†:
/// 1. Return ? ToObject(this value).
fn value_of(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    vm.to_object(this)
}

/// `Object.keys ( O )`, §20.1.2.19†:
/// 1. Let obj be ? ToObject(O).
/// 2. Let keyList be ? EnumerableOwnProperties(obj, key).
/// 3. Return CreateArrayFromList(keyList).
///
/// EnumerableOwnProperties (§7.3.23†) lists the own string keys in
/// `[[OwnPropertyKeys]]` order whose property is enumerable. The array is
/// an array-like object until arrays exist ([`new_array_like`]).
fn keys(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let obj = vm.to_object(arg(args, 0))?;
    let names = enumerable_own_keys(vm, obj)?;
    let mut items = Vec::with_capacity(names.len());
    for k in names {
        let s = vm
            .heap()
            .key_string(k)
            .cloned()
            .ok_or(Abrupt::Internal("key"))?;
        items.push(crate::util::js_string(vm, s)?);
    }
    new_array_like(vm, &items)
}

fn enumerable_own_keys(vm: &Vm, obj: Value) -> Result<Vec<clazel_js_heap::string::Key>, Abrupt> {
    Ok(vm
        .heap()
        .own_properties(obj)
        .into_iter()
        .filter(|(_, a, _)| a.0 & Attrs::ENUMERABLE != 0)
        .map(|(k, _, _)| k)
        .collect())
}

/// `Object.getPrototypeOf ( O )`, §20.1.2.12†:
/// 1. Let obj be ? ToObject(O).
/// 2. Return ? obj.[[GetPrototypeOf]]().
fn get_prototype_of(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let obj = vm.to_object(arg(args, 0))?;
    vm.heap()
        .proto_of(obj)
        .ok_or(Abrupt::Internal("prototype of a non-object"))
}

/// `Object.create ( O, Properties )`, §20.1.2.2†:
/// 1. If O is not an Object and O is not null, throw a TypeError exception.
/// 2. Let obj be OrdinaryObjectCreate(O).
/// 3. If Properties is not undefined, then
///    a. Return ? ObjectDefineProperties(obj, Properties).
/// 4. Return obj.
fn create(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let proto = arg(args, 0);
    if proto != Value::NULL && !vm.heap().is_object(proto) {
        return Err(vm.type_error("Object prototype may only be an Object or null"));
    }
    let obj = new_object_with(vm, proto, ObjKind::Plain)?;
    let props = arg(args, 1);
    if props != Value::UNDEFINED {
        define_properties(vm, obj, props)?;
    }
    Ok(obj)
}

/// ObjectDefineProperties ( O, Properties ), §20.1.2.3.1†:
/// 1. Let props be ? ToObject(Properties).
/// 2. Let keys be ? props.[[OwnPropertyKeys]]().
/// 3. Let descriptors be a new empty List.
/// 4. For each element nextKey of keys, do
///    a. Let propDesc be ? props.[[GetOwnProperty]](nextKey).
///    b. If propDesc is not undefined and propDesc.[[Enumerable]] is true,
///    then i. Let descObj be ? Get(props, nextKey). ii. Let desc be ?
///    ToPropertyDescriptor(descObj). iii. Append the pair to descriptors.
/// 5. For each element property of descriptors, do
///    a. Perform ? DefinePropertyOrThrow(O, property.[[Key]],
///    property.[[Descriptor]]).
/// 6. Return O.
fn define_properties(vm: &mut Vm, obj: Value, props: Value) -> Result<(), Abrupt> {
    let props = vm.to_object(props)?;
    let mut descriptors = Vec::new();
    for (k, attrs, _) in vm.heap().own_properties(props) {
        if attrs.0 & Attrs::ENUMERABLE == 0 {
            continue;
        }
        let desc_obj = vm.get_value(props, k)?;
        descriptors.push((k, to_property_descriptor(vm, desc_obj)?));
    }
    for (k, desc) in descriptors {
        define_property_or_throw(vm, obj, k, &desc)?;
    }
    Ok(())
}

/// A property descriptor for a data property (§6.2.6†): each field present or
/// absent.
#[derive(Clone, Copy, Debug)]
struct Descriptor {
    value: Option<Value>,
    writable: Option<bool>,
    enumerable: Option<bool>,
    configurable: Option<bool>,
}

/// ToPropertyDescriptor ( Obj ), §6.2.6.5†:
/// 1. If Obj is not an Object, throw a TypeError exception.
/// 2. Let desc be a new Property Descriptor that initially has no fields.
/// 3. Let hasEnumerable be ? HasProperty(Obj, "enumerable").
/// 4. If hasEnumerable is true, then
///    a. Let enumerable be ToBoolean(? Get(Obj, "enumerable")).
///    b. Set desc.[[Enumerable]] to enumerable.
/// 5. to 10. The same for "configurable", "value" and "writable".
/// 11. to 14. "get" and "set": accessors are not yet, `NotYet`.
/// 15. If desc has a [[Get]] or [[Set]] field and a [[Value]] or
///     [[Writable]] field, throw a TypeError (not reachable while accessors
///     are `NotYet`).
fn to_property_descriptor(vm: &mut Vm, obj: Value) -> Result<Descriptor, Abrupt> {
    if !vm.heap().is_object(obj) {
        return Err(vm.type_error("Property description must be an object"));
    }
    let field = |vm: &mut Vm, name: &str| -> Result<Option<Value>, Abrupt> {
        let k = key(vm, name)?;
        if has_property(vm, obj, k)? {
            Ok(Some(vm.get_value(obj, k)?))
        } else {
            Ok(None)
        }
    };
    let enumerable = field(vm, "enumerable")?;
    let configurable = field(vm, "configurable")?;
    let value = field(vm, "value")?;
    let writable = field(vm, "writable")?;
    let get = field(vm, "get")?;
    let set = field(vm, "set")?;
    if get.is_some() || set.is_some() {
        return Err(Abrupt::NotYet("accessor property descriptors".into()));
    }
    Ok(Descriptor {
        value,
        writable: writable.map(|v| vm.to_boolean(v)),
        enumerable: enumerable.map(|v| vm.to_boolean(v)),
        configurable: configurable.map(|v| vm.to_boolean(v)),
    })
}

/// `Object.defineProperty ( O, P, Attributes )`, §20.1.2.4†:
/// 1. If O is not an Object, throw a TypeError exception.
/// 2. Let key be ? ToPropertyKey(P).
/// 3. Let desc be ? ToPropertyDescriptor(Attributes).
/// 4. Perform ? DefinePropertyOrThrow(O, key, desc).
/// 5. Return O.
fn define_property(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = arg(args, 0);
    if !vm.heap().is_object(o) {
        return Err(vm.type_error("Object.defineProperty called on non-object"));
    }
    let k = vm.coerce_property_key(arg(args, 1))?;
    let desc = to_property_descriptor(vm, arg(args, 2))?;
    define_property_or_throw(vm, o, k, &desc)?;
    Ok(o)
}

/// DefinePropertyOrThrow, §7.3.8†, over `[[DefineOwnProperty]]`
/// (`Vm::define_own_property`: OrdinaryDefineOwnProperty §10.1.6.1† and the
/// Array exotic object's §10.4.2.1†); a false result is a TypeError.
fn define_property_or_throw(
    vm: &mut Vm,
    obj: Value,
    k: clazel_js_heap::string::Key,
    desc: &Descriptor,
) -> Result<(), Abrupt> {
    let d = PropDesc {
        value: desc.value,
        writable: desc.writable,
        enumerable: desc.enumerable,
        configurable: desc.configurable,
    };
    vm.define_property_or_throw(obj, k, &d)
}
