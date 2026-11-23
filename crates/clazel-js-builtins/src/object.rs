//! `Object` (§20.1†): the constructor and every function of `Object` (§20.1.2†:
//! `assign`, `create`, `defineProperties`, `defineProperty`, `entries`,
//! `freeze`, `fromEntries`, `getOwnPropertyDescriptor(s)`,
//! `getOwnPropertyNames`, `getOwnPropertySymbols`, `getPrototypeOf`,
//! `groupBy`, `hasOwn`, `is`, `isExtensible`, `isFrozen`, `isSealed`, `keys`,
//! `preventExtensions`, `seal`, `setPrototypeOf`, `values`), and
//! `Object.prototype` (§20.1.3†: `hasOwnProperty`, `isPrototypeOf`,
//! `propertyIsEnumerable`, `toLocaleString`, `toString`, `valueOf`, and Annex B's
//! `__proto__`, `__defineGetter__`, `__defineSetter__`, `__lookupGetter__`,
//! `__lookupSetter__`, §B.2.2†).
//!
//! Modelling choices and deviations:
//!
//! - **No Proxy yet**, so every `[[GetOwnProperty]]`, `[[DefineOwnProperty]]`,
//!   `[[OwnPropertyKeys]]`, `[[PreventExtensions]]` and `[[SetPrototypeOf]]`
//!   here is the ordinary one (§10.1†) or the Array exotic one (§10.4.2†).
//! - **A String wrapper object has no index properties** (the deviation of
//!   `lib.rs`), so `Object.getOwnPropertyNames(new String("ab"))` lists
//!   `length` and not `0` and `1`.
//! - **`Object.fromEntries` calls its adder inline** instead of through an
//!   Abstract Closure function object: the closure is never observable.

use crate::util::{
    accessor, arg, constructor, has_own_property, has_property, key, method, new_array_like,
    new_object_with, own_property_keys, same_value, string,
};
use clazel_js_heap::shape::Attrs;
use clazel_js_heap::string::Key;
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
    method(vm, proto, "toLocaleString", 0, to_locale_string)?;
    method(vm, proto, "toString", 0, to_string)?;
    method(vm, proto, "valueOf", 0, value_of)?;
    method(vm, ctor, "keys", 1, keys)?;
    method(vm, ctor, "defineProperty", 3, define_property)?;
    method(vm, ctor, "getPrototypeOf", 1, get_prototype_of)?;
    method(vm, ctor, "create", 2, create)?;
    method(
        vm,
        ctor,
        "getOwnPropertyDescriptor",
        2,
        get_own_property_descriptor,
    )?;
    method(
        vm,
        ctor,
        "getOwnPropertyDescriptors",
        1,
        get_own_property_descriptors,
    )?;
    method(vm, ctor, "getOwnPropertyNames", 1, get_own_property_names)?;
    method(
        vm,
        ctor,
        "getOwnPropertySymbols",
        1,
        get_own_property_symbols,
    )?;
    method(vm, ctor, "defineProperties", 2, define_properties_fn)?;
    method(vm, ctor, "entries", 1, entries)?;
    method(vm, ctor, "values", 1, values)?;
    method(vm, ctor, "assign", 2, assign)?;
    method(vm, ctor, "is", 2, is)?;
    method(vm, ctor, "hasOwn", 2, has_own)?;
    method(vm, ctor, "fromEntries", 1, from_entries)?;
    method(vm, ctor, "groupBy", 2, group_by)?;
    method(vm, ctor, "freeze", 1, freeze)?;
    method(vm, ctor, "seal", 1, seal)?;
    method(vm, ctor, "isFrozen", 1, is_frozen)?;
    method(vm, ctor, "isSealed", 1, is_sealed)?;
    method(vm, ctor, "preventExtensions", 1, prevent_extensions)?;
    method(vm, ctor, "isExtensible", 1, is_extensible)?;
    method(vm, ctor, "setPrototypeOf", 2, set_prototype_of)?;
    method(vm, proto, "isPrototypeOf", 1, is_prototype_of)?;
    method(vm, proto, "propertyIsEnumerable", 1, property_is_enumerable)?;
    method(vm, proto, "__defineGetter__", 2, define_getter)?;
    method(vm, proto, "__defineSetter__", 2, define_setter)?;
    method(vm, proto, "__lookupGetter__", 1, lookup_getter)?;
    method(vm, proto, "__lookupSetter__", 1, lookup_setter)?;
    let k = key(vm, "__proto__")?;
    accessor(
        vm,
        proto,
        k,
        "__proto__",
        Some(proto_getter),
        Some(proto_setter),
    )?;
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
/// 15. Let tag be ? Get(O, @@toStringTag).
/// 16. If tag is not a String, set tag to builtinTag.
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
            Some(ObjKind::Arguments) => "Arguments",
            Some(ObjKind::Primitive(p)) => match p.decode() {
                Decoded::Bool(_) => "Boolean",
                Decoded::Int32(_) | Decoded::Double(_) => "Number",
                _ if vm.heap().is_string(p) => "String",
                _ => "Object",
            },
            _ if crate::regexp::has_regexp_matcher(vm, o) => "RegExp",
            _ => "Object",
        }
    };
    let k = vm.well_known_key(clazel_js_heap::symbol::TO_STRING_TAG)?;
    let t = vm.get_value(o, k)?;
    if let Some(t) = vm.heap().string(t) {
        let mut units: Vec<u16> = "[object ".encode_utf16().collect();
        units.extend(t.units());
        units.push(u16::from(b']'));
        let s = clazel_js_heap::string::JsString::from_units(&units)
            .map_err(|_| Abrupt::OutOfMemory)?;
        return crate::util::js_string(vm, s);
    }
    string(vm, &format!("[object {tag}]"))
}

/// `Object.prototype.toLocaleString ( [ reserved1 [ , reserved2 ] ] )`,
/// §20.1.3.5†:
/// 1. Let O be the this value.
/// 2. Return ? Invoke(O, "toString").
///
/// Invoke ( V, P [ , argumentsList ] ), §7.3.20†: GetV(V, P), then Call;
/// a value that is not callable is a TypeError.
fn to_locale_string(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let k = key(vm, "toString")?;
    let f = vm.get_value(this, k)?;
    if !vm.heap().is_callable(f) {
        return Err(vm.type_error("toString is not a function"));
    }
    vm.call(f, this, &[])
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
pub struct Descriptor {
    /// `[[Value]]`.
    pub value: Option<Value>,
    /// `[[Writable]]`.
    pub writable: Option<bool>,
    /// `[[Get]]`: a function or `undefined`.
    pub get: Option<Value>,
    /// `[[Set]]`: a function or `undefined`.
    pub set: Option<Value>,
    /// `[[Enumerable]]`.
    pub enumerable: Option<bool>,
    /// `[[Configurable]]`.
    pub configurable: Option<bool>,
}

/// ToPropertyDescriptor ( Obj ), §6.2.6.5†:
/// 1. If Obj is not an Object, throw a TypeError exception.
/// 2. Let desc be a new Property Descriptor that initially has no fields.
/// 3. Let hasEnumerable be ? HasProperty(Obj, "enumerable").
/// 4. If hasEnumerable is true, then
///    a. Let enumerable be ToBoolean(? Get(Obj, "enumerable")).
///    b. Set desc.[[Enumerable]] to enumerable.
/// 5. to 10. The same for "configurable", "value" and "writable".
/// 11. Let hasGet be ? HasProperty(Obj, "get").
/// 12. If hasGet is true, then a. Let getter be ? Get(Obj, "get"). b. If
///     IsCallable(getter) is false and getter is not undefined, throw a
///     TypeError exception. c. Set desc.[[Get]] to getter.
/// 13. and 14. The same for "set".
/// 15. If desc has a [[Get]] or [[Set]] field, then a. If desc has a
///     [[Value]] or [[Writable]] field, throw a TypeError exception.
/// 16. Return desc.
pub fn to_property_descriptor(vm: &mut Vm, obj: Value) -> Result<Descriptor, Abrupt> {
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
    for f in [get, set].into_iter().flatten() {
        if f != Value::UNDEFINED && !vm.heap().is_callable(f) {
            return Err(vm.type_error("Getter or setter must be a function"));
        }
    }
    if (get.is_some() || set.is_some()) && (value.is_some() || writable.is_some()) {
        return Err(vm.type_error(
            "Invalid property descriptor. Cannot both specify accessors and a value or writable attribute",
        ));
    }
    Ok(Descriptor {
        value,
        writable: writable.map(|v| vm.to_boolean(v)),
        get,
        set,
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
///
/// # Errors
/// A `TypeError` when the definition is refused, [`Abrupt::OutOfMemory`].
pub fn define_property_or_throw(
    vm: &mut Vm,
    obj: Value,
    k: clazel_js_heap::string::Key,
    desc: &Descriptor,
) -> Result<(), Abrupt> {
    let d = PropDesc {
        value: desc.value,
        writable: desc.writable,
        get: desc.get,
        set: desc.set,
        enumerable: desc.enumerable,
        configurable: desc.configurable,
    };
    vm.define_property_or_throw(obj, k, &d)
}

// ---------------------------------------------------------------------
// Property descriptors
// ---------------------------------------------------------------------

/// FromPropertyDescriptor ( Desc ), §6.2.6.4†:
/// 1. If Desc is undefined, return undefined.
/// 2. Let obj be OrdinaryObjectCreate(%Object.prototype%).
/// 3. Assert: obj is an extensible ordinary object with no own properties.
/// 4. If Desc has a [[Value]] field, then perform ! CreateDataPropertyOrThrow(
///    obj, "value", Desc.[[Value]]).
/// 5. If Desc has a [[Writable]] field, ... "writable".
/// 6. If Desc has a [[Get]] field, ... "get".
/// 7. If Desc has a [[Set]] field, ... "set".
/// 8. If Desc has an [[Enumerable]] field, ... "enumerable".
/// 9. If Desc has a [[Configurable]] field, ... "configurable".
/// 10. Return obj.
fn from_property_descriptor(vm: &mut Vm, desc: Option<PropDesc>) -> Result<Value, Abrupt> {
    let Some(d) = desc else {
        return Ok(Value::UNDEFINED);
    };
    let obj = vm.new_object()?;
    let fields = [
        ("value", d.value),
        ("writable", d.writable.map(Value::boolean)),
        ("get", d.get),
        ("set", d.set),
        ("enumerable", d.enumerable.map(Value::boolean)),
        ("configurable", d.configurable.map(Value::boolean)),
    ];
    for (name, v) in fields {
        if let Some(v) = v {
            let k = key(vm, name)?;
            vm.heap_mut().define(obj, k, v, Attrs::ALL)?;
        }
    }
    Ok(obj)
}

/// `[[GetOwnProperty]] ( P )` as a complete Property Descriptor: OrdinaryGetOwnProperty
/// (§10.1.5.1†).
fn get_own_property(vm: &Vm, obj: Value, k: Key) -> Result<Option<PropDesc>, Abrupt> {
    vm.own_property_descriptor(obj, k)
}

/// Whether an own property exists and is enumerable.
fn is_enumerable_own(vm: &Vm, obj: Value, k: Key) -> Result<bool, Abrupt> {
    Ok(get_own_property(vm, obj, k)?.is_some_and(|d| d.enumerable == Some(true)))
}

/// `Object.getOwnPropertyDescriptor ( O, P )`, §20.1.2.8†:
/// 1. Let obj be ? ToObject(O).
/// 2. Let key be ? ToPropertyKey(P).
/// 3. Let desc be ? obj.[[GetOwnProperty]](key).
/// 4. Return FromPropertyDescriptor(desc).
fn get_own_property_descriptor(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let obj = vm.to_object(arg(args, 0))?;
    let k = vm.coerce_property_key(arg(args, 1))?;
    let desc = get_own_property(vm, obj, k)?;
    from_property_descriptor(vm, desc)
}

/// `Object.getOwnPropertyDescriptors ( O )`, §20.1.2.9†:
/// 1. Let obj be ? ToObject(O).
/// 2. Let ownKeys be ? obj.[[OwnPropertyKeys]]().
/// 3. Let descriptors be OrdinaryObjectCreate(%Object.prototype%).
/// 4. For each element key of ownKeys, do
///    a. Let desc be ? obj.[[GetOwnProperty]](key).
///    b. Let descriptor be FromPropertyDescriptor(desc).
///    c. If descriptor is not undefined, perform ! CreateDataPropertyOrThrow(
///    descriptors, key, descriptor).
/// 5. Return descriptors.
fn get_own_property_descriptors(
    vm: &mut Vm,
    _this: Value,
    args: &[Value],
) -> Result<Value, Abrupt> {
    let obj = vm.to_object(arg(args, 0))?;
    let out = vm.new_object()?;
    for k in own_property_keys(vm, obj) {
        let desc = get_own_property(vm, obj, k)?;
        let d = from_property_descriptor(vm, desc)?;
        if d != Value::UNDEFINED {
            vm.create_data_property_or_throw(out, k, d)?;
        }
    }
    Ok(out)
}

/// GetOwnPropertyKeys ( O, type ), §20.1.2.11.1†:
/// 1. Let keys be ? O.[[OwnPropertyKeys]]().
/// 2. Let nameList be a new empty List.
/// 3. For each element nextKey of keys, do
///    a. If nextKey is a Symbol and type is symbol, or nextKey is a String and
///    type is string, append nextKey to nameList.
/// 4. Return nameList.
fn own_keys_of_type(vm: &mut Vm, o: Value, symbols: bool) -> Result<Value, Abrupt> {
    let obj = vm.to_object(o)?;
    let mut items = Vec::new();
    for k in own_property_keys(vm, obj) {
        if clazel_js_vm::heap::Heap::key_symbol(k).is_some() == symbols {
            items.push(vm.key_value(k)?);
        }
    }
    new_array_like(vm, &items)
}

/// `Object.getOwnPropertyNames ( O )`, §20.1.2.10†:
/// 1. Return CreateArrayFromList(? GetOwnPropertyKeys(O, string)).
fn get_own_property_names(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    own_keys_of_type(vm, arg(args, 0), false)
}

/// `Object.getOwnPropertySymbols ( O )`, §20.1.2.11†:
/// 1. Return CreateArrayFromList(? GetOwnPropertyKeys(O, symbol)).
fn get_own_property_symbols(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    own_keys_of_type(vm, arg(args, 0), true)
}

/// `Object.defineProperties ( O, Properties )`, §20.1.2.3†:
/// 1. If O is not an Object, throw a TypeError exception.
/// 2. Return ? ObjectDefineProperties(O, Properties).
fn define_properties_fn(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = arg(args, 0);
    if !vm.heap().is_object(o) {
        return Err(vm.type_error("Object.defineProperties called on non-object"));
    }
    define_properties(vm, o, arg(args, 1))?;
    Ok(o)
}

// ---------------------------------------------------------------------
// Enumeration
// ---------------------------------------------------------------------

/// What EnumerableOwnProperties (§7.3.23†) collects.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Key,
    Value,
    KeyValue,
}

/// EnumerableOwnProperties ( O, kind ), §7.3.23†:
/// 1. Let ownKeys be ? O.[[OwnPropertyKeys]]().
/// 2. Let results be a new empty List.
/// 3. For each element key of ownKeys, do
///    a. If key is a String, then
///    i. Let desc be ? O.[[GetOwnProperty]](key).
///    ii. If desc is not undefined and desc.[[Enumerable]] is true, then
///    1. If kind is key, append key to results.
///    2. Else, a. Let value be ? Get(O, key). b. If kind is value, append
///       value to results. c. Else, append CreateArrayFromList(« key, value »).
/// 4. Return results.
fn enumerable_own_properties(vm: &mut Vm, obj: Value, kind: Kind) -> Result<Vec<Value>, Abrupt> {
    let mut results = Vec::new();
    for k in own_property_keys(vm, obj) {
        if clazel_js_vm::heap::Heap::key_symbol(k).is_some() {
            continue;
        }
        if !is_enumerable_own(vm, obj, k)? {
            continue;
        }
        if kind == Kind::Key {
            results.push(vm.key_value(k)?);
            continue;
        }
        let v = vm.get_value(obj, k)?;
        if kind == Kind::Value {
            results.push(v);
        } else {
            let name = vm.key_value(k)?;
            results.push(new_array_like(vm, &[name, v])?);
        }
    }
    Ok(results)
}

/// `Object.entries ( O )`, §20.1.2.5†:
/// 1. Let obj be ? ToObject(O).
/// 2. Let entryList be ? EnumerableOwnProperties(obj, key+value).
/// 3. Return CreateArrayFromList(entryList).
fn entries(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let obj = vm.to_object(arg(args, 0))?;
    let list = enumerable_own_properties(vm, obj, Kind::KeyValue)?;
    new_array_like(vm, &list)
}

/// `Object.values ( O )`, §20.1.2.23†:
/// 1. Let obj be ? ToObject(O).
/// 2. Let valueList be ? EnumerableOwnProperties(obj, value).
/// 3. Return CreateArrayFromList(valueList).
fn values(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let obj = vm.to_object(arg(args, 0))?;
    let list = enumerable_own_properties(vm, obj, Kind::Value)?;
    new_array_like(vm, &list)
}

/// `Object.assign ( target, ...sources )`, §20.1.2.1†:
/// 1. Let to be ? ToObject(target).
/// 2. If only one argument was passed, return to.
/// 3. Let sources be the List of argument values starting with the second
///    argument.
/// 4. For each element nextSource of sources, do
///    a. If nextSource is neither undefined nor null, then
///    i. Let from be ! ToObject(nextSource).
///    ii. Let keys be ? from.[[OwnPropertyKeys]]().
///    iii. For each element nextKey of keys, do
///    1. Let desc be ? from.[[GetOwnProperty]](nextKey).
///    2. If desc is not undefined and desc.[[Enumerable]] is true, then
///       a. Let propValue be ? Get(from, nextKey).
///       b. Perform ? Set(to, nextKey, propValue, true).
/// 5. Return to.
fn assign(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let to = vm.to_object(arg(args, 0))?;
    for next in args.iter().skip(1) {
        if *next == Value::UNDEFINED || *next == Value::NULL {
            continue;
        }
        let from = vm.to_object(*next)?;
        for k in own_property_keys(vm, from) {
            vm.charge_step()?;
            if is_enumerable_own(vm, from, k)? {
                let v = vm.get_value(from, k)?;
                vm.put_value(to, k, v, true)?;
            }
        }
    }
    Ok(to)
}

/// `Object.is ( value1, value2 )`, §20.1.2.15†: 1. Return SameValue(value1,
/// value2).
fn is(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    Ok(Value::boolean(same_value(vm, arg(args, 0), arg(args, 1))))
}

/// `Object.hasOwn ( O, P )`, §20.1.2.14†:
/// 1. Let obj be ? ToObject(O).
/// 2. Let key be ? ToPropertyKey(P).
/// 3. Return ? HasOwnProperty(obj, key).
fn has_own(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let obj = vm.to_object(arg(args, 0))?;
    let k = vm.coerce_property_key(arg(args, 1))?;
    Ok(Value::boolean(has_own_property(vm, obj, k)?))
}

/// `Object.fromEntries ( iterable )`, §20.1.2.7†:
/// 1. Perform ? RequireObjectCoercible(iterable).
/// 2. Let obj be OrdinaryObjectCreate(%Object.prototype%).
/// 3. Assert: obj is an extensible ordinary object with no own properties.
/// 4. Let closure be a new Abstract Closure with parameters (key, value) that
///    captures obj and performs the following steps when called:
///    a. Let propertyKey be ? ToPropertyKey(key).
///    b. Perform ! CreateDataPropertyOrThrow(obj, propertyKey, value).
///    c. Return undefined.
/// 5. Let adder be CreateBuiltinFunction(closure, 2, "", « »).
/// 6. Return ? AddEntriesFromIterable(obj, iterable, adder).
///
/// AddEntriesFromIterable ( target, iterable, adder ), §24.1.1.2†:
/// 1. Let iteratorRecord be ? GetIterator(iterable, sync).
/// 2. Repeat,
///    a. Let next be ? IteratorStepValue(iteratorRecord).
///    b. If next is done, return target.
///    c. If next is not an Object, then i. Let error be ThrowCompletion(a newly
///    created TypeError object). ii. Return ? IteratorClose(iteratorRecord,
///    error).
///    d. Let k be Completion(Get(next, "0")).
///    e. IfAbruptCloseIterator(k, iteratorRecord).
///    f. Let v be Completion(Get(next, "1")).
///    g. IfAbruptCloseIterator(v, iteratorRecord).
///    h. Let status be Completion(Call(adder, target, « k, v »)).
///    i. IfAbruptCloseIterator(status, iteratorRecord).
///
/// The adder is called directly: the closure's two steps are inlined.
fn from_entries(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let iterable = arg(args, 0);
    if iterable == Value::UNDEFINED || iterable == Value::NULL {
        return Err(vm.type_error("Object.fromEntries requires an iterable"));
    }
    let obj = vm.new_object()?;
    let rec = vm.get_iterator(iterable)?;
    while let Some(next) = vm.iterator_step_value(rec)? {
        vm.charge_step()?;
        let step = (|| -> Result<(), Abrupt> {
            if !vm.heap().is_object(next) {
                return Err(vm.type_error("Iterator value is not an entry object"));
            }
            let k0 = key(vm, "0")?;
            let k1 = key(vm, "1")?;
            let k = vm.get_value(next, k0)?;
            let v = vm.get_value(next, k1)?;
            let pk = vm.coerce_property_key(k)?;
            vm.create_data_property_or_throw(obj, pk, v)
        })();
        if let Err(e) = step {
            return Err(vm.iterator_close_on_throw(rec, e));
        }
    }
    Ok(obj)
}

/// `Object.groupBy ( items, callback )`, §20.1.2.13†:
/// 1. Let groups be ? GroupBy(items, callback, property).
/// 2. Let obj be OrdinaryObjectCreate(null).
/// 3. For each Record { [[Key]], [[Elements]] } g of groups, do
///    a. Let elements be CreateArrayFromList(g.[[Elements]]).
///    b. Perform ! CreateDataPropertyOrThrow(obj, g.[[Key]], elements).
/// 4. Return obj.
///
/// GroupBy ( items, callback, keyCoercion ), §7.3.35†:
/// 1. Perform ? RequireObjectCoercible(items).
/// 2. If IsCallable(callback) is false, throw a TypeError exception.
/// 3. Let groups be a new empty List.
/// 4. Let iteratorRecord be ? GetIterator(items, sync).
/// 5. Let k be 0.
/// 6. Repeat,
///    a. If k ≥ 2^53 - 1, then ... close the iterator with a TypeError.
///    b. Let next be ? IteratorStepValue(iteratorRecord).
///    c. If next is done, return groups.
///    d. Let value be next.
///    e. Let key be Completion(Call(callback, undefined, « value, 𝔽(k) »)).
///    f. IfAbruptCloseIterator(key, iteratorRecord).
///    g. If keyCoercion is property, then i. Set key to Completion(
///    ToPropertyKey(key)). ii. IfAbruptCloseIterator(key, iteratorRecord).
///    h. Else, (zero) ...
///    i. Perform AddValueToKeyedGroup(groups, key, value).
///    j. Set k to k + 1.
fn group_by(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let (items, callback) = (arg(args, 0), arg(args, 1));
    if items == Value::UNDEFINED || items == Value::NULL {
        return Err(vm.type_error("Object.groupBy requires an iterable"));
    }
    if !vm.heap().is_callable(callback) {
        return Err(vm.type_error("Object.groupBy: callback is not a function"));
    }
    let rec = vm.get_iterator(items)?;
    let mut groups: Vec<(Key, Vec<Value>)> = Vec::new();
    let mut k: i32 = 0;
    while let Some(value) = vm.iterator_step_value(rec)? {
        vm.charge_step()?;
        let key_result = vm
            .call(callback, Value::UNDEFINED, &[value, Value::int32(k)])
            .and_then(|kv| vm.coerce_property_key(kv));
        let pk = match key_result {
            Ok(pk) => pk,
            Err(e) => return Err(vm.iterator_close_on_throw(rec, e)),
        };
        match groups.iter_mut().find(|(gk, _)| *gk == pk) {
            Some((_, els)) => els.push(value),
            None => groups.push((pk, vec![value])),
        }
        k = k.saturating_add(1);
    }
    let obj = new_object_with(vm, Value::NULL, ObjKind::Plain)?;
    for (gk, els) in groups {
        let arr = new_array_like(vm, &els)?;
        vm.create_data_property_or_throw(obj, gk, arr)?;
    }
    Ok(obj)
}

// ---------------------------------------------------------------------
// Integrity levels, extensibility, the prototype
// ---------------------------------------------------------------------

/// SetIntegrityLevel ( O, level ), §7.3.15†:
/// 1. Let status be ? O.[[PreventExtensions]]().
/// 2. If status is false, return false.
/// 3. Let keys be ? O.[[OwnPropertyKeys]]().
/// 4. If level is sealed, then
///    a. For each element k of keys, do i. Perform ? DefinePropertyOrThrow(O,
///    k, { [[Configurable]]: false }).
/// 5. Else,
///    a. Assert: level is frozen.
///    b. For each element k of keys, do
///    i. Let currentDesc be ? O.[[GetOwnProperty]](k).
///    ii. If currentDesc is not undefined, then
///    1. If IsAccessorDescriptor(currentDesc) is true, then a. Let desc be the
///       PropertyDescriptor { [[Configurable]]: false }.
///    2. Else, a. Let desc be the PropertyDescriptor { [[Configurable]]:
///       false, [[Writable]]: false }.
///    3. Perform ? DefinePropertyOrThrow(O, k, desc).
/// 6. Return true.
fn set_integrity_level(vm: &mut Vm, o: Value, frozen: bool) -> Result<bool, Abrupt> {
    if !vm.prevent_extensions(o)? {
        return Ok(false);
    }
    for k in own_property_keys(vm, o) {
        vm.charge_step()?;
        let mut desc = PropDesc {
            configurable: Some(false),
            ..PropDesc::default()
        };
        if frozen {
            let Some(current) = get_own_property(vm, o, k)? else {
                continue;
            };
            if !current.is_accessor() {
                desc.writable = Some(false);
            }
        }
        vm.define_property_or_throw(o, k, &desc)?;
    }
    Ok(true)
}

/// TestIntegrityLevel ( O, level ), §7.3.16†:
/// 1. Let extensible be ? IsExtensible(O).
/// 2. If extensible is true, return false.
/// 3. NOTE: If the object is extensible, none of its properties are examined.
/// 4. Let keys be ? O.[[OwnPropertyKeys]]().
/// 5. For each element k of keys, do
///    a. Let currentDesc be ? O.[[GetOwnProperty]](k).
///    b. If currentDesc is not undefined, then
///    i. If currentDesc.[[Configurable]] is true, return false.
///    ii. If level is frozen and IsDataDescriptor(currentDesc) is true, then
///    1. If currentDesc.[[Writable]] is true, return false.
/// 6. Return true.
fn test_integrity_level(vm: &mut Vm, o: Value, frozen: bool) -> Result<bool, Abrupt> {
    if vm.heap().is_extensible(o) {
        return Ok(false);
    }
    for k in own_property_keys(vm, o) {
        if let Some(d) = get_own_property(vm, o, k)? {
            if d.configurable == Some(true) {
                return Ok(false);
            }
            if frozen && d.is_data() && d.writable == Some(true) {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

/// `Object.freeze ( O )`, §20.1.2.6†:
/// 1. If O is not an Object, return O.
/// 2. Let status be ? SetIntegrityLevel(O, frozen).
/// 3. If status is false, throw a TypeError exception.
/// 4. Return O.
fn freeze(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = arg(args, 0);
    if !vm.heap().is_object(o) {
        return Ok(o);
    }
    if !set_integrity_level(vm, o, true)? {
        return Err(vm.type_error("Cannot freeze"));
    }
    Ok(o)
}

/// `Object.seal ( O )`, §20.1.2.21†: as `freeze`, with level sealed.
fn seal(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = arg(args, 0);
    if !vm.heap().is_object(o) {
        return Ok(o);
    }
    if !set_integrity_level(vm, o, false)? {
        return Err(vm.type_error("Cannot seal"));
    }
    Ok(o)
}

/// `Object.isFrozen ( O )`, §20.1.2.17†:
/// 1. If O is not an Object, return true.
/// 2. Return ? TestIntegrityLevel(O, frozen).
fn is_frozen(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = arg(args, 0);
    if !vm.heap().is_object(o) {
        return Ok(Value::TRUE);
    }
    Ok(Value::boolean(test_integrity_level(vm, o, true)?))
}

/// `Object.isSealed ( O )`, §20.1.2.18†: as `isFrozen`, with level sealed.
fn is_sealed(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = arg(args, 0);
    if !vm.heap().is_object(o) {
        return Ok(Value::TRUE);
    }
    Ok(Value::boolean(test_integrity_level(vm, o, false)?))
}

/// `Object.preventExtensions ( O )`, §20.1.2.20†:
/// 1. If O is not an Object, return O.
/// 2. Let status be ? O.[[PreventExtensions]]().
/// 3. If status is false, throw a TypeError exception.
/// 4. Return O.
fn prevent_extensions(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = arg(args, 0);
    if !vm.heap().is_object(o) {
        return Ok(o);
    }
    if !vm.prevent_extensions(o)? {
        return Err(vm.type_error("Cannot prevent extensions"));
    }
    Ok(o)
}

/// `Object.isExtensible ( O )`, §20.1.2.16†:
/// 1. If O is not an Object, return false.
/// 2. Return ? IsExtensible(O).
fn is_extensible(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = arg(args, 0);
    Ok(Value::boolean(
        vm.heap().is_object(o) && vm.heap().is_extensible(o),
    ))
}

/// `Object.setPrototypeOf ( O, proto )`, §20.1.2.22†:
/// 1. Set O to ? RequireObjectCoercible(O).
/// 2. If proto is not an Object and proto is not null, throw a TypeError
///    exception.
/// 3. If O is not an Object, return O.
/// 4. Let status be ? O.[[SetPrototypeOf]](proto).
/// 5. If status is false, throw a TypeError exception.
/// 6. Return O.
fn set_prototype_of(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let (o, proto) = (arg(args, 0), arg(args, 1));
    if o == Value::UNDEFINED || o == Value::NULL {
        return Err(vm.type_error("Object.setPrototypeOf called on null or undefined"));
    }
    if proto != Value::NULL && !vm.heap().is_object(proto) {
        return Err(vm.type_error("Object prototype may only be an Object or null"));
    }
    if !vm.heap().is_object(o) {
        return Ok(o);
    }
    if !vm.set_prototype_of(o, proto)? {
        return Err(vm.type_error("Cannot set the prototype of this object"));
    }
    Ok(o)
}

// ---------------------------------------------------------------------
// Object.prototype
// ---------------------------------------------------------------------

/// `Object.prototype.isPrototypeOf ( V )`, §20.1.3.3†:
/// 1. If V is not an Object, return false.
/// 2. Let O be ? ToObject(this value).
/// 3. Repeat, a. Set V to ? V.[[GetPrototypeOf]](). b. If V is null, return
///    false. c. If SameValue(O, V) is true, return true.
fn is_prototype_of(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let mut v = arg(args, 0);
    if !vm.heap().is_object(v) {
        return Ok(Value::FALSE);
    }
    let o = vm.to_object(this)?;
    loop {
        vm.charge_step()?;
        v = vm.heap().proto_of(v).unwrap_or(Value::NULL);
        if !vm.heap().is_object(v) {
            return Ok(Value::FALSE);
        }
        if v == o {
            return Ok(Value::TRUE);
        }
    }
}

/// `Object.prototype.propertyIsEnumerable ( V )`, §20.1.3.4†:
/// 1. Let P be ? ToPropertyKey(V).
/// 2. Let O be ? ToObject(this value).
/// 3. Let desc be ? O.[[GetOwnProperty]](P).
/// 4. If desc is undefined, return false.
/// 5. Return desc.[[Enumerable]].
fn property_is_enumerable(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let k = vm.coerce_property_key(arg(args, 0))?;
    let o = vm.to_object(this)?;
    Ok(Value::boolean(is_enumerable_own(vm, o, k)?))
}

/// `get Object.prototype.__proto__`, §B.2.2.1.1†:
/// 1. Let O be ? ToObject(this value).
/// 2. Return ? O.[[GetPrototypeOf]]().
fn proto_getter(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    Ok(vm.heap().proto_of(o).unwrap_or(Value::NULL))
}

/// `set Object.prototype.__proto__`, §B.2.2.1.2†:
/// 1. Let O be ? RequireObjectCoercible(this value).
/// 2. If proto is not an Object and proto is not null, return undefined.
/// 3. If O is not an Object, return undefined.
/// 4. Let status be ? O.[[SetPrototypeOf]](proto).
/// 5. If status is false, throw a TypeError exception.
/// 6. Return undefined.
fn proto_setter(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    if this == Value::UNDEFINED || this == Value::NULL {
        return Err(vm.type_error("Object.prototype.__proto__ called on null or undefined"));
    }
    let proto = arg(args, 0);
    if proto != Value::NULL && !vm.heap().is_object(proto) {
        return Ok(Value::UNDEFINED);
    }
    if !vm.heap().is_object(this) {
        return Ok(Value::UNDEFINED);
    }
    if !vm.set_prototype_of(this, proto)? {
        return Err(vm.type_error("Cannot set the prototype of this object"));
    }
    Ok(Value::UNDEFINED)
}

/// `Object.prototype.__defineGetter__ ( P, getter )`, §B.2.2.2†:
/// 1. Let O be ? ToObject(this value).
/// 2. If IsCallable(getter) is false, throw a TypeError exception.
/// 3. Let desc be PropertyDescriptor { [[Get]]: getter, [[Enumerable]]: true,
///    [[Configurable]]: true }.
/// 4. Let key be ? ToPropertyKey(P).
/// 5. Perform ? DefinePropertyOrThrow(O, key, desc).
/// 6. Return undefined.
fn define_getter(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    define_legacy_accessor(vm, this, args, true)
}

/// `Object.prototype.__defineSetter__ ( P, setter )`, §B.2.2.3†: as
/// `__defineGetter__`, with [[Set]].
fn define_setter(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    define_legacy_accessor(vm, this, args, false)
}

fn define_legacy_accessor(
    vm: &mut Vm,
    this: Value,
    args: &[Value],
    getter: bool,
) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let f = arg(args, 1);
    if !vm.heap().is_callable(f) {
        return Err(vm.type_error("accessor is not a function"));
    }
    let desc = PropDesc {
        get: getter.then_some(f),
        set: (!getter).then_some(f),
        enumerable: Some(true),
        configurable: Some(true),
        ..PropDesc::default()
    };
    let k = vm.coerce_property_key(arg(args, 0))?;
    vm.define_property_or_throw(o, k, &desc)?;
    Ok(Value::UNDEFINED)
}

/// `Object.prototype.__lookupGetter__ ( P )`, §B.2.2.4†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let key be ? ToPropertyKey(P).
/// 3. Repeat, a. Let desc be ? O.[[GetOwnProperty]](key). b. If desc is not
///    undefined, then i. If IsAccessorDescriptor(desc) is true, return
///    desc.[[Get]]. ii. Return undefined. c. Set O to ? O.[[GetPrototypeOf]]().
///    d. If O is null, return undefined.
fn lookup_getter(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    lookup_legacy_accessor(vm, this, args, true)
}

/// `Object.prototype.__lookupSetter__ ( P )`, §B.2.2.5†: as `__lookupGetter__`
/// with [[Set]].
fn lookup_setter(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    lookup_legacy_accessor(vm, this, args, false)
}

fn lookup_legacy_accessor(
    vm: &mut Vm,
    this: Value,
    args: &[Value],
    getter: bool,
) -> Result<Value, Abrupt> {
    let mut o = vm.to_object(this)?;
    let k = vm.coerce_property_key(arg(args, 0))?;
    loop {
        vm.charge_step()?;
        if let Some(d) = get_own_property(vm, o, k)? {
            if d.is_accessor() {
                let f = if getter { d.get } else { d.set };
                return Ok(f.unwrap_or(Value::UNDEFINED));
            }
            return Ok(Value::UNDEFINED);
        }
        o = vm.heap().proto_of(o).unwrap_or(Value::NULL);
        if !vm.heap().is_object(o) {
            return Ok(Value::UNDEFINED);
        }
    }
}
