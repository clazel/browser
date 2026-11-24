//! `Map` (§24.1†), `Set` (§24.2†), `WeakMap` (§24.3†) and `WeakSet` (§24.4†):
//! the constructors, `Map.groupBy`, `@@species`, the prototypes' methods and
//! accessors, the Set methods of ES2025 (`union`, `intersection`,
//! `difference`, `symmetricDifference`, `isSubsetOf`, `isSupersetOf`,
//! `isDisjointFrom`, §24.2.4†) and the Map and Set iterators (§24.1.5†,
//! §24.2.6†).
//!
//! # Modelling choices
//!
//! - **`[[MapData]]` and `[[SetData]]`** are the VM's tables
//!   (`clazel_js_vm::collections`): an insertion-ordered list whose deleted
//!   entries stay as empty places, so an iterator (a place) survives deletions
//!   exactly as the standard's List does. A Set's entries are stored as the key
//!   and the same value (so an entries iterator gives « e, e »).
//! - **A Map or Set is a host object** ([`Vm::into_host_object`]) with the
//!   tag [`TAG_MAP`], [`TAG_SET`], [`TAG_WEAK_MAP`] or [`TAG_WEAK_SET`], so
//!   `RequireInternalSlot` is a tag test. The iterators are host objects with
//!   slots (the collection or `undefined` once done, the place, the kind).
//! - **Weak collections** do not collect: a WeakMap holds its keys and values
//!   and a WeakSet its values for as long as the realm lives, until the
//!   collector (item 7.6) can make them ephemerons. `CanBeHeldWeakly`
//!   (§9.13†) is as the standard says: an Object, or a Symbol that is not in
//!   the GlobalSymbolRegistry.
//!
//! # Differences from the standard, all listed
//!
//! - **Tables are not compacted** (see `clazel_js_vm::collections`).
//! - **`getOrInsert` and `getOrInsertComputed`** of `Map` and `WeakMap` (the
//!   "upsert" proposal, newer than the pinned edition) are present, as the
//!   proposal's text has them.

use crate::iterator::iter_result;
use crate::symbol::to_string_tag;
use crate::util::{
    METHOD, accessor, arg, constructor, get, key, method, new_array_like, new_object_with, number,
    to_integer_or_infinity,
};
use clazel_js_heap::symbol as wk;
use clazel_js_heap::value::{Decoded, Value};
use clazel_js_vm::heap::ObjKind;
use clazel_js_vm::interp::{Abrupt, Intrinsic, NativeFn, Vm};

const TAG_MAP: u32 = 0x5301;
const TAG_SET: u32 = 0x5302;
const TAG_WEAK_MAP: u32 = 0x5303;
const TAG_WEAK_SET: u32 = 0x5304;
const TAG_MAP_ITERATOR: u32 = 0x5305;
const TAG_SET_ITERATOR: u32 = 0x5306;

/// The slots of an iterator: the collection (`undefined` when done), the
/// next place and the kind (0 key, 1 value, 2 key+value).
const I_TARGET: usize = 0;
const I_POS: usize = 1;
const I_KIND: usize = 2;

/// Installs the four collections and their iterators.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    install_map(vm)?;
    install_set(vm)?;
    install_weak(vm)
}

/// The accessor `get X [ @@species ]`, which returns the this value.
fn get_species(_vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    Ok(this)
}

/// Makes a collection prototype's `constructor`, and the constructor's
/// `@@species` accessor.
fn make_constructor(
    vm: &mut Vm,
    name: &str,
    length: i32,
    f: NativeFn,
    intrinsic: Intrinsic,
    species: bool,
) -> Result<(Value, Value), Abrupt> {
    let object_proto = vm.intrinsic(Intrinsic::ObjectPrototype);
    let proto = new_object_with(vm, object_proto, ObjKind::Plain)?;
    vm.set_intrinsic(intrinsic, proto);
    let ctor = constructor(vm, name, length, f, proto)?;
    if species {
        let ks = vm.well_known_key(wk::SPECIES)?;
        accessor(vm, ctor, ks, "[Symbol.species]", Some(get_species), None)?;
    }
    Ok((ctor, proto))
}

/// `RequireInternalSlot ( O, [[MapData]] )` and the like (§7.3.31†): `o` is
/// an object whose host tag is `tag`.
fn require(vm: &mut Vm, o: Value, tag: u32, what: &str) -> Result<(), Abrupt> {
    if vm.heap().is_object(o) && vm.host_tag(o) == Some(tag) {
        Ok(())
    } else {
        Err(vm.type_error(&format!(
            "Method called on incompatible receiver: not a {what}"
        )))
    }
}

/// OrdinaryCreateFromConstructor(NewTarget, proto) with the collection's
/// internal slots: step 2 of `Map ( [ iterable ] )` and its siblings.
fn allocate(vm: &mut Vm, tag: u32, fallback: Intrinsic, name: &str) -> Result<Value, Abrupt> {
    let nt = vm.new_target();
    if nt == Value::UNDEFINED {
        return Err(vm.type_error(&format!("Constructor {name} requires 'new'")));
    }
    let obj = vm.create_from_constructor(nt, fallback, ObjKind::Plain)?;
    vm.into_host_object(obj, tag, Vec::new(), None)?;
    vm.attach_table(obj);
    Ok(obj)
}

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
fn add_entries_from_iterable(
    vm: &mut Vm,
    target: Value,
    iterable: Value,
    adder: Value,
) -> Result<Value, Abrupt> {
    let rec = vm.get_iterator(iterable)?;
    while let Some(next) = vm.iterator_step_value(rec)? {
        vm.charge_step()?;
        let step = (|| -> Result<(), Abrupt> {
            if !vm.heap().is_object(next) {
                return Err(vm.type_error("Iterator value is not an entry object"));
            }
            let k = get(vm, next, "0")?;
            let v = get(vm, next, "1")?;
            vm.call(adder, target, &[k, v])?;
            Ok(())
        })();
        if let Err(e) = step {
            return Err(vm.iterator_close_on_throw(rec, e));
        }
    }
    Ok(target)
}

/// The constructors' steps 4 to 7 for a collection that takes an iterable:
/// 4. If iterable is either undefined or null, return the new object.
/// 5. Let adder be ? Get(object, adderName). 6. If IsCallable(adder) is
///    false, throw a TypeError exception. 7. (Map: AddEntriesFromIterable;
///    Set: iterate and call adder with each value.)
fn fill(
    vm: &mut Vm,
    obj: Value,
    iterable: Value,
    adder_name: &str,
    entries: bool,
) -> Result<Value, Abrupt> {
    if iterable == Value::UNDEFINED || iterable == Value::NULL {
        return Ok(obj);
    }
    let adder = get(vm, obj, adder_name)?;
    if !vm.heap().is_callable(adder) {
        return Err(vm.type_error(&format!(
            "'{adder_name}' returned for property is not a function"
        )));
    }
    if entries {
        return add_entries_from_iterable(vm, obj, iterable, adder);
    }
    let rec = vm.get_iterator(iterable)?;
    while let Some(next) = vm.iterator_step_value(rec)? {
        vm.charge_step()?;
        if let Err(e) = vm.call(adder, obj, &[next]) {
            return Err(vm.iterator_close_on_throw(rec, e));
        }
    }
    Ok(obj)
}

/// An iterator over a collection (CreateMapIterator §24.1.5.1†,
/// CreateSetIterator §24.2.6.1†): a host object whose prototype is
/// `%MapIteratorPrototype%` or `%SetIteratorPrototype%`.
fn create_iterator(
    vm: &mut Vm,
    target: Value,
    kind: i32,
    tag: u32,
    proto: Intrinsic,
) -> Result<Value, Abrupt> {
    let p = vm.intrinsic(proto);
    vm.new_host_object(
        p,
        tag,
        vec![target, Value::int32(0), Value::int32(kind)],
        None,
    )
}

/// `%MapIteratorPrototype%.next ( )`, §24.1.5.2.1†, and
/// `%SetIteratorPrototype%.next ( )`, §24.2.6.2.1† (the generator closure of
/// CreateMapIterator and CreateSetIterator, step by step):
/// 3. Let entries be map.[[MapData]]. 4. Let index be 0. 5. Let numEntries be
///    the number of elements in entries. 6. Repeat, while index < numEntries,
///    a. Let e be entries[index]. b. Set index to index + 1. c. If e.[[Key]]
///    is not empty, then i. If kind is key, let result be e.[[Key]]. ii. Else
///    if kind is value, let result be e.[[Value]]. iii. Else, let result be
///    CreateArrayFromList(« e.[[Key]], e.[[Value]] »). iv. Perform ?
///    GeneratorYield(CreateIterResultObject(result, false)). v. (Set numEntries
///    to the current number of elements.) 7. Return undefined.
///
/// The iterator keeps the place `index`; reaching the end finishes it for
/// good (the generator's completion).
fn iterator_next(vm: &mut Vm, this: Value, tag: u32, what: &str) -> Result<Value, Abrupt> {
    require(vm, this, tag, what)?;
    let target = vm.host_slot(this, I_TARGET).unwrap_or(Value::UNDEFINED);
    if target == Value::UNDEFINED {
        return iter_result(vm, Value::UNDEFINED, true);
    }
    let int_slot = |vm: &Vm, i: usize| match vm.host_slot(this, i).map(Value::decode) {
        Some(Decoded::Int32(n)) => n,
        _ => 0,
    };
    let pos = usize::try_from(int_slot(vm, I_POS)).unwrap_or(0);
    let kind = int_slot(vm, I_KIND);
    match vm.table_next(target, pos) {
        Some((next, k, v)) => {
            let next = i32::try_from(next).map_err(|_| Abrupt::OutOfMemory)?;
            vm.set_host_slot(this, I_POS, Value::int32(next));
            let result = if kind == 0 {
                k
            } else if kind == 1 {
                v
            } else {
                new_array_like(vm, &[k, v])?
            };
            iter_result(vm, result, false)
        }
        None => {
            vm.set_host_slot(this, I_TARGET, Value::UNDEFINED);
            iter_result(vm, Value::UNDEFINED, true)
        }
    }
}

fn map_iterator_next(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    iterator_next(vm, this, TAG_MAP_ITERATOR, "Map Iterator")
}

fn set_iterator_next(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    iterator_next(vm, this, TAG_SET_ITERATOR, "Set Iterator")
}

/// Makes `%XIteratorPrototype%`: its prototype is `%Iterator.prototype%`,
/// with `next` and `@@toStringTag`.
fn make_iterator_prototype(
    vm: &mut Vm,
    intrinsic: Intrinsic,
    next: NativeFn,
    tag: &str,
) -> Result<(), Abrupt> {
    let iter_proto = vm.intrinsic(Intrinsic::IteratorPrototype);
    let p = new_object_with(vm, iter_proto, ObjKind::Plain)?;
    vm.set_intrinsic(intrinsic, p);
    method(vm, p, "next", 0, next)?;
    to_string_tag(vm, p, tag)
}

/// Defines `proto[@@iterator]` as the same function object as
/// `proto[name]` (§24.1.3.12†: "The initial value of the @@iterator property
/// is the same function object as the initial value of the `entries`
/// property"), and returns it.
fn alias_iterator(vm: &mut Vm, proto: Value, name: &str) -> Result<(), Abrupt> {
    let k = key(vm, name)?;
    let f = vm.get_value(proto, k)?;
    let ki = vm.well_known_key(wk::ITERATOR)?;
    vm.heap_mut().define(proto, ki, f, METHOD)?;
    Ok(())
}

/// A count as a Number value.
fn count(n: usize) -> Value {
    number(f64::from(u32::try_from(n).unwrap_or(u32::MAX)))
}

/// A count as a Number.
fn count_f64(n: usize) -> f64 {
    f64::from(u32::try_from(n).unwrap_or(u32::MAX))
}

/// A canonical key: `-0` is `+0` (`Map.prototype.set` step 5, `Set.prototype.add`
/// step 4, §24.1.3.9†, §24.2.4.1†).
fn canonical(v: Value) -> Value {
    match clazel_js_vm::numeric::num(v) {
        Some(n) if n.to_f64() == 0.0 => Value::int32(0),
        _ => v,
    }
}

// ---------------------------------------------------------------------
// Map
// ---------------------------------------------------------------------

fn install_map(vm: &mut Vm) -> Result<(), Abrupt> {
    let (ctor, proto) =
        make_constructor(vm, "Map", 0, map_constructor, Intrinsic::MapPrototype, true)?;
    method(vm, ctor, "groupBy", 2, map_group_by)?;
    method(vm, proto, "clear", 0, map_clear)?;
    method(vm, proto, "delete", 1, map_delete)?;
    method(vm, proto, "entries", 0, map_entries)?;
    method(vm, proto, "forEach", 1, map_for_each)?;
    method(vm, proto, "get", 1, map_get)?;
    method(vm, proto, "getOrInsert", 2, map_get_or_insert)?;
    method(
        vm,
        proto,
        "getOrInsertComputed",
        2,
        map_get_or_insert_computed,
    )?;
    method(vm, proto, "has", 1, map_has)?;
    method(vm, proto, "keys", 0, map_keys)?;
    method(vm, proto, "set", 2, map_set)?;
    let ks = key(vm, "size")?;
    accessor(vm, proto, ks, "size", Some(map_size), None)?;
    method(vm, proto, "values", 0, map_values)?;
    alias_iterator(vm, proto, "entries")?;
    to_string_tag(vm, proto, "Map")?;
    make_iterator_prototype(
        vm,
        Intrinsic::MapIteratorPrototype,
        map_iterator_next,
        "Map Iterator",
    )?;
    crate::util::global(vm, "Map", ctor)
}

/// `Map ( [ iterable ] )`, §24.1.1.1†:
/// 1. If NewTarget is undefined, throw a TypeError exception.
/// 2. Let map be ? OrdinaryCreateFromConstructor(NewTarget, "%Map.prototype%",
///    « [[MapData]] »).
/// 3. Set map.[[MapData]] to a new empty List.
/// 4. If iterable is either undefined or null, return map.
/// 5. Let adder be ? Get(map, "set").
/// 6. If IsCallable(adder) is false, throw a TypeError exception.
/// 7. Return ? AddEntriesFromIterable(map, iterable, adder).
fn map_constructor(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let map = allocate(vm, TAG_MAP, Intrinsic::MapPrototype, "Map")?;
    fill(vm, map, arg(args, 0), "set", true)
}

/// `Map.groupBy ( items, callback )`, §24.1.2.1†:
/// 1. Let groups be ? GroupBy(items, callback, zero).
/// 2. Let map be ! Construct(%Map%).
/// 3. For each Record { [[Key]], [[Elements]] } g of groups, do
///    a. Let elements be CreateArrayFromList(g.[[Elements]]).
///    b. Let entry be the Record { [[Key]]: g.[[Key]], [[Value]]: elements }.
///    c. Append entry to map.[[MapData]].
/// 4. Return map.
///
/// GroupBy (§7.3.35†) with keyCoercion zero: the key `-0` is `+0` and no
/// other conversion; keys are compared by SameValue.
fn map_group_by(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let (items, callback) = (arg(args, 0), arg(args, 1));
    if items == Value::UNDEFINED || items == Value::NULL {
        return Err(vm.type_error("Map.groupBy requires an iterable"));
    }
    if !vm.heap().is_callable(callback) {
        return Err(vm.type_error("Map.groupBy: callback is not a function"));
    }
    let rec = vm.get_iterator(items)?;
    let mut groups: Vec<(Value, Vec<Value>)> = Vec::new();
    let mut k: i32 = 0;
    while let Some(value) = vm.iterator_step_value(rec)? {
        vm.charge_step()?;
        let key = match vm.call(callback, Value::UNDEFINED, &[value, Value::int32(k)]) {
            Ok(key) => canonical(key),
            Err(e) => return Err(vm.iterator_close_on_throw(rec, e)),
        };
        match groups
            .iter_mut()
            .find(|(gk, _)| crate::util::same_value(vm, *gk, key))
        {
            Some((_, els)) => els.push(value),
            None => groups.push((key, vec![value])),
        }
        k = k.saturating_add(1);
    }
    let proto = vm.intrinsic(Intrinsic::MapPrototype);
    let map = vm.new_host_object(proto, TAG_MAP, Vec::new(), None)?;
    vm.attach_table(map);
    for (gk, els) in groups {
        let arr = new_array_like(vm, &els)?;
        vm.table_set(map, gk, arr);
    }
    Ok(map)
}

/// `Map.prototype.clear ( )`, §24.1.3.1†: 1. Let M be the this value. 2.
/// Perform ? RequireInternalSlot(M, [[MapData]]). 3. For each Record { [[Key]],
/// [[Value]] } p of M.[[MapData]], do a. Set p.[[Key]] to empty. b. Set
/// p.[[Value]] to empty. 4. Return undefined.
fn map_clear(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_MAP, "Map")?;
    vm.table_clear(this);
    Ok(Value::UNDEFINED)
}

/// `Map.prototype.delete ( key )`, §24.1.3.3†: 3. For each Record p of
/// M.[[MapData]], do a. If p.[[Key]] is not empty and SameValueZero(p.[[Key]],
/// key) is true, then i. Set p.[[Key]] to empty. ii. Set p.[[Value]] to empty.
/// iii. Return true. 4. Return false.
fn map_delete(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_MAP, "Map")?;
    Ok(Value::boolean(vm.table_delete(this, arg(args, 0))))
}

/// `Map.prototype.entries ( )`, §24.1.3.4†: 1. Let M be the this value. 2.
/// Return ? CreateMapIterator(M, key+value).
fn map_entries(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_MAP, "Map")?;
    create_iterator(
        vm,
        this,
        2,
        TAG_MAP_ITERATOR,
        Intrinsic::MapIteratorPrototype,
    )
}

/// `Map.prototype.keys ( )`, §24.1.3.8†: CreateMapIterator(M, key).
fn map_keys(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_MAP, "Map")?;
    create_iterator(
        vm,
        this,
        0,
        TAG_MAP_ITERATOR,
        Intrinsic::MapIteratorPrototype,
    )
}

/// `Map.prototype.values ( )`, §24.1.3.11†: CreateMapIterator(M, value).
fn map_values(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_MAP, "Map")?;
    create_iterator(
        vm,
        this,
        1,
        TAG_MAP_ITERATOR,
        Intrinsic::MapIteratorPrototype,
    )
}

/// `Map.prototype.forEach ( callbackfn [ , thisArg ] )`, §24.1.3.5†:
/// 3. If IsCallable(callbackfn) is false, throw a TypeError exception.
/// 4. Let entries be M.[[MapData]]. 5. Let numEntries be the number of
///    elements in entries. 6. Let index be 0. 7. Repeat, while index <
///    numEntries, a. Let e be entries[index]. b. Set index to index + 1. c. If
///    e.[[Key]] is not empty, then i. Perform ? Call(callbackfn, thisArg, «
///    e.[[Value]], e.[[Key]], M »). ii. NOTE: The number of elements in entries
///    may have increased during execution of callbackfn. iii. Set numEntries
///    to the number of elements in entries. 8. Return undefined.
fn map_for_each(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_MAP, "Map")?;
    let f = arg(args, 0);
    if !vm.heap().is_callable(f) {
        return Err(vm.type_error("Map.prototype.forEach: callback is not a function"));
    }
    let mut pos = 0;
    while let Some((next, k, v)) = vm.table_next(this, pos) {
        vm.charge_step()?;
        pos = next;
        vm.call(f, arg(args, 1), &[v, k, this])?;
    }
    Ok(Value::UNDEFINED)
}

/// `Map.prototype.get ( key )`, §24.1.3.6†: 3. For each Record p of
/// M.[[MapData]], do a. If p.[[Key]] is not empty and SameValueZero(p.[[Key]],
/// key) is true, return p.[[Value]]. 4. Return undefined.
fn map_get(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_MAP, "Map")?;
    Ok(vm.table_get(this, arg(args, 0)).unwrap_or(Value::UNDEFINED))
}

/// `Map.prototype.getOrInsert ( key, value )` (upsert proposal):
/// 1. Let M be the this value. 2. Perform ? RequireInternalSlot(M, [[MapData]]).
/// 3. Set key to CanonicalizeKeyedCollectionKey(key). 4. For each Record p of
///    M.[[MapData]], do a. If p.[[Key]] is not empty and SameValue(p.[[Key]],
///    key) is true, return p.[[Value]]. 5. Set p to the Record { [[Key]]: key,
///    [[Value]]: value }. 6. Append p to M.[[MapData]]. 7. Return value.
fn map_get_or_insert(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_MAP, "Map")?;
    let key = canonical(arg(args, 0));
    if let Some(v) = vm.table_get(this, key) {
        return Ok(v);
    }
    vm.table_set(this, key, arg(args, 1));
    Ok(arg(args, 1))
}

/// `Map.prototype.getOrInsertComputed ( key, callbackfn )` (upsert proposal):
/// 1. Let M be the this value. 2. Perform ? RequireInternalSlot(M, [[MapData]]).
/// 3. If IsCallable(callbackfn) is false, throw a TypeError exception. 4. Set
///    key to CanonicalizeKeyedCollectionKey(key). 5. For each Record p of
///    M.[[MapData]], do a. If p.[[Key]] is not empty and SameValue(p.[[Key]],
///    key) is true, return p.[[Value]]. 6. Let value be ? Call(callbackfn,
///    undefined, « key »). 7. For each Record p of M.[[MapData]], do a. If
///    p.[[Key]] is not empty and SameValue(p.[[Key]], key) is true, then i. Set
///    p.[[Value]] to value. ii. Return value. 8. Set p to the Record { [[Key]]:
///    key, [[Value]]: value }. 9. Append p to M.[[MapData]]. 10. Return value.
fn map_get_or_insert_computed(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_MAP, "Map")?;
    let f = arg(args, 1);
    if !vm.heap().is_callable(f) {
        return Err(vm.type_error("Map.prototype.getOrInsertComputed: callback is not a function"));
    }
    let key = canonical(arg(args, 0));
    if let Some(v) = vm.table_get(this, key) {
        return Ok(v);
    }
    let value = vm.call(f, Value::UNDEFINED, &[key])?;
    vm.table_set(this, key, value);
    Ok(value)
}

/// `Map.prototype.has ( key )`, §24.1.3.7†: ... return true; 4. Return false.
fn map_has(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_MAP, "Map")?;
    Ok(Value::boolean(vm.table_has(this, arg(args, 0))))
}

/// `Map.prototype.set ( key, value )`, §24.1.3.9†: 3. For each Record p of
/// M.[[MapData]], do a. If p.[[Key]] is not empty and SameValueZero(p.[[Key]],
/// key) is true, then i. Set p.[[Value]] to value. ii. Return M. 4. If key is
/// -0𝔽, set key to +0𝔽. 5. Let p be the Record { [[Key]]: key, [[Value]]:
/// value }. 6. Append p to M.[[MapData]]. 7. Return M.
fn map_set(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_MAP, "Map")?;
    vm.table_set(this, arg(args, 0), arg(args, 1));
    Ok(this)
}

/// `get Map.prototype.size`, §24.1.3.10†: 3. Let count be 0. 4. For each
/// Record p of M.[[MapData]], do a. If p.[[Key]] is not empty, set count to
/// count + 1. 5. Return 𝔽(count).
fn map_size(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_MAP, "Map")?;
    Ok(count(vm.table_size(this).unwrap_or(0)))
}

// ---------------------------------------------------------------------
// Set
// ---------------------------------------------------------------------

fn install_set(vm: &mut Vm) -> Result<(), Abrupt> {
    let (ctor, proto) =
        make_constructor(vm, "Set", 0, set_constructor, Intrinsic::SetPrototype, true)?;
    let methods: [(&str, i32, NativeFn); 14] = [
        ("add", 1, set_add),
        ("clear", 0, set_clear),
        ("delete", 1, set_delete),
        ("difference", 1, set_difference),
        ("entries", 0, set_entries),
        ("forEach", 1, set_for_each),
        ("has", 1, set_has),
        ("intersection", 1, set_intersection),
        ("isDisjointFrom", 1, set_is_disjoint_from),
        ("isSubsetOf", 1, set_is_subset_of),
        ("isSupersetOf", 1, set_is_superset_of),
        ("symmetricDifference", 1, set_symmetric_difference),
        ("union", 1, set_union),
        ("values", 0, set_values),
    ];
    for (name, len, f) in methods {
        method(vm, proto, name, len, f)?;
    }
    // §24.2.4†: the initial value of `keys` is the same function object as
    // `values`.
    let kv = key(vm, "values")?;
    let values = vm.get_value(proto, kv)?;
    let kk = key(vm, "keys")?;
    vm.heap_mut().define(proto, kk, values, METHOD)?;
    let ks = key(vm, "size")?;
    accessor(vm, proto, ks, "size", Some(set_size), None)?;
    alias_iterator(vm, proto, "values")?;
    to_string_tag(vm, proto, "Set")?;
    make_iterator_prototype(
        vm,
        Intrinsic::SetIteratorPrototype,
        set_iterator_next,
        "Set Iterator",
    )?;
    crate::util::global(vm, "Set", ctor)
}

/// `Set ( [ iterable ] )`, §24.2.1.1†: as `Map`, with the adder "add" called
/// with each value (steps 5 to 8 of the standard: `Get(set, "add")`, the
/// callable check, GetIterator, then for each next `Call(adder, set, « next
/// »)` with IfAbruptCloseIterator).
fn set_constructor(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let set = allocate(vm, TAG_SET, Intrinsic::SetPrototype, "Set")?;
    fill(vm, set, arg(args, 0), "add", false)
}

/// `Set.prototype.add ( value )`, §24.2.4.1†: 3. For each element e of
/// S.[[SetData]], do a. If e is not empty and SameValueZero(e, value) is true,
/// return S. 4. If value is -0𝔽, set value to +0𝔽. 5. Append value to
/// S.[[SetData]]. 6. Return S.
fn set_add(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_SET, "Set")?;
    let v = arg(args, 0);
    if !vm.table_has(this, v) {
        vm.table_set(this, v, canonical(v));
    }
    Ok(this)
}

fn set_clear(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_SET, "Set")?;
    vm.table_clear(this);
    Ok(Value::UNDEFINED)
}

fn set_delete(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_SET, "Set")?;
    Ok(Value::boolean(vm.table_delete(this, arg(args, 0))))
}

fn set_has(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_SET, "Set")?;
    Ok(Value::boolean(vm.table_has(this, arg(args, 0))))
}

fn set_size(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_SET, "Set")?;
    Ok(count(vm.table_size(this).unwrap_or(0)))
}

/// `Set.prototype.entries ( )`, §24.2.4†: CreateSetIterator(S, key+value).
fn set_entries(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_SET, "Set")?;
    create_iterator(
        vm,
        this,
        2,
        TAG_SET_ITERATOR,
        Intrinsic::SetIteratorPrototype,
    )
}

/// `Set.prototype.values ( )`, §24.2.4†: CreateSetIterator(S, value)
/// (a Set iterator over `value` kind gives the keys of the table).
fn set_values(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_SET, "Set")?;
    create_iterator(
        vm,
        this,
        0,
        TAG_SET_ITERATOR,
        Intrinsic::SetIteratorPrototype,
    )
}

/// `Set.prototype.forEach ( callbackfn [ , thisArg ] )`, §24.2.4†: as
/// `Map.prototype.forEach`, calling with « e, e, S ».
fn set_for_each(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_SET, "Set")?;
    let f = arg(args, 0);
    if !vm.heap().is_callable(f) {
        return Err(vm.type_error("Set.prototype.forEach: callback is not a function"));
    }
    let mut pos = 0;
    while let Some((next, k, _)) = vm.table_next(this, pos) {
        vm.charge_step()?;
        pos = next;
        vm.call(f, arg(args, 1), &[k, k, this])?;
    }
    Ok(Value::UNDEFINED)
}

/// A Set Record (§24.2.1.2†): the `size` of the other set-like, its `has`
/// and its `keys`.
struct SetRecord {
    set: Value,
    size: f64,
    has: Value,
    keys: Value,
}

/// GetSetRecord ( obj ), §24.2.1.2†:
/// 1. If obj is not an Object, throw a TypeError exception.
/// 2. Let rawSize be ? Get(obj, "size").
/// 3. Let numSize be ? ToNumber(rawSize).
/// 4. NOTE: If rawSize is undefined, then numSize will be NaN.
/// 5. If numSize is NaN, throw a TypeError exception.
/// 6. Let intSize be ! ToIntegerOrInfinity(numSize).
/// 7. If intSize < 0, throw a RangeError exception.
/// 8. Let has be ? Get(obj, "has").
/// 9. If IsCallable(has) is false, throw a TypeError exception.
/// 10. Let keys be ? Get(obj, "keys").
/// 11. If IsCallable(keys) is false, throw a TypeError exception.
/// 12. Return a new Set Record { [[SetObject]]: obj, [[Size]]: intSize,
///     [[Has]]: has, [[Keys]]: keys }.
fn get_set_record(vm: &mut Vm, obj: Value) -> Result<SetRecord, Abrupt> {
    if !vm.heap().is_object(obj) {
        return Err(vm.type_error("The argument is not a set-like object"));
    }
    let raw = get(vm, obj, "size")?;
    let n = vm.to_number(raw)?;
    if n.is_nan() {
        return Err(vm.type_error("The 'size' of the set-like is not a number"));
    }
    let int = to_integer_or_infinity(vm, Value::double(n))?;
    if int < 0.0 {
        return Err(vm.range_error("The 'size' of the set-like is negative"));
    }
    let has = get(vm, obj, "has")?;
    if !vm.heap().is_callable(has) {
        return Err(vm.type_error("The 'has' of the set-like is not a function"));
    }
    let keys = get(vm, obj, "keys")?;
    if !vm.heap().is_callable(keys) {
        return Err(vm.type_error("The 'keys' of the set-like is not a function"));
    }
    Ok(SetRecord {
        set: obj,
        size: int,
        has,
        keys,
    })
}

/// GetIteratorFromMethod-like `GetKeysIterator ( setRec )`, §24.2.1.3†:
/// 1. Let keysIter be ? Call(setRec.[[Keys]], setRec.[[SetObject]]).
/// 2. If keysIter is not an Object, throw a TypeError exception.
/// 3. Let nextMethod be ? Get(keysIter, "next").
/// 4. Return a new Iterator Record { [[Iterator]]: keysIter, [[NextMethod]]:
///    nextMethod, [[Done]]: false }.
///
/// (The record is the VM's iterator record, so `IteratorStepValue` is
/// [`Vm::iterator_step_value`].) The `next` method need not be callable until
/// it is called.
fn get_keys_iterator(vm: &mut Vm, rec: &SetRecord) -> Result<Value, Abrupt> {
    let it = vm.call(rec.keys, rec.set, &[])?;
    if !vm.heap().is_object(it) {
        return Err(vm.type_error("The 'keys' of the set-like did not return an object"));
    }
    let next = get(vm, it, "next")?;
    vm.new_iterator_record(it, next)
}

/// A new Set holding `entries` in order (the result of the set methods):
/// OrdinaryObjectCreate(%Set.prototype%, « [[SetData]] ») with the data.
fn new_set_from(vm: &mut Vm, entries: &[Value]) -> Result<Value, Abrupt> {
    let proto = vm.intrinsic(Intrinsic::SetPrototype);
    let set = vm.new_host_object(proto, TAG_SET, Vec::new(), None)?;
    vm.attach_table(set);
    for e in entries {
        vm.table_set(set, *e, canonical(*e));
    }
    Ok(set)
}

/// The elements of the this Set, in order, for the result of a method that
/// starts from a copy of `O.[[SetData]]`.
fn elements(vm: &Vm, set: Value) -> Vec<Value> {
    let mut out = Vec::new();
    let mut pos = 0;
    while let Some((next, k, _)) = vm.table_next(set, pos) {
        out.push(k);
        pos = next;
    }
    out
}

/// The result of a `Call(setRec.[[Has]], setRec.[[SetObject]], « e »)`, as
/// ToBoolean.
fn other_has(vm: &mut Vm, rec: &SetRecord, e: Value) -> Result<bool, Abrupt> {
    let r = vm.call(rec.has, rec.set, &[e])?;
    Ok(vm.to_boolean(r))
}

/// `Set.prototype.union ( other )`, §24.2.4†:
/// 1. Let O be the this value. 2. Perform ? RequireInternalSlot(O, [[SetData]]).
/// 3. Let otherRec be ? GetSetRecord(other). 4. Let keysIter be ?
///    GetIteratorFromMethod(otherRec.[[SetObject]], otherRec.[[Keys]]) (as
///    GetKeysIterator). 5. Let resultSetData be a copy of O.[[SetData]]. 6. Let
///    next be not-started. 7. Repeat, while next is not done, a. Set next to ?
///    IteratorStepValue(keysIter). b. If next is not done, then i. Set next to
///    CanonicalizeKeyedCollectionKey(next). ii. Let valueIndex be
///    SetDataIndex(resultSetData, next). iii. If valueIndex is not-found,
///    append next to resultSetData. 8. Let result be OrdinaryObjectCreate(
///    %Set.prototype%, « [[SetData]] »). 9. Set result.[[SetData]] to
///    resultSetData. 10. Return result.
fn set_union(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_SET, "Set")?;
    let rec = get_set_record(vm, arg(args, 0))?;
    let iter = get_keys_iterator(vm, &rec)?;
    let start = elements(vm, this);
    let result = new_set_from(vm, &start)?;
    while let Some(next) = vm.iterator_step_value(iter)? {
        vm.charge_step()?;
        let next = canonical(next);
        if !vm.table_has(result, next) {
            vm.table_set(result, next, next);
        }
    }
    Ok(result)
}

/// `Set.prototype.intersection ( other )`, §24.2.4†:
/// 3. Let otherRec be ? GetSetRecord(other). 4. Let resultSetData be a new
///    empty List. 5. If SetDataSize(O.[[SetData]]) ≤ otherRec.[[Size]], then
///    a. Let thisSize be the number of elements in O.[[SetData]]. b. Let index
///    be 0. c. Repeat, while index < thisSize, i. Let e be O.[[SetData]][index].
///    ii. Set index to index + 1. iii. If e is not empty, then 1. Let inOther
///    be ToBoolean(? Call(otherRec.[[Has]], otherRec.[[SetObject]], « e »)).
///    2. If inOther is true, then a. NOTE: It is possible for earlier calls to
///    otherRec.[[Has]] to remove and re-add an element of O.[[SetData]], which
///    can cause the same element to be visited twice during this iteration. b.
///    If SetDataHas(resultSetData, e) is false, append e to resultSetData. 3.
///    NOTE: The number of elements in O.[[SetData]] may have increased during
///    execution of otherRec.[[Has]]. 4. Set thisSize to the number of elements
///    of O.[[SetData]]. 6. Else, a. Let keysIter be ? GetIteratorFromMethod(
///    otherRec.[[SetObject]], otherRec.[[Keys]]). b. Let next be not-started. c.
///    Repeat, while next is not done, i. Set next to ? IteratorStepValue(
///    keysIter). ii. If next is not done, then 1. Set next to
///    CanonicalizeKeyedCollectionKey(next). 2. Let inThis be SetDataHas(
///    O.[[SetData]], next). 3. If inThis is true, then a. NOTE: Because other
///    is an arbitrary object, it is possible for its "keys" iterator to
///    produce the same value more than once. b. If SetDataHas(resultSetData,
///    next) is false, append next to resultSetData. 7. Let result be
///    OrdinaryObjectCreate(%Set.prototype%, « [[SetData]] »). 8. Set
///    result.[[SetData]] to resultSetData. 9. Return result.
fn set_intersection(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_SET, "Set")?;
    let rec = get_set_record(vm, arg(args, 0))?;
    let result = new_set_from(vm, &[])?;
    let this_size = count_f64(vm.table_size(this).unwrap_or(0));
    if this_size <= rec.size {
        let mut index = 0;
        while index < vm.table_places(this).unwrap_or(0) {
            vm.charge_step()?;
            let e = vm.table_entry(this, index);
            index = index.saturating_add(1);
            if let Some((e, _)) = e
                && other_has(vm, &rec, e)?
                && !vm.table_has(result, e)
            {
                vm.table_set(result, e, e);
            }
        }
    } else {
        let iter = get_keys_iterator(vm, &rec)?;
        while let Some(next) = vm.iterator_step_value(iter)? {
            vm.charge_step()?;
            let next = canonical(next);
            if vm.table_has(this, next) && !vm.table_has(result, next) {
                vm.table_set(result, next, next);
            }
        }
    }
    Ok(result)
}

/// `Set.prototype.difference ( other )`, §24.2.4†: the result starts as a
/// copy of O.[[SetData]]; if SetDataSize(O) ≤ otherRec.[[Size]], each element
/// e of O (an index loop that reads the size again) with ToBoolean(Call(
/// otherRec.[[Has]], ..., « e »)) true is removed (made empty) from the copy;
/// else each canonicalized key `next` of the other's keys iterator is removed
/// from the copy.
fn set_difference(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_SET, "Set")?;
    let rec = get_set_record(vm, arg(args, 0))?;
    let start = elements(vm, this);
    let result = new_set_from(vm, &start)?;
    let this_size = count_f64(vm.table_size(this).unwrap_or(0));
    if this_size <= rec.size {
        let mut index = 0;
        while index < vm.table_places(this).unwrap_or(0) {
            vm.charge_step()?;
            let e = vm.table_entry(this, index);
            index = index.saturating_add(1);
            if let Some((e, _)) = e
                && other_has(vm, &rec, e)?
            {
                vm.table_delete(result, e);
            }
        }
    } else {
        let iter = get_keys_iterator(vm, &rec)?;
        while let Some(next) = vm.iterator_step_value(iter)? {
            vm.charge_step()?;
            vm.table_delete(result, canonical(next));
        }
    }
    Ok(result)
}

/// `Set.prototype.symmetricDifference ( other )`, §24.2.4†:
/// 3. Let otherRec be ? GetSetRecord(other). 4. Let keysIter be ?
///    GetIteratorFromMethod(...). 5. Let resultSetData be a copy of
///    O.[[SetData]]. 6. Let next be not-started. 7. Repeat, while next is not
///    done, a. Set next to ? IteratorStepValue(keysIter). b. If next is not
///    done, then i. Set next to CanonicalizeKeyedCollectionKey(next). ii. Let
///    resultIndex be SetDataIndex(resultSetData, next). iii. If resultIndex is
///    not-found, let alreadyInResult be false. Otherwise let alreadyInResult be
///    true. iv. If SetDataHas(O.[[SetData]], next) is true, then 1. If
///    alreadyInResult is true, set resultSetData[resultIndex] to empty. v.
///    Else, 1. If alreadyInResult is false, append next to resultSetData.
fn set_symmetric_difference(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_SET, "Set")?;
    let rec = get_set_record(vm, arg(args, 0))?;
    let iter = get_keys_iterator(vm, &rec)?;
    let start = elements(vm, this);
    let result = new_set_from(vm, &start)?;
    while let Some(next) = vm.iterator_step_value(iter)? {
        vm.charge_step()?;
        let next = canonical(next);
        let already = vm.table_has(result, next);
        if vm.table_has(this, next) {
            if already {
                vm.table_delete(result, next);
            }
        } else if !already {
            vm.table_set(result, next, next);
        }
    }
    Ok(result)
}

/// `Set.prototype.isSubsetOf ( other )`, §24.2.4†:
/// 3. Let otherRec be ? GetSetRecord(other). 4. If SetDataSize(O.[[SetData]])
///    is greater than otherRec.[[Size]], return false. 5. Let thisSize be the number of
///    elements in O.[[SetData]]. 6. Let index be 0. 7. Repeat, while index <
///    thisSize, a. Let e be O.[[SetData]][index]. b. Set index to index + 1.
///    c. If e is not empty, then i. Let inOther be ToBoolean(? Call(
///    otherRec.[[Has]], otherRec.[[SetObject]], « e »)). ii. If inOther is
///    false, return false. iii. NOTE: ... iv. Set thisSize to the number of
///    elements of O.[[SetData]]. 8. Return true.
fn set_is_subset_of(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_SET, "Set")?;
    let rec = get_set_record(vm, arg(args, 0))?;
    if count_f64(vm.table_size(this).unwrap_or(0)) > rec.size {
        return Ok(Value::FALSE);
    }
    let mut index = 0;
    while index < vm.table_places(this).unwrap_or(0) {
        vm.charge_step()?;
        let e = vm.table_entry(this, index);
        index = index.saturating_add(1);
        if let Some((e, _)) = e
            && !other_has(vm, &rec, e)?
        {
            return Ok(Value::FALSE);
        }
    }
    Ok(Value::TRUE)
}

/// `Set.prototype.isSupersetOf ( other )`, §24.2.4†:
/// 3. Let otherRec be ? GetSetRecord(other). 4. If SetDataSize(O.[[SetData]])
///    is less than otherRec.[[Size]], return false. 5. Let keysIter be ?
///    GetIteratorFromMethod(...). 6. Let next be not-started. 7. Repeat, while
///    next is not done, a. Set next to ? IteratorStepValue(keysIter). b. If
///    next is not done, then i. If SetDataHas(O.[[SetData]], next) is false,
///    then 1. Perform ? IteratorClose(keysIter, NormalCompletion(unused)). 2.
///    Return false. 8. Return true.
fn set_is_superset_of(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_SET, "Set")?;
    let rec = get_set_record(vm, arg(args, 0))?;
    if (count_f64(vm.table_size(this).unwrap_or(0))) < rec.size {
        return Ok(Value::FALSE);
    }
    let iter = get_keys_iterator(vm, &rec)?;
    while let Some(next) = vm.iterator_step_value(iter)? {
        vm.charge_step()?;
        if !vm.table_has(this, canonical(next)) {
            vm.iterator_close(iter)?;
            return Ok(Value::FALSE);
        }
    }
    Ok(Value::TRUE)
}

/// `Set.prototype.isDisjointFrom ( other )`, §24.2.4†:
/// 3. Let otherRec be ? GetSetRecord(other). 4. If SetDataSize(O.[[SetData]])
///    ≤ otherRec.[[Size]], then a. Let thisSize be the number of elements in
///    O.[[SetData]]. b. Let index be 0. c. Repeat, while index < thisSize, i.
///    Let e be O.[[SetData]][index]. ii. Set index to index + 1. iii. If e is
///    not empty, then 1. Let inOther be ToBoolean(? Call(otherRec.[[Has]],
///    otherRec.[[SetObject]], « e »)). 2. If inOther is true, return false. 3.
///    NOTE: ... 4. Set thisSize to the number of elements of O.[[SetData]]. 5.
///    Else, a. Let keysIter be ? GetIteratorFromMethod(...). b. Let next be
///    not-started. c. Repeat, while next is not done, i. Set next to ?
///    IteratorStepValue(keysIter). ii. If next is not done, then 1. If
///    SetDataHas(O.[[SetData]], next) is true, then a. Perform ?
///    IteratorClose(keysIter, NormalCompletion(unused)). b. Return false. 6.
///    Return true.
fn set_is_disjoint_from(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_SET, "Set")?;
    let rec = get_set_record(vm, arg(args, 0))?;
    if count_f64(vm.table_size(this).unwrap_or(0)) <= rec.size {
        let mut index = 0;
        while index < vm.table_places(this).unwrap_or(0) {
            vm.charge_step()?;
            let e = vm.table_entry(this, index);
            index = index.saturating_add(1);
            if let Some((e, _)) = e
                && other_has(vm, &rec, e)?
            {
                return Ok(Value::FALSE);
            }
        }
    } else {
        let iter = get_keys_iterator(vm, &rec)?;
        while let Some(next) = vm.iterator_step_value(iter)? {
            vm.charge_step()?;
            if vm.table_has(this, canonical(next)) {
                vm.iterator_close(iter)?;
                return Ok(Value::FALSE);
            }
        }
    }
    Ok(Value::TRUE)
}

// ---------------------------------------------------------------------
// WeakMap and WeakSet
// ---------------------------------------------------------------------

/// CanBeHeldWeakly ( v ), §9.13†:
/// 1. If v is an Object, return true.
/// 2. If v is a Symbol and KeyForSymbol(v) is undefined, return true.
/// 3. Return false.
fn can_be_held_weakly(vm: &mut Vm, v: Value) -> Result<bool, Abrupt> {
    if vm.heap().is_object(v) {
        return Ok(true);
    }
    if !vm.heap().is_symbol(v) {
        return Ok(false);
    }
    let registry = vm.intrinsic(Intrinsic::SymbolRegistry);
    let registered = vm
        .heap()
        .own_properties(registry)
        .into_iter()
        .any(|(_, _, s)| s == v);
    Ok(!registered)
}

fn install_weak(vm: &mut Vm) -> Result<(), Abrupt> {
    let (ctor, proto) = make_constructor(
        vm,
        "WeakMap",
        0,
        weak_map_constructor,
        Intrinsic::WeakMapPrototype,
        false,
    )?;
    method(vm, proto, "delete", 1, weak_map_delete)?;
    method(vm, proto, "get", 1, weak_map_get)?;
    method(vm, proto, "getOrInsert", 2, weak_map_get_or_insert)?;
    method(
        vm,
        proto,
        "getOrInsertComputed",
        2,
        weak_map_get_or_insert_computed,
    )?;
    method(vm, proto, "has", 1, weak_map_has)?;
    method(vm, proto, "set", 2, weak_map_set)?;
    to_string_tag(vm, proto, "WeakMap")?;
    crate::util::global(vm, "WeakMap", ctor)?;
    let (ctor, proto) = make_constructor(
        vm,
        "WeakSet",
        0,
        weak_set_constructor,
        Intrinsic::WeakSetPrototype,
        false,
    )?;
    method(vm, proto, "add", 1, weak_set_add)?;
    method(vm, proto, "delete", 1, weak_set_delete)?;
    method(vm, proto, "has", 1, weak_set_has)?;
    to_string_tag(vm, proto, "WeakSet")?;
    crate::util::global(vm, "WeakSet", ctor)
}

/// `WeakMap ( [ iterable ] )`, §24.3.1.1†: as `Map`, with `[[WeakMapData]]`.
fn weak_map_constructor(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let map = allocate(vm, TAG_WEAK_MAP, Intrinsic::WeakMapPrototype, "WeakMap")?;
    fill(vm, map, arg(args, 0), "set", true)
}

/// `WeakMap.prototype.delete ( key )`, §24.3.3.2†: 3. If CanBeHeldWeakly(key)
/// is false, return false. 4. For each Record { [[Key]], [[Value]] } p of
/// M.[[WeakMapData]], do a. If p.[[Key]] is not empty and SameValue(p.[[Key]],
/// key) is true, then ... return true. 5. Return false.
fn weak_map_delete(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_WEAK_MAP, "WeakMap")?;
    if !can_be_held_weakly(vm, arg(args, 0))? {
        return Ok(Value::FALSE);
    }
    Ok(Value::boolean(vm.table_delete(this, arg(args, 0))))
}

/// `WeakMap.prototype.get ( key )`, §24.3.3.3†: 3. If CanBeHeldWeakly(key) is
/// false, return undefined. 4. ... return p.[[Value]]. 5. Return undefined.
fn weak_map_get(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_WEAK_MAP, "WeakMap")?;
    if !can_be_held_weakly(vm, arg(args, 0))? {
        return Ok(Value::UNDEFINED);
    }
    Ok(vm.table_get(this, arg(args, 0)).unwrap_or(Value::UNDEFINED))
}

/// `WeakMap.prototype.getOrInsert ( key, value )` (upsert proposal): as
/// `Map.prototype.getOrInsert`, after "3. If CanBeHeldWeakly(key) is false,
/// throw a TypeError exception." and without the canonicalization.
fn weak_map_get_or_insert(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_WEAK_MAP, "WeakMap")?;
    if !can_be_held_weakly(vm, arg(args, 0))? {
        return Err(vm.type_error("Invalid value used as weak map key"));
    }
    if let Some(v) = vm.table_get(this, arg(args, 0)) {
        return Ok(v);
    }
    vm.table_set(this, arg(args, 0), arg(args, 1));
    Ok(arg(args, 1))
}

/// `WeakMap.prototype.getOrInsertComputed ( key, callbackfn )` (upsert
/// proposal): as `Map.prototype.getOrInsertComputed`, after "3. If
/// CanBeHeldWeakly(key) is false, throw a TypeError exception." and "4. If
/// IsCallable(callbackfn) is false, throw a TypeError exception."
fn weak_map_get_or_insert_computed(
    vm: &mut Vm,
    this: Value,
    args: &[Value],
) -> Result<Value, Abrupt> {
    require(vm, this, TAG_WEAK_MAP, "WeakMap")?;
    if !can_be_held_weakly(vm, arg(args, 0))? {
        return Err(vm.type_error("Invalid value used as weak map key"));
    }
    let f = arg(args, 1);
    if !vm.heap().is_callable(f) {
        return Err(
            vm.type_error("WeakMap.prototype.getOrInsertComputed: callback is not a function")
        );
    }
    if let Some(v) = vm.table_get(this, arg(args, 0)) {
        return Ok(v);
    }
    let value = vm.call(f, Value::UNDEFINED, &[arg(args, 0)])?;
    vm.table_set(this, arg(args, 0), value);
    Ok(value)
}

/// `WeakMap.prototype.has ( key )`, §24.3.3.4†: as `get`, with true and false.
fn weak_map_has(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_WEAK_MAP, "WeakMap")?;
    if !can_be_held_weakly(vm, arg(args, 0))? {
        return Ok(Value::FALSE);
    }
    Ok(Value::boolean(vm.table_has(this, arg(args, 0))))
}

/// `WeakMap.prototype.set ( key, value )`, §24.3.3.5†: 3. If CanBeHeldWeakly(
/// key) is false, throw a TypeError exception. 4. For each Record p of
/// M.[[WeakMapData]], do a. If p.[[Key]] is not empty and SameValue(p.[[Key]],
/// key) is true, then i. Set p.[[Value]] to value. ii. Return M. 5. Let p be
/// the Record { [[Key]]: key, [[Value]]: value }. 6. Append p to
/// M.[[WeakMapData]]. 7. Return M.
fn weak_map_set(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_WEAK_MAP, "WeakMap")?;
    if !can_be_held_weakly(vm, arg(args, 0))? {
        return Err(vm.type_error("Invalid value used as weak map key"));
    }
    vm.table_set(this, arg(args, 0), arg(args, 1));
    Ok(this)
}

/// `WeakSet ( [ iterable ] )`, §24.4.1.1†: as `Set`, with `[[WeakSetData]]`.
fn weak_set_constructor(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let set = allocate(vm, TAG_WEAK_SET, Intrinsic::WeakSetPrototype, "WeakSet")?;
    fill(vm, set, arg(args, 0), "add", false)
}

/// `WeakSet.prototype.add ( value )`, §24.4.3.1†: 3. If CanBeHeldWeakly(value)
/// is false, throw a TypeError exception. 4. For each element e of
/// S.[[WeakSetData]], do a. If e is not empty and SameValue(e, value) is true,
/// return S. 5. Append value to S.[[WeakSetData]]. 6. Return S.
fn weak_set_add(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_WEAK_SET, "WeakSet")?;
    if !can_be_held_weakly(vm, arg(args, 0))? {
        return Err(vm.type_error("Invalid value used in weak set"));
    }
    vm.table_set(this, arg(args, 0), Value::UNDEFINED);
    Ok(this)
}

/// `WeakSet.prototype.delete ( value )`, §24.4.3.3†.
fn weak_set_delete(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_WEAK_SET, "WeakSet")?;
    if !can_be_held_weakly(vm, arg(args, 0))? {
        return Ok(Value::FALSE);
    }
    Ok(Value::boolean(vm.table_delete(this, arg(args, 0))))
}

/// `WeakSet.prototype.has ( value )`, §24.4.3.4†.
fn weak_set_has(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require(vm, this, TAG_WEAK_SET, "WeakSet")?;
    if !can_be_held_weakly(vm, arg(args, 0))? {
        return Ok(Value::FALSE);
    }
    Ok(Value::boolean(vm.table_has(this, arg(args, 0))))
}
