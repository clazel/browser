//! `Array` (§23.1†): the constructor, `Array.isArray`, `Array.of`, and the
//! core of `Array.prototype`: `push`, `pop`, `shift`, `unshift`, `slice`,
//! `splice`, `concat`, `join`, `toString`, `indexOf`, `lastIndexOf`,
//! `includes`, `reverse`, `fill`, `forEach`, `map`, `filter`, `some`, `every`,
//! `reduce`, `reduceRight`, `find`, `findIndex` and `sort`.
//!
//! The methods are generic, as the standard writes them: each reads and
//! writes through `Get`, `Set`, `HasProperty` and `DeletePropertyOrThrow` on
//! `ToObject(this value)`, and does not assume an Array exotic object. The
//! "mathematical values" of the algorithms (indices up to 2^53 - 1) are `f64`,
//! which holds them exactly.
//!
//! Left for when Symbols and iterators exist: `Array.from`, `entries`,
//! `keys`, `values` and `@@iterator`, `@@species`, `@@isConcatSpreadable`,
//! `@@unscopables`. `ArraySpeciesCreate` therefore uses the receiver's
//! `constructor` itself where the standard reads its `@@species`.

use crate::util::{arg, constructor, js_string, method, number, to_integer_or_infinity};
use clazel_js_heap::string::{JsString, Key};
use clazel_js_heap::value::Value;
use clazel_js_vm::interp::{Abrupt, Intrinsic, Vm};

/// 2^53 - 1: the largest integer index and length (§6.1.6.1†, §7.1.20†).
const MAX_SAFE: f64 = 9_007_199_254_740_991.0;

/// Installs `Array`, `Array.prototype` and their methods.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    // §23.1.3†: "The Array prototype object is an Array exotic object ... with
    // a [[Prototype]] of %Object.prototype% and a length of 0".
    let object_proto = vm.intrinsic(Intrinsic::ObjectPrototype);
    let proto = vm.heap_mut().new_array(object_proto, 0)?;
    vm.set_intrinsic(Intrinsic::ArrayPrototype, proto);
    let ctor = constructor(vm, "Array", 1, array_constructor, proto)?;
    vm.set_intrinsic(Intrinsic::ArrayConstructor, ctor);
    method(vm, ctor, "isArray", 1, is_array)?;
    method(vm, ctor, "of", 0, array_of)?;
    let methods: [(&str, i32, clazel_js_vm::interp::NativeFn); 24] = [
        ("concat", 1, concat),
        ("every", 1, every),
        ("fill", 1, fill),
        ("filter", 1, filter),
        ("find", 1, find),
        ("findIndex", 1, find_index),
        ("forEach", 1, for_each),
        ("includes", 1, includes),
        ("indexOf", 1, index_of),
        ("join", 1, join),
        ("lastIndexOf", 1, last_index_of),
        ("map", 1, map),
        ("pop", 0, pop),
        ("push", 1, push),
        ("reduce", 1, reduce),
        ("reduceRight", 1, reduce_right),
        ("reverse", 0, reverse),
        ("shift", 0, shift),
        ("slice", 2, slice),
        ("some", 1, some),
        ("sort", 1, sort),
        ("splice", 2, splice),
        ("toString", 0, to_string),
        ("unshift", 1, unshift),
    ];
    for (name, len, f) in methods {
        method(vm, proto, name, len, f)?;
    }
    crate::util::global(vm, "Array", ctor)
}

// ---------------------------------------------------------------------
// Abstract operations
// ---------------------------------------------------------------------

/// The key `ToString(𝔽(k))` of an integer `k`.
fn pk(vm: &mut Vm, k: f64) -> Result<Key, Abrupt> {
    vm.index_key(k as u64)
}

/// `Get(O, ToString(k))`, §7.3.2†.
fn get_at(vm: &mut Vm, o: Value, k: f64) -> Result<Value, Abrupt> {
    let key = pk(vm, k)?;
    vm.get_value(o, key)
}

/// `HasProperty(O, ToString(k))`, §7.3.12†.
fn has_at(vm: &mut Vm, o: Value, k: f64) -> Result<bool, Abrupt> {
    let key = pk(vm, k)?;
    Ok(vm.heap().find(o, key)?.is_some())
}

/// `Set(O, ToString(k), v, true)`, §7.3.4†.
fn set_at(vm: &mut Vm, o: Value, k: f64, v: Value) -> Result<(), Abrupt> {
    let key = pk(vm, k)?;
    vm.put_value(o, key, v, true)
}

/// `DeletePropertyOrThrow(O, ToString(k))`, §7.3.10†.
fn delete_at(vm: &mut Vm, o: Value, k: f64) -> Result<(), Abrupt> {
    let key = pk(vm, k)?;
    vm.delete_property_or_throw(o, key)
}

/// `CreateDataPropertyOrThrow(O, ToString(k), v)`, §7.3.7†.
fn create_at(vm: &mut Vm, o: Value, k: f64, v: Value) -> Result<(), Abrupt> {
    let key = pk(vm, k)?;
    vm.create_data_property_or_throw(o, key, v)
}

/// `Set(O, "length", n, true)`.
fn set_length(vm: &mut Vm, o: Value, n: f64) -> Result<(), Abrupt> {
    let key = crate::util::key(vm, "length")?;
    vm.put_value(o, key, number(n), true)
}

/// LengthOfArrayLike ( obj ), §7.3.19†: `ToLength(? Get(obj, "length"))`, and
/// ToLength (§7.1.20†): ToIntegerOrInfinity, then clamp to `[0, 2^53 - 1]`.
fn length_of(vm: &mut Vm, o: Value) -> Result<f64, Abrupt> {
    let key = crate::util::key(vm, "length")?;
    let v = vm.get_value(o, key)?;
    let n = to_integer_or_infinity(vm, v)?;
    Ok(n.clamp(0.0, MAX_SAFE))
}

/// The relative index of `start`, `end` and `fromIndex` arguments: ToIntegerOrInfinity,
/// then "if relative is -infinity, let k be 0; else if relative < 0, let k be
/// max(len + relative, 0); else let k be min(relative, len)".
fn relative(vm: &mut Vm, v: Value, len: f64) -> Result<f64, Abrupt> {
    let rel = to_integer_or_infinity(vm, v)?;
    Ok(if rel == f64::NEG_INFINITY {
        0.0
    } else if rel < 0.0 {
        (len + rel).max(0.0)
    } else {
        rel.min(len)
    })
}

/// The `end` argument: `len` when `undefined`, else as [`relative`].
fn relative_end(vm: &mut Vm, v: Value, len: f64) -> Result<f64, Abrupt> {
    if v == Value::UNDEFINED {
        Ok(len)
    } else {
        relative(vm, v, len)
    }
}

/// A callable argument, else a TypeError (the first steps of `forEach`, `map`
/// and the others: "If IsCallable(callbackfn) is false, throw a TypeError").
fn callable(vm: &mut Vm, f: Value) -> Result<Value, Abrupt> {
    if vm.heap().is_callable(f) {
        Ok(f)
    } else {
        let d = vm.describe(f);
        Err(vm.type_error(&format!("{d} is not a function")))
    }
}

/// SameValueZero, §7.2.11†: as SameValue except that `+0` equals `-0`.
fn same_value_zero(vm: &Vm, a: Value, b: Value) -> bool {
    if let (Some(x), Some(y)) = (crate::util::as_number(a), crate::util::as_number(b)) {
        return x == y || (x.is_nan() && y.is_nan());
    }
    vm.same_value(a, b)
}

/// ArraySpeciesCreate ( originalArray, length ), §10.4.2.3†:
/// 1. If IsArray(originalArray) is false, return ? ArrayCreate(length).
/// 2. Let C be ? Get(originalArray, "constructor").
/// 3. If IsConstructor(C) is true, then (the cross-realm check: one realm).
/// 4. If C is an Object, then a. Set C to ? Get(C, @@species). (Not
///    consulted: no Symbols; C stays the constructor.)
/// 5. If C is undefined, return ? ArrayCreate(length).
/// 6. If IsConstructor(C) is false, throw a TypeError exception.
/// 7. Return ? Construct(C, « 𝔽(length) »).
fn species_create(vm: &mut Vm, original: Value, length: f64) -> Result<Value, Abrupt> {
    if !vm.is_array(original) {
        return vm.array_create(length, None);
    }
    let c = vm.get_named(original, "constructor")?;
    if c == Value::UNDEFINED || c == vm.intrinsic(Intrinsic::ArrayConstructor) {
        return vm.array_create(length, None);
    }
    if !vm.is_constructor(c) {
        return Err(vm.type_error("object.constructor is not a constructor"));
    }
    vm.construct_value(c, &[number(length)])
}

// ---------------------------------------------------------------------
// The constructor and the static functions
// ---------------------------------------------------------------------

/// `Array ( ...values )`, §23.1.1.1†:
/// 1. If NewTarget is undefined, let newTarget be the active function object;
///    else let newTarget be NewTarget.
/// 2. Let proto be ? GetPrototypeFromConstructor(newTarget,
///    "%Array.prototype%").
/// 3. Let numberOfArgs be the number of elements in values.
/// 4. If numberOfArgs = 0, then a. Return ! ArrayCreate(0, proto).
/// 5. Else if numberOfArgs = 1, then
///    a. Let len be values[0]. b. Let array be ! ArrayCreate(0, proto).
///    c. If len is not a Number, then i. Perform !
///    CreateDataPropertyOrThrow(array, "0", len). ii. Let intLen be 1𝔽.
///    d. Else, i. Let intLen be ! ToUint32(len). ii. If SameValueZero(intLen,
///    len) is false, throw a RangeError exception.
///    e. Perform ! Set(array, "length", intLen, true). f. Return array.
/// 6. Else, a. (Assert: numberOfArgs >= 2.) b. Let array be ?
///    ArrayCreate(numberOfArgs, proto). c. Let k be 0. d. Repeat, while k <
///    numberOfArgs, i. Let Pk be ! ToString(𝔽(k)). ii. Let itemK be
///    values[k]. iii. Perform ! CreateDataPropertyOrThrow(array, Pk, itemK).
///    iv. Set k to k + 1. e. (Assert: The mathematical value of array's
///    "length" property is numberOfArgs.) f. Return array.
fn array_constructor(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let nt = vm.new_target();
    let new_target = if nt == Value::UNDEFINED {
        vm.active_function()
    } else {
        nt
    };
    // GetPrototypeFromConstructor, §10.1.14†.
    let proto = vm.get_named(new_target, "prototype")?;
    let proto = if vm.heap().is_object(proto) {
        proto
    } else {
        vm.array_prototype()
    };
    match args {
        [] => vm.array_create(0.0, Some(proto)),
        [len] => {
            let array = vm.array_create(0.0, Some(proto))?;
            let int_len = if let Some(n) = crate::util::as_number(*len) {
                let u = clazel_js_vm::numeric::to_uint32(clazel_js_vm::numeric::narrow(n));
                if f64::from(u) != n {
                    return Err(vm.range_error("Invalid array length"));
                }
                f64::from(u)
            } else {
                create_at(vm, array, 0.0, *len)?;
                1.0
            };
            set_length(vm, array, int_len)?;
            Ok(array)
        }
        _ => {
            let array = vm.array_create(args.len() as f64, Some(proto))?;
            for (k, item) in args.iter().enumerate() {
                create_at(vm, array, k as f64, *item)?;
            }
            Ok(array)
        }
    }
}

/// `Array.isArray ( arg )`, §23.1.2.2†: Return ? IsArray(arg) (§7.2.2†).
fn is_array(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    Ok(Value::boolean(vm.is_array(arg(args, 0))))
}

/// `Array.of ( ...items )`, §23.1.2.3†:
/// 1. Let len be the number of elements in items.
/// 2. Let lenNumber be 𝔽(len).
/// 3. Let C be the this value.
/// 4. If IsConstructor(C) is true, then a. Let A be ? Construct(C, «
///    lenNumber »).
/// 5. Else, a. Let A be ? ArrayCreate(len).
/// 6. Let k be 0.
/// 7. Repeat, while k < len, a. Let kValue be items[k]. b. Let Pk be !
///    ToString(𝔽(k)). c. Perform ? CreateDataPropertyOrThrow(A, Pk, kValue).
///    d. Set k to k + 1.
/// 8. Perform ? Set(A, "length", lenNumber, true).
/// 9. Return A.
fn array_of(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let len = args.len() as f64;
    let a = if vm.is_constructor(this) {
        vm.construct_value(this, &[number(len)])?
    } else {
        vm.array_create(len, None)?
    };
    for (k, v) in args.iter().enumerate() {
        create_at(vm, a, k as f64, *v)?;
    }
    set_length(vm, a, len)?;
    Ok(a)
}

// ---------------------------------------------------------------------
// Mutators
// ---------------------------------------------------------------------

/// `Array.prototype.push ( ...items )`, §23.1.3.23†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. Let argCount be the number of elements in items.
/// 4. If len + argCount > 2^53 - 1, throw a TypeError exception.
/// 5. For each element E of items, do a. Perform ? Set(O, ! ToString(𝔽(len)),
///    E, true). b. Set len to len + 1.
/// 6. Perform ? Set(O, "length", 𝔽(len), true).
/// 7. Return 𝔽(len).
fn push(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let mut len = length_of(vm, o)?;
    if len + args.len() as f64 > MAX_SAFE {
        return Err(vm.type_error("Pushing elements past 2^53-1 length"));
    }
    for e in args {
        set_at(vm, o, len, *e)?;
        len += 1.0;
    }
    set_length(vm, o, len)?;
    Ok(number(len))
}

/// `Array.prototype.pop ( )`, §23.1.3.22†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. If len = 0, then a. Perform ? Set(O, "length", +0𝔽, true). b. Return
///    undefined.
/// 4. Else, a. (Assert: len > 0.) b. Let newLen be 𝔽(len - 1). c. Let index
///    be ! ToString(newLen). d. Let element be ? Get(O, index). e. Perform ?
///    DeletePropertyOrThrow(O, index). f. Perform ? Set(O, "length", newLen,
///    true). g. Return element.
fn pop(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let len = length_of(vm, o)?;
    if len == 0.0 {
        set_length(vm, o, 0.0)?;
        return Ok(Value::UNDEFINED);
    }
    let new_len = len - 1.0;
    let element = get_at(vm, o, new_len)?;
    delete_at(vm, o, new_len)?;
    set_length(vm, o, new_len)?;
    Ok(element)
}

/// `Array.prototype.shift ( )`, §23.1.3.27†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. If len = 0, then a. Perform ? Set(O, "length", +0𝔽, true). b. Return
///    undefined.
/// 4. Let first be ? Get(O, "0").
/// 5. Let k be 1.
/// 6. Repeat, while k < len, a. Let from be ! ToString(𝔽(k)). b. Let to be !
///    ToString(𝔽(k - 1)). c. Let fromPresent be ? HasProperty(O, from). d. If
///    fromPresent is true, then i. Let fromVal be ? Get(O, from). ii. Perform
///    ? Set(O, to, fromVal, true). e. Else, i. (Assert: fromPresent is false.)
///    ii. Perform ? DeletePropertyOrThrow(O, to). f. Set k to k + 1.
/// 7. Perform ? DeletePropertyOrThrow(O, ! ToString(𝔽(len - 1))).
/// 8. Perform ? Set(O, "length", 𝔽(len - 1), true).
/// 9. Return first.
fn shift(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let len = length_of(vm, o)?;
    if len == 0.0 {
        set_length(vm, o, 0.0)?;
        return Ok(Value::UNDEFINED);
    }
    let first = get_at(vm, o, 0.0)?;
    let mut k = 1.0;
    while k < len {
        vm.charge_step()?;
        if has_at(vm, o, k)? {
            let v = get_at(vm, o, k)?;
            set_at(vm, o, k - 1.0, v)?;
        } else {
            delete_at(vm, o, k - 1.0)?;
        }
        k += 1.0;
    }
    delete_at(vm, o, len - 1.0)?;
    set_length(vm, o, len - 1.0)?;
    Ok(first)
}

/// `Array.prototype.unshift ( ...items )`, §23.1.3.34†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. Let argCount be the number of elements in items.
/// 4. If argCount > 0, then a. If len + argCount > 2^53 - 1, throw a
///    TypeError exception. b. Let k be len. c. Repeat, while k > 0, i. Let
///    from be ! ToString(𝔽(k - 1)). ii. Let to be ! ToString(𝔽(k + argCount -
///    1)). iii. Let fromPresent be ? HasProperty(O, from). iv. If fromPresent
///    is true, then 1. Let fromValue be ? Get(O, from). 2. Perform ? Set(O,
///    to, fromValue, true). v. Else, 1. Perform ? DeletePropertyOrThrow(O,
///    to). vi. Set k to k - 1. d. Let j be +0𝔽. e. For each element E of
///    items, do i. Perform ? Set(O, ! ToString(j), E, true). ii. Set j to j +
///    1𝔽.
/// 5. Perform ? Set(O, "length", 𝔽(len + argCount), true).
/// 6. Return 𝔽(len + argCount).
fn unshift(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let len = length_of(vm, o)?;
    let argc = args.len() as f64;
    if argc > 0.0 {
        if len + argc > MAX_SAFE {
            return Err(vm.type_error("Invalid array length"));
        }
        let mut k = len;
        while k > 0.0 {
            vm.charge_step()?;
            if has_at(vm, o, k - 1.0)? {
                let v = get_at(vm, o, k - 1.0)?;
                set_at(vm, o, k + argc - 1.0, v)?;
            } else {
                delete_at(vm, o, k + argc - 1.0)?;
            }
            k -= 1.0;
        }
        for (j, e) in args.iter().enumerate() {
            set_at(vm, o, j as f64, *e)?;
        }
    }
    set_length(vm, o, len + argc)?;
    Ok(number(len + argc))
}

/// `Array.prototype.splice ( start, deleteCount, ...items )`, §23.1.3.31†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. Let relativeStart be ? ToIntegerOrInfinity(start).
/// 4. to 6. Let actualStart be len clamped as `relative`.
/// 7. Let itemCount be the number of elements in items.
/// 8. If start is not present, then a. Let actualDeleteCount be 0.
/// 9. Else if deleteCount is not present, then a. Let actualDeleteCount be
///    len - actualStart.
/// 10. Else, a. Let dc be ? ToIntegerOrInfinity(deleteCount). b. Let
///     actualDeleteCount be the result of clamping dc between 0 and len -
///     actualStart.
/// 11. If len + itemCount - actualDeleteCount > 2^53 - 1, throw a TypeError
///     exception.
/// 12. Let A be ? ArraySpeciesCreate(O, actualDeleteCount).
/// 13. Let k be 0.
/// 14. Repeat, while k < actualDeleteCount, a. Let from be ! ToString(𝔽(actualStart
///     + k)). b. If ? HasProperty(O, from) is true, then i. Let fromValue be ?
///     Get(O, from). ii. Perform ? CreateDataPropertyOrThrow(A, ! ToString(𝔽(k)),
///     fromValue). c. Set k to k + 1.
/// 15. Perform ? Set(A, "length", 𝔽(actualDeleteCount), true).
/// 16. If itemCount < actualDeleteCount, then a. Set k to actualStart. b.
///     Repeat, while k < (len - actualDeleteCount), i. from is k +
///     actualDeleteCount, ii. to is k + itemCount, iii. if HasProperty(from)
///     Set(to, Get(from)), else DeletePropertyOrThrow(to), v. Set k to k + 1.
///     c. Set k to len. d. Repeat, while k > (len - actualDeleteCount +
///     itemCount), i. Perform ? DeletePropertyOrThrow(O, ! ToString(𝔽(k -
///     1))). ii. Set k to k - 1.
/// 17. Else if itemCount > actualDeleteCount, then a. Set k to (len -
///     actualDeleteCount). b. Repeat, while k > actualStart, i. from is k +
///     actualDeleteCount - 1, ii. to is k + itemCount - 1, iii. as in step
///     16.b.iii, v. Set k to k - 1.
/// 18. Set k to actualStart.
/// 19. For each element E of items, do a. Perform ? Set(O, ! ToString(𝔽(k)), E,
///     true). b. Set k to k + 1.
/// 20. Perform ? Set(O, "length", 𝔽(len - actualDeleteCount + itemCount),
///     true).
/// 21. Return A.
fn splice(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let len = length_of(vm, o)?;
    let actual_start = relative(vm, arg(args, 0), len)?;
    let items: &[Value] = args.get(2..).unwrap_or(&[]);
    let item_count = items.len() as f64;
    let actual_delete_count = match args.len() {
        0 => 0.0,
        1 => len - actual_start,
        _ => {
            let dc = to_integer_or_infinity(vm, arg(args, 1))?;
            dc.clamp(0.0, len - actual_start)
        }
    };
    if len + item_count - actual_delete_count > MAX_SAFE {
        return Err(vm.type_error("Invalid array length"));
    }
    let a = species_create(vm, o, actual_delete_count)?;
    let mut k = 0.0;
    while k < actual_delete_count {
        vm.charge_step()?;
        if has_at(vm, o, actual_start + k)? {
            let v = get_at(vm, o, actual_start + k)?;
            create_at(vm, a, k, v)?;
        }
        k += 1.0;
    }
    set_length(vm, a, actual_delete_count)?;
    let move_one = |vm: &mut Vm, from: f64, to: f64| -> Result<(), Abrupt> {
        vm.charge_step()?;
        if has_at(vm, o, from)? {
            let v = get_at(vm, o, from)?;
            set_at(vm, o, to, v)
        } else {
            delete_at(vm, o, to)
        }
    };
    if item_count < actual_delete_count {
        let mut k = actual_start;
        while k < len - actual_delete_count {
            move_one(vm, k + actual_delete_count, k + item_count)?;
            k += 1.0;
        }
        let mut k = len;
        while k > len - actual_delete_count + item_count {
            delete_at(vm, o, k - 1.0)?;
            k -= 1.0;
        }
    } else if item_count > actual_delete_count {
        let mut k = len - actual_delete_count;
        while k > actual_start {
            move_one(vm, k + actual_delete_count - 1.0, k + item_count - 1.0)?;
            k -= 1.0;
        }
    }
    for (i, e) in items.iter().enumerate() {
        set_at(vm, o, actual_start + i as f64, *e)?;
    }
    set_length(vm, o, len - actual_delete_count + item_count)?;
    Ok(a)
}

/// `Array.prototype.reverse ( )`, §23.1.3.26†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. Let middle be floor(len / 2).
/// 4. Let lower be 0.
/// 5. Repeat, while lower ≠ middle, a. Let upper be len - lower - 1. b. Let
///    upperP be ! ToString(𝔽(upper)). c. Let lowerP be ! ToString(𝔽(lower)).
///    d. Let lowerExists be ? HasProperty(O, lowerP). e. If lowerExists is
///    true, then i. Let lowerValue be ? Get(O, lowerP). f. Let upperExists be
///    ? HasProperty(O, upperP). g. If upperExists is true, then i. Let
///    upperValue be ? Get(O, upperP). h. If lowerExists is true and
///    upperExists is true, then i. Perform ? Set(O, lowerP, upperValue,
///    true). ii. Perform ? Set(O, upperP, lowerValue, true). i. Else if
///    lowerExists is false and upperExists is true, then i. Perform ? Set(O,
///    lowerP, upperValue, true). ii. Perform ? DeletePropertyOrThrow(O,
///    upperP). j. Else if lowerExists is true and upperExists is false, then
///    i. Perform ? DeletePropertyOrThrow(O, lowerP). ii. Perform ? Set(O,
///    upperP, lowerValue, true). k. Else, (neither exists) no action. l. Set
///    lower to lower + 1.
/// 6. Return O.
fn reverse(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let len = length_of(vm, o)?;
    let middle = (len / 2.0).floor();
    let mut lower = 0.0;
    while lower != middle {
        vm.charge_step()?;
        let upper = len - lower - 1.0;
        let lower_exists = has_at(vm, o, lower)?;
        let lower_value = if lower_exists {
            get_at(vm, o, lower)?
        } else {
            Value::UNDEFINED
        };
        let upper_exists = has_at(vm, o, upper)?;
        let upper_value = if upper_exists {
            get_at(vm, o, upper)?
        } else {
            Value::UNDEFINED
        };
        match (lower_exists, upper_exists) {
            (true, true) => {
                set_at(vm, o, lower, upper_value)?;
                set_at(vm, o, upper, lower_value)?;
            }
            (false, true) => {
                set_at(vm, o, lower, upper_value)?;
                delete_at(vm, o, upper)?;
            }
            (true, false) => {
                delete_at(vm, o, lower)?;
                set_at(vm, o, upper, lower_value)?;
            }
            (false, false) => {}
        }
        lower += 1.0;
    }
    Ok(o)
}

/// `Array.prototype.fill ( value [ , start [ , end ] ] )`, §23.1.3.7†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. to 5. Let k be the start, clamped as `relative`.
/// 6. to 8. Let final be the end (len if undefined), clamped.
/// 9. Repeat, while k < final, a. Let Pk be ! ToString(𝔽(k)). b. Perform ?
///    Set(O, Pk, value, true). c. Set k to k + 1.
/// 10. Return O.
fn fill(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let len = length_of(vm, o)?;
    let mut k = relative(vm, arg(args, 1), len)?;
    let fin = relative_end(vm, arg(args, 2), len)?;
    while k < fin {
        vm.charge_step()?;
        set_at(vm, o, k, arg(args, 0))?;
        k += 1.0;
    }
    Ok(o)
}

// ---------------------------------------------------------------------
// Accessors
// ---------------------------------------------------------------------

/// `Array.prototype.slice ( start, end )`, §23.1.3.28†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. to 5. Let k be the start, clamped as `relative`.
/// 6. to 8. Let final be the end (len if undefined), clamped.
/// 9. Let count be max(final - k, 0).
/// 10. Let A be ? ArraySpeciesCreate(O, count).
/// 11. Let n be 0.
/// 12. Repeat, while k < final, a. Let Pk be ! ToString(𝔽(k)). b. Let kPresent
///     be ? HasProperty(O, Pk). c. If kPresent is true, then i. Let kValue be
///     ? Get(O, Pk). ii. Perform ? CreateDataPropertyOrThrow(A, !
///     ToString(𝔽(n)), kValue). d. Set k to k + 1. e. Set n to n + 1.
/// 13. Perform ? Set(A, "length", 𝔽(n), true).
/// 14. Return A.
fn slice(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let len = length_of(vm, o)?;
    let mut k = relative(vm, arg(args, 0), len)?;
    let fin = relative_end(vm, arg(args, 1), len)?;
    let count = (fin - k).max(0.0);
    let a = species_create(vm, o, count)?;
    let mut n = 0.0;
    while k < fin {
        vm.charge_step()?;
        if has_at(vm, o, k)? {
            let v = get_at(vm, o, k)?;
            create_at(vm, a, n, v)?;
        }
        k += 1.0;
        n += 1.0;
    }
    set_length(vm, a, n)?;
    Ok(a)
}

/// `Array.prototype.concat ( ...items )`, §23.1.3.2†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let A be ? ArraySpeciesCreate(O, 0).
/// 3. Let n be 0.
/// 4. Prepend O to items.
/// 5. For each element E of items, do a. Let spreadable be ?
///    IsConcatSpreadable(E) (§23.1.3.2.1†: if E is not an Object, false; (the
///    `@@isConcatSpreadable` lookup is not consulted: no Symbols;) else
///    IsArray(E)). b. If spreadable is true, then i. Let k be 0. ii. Let len
///    be ? LengthOfArrayLike(E). iii. If n + len > 2^53 - 1, throw a
///    TypeError exception. iv. Repeat, while k < len, 1. Let P be !
///    ToString(𝔽(k)). 2. Let exists be ? HasProperty(E, P). 3. If exists is
///    true, then a. Let subElement be ? Get(E, P). b. Perform ?
///    CreateDataPropertyOrThrow(A, ! ToString(𝔽(n)), subElement). 4. Set n to
///    n + 1. 5. Set k to k + 1. c. Else, i. NOTE: E is added as a single
///    item rather than spread. ii. If n ≥ 2^53 - 1, throw a TypeError
///    exception. iii. Perform ? CreateDataPropertyOrThrow(A, ! ToString(𝔽(n)),
///    E). iv. Set n to n + 1.
/// 6. Perform ? Set(A, "length", 𝔽(n), true).
/// 7. Return A.
fn concat(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let a = species_create(vm, o, 0.0)?;
    let mut n = 0.0;
    let mut items = vec![o];
    items.extend_from_slice(args);
    for e in items {
        if vm.is_array(e) {
            let len = length_of(vm, e)?;
            if n + len > MAX_SAFE {
                return Err(vm.type_error("Invalid array length"));
            }
            let mut k = 0.0;
            while k < len {
                vm.charge_step()?;
                if has_at(vm, e, k)? {
                    let v = get_at(vm, e, k)?;
                    create_at(vm, a, n, v)?;
                }
                n += 1.0;
                k += 1.0;
            }
        } else {
            if n >= MAX_SAFE {
                return Err(vm.type_error("Invalid array length"));
            }
            create_at(vm, a, n, e)?;
            n += 1.0;
        }
    }
    set_length(vm, a, n)?;
    Ok(a)
}

/// `Array.prototype.join ( separator )`, §23.1.3.18†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. If separator is undefined, let sep be ",".
/// 4. Else, let sep be ? ToString(separator).
/// 5. Let R be the empty String.
/// 6. Let k be 0.
/// 7. Repeat, while k < len, a. If k > 0, set R to the string-concatenation of
///    R and sep. b. Let element be ? Get(O, ! ToString(𝔽(k))). c. If element
///    is either undefined or null, let next be the empty String; otherwise,
///    let next be ? ToString(element). d. Set R to the string-concatenation of
///    R and next. e. Set k to k + 1.
/// 8. Return R.
fn join(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let len = length_of(vm, o)?;
    let sep: Vec<u16> = if arg(args, 0) == Value::UNDEFINED {
        vec![u16::from(b',')]
    } else {
        vm.to_js_string(arg(args, 0))?.units().collect()
    };
    let mut r: Vec<u16> = Vec::new();
    let mut k = 0.0;
    while k < len {
        vm.charge_step()?;
        if k > 0.0 {
            r.extend_from_slice(&sep);
        }
        let element = get_at(vm, o, k)?;
        if element != Value::UNDEFINED && element != Value::NULL {
            r.extend(vm.to_js_string(element)?.units());
        }
        k += 1.0;
    }
    let s = JsString::from_units(&r).map_err(|_| Abrupt::OutOfMemory)?;
    js_string(vm, s)
}

/// `Array.prototype.toString ( )`, §23.1.3.33†:
/// 1. Let array be ? ToObject(this value).
/// 2. Let func be ? Get(array, "join").
/// 3. If IsCallable(func) is false, then a. Set func to the intrinsic
///    function %Object.prototype.toString%.
/// 4. Return ? Call(func, array).
fn to_string(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let array = vm.to_object(this)?;
    let func = vm.get_named(array, "join")?;
    let func = if vm.heap().is_callable(func) {
        func
    } else {
        let op = vm.intrinsic(Intrinsic::ObjectPrototype);
        vm.get_named(op, "toString")?
    };
    vm.call(func, array, &[])
}

/// `Array.prototype.indexOf ( searchElement [ , fromIndex ] )`, §23.1.3.17†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. If len = 0, return -1𝔽.
/// 4. Let n be ? ToIntegerOrInfinity(fromIndex).
/// 5. (Assert: If fromIndex is undefined, then n is 0.)
/// 6. If n = +∞, return -1𝔽.
/// 7. Else if n = -∞, set n to 0.
/// 8. If n ≥ 0, then a. Let k be n.
/// 9. Else, a. Let k be len + n. b. If k < 0, set k to 0.
/// 10. Repeat, while k < len, a. Let kPresent be ? HasProperty(O, !
///     ToString(𝔽(k))). b. If kPresent is true, then i. Let elementK be ?
///     Get(O, ! ToString(𝔽(k))). ii. If IsStrictlyEqual(searchElement,
///     elementK) is true, return 𝔽(k). c. Set k to k + 1.
/// 11. Return -1𝔽.
fn index_of(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let len = length_of(vm, o)?;
    if len == 0.0 {
        return Ok(Value::int32(-1));
    }
    let n = to_integer_or_infinity(vm, arg(args, 1))?;
    if n == f64::INFINITY {
        return Ok(Value::int32(-1));
    }
    let mut k = if n == f64::NEG_INFINITY {
        0.0
    } else if n >= 0.0 {
        n
    } else {
        (len + n).max(0.0)
    };
    while k < len {
        vm.charge_step()?;
        if has_at(vm, o, k)? {
            let e = get_at(vm, o, k)?;
            if vm.strict_equals(arg(args, 0), e) {
                return Ok(number(k));
            }
        }
        k += 1.0;
    }
    Ok(Value::int32(-1))
}

/// `Array.prototype.lastIndexOf ( searchElement [ , fromIndex ] )`,
/// §23.1.3.20†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. If len = 0, return -1𝔽.
/// 4. If fromIndex is present, let n be ? ToIntegerOrInfinity(fromIndex); else
///    let n be len - 1.
/// 5. If n = -∞, return -1𝔽.
/// 6. If n ≥ 0, then a. Let k be min(n, len - 1).
/// 7. Else, a. Let k be len + n.
/// 8. Repeat, while k ≥ 0, a. Let kPresent be ? HasProperty(O, ! ToString(𝔽(k))).
///    b. If kPresent is true, then i. Let elementK be ? Get(O, ! ToString(𝔽(k))).
///    ii. If IsStrictlyEqual(searchElement, elementK) is true, return 𝔽(k).
///    c. Set k to k - 1.
/// 9. Return -1𝔽.
fn last_index_of(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let len = length_of(vm, o)?;
    if len == 0.0 {
        return Ok(Value::int32(-1));
    }
    let n = if args.len() > 1 {
        to_integer_or_infinity(vm, arg(args, 1))?
    } else {
        len - 1.0
    };
    if n == f64::NEG_INFINITY {
        return Ok(Value::int32(-1));
    }
    let mut k = if n >= 0.0 { n.min(len - 1.0) } else { len + n };
    while k >= 0.0 {
        vm.charge_step()?;
        if has_at(vm, o, k)? {
            let e = get_at(vm, o, k)?;
            if vm.strict_equals(arg(args, 0), e) {
                return Ok(number(k));
            }
        }
        k -= 1.0;
    }
    Ok(Value::int32(-1))
}

/// `Array.prototype.includes ( searchElement [ , fromIndex ] )`, §23.1.3.16†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. If len = 0, return false.
/// 4. Let n be ? ToIntegerOrInfinity(fromIndex).
/// 5. (Assert: If fromIndex is undefined, then n is 0.)
/// 6. If n = +∞, return false.
/// 7. Else if n = -∞, set n to 0.
/// 8. If n ≥ 0, then a. Let k be n.
/// 9. Else, a. Let k be len + n. b. If k < 0, set k to 0.
/// 10. Repeat, while k < len, a. Let elementK be ? Get(O, ! ToString(𝔽(k))).
///     b. If SameValueZero(searchElement, elementK) is true, return true. c.
///     Set k to k + 1.
/// 11. Return false.
fn includes(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let len = length_of(vm, o)?;
    if len == 0.0 {
        return Ok(Value::FALSE);
    }
    let n = to_integer_or_infinity(vm, arg(args, 1))?;
    if n == f64::INFINITY {
        return Ok(Value::FALSE);
    }
    let mut k = if n == f64::NEG_INFINITY {
        0.0
    } else if n >= 0.0 {
        n
    } else {
        (len + n).max(0.0)
    };
    while k < len {
        vm.charge_step()?;
        let e = get_at(vm, o, k)?;
        if same_value_zero(vm, arg(args, 0), e) {
            return Ok(Value::TRUE);
        }
        k += 1.0;
    }
    Ok(Value::FALSE)
}

// ---------------------------------------------------------------------
// Callback methods
// ---------------------------------------------------------------------

/// The callback of one element: `Call(callbackfn, thisArg, « kValue, 𝔽(k), O
/// »)`.
fn call3(
    vm: &mut Vm,
    f: Value,
    this_arg: Value,
    v: Value,
    k: f64,
    o: Value,
) -> Result<Value, Abrupt> {
    vm.call(f, this_arg, &[v, number(k), o])
}

/// `Array.prototype.forEach ( callbackfn [ , thisArg ] )`, §23.1.3.15†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. If IsCallable(callbackfn) is false, throw a TypeError exception.
/// 4. Let k be 0.
/// 5. Repeat, while k < len, a. Let Pk be ! ToString(𝔽(k)). b. Let kPresent be
///    ? HasProperty(O, Pk). c. If kPresent is true, then i. Let kValue be ?
///    Get(O, Pk). ii. Perform ? Call(callbackfn, thisArg, « kValue, 𝔽(k), O
///    »). d. Set k to k + 1.
/// 6. Return undefined.
fn for_each(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let len = length_of(vm, o)?;
    let f = callable(vm, arg(args, 0))?;
    let mut k = 0.0;
    while k < len {
        vm.charge_step()?;
        if has_at(vm, o, k)? {
            let v = get_at(vm, o, k)?;
            call3(vm, f, arg(args, 1), v, k, o)?;
        }
        k += 1.0;
    }
    Ok(Value::UNDEFINED)
}

/// `Array.prototype.map ( callbackfn [ , thisArg ] )`, §23.1.3.21†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. If IsCallable(callbackfn) is false, throw a TypeError exception.
/// 4. Let A be ? ArraySpeciesCreate(O, len).
/// 5. Let k be 0.
/// 6. Repeat, while k < len, a. Let Pk be ! ToString(𝔽(k)). b. Let kPresent be
///    ? HasProperty(O, Pk). c. If kPresent is true, then i. Let kValue be ?
///    Get(O, Pk). ii. Let mappedValue be ? Call(callbackfn, thisArg, « kValue,
///    𝔽(k), O »). iii. Perform ? CreateDataPropertyOrThrow(A, Pk,
///    mappedValue). d. Set k to k + 1.
/// 7. Return A.
fn map(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let len = length_of(vm, o)?;
    let f = callable(vm, arg(args, 0))?;
    let a = species_create(vm, o, len)?;
    let mut k = 0.0;
    while k < len {
        vm.charge_step()?;
        if has_at(vm, o, k)? {
            let v = get_at(vm, o, k)?;
            let mapped = call3(vm, f, arg(args, 1), v, k, o)?;
            create_at(vm, a, k, mapped)?;
        }
        k += 1.0;
    }
    Ok(a)
}

/// `Array.prototype.filter ( callbackfn [ , thisArg ] )`, §23.1.3.8†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. If IsCallable(callbackfn) is false, throw a TypeError exception.
/// 4. Let A be ? ArraySpeciesCreate(O, 0).
/// 5. Let k be 0.
/// 6. Let to be 0.
/// 7. Repeat, while k < len, a. Let Pk be ! ToString(𝔽(k)). b. Let kPresent be
///    ? HasProperty(O, Pk). c. If kPresent is true, then i. Let kValue be ?
///    Get(O, Pk). ii. Let selected be ToBoolean(? Call(callbackfn, thisArg, «
///    kValue, 𝔽(k), O »)). iii. If selected is true, then 1. Perform ?
///    CreateDataPropertyOrThrow(A, ! ToString(𝔽(to)), kValue). 2. Set to to to
///    + 1. d. Set k to k + 1.
/// 8. Return A.
fn filter(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let len = length_of(vm, o)?;
    let f = callable(vm, arg(args, 0))?;
    let a = species_create(vm, o, 0.0)?;
    let (mut k, mut to) = (0.0, 0.0);
    while k < len {
        vm.charge_step()?;
        if has_at(vm, o, k)? {
            let v = get_at(vm, o, k)?;
            let r = call3(vm, f, arg(args, 1), v, k, o)?;
            if vm.to_boolean(r) {
                create_at(vm, a, to, v)?;
                to += 1.0;
            }
        }
        k += 1.0;
    }
    Ok(a)
}

/// `Array.prototype.some ( callbackfn [ , thisArg ] )`, §23.1.3.29†, and
/// `Array.prototype.every`, §23.1.3.6†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. If IsCallable(callbackfn) is false, throw a TypeError exception.
/// 4. Let k be 0.
/// 5. Repeat, while k < len, a. Let Pk be ! ToString(𝔽(k)). b. Let kPresent be
///    ? HasProperty(O, Pk). c. If kPresent is true, then i. Let kValue be ?
///    Get(O, Pk). ii. Let testResult be ToBoolean(? Call(callbackfn, thisArg,
///    « kValue, 𝔽(k), O »)). iii. (`some`:) If testResult is true, return
///    true. (`every`:) If testResult is false, return false. d. Set k to k +
///    1.
/// 6. Return false (`some`) or true (`every`).
fn some_or_every(vm: &mut Vm, this: Value, args: &[Value], is_some: bool) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let len = length_of(vm, o)?;
    let f = callable(vm, arg(args, 0))?;
    let mut k = 0.0;
    while k < len {
        vm.charge_step()?;
        if has_at(vm, o, k)? {
            let v = get_at(vm, o, k)?;
            let r = call3(vm, f, arg(args, 1), v, k, o)?;
            if vm.to_boolean(r) == is_some {
                return Ok(Value::boolean(is_some));
            }
        }
        k += 1.0;
    }
    Ok(Value::boolean(!is_some))
}

fn some(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    some_or_every(vm, this, args, true)
}

fn every(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    some_or_every(vm, this, args, false)
}

/// `Array.prototype.reduce ( callbackfn [ , initialValue ] )`, §23.1.3.24†,
/// and `reduceRight`, §23.1.3.25†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. If IsCallable(callbackfn) is false, throw a TypeError exception.
/// 4. If len = 0 and initialValue is not present, throw a TypeError exception.
/// 5. Let k be 0 (`reduceRight`: len - 1).
/// 6. Let accumulator be undefined.
/// 7. If initialValue is present, then a. Set accumulator to initialValue.
/// 8. Else, a. Let kPresent be false. b. Repeat, while kPresent is false and k
///    < len (k ≥ 0), i. Let Pk be ! ToString(𝔽(k)). ii. Set kPresent to ?
///    HasProperty(O, Pk). iii. If kPresent is true, then 1. Set accumulator to
///    ? Get(O, Pk). iv. Set k to k + 1 (k - 1). c. If kPresent is false, throw
///    a TypeError exception.
/// 9. Repeat, while k < len (k ≥ 0), a. Let Pk be ! ToString(𝔽(k)). b. Let
///    kPresent be ? HasProperty(O, Pk). c. If kPresent is true, then i. Let
///    kValue be ? Get(O, Pk). ii. Set accumulator to ? Call(callbackfn,
///    undefined, « accumulator, kValue, 𝔽(k), O »). d. Set k to k + 1 (k - 1).
/// 10. Return accumulator.
fn reduce_impl(vm: &mut Vm, this: Value, args: &[Value], right: bool) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let len = length_of(vm, o)?;
    let f = callable(vm, arg(args, 0))?;
    if len == 0.0 && args.len() < 2 {
        return Err(vm.type_error("Reduce of empty array with no initial value"));
    }
    let (mut k, step) = if right { (len - 1.0, -1.0) } else { (0.0, 1.0) };
    let in_range = |k: f64| if right { k >= 0.0 } else { k < len };
    let mut acc = Value::UNDEFINED;
    if args.len() >= 2 {
        acc = arg(args, 1);
    } else {
        let mut present = false;
        while !present && in_range(k) {
            vm.charge_step()?;
            present = has_at(vm, o, k)?;
            if present {
                acc = get_at(vm, o, k)?;
            }
            k += step;
        }
        if !present {
            return Err(vm.type_error("Reduce of empty array with no initial value"));
        }
    }
    while in_range(k) {
        vm.charge_step()?;
        if has_at(vm, o, k)? {
            let v = get_at(vm, o, k)?;
            acc = vm.call(f, Value::UNDEFINED, &[acc, v, number(k), o])?;
        }
        k += step;
    }
    Ok(acc)
}

fn reduce(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    reduce_impl(vm, this, args, false)
}

fn reduce_right(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    reduce_impl(vm, this, args, true)
}

/// `Array.prototype.find ( predicate [ , thisArg ] )`, §23.1.3.9†, and
/// `findIndex`, §23.1.3.10†, over FindViaPredicate ( O, len, direction,
/// predicate, thisArg ), §23.1.3.9.1†:
/// 1. Let O be ? ToObject(this value).
/// 2. Let len be ? LengthOfArrayLike(O).
/// 3. Let findRec be ? FindViaPredicate(O, len, ascending, predicate,
///    thisArg).
/// 4. Return findRec.[[Value]] (`find`) or findRec.[[Index]] (`findIndex`).
///
/// FindViaPredicate:
/// 1. If IsCallable(predicate) is false, throw a TypeError exception.
/// 2. If direction is ascending, let indices be a List of the integers in the
///    interval from 0 to len, exclusive, in ascending order.
/// 4. For each integer k of indices, do a. Let Pk be ! ToString(𝔽(k)). b. NOTE:
///    If O is a TypedArray, the following invocation of Get will return a
///    normal completion. c. Let kValue be ? Get(O, Pk). d. Let testResult be ?
///    Call(predicate, thisArg, « kValue, 𝔽(k), O »). e. If ToBoolean(testResult)
///    is true, return the Record { [[Index]]: 𝔽(k), [[Value]]: kValue }.
/// 5. Return the Record { [[Index]]: -1𝔽, [[Value]]: undefined }.
fn find_via_predicate(vm: &mut Vm, this: Value, args: &[Value]) -> Result<(f64, Value), Abrupt> {
    let o = vm.to_object(this)?;
    let len = length_of(vm, o)?;
    let f = callable(vm, arg(args, 0))?;
    let mut k = 0.0;
    while k < len {
        vm.charge_step()?;
        let v = get_at(vm, o, k)?;
        let r = call3(vm, f, arg(args, 1), v, k, o)?;
        if vm.to_boolean(r) {
            return Ok((k, v));
        }
        k += 1.0;
    }
    Ok((-1.0, Value::UNDEFINED))
}

fn find(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    Ok(find_via_predicate(vm, this, args)?.1)
}

fn find_index(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    Ok(number(find_via_predicate(vm, this, args)?.0))
}

// ---------------------------------------------------------------------
// sort
// ---------------------------------------------------------------------

/// SortCompare ( x, y ), §23.1.3.30.2†, with the `comparefn` of the call:
/// 1. If x and y are both undefined, return +0𝔽.
/// 2. If x is undefined, return 1𝔽.
/// 3. If y is undefined, return -1𝔽.
/// 4. If comparefn is not undefined, then a. Let v be ? ToNumber(? Call(comparefn,
///    undefined, « x, y »)). b. If v is NaN, return +0𝔽. c. Return v.
/// 5. Let xString be ? ToString(x).
/// 6. Let yString be ? ToString(y).
/// 7. Let xSmaller be ! IsLessThan(xString, yString, true) (by code units).
/// 8. If xSmaller is true, return -1𝔽.
/// 9. Let ySmaller be ! IsLessThan(yString, xString, true).
/// 10. If ySmaller is true, return 1𝔽.
/// 11. Return +0𝔽.
fn sort_compare(vm: &mut Vm, cmp: Value, x: Value, y: Value) -> Result<f64, Abrupt> {
    if x == Value::UNDEFINED && y == Value::UNDEFINED {
        return Ok(0.0);
    }
    if x == Value::UNDEFINED {
        return Ok(1.0);
    }
    if y == Value::UNDEFINED {
        return Ok(-1.0);
    }
    if cmp != Value::UNDEFINED {
        let r = vm.call(cmp, Value::UNDEFINED, &[x, y])?;
        let v = vm.to_number(r)?;
        return Ok(if v.is_nan() { 0.0 } else { v });
    }
    let xs = vm.to_js_string(x)?;
    let ys = vm.to_js_string(y)?;
    Ok(match xs.units().cmp(ys.units()) {
        std::cmp::Ordering::Less => -1.0,
        std::cmp::Ordering::Greater => 1.0,
        std::cmp::Ordering::Equal => 0.0,
    })
}

/// A stable merge sort over `items` by `SortCompare` (the standard requires a
/// stable sort, §23.1.3.30† NOTE 2; an exception from the comparator ends it).
fn merge_sort(vm: &mut Vm, cmp: Value, items: Vec<Value>) -> Result<Vec<Value>, Abrupt> {
    let n = items.len();
    if n < 2 {
        return Ok(items);
    }
    let mut src = items;
    let mut width = 1usize;
    while width < n {
        let mut dst: Vec<Value> = Vec::with_capacity(n);
        let mut start = 0usize;
        while start < n {
            let mid = start.saturating_add(width).min(n);
            let end = start.saturating_add(width.saturating_mul(2)).min(n);
            let (mut i, mut j) = (start, mid);
            while i < mid && j < end {
                vm.charge_step()?;
                let (l, r) = (
                    *src.get(i).ok_or(Abrupt::Internal("sort index"))?,
                    *src.get(j).ok_or(Abrupt::Internal("sort index"))?,
                );
                // Stable: the right one goes first only when it is smaller.
                if sort_compare(vm, cmp, l, r)? > 0.0 {
                    dst.push(r);
                    j = j.saturating_add(1);
                } else {
                    dst.push(l);
                    i = i.saturating_add(1);
                }
            }
            while let Some(v) = src.get(i).filter(|_| i < mid) {
                dst.push(*v);
                i = i.saturating_add(1);
            }
            while let Some(v) = src.get(j).filter(|_| j < end) {
                dst.push(*v);
                j = j.saturating_add(1);
            }
            start = end;
        }
        src = dst;
        width = width.saturating_mul(2);
    }
    Ok(src)
}

/// `Array.prototype.sort ( comparefn )`, §23.1.3.30†:
/// 1. If comparefn is not undefined and IsCallable(comparefn) is false, throw
///    a TypeError exception.
/// 2. Let obj be ? ToObject(this value).
/// 3. Let len be ? LengthOfArrayLike(obj).
/// 4. Let SortCompare be a new Abstract Closure ... that performs
///    SortCompare(x, y) with comparefn.
/// 5. Let sortedList be ? SortIndexedProperties(obj, len, SortCompare,
///    skip-holes).
/// 6. Let itemCount be the number of elements in sortedList.
/// 7. Let j be 0.
/// 8. Repeat, while j < itemCount, a. Perform ? Set(obj, ! ToString(𝔽(j)),
///    sortedList[j], true). b. Set j to j + 1.
/// 9. NOTE: The call to SortIndexedProperties in step 5 uses skip-holes. The
///    remaining indices are deleted to preserve the number of holes that were
///    detected and excluded from the sort.
/// 10. Repeat, while j < len, a. Perform ? DeletePropertyOrThrow(obj, !
///     ToString(𝔽(j))). b. Set j to j + 1.
/// 11. Return obj.
///
/// SortIndexedProperties ( obj, len, SortCompare, holes ), §23.1.3.30.1†:
/// 1. Let items be a new empty List.
/// 2. Let k be 0.
/// 3. Repeat, while k < len, a. Let Pk be ! ToString(𝔽(k)). b. If holes is
///    skip-holes, then i. Let kRead be ? HasProperty(obj, Pk). c. Else, (read-through-holes)
///    ... d. If kRead is true, then i. Let kValue be ? Get(obj, Pk). ii.
///    Append kValue to items. e. Set k to k + 1.
/// 4. Sort items using an implementation-defined sequence of calls to
///    SortCompare. If any call returns an abrupt completion, stop before
///    performing any further calls and return that Completion Record. (The
///    sort is stable.)
/// 5. Return items.
fn sort(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let cmp = arg(args, 0);
    if cmp != Value::UNDEFINED && !vm.heap().is_callable(cmp) {
        return Err(vm.type_error("The comparison function must be either a function or undefined"));
    }
    let obj = vm.to_object(this)?;
    let len = length_of(vm, obj)?;
    let mut items = Vec::new();
    let mut k = 0.0;
    while k < len {
        vm.charge_step()?;
        if has_at(vm, obj, k)? {
            items.push(get_at(vm, obj, k)?);
        }
        k += 1.0;
    }
    let sorted = merge_sort(vm, cmp, items)?;
    let mut j = 0.0;
    for v in &sorted {
        set_at(vm, obj, j, *v)?;
        j += 1.0;
    }
    while j < len {
        vm.charge_step()?;
        delete_at(vm, obj, j)?;
        j += 1.0;
    }
    Ok(obj)
}
