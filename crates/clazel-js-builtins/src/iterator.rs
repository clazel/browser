//! Iteration (§27.1†, §23.1.5†, §22.1.5†): `%Iterator.prototype%` with its
//! `@@iterator`, `%ArrayIteratorPrototype%` and `%StringIteratorPrototype%`
//! with their `next`, and CreateIterResultObject.
//!
//! The standard writes the Array and String iterators as generators over an
//! abstract closure (CreateArrayIterator §23.1.5.1†, `String.prototype [
//! @@iterator ]` §22.1.3.36†); here the closure's state is the iterator
//! object's own slots ([`ObjKind::ArrayIterator`], [`ObjKind::StringIterator`])
//! and `next` runs one step of the closure. The observable behaviour is the
//! same: each `next` reads the length afresh (an array that grows is seen to
//! grow), and once done an iterator stays done.
//!
//! Not here: the `Iterator` constructor and its helpers (`map`, `filter`,
//! `take`, ...; §27.1.3†), and `%IteratorHelperPrototype%`.

use crate::symbol::to_string_tag;
use crate::util::{js_string, method, number};
use clazel_js_heap::string::JsString;
use clazel_js_heap::symbol as wk;
use clazel_js_heap::value::Value;
use clazel_js_vm::heap::{IterKind, ObjKind};
use clazel_js_vm::interp::{Abrupt, Intrinsic, Vm};

/// Installs `%Iterator.prototype%`, `%ArrayIteratorPrototype%` and
/// `%StringIteratorPrototype%` (the `Array` and `String` methods that make
/// iterators are in their modules).
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    // §27.1.2†: an ordinary object whose [[Prototype]] is %Object.prototype%.
    let iter_proto = vm.new_object()?;
    vm.set_intrinsic(Intrinsic::IteratorPrototype, iter_proto);
    // §27.1.2.1† `%Iterator.prototype% [ @@iterator ] ( )`: its `name` is
    // "[Symbol.iterator]".
    let f = vm.new_native("[Symbol.iterator]", 0, return_this)?;
    let k = vm.well_known_key(wk::ITERATOR)?;
    vm.heap_mut()
        .define(iter_proto, k, f, crate::util::METHOD)?;

    // §23.1.5.2†: %ArrayIteratorPrototype% has [[Prototype]]
    // %Iterator.prototype%.
    let array_proto = vm.heap_mut().new_object(iter_proto, ObjKind::Plain)?;
    vm.set_intrinsic(Intrinsic::ArrayIteratorPrototype, array_proto);
    method(vm, array_proto, "next", 0, array_iterator_next)?;
    to_string_tag(vm, array_proto, "Array Iterator")?;

    // §22.1.5.1†: %StringIteratorPrototype% likewise.
    let string_proto = vm.heap_mut().new_object(iter_proto, ObjKind::Plain)?;
    vm.set_intrinsic(Intrinsic::StringIteratorPrototype, string_proto);
    method(vm, string_proto, "next", 0, string_iterator_next)?;
    to_string_tag(vm, string_proto, "String Iterator")
}

/// `%Iterator.prototype% [ @@iterator ] ( )`, §27.1.2.1†:
/// 1. Return the this value.
fn return_this(_vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    Ok(this)
}

/// CreateIterResultObject ( value, done ), §7.4.14†:
/// 1. Let obj be OrdinaryObjectCreate(%Object.prototype%).
/// 2. Perform ! CreateDataPropertyOrThrow(obj, "value", value).
/// 3. Perform ! CreateDataPropertyOrThrow(obj, "done", done).
/// 4. Return obj.
///
/// # Errors
/// [`Abrupt::OutOfMemory`].
pub fn iter_result(vm: &mut Vm, value: Value, done: bool) -> Result<Value, Abrupt> {
    let o = vm.new_object()?;
    vm.define_property(o, "value", value)?;
    vm.define_property(o, "done", Value::boolean(done))?;
    Ok(o)
}

/// CreateArrayIterator ( array, kind ), §23.1.5.1†: an Array Iterator over
/// `array` whose [[Prototype]] is %ArrayIteratorPrototype%.
///
/// # Errors
/// [`Abrupt::OutOfMemory`].
pub fn create_array_iterator(vm: &mut Vm, array: Value, kind: IterKind) -> Result<Value, Abrupt> {
    let proto = vm.intrinsic(Intrinsic::ArrayIteratorPrototype);
    Ok(vm.heap_mut().new_object(
        proto,
        ObjKind::ArrayIterator {
            target: array,
            next: 0,
            kind,
        },
    )?)
}

/// A String Iterator over the string value `s` (§22.1.3.36† step 5:
/// CreateIteratorFromClosure(closure, "%StringIteratorPrototype%", ...)).
///
/// # Errors
/// [`Abrupt::OutOfMemory`].
pub fn create_string_iterator(vm: &mut Vm, s: Value) -> Result<Value, Abrupt> {
    let proto = vm.intrinsic(Intrinsic::StringIteratorPrototype);
    Ok(vm
        .heap_mut()
        .new_object(proto, ObjKind::StringIterator { target: s, next: 0 })?)
}

/// `%ArrayIteratorPrototype%.next ( )`, §23.1.5.2.1†: GeneratorResume(this
/// value, empty, "%ArrayIteratorPrototype%"), a TypeError if the this value
/// is not an Array Iterator (GeneratorValidate, §27.5.3.2† steps 1 and 2),
/// then one step of CreateArrayIterator's closure, §23.1.5.1† step 1:
/// a. Let index be 0.
/// b. Repeat,
///    i. If array has a [[TypedArrayName]] internal slot, then (no typed
///       arrays yet)
///    ii. Else, 1. Let len be ? LengthOfArrayLike(array).
///    iii. If index ≥ len, return NormalCompletion(undefined) (the iterator
///         is done from then on).
///    iv. Let indexNumber be 𝔽(index).
///    v. If kind is key, then 1. Let result be indexNumber.
///    vi. Else, 1. Let elementKey be ! ToString(indexNumber). 2. Let
///        elementValue be ? Get(array, elementKey). 3. If kind is value,
///        then a. Let result be elementValue. 4. Else, a. Assert: kind is
///        key+value. b. Let result be CreateArrayFromList(« indexNumber,
///        elementValue »).
///    vii. Perform ? GeneratorYield(CreateIterResultObject(result, false)).
///    viii. Set index to index + 1.
fn array_iterator_next(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let Some(ObjKind::ArrayIterator { target, next, kind }) = vm.heap().obj(this).map(|o| o.kind)
    else {
        return Err(vm.type_error("next called on an object that is not an Array Iterator"));
    };
    if target == Value::UNDEFINED {
        return iter_result(vm, Value::UNDEFINED, true);
    }
    let kl = crate::util::key(vm, "length")?;
    let lv = vm.get_value(target, kl)?;
    let len = crate::util::to_integer_or_infinity(vm, lv)?.clamp(0.0, 9_007_199_254_740_991.0);
    let index = next as f64;
    if index >= len {
        set_array_iterator(vm, this, Value::UNDEFINED, next, kind)?;
        return iter_result(vm, Value::UNDEFINED, true);
    }
    // The index stays below 2^53, so the increment cannot overflow.
    set_array_iterator(vm, this, target, next.saturating_add(1), kind)?;
    let result = match kind {
        IterKind::Keys => number(index),
        IterKind::Values | IterKind::Entries => {
            let k = vm.index_key(next)?;
            let v = vm.get_value(target, k)?;
            if kind == IterKind::Values {
                v
            } else {
                vm.create_array_from_list(&[number(index), v])?
            }
        }
    };
    iter_result(vm, result, false)
}

fn set_array_iterator(
    vm: &mut Vm,
    it: Value,
    target: Value,
    next: u64,
    kind: IterKind,
) -> Result<(), Abrupt> {
    let o = vm
        .heap_mut()
        .obj_mut(it)
        .ok_or(Abrupt::Internal("array iterator"))?;
    o.kind = ObjKind::ArrayIterator { target, next, kind };
    Ok(())
}

/// `%StringIteratorPrototype%.next ( )`, §22.1.5.1.1†: GeneratorResume(this
/// value, empty, "%StringIteratorPrototype%") (a TypeError if the this value
/// is not a String Iterator), then one step of the closure of `String.prototype
/// [ @@iterator ]`, §22.1.3.36† step 4:
/// a. Let len be the length of s.
/// b. Let position be 0.
/// c. Repeat, while position < len,
///    i. Let cp be CodePointAt(s, position).
///    ii. Let nextIndex be position + cp.[[CodeUnitCount]].
///    iii. Let resultString be the substring of s from position to nextIndex.
///    iv. Set position to nextIndex.
///    v. Perform ? GeneratorYield(CreateIterResultObject(resultString, false)).
/// d. Return NormalCompletion(unused).
fn string_iterator_next(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let Some(ObjKind::StringIterator { target, next }) = vm.heap().obj(this).map(|o| o.kind) else {
        return Err(vm.type_error("next called on an object that is not a String Iterator"));
    };
    let Some(s) = vm.heap().string(target).cloned() else {
        return iter_result(vm, Value::UNDEFINED, true);
    };
    let position = usize::try_from(next).map_err(|_| Abrupt::Internal("string index"))?;
    if position >= s.len() {
        set_string_iterator(vm, this, Value::UNDEFINED, next)?;
        return iter_result(vm, Value::UNDEFINED, true);
    }
    let count = code_point_at(&s, position).1;
    let next_index = position.saturating_add(count);
    let n = u32::try_from(next_index).map_err(|_| Abrupt::Internal("string index"))?;
    set_string_iterator(vm, this, target, n)?;
    let piece = js_string(vm, s.substring(position, next_index))?;
    iter_result(vm, piece, false)
}

fn set_string_iterator(vm: &mut Vm, it: Value, target: Value, next: u32) -> Result<(), Abrupt> {
    let o = vm
        .heap_mut()
        .obj_mut(it)
        .ok_or(Abrupt::Internal("string iterator"))?;
    o.kind = ObjKind::StringIterator { target, next };
    Ok(())
}

/// CodePointAt ( string, position ), §11.1.4†: the code point at
/// `position` and its [[CodeUnitCount]] (a lone surrogate is itself, one
/// unit):
/// 1. Let size be the length of string.
/// 2. Assert: position ≥ 0 and position < size.
/// 3. Let first be the code unit at index position within string.
/// 4. Let cp be the code point whose numeric value is the numeric value of
///    first.
/// 5. If first is neither a leading surrogate nor a trailing surrogate, then
///    a. Return the Record { [[CodePoint]]: cp, [[CodeUnitCount]]: 1,
///    [[IsUnpairedSurrogate]]: false }.
/// 6. If first is a trailing surrogate or position + 1 = size, then
///    a. Return the Record { [[CodePoint]]: cp, [[CodeUnitCount]]: 1,
///    [[IsUnpairedSurrogate]]: true }.
/// 7. Let second be the code unit at index position + 1 within string.
/// 8. If second is not a trailing surrogate, then
///    a. Return the Record { [[CodePoint]]: cp, [[CodeUnitCount]]: 1,
///    [[IsUnpairedSurrogate]]: true }.
/// 9. Set cp to UTF16SurrogatePairToCodePoint(first, second).
/// 10. Return the Record { [[CodePoint]]: cp, [[CodeUnitCount]]: 2,
///     [[IsUnpairedSurrogate]]: false }.
///
/// (`(0, 0)` past the end.)
#[must_use]
pub fn code_point_at(s: &JsString, position: usize) -> (u32, usize) {
    let Some(first) = s.unit(position) else {
        return (0, 0);
    };
    let cp = u32::from(first);
    if !(0xD800..=0xDBFF).contains(&first) {
        return (cp, 1);
    }
    match s.unit(position.saturating_add(1)) {
        Some(second) if (0xDC00..=0xDFFF).contains(&second) => {
            // UTF16SurrogatePairToCodePoint, §11.1.3†: (lead - 0xD800) ×
            // 0x400 + (trail - 0xDC00) + 0x10000; the ranges keep it in
            // u32.
            let lead = u32::from(first).saturating_sub(0xD800);
            let trail = u32::from(second).saturating_sub(0xDC00);
            (
                lead.saturating_mul(0x400)
                    .saturating_add(trail)
                    .saturating_add(0x1_0000),
                2,
            )
        }
        _ => (cp, 1),
    }
}
