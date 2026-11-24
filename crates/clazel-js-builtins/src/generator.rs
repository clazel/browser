//! The objects of generators and async functions (§27.1.4† to §27.1.6†,
//! §27.3† to §27.7†): `%GeneratorFunction%` and its prototype,
//! `%GeneratorPrototype%` with `next`, `return` and `throw`, `%AsyncFunction%`
//! and its prototype, `%AsyncIteratorPrototype%`, `%AsyncGeneratorFunction%`
//! and its prototype, `%AsyncGeneratorPrototype%` with `next`, `return` and
//! `throw`, and `%AsyncFromSyncIteratorPrototype%`.
//!
//! The VM runs the functions themselves (`clazel_js_vm::suspend`): the frame
//! of a generator is copied into its generator object, and the methods here
//! resume it. Each method's comment quotes the algorithm it covers; the
//! resumption algorithms are quoted where the VM implements them.
//!
//! # Differences from the standard, all listed
//!
//! - **The constructors `%GeneratorFunction%`, `%AsyncFunction%` and
//!   `%AsyncGeneratorFunction%`** (§27.3.1.1†, §27.7.1.1†, §27.4.1.1†) are
//!   CreateDynamicFunction, which compiles source text, as `Function` does:
//!   not yet (they throw "not implemented", as `Function` does).

use crate::promise::{Cap, new_promise_capability, perform_promise_then, promise_resolve};
use crate::symbol::to_string_tag;
use crate::util::{CONFIGURABLE_ONLY, CONSTANT, arg, caught, define, method, new_object_with};
use clazel_js_heap::symbol as wk;
use clazel_js_heap::value::Value;
use clazel_js_vm::heap::ObjKind;
use clazel_js_vm::interp::{Abrupt, Intrinsic, Vm};
use clazel_js_vm::suspend::{ResumeMode, TAG_ASYNC_FROM_SYNC};

/// Installs the objects of this module and makes them the VM's intrinsics.
/// Needs `%Function.prototype%`, `%Iterator.prototype%` and `Promise`
/// installed first.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    let function_proto = vm.intrinsic(Intrinsic::FunctionPrototype);
    let object_proto = vm.intrinsic(Intrinsic::ObjectPrototype);
    let iterator_proto = vm.intrinsic(Intrinsic::IteratorPrototype);

    // §27.3.3† %GeneratorFunction.prototype% and §27.5.1†
    // %GeneratorPrototype%.
    let gf_proto = new_object_with(vm, function_proto, ObjKind::Plain)?;
    let g_proto = new_object_with(vm, iterator_proto, ObjKind::Plain)?;
    vm.set_intrinsic(Intrinsic::GeneratorFunctionPrototype, gf_proto);
    vm.set_intrinsic(Intrinsic::GeneratorPrototype, g_proto);
    function_family(vm, "GeneratorFunction", gf_proto, generator_function)?;
    // §27.3.3.2† `%GeneratorFunction.prototype%.prototype` and §27.5.1.1†
    // `%GeneratorPrototype%.constructor`: { [[Writable]]: false,
    // [[Enumerable]]: false, [[Configurable]]: true }.
    define(vm, gf_proto, "prototype", g_proto, CONFIGURABLE_ONLY)?;
    define(vm, g_proto, "constructor", gf_proto, CONFIGURABLE_ONLY)?;
    method(vm, g_proto, "next", 1, generator_next)?;
    method(vm, g_proto, "return", 1, generator_return)?;
    method(vm, g_proto, "throw", 1, generator_throw)?;
    // §27.5.1.5† `%GeneratorPrototype% [ @@toStringTag ]` is "Generator".
    to_string_tag(vm, g_proto, "Generator")?;

    // §27.7.3† %AsyncFunction.prototype%.
    let af_proto = new_object_with(vm, function_proto, ObjKind::Plain)?;
    vm.set_intrinsic(Intrinsic::AsyncFunctionPrototype, af_proto);
    function_family(vm, "AsyncFunction", af_proto, async_function)?;

    // §27.1.3† %AsyncIteratorPrototype%, with `[ @@asyncIterator ] ( )`
    // (§27.1.3.1†): "1. Return the this value."; its `name` is
    // "[Symbol.asyncIterator]".
    let ai_proto = new_object_with(vm, object_proto, ObjKind::Plain)?;
    let f = vm.new_native("[Symbol.asyncIterator]", 0, return_this)?;
    let k = vm.well_known_key(wk::ASYNC_ITERATOR)?;
    vm.heap_mut().define(ai_proto, k, f, crate::util::METHOD)?;

    // §27.4.3† %AsyncGeneratorFunction.prototype% and §27.6.1†
    // %AsyncGeneratorPrototype%.
    let agf_proto = new_object_with(vm, function_proto, ObjKind::Plain)?;
    let ag_proto = new_object_with(vm, ai_proto, ObjKind::Plain)?;
    vm.set_intrinsic(Intrinsic::AsyncGeneratorFunctionPrototype, agf_proto);
    vm.set_intrinsic(Intrinsic::AsyncGeneratorPrototype, ag_proto);
    function_family(
        vm,
        "AsyncGeneratorFunction",
        agf_proto,
        async_generator_function,
    )?;
    // §27.4.3.2† and §27.6.1.1†, as for generators.
    define(vm, agf_proto, "prototype", ag_proto, CONFIGURABLE_ONLY)?;
    define(vm, ag_proto, "constructor", agf_proto, CONFIGURABLE_ONLY)?;
    method(vm, ag_proto, "next", 1, async_generator_next)?;
    method(vm, ag_proto, "return", 1, async_generator_return)?;
    method(vm, ag_proto, "throw", 1, async_generator_throw)?;
    // §27.6.1.5† `[ @@toStringTag ]` is "AsyncGenerator".
    to_string_tag(vm, ag_proto, "AsyncGenerator")?;

    // §27.1.6.2† %AsyncFromSyncIteratorPrototype%: [[Prototype]]
    // %AsyncIteratorPrototype%; not reachable by scripts.
    let afs_proto = new_object_with(vm, ai_proto, ObjKind::Plain)?;
    vm.set_intrinsic(Intrinsic::AsyncFromSyncIteratorPrototype, afs_proto);
    method(vm, afs_proto, "next", 1, from_sync_next)?;
    method(vm, afs_proto, "return", 1, from_sync_return)?;
    method(vm, afs_proto, "throw", 1, from_sync_throw)?;
    Ok(())
}

/// The constructor of a function kind and its links (§27.3.1†, §27.3.2†,
/// §27.3.3.1†, and the same clauses of §27.4† and §27.7†):
/// - the constructor `name` (`length` 1), whose [[Prototype]] is `%Function%`
///   and whose `prototype` is `proto` ({ [[Writable]]: false, [[Enumerable]]:
///   false, [[Configurable]]: false });
/// - `proto.constructor` is the constructor ({ [[Writable]]: false,
///   [[Configurable]]: true });
/// - `proto[@@toStringTag]` is `name`.
///
/// None of them is a global property.
fn function_family(
    vm: &mut Vm,
    name: &str,
    proto: Value,
    f: clazel_js_vm::interp::NativeFn,
) -> Result<(), Abrupt> {
    let ctor = vm.new_native_constructor(name, 1, f)?;
    let g = vm.global();
    let function = vm.get_named(g, "Function")?;
    if vm.heap().is_object(function) {
        vm.heap_mut().set_proto(ctor, function)?;
    }
    define(vm, ctor, "prototype", proto, CONSTANT)?;
    define(vm, proto, "constructor", ctor, CONFIGURABLE_ONLY)?;
    to_string_tag(vm, proto, name)
}

/// `GeneratorFunction ( ...parameterArgs, bodyArg )`, §27.3.1.1†:
/// CreateDynamicFunction, which needs the compiler at run time; not yet.
fn generator_function(_vm: &mut Vm, _this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    Err(Abrupt::NotYet(
        "the GeneratorFunction constructor (CreateDynamicFunction needs the compiler)".into(),
    ))
}

/// `AsyncFunction ( ...parameterArgs, bodyArg )`, §27.7.1.1†: as
/// `GeneratorFunction`.
fn async_function(_vm: &mut Vm, _this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    Err(Abrupt::NotYet(
        "the AsyncFunction constructor (CreateDynamicFunction needs the compiler)".into(),
    ))
}

/// `AsyncGeneratorFunction ( ...parameterArgs, bodyArg )`, §27.4.1.1†: as
/// `GeneratorFunction`.
fn async_generator_function(_vm: &mut Vm, _this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    Err(Abrupt::NotYet(
        "the AsyncGeneratorFunction constructor (CreateDynamicFunction needs the compiler)".into(),
    ))
}

/// `%AsyncIteratorPrototype% [ @@asyncIterator ] ( )`, §27.1.3.1†.
fn return_this(_vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    Ok(this)
}

// -----------------------------------------------------------------------
// %GeneratorPrototype%
// -----------------------------------------------------------------------

/// `%GeneratorPrototype%.next ( value )`, §27.5.1.2†:
/// 1. Return ? GeneratorResume(this value, value, empty).
fn generator_next(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    vm.generator_resume(this, arg(args, 0), ResumeMode::Next)
}

/// `%GeneratorPrototype%.return ( value )`, §27.5.1.3†:
/// 1. Let g be the this value.
/// 2. Let C be Completion Record { [[Type]]: return, [[Value]]: value,
///    [[Target]]: empty }.
/// 3. Return ? GeneratorResumeAbrupt(g, C, empty).
fn generator_return(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    vm.generator_resume(this, arg(args, 0), ResumeMode::Return)
}

/// `%GeneratorPrototype%.throw ( exception )`, §27.5.1.4†:
/// 1. Let g be the this value.
/// 2. Let C be ThrowCompletion(exception).
/// 3. Return ? GeneratorResumeAbrupt(g, C, empty).
fn generator_throw(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    vm.generator_resume(this, arg(args, 0), ResumeMode::Throw)
}

// -----------------------------------------------------------------------
// %AsyncGeneratorPrototype%
// -----------------------------------------------------------------------

/// `%AsyncGeneratorPrototype%.next ( value )`, §27.6.1.2† (the steps are
/// quoted at `Vm::async_generator_request`).
fn async_generator_next(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    vm.async_generator_request(this, arg(args, 0), ResumeMode::Next)
}

/// `%AsyncGeneratorPrototype%.return ( value )`, §27.6.1.3†.
fn async_generator_return(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    vm.async_generator_request(this, arg(args, 0), ResumeMode::Return)
}

/// `%AsyncGeneratorPrototype%.throw ( exception )`, §27.6.1.4†.
fn async_generator_throw(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    vm.async_generator_request(this, arg(args, 0), ResumeMode::Throw)
}

// -----------------------------------------------------------------------
// %AsyncFromSyncIteratorPrototype%
// -----------------------------------------------------------------------

/// A capability of `%Promise%`.
fn capability(vm: &mut Vm) -> Result<Cap, Abrupt> {
    let c = vm.intrinsic(Intrinsic::PromiseConstructor);
    new_promise_capability(vm, c)
}

/// IfAbruptRejectPromise ( value, capability ), §27.2.1.1.1†: a throw
/// rejects the capability's promise, which is the result; any other abrupt
/// completion goes on.
fn reject_with(vm: &mut Vm, cap: Cap, e: Abrupt) -> Result<Value, Abrupt> {
    let v = caught(e)?;
    vm.call(cap.reject, Value::UNDEFINED, &[v])?;
    Ok(cap.promise)
}

/// The `[[SyncIteratorRecord]]` of an Async-from-Sync Iterator: the iterator
/// and its `next` method.
fn sync_record(vm: &Vm, o: Value) -> Result<(Value, Value), Abrupt> {
    if vm.host_tag(o) != Some(TAG_ASYNC_FROM_SYNC) {
        return Err(Abrupt::Internal("not an Async-from-Sync Iterator"));
    }
    match (vm.host_slot(o, 0), vm.host_slot(o, 1)) {
        (Some(i), Some(n)) => Ok((i, n)),
        _ => Err(Abrupt::Internal("Async-from-Sync Iterator slots")),
    }
}

/// GetMethod ( V, P ), §7.3.10†, on the sync iterator: `None` for undefined
/// and null.
fn get_method(vm: &mut Vm, o: Value, name: &str) -> Result<Option<Value>, Abrupt> {
    let m = crate::util::get(vm, o, name)?;
    if m == Value::UNDEFINED || m == Value::NULL {
        return Ok(None);
    }
    if !vm.heap().is_callable(m) {
        return Err(vm.type_error(&format!("iterator.{name} is not a function")));
    }
    Ok(Some(m))
}

/// `%AsyncFromSyncIteratorPrototype%.next ( [ value ] )`, §27.1.6.2.1†:
/// 1. Let O be the this value.
/// 2. Assert: O is an Object that has a [[SyncIteratorRecord]] internal slot.
/// 3. Let promiseCapability be ! NewPromiseCapability(%Promise%).
/// 4. Let syncIteratorRecord be O.[[SyncIteratorRecord]].
/// 5. If value is present, then
///    a. Let result be Completion(IteratorNext(syncIteratorRecord, value)).
/// 6. Else,
///    a. Let result be Completion(IteratorNext(syncIteratorRecord)).
/// 7. IfAbruptRejectPromise(result, promiseCapability).
/// 8. Return AsyncFromSyncIteratorContinuation(result, promiseCapability,
///    syncIteratorRecord, true).
///
/// IteratorNext §7.4.6†: the call, and "If result is not an Object, throw a
/// TypeError exception".
fn from_sync_next(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let cap = capability(vm)?;
    let (iterator, next) = sync_record(vm, this)?;
    let present: &[Value] = args.get(..1).unwrap_or(&[]);
    let result = if vm.heap().is_callable(next) {
        vm.call(next, iterator, present)
    } else {
        Err(vm.type_error("iterator.next is not a function"))
    };
    let result = match result {
        Ok(r) if vm.heap().is_object(r) => r,
        Ok(_) => {
            let e = vm.type_error("Iterator result is not an object");
            return reject_with(vm, cap, e);
        }
        Err(e) => return reject_with(vm, cap, e),
    };
    continuation(vm, result, cap, iterator, true)
}

/// `%AsyncFromSyncIteratorPrototype%.return ( [ value ] )`, §27.1.6.2.2†:
/// 3. Let promiseCapability be ! NewPromiseCapability(%Promise%).
/// 4. Let syncIteratorRecord be O.[[SyncIteratorRecord]].
/// 5. Let syncIterator be syncIteratorRecord.[[Iterator]].
/// 6. Let return be Completion(GetMethod(syncIterator, "return")).
/// 7. IfAbruptRejectPromise(return, promiseCapability).
/// 8. If return is undefined, then
///    a. Let iteratorResult be CreateIterResultObject(value, true).
///    b. Perform ! Call(promiseCapability.[[Resolve]], undefined, «
///    iteratorResult »).
///    c. Return promiseCapability.[[Promise]].
/// 9. If value is present, then
///    a. Let result be Completion(Call(return, syncIterator, « value »)).
/// 10. Else,
///     a. Let result be Completion(Call(return, syncIterator)).
/// 11. IfAbruptRejectPromise(result, promiseCapability).
/// 12. If result is not an Object, then
///     a. Perform ! Call(promiseCapability.[[Reject]], undefined, « a newly
///     created TypeError object »).
///     b. Return promiseCapability.[[Promise]].
/// 13. Return AsyncFromSyncIteratorContinuation(result, promiseCapability,
///     syncIteratorRecord, false).
fn from_sync_return(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let cap = capability(vm)?;
    let (iterator, _) = sync_record(vm, this)?;
    let ret = match get_method(vm, iterator, "return") {
        Ok(m) => m,
        Err(e) => return reject_with(vm, cap, e),
    };
    let Some(ret) = ret else {
        let r = crate::iterator::iter_result(vm, arg(args, 0), true)?;
        vm.call(cap.resolve, Value::UNDEFINED, &[r])?;
        return Ok(cap.promise);
    };
    let present: &[Value] = args.get(..1).unwrap_or(&[]);
    let result = match vm.call(ret, iterator, present) {
        Ok(r) => r,
        Err(e) => return reject_with(vm, cap, e),
    };
    if !vm.heap().is_object(result) {
        let e = vm.type_error("iterator.return result is not an object");
        return reject_with(vm, cap, e);
    }
    continuation(vm, result, cap, iterator, false)
}

/// `%AsyncFromSyncIteratorPrototype%.throw ( [ value ] )`, §27.1.6.2.3†:
/// 5. Let syncIterator be syncIteratorRecord.[[Iterator]].
/// 6. Let throw be Completion(GetMethod(syncIterator, "throw")).
/// 7. IfAbruptRejectPromise(throw, promiseCapability).
/// 8. If throw is undefined, then
///    a. NOTE: If syncIterator does not have a throw method, close it to
///    give it a chance to clean up before we reject the capability.
///    b. Let closeCompletion be NormalCompletion(empty).
///    c. Let result be Completion(IteratorClose(syncIteratorRecord,
///    closeCompletion)).
///    d. IfAbruptRejectPromise(result, promiseCapability).
///    e.-f. (Notes.)
///    g. Perform ! Call(promiseCapability.[[Reject]], undefined, « a newly
///    created TypeError object »).
///    h. Return promiseCapability.[[Promise]].
/// 9. If value is present, then
///    a. Let result be Completion(Call(throw, syncIterator, « value »)).
/// 10. Else,
///     a. Let result be Completion(Call(throw, syncIterator)).
/// 11. IfAbruptRejectPromise(result, promiseCapability).
/// 12. If result is not an Object, then
///     a. Perform ! Call(promiseCapability.[[Reject]], undefined, « a newly
///     created TypeError object »).
///     b. Return promiseCapability.[[Promise]].
/// 13. Return AsyncFromSyncIteratorContinuation(result, promiseCapability,
///     syncIteratorRecord, true).
fn from_sync_throw(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let cap = capability(vm)?;
    let (iterator, next) = sync_record(vm, this)?;
    let throw = match get_method(vm, iterator, "throw") {
        Ok(m) => m,
        Err(e) => return reject_with(vm, cap, e),
    };
    let Some(throw) = throw else {
        let record = vm.new_iterator_record(iterator, next)?;
        if let Err(e) = vm.iterator_close(record) {
            return reject_with(vm, cap, e);
        }
        let e = vm.type_error("The iterator does not provide a 'throw' method");
        return reject_with(vm, cap, e);
    };
    let present: &[Value] = args.get(..1).unwrap_or(&[]);
    let result = match vm.call(throw, iterator, present) {
        Ok(r) => r,
        Err(e) => return reject_with(vm, cap, e),
    };
    if !vm.heap().is_object(result) {
        let e = vm.type_error("iterator.throw result is not an object");
        return reject_with(vm, cap, e);
    }
    continuation(vm, result, cap, iterator, true)
}

/// AsyncFromSyncIteratorContinuation ( result, promiseCapability,
/// syncIteratorRecord, closeOnRejection ), §27.1.6.4†:
/// 1. NOTE: ...
/// 2. Let done be Completion(IteratorComplete(result)).
/// 3. IfAbruptRejectPromise(done, promiseCapability).
/// 4. Let value be Completion(IteratorValue(result)).
/// 5. IfAbruptRejectPromise(value, promiseCapability).
/// 6. Let valueWrapper be Completion(PromiseResolve(%Promise%, value)).
/// 7. If valueWrapper is an abrupt completion, done is false, and
///    closeOnRejection is true, then
///    a. Set valueWrapper to Completion(IteratorClose(syncIteratorRecord,
///    valueWrapper)).
/// 8. IfAbruptRejectPromise(valueWrapper, promiseCapability).
/// 9. Let unwrap be a new Abstract Closure with parameters (v) that captures
///    done and performs the following steps when called:
///    a. Return CreateIterResultObject(v, done).
/// 10. Let onFulfilled be CreateBuiltinFunction(unwrap, 1, "", « »).
/// 11. NOTE: ...
/// 12. If done is true, or if closeOnRejection is false, then
///     a. Let onRejected be undefined.
/// 13. Else,
///     a. Let closeIterator be a new Abstract Closure with parameters (error)
///     that captures syncIteratorRecord and performs the following steps
///     when called:
///     i. Return ? IteratorClose(syncIteratorRecord,
///     ThrowCompletion(error)).
///     b. Let onRejected be CreateBuiltinFunction(closeIterator, 1, "", « »).
///     c. NOTE: ...
/// 14. Perform PerformPromiseThen(valueWrapper, onFulfilled, onRejected,
///     promiseCapability).
/// 15. Return promiseCapability.[[Promise]].
fn continuation(
    vm: &mut Vm,
    result: Value,
    cap: Cap,
    iterator: Value,
    close_on_rejection: bool,
) -> Result<Value, Abrupt> {
    let done = match crate::util::get(vm, result, "done") {
        Ok(d) => vm.to_boolean(d),
        Err(e) => return reject_with(vm, cap, e),
    };
    let value = match crate::util::get(vm, result, "value") {
        Ok(v) => v,
        Err(e) => return reject_with(vm, cap, e),
    };
    let c = vm.intrinsic(Intrinsic::PromiseConstructor);
    let wrapper = match promise_resolve(vm, c, value) {
        Ok(w) => w,
        Err(e) => {
            let e = if !done && close_on_rejection {
                let record = vm.new_iterator_record(iterator, Value::UNDEFINED)?;
                vm.iterator_close_on_throw(record, e)
            } else {
                e
            };
            return reject_with(vm, cap, e);
        }
    };
    let on_fulfilled = vm.new_native("", 1, unwrap)?;
    vm.set_function_slots(on_fulfilled, vec![Value::boolean(done)]);
    let on_rejected = if done || !close_on_rejection {
        Value::UNDEFINED
    } else {
        let f = vm.new_native("", 1, close_iterator)?;
        vm.set_function_slots(f, vec![iterator]);
        f
    };
    perform_promise_then(vm, wrapper, on_fulfilled, on_rejected, Some(cap))
}

/// The `unwrap` closure of §27.1.6.4† step 9: "a. Return
/// CreateIterResultObject(v, done)."
fn unwrap(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let done = vm.function_slot(0) == Some(Value::TRUE);
    crate::iterator::iter_result(vm, arg(args, 0), done)
}

/// The `closeIterator` closure of §27.1.6.4† step 13.a: "i. Return ?
/// IteratorClose(syncIteratorRecord, ThrowCompletion(error))."
fn close_iterator(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let iterator = vm
        .function_slot(0)
        .ok_or(Abrupt::Internal("closeIterator without its iterator"))?;
    let record = vm.new_iterator_record(iterator, Value::UNDEFINED)?;
    Err(vm.iterator_close_on_throw(record, Abrupt::Throw(arg(args, 0))))
}
