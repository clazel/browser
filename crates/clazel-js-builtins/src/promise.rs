//! `Promise` (§27.2†) and the job queue it runs on (§9.5†): the constructor,
//! `Promise.all`, `allSettled`, `any`, `race`, `reject`, `resolve`,
//! `withResolvers` and `try`, and `Promise.prototype.then`, `catch`,
//! `finally`, `@@toStringTag`.
//!
//! The queue is the VM's ([`Vm::enqueue_job`], [`Vm::run_jobs`]): a job is a
//! built-in function and its arguments. HostEnqueuePromiseJob (§9.5.5†)
//! appends to it, and the embedder runs it at its microtask checkpoint; this
//! crate never runs it by itself, as no standard says when the JS stack is
//! empty.
//!
//! # Modelling choices
//!
//! - **Internal slots.** A Promise is a host object ([`Vm::new_host_object`])
//!   whose slots are `[[PromiseState]]` (0 pending, 1 fulfilled, 2 rejected),
//!   `[[PromiseResult]]`, `[[PromiseFulfillReactions]]`,
//!   `[[PromiseRejectReactions]]` and `[[PromiseIsHandled]]`. The two reaction
//!   Lists are chains of reaction records (host objects too) linked newest
//!   first, reversed when triggered, so appending is O(1) and the order of
//!   TriggerPromiseReactions (§27.2.1.8†) is the order of `then` calls.
//! - **Abstract closures** are native functions with slots
//!   ([`Vm::set_function_slots`]): the resolving functions (§27.2.1.3†), the
//!   capability executor (§27.2.1.5.1†), the `all`, `allSettled` and `any`
//!   element functions and the functions of `finally`.
//! - **Capabilities** are plain Rust records (`Cap`) once made; the
//!   reaction records hold their three fields in slots.
//!
//! # Differences from the standard, all listed
//!
//! - **HostPromiseRejectionTracker** (§27.2.1.9†) is not called: no host
//!   exists yet that wants it.
//! - **HostMakeJobCallback and HostCallJobCallback** (§9.5.3†, §9.5.4†) are
//!   the default implementations: the callback is the function.

use crate::symbol::to_string_tag;
use crate::util::{
    arg, caught, constructor, define, get, invoke, method, new_object_with, species_constructor,
};
use clazel_js_heap::symbol as wk;
use clazel_js_heap::value::Value;
use clazel_js_vm::heap::ObjKind;
use clazel_js_vm::interp::{Abrupt, Intrinsic, Vm};
use clazel_js_vm::suspend::{Capability, PromiseOps};

/// The tags of this module's host objects.
const TAG_PROMISE: u32 = 0x5001;
const TAG_REACTION: u32 = 0x5002;
const TAG_RECORD: u32 = 0x5003;
const TAG_CAPABILITY: u32 = 0x5004;
const TAG_COUNTER: u32 = 0x5005;
const TAG_LIST: u32 = 0x5006;

/// Slots of a Promise.
const P_STATE: usize = 0;
const P_RESULT: usize = 1;
const P_FULFILL: usize = 2;
const P_REJECT: usize = 3;
const P_HANDLED: usize = 4;

/// Slots of a PromiseReaction record: the next (older) one in its chain, the
/// three fields of `[[Capability]]` (`undefined` if there is none), the type
/// (0 Fulfill, 1 Reject) and `[[Handler]]` (`undefined` for empty).
const R_NEXT: usize = 0;
const R_PROMISE: usize = 1;
const R_RESOLVE: usize = 2;
const R_REJECT: usize = 3;
const R_KIND: usize = 4;
const R_HANDLER: usize = 5;

/// `[[PromiseState]]` values.
const PENDING: i32 = 0;
const FULFILLED: i32 = 1;
const REJECTED: i32 = 2;

/// A PromiseCapability Record (§27.2.1.1†).
#[derive(Clone, Copy)]
pub(crate) struct Cap {
    pub(crate) promise: Value,
    pub(crate) resolve: Value,
    pub(crate) reject: Value,
}

/// The state of a Promise, as an embedder sees it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum State {
    /// `[[PromiseState]]` pending.
    Pending,
    /// Fulfilled.
    Fulfilled,
    /// Rejected.
    Rejected,
}

/// The state and result of a Promise, or `None` if `v` is not one.
#[must_use]
pub fn state_of(vm: &Vm, v: Value) -> Option<(State, Value)> {
    if vm.host_tag(v) != Some(TAG_PROMISE) {
        return None;
    }
    let st = match vm.host_slot(v, P_STATE).and_then(crate::util::as_number)? as i32 {
        FULFILLED => State::Fulfilled,
        REJECTED => State::Rejected,
        _ => State::Pending,
    };
    Some((st, vm.host_slot(v, P_RESULT)?))
}

/// Installs `Promise`, its prototype and the two job functions.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    let object_proto = vm.intrinsic(Intrinsic::ObjectPrototype);
    let proto = new_object_with(vm, object_proto, ObjKind::Plain)?;
    vm.set_intrinsic(Intrinsic::PromisePrototype, proto);
    let ctor = constructor(vm, "Promise", 1, promise_constructor, proto)?;
    vm.set_intrinsic(Intrinsic::PromiseConstructor, ctor);
    method(vm, ctor, "all", 1, all)?;
    method(vm, ctor, "allSettled", 1, all_settled)?;
    method(vm, ctor, "any", 1, any)?;
    method(vm, ctor, "race", 1, race)?;
    method(vm, ctor, "reject", 1, reject)?;
    method(vm, ctor, "resolve", 1, resolve)?;
    method(vm, ctor, "try", 1, try_fn)?;
    method(vm, ctor, "withResolvers", 0, with_resolvers)?;
    // §27.2.4.9†: `get Promise [ @@species ]` returns the this value.
    let ks = vm.well_known_key(wk::SPECIES)?;
    crate::util::accessor(vm, ctor, ks, "[Symbol.species]", Some(get_species), None)?;
    method(vm, proto, "catch", 1, catch)?;
    method(vm, proto, "finally", 1, finally)?;
    method(vm, proto, "then", 2, then)?;
    to_string_tag(vm, proto, "Promise")?;
    let job = vm.new_native("", 2, promise_reaction_job)?;
    vm.set_intrinsic(Intrinsic::PromiseReactionJob, job);
    let job = vm.new_native("", 3, promise_resolve_thenable_job)?;
    vm.set_intrinsic(Intrinsic::PromiseResolveThenableJob, job);
    vm.set_promise_ops(PromiseOps {
        new_capability: ops_new_capability,
        resolve: ops_resolve,
        then: ops_then,
    });
    crate::util::global(vm, "Promise", ctor)
}

/// NewPromiseCapability(%Promise%), for `await` and async functions
/// ([`PromiseOps`]).
fn ops_new_capability(vm: &mut Vm) -> Result<Capability, Abrupt> {
    let c = vm.intrinsic(Intrinsic::PromiseConstructor);
    let cap = new_promise_capability(vm, c)?;
    Ok((cap.promise, cap.resolve, cap.reject))
}

/// PromiseResolve(%Promise%, x), for `await` ([`PromiseOps`]).
fn ops_resolve(vm: &mut Vm, x: Value) -> Result<Value, Abrupt> {
    let c = vm.intrinsic(Intrinsic::PromiseConstructor);
    promise_resolve(vm, c, x)
}

/// PerformPromiseThen(promise, onFulfilled, onRejected), for `await`
/// ([`PromiseOps`]).
fn ops_then(vm: &mut Vm, p: Value, f: Value, r: Value) -> Result<(), Abrupt> {
    perform_promise_then(vm, p, f, r, None).map(|_| ())
}

// -----------------------------------------------------------------------
// Internal-slot helpers
// -----------------------------------------------------------------------

/// An object only the built-ins reach: null prototype, internal slots.
fn host(vm: &mut Vm, tag: u32, slots: Vec<Value>) -> Result<Value, Abrupt> {
    vm.new_host_object(Value::NULL, tag, slots, None)
}

fn slot(vm: &Vm, obj: Value, i: usize) -> Result<Value, Abrupt> {
    vm.host_slot(obj, i)
        .ok_or(Abrupt::Internal("promise internal slot"))
}

fn set_slot(vm: &mut Vm, obj: Value, i: usize, v: Value) -> Result<(), Abrupt> {
    if vm.set_host_slot(obj, i, v) {
        Ok(())
    } else {
        Err(Abrupt::Internal("promise internal slot"))
    }
}

/// Slot `i` of the running function.
fn fslot(vm: &Vm, i: usize) -> Result<Value, Abrupt> {
    vm.function_slot(i).ok_or(Abrupt::Internal("function slot"))
}

fn int_of(v: Value) -> i32 {
    crate::util::as_number(v).map_or(0, |d| d as i32)
}

/// A counter record: adds `delta` and returns the new value.
fn counter_add(vm: &mut Vm, rec: Value, delta: i32) -> Result<i32, Abrupt> {
    let n = int_of(slot(vm, rec, 0)?)
        .checked_add(delta)
        .ok_or(Abrupt::Internal("counter overflow"))?;
    set_slot(vm, rec, 0, Value::int32(n))?;
    Ok(n)
}

/// IsPromise ( x ), §27.2.1.2†.
fn is_promise(vm: &Vm, v: Value) -> bool {
    vm.host_tag(v) == Some(TAG_PROMISE)
}

fn type_error_value(vm: &mut Vm, msg: &str) -> Result<Value, Abrupt> {
    caught(vm.type_error(msg))
}

// -----------------------------------------------------------------------
// §27.2.1 Promise abstract operations
// -----------------------------------------------------------------------

/// CreateResolvingFunctions ( promise ), §27.2.1.3†:
/// 1. Let alreadyResolved be the Record { [[Value]]: false }.
/// 2. Let `resolve` be a built-in function of length 1 with [[Promise]] and
///    [[AlreadyResolved]] whose steps are `resolve_function`'s (steps 2 to 4).
/// 3. Let `reject` likewise, with `reject_function`'s steps (steps 5 to 8).
/// 4. Return the Record { [[Resolve]]: resolve, [[Reject]]: reject }.
fn create_resolving_functions(vm: &mut Vm, promise: Value) -> Result<(Value, Value), Abrupt> {
    let record = host(vm, TAG_RECORD, vec![Value::FALSE])?;
    let res = vm.new_native("", 1, resolve_function)?;
    vm.set_function_slots(res, vec![promise, record]);
    let rej = vm.new_native("", 1, reject_function)?;
    vm.set_function_slots(rej, vec![promise, record]);
    Ok((res, rej))
}

/// Takes the right to resolve: step 5 and 6 of the resolving functions.
fn take_already_resolved(vm: &mut Vm, record: Value) -> Result<bool, Abrupt> {
    if slot(vm, record, 0)? == Value::TRUE {
        return Ok(false);
    }
    set_slot(vm, record, 0, Value::TRUE)?;
    Ok(true)
}

/// Promise Resolve Functions, §27.2.1.3.2†:
/// 1. Let F be the active function object.
/// 2. Assert: F has a [[Promise]] internal slot.
/// 3. Let promise be F.[[Promise]].
/// 4. Let alreadyResolved be F.[[AlreadyResolved]].
/// 5. If alreadyResolved.[[Value]] is true, return undefined.
/// 6. Set alreadyResolved.[[Value]] to true.
/// 7. If SameValue(resolution, promise) is true, then
///    a. Let selfResolutionError be a newly created TypeError object.
///    b. Perform RejectPromise(promise, selfResolutionError).
///    c. Return undefined.
/// 8. If resolution is not an Object, then
///    a. Perform FulfillPromise(promise, resolution).
///    b. Return undefined.
/// 9. Let then be Completion(Get(resolution, "then")).
/// 10. If then is an abrupt completion, then
///     a. Perform RejectPromise(promise, then.[[Value]]).
///     b. Return undefined.
/// 11. Let thenAction be then.[[Value]].
/// 12. If IsCallable(thenAction) is false, then
///     a. Perform FulfillPromise(promise, resolution).
///     b. Return undefined.
/// 13. Let thenJobCallback be HostMakeJobCallback(thenAction).
/// 14. Let job be NewPromiseResolveThenableJob(promise, resolution,
///     thenJobCallback).
/// 15. Perform HostEnqueuePromiseJob(job.[[Job]], job.[[Realm]]).
/// 16. Return undefined.
fn resolve_function(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let (promise, record) = (fslot(vm, 0)?, fslot(vm, 1)?);
    if !take_already_resolved(vm, record)? {
        return Ok(Value::UNDEFINED);
    }
    let resolution = arg(args, 0);
    if resolution == promise {
        let e = type_error_value(vm, "Chaining cycle detected for promise")?;
        reject_promise(vm, promise, e)?;
        return Ok(Value::UNDEFINED);
    }
    if !vm.heap().is_object(resolution) {
        fulfill_promise(vm, promise, resolution)?;
        return Ok(Value::UNDEFINED);
    }
    let then = match get(vm, resolution, "then") {
        Ok(t) => t,
        Err(e) => {
            reject_promise(vm, promise, caught(e)?)?;
            return Ok(Value::UNDEFINED);
        }
    };
    if !vm.heap().is_callable(then) {
        fulfill_promise(vm, promise, resolution)?;
        return Ok(Value::UNDEFINED);
    }
    let job = vm.intrinsic(Intrinsic::PromiseResolveThenableJob);
    vm.enqueue_job(job, vec![promise, resolution, then]);
    Ok(Value::UNDEFINED)
}

/// Promise Reject Functions, §27.2.1.3.1†:
/// 1-4. As the resolve function.
/// 5. If alreadyResolved.[[Value]] is true, return undefined.
/// 6. Set alreadyResolved.[[Value]] to true.
/// 7. Perform RejectPromise(promise, reason).
/// 8. Return undefined.
fn reject_function(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let (promise, record) = (fslot(vm, 0)?, fslot(vm, 1)?);
    if take_already_resolved(vm, record)? {
        reject_promise(vm, promise, arg(args, 0))?;
    }
    Ok(Value::UNDEFINED)
}

/// FulfillPromise ( promise, value ), §27.2.1.4†:
/// 1. Assert: The value of promise.[[PromiseState]] is pending.
/// 2. Let reactions be promise.[[PromiseFulfillReactions]].
/// 3. Set promise.[[PromiseResult]] to value.
/// 4. Set promise.[[PromiseFulfillReactions]] to undefined.
/// 5. Set promise.[[PromiseRejectReactions]] to undefined.
/// 6. Set promise.[[PromiseState]] to fulfilled.
/// 7. Perform TriggerPromiseReactions(reactions, value).
/// 8. Return unused.
fn fulfill_promise(vm: &mut Vm, promise: Value, value: Value) -> Result<(), Abrupt> {
    settle(vm, promise, value, FULFILLED, P_FULFILL)
}

/// RejectPromise ( promise, reason ), §27.2.1.7†:
/// 1. Assert: The value of promise.[[PromiseState]] is pending.
/// 2. Let reactions be promise.[[PromiseRejectReactions]].
/// 3. Set promise.[[PromiseResult]] to reason.
/// 4. Set promise.[[PromiseFulfillReactions]] to undefined.
/// 5. Set promise.[[PromiseRejectReactions]] to undefined.
/// 6. Set promise.[[PromiseState]] to rejected.
/// 7. If promise.[[PromiseIsHandled]] is false, perform
///    HostPromiseRejectionTracker(promise, "reject") (not called: see the
///    module header).
/// 8. Perform TriggerPromiseReactions(reactions, reason).
/// 9. Return unused.
fn reject_promise(vm: &mut Vm, promise: Value, reason: Value) -> Result<(), Abrupt> {
    settle(vm, promise, reason, REJECTED, P_REJECT)
}

fn settle(
    vm: &mut Vm,
    promise: Value,
    value: Value,
    state: i32,
    which: usize,
) -> Result<(), Abrupt> {
    let reactions = slot(vm, promise, which)?;
    set_slot(vm, promise, P_RESULT, value)?;
    set_slot(vm, promise, P_FULFILL, Value::UNDEFINED)?;
    set_slot(vm, promise, P_REJECT, Value::UNDEFINED)?;
    set_slot(vm, promise, P_STATE, Value::int32(state))?;
    trigger_promise_reactions(vm, reactions, value)
}

/// TriggerPromiseReactions ( reactions, argument ), §27.2.1.8†:
/// 1. For each element reaction of reactions, do
///    a. Let job be NewPromiseReactionJob(reaction, argument).
///    b. Perform HostEnqueuePromiseJob(job.[[Job]], job.[[Realm]]).
/// 2. Return unused.
///
/// (`reactions` is the chain, newest first: it is walked and then run
/// oldest first.)
fn trigger_promise_reactions(vm: &mut Vm, head: Value, argument: Value) -> Result<(), Abrupt> {
    let mut chain = Vec::new();
    let mut cur = head;
    while cur != Value::UNDEFINED {
        chain.push(cur);
        cur = slot(vm, cur, R_NEXT)?;
    }
    let job = vm.intrinsic(Intrinsic::PromiseReactionJob);
    for reaction in chain.into_iter().rev() {
        vm.enqueue_job(job, vec![reaction, argument]);
    }
    Ok(())
}

/// NewPromiseReactionJob ( reaction, argument ), §27.2.2.1†, the job's steps:
/// 1. Let promiseCapability be reaction.[[Capability]].
/// 2. Let type be reaction.[[Type]].
/// 3. Let handler be reaction.[[Handler]].
/// 4. If handler is empty, then
///    a. If type is fulfill, let handlerResult be NormalCompletion(argument).
///    b. Else, let handlerResult be ThrowCompletion(argument).
/// 5. Else, let handlerResult be Completion(HostCallJobCallback(handler,
///    undefined, « argument »)).
/// 6. If promiseCapability is undefined, then
///    a. Assert: handlerResult is not an abrupt completion (here a throw
///    stays the job's exception).
///    b. Return unused.
/// 7. Assert: promiseCapability is a PromiseCapability Record.
/// 8. If handlerResult is an abrupt completion, then
///    a. Return ? Call(promiseCapability.[[Reject]], undefined, «
///    handlerResult.[[Value]] »).
/// 9. Else,
///    a. Return ? Call(promiseCapability.[[Resolve]], undefined, «
///    handlerResult.[[Value]] »).
fn promise_reaction_job(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let (reaction, argument) = (arg(args, 0), arg(args, 1));
    let handler = slot(vm, reaction, R_HANDLER)?;
    let kind = int_of(slot(vm, reaction, R_KIND)?);
    let result = if handler == Value::UNDEFINED {
        if kind == 0 {
            Ok(argument)
        } else {
            Err(Abrupt::Throw(argument))
        }
    } else {
        vm.call(handler, Value::UNDEFINED, &[argument])
    };
    let (promise, resolve, reject) = (
        slot(vm, reaction, R_PROMISE)?,
        slot(vm, reaction, R_RESOLVE)?,
        slot(vm, reaction, R_REJECT)?,
    );
    if promise == Value::UNDEFINED {
        return result.map(|_| Value::UNDEFINED);
    }
    match result {
        Ok(v) => vm.call(resolve, Value::UNDEFINED, &[v]),
        Err(Abrupt::Throw(e)) => vm.call(reject, Value::UNDEFINED, &[e]),
        Err(other) => Err(other),
    }
}

/// NewPromiseResolveThenableJob ( promiseToResolve, thenable, then ),
/// §27.2.2.2†, the job's steps:
/// 1. Let resolvingFunctions be CreateResolvingFunctions(promiseToResolve).
/// 2. Let thenCallResult be Completion(HostCallJobCallback(then, thenable, «
///    resolvingFunctions.[[Resolve]], resolvingFunctions.[[Reject]] »)).
/// 3. If thenCallResult is an abrupt completion, then
///    a. Return ? Call(resolvingFunctions.[[Reject]], undefined, «
///    thenCallResult.[[Value]] »).
/// 4. Return ? thenCallResult.
fn promise_resolve_thenable_job(
    vm: &mut Vm,
    _this: Value,
    args: &[Value],
) -> Result<Value, Abrupt> {
    let (promise, thenable, then) = (arg(args, 0), arg(args, 1), arg(args, 2));
    let (res, rej) = create_resolving_functions(vm, promise)?;
    match vm.call(then, thenable, &[res, rej]) {
        Ok(v) => Ok(v),
        Err(e) => {
            let v = caught(e)?;
            vm.call(rej, Value::UNDEFINED, &[v])
        }
    }
}

/// NewPromiseCapability ( C ), §27.2.1.5†:
/// 1. If IsConstructor(C) is false, throw a TypeError exception.
/// 2. NOTE: C is assumed to be a constructor function that supports the
///    parameter conventions of the Promise constructor.
/// 3. Let resolvingFunctions be the Record { [[Resolve]]: undefined,
///    [[Reject]]: undefined }.
/// 4. Let promiseCapability be the PromiseCapability Record { [[Promise]]:
///    undefined, [[Resolve]]: undefined, [[Reject]]: undefined }.
/// 5. Let executorClosure be a new Abstract Closure (GetCapabilitiesExecutor
///    Functions, §27.2.1.5.1†).
/// 6. Let executor be CreateBuiltinFunction(executorClosure, 2, "", « »).
/// 7. Let promise be ? Construct(C, « executor »).
/// 8. If IsCallable(resolvingFunctions.[[Resolve]]) is false, throw a
///    TypeError exception.
/// 9. If IsCallable(resolvingFunctions.[[Reject]]) is false, throw a
///    TypeError exception.
/// 10. Set promiseCapability.[[Promise]] to promise.
/// 11. Set promiseCapability.[[Resolve]] to resolvingFunctions.[[Resolve]].
/// 12. Set promiseCapability.[[Reject]] to resolvingFunctions.[[Reject]].
/// 13. Return promiseCapability.
pub(crate) fn new_promise_capability(vm: &mut Vm, c: Value) -> Result<Cap, Abrupt> {
    if !vm.is_constructor(c) {
        return Err(vm.type_error("Promise capability constructor is not a constructor"));
    }
    let fns = host(vm, TAG_CAPABILITY, vec![Value::UNDEFINED, Value::UNDEFINED])?;
    let executor = vm.new_native("", 2, capability_executor)?;
    vm.set_function_slots(executor, vec![fns]);
    let promise = vm.construct_value(c, &[executor])?;
    let (resolve, reject) = (slot(vm, fns, 0)?, slot(vm, fns, 1)?);
    if !vm.heap().is_callable(resolve) || !vm.heap().is_callable(reject) {
        return Err(vm.type_error("Promise resolve or reject function is not callable"));
    }
    Ok(Cap {
        promise,
        resolve,
        reject,
    })
}

/// GetCapabilitiesExecutor Functions, §27.2.1.5.1†:
/// 1. Let F be the active function object.
/// 2. Assert: F has a [[Capability]] internal slot whose value is a
///    PromiseCapability Record.
/// 3. Let promiseCapability be F.[[Capability]].
/// 4. If promiseCapability.[[Resolve]] is not undefined, throw a TypeError
///    exception.
/// 5. If promiseCapability.[[Reject]] is not undefined, throw a TypeError
///    exception.
/// 6. Set promiseCapability.[[Resolve]] to resolve.
/// 7. Set promiseCapability.[[Reject]] to reject.
/// 8. Return undefined.
fn capability_executor(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let fns = fslot(vm, 0)?;
    if slot(vm, fns, 0)? != Value::UNDEFINED || slot(vm, fns, 1)? != Value::UNDEFINED {
        return Err(vm.type_error("Promise executor has already been invoked"));
    }
    set_slot(vm, fns, 0, arg(args, 0))?;
    set_slot(vm, fns, 1, arg(args, 1))?;
    Ok(Value::UNDEFINED)
}

/// PerformPromiseThen ( promise, onFulfilled, onRejected [ ,
/// resultCapability ] ), §27.2.5.4.1†:
/// 1. Assert: IsPromise(promise) is true.
/// 2. If resultCapability is not present, then a. Set resultCapability to
///    undefined.
/// 3. If IsCallable(onFulfilled) is false, then a. Let onFulfilledJobCallback
///    be empty.
/// 4. Else, a. Let onFulfilledJobCallback be HostMakeJobCallback(onFulfilled).
/// 5. Likewise onRejectedJobCallback (steps 5 and 6).
/// 7. Let fulfillReaction be the PromiseReaction Record { [[Capability]]:
///    resultCapability, [[Type]]: fulfill, [[Handler]]: onFulfilledJobCallback
///    }.
/// 8. Let rejectReaction be likewise with reject.
/// 9. If promise.[[PromiseState]] is pending, then
///    a. Append fulfillReaction to promise.[[PromiseFulfillReactions]].
///    b. Append rejectReaction to promise.[[PromiseRejectReactions]].
/// 10. Else if promise.[[PromiseState]] is fulfilled, then
///     a. Let value be promise.[[PromiseResult]].
///     b. Let fulfillJob be NewPromiseReactionJob(fulfillReaction, value).
///     c. Perform HostEnqueuePromiseJob(fulfillJob.[[Job]],
///     fulfillJob.[[Realm]]).
/// 11. Else,
///     a. Assert: The value of promise.[[PromiseState]] is rejected.
///     b. Let reason be promise.[[PromiseResult]].
///     c. If promise.[[PromiseIsHandled]] is false, perform
///     HostPromiseRejectionTracker(promise, "handle").
///     d. Let rejectJob be NewPromiseReactionJob(rejectReaction, reason).
///     e. Perform HostEnqueuePromiseJob(rejectJob.[[Job]],
///     rejectJob.[[Realm]]).
/// 12. Set promise.[[PromiseIsHandled]] to true.
/// 13. If resultCapability is undefined, then a. Return undefined.
/// 14. Else, a. Return resultCapability.[[Promise]].
pub(crate) fn perform_promise_then(
    vm: &mut Vm,
    promise: Value,
    on_fulfilled: Value,
    on_rejected: Value,
    result: Option<Cap>,
) -> Result<Value, Abrupt> {
    let handler = |vm: &Vm, f: Value| {
        if vm.heap().is_callable(f) {
            f
        } else {
            Value::UNDEFINED
        }
    };
    let (hf, hr) = (handler(vm, on_fulfilled), handler(vm, on_rejected));
    let cap = result.unwrap_or(Cap {
        promise: Value::UNDEFINED,
        resolve: Value::UNDEFINED,
        reject: Value::UNDEFINED,
    });
    let make = |vm: &mut Vm, kind: i32, h: Value, next: Value| {
        host(
            vm,
            TAG_REACTION,
            vec![
                next,
                cap.promise,
                cap.resolve,
                cap.reject,
                Value::int32(kind),
                h,
            ],
        )
    };
    let (fulfill_head, reject_head) = (slot(vm, promise, P_FULFILL)?, slot(vm, promise, P_REJECT)?);
    let state = int_of(slot(vm, promise, P_STATE)?);
    let job = vm.intrinsic(Intrinsic::PromiseReactionJob);
    if state == PENDING {
        let fr = make(vm, 0, hf, fulfill_head)?;
        let rr = make(vm, 1, hr, reject_head)?;
        set_slot(vm, promise, P_FULFILL, fr)?;
        set_slot(vm, promise, P_REJECT, rr)?;
    } else {
        let value = slot(vm, promise, P_RESULT)?;
        let reaction = if state == FULFILLED {
            make(vm, 0, hf, Value::UNDEFINED)?
        } else {
            make(vm, 1, hr, Value::UNDEFINED)?
        };
        vm.enqueue_job(job, vec![reaction, value]);
    }
    set_slot(vm, promise, P_HANDLED, Value::TRUE)?;
    Ok(result.map_or(Value::UNDEFINED, |c| c.promise))
}

/// PromiseResolve ( C, x ), §27.2.4.7.1†:
/// 1. If IsPromise(x) is true, then
///    a. Let xConstructor be ? Get(x, "constructor").
///    b. If SameValue(xConstructor, C) is true, return x.
/// 2. Let promiseCapability be ? NewPromiseCapability(C).
/// 3. Perform ? Call(promiseCapability.[[Resolve]], undefined, « x »).
/// 4. Return promiseCapability.[[Promise]].
pub(crate) fn promise_resolve(vm: &mut Vm, c: Value, x: Value) -> Result<Value, Abrupt> {
    if is_promise(vm, x) {
        let x_constructor = get(vm, x, "constructor")?;
        if crate::util::same_value(vm, x_constructor, c) {
            return Ok(x);
        }
    }
    let cap = new_promise_capability(vm, c)?;
    vm.call(cap.resolve, Value::UNDEFINED, &[x])?;
    Ok(cap.promise)
}

// -----------------------------------------------------------------------
// §27.2.3 The constructor and its properties
// -----------------------------------------------------------------------

/// `Promise ( executor )`, §27.2.3.1†:
/// 1. If NewTarget is undefined, throw a TypeError exception.
/// 2. If IsCallable(executor) is false, throw a TypeError exception.
/// 3. Let promise be ? OrdinaryCreateFromConstructor(NewTarget,
///    "%Promise.prototype%", « [[PromiseState]], [[PromiseResult]],
///    [[PromiseFulfillReactions]], [[PromiseRejectReactions]],
///    [[PromiseIsHandled]] »).
/// 4. Set promise.[[PromiseState]] to pending.
/// 5. Set promise.[[PromiseFulfillReactions]] to a new empty List.
/// 6. Set promise.[[PromiseRejectReactions]] to a new empty List.
/// 7. Set promise.[[PromiseIsHandled]] to false.
/// 8. Let resolvingFunctions be CreateResolvingFunctions(promise).
/// 9. Let completion be Completion(Call(executor, undefined, «
///    resolvingFunctions.[[Resolve]], resolvingFunctions.[[Reject]] »)).
/// 10. If completion is an abrupt completion, then
///     a. Perform ? Call(resolvingFunctions.[[Reject]], undefined, «
///     completion.[[Value]] »).
/// 11. Return promise.
fn promise_constructor(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let nt = vm.new_target();
    if nt == Value::UNDEFINED {
        return Err(vm.type_error("Promise constructor cannot be invoked without 'new'"));
    }
    let executor = arg(args, 0);
    if !vm.heap().is_callable(executor) {
        return Err(vm.type_error("Promise resolver is not a function"));
    }
    let promise = vm.create_from_constructor(nt, Intrinsic::PromisePrototype, ObjKind::Plain)?;
    vm.into_host_object(
        promise,
        TAG_PROMISE,
        vec![
            Value::int32(PENDING),
            Value::UNDEFINED,
            Value::UNDEFINED,
            Value::UNDEFINED,
            Value::FALSE,
        ],
        None,
    )?;
    let (resolve, reject) = create_resolving_functions(vm, promise)?;
    if let Err(e) = vm.call(executor, Value::UNDEFINED, &[resolve, reject]) {
        let v = caught(e)?;
        vm.call(reject, Value::UNDEFINED, &[v])?;
    }
    Ok(promise)
}

/// IfAbruptRejectPromise ( value, capability ), §27.2.1.1.1†: for the abrupt
/// completion `e`: `Call(capability.[[Reject]], undefined, « value »)` and
/// return `capability.[[Promise]]`.
fn reject_with(vm: &mut Vm, cap: Cap, e: Abrupt) -> Result<Value, Abrupt> {
    let v = caught(e)?;
    vm.call(cap.reject, Value::UNDEFINED, &[v])?;
    Ok(cap.promise)
}

/// GetPromiseResolve ( promiseConstructor ), §27.2.4.1.1†:
/// 1. Let promiseResolve be ? Get(promiseConstructor, "resolve").
/// 2. If IsCallable(promiseResolve) is false, throw a TypeError exception.
/// 3. Return promiseResolve.
fn get_promise_resolve(vm: &mut Vm, c: Value) -> Result<Value, Abrupt> {
    let f = get(vm, c, "resolve")?;
    if !vm.heap().is_callable(f) {
        return Err(vm.type_error("Promise resolve is not a function"));
    }
    Ok(f)
}

/// Which of the four combinators runs.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Combinator {
    All,
    AllSettled,
    Any,
    Race,
}

/// The element functions' codes.
const ELEM_ALL: i32 = 0;
const ELEM_FULFILLED: i32 = 1;
const ELEM_REJECTED: i32 = 2;
const ELEM_ANY: i32 = 3;

/// `Promise.all ( iterable )`, §27.2.4.1†, `Promise.allSettled`, §27.2.4.2†,
/// `Promise.any`, §27.2.4.3† and `Promise.race`, §27.2.4.5†, whose first
/// steps are the same:
/// 1. Let C be the this value.
/// 2. Let promiseCapability be ? NewPromiseCapability(C).
/// 3. Let promiseResolve be Completion(GetPromiseResolve(C)).
/// 4. IfAbruptRejectPromise(promiseResolve, promiseCapability).
/// 5. Let iteratorRecord be Completion(GetIterator(iterable, sync)).
/// 6. IfAbruptRejectPromise(iteratorRecord, promiseCapability).
/// 7. Let result be Completion(PerformPromiseAll(iteratorRecord, C,
///    promiseCapability, promiseResolve)).
/// 8. If result is an abrupt completion, then
///    a. If iteratorRecord.[[Done]] is false, set result to
///    Completion(IteratorClose(iteratorRecord, result)).
///    b. IfAbruptRejectPromise(result, promiseCapability).
/// 9. Return ? result.
fn combinator(vm: &mut Vm, this: Value, args: &[Value], kind: Combinator) -> Result<Value, Abrupt> {
    let cap = new_promise_capability(vm, this)?;
    let promise_resolve = match get_promise_resolve(vm, this) {
        Ok(f) => f,
        Err(e) => return reject_with(vm, cap, e),
    };
    let record = match vm.get_iterator(arg(args, 0)) {
        Ok(r) => r,
        Err(e) => return reject_with(vm, cap, e),
    };
    match perform_combinator(vm, record, this, cap, promise_resolve, kind) {
        Ok(v) => Ok(v),
        Err(e) => {
            let e = if vm.iterator_done(record) {
                e
            } else {
                vm.iterator_close_on_throw(record, e)
            };
            reject_with(vm, cap, e)
        }
    }
}

/// PerformPromiseAll ( iteratorRecord, constructor, resultCapability,
/// promiseResolve ), §27.2.4.1.2†, and the matching operations of
/// `allSettled` (§27.2.4.2.1†), `any` (§27.2.4.3.1†) and `race`
/// (§27.2.4.5.1†):
/// 1. Let values be a new empty List.
/// 2. Let remainingElementsCount be the Record { [[Value]]: 1 }.
/// 3. Let index be 0.
/// 4. Repeat,
///    a. Let next be ? IteratorStepValue(iteratorRecord).
///    b. If next is done, then (i) set remainingElementsCount.[[Value]] to
///    remainingElementsCount.[[Value]] - 1; (ii) if it is 0, let valuesArray
///    be CreateArrayFromList(values) and perform ? Call(
///    resultCapability.[[Resolve]], undefined, « valuesArray ») (for `any`: a
///    newly created AggregateError with an `errors` property of the array,
///    and ? Call(resultCapability.[[Reject]], undefined, « error »)); (iii)
///    return resultCapability.[[Promise]].
///    c. Append undefined to values.
///    d. Let nextPromise be ? Call(promiseResolve, constructor, « next »).
///    e. Let onFulfilled be CreateBuiltinFunction(steps, 1, "", ...) with
///    [[AlreadyCalled]], [[Index]], [[Values]], [[Capability]],
///    [[RemainingElements]].
///    f. Set remainingElementsCount.[[Value]] to
///    remainingElementsCount.[[Value]] + 1.
///    g. Perform ? Invoke(nextPromise, "then", « onFulfilled,
///    resultCapability.[[Reject]] »).
///    h. Set index to index + 1.
///
/// (`race` has no values or count: step 4.b returns the promise, and 4.d and
/// 4.g invoke `then` with the capability's own resolve and reject.)
fn perform_combinator(
    vm: &mut Vm,
    record: Value,
    c: Value,
    cap: Cap,
    promise_resolve: Value,
    kind: Combinator,
) -> Result<Value, Abrupt> {
    let values = host(vm, TAG_LIST, Vec::new())?;
    let remaining = host(vm, TAG_COUNTER, vec![Value::int32(1)])?;
    let mut index: i32 = 0;
    loop {
        let Some(next) = vm.iterator_step_value(record)? else {
            if kind != Combinator::Race && counter_add(vm, remaining, -1)? == 0 {
                finish_combinator(vm, values, cap, kind)?;
            }
            return Ok(cap.promise);
        };
        if kind != Combinator::Race {
            vm.push_host_slot(values, Value::UNDEFINED);
        }
        let next_promise = vm.call(promise_resolve, c, &[next])?;
        let element = |vm: &mut Vm, code: i32, shared: Option<Value>| {
            element_function(vm, code, shared, index, values, cap, remaining)
        };
        let (on_fulfilled, on_rejected) = match kind {
            Combinator::All => (element(vm, ELEM_ALL, None)?, cap.reject),
            Combinator::AllSettled => {
                let shared = host(vm, TAG_RECORD, vec![Value::FALSE])?;
                (
                    element(vm, ELEM_FULFILLED, Some(shared))?,
                    element(vm, ELEM_REJECTED, Some(shared))?,
                )
            }
            Combinator::Any => (cap.resolve, element(vm, ELEM_ANY, None)?),
            Combinator::Race => (cap.resolve, cap.reject),
        };
        if kind != Combinator::Race {
            counter_add(vm, remaining, 1)?;
        }
        invoke(vm, next_promise, "then", &[on_fulfilled, on_rejected])?;
        index = index
            .checked_add(1)
            .ok_or(Abrupt::Internal("too many promises"))?;
    }
}

/// Step 4.b.ii of the combinators: the values are all in.
fn finish_combinator(vm: &mut Vm, values: Value, cap: Cap, kind: Combinator) -> Result<(), Abrupt> {
    let list: Vec<Value> = vm
        .host_slots(values)
        .map(<[Value]>::to_vec)
        .unwrap_or_default();
    let array = vm.create_array_from_list(&list)?;
    if kind == Combinator::Any {
        let error = aggregate_error(vm, array)?;
        vm.call(cap.reject, Value::UNDEFINED, &[error])?;
    } else {
        vm.call(cap.resolve, Value::UNDEFINED, &[array])?;
    }
    Ok(())
}

/// "A newly created AggregateError object" with its `errors` property
/// (§27.2.4.3.1† step 4.b.ii.2 and 3).
fn aggregate_error(vm: &mut Vm, errors: Value) -> Result<Value, Abrupt> {
    let proto = vm.intrinsic(Intrinsic::AggregateErrorPrototype);
    let e = new_object_with(vm, proto, ObjKind::Error)?;
    define(vm, e, "errors", errors, crate::util::METHOD)?;
    Ok(e)
}

/// One element function: the `Promise.all` Resolve Element Function
/// (§27.2.4.1.3†), the `allSettled` ones (§27.2.4.2.2†, §27.2.4.2.3†) and
/// the `any` Reject Element Function (§27.2.4.3.2†).
fn element_function(
    vm: &mut Vm,
    code: i32,
    shared: Option<Value>,
    index: i32,
    values: Value,
    cap: Cap,
    remaining: Value,
) -> Result<Value, Abrupt> {
    let already = match shared {
        Some(r) => r,
        None => host(vm, TAG_RECORD, vec![Value::FALSE])?,
    };
    let f = vm.new_native("", 1, element_steps)?;
    vm.set_function_slots(
        f,
        vec![
            Value::int32(code),
            already,
            Value::int32(index),
            values,
            cap.resolve,
            cap.reject,
            remaining,
        ],
    );
    Ok(f)
}

/// The steps of the element functions:
/// 1. Let F be the active function object.
/// 2. If F.[[AlreadyCalled]] is true, return undefined.
/// 3. Set F.[[AlreadyCalled]] to true.
/// 4. Let index be F.[[Index]].
/// 5. Let values be F.[[Values]].
/// 6. (allSettled: Let obj be OrdinaryObjectCreate(%Object.prototype%) with
///    `status` "fulfilled" and `value` x, or `status` "rejected" and `reason`
///    x.)
/// 7. Set values[index] to x (or obj).
/// 8. Let remainingElementsCount be F.[[RemainingElements]].
/// 9. Set remainingElementsCount.[[Value]] to
///    remainingElementsCount.[[Value]] - 1.
/// 10. If remainingElementsCount.[[Value]] = 0, then
///     a. Let valuesArray be CreateArrayFromList(values).
///     b. Return ? Call(promiseCapability.[[Resolve]], undefined, «
///     valuesArray »). (any: the AggregateError and [[Reject]].)
/// 11. Return undefined.
fn element_steps(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let code = int_of(fslot(vm, 0)?);
    let already = fslot(vm, 1)?;
    if !take_already_resolved(vm, already)? {
        return Ok(Value::UNDEFINED);
    }
    let index = usize::try_from(int_of(fslot(vm, 2)?)).map_err(|_| Abrupt::Internal("index"))?;
    let (values, resolve, reject, remaining) =
        (fslot(vm, 3)?, fslot(vm, 4)?, fslot(vm, 5)?, fslot(vm, 6)?);
    let x = arg(args, 0);
    let stored = match code {
        ELEM_FULFILLED | ELEM_REJECTED => {
            let obj = vm.new_object()?;
            let (status, field) = if code == ELEM_FULFILLED {
                ("fulfilled", "value")
            } else {
                ("rejected", "reason")
            };
            let s = vm.new_string(status)?;
            vm.define_property(obj, "status", s)?;
            vm.define_property(obj, field, x)?;
            obj
        }
        _ => x,
    };
    set_slot(vm, values, index, stored)?;
    if counter_add(vm, remaining, -1)? == 0 {
        let list: Vec<Value> = vm
            .host_slots(values)
            .map(<[Value]>::to_vec)
            .unwrap_or_default();
        let array = vm.create_array_from_list(&list)?;
        if code == ELEM_ANY {
            let error = aggregate_error(vm, array)?;
            return vm.call(reject, Value::UNDEFINED, &[error]);
        }
        return vm.call(resolve, Value::UNDEFINED, &[array]);
    }
    Ok(Value::UNDEFINED)
}

fn all(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    combinator(vm, this, args, Combinator::All)
}

fn all_settled(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    combinator(vm, this, args, Combinator::AllSettled)
}

fn any(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    combinator(vm, this, args, Combinator::Any)
}

fn race(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    combinator(vm, this, args, Combinator::Race)
}

/// `Promise.reject ( r )`, §27.2.4.6†:
/// 1. Let C be the this value.
/// 2. Let promiseCapability be ? NewPromiseCapability(C).
/// 3. Perform ? Call(promiseCapability.[[Reject]], undefined, « r »).
/// 4. Return promiseCapability.[[Promise]].
fn reject(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let cap = new_promise_capability(vm, this)?;
    vm.call(cap.reject, Value::UNDEFINED, &[arg(args, 0)])?;
    Ok(cap.promise)
}

/// `Promise.resolve ( x )`, §27.2.4.7†:
/// 1. Let C be the this value.
/// 2. If C is not an Object, throw a TypeError exception.
/// 3. Return ? PromiseResolve(C, x).
fn resolve(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    if !vm.heap().is_object(this) {
        return Err(vm.type_error("Promise.resolve called on a non-object"));
    }
    promise_resolve(vm, this, arg(args, 0))
}

/// `Promise.try ( callbackfn, ...args )`, §27.2.4.8†:
/// 1. Let C be the this value.
/// 2. If C is not an Object, throw a TypeError exception.
/// 3. Let promiseCapability be ? NewPromiseCapability(C).
/// 4. Let status be Completion(Call(callbackfn, undefined, args)).
/// 5. If status is an abrupt completion, then
///    a. Perform ? Call(promiseCapability.[[Reject]], undefined, «
///    status.[[Value]] »).
/// 6. Else,
///    a. Perform ? Call(promiseCapability.[[Resolve]], undefined, «
///    status.[[Value]] »).
/// 7. Return promiseCapability.[[Promise]].
fn try_fn(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    if !vm.heap().is_object(this) {
        return Err(vm.type_error("Promise.try called on a non-object"));
    }
    let cap = new_promise_capability(vm, this)?;
    let rest = args.get(1..).unwrap_or(&[]);
    match vm.call(arg(args, 0), Value::UNDEFINED, rest) {
        Ok(v) => vm.call(cap.resolve, Value::UNDEFINED, &[v])?,
        Err(e) => {
            let v = caught(e)?;
            vm.call(cap.reject, Value::UNDEFINED, &[v])?
        }
    };
    Ok(cap.promise)
}

/// `Promise.withResolvers ( )`, §27.2.4.9†:
/// 1. Let C be the this value.
/// 2. Let promiseCapability be ? NewPromiseCapability(C).
/// 3. Let obj be OrdinaryObjectCreate(%Object.prototype%).
/// 4. Perform ! CreateDataPropertyOrThrow(obj, "promise",
///    promiseCapability.[[Promise]]).
/// 5. Perform ! CreateDataPropertyOrThrow(obj, "resolve",
///    promiseCapability.[[Resolve]]).
/// 6. Perform ! CreateDataPropertyOrThrow(obj, "reject",
///    promiseCapability.[[Reject]]).
/// 7. Return obj.
fn with_resolvers(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let cap = new_promise_capability(vm, this)?;
    let obj = vm.new_object()?;
    vm.define_property(obj, "promise", cap.promise)?;
    vm.define_property(obj, "resolve", cap.resolve)?;
    vm.define_property(obj, "reject", cap.reject)?;
    Ok(obj)
}

// -----------------------------------------------------------------------
// §27.2.5 Promise.prototype
// -----------------------------------------------------------------------

/// `Promise.prototype.catch ( onRejected )`, §27.2.5.1†:
/// 1. Let promise be the this value.
/// 2. Return ? Invoke(promise, "then", « undefined, onRejected »).
fn catch(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    invoke(vm, this, "then", &[Value::UNDEFINED, arg(args, 0)])
}

/// `Promise.prototype.finally ( onFinally )`, §27.2.5.3†:
/// 1. Let promise be the this value.
/// 2. If promise is not an Object, throw a TypeError exception.
/// 3. Let C be ? SpeciesConstructor(promise, %Promise%).
/// 4. Assert: IsConstructor(C) is true.
/// 5. If IsCallable(onFinally) is false, then
///    a. Let thenFinally be onFinally.
///    b. Let catchFinally be onFinally.
/// 6. Else,
///    a. Let thenFinallyClosure be a new Abstract Closure with parameters
///    (value) that captures onFinally and C and performs the following steps
///    when called: i. Let result be ? Call(onFinally, undefined). ii. Let
///    p be ? PromiseResolve(C, result). iii. Let returnValue be a new
///    Abstract Closure with no parameters that captures value and performs
///    the following steps when called: 1. Return value. iv. Let valueThunk be
///    CreateBuiltinFunction(returnValue, 0, "", « »). v. Return ?
///    Invoke(p, "then", « valueThunk »).
///    b. Let thenFinally be CreateBuiltinFunction(thenFinallyClosure, 1, "",
///    « »).
///    c. Let catchFinallyClosure be a new Abstract Closure with parameters
///    (reason) ... iv. Let thrower be CreateBuiltinFunction(throwReason, 0,
///    "", « »), where throwReason is `Return ThrowCompletion(reason)`. v.
///    Return ? Invoke(p, "then", « thrower »).
///    d. Let catchFinally be CreateBuiltinFunction(catchFinallyClosure, 1,
///    "", « »).
/// 7. Return ? Invoke(promise, "then", « thenFinally, catchFinally »).
fn finally(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    if !vm.heap().is_object(this) {
        return Err(vm.type_error("Promise.prototype.finally called on a non-object"));
    }
    let default = vm.intrinsic(Intrinsic::PromiseConstructor);
    let c = species_constructor(vm, this, default)?;
    let on_finally = arg(args, 0);
    let (then_finally, catch_finally) = if vm.heap().is_callable(on_finally) {
        let tf = vm.new_native("", 1, then_finally_steps)?;
        vm.set_function_slots(tf, vec![on_finally, c]);
        let cf = vm.new_native("", 1, catch_finally_steps)?;
        vm.set_function_slots(cf, vec![on_finally, c]);
        (tf, cf)
    } else {
        (on_finally, on_finally)
    };
    invoke(vm, this, "then", &[then_finally, catch_finally])
}

fn then_finally_steps(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    finally_steps(vm, arg(args, 0), false)
}

fn catch_finally_steps(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    finally_steps(vm, arg(args, 0), true)
}

fn finally_steps(vm: &mut Vm, value: Value, throws: bool) -> Result<Value, Abrupt> {
    let (on_finally, c) = (fslot(vm, 0)?, fslot(vm, 1)?);
    let result = vm.call(on_finally, Value::UNDEFINED, &[])?;
    let p = promise_resolve(vm, c, result)?;
    let thunk = vm.new_native("", 0, if throws { thrower } else { value_thunk })?;
    vm.set_function_slots(thunk, vec![value]);
    invoke(vm, p, "then", &[thunk])
}

fn value_thunk(vm: &mut Vm, _this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    fslot(vm, 0)
}

fn thrower(vm: &mut Vm, _this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    Err(Abrupt::Throw(fslot(vm, 0)?))
}

/// `Promise.prototype.then ( onFulfilled, onRejected )`, §27.2.5.4†:
/// 1. Let promise be the this value.
/// 2. If IsPromise(promise) is false, throw a TypeError exception.
/// 3. Let C be ? SpeciesConstructor(promise, %Promise%).
/// 4. Let resultCapability be ? NewPromiseCapability(C).
/// 5. Return PerformPromiseThen(promise, onFulfilled, onRejected,
///    resultCapability).
fn then(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    if !is_promise(vm, this) {
        return Err(vm.type_error("Promise.prototype.then called on an incompatible receiver"));
    }
    let default = vm.intrinsic(Intrinsic::PromiseConstructor);
    let c = species_constructor(vm, this, default)?;
    let cap = new_promise_capability(vm, c)?;
    perform_promise_then(vm, this, arg(args, 0), arg(args, 1), Some(cap))
}

/// `get Promise [ @@species ]`, §27.2.4.9†: 1. Return the this value.
fn get_species(_vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    Ok(this)
}
