//! Generators, async functions and async generators in the interpreter
//! (phase-7.md items 7.7 and 7.8: "generators and async functions, whose
//! frames are copied to a heap object on suspend and back on resume").
//!
//! # The mechanism
//!
//! A call of a generator, async function or async generator pushes an
//! ordinary frame of kind `KIND_SUSPENDABLE` (`spec::kind_suspendable`) and
//! runs it in the loop like any other call. The frame's object (the generator
//! object, or the state of an async function) is found from the frame's base
//! in a table of the VM ([`crate::host`]'s `suspendables`), which a frame of
//! that kind has from the op that creates the object until it leaves.
//!
//! - **Suspension** ([`Instr::GeneratorStart`](crate::bytecode::Instr),
//!   `Yield`, `YieldDelegate`, `Await`) copies the frame (header and
//!   registers), the `pc` after the op and the two registers the op names for
//!   the resumption into the object's slots, then leaves the frame as a
//!   `Return` does, with the value the caller gets: the generator object, an
//!   iterator result, an async function's promise, or `undefined`.
//! - **Resumption** pushes the copy back as a new frame on top of the running
//!   one, with no caller in the region (`RET_NONE`), writes the sent value and
//!   the mode (0 next, 1 throw, 2 return) into the op's two registers, and runs
//!   the loop on it until it suspends or leaves ([`Vm::execute`]), as a native
//!   that calls into JS does. The compiled code after the op dispatches on the
//!   mode (`compile/suspend.rs`), so a throw or return resumption is ordinary
//!   control flow through the `finally` blocks.
//! - **Leaving.** A `Return` from such a frame completes the object (the
//!   generator's result `{ value, done: true }`, the async function's promise
//!   resolved). An exception that leaves the frame completes a generator and
//!   goes on to its consumer, and rejects an async function's promise (or an
//!   async generator's request), which the caller then gets as for a return.
//!
//! The registers are the whole frame, so a suspension keeps every local; the
//! slots are ordinary heap values, so nothing is hidden from the collector of
//! item 7.6. `spec::fast_path` already sends every op here to its handler:
//! the suspension ops are handler ops, a `Return` from a frame that is not
//! plain is not fast, and `FnInfo::fast_callable` is false for these
//! functions.
//!
//! # Where the standard is followed
//!
//! ECMA-262 §27.5† (generators: GeneratorStart §27.5.3.1†, GeneratorValidate
//! §27.5.3.2†, GeneratorResume §27.5.3.3†, GeneratorResumeAbrupt §27.5.3.4†,
//! GeneratorYield §27.5.3.6†), §27.6† (async generators: AsyncGeneratorStart
//! §27.6.3.3†, AsyncGeneratorEnqueue §27.6.3.5†, AsyncGeneratorCompleteStep
//! §27.6.3.6†, AsyncGeneratorResume §27.6.3.7†, AsyncGeneratorYield
//! §27.6.3.8†, AsyncGeneratorAwaitReturn §27.6.3.9†,
//! AsyncGeneratorDrainQueue §27.6.3.10†, and the prototype methods
//! §27.6.1.2† to §27.6.1.4†), §27.7† (AsyncFunctionStart §27.7.5.1†,
//! AsyncBlockStart §27.7.5.2†), Await §6.2.3.1†, EvaluateGeneratorBody
//! §15.5.2†, EvaluateAsyncFunctionBody §15.8.4†, EvaluateAsyncGeneratorBody
//! §15.6.2†, CreateAsyncFromSyncIterator §27.1.6.1†, and the iterator
//! operations of §7.4† that `yield*` and `for await` use.
//!
//! # Differences from the standard, all listed
//!
//! - **A resumption runs on the host stack**, as a native's call into JS does:
//!   generators that resume each other (`yield*` through a chain of
//!   generators) nest one run of the loop per level, and the levels count
//!   towards [`Vm::set_native_depth_limit`]'s bound, past which the resumption
//!   is a `RangeError`.
//! - **The promises come from the built-ins** ([`PromiseOps`]); a VM without
//!   them reports an async function's call and `await` as not implemented.
//! - **One realm**: the realm switches of AsyncGeneratorCompleteStep do not
//!   arise.

use crate::bytecode::{Flavor, Instr};
use crate::frame::{
    FrameError, HDR_ARGC, HDR_CALLEE, HDR_SLOTS, HDR_THIS, KIND_SUSPENDABLE, RET_NONE, frame_size,
};
use crate::heap::{IterRecord, ObjKind};
use crate::interp::{Abrupt, Flow, Intrinsic, Vm};
use clazel_js_heap::shape::Attrs;
use clazel_js_heap::value::{Decoded, Value};
use std::collections::VecDeque;

/// The host-object tag of a generator object (§27.5†).
pub const TAG_GENERATOR: u32 = 0x4701;
/// The host-object tag of the state of a running async function.
pub const TAG_ASYNC_FUNCTION: u32 = 0x4702;
/// The host-object tag of an async generator object (§27.6†).
pub const TAG_ASYNC_GENERATOR: u32 = 0x4703;
/// The host-object tag of an Async-from-Sync Iterator object (§27.1.6†): its
/// slots are the sync iterator and its `next` method
/// (`[[SyncIteratorRecord]]`).
pub const TAG_ASYNC_FROM_SYNC: u32 = 0x4704;

/// Slots of a suspendable's object: the state, the frame header, the `pc`
/// to resume at, the registers the resumption writes (or -1), the promise
/// capability of an async function, the cached Await reactions, and from
/// `S_REGS` on the frame's registers while it is suspended.
const S_STATE: usize = 0;
const S_CALLEE: usize = 1;
const S_THIS: usize = 2;
const S_ARGC: usize = 3;
const S_PC: usize = 4;
const S_VALUE: usize = 5;
const S_MODE: usize = 6;
const S_PROMISE: usize = 7;
const S_RESOLVE: usize = 8;
const S_REJECT: usize = 9;
const S_ON_FULFILLED: usize = 10;
const S_ON_REJECTED: usize = 11;
const S_REGS: usize = 12;

/// `[[GeneratorState]]` and `[[AsyncGeneratorState]]` (§27.5†, §27.6†); an
/// async function uses the first four.
const SUSPENDED_START: i32 = 0;
const SUSPENDED_YIELD: i32 = 1;
const EXECUTING: i32 = 2;
const COMPLETED: i32 = 3;
const AWAITING_RETURN: i32 = 4;

/// How a suspended frame is resumed: the mode its suspension op receives,
/// and the kind of the completion of the standard's GeneratorResume and
/// GeneratorResumeAbrupt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResumeMode {
    /// A normal completion: `next(v)`, or a fulfilled await.
    Next,
    /// A throw completion: `throw(e)`, or a rejected await.
    Throw,
    /// A return completion: `return(v)`.
    Return,
}

impl ResumeMode {
    fn code(self) -> i32 {
        match self {
            ResumeMode::Next => 0,
            ResumeMode::Throw => 1,
            ResumeMode::Return => 2,
        }
    }
}

/// A PromiseCapability Record (§27.2.1.1†): the promise, its resolve function
/// and its reject function.
pub type Capability = (Value, Value, Value);

/// The Promise operations that `await` and async functions need, which the
/// built-ins provide (`clazel-js-builtins`' `promise` installs them with
/// [`Vm::set_promise_ops`]): the VM has no Promise of its own.
#[derive(Clone, Copy, Debug)]
pub struct PromiseOps {
    /// NewPromiseCapability(%Promise%) (§27.2.1.5†): the promise, its resolve
    /// function and its reject function.
    pub new_capability: fn(&mut Vm) -> Result<Capability, Abrupt>,
    /// PromiseResolve(%Promise%, x) (§27.2.4.7.1†).
    pub resolve: fn(&mut Vm, Value) -> Result<Value, Abrupt>,
    /// PerformPromiseThen(promise, onFulfilled, onRejected) (§27.2.5.4.1†),
    /// without a result capability.
    pub then: fn(&mut Vm, Value, Value, Value) -> Result<(), Abrupt>,
}

/// An AsyncGeneratorRequest Record (§27.6.3.1†): the completion, and of the
/// capability of the promise `next`, `return` or `throw` returned the two
/// functions that settle it.
#[derive(Clone, Copy, Debug)]
pub(crate) struct AgRequest {
    value: Value,
    mode: ResumeMode,
    resolve: Value,
    reject: Value,
}

/// A completion that AsyncGeneratorCompleteStep settles a request with.
#[derive(Clone, Copy, Debug)]
enum Completion {
    Normal(Value),
    Throw(Value),
}

/// The state this module adds to the VM's host state.
#[derive(Debug, Default)]
pub(crate) struct SuspendState {
    /// The object of each running suspendable frame, by the frame's base.
    pub(crate) frames: std::collections::HashMap<usize, Value>,
    /// `[[AsyncGeneratorQueue]]` of each async generator that has one.
    pub(crate) queues: std::collections::HashMap<Value, VecDeque<AgRequest>>,
    /// The Promise operations of the built-ins.
    pub(crate) promise_ops: Option<PromiseOps>,
    /// The native-table indices of the reactions this module makes (see
    /// [`Vm::reaction`]), made once.
    pub(crate) natives: Option<[u32; 4]>,
}

/// Which reaction function [`Vm::reaction`] makes.
#[derive(Clone, Copy)]
enum Reaction {
    AwaitFulfilled = 0,
    AwaitRejected = 1,
    ReturnFulfilled = 2,
    ReturnRejected = 3,
}

fn int_of(v: Option<Value>) -> i32 {
    match v.map(|v| v.decode()) {
        Some(Decoded::Int32(i)) => i,
        _ => -1,
    }
}

fn reg_of(v: Option<Value>) -> Option<u32> {
    u32::try_from(int_of(v)).ok()
}

fn int_value(n: u32) -> Result<Value, Abrupt> {
    i32::try_from(n)
        .map(Value::int32)
        .map_err(|_| Abrupt::Internal("register or pc out of range"))
}

impl Vm {
    /// Installs the Promise operations of the built-ins.
    pub fn set_promise_ops(&mut self, ops: PromiseOps) {
        self.host.suspend.promise_ops = Some(ops);
    }

    fn promise_ops(&self) -> Result<PromiseOps, Abrupt> {
        self.host
            .suspend
            .promise_ops
            .ok_or_else(|| Abrupt::NotYet("async functions without the Promise built-ins".into()))
    }

    // -----------------------------------------------------------------
    // The object's slots
    // -----------------------------------------------------------------

    fn sus_slot(&self, obj: Value, i: usize) -> Result<Value, Abrupt> {
        self.host_slot(obj, i)
            .ok_or(Abrupt::Internal("suspendable object slot"))
    }

    fn set_sus_slot(&mut self, obj: Value, i: usize, v: Value) -> Result<(), Abrupt> {
        if self.set_host_slot(obj, i, v) {
            Ok(())
        } else {
            Err(Abrupt::Internal("suspendable object slot"))
        }
    }

    fn sus_state(&self, obj: Value) -> i32 {
        int_of(self.host_slot(obj, S_STATE))
    }

    fn set_sus_state(&mut self, obj: Value, state: i32) -> Result<(), Abrupt> {
        self.set_sus_slot(obj, S_STATE, Value::int32(state))
    }

    /// Completes the object: its state is completed and the frame copy is
    /// dropped (a completed generator never runs again).
    fn complete(&mut self, obj: Value) -> Result<(), Abrupt> {
        self.set_sus_state(obj, COMPLETED)?;
        if let Some(h) = self.host_object_mut(obj) {
            h.slots.truncate(S_REGS);
        }
        Ok(())
    }

    /// A new suspendable object of prototype `proto` in state
    /// suspended-start.
    fn new_suspendable(&mut self, proto: Value, tag: u32) -> Result<Value, Abrupt> {
        let mut slots = vec![Value::UNDEFINED; S_REGS];
        if let Some(s) = slots.get_mut(S_STATE) {
            *s = Value::int32(SUSPENDED_START);
        }
        self.new_host_object(proto, tag, slots, None)
    }

    /// The object of the running frame.
    fn frame_object(&self) -> Result<Value, Abrupt> {
        self.host
            .suspend
            .frames
            .get(&self.fp)
            .copied()
            .ok_or(Abrupt::Internal(
                "suspension op outside a suspendable frame",
            ))
    }

    // -----------------------------------------------------------------
    // Copying the frame out and back
    // -----------------------------------------------------------------

    /// Copies the running frame into `obj`: the header, the registers, the
    /// `pc` to resume at and the registers of the resumption (`None` for the
    /// start, whose first resumption sends nothing).
    fn save_frame(
        &mut self,
        obj: Value,
        resume_pc: usize,
        regs: Option<(u32, u32)>,
    ) -> Result<(), Abrupt> {
        let fp = self.fp;
        let callee = self.region.header(fp, HDR_CALLEE)?;
        let this = self.region.header(fp, HDR_THIS)?;
        let argc = self.region.header(fp, HDR_ARGC)?;
        let first = fp
            .checked_add(HDR_SLOTS)
            .ok_or(Abrupt::Internal("frame base"))?;
        let mut copy = Vec::with_capacity(self.top.saturating_sub(first));
        for i in first..self.top {
            copy.push(self.region.get(i)?);
        }
        let pc = int_value(u32::try_from(resume_pc).map_err(|_| Abrupt::Internal("pc"))?)?;
        let (vreg, mreg) = match regs {
            Some((v, m)) => (int_value(v)?, int_value(m)?),
            None => (Value::int32(-1), Value::int32(-1)),
        };
        let h = self
            .host_object_mut(obj)
            .ok_or(Abrupt::Internal("suspendable object"))?;
        h.slots.truncate(S_REGS);
        for (i, v) in [
            (S_CALLEE, callee),
            (S_THIS, this),
            (S_ARGC, argc),
            (S_PC, pc),
            (S_VALUE, vreg),
            (S_MODE, mreg),
        ] {
            if let Some(s) = h.slots.get_mut(i) {
                *s = v;
            }
        }
        h.slots.extend(copy);
        Ok(())
    }

    /// Pushes the frame copied into `obj` on top of the running frame, with
    /// no caller in the region, and makes it the running one: the sent value
    /// and the mode go to the registers its suspension op named.
    fn restore_frame(&mut self, obj: Value, value: Value, mode: ResumeMode) -> Result<(), Abrupt> {
        let (callee, this, argc, pc, vreg, mreg, regs) = {
            let s = self
                .host_slots(obj)
                .ok_or(Abrupt::Internal("suspendable object"))?;
            let at = |i: usize| s.get(i).copied();
            (
                at(S_CALLEE).ok_or(Abrupt::Internal("suspended frame"))?,
                at(S_THIS).ok_or(Abrupt::Internal("suspended frame"))?,
                at(S_ARGC).ok_or(Abrupt::Internal("suspended frame"))?,
                usize::try_from(int_of(at(S_PC))).map_err(|_| Abrupt::Internal("suspended pc"))?,
                reg_of(at(S_VALUE)),
                reg_of(at(S_MODE)),
                s.get(S_REGS..).map(<[Value]>::to_vec).unwrap_or_default(),
            )
        };
        let code = self.code_of(callee)?;
        let (nparams, nregs) = {
            let f = self.codes.get(code).ok_or(Abrupt::Internal("code index"))?;
            (f.code.nparams, f.code.nregs)
        };
        let size = frame_size(nparams, nregs).ok_or(Abrupt::Internal("frame size"))?;
        if size.checked_sub(HDR_SLOTS) != Some(regs.len()) {
            return Err(Abrupt::Internal("suspended frame size"));
        }
        self.charge()?;
        let ret = Value::raw(RET_NONE).ok_or(Abrupt::Internal("return address"))?;
        let base = self.top;
        if self
            .region
            .push_frame(base, size, [callee, this, argc, ret])
            == Err(FrameError::Overflow)
        {
            return Err(self.range_error("Maximum call stack size exceeded"));
        }
        let first = base
            .checked_add(HDR_SLOTS)
            .ok_or(Abrupt::Internal("frame base"))?;
        for (i, v) in regs.into_iter().enumerate() {
            let at = first.checked_add(i).ok_or(Abrupt::Internal("frame slot"))?;
            self.region.set(at, v)?;
        }
        self.set_frame(base, pc, code)?;
        if let (Some(v), Some(m)) = (vreg, mreg) {
            self.w(v, value)?;
            self.w(m, Value::int32(mode.code()))?;
        }
        self.host.suspend.frames.insert(base, obj);
        self.set_sus_state(obj, EXECUTING)
    }

    /// Resumes the frame suspended in `obj` and runs it until it suspends
    /// again or leaves: the value the frame leaves with (an iterator result,
    /// a promise, or `undefined`).
    fn run_resumed(&mut self, obj: Value, value: Value, mode: ResumeMode) -> Result<Value, Abrupt> {
        let saved = (self.fp, self.pc, self.cur, self.top);
        let base = self.top;
        let r = match self.restore_frame(obj, value, mode) {
            Ok(()) => self.execute(),
            Err(e) => Err(e),
        };
        (self.fp, self.pc, self.cur, self.top) = saved;
        if r.is_err() {
            // An exception that left a generator, or an error JS cannot
            // catch: the object is done either way.
            self.host.suspend.frames.remove(&base);
            if self.sus_state(obj) == EXECUTING {
                self.complete(obj)?;
            }
        }
        r
    }

    /// Leaves the running suspendable frame with `v`, as `Return` does: to
    /// the caller's call op, or out of the loop for a frame with no caller.
    fn leave(&mut self, v: Value) -> Result<Flow, Abrupt> {
        self.host.suspend.frames.remove(&self.fp);
        self.return_to_caller(v)
    }

    // -----------------------------------------------------------------
    // Calls
    // -----------------------------------------------------------------

    /// The frame kind of a call of code `code`, and for an async function the
    /// object the frame starts with (AsyncFunctionStart §27.7.5.1†:
    /// EvaluateAsyncFunctionBody §15.8.4† step 1, "Let promiseCapability be !
    /// NewPromiseCapability(%Promise%)", before FunctionDeclarationInstantiation,
    /// whose errors reject the promise).
    pub(crate) fn suspendable_entry(
        &mut self,
        code: usize,
        frame_kind: u32,
    ) -> Result<(u32, Option<Value>), Abrupt> {
        let flavor = self
            .codes
            .get(code)
            .map(|f| f.code.flavor)
            .ok_or(Abrupt::Internal("code index"))?;
        match flavor {
            Flavor::Plain => Ok((frame_kind, None)),
            Flavor::Generator | Flavor::AsyncGenerator => Ok((KIND_SUSPENDABLE, None)),
            Flavor::Async => {
                let ops = self.promise_ops()?;
                let (promise, resolve, reject) = (ops.new_capability)(self)?;
                let obj = self.new_suspendable(Value::NULL, TAG_ASYNC_FUNCTION)?;
                self.set_sus_slot(obj, S_PROMISE, promise)?;
                self.set_sus_slot(obj, S_RESOLVE, resolve)?;
                self.set_sus_slot(obj, S_REJECT, reject)?;
                self.set_sus_state(obj, EXECUTING)?;
                Ok((KIND_SUSPENDABLE, Some(obj)))
            }
        }
    }

    /// Records the object of a suspendable frame just pushed at `base`.
    pub(crate) fn suspendable_entered(&mut self, base: usize, obj: Option<Value>) {
        match obj {
            Some(o) => {
                self.host.suspend.frames.insert(base, o);
            }
            None => {
                self.host.suspend.frames.remove(&base);
            }
        }
    }

    // -----------------------------------------------------------------
    // The ops
    // -----------------------------------------------------------------

    /// `GeneratorStart`: EvaluateGeneratorBody §15.5.2† steps 2 to 5 and
    /// EvaluateAsyncGeneratorBody §15.6.2† steps 2 to 5:
    /// 2. Let G be ? OrdinaryCreateFromConstructor(functionObject,
    ///    "%GeneratorFunction.prototype.prototype%", « [[GeneratorState]],
    ///    [[GeneratorContext]], [[GeneratorBrand]] »).
    /// 3. Set G.[[GeneratorBrand]] to empty.
    /// 4. Perform GeneratorStart(G, FunctionBody) (§27.5.3.1†: "Set
    ///    generator.[[GeneratorState]] to suspended-start").
    /// 5. Return Completion Record { [[Type]]: return, [[Value]]: G }.
    ///
    /// (For an async generator, `%AsyncGeneratorFunction.prototype.prototype%`
    /// and AsyncGeneratorStart §27.6.3.3†, with an empty queue.)
    ///
    /// GetPrototypeFromConstructor (§10.1.14†) reads the function's
    /// `prototype` and takes the intrinsic when it is not an Object.
    pub(crate) fn op_generator_start(&mut self) -> Result<Flow, Abrupt> {
        let callee = self.region.header(self.fp, HDR_CALLEE)?;
        let flavor = self
            .codes
            .get(self.cur)
            .map(|f| f.code.flavor)
            .ok_or(Abrupt::Internal("code index"))?;
        let (fallback, tag) = if flavor == Flavor::AsyncGenerator {
            (
                self.intrinsic(Intrinsic::AsyncGeneratorPrototype),
                TAG_ASYNC_GENERATOR,
            )
        } else {
            (self.intrinsic(Intrinsic::GeneratorPrototype), TAG_GENERATOR)
        };
        let kp = self.atoms.k_prototype;
        let p = self.get_property(callee, kp, None)?;
        let proto = if self.heap.is_object(p) {
            p
        } else if self.heap.is_object(fallback) {
            fallback
        } else {
            self.atoms.object_proto
        };
        let g = self.new_suspendable(proto, tag)?;
        self.save_frame(g, self.pc.saturating_add(1), None)?;
        if tag == TAG_ASYNC_GENERATOR {
            self.host.suspend.queues.insert(g, VecDeque::new());
        }
        self.leave(g)
    }

    /// `Yield` and `YieldDelegate`.
    ///
    /// In a generator, GeneratorYield (§27.5.3.6†) of CreateIterResultObject(
    /// value, false) (Yield §27.5.3.7†), or of the inner result object itself
    /// for `YieldDelegate`: "Set generator.[[GeneratorState]] to
    /// suspended-yield", and the caller gets the result.
    ///
    /// In an async generator, AsyncGeneratorYield ( value ) §27.6.3.8†:
    /// 10. Perform AsyncGeneratorCompleteStep(generator, completion, false,
    ///     previousRealm).
    /// 11. Let queue be generator.[[AsyncGeneratorQueue]].
    /// 12. If queue is not empty, then
    ///     a. NOTE: Execution continues without suspending the generator.
    ///     b. Let toYield be the first element of queue.
    ///     c. Let resumptionValue be Completion(toYield.[[Completion]]).
    ///     d. Return ? AsyncGeneratorUnwrapYieldResumption(resumptionValue).
    /// 13. Else,
    ///     a. Set generator.[[AsyncGeneratorState]] to suspended-yield.
    ///     b.-d. Suspend; the caller gets undefined.
    ///
    /// (AsyncGeneratorUnwrapYieldResumption's await of a return is compiled
    /// after the op, `compile/suspend.rs`.)
    pub(crate) fn op_yield(
        &mut self,
        src: u32,
        value: u32,
        mode: u32,
        delegate: bool,
    ) -> Result<Flow, Abrupt> {
        let obj = self.frame_object()?;
        let v = self.r(src)?;
        let next_pc = self.pc.saturating_add(1);
        if self.host_tag(obj) == Some(TAG_ASYNC_GENERATOR) {
            self.complete_step(obj, Completion::Normal(v), false)?;
            let front = self
                .host
                .suspend
                .queues
                .get(&obj)
                .and_then(|q| q.front().copied());
            if let Some(req) = front {
                self.w(value, req.value)?;
                self.w(mode, Value::int32(req.mode.code()))?;
                self.pc = next_pc;
                return Ok(Flow::Continue);
            }
            self.save_frame(obj, next_pc, Some((value, mode)))?;
            self.set_sus_state(obj, SUSPENDED_YIELD)?;
            return self.leave(Value::UNDEFINED);
        }
        let result = if delegate {
            v
        } else {
            self.iter_result(v, false)?
        };
        self.save_frame(obj, next_pc, Some((value, mode)))?;
        self.set_sus_state(obj, SUSPENDED_YIELD)?;
        self.leave(result)
    }

    /// `Await`: Await ( value ) §6.2.3.1†:
    /// 1. Let asyncContext be the running execution context.
    /// 2. Let promise be ? PromiseResolve(%Promise%, value).
    /// 3. to 6. onFulfilled and onRejected resume asyncContext with a normal or
    ///    a throw completion.
    /// 7. Perform PerformPromiseThen(promise, onFulfilled, onRejected).
    /// 8. Remove asyncContext from the execution context stack and restore
    ///    the execution context that is at the top of the execution context
    ///    stack as the running execution context.
    /// 9. Let callerContext be the running execution context.
    /// 10. Resume callerContext passing empty.
    ///
    /// An async function's caller gets its promise (AsyncBlockStart
    /// §27.7.5.2†: the call returns promiseCapability.[[Promise]] when the
    /// body first suspends); an async generator's resumer gets `undefined`.
    pub(crate) fn op_await(&mut self, src: u32, value: u32, mode: u32) -> Result<Flow, Abrupt> {
        let obj = self.frame_object()?;
        let ops = self.promise_ops()?;
        let v = self.r(src)?;
        let promise = (ops.resolve)(self, v)?;
        let on_fulfilled = self.cached_reaction(obj, S_ON_FULFILLED, Reaction::AwaitFulfilled)?;
        let on_rejected = self.cached_reaction(obj, S_ON_REJECTED, Reaction::AwaitRejected)?;
        (ops.then)(self, promise, on_fulfilled, on_rejected)?;
        self.save_frame(obj, self.pc.saturating_add(1), Some((value, mode)))?;
        let out = if self.host_tag(obj) == Some(TAG_ASYNC_FUNCTION) {
            self.sus_slot(obj, S_PROMISE)?
        } else {
            Value::UNDEFINED
        };
        self.leave(out)
    }

    /// `Return` from a suspendable frame.
    ///
    /// - A generator: GeneratorStart §27.5.3.1† step 4.g to 4.l, "Set
    ///   acGenerator.[[GeneratorState]] to completed", and the result is
    ///   CreateIterResultObject(resultValue, true).
    /// - An async function: AsyncBlockStart §27.7.5.2† step 2.f, "Perform !
    ///   Call(promiseCapability.[[Resolve]], undefined, « result.[[Value]]
    ///   »)"; the caller gets the promise.
    /// - An async generator: AsyncGeneratorStart §27.6.3.3† step 4.d to 4.h:
    ///   completed, AsyncGeneratorCompleteStep(acGenerator, result, true) and
    ///   AsyncGeneratorDrainQueue(acGenerator).
    ///
    /// A frame without an object (none is possible: a generator's frame has
    /// returned at `GeneratorStart` before its body runs) returns as a plain
    /// one.
    pub(crate) fn suspendable_return(&mut self, v: Value) -> Result<Flow, Abrupt> {
        let Some(obj) = self.host.suspend.frames.get(&self.fp).copied() else {
            return self.leave(v);
        };
        self.complete(obj)?;
        match self.host_tag(obj) {
            Some(TAG_GENERATOR) => {
                let r = self.iter_result(v, true)?;
                self.leave(r)
            }
            Some(TAG_ASYNC_FUNCTION) => {
                let resolve = self.sus_slot(obj, S_RESOLVE)?;
                self.call(resolve, Value::UNDEFINED, &[v])?;
                let p = self.sus_slot(obj, S_PROMISE)?;
                self.leave(p)
            }
            Some(TAG_ASYNC_GENERATOR) => {
                self.complete_step(obj, Completion::Normal(v), true)?;
                self.drain_queue(obj)?;
                self.leave(Value::UNDEFINED)
            }
            _ => Err(Abrupt::Internal("suspendable object tag")),
        }
    }

    /// An exception leaving the running frame, if it is suspendable: `None`
    /// when it goes on to the caller (a generator is completed first), or how
    /// the loop goes on when the frame catches it as its object's result.
    ///
    /// - An async function: AsyncBlockStart §27.7.5.2† step 2.g, "Assert:
    ///   result is a throw completion. Perform ! Call(promiseCapability.
    ///   [[Reject]], undefined, « result.[[Value]] »)" (and
    ///   EvaluateAsyncFunctionBody §15.8.4† step 3 for an error of the
    ///   parameters); the caller gets the promise.
    /// - An async generator: AsyncGeneratorStart §27.6.3.3† step 4.g, the
    ///   throw completes the first request.
    pub(crate) fn suspendable_throw(&mut self, exc: Value) -> Result<Option<Flow>, Abrupt> {
        let (_, kind) = crate::frame::dec_argc(self.region.header(self.fp, HDR_ARGC)?)
            .ok_or(Abrupt::Internal("argument count slot"))?;
        if kind != KIND_SUSPENDABLE {
            return Ok(None);
        }
        let Some(obj) = self.host.suspend.frames.remove(&self.fp) else {
            return Ok(None);
        };
        self.complete(obj)?;
        match self.host_tag(obj) {
            Some(TAG_ASYNC_FUNCTION) => {
                let reject = self.sus_slot(obj, S_REJECT)?;
                self.call(reject, Value::UNDEFINED, &[exc])?;
                let p = self.sus_slot(obj, S_PROMISE)?;
                self.return_to_caller(p).map(Some)
            }
            Some(TAG_ASYNC_GENERATOR) => {
                self.complete_step(obj, Completion::Throw(exc), true)?;
                self.drain_queue(obj)?;
                self.return_to_caller(Value::UNDEFINED).map(Some)
            }
            _ => Ok(None),
        }
    }

    // -----------------------------------------------------------------
    // Generators
    // -----------------------------------------------------------------

    /// `%GeneratorPrototype%.next`, `return` and `throw` (§27.5.1.2† to
    /// §27.5.1.4†) on `generator`: GeneratorResume (§27.5.3.3†) for a normal
    /// completion, GeneratorResumeAbrupt (§27.5.3.4†) for the others.
    ///
    /// GeneratorValidate ( generator, generatorBrand ) §27.5.3.2†:
    /// 1. Perform ? RequireInternalSlot(generator, [[GeneratorState]]).
    /// 2. and 3. (The brand is empty.)
    /// 4. Let state be generator.[[GeneratorState]].
    /// 5. If state is executing, throw a TypeError exception.
    /// 6. Return state.
    ///
    /// GeneratorResumeAbrupt ( generator, abruptCompletion, generatorBrand ):
    /// 1. Let state be ? GeneratorValidate(generator, generatorBrand).
    /// 2. If state is suspended-start, then
    ///    a. Set generator.[[GeneratorState]] to completed.
    ///    b. NOTE: Once a generator enters the completed state it never
    ///    leaves it and its associated execution context is never resumed.
    ///    c. Set state to completed.
    /// 3. If state is completed, then
    ///    a. If abruptCompletion is a return completion, then
    ///    i. Return CreateIterResultObject(abruptCompletion.[[Value]], true).
    ///    b. Return ? abruptCompletion.
    /// 4. Assert: state is suspended-yield.
    /// 5. to 10. Resume the generator with abruptCompletion.
    ///
    /// GeneratorResume ( generator, value, generatorBrand ):
    /// 1. Let state be ? GeneratorValidate(generator, generatorBrand).
    /// 2. If state is completed, return CreateIterResultObject(undefined, true).
    /// 3. Assert: state is either suspended-start or suspended-yield.
    /// 4. to 10. Resume the generator with NormalCompletion(value).
    ///
    /// # Errors
    /// The TypeErrors of GeneratorValidate, a thrown value of a throw
    /// completion, or what the generator throws.
    pub fn generator_resume(
        &mut self,
        generator: Value,
        value: Value,
        mode: ResumeMode,
    ) -> Result<Value, Abrupt> {
        if self.host_tag(generator) != Some(TAG_GENERATOR) {
            return Err(self.type_error("not a generator object"));
        }
        let mut state = self.sus_state(generator);
        if state == EXECUTING {
            return Err(self.type_error("Generator is already running"));
        }
        if state == SUSPENDED_START && mode != ResumeMode::Next {
            self.complete(generator)?;
            state = COMPLETED;
        }
        if state == COMPLETED {
            return match mode {
                ResumeMode::Next => self.iter_result(Value::UNDEFINED, true),
                ResumeMode::Return => self.iter_result(value, true),
                ResumeMode::Throw => Err(Abrupt::Throw(value)),
            };
        }
        self.run_resumed(generator, value, mode)
    }

    /// CreateIterResultObject ( value, done ), §7.4.14†.
    pub(crate) fn iter_result(&mut self, value: Value, done: bool) -> Result<Value, Abrupt> {
        let o = self.new_object()?;
        let (kv, kd) = (self.atoms.k_value, self.atoms.k_done);
        self.heap.define(o, kv, value, Attrs::ALL)?;
        self.heap.define(o, kd, Value::boolean(done), Attrs::ALL)?;
        Ok(o)
    }

    // -----------------------------------------------------------------
    // Async functions and async generators: the reactions
    // -----------------------------------------------------------------

    /// A built-in function with one captured value, `obj` (the closures of
    /// Await §6.2.3.1† steps 3 to 6, and of AsyncGeneratorAwaitReturn
    /// §27.6.3.9† steps 11 to 14). The native table holds each kind once.
    fn reaction(&mut self, which: Reaction, obj: Value) -> Result<Value, Abrupt> {
        let natives = match self.host.suspend.natives {
            Some(n) => n,
            None => {
                let mut n = [0u32; 4];
                for (slot, f) in n.iter_mut().zip([
                    await_fulfilled as crate::interp::NativeFn,
                    await_rejected,
                    return_fulfilled,
                    return_rejected,
                ]) {
                    *slot = u32::try_from(self.natives.len()).map_err(|_| Abrupt::OutOfMemory)?;
                    self.natives.push((f, false));
                }
                self.host.suspend.natives = Some(n);
                n
            }
        };
        let index = natives
            .get(which as usize)
            .copied()
            .ok_or(Abrupt::Internal("reaction kind"))?;
        let proto = self.atoms.function_proto;
        let f = self.heap.new_object(proto, ObjKind::Native(index))?;
        let (kl, kn) = (self.atoms.k_length, self.atoms.k_name);
        let empty = self.heap.new_str("")?;
        let attrs = Attrs(Attrs::CONFIGURABLE);
        self.heap.define(f, kl, Value::int32(1), attrs)?;
        self.heap.define(f, kn, empty, attrs)?;
        self.set_function_slots(f, vec![obj]);
        Ok(f)
    }

    /// The Await reaction of `obj` kept in slot `slot`, made the first time.
    fn cached_reaction(
        &mut self,
        obj: Value,
        slot: usize,
        which: Reaction,
    ) -> Result<Value, Abrupt> {
        let f = self.sus_slot(obj, slot)?;
        if f != Value::UNDEFINED {
            return Ok(f);
        }
        let f = self.reaction(which, obj)?;
        self.set_sus_slot(obj, slot, f)?;
        Ok(f)
    }

    // -----------------------------------------------------------------
    // Async generators
    // -----------------------------------------------------------------

    /// `%AsyncGeneratorPrototype%.next`, `return` and `throw` (§27.6.1.2† to
    /// §27.6.1.4†): the promise of the request.
    ///
    /// `next ( value )`:
    /// 1. Let generator be the this value.
    /// 2. Let promiseCapability be ! NewPromiseCapability(%Promise%).
    /// 3. Let result be Completion(AsyncGeneratorValidate(generator, empty)).
    /// 4. IfAbruptRejectPromise(result, promiseCapability).
    /// 5. Let state be generator.[[AsyncGeneratorState]].
    /// 6. If state is completed, then
    ///    a. Let iteratorResult be CreateIterResultObject(undefined, true).
    ///    b. Perform ! Call(promiseCapability.[[Resolve]], undefined, «
    ///    iteratorResult »).
    ///    c. Return promiseCapability.[[Promise]].
    /// 7. Let completion be NormalCompletion(value).
    /// 8. Perform AsyncGeneratorEnqueue(generator, completion,
    ///    promiseCapability).
    /// 9. If state is either suspended-start or suspended-yield, then
    ///    a. Perform AsyncGeneratorResume(generator, completion).
    /// 10. Else, a. Assert: state is either executing or awaiting-return.
    /// 11. Return promiseCapability.[[Promise]].
    ///
    /// `return ( value )`, after step 4:
    /// 5. Let completion be Completion Record { [[Type]]: return,
    ///    [[Value]]: value, [[Target]]: empty }.
    /// 6. Perform AsyncGeneratorEnqueue(generator, completion,
    ///    promiseCapability).
    /// 7. Let state be generator.[[AsyncGeneratorState]].
    /// 8. If state is either suspended-start or completed, then
    ///    a. Set generator.[[AsyncGeneratorState]] to awaiting-return.
    ///    b. Perform AsyncGeneratorAwaitReturn(generator).
    /// 9. Else if state is suspended-yield, then
    ///    a. Perform AsyncGeneratorResume(generator, completion).
    /// 10. Else, a. Assert: state is either executing or awaiting-return.
    /// 11. Return promiseCapability.[[Promise]].
    ///
    /// `throw ( exception )`, after step 4:
    /// 5. Let state be generator.[[AsyncGeneratorState]].
    /// 6. If state is suspended-start, then
    ///    a. Set generator.[[AsyncGeneratorState]] to completed.
    ///    b. Set state to completed.
    /// 7. If state is completed, then
    ///    a. Perform ! Call(promiseCapability.[[Reject]], undefined, «
    ///    exception »).
    ///    b. Return promiseCapability.[[Promise]].
    /// 8. Let completion be ThrowCompletion(exception).
    /// 9. Perform AsyncGeneratorEnqueue(generator, completion,
    ///    promiseCapability).
    /// 10. If state is suspended-yield, then
    ///     a. Perform AsyncGeneratorResume(generator, completion).
    /// 11. Else, a. Assert: state is either executing or awaiting-return.
    /// 12. Return promiseCapability.[[Promise]].
    ///
    /// AsyncGeneratorValidate ( generator, generatorBrand ) §27.6.3.2†:
    /// RequireInternalSlot for [[AsyncGeneratorContext]],
    /// [[AsyncGeneratorState]] and [[AsyncGeneratorQueue]], and a TypeError
    /// if the brand differs (it is empty).
    ///
    /// # Errors
    /// Only errors JS cannot catch: a JS error rejects the promise.
    pub fn async_generator_request(
        &mut self,
        generator: Value,
        value: Value,
        mode: ResumeMode,
    ) -> Result<Value, Abrupt> {
        let ops = self.promise_ops()?;
        let (promise, resolve, reject) = (ops.new_capability)(self)?;
        if self.host_tag(generator) != Some(TAG_ASYNC_GENERATOR) {
            let e = self.type_error("not an async generator object");
            let Abrupt::Throw(e) = e else { return Err(e) };
            self.call(reject, Value::UNDEFINED, &[e])?;
            return Ok(promise);
        }
        let mut state = self.sus_state(generator);
        if mode == ResumeMode::Throw && state == SUSPENDED_START {
            self.complete(generator)?;
            state = COMPLETED;
        }
        if state == COMPLETED {
            match mode {
                ResumeMode::Next => {
                    let r = self.iter_result(Value::UNDEFINED, true)?;
                    self.call(resolve, Value::UNDEFINED, &[r])?;
                    return Ok(promise);
                }
                ResumeMode::Throw => {
                    self.call(reject, Value::UNDEFINED, &[value])?;
                    return Ok(promise);
                }
                ResumeMode::Return => {}
            }
        }
        // AsyncGeneratorEnqueue §27.6.3.5†: "Append request to
        // generator.[[AsyncGeneratorQueue]]".
        self.host
            .suspend
            .queues
            .entry(generator)
            .or_default()
            .push_back(AgRequest {
                value,
                mode,
                resolve,
                reject,
            });
        match (mode, state) {
            (ResumeMode::Return, SUSPENDED_START | COMPLETED) => {
                self.set_sus_state(generator, AWAITING_RETURN)?;
                self.await_return(generator)?;
            }
            (_, SUSPENDED_START | SUSPENDED_YIELD) => {
                // AsyncGeneratorResume §27.6.3.7†.
                self.run_resumed(generator, value, mode)?;
            }
            _ => {}
        }
        Ok(promise)
    }

    /// AsyncGeneratorCompleteStep ( generator, completion, done [ , realm ] )
    /// §27.6.3.6†:
    /// 1. Assert: generator.[[AsyncGeneratorQueue]] is not empty.
    /// 2. Let next be the first element of generator.[[AsyncGeneratorQueue]].
    /// 3. Remove the first element from generator.[[AsyncGeneratorQueue]].
    /// 4. Let promiseCapability be next.[[Capability]].
    /// 5. Let value be completion.[[Value]].
    /// 6. If completion is a throw completion, then
    ///    a. Perform ! Call(promiseCapability.[[Reject]], undefined, « value »).
    /// 7. Else,
    ///    a. Assert: completion is a normal completion.
    ///    b.-c. Let iteratorResult be CreateIterResultObject(value, done).
    ///    d. Perform ! Call(promiseCapability.[[Resolve]], undefined, «
    ///    iteratorResult »).
    fn complete_step(&mut self, generator: Value, c: Completion, done: bool) -> Result<(), Abrupt> {
        let next = self
            .host
            .suspend
            .queues
            .get_mut(&generator)
            .and_then(VecDeque::pop_front)
            .ok_or(Abrupt::Internal("async generator queue is empty"))?;
        match c {
            Completion::Throw(e) => {
                self.call(next.reject, Value::UNDEFINED, &[e])?;
            }
            Completion::Normal(v) => {
                let r = self.iter_result(v, done)?;
                self.call(next.resolve, Value::UNDEFINED, &[r])?;
            }
        }
        Ok(())
    }

    /// AsyncGeneratorAwaitReturn ( generator ) §27.6.3.9†:
    /// 1. Assert: generator.[[AsyncGeneratorState]] is awaiting-return.
    /// 2. to 6. Let completion be the first request's completion, a return.
    /// 7. Let promiseCompletion be Completion(PromiseResolve(%Promise%,
    ///    completion.[[Value]])).
    /// 8. If promiseCompletion is an abrupt completion, then
    ///    a. Perform AsyncGeneratorCompleteStep(generator, promiseCompletion,
    ///    true).
    ///    b. Perform AsyncGeneratorDrainQueue(generator).
    ///    c. Return unused.
    /// 9. to 10. Let promise be promiseCompletion.[[Value]].
    /// 11. to 14. onFulfilled and onRejected (see `return_fulfilled`).
    /// 15. Perform PerformPromiseThen(promise, onFulfilled, onRejected).
    fn await_return(&mut self, generator: Value) -> Result<(), Abrupt> {
        let ops = self.promise_ops()?;
        let value = self
            .host
            .suspend
            .queues
            .get(&generator)
            .and_then(|q| q.front())
            .map(|r| r.value)
            .ok_or(Abrupt::Internal("async generator queue is empty"))?;
        match (ops.resolve)(self, value) {
            Err(Abrupt::Throw(e)) => {
                self.set_sus_state(generator, COMPLETED)?;
                self.complete_step(generator, Completion::Throw(e), true)?;
                self.drain_queue(generator)
            }
            Err(other) => Err(other),
            Ok(promise) => {
                let f = self.reaction(Reaction::ReturnFulfilled, generator)?;
                let r = self.reaction(Reaction::ReturnRejected, generator)?;
                (ops.then)(self, promise, f, r)
            }
        }
    }

    /// AsyncGeneratorDrainQueue ( generator ) §27.6.3.10†:
    /// 1. Assert: generator.[[AsyncGeneratorState]] is completed.
    /// 2. Let queue be generator.[[AsyncGeneratorQueue]].
    /// 3. If queue is empty, return unused.
    /// 4. Let done be false.
    /// 5. Repeat, while done is false,
    ///    a. Let next be the first element of queue.
    ///    b. Let completion be Completion(next.[[Completion]]).
    ///    c. If completion is a return completion, then
    ///    i. Set generator.[[AsyncGeneratorState]] to awaiting-return.
    ///    ii. Perform AsyncGeneratorAwaitReturn(generator).
    ///    iii. Set done to true.
    ///    d. Else,
    ///    i. If completion is a normal completion, then 1. Set completion to
    ///    NormalCompletion(undefined).
    ///    ii. Perform AsyncGeneratorCompleteStep(generator, completion,
    ///    true).
    ///    iii. If queue is empty, set done to true.
    fn drain_queue(&mut self, generator: Value) -> Result<(), Abrupt> {
        loop {
            let front = self
                .host
                .suspend
                .queues
                .get(&generator)
                .and_then(|q| q.front().copied());
            let Some(next) = front else {
                return Ok(());
            };
            match next.mode {
                ResumeMode::Return => {
                    self.set_sus_state(generator, AWAITING_RETURN)?;
                    return self.await_return(generator);
                }
                ResumeMode::Next => {
                    self.complete_step(generator, Completion::Normal(Value::UNDEFINED), true)?;
                }
                ResumeMode::Throw => {
                    self.complete_step(generator, Completion::Throw(next.value), true)?;
                }
            }
        }
    }

    // -----------------------------------------------------------------
    // The iteration ops of `yield*` and `for await`
    // -----------------------------------------------------------------

    /// `GetAsyncIterator`: GetIterator ( obj, async ) §7.4.4† (see
    /// [`crate::ops::Op::GetAsyncIterator`]):
    /// 1. If kind is async, then
    ///    a. Let method be ? GetMethod(obj, @@asyncIterator).
    ///    b. If method is undefined, then
    ///    i. Let syncMethod be ? GetMethod(obj, @@iterator).
    ///    ii. If syncMethod is undefined, throw a TypeError exception.
    ///    iii. Let syncIteratorRecord be ? GetIteratorFromMethod(obj,
    ///    syncMethod).
    ///    iv. Return CreateAsyncFromSyncIterator(syncIteratorRecord).
    /// 3. If method is undefined, throw a TypeError exception.
    /// 4. Return ? GetIteratorFromMethod(obj, method).
    ///
    /// CreateAsyncFromSyncIterator ( syncIteratorRecord ) §27.1.6.1†:
    /// 1. Let asyncIterator be OrdinaryObjectCreate(
    ///    %AsyncFromSyncIteratorPrototype%, « [[SyncIteratorRecord]] »).
    /// 2. Set asyncIterator.[[SyncIteratorRecord]] to syncIteratorRecord.
    /// 3. Let nextMethod be ! Get(asyncIterator, "next").
    /// 4. Let iteratorRecord be the Iterator Record { [[Iterator]]:
    ///    asyncIterator, [[NextMethod]]: nextMethod, [[Done]]: false }.
    /// 5. Return iteratorRecord.
    pub(crate) fn get_async_iterator(&mut self, obj: Value) -> Result<Value, Abrupt> {
        if obj == Value::UNDEFINED || obj == Value::NULL {
            return Err(self.type_error("value is not async iterable"));
        }
        let ka = self.well_known_key(clazel_js_heap::symbol::ASYNC_ITERATOR)?;
        let method = self.get_property(obj, ka, None)?;
        if method != Value::UNDEFINED && method != Value::NULL {
            if !self.heap.is_callable(method) {
                return Err(self.type_error("Symbol.asyncIterator is not a function"));
            }
            return self.get_iterator_from_method(obj, method);
        }
        let ki = self.well_known_key(clazel_js_heap::symbol::ITERATOR)?;
        let sync = self.get_property(obj, ki, None)?;
        if sync == Value::UNDEFINED || sync == Value::NULL {
            return Err(self.type_error("object is not async iterable"));
        }
        if !self.heap.is_callable(sync) {
            return Err(self.type_error("Symbol.iterator is not a function"));
        }
        let record = self.get_iterator_from_method(obj, sync)?;
        let (iterator, next) = match self.heap.iter_record(record) {
            Some(IterRecord::Protocol { iterator, next, .. }) => (*iterator, *next),
            _ => return Err(Abrupt::Internal("iterator record")),
        };
        let proto = self.intrinsic(Intrinsic::AsyncFromSyncIteratorPrototype);
        let proto = if self.heap.is_object(proto) {
            proto
        } else {
            return Err(Abrupt::NotYet(
                "for await over a sync iterable without the built-ins".into(),
            ));
        };
        let ai = self.new_host_object(proto, TAG_ASYNC_FROM_SYNC, vec![iterator, next], None)?;
        let kn = self.atoms.k_next;
        let next_method = self.get_property(ai, kn, None)?;
        self.new_iterator_record(ai, next_method)
    }

    /// `IterCallMethod` (see [`crate::ops::Op::IterCallMethod`]): the
    /// iterator's `next` (`which` 0 and 4), `throw` (1) or `return` (2 and
    /// 3), with GetMethod (§7.3.10†) for the last two: "1. Let func be ?
    /// GetV(V, P). 2. If func is either undefined or null, return undefined.
    /// 3. If IsCallable(func) is false, throw a TypeError exception."
    /// `Some` is the call's result; `None` when the method is not there.
    pub(crate) fn iter_call_method(
        &mut self,
        record: Value,
        arg: Value,
        which: u32,
    ) -> Result<Option<Value>, Abrupt> {
        let (iterator, next) = match self.heap.iter_record(record) {
            Some(IterRecord::Protocol { iterator, next, .. }) => (*iterator, *next),
            _ => {
                return Err(Abrupt::Internal(
                    "IterCallMethod without an iterator record",
                ));
            }
        };
        let with_arg = matches!(which, 0..=2);
        let args: &[Value] = if with_arg { &[arg] } else { &[] };
        let method = match which {
            0 | 4 => {
                if !self.heap.is_callable(next) {
                    return Err(self.type_error("iterator.next is not a function"));
                }
                next
            }
            1..=3 => {
                let name = if which == 1 { "throw" } else { "return" };
                let key = self.heap.intern_str(name)?;
                let m = self.get_property(iterator, key, None)?;
                if m == Value::UNDEFINED || m == Value::NULL {
                    return Ok(None);
                }
                if !self.heap.is_callable(m) {
                    return Err(self.type_error(&format!("iterator.{name} is not a function")));
                }
                m
            }
            _ => return Err(Abrupt::Internal("IterCallMethod which")),
        };
        self.call(method, iterator, args).map(Some)
    }

    /// `IterComplete`: "If result is not an Object, throw a TypeError
    /// exception", then IteratorComplete ( iteratorResult ) §7.4.7†: "Return
    /// ToBoolean(? Get(iteratorResult, "done"))".
    pub(crate) fn iter_complete(&mut self, result: Value) -> Result<bool, Abrupt> {
        if !self.heap.is_object(result) {
            return Err(self.type_error("Iterator result is not an object"));
        }
        let kd = self.atoms.k_done;
        let d = self.get_property(result, kd, None)?;
        Ok(self.to_boolean(d))
    }

    /// `IterValue`: IteratorValue ( iteratorResult ) §7.4.8†: "Return ?
    /// Get(iteratorResult, "value")".
    pub(crate) fn iter_value(&mut self, result: Value) -> Result<Value, Abrupt> {
        let kv = self.atoms.k_value;
        self.get_property(result, kv, None)
    }

    /// Runs one of this module's ops, `None` for any other.
    pub(crate) fn step_suspend(&mut self, ins: &Instr) -> Result<Option<Flow>, Abrupt> {
        let next = self.pc.saturating_add(1);
        match *ins {
            Instr::GeneratorStart => self.op_generator_start().map(Some),
            Instr::Yield { src, value, mode } => self.op_yield(src, value, mode, false).map(Some),
            Instr::YieldDelegate { src, value, mode } => {
                self.op_yield(src, value, mode, true).map(Some)
            }
            Instr::Await { src, value, mode } => self.op_await(src, value, mode).map(Some),
            Instr::GetAsyncIterator { dst, src } => {
                let v = self.r(src)?;
                let rec = self.get_async_iterator(v)?;
                self.w(dst, rec)?;
                self.pc = next;
                Ok(Some(Flow::Continue))
            }
            Instr::IterCallMethod {
                dst,
                found,
                iter,
                arg,
                which,
            } => {
                let rec = self.r(iter)?;
                let a = self.r(arg)?;
                match self.iter_call_method(rec, a, which)? {
                    Some(v) => {
                        self.w(dst, v)?;
                        self.w(found, Value::TRUE)?;
                    }
                    None => self.w(found, Value::FALSE)?,
                }
                self.pc = next;
                Ok(Some(Flow::Continue))
            }
            Instr::IterComplete { done, result } => {
                let r = self.r(result)?;
                let d = self.iter_complete(r)?;
                self.w(done, Value::boolean(d))?;
                self.pc = next;
                Ok(Some(Flow::Continue))
            }
            Instr::IterValue { dst, result } => {
                let r = self.r(result)?;
                let v = self.iter_value(r)?;
                self.w(dst, v)?;
                self.pc = next;
                Ok(Some(Flow::Continue))
            }
            _ => Ok(None),
        }
    }
}

/// The value a resumption sends: the reaction's argument.
fn first(args: &[Value]) -> Value {
    args.first().copied().unwrap_or(Value::UNDEFINED)
}

/// The object a reaction function captured.
fn captured(vm: &Vm) -> Result<Value, Abrupt> {
    vm.function_slot(0)
        .ok_or(Abrupt::Internal("reaction without its object"))
}

/// Await §6.2.3.1† step 3, the fulfilled closure: "a. Let prevContext be the
/// running execution context. b. Suspend prevContext. c. Push asyncContext
/// onto the execution context stack; asyncContext is now the running
/// execution context. d. Resume the suspended evaluation of asyncContext
/// using NormalCompletion(v) as the result of the operation that suspended
/// it. ... f. Return undefined."
fn await_fulfilled(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let obj = captured(vm)?;
    vm.run_resumed(obj, first(args), ResumeMode::Next)?;
    Ok(Value::UNDEFINED)
}

/// Await §6.2.3.1† step 5, the rejected closure: as step 3 with
/// ThrowCompletion(reason).
fn await_rejected(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let obj = captured(vm)?;
    vm.run_resumed(obj, first(args), ResumeMode::Throw)?;
    Ok(Value::UNDEFINED)
}

/// AsyncGeneratorAwaitReturn §27.6.3.9† step 11, fulfilledClosure ( value ):
/// a. Assert: generator.[[AsyncGeneratorState]] is awaiting-return.
/// b. Set generator.[[AsyncGeneratorState]] to completed.
/// c. Let result be NormalCompletion(value).
/// d. Perform AsyncGeneratorCompleteStep(generator, result, true).
/// e. Perform AsyncGeneratorDrainQueue(generator).
/// f. Return undefined.
fn return_fulfilled(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let g = captured(vm)?;
    vm.set_sus_state(g, COMPLETED)?;
    vm.complete_step(g, Completion::Normal(first(args)), true)?;
    vm.drain_queue(g)?;
    Ok(Value::UNDEFINED)
}

/// AsyncGeneratorAwaitReturn §27.6.3.9† step 13, rejectedClosure ( reason ):
/// as step 11 with ThrowCompletion(reason).
fn return_rejected(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let g = captured(vm)?;
    vm.set_sus_state(g, COMPLETED)?;
    vm.complete_step(g, Completion::Throw(first(args)), true)?;
    vm.drain_queue(g)?;
    Ok(Value::UNDEFINED)
}
