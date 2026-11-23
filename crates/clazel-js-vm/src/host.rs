//! Objects with internal slots, native functions with captured values, and the
//! job queue: what the built-ins of `clazel-js-builtins` need to be written as
//! plain functions over a [`Vm`] (phase-7.md item 7.9: `Promise` and the job
//! queue; item 7.10: the `RegExp` object).
//!
//! # Modelling choices
//!
//! - **Internal slots.** The standard gives an object internal slots
//!   (`[[PromiseState]]`, `[[RegExpMatcher]]`, ...). A [`ObjKind::Host`] object
//!   names a row of the VM's table of host objects: a tag the built-in chose, a
//!   list of [`Value`] slots, and one optional Rust value (a compiled pattern).
//!   The slots are ordinary heap references, so nothing here hides a value from
//!   the collector item 7.6 will add (it traces the slots).
//! - **Closures of the standard.** A [`crate::interp::NativeFn`] is a plain
//!   function pointer. The "built-in function that has captured state" of
//!   §10.3.1† (Promise resolving functions, `Promise.all`'s resolve element
//!   functions, ...) is a native function object that also has slots, read with
//!   [`Vm::function_slot`] by the function itself.
//! - **The job queue** (§9.5†, HostEnqueuePromiseJob). A job is a callable and
//!   its arguments; [`Vm::run_jobs`] runs the queue to empty, in order, as a
//!   host does at a microtask checkpoint. The VM never runs it by itself: the
//!   embedder decides when the JS stack is empty (the HTML standard's "perform
//!   a microtask checkpoint").
//! - **Uncaught job exceptions.** A job that throws is reported to the host by
//!   leaving the exception in [`Vm::take_job_errors`]; the queue goes on, as
//!   the standard's loop does after HostReportErrors.

use crate::heap::ObjKind;
use crate::interp::{Abrupt, Vm};
use clazel_js_heap::value::Value;
use std::any::Any;
use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

/// The internal slots of one host object.
#[derive(Debug)]
pub(crate) struct HostObject {
    pub(crate) tag: u32,
    pub(crate) slots: Vec<Value>,
    pub(crate) data: Option<Arc<dyn Any + Send + Sync>>,
}

/// A pending job: a call of `callee` with `args` and `this` `undefined`.
#[derive(Debug)]
pub(crate) struct Job {
    pub(crate) callee: Value,
    pub(crate) args: Vec<Value>,
}

/// The state this module adds to a [`Vm`].
#[derive(Debug, Default)]
pub(crate) struct HostState {
    pub(crate) objects: Vec<HostObject>,
    pub(crate) function_slots: HashMap<Value, Vec<Value>>,
    pub(crate) jobs: VecDeque<Job>,
    pub(crate) job_errors: Vec<Value>,
}

/// The most jobs one [`Vm::run_jobs`] runs: a promise chain that enqueues
/// another job from every job never ends, like an infinite loop (the step
/// budget and the terminator also stop it).
pub const MAX_JOBS_PER_CHECKPOINT: u64 = 1 << 24;

impl Vm {
    /// A new object of the prototype `proto` with internal slots: `tag` says
    /// what the built-in made it (the built-in chooses its tags), `slots` are
    /// its `[[...]]` values, `data` is a Rust value that has no place in a
    /// slot.
    ///
    /// # Errors
    /// [`Abrupt::OutOfMemory`].
    pub fn new_host_object(
        &mut self,
        proto: Value,
        tag: u32,
        slots: Vec<Value>,
        data: Option<Arc<dyn Any + Send + Sync>>,
    ) -> Result<Value, Abrupt> {
        let index = u32::try_from(self.host.objects.len()).map_err(|_| Abrupt::OutOfMemory)?;
        let o = self.heap.new_object(proto, ObjKind::Host(index))?;
        self.host.objects.push(HostObject { tag, slots, data });
        Ok(o)
    }

    /// Turns the ordinary object `obj` (made by
    /// [`Vm::create_from_constructor`], so that its prototype comes from
    /// NewTarget) into a host object: the internal slots of the standard's
    /// OrdinaryCreateFromConstructor "internalSlotsList".
    ///
    /// # Errors
    /// [`Abrupt::OutOfMemory`], or [`Abrupt::Internal`] if `obj` is not an
    /// ordinary object.
    pub fn into_host_object(
        &mut self,
        obj: Value,
        tag: u32,
        slots: Vec<Value>,
        data: Option<Arc<dyn Any + Send + Sync>>,
    ) -> Result<(), Abrupt> {
        let index = u32::try_from(self.host.objects.len()).map_err(|_| Abrupt::OutOfMemory)?;
        match self.heap.obj_mut(obj) {
            Some(o) if o.kind == ObjKind::Plain => o.kind = ObjKind::Host(index),
            _ => {
                return Err(Abrupt::Internal(
                    "into_host_object of a non-ordinary object",
                ));
            }
        }
        self.host.objects.push(HostObject { tag, slots, data });
        Ok(())
    }

    /// Appends a slot to a host object and returns its index (a built-in's
    /// growable List, such as the values of `Promise.all`).
    pub fn push_host_slot(&mut self, obj: Value, v: Value) -> Option<usize> {
        let h = self.host_object_mut(obj)?;
        h.slots.push(v);
        h.slots.len().checked_sub(1)
    }

    /// All the slots of a host object.
    #[must_use]
    pub fn host_slots(&self, obj: Value) -> Option<&[Value]> {
        self.host_object(obj).map(|h| h.slots.as_slice())
    }

    fn host_object(&self, obj: Value) -> Option<&HostObject> {
        match self.heap.obj(obj)?.kind {
            ObjKind::Host(i) => self.host.objects.get(usize::try_from(i).ok()?),
            _ => None,
        }
    }

    fn host_object_mut(&mut self, obj: Value) -> Option<&mut HostObject> {
        match self.heap.obj(obj)?.kind {
            ObjKind::Host(i) => self.host.objects.get_mut(usize::try_from(i).ok()?),
            _ => None,
        }
    }

    /// The tag of a host object, or `None` for any other value.
    #[must_use]
    pub fn host_tag(&self, obj: Value) -> Option<u32> {
        self.host_object(obj).map(|h| h.tag)
    }

    /// Slot `i` of a host object.
    #[must_use]
    pub fn host_slot(&self, obj: Value, i: usize) -> Option<Value> {
        self.host_object(obj)?.slots.get(i).copied()
    }

    /// Sets slot `i` of a host object; `false` if there is no such slot.
    pub fn set_host_slot(&mut self, obj: Value, i: usize, v: Value) -> bool {
        match self.host_object_mut(obj).and_then(|h| h.slots.get_mut(i)) {
            Some(s) => {
                *s = v;
                true
            }
            None => false,
        }
    }

    /// The Rust value of a host object (a clone of the shared pointer).
    #[must_use]
    pub fn host_data(&self, obj: Value) -> Option<Arc<dyn Any + Send + Sync>> {
        self.host_object(obj)?.data.clone()
    }

    /// Replaces the Rust value of a host object; `false` if `obj` is not one.
    pub fn set_host_data(&mut self, obj: Value, data: Option<Arc<dyn Any + Send + Sync>>) -> bool {
        match self.host_object_mut(obj) {
            Some(h) => {
                h.data = data;
                true
            }
            None => false,
        }
    }

    /// Gives a function object (made by [`Vm::new_native`] or
    /// [`Vm::new_native_constructor`]) the slots a native reads with
    /// [`Vm::function_slot`] (the captured values of §10.3.1†'s closures).
    pub fn set_function_slots(&mut self, func: Value, slots: Vec<Value>) {
        self.host.function_slots.insert(func, slots);
    }

    /// Slot `i` of the running native function (see
    /// [`Vm::set_function_slots`]).
    #[must_use]
    pub fn function_slot(&self, i: usize) -> Option<Value> {
        self.host
            .function_slots
            .get(&self.active_function())?
            .get(i)
            .copied()
    }

    /// Sets slot `i` of the running native function; `false` if it has no
    /// such slot.
    pub fn set_function_slot(&mut self, i: usize, v: Value) -> bool {
        let f = self.active_function();
        match self
            .host
            .function_slots
            .get_mut(&f)
            .and_then(|s| s.get_mut(i))
        {
            Some(s) => {
                *s = v;
                true
            }
            None => false,
        }
    }

    /// HostEnqueuePromiseJob, §9.5.5†: appends a job that calls `callee` with
    /// `args` (and `this` `undefined`) to the queue.
    pub fn enqueue_job(&mut self, callee: Value, args: Vec<Value>) {
        self.host.jobs.push_back(Job { callee, args });
    }

    /// How many jobs are waiting.
    #[must_use]
    pub fn pending_jobs(&self) -> usize {
        self.host.jobs.len()
    }

    /// Runs the job queue until it is empty (a microtask checkpoint): each
    /// job in the order enqueued, jobs enqueued by a job after those already
    /// waiting. A job that throws is kept in [`Vm::take_job_errors`] and the
    /// queue goes on.
    ///
    /// # Errors
    /// An error JS cannot catch ([`Abrupt::Terminated`], [`Abrupt::NotYet`],
    /// [`Abrupt::OutOfMemory`], [`Abrupt::Internal`]) ends the run; jobs not
    /// yet run stay queued. More than [`MAX_JOBS_PER_CHECKPOINT`] jobs end it
    /// with [`Abrupt::Terminated`].
    pub fn run_jobs(&mut self) -> Result<(), Abrupt> {
        let mut ran = 0u64;
        while let Some(job) = self.host.jobs.pop_front() {
            ran = ran.saturating_add(1);
            if ran > MAX_JOBS_PER_CHECKPOINT || self.terminator.is_set() {
                self.host.jobs.push_front(job);
                return Err(Abrupt::Terminated);
            }
            match self.call(job.callee, Value::UNDEFINED, &job.args) {
                Ok(_) => {}
                Err(Abrupt::Throw(e)) => self.host.job_errors.push(e),
                Err(other) => return Err(other),
            }
        }
        Ok(())
    }

    /// The exceptions that escaped jobs since the last call, oldest first.
    pub fn take_job_errors(&mut self) -> Vec<Value> {
        std::mem::take(&mut self.host.job_errors)
    }
}
