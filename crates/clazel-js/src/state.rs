//! What a [`Runtime`](crate::Runtime) keeps besides the VM, and how Rust
//! closures become the VM's native functions.
//!
//! # Where the state lives
//!
//! A native function of the VM ([`clazel_js_vm::interp::NativeFn`]) is a plain
//! function pointer that receives `&mut Vm` and nothing else, so a closure has
//! nowhere to be captured. The runtime therefore keeps its state inside the VM,
//! in the slot [`Vm::set_embedder`] gives, and one function,
//! [`trampoline`], is the native behind every closure: it reads
//! [`Vm::active_function`] to find which closure the VM is calling, takes the
//! closure out of the table, builds a [`Scope`] over the same `&mut Vm`, and
//! runs it. A [`Scope`] is just a `&mut Vm` and the runtime's identity; all the
//! rest is looked up in [`State`] when needed.
//!
//! # Re-entrancy
//!
//! The table holds each closure in an [`Arc`], and a call clones the `Arc`
//! out of the table before it runs the closure, because the table is inside
//! the VM that the closure borrows. A native function that JavaScript
//! re-enters while it is still running (it called a script that called it)
//! is cloned out again and runs nested, as the contract promises ("a native
//! function can be re-entered"). Sharing the closure between the two calls
//! is why [`NativeFn`] is `Sync` (the README's open question 14).
//!
//! # Errors across the VM
//!
//! The VM's [`Abrupt`] has a thrown value, "terminated", "out of memory" and
//! two uncatchable internal kinds. The API's [`Error`] has more. A thrown
//! value, [`Error::Terminated`] and [`Error::OutOfMemory`] cross as themselves;
//! any other [`Error`] a closure returns is parked in [`State::pending`] and
//! crosses as `Abrupt::Internal`, which JavaScript cannot catch, and
//! [`Scope::err`] gives it back unchanged at the first Rust caller.

use std::any::Any;
use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

use clazel_js_heap::value::Value;
use clazel_js_vm::interp::{Abrupt, Vm};

use crate::error::{Error, Exception};
use crate::host::{Host, Job};
use crate::native::{Args, HostObject, NativeFn};
use crate::runtime::Limits;
use crate::scope::Scope;
use crate::value::Handle;

/// Everything the runtime keeps in the VM's embedder slot.
pub(crate) struct State {
    /// The runtime's identity: handles keep it alive.
    pub(crate) token: Arc<()>,
    /// The token's address, which names the runtime in a `Local`.
    pub(crate) id: usize,
    pub(crate) host: Box<dyn Host>,
    pub(crate) limits: Limits,
    /// The closures behind native functions, by the function object's bits.
    /// `None` while the closure runs (see the module docs).
    pub(crate) natives: HashMap<u64, Arc<NativeFn>>,
    /// The accessors defined with `Scope::define_accessor` whose function
    /// objects have not been needed yet, by the number their property's
    /// lazy pair holds; `None` once [`make_lazy_accessor`] has made them.
    pub(crate) lazy_accessors: Vec<Option<LazyAccessor>>,
    /// The Rust data of host objects, by the object's bits.
    pub(crate) host_objects: HashMap<u64, Box<dyn HostObject>>,
    pub(crate) realm_host_defined: Option<Box<dyn Any + Send>>,
    /// `Source::host_defined` of each compiled script, by its code index.
    pub(crate) script_host_defined: HashMap<u32, Box<dyn Any + Send>>,
    /// Whether `create_realm` has handed out the VM's one realm.
    pub(crate) realm_made: bool,
    /// The engine's own job queue (see `Scope::enqueue_job_internal`).
    pub(crate) jobs: VecDeque<Job>,
    /// How many closures are running now.
    pub(crate) native_depth: u32,
    /// The error an infallible constructor could not report; the next
    /// operation that can fail returns it.
    pub(crate) deferred: Option<Error>,
    /// An error parked while it crosses the VM as `Abrupt::Internal`.
    pub(crate) pending: Option<Error>,
}

/// The closures of an accessor property whose function objects are made
/// when they are first needed (`Scope::define_accessor`).
pub(crate) struct LazyAccessor {
    /// The property's name: the getter is named `get <name>` and the setter
    /// `set <name>`.
    pub(crate) name: Box<str>,
    pub(crate) get: Arc<NativeFn>,
    pub(crate) set: Option<Arc<NativeFn>>,
}

/// The name of an accessor's getter or setter function (ECMA-262 §10.2.9†
/// SetFunctionName step 5: "If prefix is present, then a. Set name to the
/// string-concatenation of prefix, the code unit 0x0020 (SPACE), and name").
pub(crate) fn accessor_function_name(prefix: &str, name: &str) -> String {
    format!("{prefix} {name}")
}

/// The VM's maker of lazy accessor pairs (`Vm::set_lazy_accessor_maker`):
/// the getter and setter function objects of entry `id` of
/// [`State::lazy_accessors`], made exactly as `Scope::define_accessor`
/// makes them when it cannot defer (`get <name>` of length 0, `set <name>`
/// of length 1 or `undefined`). The entry is cleared only once both exist,
/// so a failure (the heap limit) leaves the pair lazy and a later use tries
/// again.
pub(crate) fn make_lazy_accessor(vm: &mut Vm, id: u32) -> Result<(Value, Value), Abrupt> {
    const GONE: Abrupt = Abrupt::Internal("a lazy accessor of no runtime");
    let index = usize::try_from(id).map_err(|_| GONE)?;
    let (name, get, set) = vm
        .embedder::<State>()
        .and_then(|state| state.lazy_accessors.get(index)?.as_ref())
        .map(|entry| {
            (
                entry.name.clone(),
                Arc::clone(&entry.get),
                entry.set.clone(),
            )
        })
        .ok_or(GONE)?;
    let getter = vm.new_native(&accessor_function_name("get", &name), 0, trampoline)?;
    let setter = match set {
        Some(_) => vm.new_native(&accessor_function_name("set", &name), 1, trampoline)?,
        None => Value::UNDEFINED,
    };
    let state = vm.embedder_mut::<State>().ok_or(GONE)?;
    state.natives.insert(getter.bits(), get);
    if let Some(set) = set {
        state.natives.insert(setter.bits(), set);
    }
    if let Some(entry) = state.lazy_accessors.get_mut(index) {
        *entry = None;
    }
    Ok((getter, setter))
}

impl State {
    pub(crate) fn new(host: Box<dyn Host>, limits: Limits) -> State {
        let token = Arc::new(());
        let id = Arc::as_ptr(&token) as usize;
        State {
            token,
            id,
            host,
            limits,
            natives: HashMap::new(),
            lazy_accessors: Vec::new(),
            host_objects: HashMap::new(),
            realm_host_defined: None,
            script_host_defined: HashMap::new(),
            realm_made: false,
            jobs: VecDeque::new(),
            native_depth: 0,
            deferred: None,
            pending: None,
        }
    }
}

pub(crate) const NOT_YET: &str = "an operation the interpreter does not implement yet";

/// The VM's reason a run ended, as the API's error. A thrown value becomes an
/// [`Exception`] holding a [`Handle`].
pub(crate) fn abrupt_to_error(vm: &mut Vm, abrupt: Abrupt) -> Error {
    let Some(state) = vm.embedder_mut::<State>() else {
        return Error::WrongRuntime;
    };
    match abrupt {
        Abrupt::Throw(value) => Error::Thrown(Exception::from_handle(Handle::new(
            state.token.clone(),
            value,
        ))),
        Abrupt::Terminated => Error::Terminated,
        Abrupt::OutOfMemory => Error::OutOfMemory,
        Abrupt::NotYet(_) => Error::NotImplemented(NOT_YET),
        // An error a closure returned, parked while it crossed the VM; or,
        // if there is none, a broken invariant of the VM, which this API can
        // only call a stale reference.
        Abrupt::Internal(_) => state.pending.take().unwrap_or(Error::StaleHandle),
    }
}

/// The API's error as the VM's reason to stop, for a closure's result.
fn error_to_abrupt(vm: &mut Vm, error: Error) -> Abrupt {
    let Some(state) = vm.embedder_mut::<State>() else {
        return Abrupt::Internal("no runtime state");
    };
    match error {
        Error::Thrown(exception) => {
            if Arc::ptr_eq(exception.value().token(), &state.token) {
                Abrupt::Throw(exception.value().value())
            } else {
                state.pending = Some(Error::WrongRuntime);
                Abrupt::Internal("an exception of another runtime")
            }
        }
        Error::Terminated => Abrupt::Terminated,
        Error::OutOfMemory => Abrupt::OutOfMemory,
        other => {
            state.pending = Some(other);
            Abrupt::Internal("an error of the embedder")
        }
    }
}

/// The native function behind every closure made by `Scope::function`.
pub(crate) fn trampoline(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let callee = vm.active_function();
    let new_target = vm.new_target();
    let key = callee.bits();

    // Take the closure out, and count the call.
    let taken = {
        let Some(state) = vm.embedder_mut::<State>() else {
            return Err(Abrupt::Internal("no runtime state"));
        };
        if state.native_depth >= state.limits.native_depth {
            None
        } else {
            match state.natives.get(&key) {
                Some(f) => {
                    let f = Arc::clone(f);
                    state.native_depth = state.native_depth.saturating_add(1);
                    Some(Ok((state.id, f)))
                }
                None => Some(Err(Abrupt::Internal("a native function of no runtime"))),
            }
        }
    };
    let (runtime, f) = match taken {
        None => return Err(vm.range_error("too many nested native calls")),
        Some(Err(abrupt)) => return Err(abrupt),
        Some(Ok(pair)) => pair,
    };

    let result = {
        let mut scope = Scope::new(vm, runtime);
        let arguments = Args::new(runtime, this, args, new_target);
        f(&mut scope, &arguments).map(|local| (local.value(), local.runtime()))
    };

    drop(f);
    if let Some(state) = vm.embedder_mut::<State>() {
        state.native_depth = state.native_depth.saturating_sub(1);
    }
    match result {
        Ok((value, rt)) if rt == runtime => Ok(value),
        Ok(_) => Err(error_to_abrupt(vm, Error::WrongRuntime)),
        Err(error) => Err(error_to_abrupt(vm, error)),
    }
}
