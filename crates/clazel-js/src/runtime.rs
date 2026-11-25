//! [`Runtime`], its [`Config`] and [`Limits`], and the [`Terminator`].

use core::cell::Cell;
use core::marker::PhantomData;

use clazel_js_vm::interp::{Abrupt, Config as VmConfig, Terminator as VmTerminator, Vm};

use crate::error::{Error, Result};
use crate::host::{DefaultHost, Host};
use crate::scope::{CELL_BYTES, Scope};
use crate::state::State;

/// Every limit is the embedder's to set, and the engine has no default for
/// any of them (phase-7.md, "Limits and stopping").
///
/// A struct literal must name every field, so adding a limit later makes
/// every embedder choose a value. The numbers the browser picks are not in
/// this crate. Each limit has its own report, listed with the field.
///
/// ```
/// use clazel_js::Limits;
///
/// // A test harness with limits generous enough never to matter, and one
/// // that is not: a small heap that is meant to be hit.
/// let relaxed = Limits::unlimited();
/// let strict = Limits {
///     heap_bytes: 64 << 20,
///     ..relaxed
/// };
/// assert_eq!(strict.heap_bytes, 64 << 20);
/// assert_eq!(strict.native_depth, relaxed.native_depth);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    /// Heap size in bytes, as the heap counts them (an estimate: 64 bytes a
    /// cell, a string's code units at one or two bytes each, 32 bytes an
    /// added property; [`Runtime::heap_used`] reads the count). An allocation
    /// that would pass it throws a `RangeError`, which JavaScript can catch;
    /// the error itself comes from a 64 KiB reserve past the limit, and when
    /// that is spent too the call ends in [`Error::OutOfMemory`]. phase-7.md
    /// asks for a full collection first; the interpreter does not use the
    /// collector yet, so nothing is ever freed and the error comes at once.
    /// The built-ins count against it, so a limit too small for them makes
    /// [`Runtime::new`] fail with `OutOfMemory`.
    pub heap_bytes: u64,
    /// Size of the value-stack region in bytes (8 a slot). JavaScript calls
    /// JavaScript in this region, not on the host stack; passing it throws a
    /// `RangeError` ("Maximum call stack size exceeded").
    pub value_stack_bytes: u64,
    /// How many native functions may be on the call stack at once, counting
    /// built-ins that call back into JavaScript such as `Array.prototype.map`
    /// and the embedder's own. Re-entries of the interpreter from inside an
    /// operation (the `toString` that `'' + o` calls) are bounded by one more
    /// than this. Passing either throws a `RangeError`.
    ///
    /// Each level takes host stack: about 40 KB in an unoptimised build and
    /// 1.5 KB in an optimised one (measured; see `clazel-js-vm`'s
    /// `DEFAULT_NATIVE_DEPTH`). The thread the runtime runs on must hold this
    /// many levels, or a deep enough recursion through natives overflows the
    /// host stack and aborts the process.
    pub native_depth: u32,
    /// Bytes of generated machine code the JIT may hold. Passing it stops
    /// compiling and leaves functions to the interpreter; it is not an error.
    /// Ignored when [`JitMode::Off`], which is the only mode so far.
    pub code_bytes: u64,
    /// Entries in the RegExp matcher's backtrack stack (16 to 24 bytes each).
    /// Passing it throws a `RangeError` from the match (the VM stores it, and
    /// `clazel-js-builtins`' `regexp::backtrack_limit` hands it to the matcher).
    pub regexp_backtrack_entries: u64,
    /// Nesting depth of source text (the height of its parse tree) and of
    /// `JSON.parse` and `JSON.stringify` (levels of arrays and objects).
    /// Passing it throws a `SyntaxError` for source and for `JSON.parse`
    /// (phase-7.md 7.11's listed deviation), and a `RangeError` for
    /// `JSON.stringify`. Each also has a fixed bound of its own that keeps
    /// its recursion off the end of the host stack, and the smaller applies:
    /// 1024 for source, 512 for `JSON.parse`, 128 for `JSON.stringify`.
    pub nesting_depth: u32,
}

impl Limits {
    /// Limits that no ordinary program reaches, for tests and for a runner
    /// that wants the engine's behaviour without its limits getting in the
    /// way. This is a named choice, not a default: nothing in the engine
    /// calls it.
    pub const fn unlimited() -> Limits {
        Limits {
            heap_bytes: u64::MAX,
            value_stack_bytes: u64::MAX,
            native_depth: u32::MAX,
            code_bytes: u64::MAX,
            regexp_backtrack_entries: u64::MAX,
            nesting_depth: u32::MAX,
        }
    }

    /// Limits for running untrusted pages on a thread with a 2 MiB stack, in
    /// an optimised or an unoptimised build (phase-7.md 7.19). A named
    /// starting point, not a default: nothing in the engine calls it, and the
    /// browser sets its own.
    ///
    /// | Limit | Value | Error past it |
    /// |---|---|---|
    /// | `heap_bytes` | 512 MiB | `RangeError` |
    /// | `value_stack_bytes` | 4 MiB (512 Ki slots) | `RangeError` |
    /// | `native_depth` | 32 | `RangeError` |
    /// | `code_bytes` | 64 MiB | none (no JIT) |
    /// | `regexp_backtrack_entries` | 1 Mi | `RangeError` |
    /// | `nesting_depth` | 512 | `SyntaxError` (source, `JSON.parse`), `RangeError` (`JSON.stringify`) |
    ///
    /// ```
    /// use clazel_js::Limits;
    ///
    /// let page = Limits::recommended();
    /// assert_eq!(page.heap_bytes, 512 << 20);
    /// assert_eq!(page.native_depth, 32);
    /// ```
    pub const fn recommended() -> Limits {
        Limits {
            heap_bytes: 512 << 20,
            value_stack_bytes: 4 << 20,
            native_depth: 32,
            code_bytes: 64 << 20,
            regexp_backtrack_entries: 1 << 20,
            nesting_depth: 512,
        }
    }
}

/// Whether the JIT is on. Only [`Off`](JitMode::Off) exists until jit.md's
/// `clazel-jit` does; then a variant carrying a `CodeMapper` is added
/// (jit.md J.0(b)): the embedder's choice of how validated code becomes
/// executable. The interpreter is complete without it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub enum JitMode {
    /// Interpret only.
    #[default]
    Off,
}

/// What a [`Runtime`] is built from.
///
/// ```
/// use clazel_js::{Config, JitMode, Limits};
///
/// let config = Config::new(Limits::unlimited());
/// assert_eq!(config.jit, JitMode::Off);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Config {
    /// The limits. See [`Limits`].
    pub limits: Limits,
    /// Whether to use the JIT.
    pub jit: JitMode,
}

impl Config {
    /// A configuration with the given limits and the JIT off.
    pub const fn new(limits: Limits) -> Config {
        Config {
            limits,
            jit: JitMode::Off,
        }
    }
}

/// A handle that stops a [`Runtime`] from another thread.
///
/// - **How it works.** `terminate` sets a flag. The interpreter checks it at
///   loop back-edges and at calls, and JIT code checks it at the same points.
///   An evaluation that sees it ends with
///   [`Error::Terminated`](crate::Error::Terminated).
/// - **JavaScript cannot catch it.** `catch` does not run, and neither does
///   `finally`: running either would run JavaScript after being told to stop.
///   Native frames see `Err(Error::Terminated)` and must pass it on. One that
///   does not still stops at the next check, which raises it again.
/// - **It is sticky.** The flag stays set, so every later call into the same
///   `Runtime` also ends in `Terminated`, until [`Terminator::clear`] (an open
///   question in the README is whether a terminated runtime stays usable).
/// - **Cost.** The check is one relaxed atomic load. It is not a way to
///   interrupt a native function that is itself in a long loop; built-ins
///   check it too, and an embedder's native function should
///   [`Scope::check_terminated`] in a long loop.
/// - **It is the embedder's policy.** The browser still ends a stuck renderer
///   from outside, on the user's word (phase-7.md 7.0(g)), and may use this
///   later to keep the tab.
///
/// A `Terminator` is `Clone`, `Send` and `Sync`.
///
/// ```
/// use std::thread;
/// use std::time::Duration;
/// use clazel_js::{Config, DefaultHost, Limits, Realm, RealmOptions, Runtime};
///
/// fn run_until_stopped(rt: &mut Runtime, realm: &Realm) -> bool {
///     let terminator = rt.terminator();
///     let watchdog = thread::spawn(move || {
///         thread::sleep(Duration::from_millis(20));
///         terminator.terminate();
///     });
///     let result = rt.scope(|scope| {
///         scope.eval_script(realm, clazel_js::Source::new("loop.js", "for (;;) {}"))?;
///         Ok::<(), clazel_js::Error>(())
///     });
///     let _ = watchdog.join();
///     rt.terminator().clear();
///     matches!(result, Err(clazel_js::Error::Terminated))
/// }
/// # let mut rt = Runtime::new(Config::new(Limits::unlimited()), DefaultHost::new())?;
/// # let realm = rt.scope(|scope| scope.create_realm(RealmOptions::default()))?;
/// # assert!(run_until_stopped(&mut rt, &realm));
/// # Ok::<(), clazel_js::Error>(())
/// ```
#[derive(Clone, Debug, Default)]
pub struct Terminator {
    /// The interpreter's own flag, which its loop reads at back-edges and
    /// calls.
    flag: VmTerminator,
}

impl Terminator {
    /// Asks the runtime to stop. Safe to call from any thread, any number of
    /// times.
    pub fn terminate(&self) {
        self.flag.terminate();
    }

    /// Whether `terminate` has been called and not cleared.
    pub fn is_terminated(&self) -> bool {
        self.flag.is_set()
    }

    /// Lets the runtime run again. Call it after an evaluation has returned
    /// `Terminated`, never while one is running.
    pub fn clear(&self) {
        self.flag.reset();
    }
}

/// One ECMAScript agent: a heap, a job queue, limits and a [`Host`].
///
/// - **No global state.** Everything the engine knows lives in the `Runtime`,
///   with no `static` and no thread-local, so a process can hold many.
/// - **Threads.** A `Runtime` is `Send` and not `Sync`. It can move to another
///   thread between calls, and only one thread can use it at a time. The
///   browser runs one per renderer, on one thread, as phase-7.md 7.0(e)
///   decided. [`Terminator`] is the one piece usable from other threads.
///   `Host: Send` is what keeps this true, because the host lives inside.
/// - **Calls go through a scope.** [`Runtime::scope`] runs a closure with a
///   [`Scope`], and everything else is a method of that.
/// - **Dropping** frees the whole heap, runs each native closure's and host
///   object's destructor, and does not run any JavaScript (no finalizer).
///
/// ```compile_fail
/// use clazel_js::Runtime;
///
/// fn needs_sync<T: Sync>() {}
///
/// // Does not compile: a Runtime is not Sync.
/// fn check() { needs_sync::<Runtime>(); }
/// ```
///
/// The compiler gives a script no completion value yet, so `eval_script`
/// returns `undefined` and this example reads its result from a global (see
/// the README):
///
/// ```
/// use clazel_js::{Config, DefaultHost, Key, Limits, RealmOptions, Runtime, Source};
///
/// fn main() -> Result<(), clazel_js::Error> {
///     let mut rt = Runtime::new(Config::new(Limits::unlimited()), DefaultHost::new())?;
///     let realm = rt.scope(|scope| scope.create_realm(RealmOptions::default()))?;
///     let sum = rt.scope(|scope| {
///         scope.eval_script(&realm, Source::new("sum.js", "var sum = 1 + 2;"))?;
///         let global = scope.global(&realm)?;
///         let value = scope.get(global, Key::from("sum"))?;
///         Ok(scope.as_number(value))
///     })?;
///     assert_eq!(sum, Some(3.0));
///     rt.run_jobs()?;
///     Ok(())
/// }
/// ```
///
/// A `Runtime` moves to another thread as a whole:
///
/// ```
/// use clazel_js::Runtime;
///
/// fn assert_send<T: Send>() {}
/// fn check() { assert_send::<Runtime>(); }
/// check();
/// ```
pub struct Runtime {
    limits: Limits,
    terminator: Terminator,
    /// The VM, with the runtime's state (and so the host) in its embedder
    /// slot, see [`crate::state`].
    vm: Box<Vm>,
    /// What [`Runtime::host_mut`] answers with if the state is ever missing,
    /// which it cannot be: the method has no way to fail.
    fallback_host: DefaultHost,
    // `Cell` is `Send` and not `Sync`, which is the rule.
    _not_sync: PhantomData<Cell<()>>,
}

impl Runtime {
    /// Builds a runtime. The `host` is taken for the life of the runtime;
    /// reach it again with [`Runtime::host_mut`] or, from inside a native
    /// function, [`Scope::host_mut`].
    ///
    /// The VM and the built-ins are made here, so the one realm the VM has
    /// exists at once, and [`Scope::create_realm`] hands it out (the
    /// contract's "no realms" is not what a VM with one global can do). The
    /// limits are applied as [`Limits`] describes: `heap_bytes` is the VM
    /// heap's byte limit (and, at 64 bytes a cell, its arena's cell limit),
    /// `value_stack_bytes` the frame region's slot count (8 bytes a slot),
    /// `native_depth` the VM's bound on nested natives (and is also checked
    /// on every call of a closure made by [`Scope::function`]), and
    /// `nesting_depth` bounds the parse tree here and the JSON built-ins in
    /// the VM. `code_bytes` (no JIT) is accepted and not used, and
    /// `regexp_backtrack_entries` is stored in the VM, and the RegExp
    /// built-in's matcher takes it as its stack bound.
    pub fn new(config: Config, host: impl Host) -> Result<Runtime> {
        let limits = config.limits;
        // Limits the VM has a counterpart for: its arena counts cells (an
        // estimate of `CELL_BYTES` each) and its frame region counts 8-byte
        // slots. The VM clamps both to what it can address.
        let heap_cells = usize::try_from(limits.heap_bytes / CELL_BYTES).unwrap_or(usize::MAX);
        let region_slots = usize::try_from(limits.value_stack_bytes / 8).unwrap_or(usize::MAX);
        let mut vm = Vm::new(VmConfig {
            region_slots,
            heap_cells,
        })
        .map_err(vm_failure)?;
        // The limits the VM checks itself (phase-7.md 7.19), set before the
        // built-ins are installed so that they count against the heap too.
        vm.set_heap_limit(limits.heap_bytes);
        vm.set_native_depth_limit(limits.native_depth);
        vm.set_nesting_depth_limit(limits.nesting_depth);
        vm.set_regexp_backtrack_limit(limits.regexp_backtrack_entries);
        clazel_js_builtins::install(&mut vm).map_err(vm_failure)?;
        let terminator = Terminator {
            flag: vm.terminator(),
        };
        vm.set_embedder(State::new(Box::new(host), limits));
        vm.set_lazy_accessor_maker(crate::state::make_lazy_accessor);
        Ok(Runtime {
            limits,
            terminator,
            vm: Box::new(vm),
            fallback_host: DefaultHost::new(),
            _not_sync: PhantomData,
        })
    }

    /// Runs `f` with a [`Scope`]. Every [`Local`](crate::Local) made inside is
    /// rooted until `f` returns, and cannot leave it; what `f` returns must
    /// not borrow from the scope. This is the only way in.
    ///
    /// `f` cannot call `scope` again, because it has no access to the
    /// `Runtime`. Code that wants an inner scope uses [`Scope::nested`].
    pub fn scope<R>(&mut self, f: impl for<'s> FnOnce(&mut Scope<'s>) -> R) -> R {
        let runtime = self.runtime_id();
        let mut scope = Scope::new(&mut self.vm, runtime);
        f(&mut scope)
    }

    /// Runs queued jobs (promise reactions, generic jobs, finalization
    /// callbacks) until the queue is empty, and returns how many ran. This is
    /// a microtask checkpoint; the engine never decides when to run one.
    ///
    /// The queue is the engine's own unless the [`Host`] diverted it:
    /// [`Host::enqueue_promise_job`] and its siblings default to appending to
    /// it. A job that throws stops the run: the exception comes back as
    /// `Err`, the jobs after it stay queued, and calling `run_jobs` again
    /// continues with them. A [`Terminator`] stops it as it stops anything.
    ///
    /// ```
    /// use clazel_js::Runtime;
    ///
    /// fn checkpoint(rt: &mut Runtime) -> clazel_js::Result<()> {
    ///     // After a script returns, with the host's own tasks still to run:
    ///     let ran = rt.run_jobs()?;
    ///     println!("{ran} jobs");
    ///     Ok(())
    /// }
    /// # let mut rt = clazel_js::Runtime::new(clazel_js::Config::new(clazel_js::Limits::unlimited()), clazel_js::DefaultHost::new())?;
    /// # checkpoint(&mut rt)?;
    /// # Ok::<(), clazel_js::Error>(())
    /// ```
    pub fn run_jobs(&mut self) -> Result<u64> {
        let runtime = self.runtime_id();
        let mut scope = Scope::new(&mut self.vm, runtime);
        scope.run_jobs()
    }

    /// A handle that stops this runtime from another thread. Every call gives
    /// a handle to the same flag.
    pub fn terminator(&self) -> Terminator {
        self.terminator.clone()
    }

    /// The limits this runtime was built with.
    pub fn limits(&self) -> Limits {
        self.limits
    }

    /// The host, between calls. Not available while a hook is running; there
    /// the hook's own `&mut self` is the host.
    pub fn host_mut(&mut self) -> &mut dyn Host {
        match self.vm.embedder_mut::<State>() {
            Some(state) => &mut *state.host,
            None => &mut self.fallback_host,
        }
    }

    /// Bytes the heap holds now, live and not yet swept, for the embedder's
    /// own accounting and for tests of [`Limits::heap_bytes`].
    pub fn heap_used(&self) -> Result<u64> {
        // The VM heap's byte count, the one `Limits::heap_bytes` is checked
        // against: an estimate (64 bytes a cell, a string's code units, 32
        // bytes a property). Nothing is swept yet.
        Ok(self.vm.heap().bytes())
    }
}

impl Runtime {
    /// The runtime's identity, as `Local`s carry it.
    fn runtime_id(&mut self) -> usize {
        self.vm.embedder::<State>().map_or(0, |state| state.id)
    }
}

/// A failure of the VM while a runtime is being built, before there is a
/// runtime state to take errors from.
fn vm_failure(abrupt: Abrupt) -> Error {
    match abrupt {
        Abrupt::OutOfMemory => Error::OutOfMemory,
        Abrupt::Terminated => Error::Terminated,
        Abrupt::Throw(_) | Abrupt::NotYet(_) | Abrupt::Internal(_) => {
            Error::NotImplemented("the VM could not start with these limits")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn is_send<T: Send>() {}
    fn is_send_sync<T: Send + Sync>() {}

    #[test]
    fn terminator_is_a_shared_sticky_flag() {
        is_send_sync::<Terminator>();
        let a = Terminator::default();
        let b = a.clone();
        assert!(!a.is_terminated());
        b.terminate();
        assert!(a.is_terminated());
        b.terminate();
        assert!(a.is_terminated());
        a.clear();
        assert!(!b.is_terminated());
    }

    #[test]
    fn runtime_is_send() {
        is_send::<Runtime>();
    }

    #[test]
    fn unlimited_is_the_largest_of_each() {
        let l = Limits::unlimited();
        assert_eq!(l.heap_bytes, u64::MAX);
        assert_eq!(l.native_depth, u32::MAX);
    }
}
