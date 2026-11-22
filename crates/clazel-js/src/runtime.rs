//! [`Runtime`], its [`Config`] and [`Limits`], and the [`Terminator`].

use core::cell::Cell;
use core::marker::PhantomData;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use crate::error::{Result, not_implemented};
use crate::host::Host;
use crate::scope::Scope;

/// Every limit is the embedder's to set, and the engine has no default for
/// any of them (phase-7.md, "Limits and stopping").
///
/// A struct literal must name every field, so adding a limit later makes
/// every embedder choose a value. The numbers the browser picks are not in
/// this crate. Each limit has its own report, listed with the field.
///
/// ```no_run
/// use clazel_js::Limits;
///
/// // A test harness with limits generous enough never to matter, and one
/// // that is not: a small heap that is meant to be hit.
/// let relaxed = Limits::unlimited();
/// let strict = Limits {
///     heap_bytes: 64 << 20,
///     ..relaxed
/// };
/// # let _ = strict;
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    /// Heap size in bytes. An allocation that would pass it first runs a full
    /// collection, then throws a `RangeError` if it still would.
    pub heap_bytes: u64,
    /// Size of the value-stack region in bytes. Passing it throws a
    /// `RangeError` ("too much recursion").
    pub value_stack_bytes: u64,
    /// How many native functions may be on the call stack at once, counting
    /// built-ins that call back into JavaScript such as `Array.prototype.map`.
    /// Passing it throws a `RangeError`.
    pub native_depth: u32,
    /// Bytes of generated machine code the JIT may hold. Passing it stops
    /// compiling and leaves functions to the interpreter; it is not an error.
    /// Ignored when [`JitMode::Off`].
    pub code_bytes: u64,
    /// Entries in the RegExp matcher's backtrack stack. Passing it throws a
    /// `RangeError` from the match, rather than hanging on `(a+)+b`.
    pub regexp_backtrack_entries: u64,
    /// Nesting depth of the parser (source text) and of `JSON.parse`. Passing
    /// it throws a `SyntaxError` for source and a `RangeError` for JSON.
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
/// ```no_run
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
/// ```no_run
/// use std::thread;
/// use std::time::Duration;
/// use clazel_js::{Config, DefaultHost, Limits, Realm, Runtime};
///
/// fn run_for_a_second(rt: &mut Runtime, realm: &Realm) {
///     let terminator = rt.terminator();
///     let watchdog = thread::spawn(move || {
///         thread::sleep(Duration::from_secs(1));
///         terminator.terminate();
///     });
///     let _ = rt.scope(|scope| {
///         scope.eval_script(realm, clazel_js::Source::new("loop.js", "for (;;) {}"))?;
///         Ok::<(), clazel_js::Error>(())
///     });
///     let _ = watchdog.join();
///     rt.terminator().clear();
/// }
/// ```
#[derive(Clone, Debug, Default)]
pub struct Terminator {
    flag: Arc<AtomicBool>,
}

impl Terminator {
    /// Asks the runtime to stop. Safe to call from any thread, any number of
    /// times.
    pub fn terminate(&self) {
        self.flag.store(true, Ordering::Relaxed);
    }

    /// Whether `terminate` has been called and not cleared.
    pub fn is_terminated(&self) -> bool {
        self.flag.load(Ordering::Relaxed)
    }

    /// Lets the runtime run again. Call it after an evaluation has returned
    /// `Terminated`, never while one is running.
    pub fn clear(&self) {
        self.flag.store(false, Ordering::Relaxed);
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
/// ```no_run
/// use clazel_js::{Config, DefaultHost, Limits, RealmOptions, Runtime, Source};
///
/// fn main() -> Result<(), clazel_js::Error> {
///     let mut rt = Runtime::new(Config::new(Limits::unlimited()), DefaultHost::new())?;
///     let realm = rt.scope(|scope| scope.create_realm(RealmOptions::default()))?;
///     let sum = rt.scope(|scope| {
///         let value = scope.eval_script(&realm, Source::new("sum.js", "1 + 2"))?;
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
/// ```no_run
/// use clazel_js::Runtime;
///
/// fn assert_send<T: Send>() {}
/// fn check() { assert_send::<Runtime>(); }
/// ```
pub struct Runtime {
    limits: Limits,
    terminator: Terminator,
    host: Box<dyn Host>,
    // `Cell` is `Send` and not `Sync`, which is the rule.
    _not_sync: PhantomData<Cell<()>>,
}

impl Runtime {
    /// Builds a runtime with no realms. The `host` is taken for the life of
    /// the runtime; reach it again with [`Runtime::host_mut`] or, from inside
    /// a native function, [`Scope::host_mut`].
    pub fn new(config: Config, host: impl Host) -> Result<Runtime> {
        not_implemented!("Runtime::new", config, host)
    }

    /// Runs `f` with a [`Scope`]. Every [`Local`](crate::Local) made inside is
    /// rooted until `f` returns, and cannot leave it; what `f` returns must
    /// not borrow from the scope. This is the only way in.
    ///
    /// `f` cannot call `scope` again, because it has no access to the
    /// `Runtime`. Code that wants an inner scope uses [`Scope::nested`].
    pub fn scope<R>(&mut self, f: impl for<'s> FnOnce(&mut Scope<'s>) -> R) -> R {
        let mut scope = Scope::new();
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
    /// ```no_run
    /// use clazel_js::Runtime;
    ///
    /// fn checkpoint(rt: &mut Runtime) -> clazel_js::Result<()> {
    ///     // After a script returns, with the host's own tasks still to run:
    ///     let ran = rt.run_jobs()?;
    ///     println!("{ran} jobs");
    ///     Ok(())
    /// }
    /// ```
    pub fn run_jobs(&mut self) -> Result<u64> {
        not_implemented!("Runtime::run_jobs")
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
        &mut *self.host
    }

    /// Bytes the heap holds now, live and not yet swept, for the embedder's
    /// own accounting and for tests of [`Limits::heap_bytes`].
    pub fn heap_used(&self) -> Result<u64> {
        not_implemented!("Runtime::heap_used")
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
