//! The [`Host`] trait: everything ECMA-262 leaves to the host, and what the
//! engine needs from the world.
//!
//! The ECMA-262 section of each hook is not cited yet. Rule 5 asks for the
//! exact section, and the edition they refer to is pinned in item 7.1, which
//! has not run. Each hook is named by the abstract operation's name, which
//! does not change between editions; section numbers join when 7.1 pins one,
//! and 7.4 checks this list against the pinned edition's list of host hooks.

use core::any::Any;
use std::hash::{BuildHasher, RandomState};
use std::time::{SystemTime, UNIX_EPOCH};

use crate::code::{LoadPayload, Module, ModuleRequest, Realm, Referrer};
use crate::error::{ErrorKind, Result, not_implemented};
use crate::native::Tracer;
use crate::scope::Scope;
use crate::value::{Handle, Local};

/// A queued unit of work for the event loop: a promise reaction, a
/// `FinalizationRegistry` cleanup, or a generic job.
///
/// The engine makes a `Job` and gives it to the host to queue. Running it is
/// [`Scope::run_job`](crate::Scope::run_job), once, on the runtime's thread. A
/// `Job` is a root, so dropping one without running it only loses the work.
/// It is `Send` and `Sync` like a [`Handle`].
#[derive(Debug)]
pub struct Job {
    root: Handle,
    realm: Option<Realm>,
}

impl Job {
    /// The realm the job runs in, if the operation that made it names one.
    pub fn realm(&self) -> Option<&Realm> {
        self.realm.as_ref()
    }

    /// The root that keeps the job's closure alive.
    pub fn as_handle(&self) -> &Handle {
        &self.root
    }
}

/// A callback and the host's data about it: ECMA-262's JobCallback Record.
///
/// [`Host::make_job_callback`] makes one when a promise reaction or a
/// `FinalizationRegistry` is created, and [`Host::call_job_callback`] calls it
/// later. HTML uses the data to remember the "incumbent settings object".
#[derive(Debug)]
pub struct JobCallback {
    callback: Handle,
    host_defined: Option<Box<dyn Any + Send>>,
}

impl JobCallback {
    /// A job callback with no host data.
    pub fn new(callback: Handle) -> JobCallback {
        JobCallback {
            callback,
            host_defined: None,
        }
    }

    /// Attaches the host's data.
    #[must_use]
    pub fn with_host_defined(mut self, data: Box<dyn Any + Send>) -> JobCallback {
        self.host_defined = Some(data);
        self
    }

    /// The callback function.
    pub fn callback(&self) -> &Handle {
        &self.callback
    }

    /// The host's data, if any.
    pub fn host_defined(&self) -> Option<&(dyn Any + Send)> {
        self.host_defined.as_deref()
    }
}

/// What [`Host::promise_rejection_tracker`] is told happened.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RejectionOperation {
    /// A promise with no handler was rejected.
    Reject,
    /// A handler was added to an already-rejected promise that had none.
    Handle,
}

/// Which dynamic code-from-strings feature is asking
/// [`Host::ensure_can_compile_strings`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DynamicCodeKind {
    /// `eval(...)`; `direct` is true for a direct call that sees local scope.
    Eval {
        /// Whether this was a direct `eval`.
        direct: bool,
    },
    /// `Function(...)`.
    Function,
    /// `GeneratorFunction(...)`.
    GeneratorFunction,
    /// `AsyncFunction(...)`.
    AsyncFunction,
    /// `AsyncGeneratorFunction(...)`.
    AsyncGeneratorFunction,
}

/// The strings handed to [`Host::ensure_can_compile_strings`]. They are
/// UTF-16 because the program can build them with lone surrogates.
#[derive(Clone, Copy, Debug)]
pub struct CompileStrings<'a> {
    /// Which feature is compiling code.
    pub kind: DynamicCodeKind,
    /// The parameter strings (empty for `eval`).
    pub parameters: &'a [Vec<u16>],
    /// The body, or for `eval` the code.
    pub body: &'a [u16],
}

/// The answer of [`Host::resize_array_buffer`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Resize {
    /// The host did the resize.
    Handled,
    /// The host left it to the engine's default, which allocates.
    Unhandled,
}

/// What the embedder supplies. Every method has a default so a program that
/// needs none of the hooks can use [`DefaultHost`], and an embedder
/// overrides what it needs.
///
/// - **Reentrancy.** A hook gets `&mut self` and a [`Scope`] and may call
///   back into the engine through that scope, including evaluating code.
///   While a hook runs, the host is lent to it, so [`Scope::host_mut`] from
///   code the hook runs gives [`Error::Busy`](crate::Error::Busy).
/// - **Errors.** A hook that returns `Err` makes the operation that called it
///   fail with that error, as ECMA-262 says for an abrupt completion from a
///   host-defined operation. `Err(Error::Terminated)` is passed on as is.
/// - **Threads.** `Host: Send`, which keeps [`Runtime`](crate::Runtime)
///   `Send`. A host that needs a value that is not `Send` keeps an id or a
///   channel in the host and the value elsewhere.
/// - **The event loop is the host's.** Nothing here runs a job: the hooks
///   queue, and the embedder calls [`Runtime::run_jobs`](crate::Runtime::run_jobs)
///   when its loop says to.
///
/// The defaults named in each method are the engine's behaviour for a host
/// that says nothing. The browser's answers (HTML's, and 7.0(b)'s fixed
/// time zone offset and `en-US`) are the browser's, in `clazel-web`.
///
/// ```no_run
/// use clazel_js::{
///     Host, Job, Local, Module, ModuleRequest, LoadPayload, Referrer, RejectionOperation,
///     Result, Scope,
/// };
///
/// /// A host with a task queue of its own, rejection reporting, and a fixed clock.
/// struct PageHost {
///     tasks: Vec<Job>,
///     unhandled: Vec<String>,
/// }
///
/// impl Host for PageHost {
///     fn enqueue_promise_job(&mut self, _scope: &mut Scope<'_>, job: Job) -> Result<()> {
///         self.tasks.push(job);
///         Ok(())
///     }
///
///     fn promise_rejection_tracker(
///         &mut self,
///         _scope: &mut Scope<'_>,
///         _promise: Local<'_>,
///         operation: RejectionOperation,
///     ) {
///         self.unhandled.push(format!("{operation:?}"));
///     }
///
///     fn now_ms(&mut self) -> f64 {
///         1_700_000_000_000.0
///     }
///
///     fn random_u64(&mut self) -> u64 {
///         4 // chosen by fair dice roll
///     }
/// }
/// ```
pub trait Host: Any + Send {
    // ---- Jobs -----------------------------------------------------------

    /// `HostEnqueuePromiseJob(job, realm)`: queue a promise reaction.
    ///
    /// Default: append it to the engine's own queue, which
    /// [`Runtime::run_jobs`](crate::Runtime::run_jobs) drains in order. A host
    /// that overrides this takes over the order and calls
    /// [`Scope::run_job`] itself.
    fn enqueue_promise_job(&mut self, scope: &mut Scope<'_>, job: Job) -> Result<()> {
        scope.enqueue_job_internal(job)
    }

    /// `HostEnqueueGenericJob(job, realm)`. Default: as for promise jobs.
    fn enqueue_generic_job(&mut self, scope: &mut Scope<'_>, job: Job) -> Result<()> {
        scope.enqueue_job_internal(job)
    }

    /// `HostEnqueueTimeoutJob(job, realm, milliseconds)`: run `job` after at
    /// least `delay_ms`. Only a feature with timers in the language uses it
    /// (`Atomics.waitAsync`, which the browser does not ship), so no
    /// embedder is required to override it. Default: the engine's own queue,
    /// with the delay ignored.
    fn enqueue_timeout_job(
        &mut self,
        scope: &mut Scope<'_>,
        job: Job,
        delay_ms: f64,
    ) -> Result<()> {
        let _ = delay_ms;
        scope.enqueue_job_internal(job)
    }

    /// `HostEnqueueFinalizationRegistryCleanupJob(finalizationRegistry)`: a
    /// registry has cells to clean up. The phase plan's list of hooks does not
    /// name this one and 7.6 needs it (finalization callbacks are queued as
    /// tasks); it is listed under the README's open questions. Default: the
    /// engine's own queue.
    fn enqueue_finalization_registry_cleanup_job(
        &mut self,
        scope: &mut Scope<'_>,
        job: Job,
    ) -> Result<()> {
        scope.enqueue_job_internal(job)
    }

    /// `HostMakeJobCallback(callback)`. Default: a [`JobCallback`] holding the
    /// function and no host data.
    fn make_job_callback(
        &mut self,
        scope: &mut Scope<'_>,
        callback: Local<'_>,
    ) -> Result<JobCallback> {
        Ok(JobCallback::new(scope.persist(callback)))
    }

    /// `HostCallJobCallback(jobCallback, V, argumentsList)`. Default: call the
    /// function with `this` and the arguments.
    fn call_job_callback<'s>(
        &mut self,
        scope: &mut Scope<'s>,
        callback: &JobCallback,
        this: Local<'_>,
        arguments: &[Local<'_>],
    ) -> Result<Local<'s>> {
        let function = scope.local(callback.callback())?;
        scope.call(function, this, arguments)
    }

    // ---- Modules --------------------------------------------------------

    /// `HostLoadImportedModule(referrer, moduleRequest, hostDefined, payload)`:
    /// find (and fetch, if need be) the module `request` names, then call
    /// [`Scope::finish_loading_imported_module`] with it or with the error.
    /// It may do so before returning or on a later turn.
    ///
    /// ECMA-262 requires the same `(referrer, request)` to give the same module
    /// every time or fail every time; keeping that is the host's job.
    ///
    /// Default: finish with a `TypeError` saying this host loads no modules.
    fn load_imported_module(
        &mut self,
        scope: &mut Scope<'_>,
        referrer: Referrer<'_>,
        request: &ModuleRequest,
        payload: LoadPayload,
    ) -> Result<()> {
        let _ = (referrer, request);
        let error = scope.new_exception(ErrorKind::TypeError, "this host does not load modules")?;
        scope.finish_loading_imported_module(payload, Err(error))
    }

    /// `HostGetSupportedImportAttributes()`: the attribute keys this host
    /// understands (for example `"type"`). The engine refuses an import with
    /// any other key with a `SyntaxError`. Default: none. Whether the pinned
    /// edition has this hook is checked in 7.4.
    fn supported_import_attributes(&self) -> &[&'static str] {
        &[]
    }

    /// `HostGetImportMetaProperties(moduleRecord)`: the properties of
    /// `import.meta` for `module`, as (key, value) pairs. Default: none.
    fn get_import_meta_properties<'s>(
        &mut self,
        scope: &mut Scope<'s>,
        module: &Module,
    ) -> Result<Vec<(String, Local<'s>)>> {
        let _ = (scope, module);
        Ok(Vec::new())
    }

    /// `HostFinalizeImportMeta(importMeta, moduleRecord)`: last chance to change
    /// the `import.meta` object. Default: nothing.
    fn finalize_import_meta(
        &mut self,
        scope: &mut Scope<'_>,
        import_meta: Local<'_>,
        module: &Module,
    ) -> Result<()> {
        let _ = (scope, import_meta, module);
        Ok(())
    }

    // ---- Promises, code from strings, and the like ------------------------

    /// `HostPromiseRejectionTracker(promise, operation)`: a promise was
    /// rejected with no handler, or got its first handler after that. It
    /// cannot fail or throw; the host records what it needs. Default: nothing.
    fn promise_rejection_tracker(
        &mut self,
        scope: &mut Scope<'_>,
        promise: Local<'_>,
        operation: RejectionOperation,
    ) {
        let _ = (scope, promise, operation);
    }

    /// `HostEnsureCanCompileStrings(calleeRealm, ...)`: may `eval` and the
    /// `Function` constructors compile this text in `callee`? `Err` refuses,
    /// and the error is what the call throws. Default: yes.
    fn ensure_can_compile_strings(
        &mut self,
        scope: &mut Scope<'_>,
        callee: &Realm,
        strings: &CompileStrings<'_>,
    ) -> Result<()> {
        let _ = (scope, callee, strings);
        Ok(())
    }

    /// `HostHasSourceTextAvailable(func)`: may `Function.prototype.toString`
    /// show the source of `function`? Default: yes.
    fn has_source_text_available(&mut self, scope: &mut Scope<'_>, function: Local<'_>) -> bool {
        let _ = (scope, function);
        true
    }

    /// `HostEnsureCanAddPrivateElement(O)`: may a private element be added to
    /// `object`? `Err` refuses. Default: yes.
    fn ensure_can_add_private_element(
        &mut self,
        scope: &mut Scope<'_>,
        object: Local<'_>,
    ) -> Result<()> {
        let _ = (scope, object);
        Ok(())
    }

    /// `HostResizeArrayBuffer(buffer, newByteLength)`. Default:
    /// [`Resize::Unhandled`].
    fn resize_array_buffer(
        &mut self,
        scope: &mut Scope<'_>,
        buffer: Local<'_>,
        new_byte_length: u64,
    ) -> Result<Resize> {
        let _ = (scope, buffer, new_byte_length);
        Ok(Resize::Unhandled)
    }

    // ---- What the engine needs from the world -----------------------------

    /// The current time in milliseconds since the Unix epoch, for
    /// `Date.now()` and `new Date()`. Default: the system clock.
    fn now_ms(&mut self) -> f64 {
        match SystemTime::now().duration_since(UNIX_EPOCH) {
            Ok(d) => d.as_secs_f64() * 1000.0,
            Err(_) => 0.0,
        }
    }

    /// The local time zone's offset from UTC in milliseconds at `time_ms`
    /// (ECMA-262's `LocalTZA`). `is_utc` says whether `time_ms` is a UTC time
    /// or a local one to convert back. Default: 0, that is, UTC.
    fn local_tza(&mut self, time_ms: f64, is_utc: bool) -> f64 {
        let _ = (time_ms, is_utc);
        0.0
    }

    /// Random bits for `Math.random`. Required, because the engine has no
    /// source of its own (rule 8: no randomness dependency). It need not be
    /// cryptographic. [`DefaultHost`] draws from the standard library's
    /// per-process random hash keys.
    fn random_u64(&mut self) -> u64;

    /// The default locale, as a BCP 47 tag, for `toLocaleString` and friends.
    /// Default: `"en-US"`.
    fn default_locale(&self) -> &str {
        "en-US"
    }

    // ---- The collector ------------------------------------------------------

    /// Reports the JavaScript values the host keeps alive: for the browser,
    /// the wrapper of every node in a document's tree, the task queues and the
    /// timers. Called during every collection. See [`Tracer`]. Default:
    /// nothing.
    fn trace_roots(&mut self, tracer: &mut Tracer<'_>) {
        let _ = tracer;
    }
}

/// A host that says nothing: every hook has its default, and the clock and
/// randomness come from the standard library.
///
/// Test262's runner, small tools and the examples use it. A real embedder
/// supplies its own.
///
/// ```no_run
/// use clazel_js::{Config, DefaultHost, Limits, Runtime};
///
/// fn main() -> Result<(), clazel_js::Error> {
///     let _rt = Runtime::new(Config::new(Limits::unlimited()), DefaultHost::new())?;
///     Ok(())
/// }
/// ```
#[derive(Debug, Default)]
pub struct DefaultHost {
    draws: u64,
}

impl DefaultHost {
    /// A default host.
    pub fn new() -> DefaultHost {
        DefaultHost { draws: 0 }
    }
}

impl Host for DefaultHost {
    fn random_u64(&mut self) -> u64 {
        // A fresh `RandomState` has per-process random keys; hashing a counter
        // gives different bits each call. Good enough for `Math.random`, which
        // ECMA-262 does not require to be unpredictable.
        self.draws = self.draws.wrapping_add(1);
        RandomState::new().hash_one(self.draws)
    }
}

// The engine's own queue is reached through this one call, which the default
// hooks use and an embedder that forwards to it may too.
impl Scope<'_> {
    /// Appends `job` to the engine's own job queue, the one
    /// [`Runtime::run_jobs`](crate::Runtime::run_jobs) drains. What the default
    /// `enqueue_*` hooks do, and what an overriding host may call to forward.
    pub fn enqueue_job_internal(&mut self, job: Job) -> Result<()> {
        not_implemented!("Scope::enqueue_job_internal", job)
    }

    /// Runs a job to completion. A job that throws returns the exception.
    pub fn run_job(&mut self, job: Job) -> Result<()> {
        not_implemented!("Scope::run_job", job)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_host_answers_for_the_world() {
        let mut host = DefaultHost::new();
        assert_eq!(host.local_tza(0.0, true), 0.0);
        assert_eq!(host.default_locale(), "en-US");
        assert!(host.now_ms() > 1.5e12);
        assert_ne!(host.random_u64(), host.random_u64());
        assert!(host.supported_import_attributes().is_empty());
    }
}
