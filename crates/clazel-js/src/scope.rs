//! [`Scope`]: every operation on values, realms, code and objects.

use core::any::Any;
use core::marker::PhantomData;

use crate::code::{
    LoadPayload, Module, ModuleStatus, Realm, RealmOptions, Referrer, Script, Source,
};
use crate::error::{Error, ErrorKind, ErrorReport, Exception, Result, not_implemented};
use crate::host::Host;
use crate::native::{Args, Callable, HostObject};
use crate::value::{
    Handle, Key, Local, Member, PromiseState, PropertyDescriptor, ValueKind, Weak, WellKnownSymbol,
};

/// The resolving functions of a promise made by [`Scope::new_promise`].
///
/// Held by the embedder until the work the promise stands for is done: a
/// fetch finishes, a timer fires. It is two [`Handle`]s, `Send` and `Sync`,
/// and settling uses [`Scope::resolve_promise`] and [`Scope::reject_promise`]
/// on the runtime's thread. Settling twice is a no-op, as for JavaScript's own
/// resolving functions.
#[derive(Clone, Debug)]
pub struct Resolvers {
    resolve: Handle,
    reject: Handle,
}

impl Resolvers {
    /// The `resolve` function.
    pub fn resolve_function(&self) -> &Handle {
        &self.resolve
    }

    /// The `reject` function.
    pub fn reject_function(&self) -> &Handle {
        &self.reject
    }
}

/// Where all work on a [`Runtime`](crate::Runtime) happens, and the owner of
/// the lifetime `'s` that every [`Local`] it makes carries.
///
/// A `Scope` exists inside [`Runtime::scope`](crate::Runtime::scope), inside
/// each native function and hook (which get one for their call), and inside
/// [`Scope::nested`]. All the engine's operations are methods of it, grouped
/// below.
///
/// - **Rooting.** Each `Local` is rooted until its scope ends. A loop that
///   makes many temporary values uses `nested` per iteration so they are not
///   all held until the end.
/// - **Collection.** The collector runs only inside an operation that
///   allocates or that the embedder asks for ([`Scope::gc`]), never between
///   two lines of the embedder's own code, so no `Local` is ever seen half
///   moved. The heap does not move objects (phase-7.md 7.0(f)).
/// - **Errors.** Operations that can run JavaScript, and so throw, return
///   `Result`. Operations that cannot (making a number, reading a kind) do not.
///
/// ```no_run
/// use clazel_js::{Key, Runtime};
///
/// fn sum_squares(rt: &mut Runtime, n: u32) -> clazel_js::Result<f64> {
///     rt.scope(|scope| {
///         let list = scope.new_array(0)?;
///         for i in 0..n {
///             // Temporaries die at the end of each pass, not at the end of the call.
///             scope.nested(|inner| {
///                 let x = inner.number(f64::from(i) * f64::from(i));
///                 inner.set(list, Key::Index(i), x)
///             })?;
///         }
///         let length = scope.get(list, Key::from("length"))?;
///         Ok(scope.as_number(length).unwrap_or(0.0))
///     })
/// }
/// ```
#[derive(Debug)]
pub struct Scope<'s> {
    // Invariant in `'s`, so a `Local<'s>` cannot be coerced to another scope's.
    _scope: PhantomData<fn(&'s ()) -> &'s ()>,
}

impl<'s> Scope<'s> {
    pub(crate) fn new() -> Scope<'s> {
        Scope {
            _scope: PhantomData,
        }
    }

    /// Runs `f` with an inner scope. The `Local`s `f` makes are released when
    /// it returns, and cannot escape it. What `f` returns must be owned
    /// (a [`Handle`], a number, an [`Exception`]); to keep a value, call
    /// [`Scope::persist`] inside `f`.
    pub fn nested<R>(&mut self, f: impl for<'i> FnOnce(&mut Scope<'i>) -> R) -> R {
        let mut inner = Scope::new();
        f(&mut inner)
    }

    // ---- Holding values ----------------------------------------------------

    /// Roots `value` beyond this scope. See [`Handle`].
    pub fn persist(&mut self, value: Local<'_>) -> Handle {
        let _ = value;
        Handle::placeholder()
    }

    /// The value a handle names, as a `Local` of this scope.
    /// [`Error::WrongRuntime`] if the handle is another runtime's,
    /// [`Error::StaleHandle`] if its generation does not match.
    pub fn local(&mut self, handle: &Handle) -> Result<Local<'s>> {
        not_implemented!("Scope::local", handle)
    }

    /// A weak reference to `value`. See [`Weak`].
    pub fn downgrade(&mut self, value: Local<'_>) -> Weak {
        let _ = value;
        Weak::placeholder()
    }

    /// The value, if it is still alive. `Ok(None)` once it has been collected.
    pub fn upgrade(&mut self, weak: &Weak) -> Result<Option<Local<'s>>> {
        not_implemented!("Scope::upgrade", weak)
    }

    /// A [`Member`] for `value`, to store in a host object's data and report
    /// from its `trace`.
    pub fn member(&mut self, value: Local<'_>) -> Member {
        let _ = value;
        Member::placeholder()
    }

    /// The value a member names. [`Error::StaleHandle`] if the owner did not
    /// report it and it has been collected.
    pub fn local_from_member(&mut self, member: Member) -> Result<Local<'s>> {
        not_implemented!("Scope::local_from_member", member)
    }

    // ---- Making and reading primitive values -----------------------------

    /// `undefined`.
    pub fn undefined(&mut self) -> Local<'s> {
        Local::placeholder()
    }

    /// `null`.
    pub fn null(&mut self) -> Local<'s> {
        Local::placeholder()
    }

    /// A Boolean.
    pub fn boolean(&mut self, value: bool) -> Local<'s> {
        let _ = value;
        Local::placeholder()
    }

    /// A Number. NaN is canonicalized, as the value encoding requires.
    pub fn number(&mut self, value: f64) -> Local<'s> {
        let _ = value;
        Local::placeholder()
    }

    /// A String from Rust text.
    pub fn string(&mut self, value: &str) -> Local<'s> {
        let _ = value;
        Local::placeholder()
    }

    /// A String from UTF-16 code units, which may hold lone surrogates that a
    /// Rust `&str` cannot. This is the exact form JavaScript strings take,
    /// and what WebIDL's `DOMString` and `USVString` conversions start from.
    pub fn string_utf16(&mut self, units: &[u16]) -> Local<'s> {
        let _ = units;
        Local::placeholder()
    }

    /// A BigInt from an `i64`.
    pub fn bigint_from_i64(&mut self, value: i64) -> Local<'s> {
        let _ = value;
        Local::placeholder()
    }

    /// A BigInt from a `u64`.
    pub fn bigint_from_u64(&mut self, value: u64) -> Local<'s> {
        let _ = value;
        Local::placeholder()
    }

    /// A new unique Symbol with an optional description.
    pub fn new_symbol(&mut self, description: Option<&str>) -> Local<'s> {
        let _ = description;
        Local::placeholder()
    }

    /// A well-known symbol. The same symbol in every call and every realm of
    /// this runtime, as ECMA-262 says.
    pub fn well_known_symbol(&mut self, symbol: WellKnownSymbol) -> Local<'s> {
        let _ = symbol;
        Local::placeholder()
    }

    /// What kind of value this is. Never throws and never runs JavaScript.
    pub fn kind(&self, value: Local<'_>) -> ValueKind {
        let _ = value;
        ValueKind::Undefined
    }

    /// The Boolean, or `None` if the value is not one.
    pub fn as_boolean(&self, value: Local<'_>) -> Option<bool> {
        let _ = value;
        None
    }

    /// The Number, or `None` if the value is not one.
    pub fn as_number(&self, value: Local<'_>) -> Option<f64> {
        let _ = value;
        None
    }

    /// A String's UTF-16 code units, exactly. `Err(WrongType)` for a
    /// non-string.
    pub fn string_to_utf16(&self, value: Local<'_>) -> Result<Vec<u16>> {
        not_implemented!("Scope::string_to_utf16", value)
    }

    /// A String as Rust text, with each lone surrogate replaced by U+FFFD.
    /// `Err(WrongType)` for a non-string.
    pub fn string_to_string_lossy(&self, value: Local<'_>) -> Result<String> {
        not_implemented!("Scope::string_to_string_lossy", value)
    }

    // ---- Conversions and tests (what WebIDL's conversions are built from) --

    /// `ToBoolean`. Cannot throw.
    pub fn to_boolean(&mut self, value: Local<'_>) -> bool {
        let _ = value;
        false
    }

    /// `ToNumber`. Can throw: a Symbol, a BigInt, or an object whose
    /// `valueOf` throws.
    pub fn to_number(&mut self, value: Local<'_>) -> Result<f64> {
        not_implemented!("Scope::to_number", value)
    }

    /// `ToString`, as a String value. Can throw.
    pub fn to_string(&mut self, value: Local<'_>) -> Result<Local<'s>> {
        not_implemented!("Scope::to_string", value)
    }

    /// `ToObject`. Throws a `TypeError` for `undefined` and `null`.
    pub fn to_object(&mut self, value: Local<'_>) -> Result<Local<'s>> {
        not_implemented!("Scope::to_object", value)
    }

    /// `IsCallable`.
    pub fn is_callable(&self, value: Local<'_>) -> bool {
        let _ = value;
        false
    }

    /// `IsConstructor`.
    pub fn is_constructor(&self, value: Local<'_>) -> bool {
        let _ = value;
        false
    }

    /// `IsArray`. Throws for a revoked proxy.
    pub fn is_array(&mut self, value: Local<'_>) -> Result<bool> {
        not_implemented!("Scope::is_array", value)
    }

    /// `IsStrictlyEqual` (`===`).
    pub fn strict_equals(&self, a: Local<'_>, b: Local<'_>) -> bool {
        let _ = (a, b);
        false
    }

    /// `SameValue` (`Object.is`).
    pub fn same_value(&self, a: Local<'_>, b: Local<'_>) -> bool {
        let _ = (a, b);
        false
    }

    /// `InstanceofOperator` (`value instanceof constructor`). Can throw.
    pub fn instance_of(&mut self, value: Local<'_>, constructor: Local<'_>) -> Result<bool> {
        not_implemented!("Scope::instance_of", value, constructor)
    }

    // ---- Objects ------------------------------------------------------------

    /// A new ordinary object, as `{}` in the current realm.
    pub fn new_object(&mut self) -> Result<Local<'s>> {
        not_implemented!("Scope::new_object")
    }

    /// A new Array of the given length, as `new Array(length)`.
    pub fn new_array(&mut self, length: u32) -> Result<Local<'s>> {
        not_implemented!("Scope::new_array", length)
    }

    /// A new Array holding these values.
    pub fn new_array_from(&mut self, elements: &[Local<'_>]) -> Result<Local<'s>> {
        not_implemented!("Scope::new_array_from", elements)
    }

    /// `Get(object, key)`. Runs getters and proxy traps, so can throw.
    pub fn get(&mut self, object: Local<'_>, key: Key<'_, '_>) -> Result<Local<'s>> {
        not_implemented!("Scope::get", object, key)
    }

    /// `Set(object, key, value, true)`: throws in the cases strict-mode
    /// assignment throws (a read-only property, a frozen object).
    pub fn set(&mut self, object: Local<'_>, key: Key<'_, '_>, value: Local<'_>) -> Result<()> {
        not_implemented!("Scope::set", object, key, value)
    }

    /// `HasProperty` (`key in object`).
    pub fn has_property(&mut self, object: Local<'_>, key: Key<'_, '_>) -> Result<bool> {
        not_implemented!("Scope::has_property", object, key)
    }

    /// `DeletePropertyOrThrow`, but returning `false` for a refusal instead of
    /// throwing, as sloppy-mode `delete` does.
    pub fn delete_property(&mut self, object: Local<'_>, key: Key<'_, '_>) -> Result<bool> {
        not_implemented!("Scope::delete_property", object, key)
    }

    /// `DefinePropertyOrThrow`: `Object.defineProperty`.
    pub fn define_property(
        &mut self,
        object: Local<'_>,
        key: Key<'_, '_>,
        descriptor: PropertyDescriptor<'_>,
    ) -> Result<()> {
        not_implemented!("Scope::define_property", object, key, descriptor)
    }

    /// `GetPrototypeOf`. `null` is returned as the `null` value.
    pub fn get_prototype_of(&mut self, object: Local<'_>) -> Result<Local<'s>> {
        not_implemented!("Scope::get_prototype_of", object)
    }

    /// `SetPrototypeOf`: throws if the object refuses (not extensible, or a
    /// cycle).
    pub fn set_prototype_of(&mut self, object: Local<'_>, prototype: Local<'_>) -> Result<()> {
        not_implemented!("Scope::set_prototype_of", object, prototype)
    }

    /// `GetMethod(value, key)`: `Ok(None)` if the property is `undefined` or
    /// `null`, a `TypeError` if it is anything else but callable.
    pub fn get_method(&mut self, value: Local<'_>, key: Key<'_, '_>) -> Result<Option<Local<'s>>> {
        not_implemented!("Scope::get_method", value, key)
    }

    /// `Call(function, this, arguments)`.
    pub fn call(
        &mut self,
        function: Local<'_>,
        this: Local<'_>,
        arguments: &[Local<'_>],
    ) -> Result<Local<'s>> {
        not_implemented!("Scope::call", function, this, arguments)
    }

    /// `Construct(constructor, arguments, newTarget)`; `new_target` of `None`
    /// is the constructor itself.
    pub fn construct(
        &mut self,
        constructor: Local<'_>,
        arguments: &[Local<'_>],
        new_target: Option<Local<'_>>,
    ) -> Result<Local<'s>> {
        not_implemented!("Scope::construct", constructor, arguments, new_target)
    }

    /// Runs the iterator protocol over `iterable`, calling `f` with each value
    /// until it returns `Ok(false)` or the iterator ends. If `f` returns `Err`,
    /// or `Ok(false)`, the iterator is closed (`IteratorClose`) first. This is
    /// the operation WebIDL's `sequence<T>` and `iterable` conversions need.
    ///
    /// ```no_run
    /// use clazel_js::Runtime;
    ///
    /// fn count(rt: &mut Runtime, iterable: &clazel_js::Handle) -> clazel_js::Result<usize> {
    ///     rt.scope(|scope| {
    ///         let iterable = scope.local(iterable)?;
    ///         let mut n = 0;
    ///         scope.iterate(iterable, |_scope, _item| {
    ///             n += 1;
    ///             Ok(true)
    ///         })?;
    ///         Ok(n)
    ///     })
    /// }
    /// ```
    pub fn iterate(
        &mut self,
        iterable: Local<'_>,
        f: impl for<'i> FnMut(&mut Scope<'i>, Local<'i>) -> Result<bool>,
    ) -> Result<()> {
        not_implemented!("Scope::iterate", iterable, f)
    }

    // ---- Native functions and host objects ------------------------------------

    /// A JavaScript function that runs `f`.
    ///
    /// `name` and `length` are the function's `name` and `length`. `callable`
    /// says whether `new` works on it. `f` gets a fresh scope for the call,
    /// the arguments, and returns the result or an [`Error`]. Panics in `f`
    /// are not caught: the lints forbid them in this repository, and an
    /// embedder that panics gets its own panic.
    ///
    /// ```no_run
    /// use clazel_js::{Args, Callable, Key, Local, Result, Runtime, Scope};
    ///
    /// fn install(rt: &mut Runtime, realm: &clazel_js::Realm) -> Result<()> {
    ///     rt.scope(|scope| {
    ///         let global = scope.global(realm)?;
    ///         let greet = scope.function("greet", 1, Callable::Function, |scope, args| {
    ///             let who = scope.to_string(args.get(0))?;
    ///             let who = scope.string_to_string_lossy(who)?;
    ///             Ok(scope.string(&format!("hello, {who}")))
    ///         })?;
    ///         scope.set(global, Key::from("greet"), greet)
    ///     })
    /// }
    /// ```
    pub fn function(
        &mut self,
        name: &str,
        length: u32,
        callable: Callable,
        f: impl for<'a> Fn(&mut Scope<'a>, &Args<'a>) -> Result<Local<'a>> + Send + 'static,
    ) -> Result<Local<'s>> {
        not_implemented!("Scope::function", name, length, callable, f)
    }

    /// Makes a function with [`Scope::function`] and defines it as a method
    /// of `object`: writable, non-enumerable, configurable, as WebIDL
    /// operations and built-in methods are.
    pub fn define_method(
        &mut self,
        object: Local<'_>,
        name: &str,
        length: u32,
        f: impl for<'a> Fn(&mut Scope<'a>, &Args<'a>) -> Result<Local<'a>> + Send + 'static,
    ) -> Result<()> {
        not_implemented!("Scope::define_method", object, name, length, f)
    }

    /// A new host object carrying `data`, with this prototype (`None` is
    /// `null`). See [`HostObject`].
    pub fn new_host_object(
        &mut self,
        prototype: Option<Local<'_>>,
        data: impl HostObject,
    ) -> Result<Local<'s>> {
        not_implemented!("Scope::new_host_object", prototype, data)
    }

    /// The data of a host object of type `T`. [`Error::WrongType`] if the
    /// value is anything else (another type of host object included), and
    /// [`Error::Busy`] if one of its own hooks is running.
    pub fn host_data<T: HostObject>(&self, object: Local<'_>) -> Result<&T> {
        not_implemented!("Scope::host_data", object)
    }

    /// As [`Scope::host_data`], mutably.
    pub fn host_data_mut<T: HostObject>(&mut self, object: Local<'_>) -> Result<&mut T> {
        not_implemented!("Scope::host_data_mut", object)
    }

    /// `GetPrototypeFromConstructor(newTarget, ...)`: the `prototype` of
    /// `new_target` if it is an object, else `fallback`. A constructor that
    /// makes a host object calls this with its [`Args::new_target`] so that a
    /// subclass (`class X extends Node`) gets its own prototype.
    pub fn get_prototype_from_constructor(
        &mut self,
        new_target: Local<'_>,
        fallback: Local<'_>,
    ) -> Result<Local<'s>> {
        not_implemented!(
            "Scope::get_prototype_from_constructor",
            new_target,
            fallback
        )
    }

    /// The embedder's [`Host`] as its own type. [`Error::WrongType`] if the
    /// host is another type, and [`Error::Busy`] while a hook of the host is
    /// running (the hook already has the host as `&mut self`).
    pub fn host_mut<H: Host>(&mut self) -> Result<&mut H> {
        not_implemented!("Scope::host_mut")
    }

    /// For a native function: ends the call with [`Error::Terminated`] if a
    /// [`Terminator`](crate::Terminator) has been used. Call it in any native
    /// loop that can run long.
    pub fn check_terminated(&self) -> Result<()> {
        not_implemented!("Scope::check_terminated")
    }

    // ---- Errors ---------------------------------------------------------------

    /// A new error object of `kind` with `message`, as an [`Exception`] ready to
    /// throw or to refuse a module load with.
    pub fn new_exception(&mut self, kind: ErrorKind, message: &str) -> Result<Exception> {
        not_implemented!("Scope::new_exception", kind, message)
    }

    /// The `Err` for throwing a new error: `return Err(scope.throw_error(...))`.
    /// If creating the error object itself fails, that failure is returned.
    pub fn throw_error(&mut self, kind: ErrorKind, message: &str) -> Error {
        match self.new_exception(kind, message) {
            Ok(exception) => Error::Thrown(exception),
            Err(other) => other,
        }
    }

    /// The `Err` for throwing any value, for example a `DOMException` the
    /// embedder made.
    pub fn throw(&mut self, value: Local<'_>) -> Error {
        Error::Thrown(Exception::from_handle(self.persist(value)))
    }

    /// The value inside an exception, as a `Local` of this scope.
    pub fn exception_value(&mut self, exception: &Exception) -> Result<Local<'s>> {
        self.local(exception.value())
    }

    /// Describes a thrown value. See [`ErrorReport`]. Reads `name`, `message`
    /// and `stack` as data properties and does not call getters, so it cannot
    /// run JavaScript or throw.
    pub fn report(&mut self, exception: &Exception) -> Result<ErrorReport> {
        not_implemented!("Scope::report", exception)
    }

    // ---- Promises ---------------------------------------------------------------

    /// A new pending promise and its resolving functions. For an API that
    /// returns a promise and settles it later (`fetch`).
    ///
    /// ```no_run
    /// use clazel_js::{Handle, Resolvers, Runtime};
    ///
    /// // `fetch()` returns the promise now and keeps the resolvers for later.
    /// fn start_fetch(rt: &mut Runtime) -> clazel_js::Result<(Handle, Resolvers)> {
    ///     rt.scope(|scope| {
    ///         let (promise, resolvers) = scope.new_promise()?;
    ///         Ok((scope.persist(promise), resolvers))
    ///     })
    /// }
    ///
    /// // The kernel answered; settle it, then let the reactions run.
    /// fn finish_fetch(rt: &mut Runtime, resolvers: &Resolvers) -> clazel_js::Result<()> {
    ///     rt.scope(|scope| {
    ///         let response = scope.new_object()?;
    ///         scope.resolve_promise(resolvers, response)
    ///     })?;
    ///     rt.run_jobs()?;
    ///     Ok(())
    /// }
    /// ```
    pub fn new_promise(&mut self) -> Result<(Local<'s>, Resolvers)> {
        not_implemented!("Scope::new_promise")
    }

    /// Calls the promise's `resolve` with `value`. If the value is a thenable
    /// the promise follows it, as for any resolve.
    pub fn resolve_promise(&mut self, resolvers: &Resolvers, value: Local<'_>) -> Result<()> {
        not_implemented!("Scope::resolve_promise", resolvers, value)
    }

    /// Calls the promise's `reject` with `reason`.
    pub fn reject_promise(&mut self, resolvers: &Resolvers, reason: Local<'_>) -> Result<()> {
        not_implemented!("Scope::reject_promise", resolvers, reason)
    }

    /// `Promise.resolve(value)` in the current realm.
    pub fn promise_resolve(&mut self, value: Local<'_>) -> Result<Local<'s>> {
        not_implemented!("Scope::promise_resolve", value)
    }

    /// `PerformPromiseThen` on `promise` with these reactions (each a function
    /// or `None`), returning the derived promise. This is how the embedder
    /// continues after a promise it did not make, such as the one
    /// [`Scope::evaluate_module`] returns.
    pub fn promise_then(
        &mut self,
        promise: Local<'_>,
        on_fulfilled: Option<Local<'_>>,
        on_rejected: Option<Local<'_>>,
    ) -> Result<Local<'s>> {
        not_implemented!("Scope::promise_then", promise, on_fulfilled, on_rejected)
    }

    /// A promise's state now. Reading it never marks a rejection handled.
    pub fn promise_state(&self, promise: Local<'_>) -> Result<PromiseState<'s>> {
        not_implemented!("Scope::promise_state", promise)
    }

    // ---- ArrayBuffers ------------------------------------------------------------

    /// A new `ArrayBuffer` that owns `bytes`.
    pub fn new_array_buffer(&mut self, bytes: Vec<u8>) -> Result<Local<'s>> {
        not_implemented!("Scope::new_array_buffer", bytes)
    }

    /// An `ArrayBuffer`'s bytes. Empty for a detached one. The borrow ends
    /// before any call that can run JavaScript, which could detach or resize it.
    pub fn array_buffer_bytes(&self, buffer: Local<'_>) -> Result<&[u8]> {
        not_implemented!("Scope::array_buffer_bytes", buffer)
    }

    /// `DetachArrayBuffer(buffer, key)`: after it the buffer has length 0.
    /// `key` must be the `ArrayBuffer`'s detach key if it has one, else a
    /// `TypeError`. This is Test262's `$262.detachArrayBuffer`, and what
    /// `postMessage` transfers and `structuredClone` use later.
    pub fn detach_array_buffer(&mut self, buffer: Local<'_>, key: Option<Local<'_>>) -> Result<()> {
        not_implemented!("Scope::detach_array_buffer", buffer, key)
    }

    // ---- Realms ---------------------------------------------------------------------

    /// `CreateRealm` plus `SetDefaultGlobalBindings`: a new realm with its own
    /// built-ins. This is `$262.createRealm`.
    pub fn create_realm(&mut self, options: RealmOptions) -> Result<Realm> {
        not_implemented!("Scope::create_realm", options)
    }

    /// The realm of the function being run. Inside a native function, the
    /// function's own realm; inside a hook, the realm of the code that
    /// triggered it, if there is one.
    pub fn current_realm(&mut self) -> Result<Realm> {
        not_implemented!("Scope::current_realm")
    }

    /// The realm's global object. Add properties to it with [`Scope::set`] and
    /// [`Scope::define_property`]; that is how an embedder installs `console`
    /// or `window`.
    pub fn global(&mut self, realm: &Realm) -> Result<Local<'s>> {
        not_implemented!("Scope::global", realm)
    }

    /// Attaches the embedder's data to a realm (HTML's environment settings
    /// object), replacing what was there.
    pub fn set_realm_host_defined(
        &mut self,
        realm: &Realm,
        data: Box<dyn Any + Send>,
    ) -> Result<()> {
        not_implemented!("Scope::set_realm_host_defined", realm, data)
    }

    /// The data attached with [`Scope::set_realm_host_defined`].
    pub fn realm_host_defined(&self, realm: &Realm) -> Result<Option<&(dyn Any + Send)>> {
        not_implemented!("Scope::realm_host_defined", realm)
    }

    // ---- Scripts and modules ------------------------------------------------------------

    /// `ParseScript`: compiles `source`. A syntax error is
    /// [`Error::Thrown`] holding a `SyntaxError` of `realm`.
    pub fn compile_script(&mut self, realm: &Realm, source: Source<'_>) -> Result<Script> {
        not_implemented!("Scope::compile_script", realm, source)
    }

    /// `ScriptEvaluation`: runs a compiled script, returning the value of its
    /// last expression statement (the completion value, as `eval` gives).
    pub fn run_script(&mut self, script: &Script) -> Result<Local<'s>> {
        not_implemented!("Scope::run_script", script)
    }

    /// `compile_script` and `run_script` in one.
    pub fn eval_script(&mut self, realm: &Realm, source: Source<'_>) -> Result<Local<'s>> {
        let script = self.compile_script(realm, source)?;
        self.run_script(&script)
    }

    /// `ParseModule`: compiles `source` as a module. The module is
    /// [`ModuleStatus::New`]; its imports are not resolved yet.
    pub fn parse_module(&mut self, realm: &Realm, source: Source<'_>) -> Result<Module> {
        not_implemented!("Scope::parse_module", realm, source)
    }

    /// A synthetic module: one whose exports are set by the embedder, so a host
    /// can offer JSON modules, or wrap CommonJS, without engine changes.
    /// `evaluate` runs when the module is evaluated and sets the exports with
    /// [`Scope::set_synthetic_export`]. Whether Phase 7 builds this is an open
    /// question in the README; the contract reserves it.
    pub fn new_synthetic_module(
        &mut self,
        realm: &Realm,
        export_names: &[&str],
        evaluate: impl for<'a> Fn(&mut Scope<'a>, &Module) -> Result<()> + Send + 'static,
    ) -> Result<Module> {
        not_implemented!("Scope::new_synthetic_module", realm, export_names, evaluate)
    }

    /// `SetSyntheticModuleExport`.
    pub fn set_synthetic_export(
        &mut self,
        module: &Module,
        name: &str,
        value: Local<'_>,
    ) -> Result<()> {
        not_implemented!("Scope::set_synthetic_export", module, name, value)
    }

    /// `LoadRequestedModules()`: asks the host, through
    /// [`Host::load_imported_module`], for every module `module` imports,
    /// then theirs. Returns a promise that settles when all are loaded or one
    /// failed.
    pub fn load_requested_modules(&mut self, module: &Module) -> Result<Local<'s>> {
        not_implemented!("Scope::load_requested_modules", module)
    }

    /// `FinishLoadingImportedModule`: the host's answer to one
    /// [`Host::load_imported_module`] request: the module, or the error to
    /// reject with. It consumes the payload.
    pub fn finish_loading_imported_module(
        &mut self,
        payload: LoadPayload,
        result: core::result::Result<Module, Exception>,
    ) -> Result<()> {
        not_implemented!("Scope::finish_loading_imported_module", payload, result)
    }

    /// `Link()`: resolves exports and creates bindings. Needs every import
    /// loaded, so call it after the promise from
    /// [`Scope::load_requested_modules`] has fulfilled. A link error is a
    /// thrown `SyntaxError`.
    pub fn link(&mut self, module: &Module) -> Result<()> {
        not_implemented!("Scope::link", module)
    }

    /// `Evaluate()`: runs the module and its imports, returning a promise that
    /// settles when evaluation (including top-level `await`) has finished.
    pub fn evaluate_module(&mut self, module: &Module) -> Result<Local<'s>> {
        not_implemented!("Scope::evaluate_module", module)
    }

    /// `GetModuleNamespace`: the module's namespace object. The module must be
    /// linked.
    pub fn module_namespace(&mut self, module: &Module) -> Result<Local<'s>> {
        not_implemented!("Scope::module_namespace", module)
    }

    /// The module's status.
    pub fn module_status(&self, module: &Module) -> Result<ModuleStatus> {
        not_implemented!("Scope::module_status", module)
    }

    /// The data attached to a script, module or realm by whoever made it.
    pub fn host_defined(&self, referrer: Referrer<'_>) -> Result<Option<&(dyn Any + Send)>> {
        not_implemented!("Scope::host_defined", referrer)
    }

    // ---- The collector and the language's own host calls ----------------------------

    /// Runs a full collection now. This is `$262.gc()`, and what a limit
    /// check does before it gives up. It runs the host's
    /// [`trace_roots`](Host::trace_roots) and every host object's `trace`.
    pub fn gc(&mut self) -> Result<()> {
        not_implemented!("Scope::gc")
    }

    /// `ClearKeptObjects`: lets `WeakRef` targets read during this turn be
    /// collected. ECMA-262 makes the host call it when a synchronous run of
    /// JavaScript ends; HTML does so after each microtask checkpoint.
    pub fn clear_kept_objects(&mut self) -> Result<()> {
        not_implemented!("Scope::clear_kept_objects")
    }
}
