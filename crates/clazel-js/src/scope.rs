//! [`Scope`]: every operation on values, realms, code and objects.

use core::any::Any;
use core::marker::PhantomData;
use std::sync::Arc;

use clazel_js_builtins::object::{Descriptor, define_property_or_throw};
use clazel_js_builtins::util;
use clazel_js_heap::shape::Attrs;
use clazel_js_heap::string::{JsString, Key as HeapKey};
use clazel_js_heap::value::{Decoded, Value};
use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;
use clazel_js_vm::compile::{CompileError, compile_script};
use clazel_js_vm::heap::{HeapError, MAX_PROTO_DEPTH, ObjKind};
use clazel_js_vm::interp::{Abrupt, Intrinsic, Vm};

use crate::code::{
    LoadPayload, Module, ModuleStatus, Realm, RealmOptions, Referrer, Script, Source,
};
use crate::error::{Error, ErrorKind, ErrorReport, Exception, Result, not_implemented};
use crate::host::Host;
use crate::native::{Args, Callable, HostObject};
use crate::state::{LazyAccessor, State, abrupt_to_error, accessor_function_name, trampoline};
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
/// There are no Arrays in the VM yet, so the list here is an ordinary object:
///
/// ```
/// use clazel_js::{Key, Runtime};
///
/// fn sum_squares(rt: &mut Runtime, n: u32) -> clazel_js::Result<f64> {
///     rt.scope(|scope| {
///         let list = scope.new_object()?;
///         for i in 0..n {
///             // Temporaries die at the end of each pass, not at the end of the call.
///             scope.nested(|inner| {
///                 let x = inner.number(f64::from(i) * f64::from(i));
///                 inner.set(list, Key::Index(i), x)
///             })?;
///         }
///         let mut sum = 0.0;
///         for i in 0..n {
///             let x = scope.get(list, Key::Index(i))?;
///             sum += scope.as_number(x).unwrap_or(0.0);
///         }
///         Ok(sum)
///     })
/// }
/// # let mut rt = clazel_js::Runtime::new(clazel_js::Config::new(clazel_js::Limits::unlimited()), clazel_js::DefaultHost::new())?;
/// # assert_eq!(sum_squares(&mut rt, 4)?, 14.0);
/// # Ok::<(), clazel_js::Error>(())
/// ```
#[derive(Debug)]
pub struct Scope<'s> {
    /// The runtime's VM. A scope is this borrow and the runtime's identity;
    /// everything else is in the VM's embedder slot (see [`crate::state`]).
    vm: &'s mut Vm,
    runtime: usize,
    // Invariant in `'s`, so a `Local<'s>` cannot be coerced to another scope's.
    _scope: PhantomData<fn(&'s ()) -> &'s ()>,
}

/// What the heap's arena stands for in bytes, for `Limits::heap_bytes` and
/// `Runtime::heap_used`. The arena counts cells (a string, an object or an
/// environment), whose size varies, so both are estimates.
pub(crate) const CELL_BYTES: u64 = 64;

/// A key of the property tables, an `Attrs` for methods and the like.
const METHOD_ATTRS: Attrs = Attrs(Attrs::WRITABLE | Attrs::CONFIGURABLE);

// The machinery every operation uses.
impl<'s> Scope<'s> {
    pub(crate) fn new(vm: &'s mut Vm, runtime: usize) -> Scope<'s> {
        Scope {
            vm,
            runtime,
            _scope: PhantomData,
        }
    }

    /// The runtime's state.
    fn state(&self) -> Result<&State> {
        self.vm.embedder::<State>().ok_or(Error::WrongRuntime)
    }

    /// The runtime's state, mutably.
    fn state_mut(&mut self) -> Result<&mut State> {
        self.vm.embedder_mut::<State>().ok_or(Error::WrongRuntime)
    }

    /// A `Local` of this scope for a value of the VM.
    fn lv(&self, value: Value) -> Local<'s> {
        Local::new(value, self.runtime)
    }

    /// The VM's value of a `Local`, if it is of this runtime.
    fn peek(&self, local: Local<'_>) -> Option<Value> {
        (local.runtime() == self.runtime).then(|| local.value())
    }

    /// The VM's value of a `Local`: [`Error::WrongRuntime`] if it is another
    /// runtime's.
    fn val(&self, local: Local<'_>) -> Result<Value> {
        self.peek(local).ok_or(Error::WrongRuntime)
    }

    /// A VM operation's failure as this API's error.
    fn err(&mut self, abrupt: Abrupt) -> Error {
        abrupt_to_error(self.vm, abrupt)
    }

    /// A VM operation's result as this API's.
    fn run<T>(&mut self, result: core::result::Result<T, Abrupt>) -> Result<T> {
        result.map_err(|abrupt| self.err(abrupt))
    }

    /// A heap operation's failure as this API's error.
    fn heap<T>(&mut self, result: core::result::Result<T, HeapError>) -> Result<T> {
        result.map_err(|e| match e {
            HeapError::Full | HeapError::TooLong => Error::OutOfMemory,
            HeapError::Corrupt => Error::StaleHandle,
        })
    }

    /// Records the error an infallible constructor could not return, for the
    /// next operation that can fail to return instead.
    fn defer(&mut self, error: Error) {
        if let Ok(state) = self.state_mut() {
            state.deferred.get_or_insert(error);
        }
    }

    /// Returns the error an earlier infallible constructor recorded, once.
    pub(crate) fn check_deferred(&mut self) -> Result<()> {
        match self.state_mut()?.deferred.take() {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }

    /// Whether a reference still names a live cell (the arena's generation
    /// check). Values that are not references are always alive.
    fn alive(&self, value: Value) -> bool {
        value.as_ref().is_none() || self.vm.heap().cell(value).is_some()
    }

    fn token(&self) -> Arc<()> {
        match self.state() {
            Ok(state) => state.token.clone(),
            Err(_) => Arc::new(()),
        }
    }

    /// Whether a handle's token is this runtime's.
    fn owns(&self, token: &Arc<()>) -> Result<()> {
        if Arc::ptr_eq(token, &self.state()?.token) {
            Ok(())
        } else {
            Err(Error::WrongRuntime)
        }
    }

    fn persist_value(&mut self, value: Value) -> Handle {
        Handle::new(self.token(), value)
    }

    /// An object value, or [`Error::WrongType`].
    fn object(&self, local: Local<'_>) -> Result<Value> {
        let value = self.val(local)?;
        if self.vm.heap().is_object(value) {
            Ok(value)
        } else {
            Err(Error::WrongType("object"))
        }
    }

    /// A property key as the heap's interned key. A string key is interned, so
    /// a long-lived runtime that is given endlessly new names grows its
    /// interner (nothing collects it yet).
    fn heap_key(&mut self, key: Key<'_, '_>) -> Result<HeapKey> {
        match key {
            Key::Str(text) => {
                let interned = self.vm.heap_mut().intern_str(text);
                self.heap(interned)
            }
            Key::Index(index) => {
                let interned = self.vm.heap_mut().intern_str(&index.to_string());
                self.heap(interned)
            }
            Key::Value(local) => {
                let value = self.val(local)?;
                let key = self.vm.coerce_property_key(value);
                self.run(key)
            }
        }
    }

    /// A string value from a conversion that can fail for length.
    fn string_value(
        &mut self,
        text: core::result::Result<JsString, clazel_js_heap::string::TooLong>,
    ) -> Local<'s> {
        let value = match text {
            Ok(text) => self.vm.heap_mut().new_string(text),
            Err(_) => Err(HeapError::TooLong),
        };
        match value {
            Ok(value) => self.lv(value),
            Err(_) => {
                self.defer(Error::OutOfMemory);
                self.lv(Value::UNDEFINED)
            }
        }
    }

    /// An infallible constructor of something this runtime lacks.
    fn missing(&mut self, what: &'static str) -> Local<'s> {
        self.defer(Error::NotImplemented(what));
        self.lv(Value::UNDEFINED)
    }

    /// The realm: the VM's one global environment.
    fn realm(&self) -> Realm {
        Realm::new(Handle::new(self.token(), self.vm.global()))
    }

    /// [`Error::WrongRuntime`] unless the realm is this runtime's.
    fn check_realm(&self, realm: &Realm) -> Result<()> {
        let handle = realm.as_handle();
        self.owns(handle.token())?;
        if handle.value() == self.vm.global() {
            Ok(())
        } else {
            Err(Error::WrongRuntime)
        }
    }

    /// Takes the oldest job of the engine's own queue.
    pub(crate) fn pop_job(&mut self) -> Option<crate::host::Job> {
        self.state_mut().ok()?.jobs.pop_front()
    }

    /// Queues a job on the engine's own queue.
    pub(crate) fn push_job(&mut self, job: crate::host::Job) -> Result<()> {
        self.check_deferred()?;
        self.state_mut()?.jobs.push_back(job);
        Ok(())
    }
}

impl<'s> Scope<'s> {
    /// Runs `f` with an inner scope. The `Local`s `f` makes are released when
    /// it returns, and cannot escape it. What `f` returns must be owned
    /// (a [`Handle`], a number, an [`Exception`]); to keep a value, call
    /// [`Scope::persist`] inside `f`.
    pub fn nested<R>(&mut self, f: impl for<'i> FnOnce(&mut Scope<'i>) -> R) -> R {
        let runtime = self.runtime;
        let mut inner = Scope::new(&mut *self.vm, runtime);
        f(&mut inner)
    }

    // ---- Holding values ----------------------------------------------------

    /// Roots `value` beyond this scope. See [`Handle`].
    pub fn persist(&mut self, value: Local<'_>) -> Handle {
        match self.peek(value) {
            Some(value) => self.persist_value(value),
            None => {
                self.defer(Error::WrongRuntime);
                self.persist_value(Value::UNDEFINED)
            }
        }
    }

    /// The value a handle names, as a `Local` of this scope.
    /// [`Error::WrongRuntime`] if the handle is another runtime's,
    /// [`Error::StaleHandle`] if its generation does not match.
    pub fn local(&mut self, handle: &Handle) -> Result<Local<'s>> {
        self.check_deferred()?;
        self.owns(handle.token())?;
        let value = handle.value();
        if self.alive(value) {
            Ok(self.lv(value))
        } else {
            Err(Error::StaleHandle)
        }
    }

    /// A weak reference to `value`. See [`Weak`].
    pub fn downgrade(&mut self, value: Local<'_>) -> Weak {
        match self.peek(value) {
            Some(value) => Weak::new(self.token(), value),
            None => {
                self.defer(Error::WrongRuntime);
                Weak::new(self.token(), Value::UNDEFINED)
            }
        }
    }

    /// The value, if it is still alive. `Ok(None)` once it has been collected.
    pub fn upgrade(&mut self, weak: &Weak) -> Result<Option<Local<'s>>> {
        self.check_deferred()?;
        self.owns(weak.token())?;
        let value = weak.value();
        Ok(self.alive(value).then(|| self.lv(value)))
    }

    /// A [`Member`] for `value`, to store in a host object's data and report
    /// from its `trace`.
    pub fn member(&mut self, value: Local<'_>) -> Member {
        match self.peek(value) {
            Some(value) => Member::new(value, self.runtime),
            None => {
                self.defer(Error::WrongRuntime);
                Member::new(Value::UNDEFINED, self.runtime)
            }
        }
    }

    /// The value a member names. [`Error::StaleHandle`] if the owner did not
    /// report it and it has been collected.
    pub fn local_from_member(&mut self, member: Member) -> Result<Local<'s>> {
        self.check_deferred()?;
        if member.runtime() != self.runtime {
            return Err(Error::WrongRuntime);
        }
        let value = member.value();
        if self.alive(value) {
            Ok(self.lv(value))
        } else {
            Err(Error::StaleHandle)
        }
    }

    // ---- Making and reading primitive values -----------------------------

    /// `undefined`.
    pub fn undefined(&mut self) -> Local<'s> {
        self.lv(Value::UNDEFINED)
    }

    /// `null`.
    pub fn null(&mut self) -> Local<'s> {
        self.lv(Value::NULL)
    }

    /// A Boolean.
    pub fn boolean(&mut self, value: bool) -> Local<'s> {
        self.lv(Value::boolean(value))
    }

    /// A Number. NaN is canonicalized, as the value encoding requires.
    pub fn number(&mut self, value: f64) -> Local<'s> {
        self.lv(util::number(value))
    }

    /// A String from Rust text.
    pub fn string(&mut self, value: &str) -> Local<'s> {
        self.string_value(JsString::from_rust_str(value))
    }

    /// A String from UTF-16 code units, which may hold lone surrogates that a
    /// Rust `&str` cannot. This is the exact form JavaScript strings take,
    /// and what WebIDL's `DOMString` and `USVString` conversions start from.
    pub fn string_utf16(&mut self, units: &[u16]) -> Local<'s> {
        self.string_value(JsString::from_units(units))
    }

    /// A BigInt from an `i64`.
    pub fn bigint_from_i64(&mut self, value: i64) -> Local<'s> {
        let _ = value;
        self.missing("Scope::bigint_from_i64: the VM has no BigInt yet")
    }

    /// A BigInt from a `u64`.
    pub fn bigint_from_u64(&mut self, value: u64) -> Local<'s> {
        let _ = value;
        self.missing("Scope::bigint_from_u64: the VM has no BigInt yet")
    }

    /// A new unique Symbol with an optional description.
    pub fn new_symbol(&mut self, description: Option<&str>) -> Local<'s> {
        let _ = description;
        self.missing("Scope::new_symbol: the VM has no Symbols yet")
    }

    /// A well-known symbol. The same symbol in every call and every realm of
    /// this runtime, as ECMA-262 says.
    pub fn well_known_symbol(&mut self, symbol: WellKnownSymbol) -> Local<'s> {
        let _ = symbol;
        self.missing("Scope::well_known_symbol: the VM has no Symbols yet")
    }

    /// What kind of value this is. Never throws and never runs JavaScript.
    pub fn kind(&self, value: Local<'_>) -> ValueKind {
        let Some(v) = self.peek(value) else {
            return ValueKind::Undefined;
        };
        let heap = self.vm.heap();
        match v.decode() {
            Decoded::Null => ValueKind::Null,
            Decoded::Bool(_) => ValueKind::Boolean,
            Decoded::Int32(_) | Decoded::Double(_) => ValueKind::Number,
            Decoded::Ref(_) if heap.is_string(v) => ValueKind::String,
            Decoded::Ref(_) if heap.is_symbol(v) => ValueKind::Symbol,
            Decoded::Ref(_) if heap.is_callable(v) => ValueKind::Function,
            Decoded::Ref(_) if heap.is_object(v) => ValueKind::Object,
            _ => ValueKind::Undefined,
        }
    }

    /// The Boolean, or `None` if the value is not one.
    pub fn as_boolean(&self, value: Local<'_>) -> Option<bool> {
        match self.peek(value)?.decode() {
            Decoded::Bool(b) => Some(b),
            _ => None,
        }
    }

    /// The Number, or `None` if the value is not one.
    pub fn as_number(&self, value: Local<'_>) -> Option<f64> {
        util::as_number(self.peek(value)?)
    }

    /// A String's UTF-16 code units, exactly. `Err(WrongType)` for a
    /// non-string.
    pub fn string_to_utf16(&self, value: Local<'_>) -> Result<Vec<u16>> {
        let v = self.val(value)?;
        let text = self.vm.heap().string(v).ok_or(Error::WrongType("string"))?;
        Ok(text.units().collect())
    }

    /// A String as Rust text, with each lone surrogate replaced by U+FFFD.
    /// `Err(WrongType)` for a non-string.
    pub fn string_to_string_lossy(&self, value: Local<'_>) -> Result<String> {
        let v = self.val(value)?;
        let text = self.vm.heap().string(v).ok_or(Error::WrongType("string"))?;
        Ok(text.to_string_lossy())
    }

    // ---- Conversions and tests (what WebIDL's conversions are built from) --

    /// `ToBoolean`. Cannot throw.
    pub fn to_boolean(&mut self, value: Local<'_>) -> bool {
        match self.peek(value) {
            Some(v) => self.vm.to_boolean(v),
            None => {
                self.defer(Error::WrongRuntime);
                false
            }
        }
    }

    /// `ToNumber`. Can throw: a Symbol, a BigInt, or an object whose
    /// `valueOf` throws.
    pub fn to_number(&mut self, value: Local<'_>) -> Result<f64> {
        self.check_deferred()?;
        let v = self.val(value)?;
        let n = self.vm.to_number(v);
        self.run(n)
    }

    /// `ToString`, as a String value. Can throw.
    pub fn to_string(&mut self, value: Local<'_>) -> Result<Local<'s>> {
        self.check_deferred()?;
        let v = self.val(value)?;
        if self.vm.heap().is_string(v) {
            return Ok(self.lv(v));
        }
        let text = self.vm.to_js_string(v);
        let text = self.run(text)?;
        let made = self.vm.heap_mut().new_string(text);
        let made = self.heap(made)?;
        Ok(self.lv(made))
    }

    /// `ToObject`. Throws a `TypeError` for `undefined` and `null`.
    pub fn to_object(&mut self, value: Local<'_>) -> Result<Local<'s>> {
        self.check_deferred()?;
        let v = self.val(value)?;
        let o = self.vm.to_object(v);
        let o = self.run(o)?;
        Ok(self.lv(o))
    }

    /// `IsCallable`.
    pub fn is_callable(&self, value: Local<'_>) -> bool {
        self.peek(value)
            .is_some_and(|v| self.vm.heap().is_callable(v))
    }

    /// `IsConstructor`.
    pub fn is_constructor(&self, value: Local<'_>) -> bool {
        self.peek(value).is_some_and(|v| self.vm.is_constructor(v))
    }

    /// `IsArray`. Throws for a revoked proxy.
    pub fn is_array(&mut self, value: Local<'_>) -> Result<bool> {
        self.check_deferred()?;
        let v = self.val(value)?;
        Ok(self.vm.is_array(v))
    }

    /// `IsStrictlyEqual` (`===`).
    pub fn strict_equals(&self, a: Local<'_>, b: Local<'_>) -> bool {
        let (Some(x), Some(y)) = (self.peek(a), self.peek(b)) else {
            return false;
        };
        if let (Some(x), Some(y)) = (util::as_number(x), util::as_number(y)) {
            return x == y;
        }
        let heap = self.vm.heap();
        if let (Some(x), Some(y)) = (heap.string(x), heap.string(y)) {
            return x == y;
        }
        x == y
    }

    /// `SameValue` (`Object.is`).
    pub fn same_value(&self, a: Local<'_>, b: Local<'_>) -> bool {
        match (self.peek(a), self.peek(b)) {
            (Some(x), Some(y)) => util::same_value(self.vm, x, y),
            _ => false,
        }
    }

    /// `InstanceofOperator` (`value instanceof constructor`). Can throw.
    pub fn instance_of(&mut self, value: Local<'_>, constructor: Local<'_>) -> Result<bool> {
        // InstanceofOperator (§13.10.2) without step 2 (`@@hasInstance`, there
        // are no Symbols yet): step 3 is IsCallable, step 4 OrdinaryHasInstance.
        self.check_deferred()?;
        let v = self.val(value)?;
        let c = self.val(constructor)?;
        if !self.vm.heap().is_object(c) {
            let e = self
                .vm
                .type_error("Right-hand side of 'instanceof' is not an object");
            return Err(self.err(e));
        }
        if !self.vm.heap().is_callable(c) {
            let e = self
                .vm
                .type_error("Right-hand side of 'instanceof' is not callable");
            return Err(self.err(e));
        }
        if matches!(
            self.vm.heap().obj(c).map(|o| o.kind),
            Some(ObjKind::Bound(_))
        ) {
            return Err(Error::NotImplemented(
                "Scope::instance_of with a bound function: its target is not readable yet",
            ));
        }
        if !self.vm.heap().is_object(v) {
            return Ok(false);
        }
        let key = self.heap_key(Key::Str("prototype"))?;
        let proto = self.vm.get_value(c, key);
        let proto = self.run(proto)?;
        if !self.vm.heap().is_object(proto) {
            let e = self
                .vm
                .type_error("Function has non-object prototype in instanceof check");
            return Err(self.err(e));
        }
        let mut current = v;
        for _ in 0..MAX_PROTO_DEPTH {
            current = self.vm.heap().proto_of(current).unwrap_or(Value::NULL);
            if current == Value::NULL || !self.vm.heap().is_object(current) {
                return Ok(false);
            }
            if current == proto {
                return Ok(true);
            }
        }
        Err(Error::StaleHandle)
    }

    // ---- Objects ------------------------------------------------------------

    /// A new ordinary object, as `{}` in the current realm.
    pub fn new_object(&mut self) -> Result<Local<'s>> {
        self.check_deferred()?;
        let o = self.vm.new_object();
        let o = self.run(o)?;
        Ok(self.lv(o))
    }

    /// A new Array of the given length, as `new Array(length)`.
    pub fn new_array(&mut self, length: u32) -> Result<Local<'s>> {
        self.check_deferred()?;
        let a = self.vm.array_create(f64::from(length), None);
        let a = self.run(a)?;
        Ok(self.lv(a))
    }

    /// A new Array holding these values.
    pub fn new_array_from(&mut self, elements: &[Local<'_>]) -> Result<Local<'s>> {
        self.check_deferred()?;
        let mut values = Vec::with_capacity(elements.len());
        for e in elements {
            values.push(self.val(*e)?);
        }
        let a = self.vm.create_array_from_list(&values);
        let a = self.run(a)?;
        Ok(self.lv(a))
    }

    /// `Get(object, key)`. Runs getters and proxy traps, so can throw.
    pub fn get(&mut self, object: Local<'_>, key: Key<'_, '_>) -> Result<Local<'s>> {
        self.check_deferred()?;
        let o = self.val(object)?;
        let k = self.heap_key(key)?;
        let v = self.vm.get_value(o, k);
        let v = self.run(v)?;
        Ok(self.lv(v))
    }

    /// `Set(object, key, value, true)`: throws in the cases strict-mode
    /// assignment throws (a read-only property, a frozen object).
    pub fn set(&mut self, object: Local<'_>, key: Key<'_, '_>, value: Local<'_>) -> Result<()> {
        self.check_deferred()?;
        let o = self.object(object)?;
        let v = self.val(value)?;
        let k = self.heap_key(key)?;
        let done = self.vm.put_value(o, k, v, true);
        self.run(done)
    }

    /// `HasProperty` (`key in object`).
    pub fn has_property(&mut self, object: Local<'_>, key: Key<'_, '_>) -> Result<bool> {
        self.check_deferred()?;
        let o = self.object(object)?;
        let k = self.heap_key(key)?;
        let found = util::has_property(self.vm, o, k);
        let found = self.run(found)?;
        Ok(found)
    }

    /// `DeletePropertyOrThrow`, but returning `false` for a refusal instead of
    /// throwing, as sloppy-mode `delete` does.
    pub fn delete_property(&mut self, object: Local<'_>, key: Key<'_, '_>) -> Result<bool> {
        self.check_deferred()?;
        let o = self.object(object)?;
        let k = self.heap_key(key)?;
        let done = self.vm.delete_property(o, k);
        self.run(done)
    }

    /// `[[GetOwnProperty]]` (`Object.getOwnPropertyDescriptor`): the own
    /// property's complete descriptor, or `None`.
    pub fn get_own_property(
        &mut self,
        object: Local<'_>,
        key: Key<'_, '_>,
    ) -> Result<Option<PropertyDescriptor<'s>>> {
        self.check_deferred()?;
        let o = self.object(object)?;
        let k = self.heap_key(key)?;
        let found = self.vm.own_property_descriptor(o, k);
        let Some(d) = self.run(found)? else {
            return Ok(None);
        };
        Ok(Some(PropertyDescriptor {
            value: d.value.map(|v| self.lv(v)),
            writable: d.writable,
            get: d.get.map(|v| self.lv(v)),
            set: d.set.map(|v| self.lv(v)),
            enumerable: d.enumerable,
            configurable: d.configurable,
        }))
    }

    /// `DefinePropertyOrThrow`: `Object.defineProperty`.
    pub fn define_property(
        &mut self,
        object: Local<'_>,
        key: Key<'_, '_>,
        descriptor: PropertyDescriptor<'_>,
    ) -> Result<()> {
        self.check_deferred()?;
        let o = self.object(object)?;
        let k = self.heap_key(key)?;
        let value = match descriptor.value {
            Some(v) => Some(self.val(v)?),
            None => None,
        };
        let mut halves = [None, None];
        for (half, given) in halves.iter_mut().zip([descriptor.get, descriptor.set]) {
            if let Some(f) = given {
                let f = self.val(f)?;
                if f != Value::UNDEFINED && !self.vm.heap().is_callable(f) {
                    return Err(Error::WrongType("a function or undefined"));
                }
                *half = Some(f);
            }
        }
        let [get, set] = halves;
        if (get.is_some() || set.is_some()) && (value.is_some() || descriptor.writable.is_some()) {
            return Err(Error::WrongType(
                "a descriptor with accessors and no value or writable",
            ));
        }
        let desc = Descriptor {
            value,
            get,
            set,
            writable: descriptor.writable,
            enumerable: descriptor.enumerable,
            configurable: descriptor.configurable,
        };
        let done = define_property_or_throw(self.vm, o, k, &desc);
        self.run(done)
    }

    /// `GetPrototypeOf`. `null` is returned as the `null` value.
    pub fn get_prototype_of(&mut self, object: Local<'_>) -> Result<Local<'s>> {
        self.check_deferred()?;
        let o = self.object(object)?;
        let proto = self.vm.heap().proto_of(o).unwrap_or(Value::NULL);
        Ok(self.lv(proto))
    }

    /// `SetPrototypeOf`: throws if the object refuses (not extensible, or a
    /// cycle).
    pub fn set_prototype_of(&mut self, object: Local<'_>, prototype: Local<'_>) -> Result<()> {
        // OrdinarySetPrototypeOf (§10.1.2.1): an object is always extensible
        // here, so only the cycle check (step 8) can refuse.
        self.check_deferred()?;
        let o = self.object(object)?;
        let p = self.val(prototype)?;
        if p != Value::NULL && !self.vm.heap().is_object(p) {
            let e = self
                .vm
                .type_error("Object prototype may only be an Object or null");
            return Err(self.err(e));
        }
        let mut walk = p;
        for _ in 0..MAX_PROTO_DEPTH {
            if walk == Value::NULL {
                let done = self.vm.heap_mut().set_proto(o, p);
                return self.heap(done);
            }
            if walk == o {
                let e = self.vm.type_error("Cyclic prototype value");
                return Err(self.err(e));
            }
            walk = self.vm.heap().proto_of(walk).unwrap_or(Value::NULL);
        }
        Err(Error::StaleHandle)
    }

    /// `GetMethod(value, key)`: `Ok(None)` if the property is `undefined` or
    /// `null`, a `TypeError` if it is anything else but callable.
    pub fn get_method(&mut self, value: Local<'_>, key: Key<'_, '_>) -> Result<Option<Local<'s>>> {
        let f = self.get(value, key)?;
        let v = self.val(f)?;
        if v == Value::UNDEFINED || v == Value::NULL {
            return Ok(None);
        }
        if self.vm.heap().is_callable(v) {
            return Ok(Some(f));
        }
        let e = self.vm.type_error("property is not a function");
        Err(self.err(e))
    }

    /// `Call(function, this, arguments)`.
    pub fn call(
        &mut self,
        function: Local<'_>,
        this: Local<'_>,
        arguments: &[Local<'_>],
    ) -> Result<Local<'s>> {
        self.check_deferred()?;
        let f = self.val(function)?;
        let t = self.val(this)?;
        let mut args = Vec::with_capacity(arguments.len());
        for a in arguments {
            args.push(self.val(*a)?);
        }
        let r = self.vm.call(f, t, &args);
        let r = self.run(r)?;
        Ok(self.lv(r))
    }

    /// `Construct(constructor, arguments, newTarget)`; `new_target` of `None`
    /// is the constructor itself.
    pub fn construct(
        &mut self,
        constructor: Local<'_>,
        arguments: &[Local<'_>],
        new_target: Option<Local<'_>>,
    ) -> Result<Local<'s>> {
        self.check_deferred()?;
        let c = self.val(constructor)?;
        if let Some(nt) = new_target
            && self.val(nt)? != c
        {
            return Err(Error::NotImplemented(
                "Scope::construct with a new_target other than the constructor",
            ));
        }
        let mut args = Vec::with_capacity(arguments.len());
        for a in arguments {
            args.push(self.val(*a)?);
        }
        let r = self.vm.construct_value(c, &args);
        let r = self.run(r)?;
        Ok(self.lv(r))
    }

    /// Runs the iterator protocol over `iterable`, calling `f` with each value
    /// until it returns `Ok(false)` or the iterator ends. If `f` returns `Err`,
    /// or `Ok(false)`, the iterator is closed (`IteratorClose`) first. This is
    /// the operation WebIDL's `sequence<T>` and `iterable` conversions need.
    ///
    /// This stays `no_run`: `iterate` returns `NotImplemented` until the VM
    /// has Symbols and iterators.
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
        let _ = (iterable, f);
        not_implemented!("Scope::iterate: the VM has no iteration protocol or Symbols yet")
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
    /// **Re-entrance:** `f` is `Fn` so that JavaScript can call it again
    /// while it runs (HTML's `document.write` runs the parser, which runs a
    /// script, which calls `document.write`), and `Sync` because the nested
    /// call shares it with the running one (the README's open question 14).
    ///
    /// ```
    /// use clazel_js::{Args, Callable, Key, Local, Result, Runtime, Scope, Source};
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
    /// # let mut rt = clazel_js::Runtime::new(clazel_js::Config::new(clazel_js::Limits::unlimited()), clazel_js::DefaultHost::new())?;
    /// # let realm = rt.scope(|scope| scope.create_realm(clazel_js::RealmOptions::default()))?;
    /// # install(&mut rt, &realm)?;
    /// # let text = rt.scope(|scope| {
    /// #     scope.eval_script(&realm, Source::new("g.js", "var said = greet('world');"))?;
    /// #     let global = scope.global(&realm)?;
    /// #     let said = scope.get(global, Key::from("said"))?;
    /// #     scope.string_to_string_lossy(said)
    /// # })?;
    /// # assert_eq!(text, "hello, world");
    /// # Ok::<(), clazel_js::Error>(())
    /// ```
    pub fn function(
        &mut self,
        name: &str,
        length: u32,
        callable: Callable,
        f: impl for<'a> Fn(&mut Scope<'a>, &Args<'a>) -> Result<Local<'a>> + Send + Sync + 'static,
    ) -> Result<Local<'s>> {
        self.function_of(name, length, callable, Arc::new(f))
    }

    /// [`Scope::function`] for a closure that is already shared.
    fn function_of(
        &mut self,
        name: &str,
        length: u32,
        callable: Callable,
        shared: Arc<crate::native::NativeFn>,
    ) -> Result<Local<'s>> {
        self.check_deferred()?;
        let length = i32::try_from(length).unwrap_or(i32::MAX);
        let made = match callable {
            Callable::Function => self.vm.new_native(name, length, trampoline),
            Callable::Constructor => self.vm.new_native_constructor(name, length, trampoline),
        };
        let function = self.run(made)?;
        self.state_mut()?.natives.insert(function.bits(), shared);
        Ok(self.lv(function))
    }

    /// Defines the accessor property `name` of `object` from native
    /// closures, as a built-in accessor is defined: `[[Get]]` is a function
    /// named `get <name>` with `length` 0 running `getter`, `[[Set]]` a
    /// function named `set <name>` with `length` 1 running `setter` (or
    /// `undefined` without one), and the property is
    /// `{ [[Enumerable]]: enumerable, [[Configurable]]: configurable }`.
    /// It is `DefinePropertyOrThrow` (ECMA-262 §7.3.8†) with that
    /// descriptor, so it throws a `TypeError` where that does.
    ///
    /// **The two function objects are made when they are first needed.**
    /// When the property is new (the usual case: an interface's prototype
    /// being filled in), it is created at once, in its place in the
    /// object's property order and with its attributes, but the functions
    /// are not: the first `[[Get]]` or `[[Set]]` through the property, or
    /// the first `[[GetOwnProperty]]` of it, makes both, and the property
    /// holds those two objects from then on. A page's bindings define about
    /// a thousand accessors and a script uses a handful, which is why.
    ///
    /// Script cannot tell this from making them here. Creating a built-in
    /// function (§10.3.4† CreateBuiltinFunction) runs no script and changes
    /// no object but the new one, so when it happens is visible only through
    /// the function itself, and nothing reaches the function without going
    /// through the property: every operation that reads `[[Get]]` or
    /// `[[Set]]` makes them first, and operations that do not (the keys of
    /// `[[OwnPropertyKeys]]` §10.1.11.1†, `[[HasProperty]]`, the attributes)
    /// see the property that is already there. The functions' identity is
    /// stable once made, their `name`, `length` and `[[Prototype]]` are the
    /// same as an eager function's, and there is one realm. What does
    /// differ is the embedder's view: the heap is charged for the functions
    /// when they are made ([`Runtime::heap_used`](crate::Runtime::heap_used)),
    /// so a heap limit reached then is reported at that use, as for any
    /// other allocation.
    ///
    /// When the property cannot simply be created (the object has one of
    /// that name already, is not extensible, or is an Array), the functions
    /// are made now and the definition takes `DefinePropertyOrThrow`'s
    /// ordinary path.
    pub fn define_accessor(
        &mut self,
        object: Local<'_>,
        name: &str,
        getter: impl for<'a> Fn(&mut Scope<'a>, &Args<'a>) -> Result<Local<'a>> + Send + Sync + 'static,
        setter: Option<Arc<crate::native::NativeFn>>,
        enumerable: bool,
        configurable: bool,
    ) -> Result<()> {
        self.check_deferred()?;
        let o = self.object(object)?;
        let k = self.heap_key(Key::Str(name))?;
        let getter: Arc<crate::native::NativeFn> = Arc::new(getter);
        let state = self.state_mut()?;
        if let Ok(id) = u32::try_from(state.lazy_accessors.len()) {
            state.lazy_accessors.push(Some(LazyAccessor {
                name: name.into(),
                get: Arc::clone(&getter),
                set: setter.clone(),
            }));
            let deferred = self
                .vm
                .define_lazy_accessor(o, k, id, enumerable, configurable);
            if self.run(deferred)? {
                return Ok(());
            }
            // Not deferred: the entry was the last one pushed, and nothing
            // refers to it.
            self.state_mut()?.lazy_accessors.pop();
        }
        let get = self.function_of(
            &accessor_function_name("get", name),
            0,
            Callable::Function,
            getter,
        )?;
        let set = match setter {
            Some(setter) => self.function_of(
                &accessor_function_name("set", name),
                1,
                Callable::Function,
                setter,
            )?,
            None => self.undefined(),
        };
        self.define_property(
            object,
            Key::Str(name),
            PropertyDescriptor {
                get: Some(get),
                set: Some(set),
                enumerable: Some(enumerable),
                configurable: Some(configurable),
                ..PropertyDescriptor::default()
            },
        )
    }

    /// As [`Scope::function`]. Every native closure is now `Sync` and
    /// re-entrant, so the two are the same; this name stays for embedders
    /// that spell the intent (event dispatch, WebIDL callbacks), README open
    /// question 14.
    pub fn shared_function(
        &mut self,
        name: &str,
        length: u32,
        callable: Callable,
        f: impl for<'a> Fn(&mut Scope<'a>, &Args<'a>) -> Result<Local<'a>> + Send + Sync + 'static,
    ) -> Result<Local<'s>> {
        self.function(name, length, callable, f)
    }

    /// Makes a function with [`Scope::function`] and defines it as a method
    /// of `object`: writable, non-enumerable, configurable, as WebIDL
    /// operations and built-in methods are.
    pub fn define_method(
        &mut self,
        object: Local<'_>,
        name: &str,
        length: u32,
        f: impl for<'a> Fn(&mut Scope<'a>, &Args<'a>) -> Result<Local<'a>> + Send + Sync + 'static,
    ) -> Result<()> {
        self.check_deferred()?;
        let o = self.object(object)?;
        let function = self.function(name, length, Callable::Function, f)?;
        let k = self.heap_key(Key::Str(name))?;
        let v = self.val(function)?;
        let done = self.vm.heap_mut().define(o, k, v, METHOD_ATTRS);
        self.heap(done)
    }

    /// A new host object carrying `data`, with this prototype (`None` is
    /// `null`). See [`HostObject`].
    pub fn new_host_object(
        &mut self,
        prototype: Option<Local<'_>>,
        data: impl HostObject,
    ) -> Result<Local<'s>> {
        self.check_deferred()?;
        let proto = match prototype {
            Some(p) => {
                let p = self.val(p)?;
                if p != Value::NULL && !self.vm.heap().is_object(p) {
                    return Err(Error::WrongType("object or null"));
                }
                p
            }
            None => Value::NULL,
        };
        let made = self.vm.heap_mut().new_object(proto, ObjKind::Plain);
        let object = self.heap(made)?;
        self.state_mut()?
            .host_objects
            .insert(object.bits(), Box::new(data));
        Ok(self.lv(object))
    }

    /// The data of a host object of type `T`. [`Error::WrongType`] if the
    /// value is anything else (another type of host object included), and
    /// [`Error::Busy`] if one of its own hooks is running.
    pub fn host_data<T: HostObject>(&self, object: Local<'_>) -> Result<&T> {
        let o = self.val(object)?;
        let data = self
            .state()?
            .host_objects
            .get(&o.bits())
            .ok_or(Error::WrongType("a host object"))?;
        let data: &dyn Any = &**data;
        data.downcast_ref::<T>()
            .ok_or(Error::WrongType("a host object of the requested type"))
    }

    /// As [`Scope::host_data`], mutably.
    pub fn host_data_mut<T: HostObject>(&mut self, object: Local<'_>) -> Result<&mut T> {
        let o = self.val(object)?;
        let data = self
            .state_mut()?
            .host_objects
            .get_mut(&o.bits())
            .ok_or(Error::WrongType("a host object"))?;
        let data: &mut dyn Any = &mut **data;
        data.downcast_mut::<T>()
            .ok_or(Error::WrongType("a host object of the requested type"))
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
        self.check_deferred()?;
        let nt = self.val(new_target)?;
        let fb = self.val(fallback)?;
        if self.vm.heap().is_object(nt) {
            let key = self.heap_key(Key::Str("prototype"))?;
            let proto = self.vm.get_value(nt, key);
            let proto = self.run(proto)?;
            if self.vm.heap().is_object(proto) {
                return Ok(self.lv(proto));
            }
        }
        Ok(self.lv(fb))
    }

    /// The embedder's [`Host`] as its own type. [`Error::WrongType`] if the
    /// host is another type, and [`Error::Busy`] while a hook of the host is
    /// running (the hook already has the host as `&mut self`).
    pub fn host_mut<H: Host>(&mut self) -> Result<&mut H> {
        let host: &mut dyn Any = &mut *self.state_mut()?.host;
        host.downcast_mut::<H>()
            .ok_or(Error::WrongType("the host's type"))
    }

    /// For a native function: ends the call with [`Error::Terminated`] if a
    /// [`Terminator`](crate::Terminator) has been used. Call it in any native
    /// loop that can run long.
    pub fn check_terminated(&self) -> Result<()> {
        if self.vm.terminator().is_set() {
            Err(Error::Terminated)
        } else {
            Ok(())
        }
    }

    // ---- Errors ---------------------------------------------------------------

    /// A new error object of `kind` with `message`, as an [`Exception`] ready to
    /// throw or to refuse a module load with.
    pub fn new_exception(&mut self, kind: ErrorKind, message: &str) -> Result<Exception> {
        self.check_deferred()?;
        let which = match kind {
            ErrorKind::Error => Intrinsic::ErrorPrototype,
            ErrorKind::RangeError => Intrinsic::RangeErrorPrototype,
            ErrorKind::ReferenceError => Intrinsic::ReferenceErrorPrototype,
            ErrorKind::SyntaxError => Intrinsic::SyntaxErrorPrototype,
            ErrorKind::TypeError => Intrinsic::TypeErrorPrototype,
            ErrorKind::EvalError | ErrorKind::UriError => {
                return Err(Error::NotImplemented(
                    "Scope::new_exception for EvalError and URIError: the built-ins have no such constructor yet",
                ));
            }
        };
        // §20.5.6.1.1 NativeError ( message ), steps 2 to 4: `[[ErrorData]]`,
        // the intrinsic prototype and an own, non-enumerable `message`.
        let proto = self.vm.intrinsic(which);
        let made = self.vm.heap_mut().new_object(proto, ObjKind::Error);
        let object = self.heap(made)?;
        let text = JsString::from_rust_str(message).map_err(|_| Error::OutOfMemory)?;
        let text = self.vm.heap_mut().new_string(text);
        let text = self.heap(text)?;
        let k = self.heap_key(Key::Str("message"))?;
        let done = self.vm.heap_mut().define(object, k, text, METHOD_ATTRS);
        self.heap(done)?;
        Ok(Exception::from_handle(self.persist_value(object)))
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
        let value = self.exception_value(exception)?;
        let v = self.val(value)?;
        if self.vm.heap().is_object(v) {
            // Data properties only: there are no accessors to run, and
            // `get_named` runs no JavaScript.
            let name = self.vm.get_named(v, "name");
            let name = self.run(name)?;
            let message = self.vm.get_named(v, "message");
            let message = self.run(message)?;
            return Ok(ErrorReport {
                name: self.vm.string_text(name).unwrap_or_default(),
                message: self.vm.string_text(message).unwrap_or_default(),
                // The VM keeps no stack of source positions yet.
                stack: Vec::new(),
            });
        }
        // A primitive (a Symbol is the only one ToString can throw on, and
        // there are none).
        let text = self.vm.to_js_string(v);
        let text = self.run(text)?;
        Ok(ErrorReport {
            name: String::new(),
            message: text.to_string_lossy(),
            stack: Vec::new(),
        })
    }

    // ---- Promises ---------------------------------------------------------------

    /// A new pending promise and its resolving functions. For an API that
    /// returns a promise and settles it later (`fetch`).
    ///
    /// This stays `no_run`: promises return `NotImplemented` until the VM has
    /// them.
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
        not_implemented!("Scope::new_promise: the VM has no Promise objects yet")
    }

    /// Calls the promise's `resolve` with `value`. If the value is a thenable
    /// the promise follows it, as for any resolve.
    pub fn resolve_promise(&mut self, resolvers: &Resolvers, value: Local<'_>) -> Result<()> {
        let _ = (resolvers, value);
        not_implemented!("Scope::resolve_promise: the VM has no Promise objects yet")
    }

    /// Calls the promise's `reject` with `reason`.
    pub fn reject_promise(&mut self, resolvers: &Resolvers, reason: Local<'_>) -> Result<()> {
        let _ = (resolvers, reason);
        not_implemented!("Scope::reject_promise: the VM has no Promise objects yet")
    }

    /// `Promise.resolve(value)` in the current realm.
    pub fn promise_resolve(&mut self, value: Local<'_>) -> Result<Local<'s>> {
        let _ = value;
        not_implemented!("Scope::promise_resolve: the VM has no Promise objects yet")
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
        let _ = (promise, on_fulfilled, on_rejected);
        not_implemented!("Scope::promise_then: the VM has no Promise objects yet")
    }

    /// A promise's state now. Reading it never marks a rejection handled.
    pub fn promise_state(&self, promise: Local<'_>) -> Result<PromiseState<'s>> {
        let _ = promise;
        not_implemented!("Scope::promise_state: the VM has no Promise objects yet")
    }

    // ---- ArrayBuffers ------------------------------------------------------------

    /// A new `ArrayBuffer` that owns `bytes`.
    pub fn new_array_buffer(&mut self, bytes: Vec<u8>) -> Result<Local<'s>> {
        let _ = bytes;
        not_implemented!("Scope::new_array_buffer: the VM has no ArrayBuffer yet")
    }

    /// An `ArrayBuffer`'s bytes. Empty for a detached one. The borrow ends
    /// before any call that can run JavaScript, which could detach or resize it.
    pub fn array_buffer_bytes(&self, buffer: Local<'_>) -> Result<&[u8]> {
        let _ = buffer;
        not_implemented!("Scope::array_buffer_bytes: the VM has no ArrayBuffer yet")
    }

    /// `DetachArrayBuffer(buffer, key)`: after it the buffer has length 0.
    /// `key` must be the `ArrayBuffer`'s detach key if it has one, else a
    /// `TypeError`. This is Test262's `$262.detachArrayBuffer`, and what
    /// `postMessage` transfers and `structuredClone` use later.
    pub fn detach_array_buffer(&mut self, buffer: Local<'_>, key: Option<Local<'_>>) -> Result<()> {
        let _ = (buffer, key);
        not_implemented!("Scope::detach_array_buffer: the VM has no ArrayBuffer yet")
    }

    // ---- Realms ---------------------------------------------------------------------

    /// `CreateRealm` plus `SetDefaultGlobalBindings`: a new realm with its own
    /// built-ins. This is `$262.createRealm`.
    ///
    /// **Not yet:** the VM has one global environment, and
    /// [`Runtime::new`](crate::Runtime::new) has already installed the
    /// built-ins in it. The first call returns that realm and a second is
    /// [`Error::NotImplemented`]; so is `RealmOptions::global`.
    pub fn create_realm(&mut self, options: RealmOptions) -> Result<Realm> {
        self.check_deferred()?;
        if options.global.is_some() {
            return Err(Error::NotImplemented(
                "Scope::create_realm with RealmOptions::global: the VM's global is an ordinary object",
            ));
        }
        let state = self.state_mut()?;
        if state.realm_made {
            return Err(Error::NotImplemented(
                "a second realm: a VM has one global environment",
            ));
        }
        state.realm_made = true;
        Ok(self.realm())
    }

    /// The realm of the function being run. Inside a native function, the
    /// function's own realm; inside a hook, the realm of the code that
    /// triggered it, if there is one.
    pub fn current_realm(&mut self) -> Result<Realm> {
        self.check_deferred()?;
        Ok(self.realm())
    }

    /// The realm's global object. Add properties to it with [`Scope::set`] and
    /// [`Scope::define_property`]; that is how an embedder installs `console`
    /// or `window`.
    pub fn global(&mut self, realm: &Realm) -> Result<Local<'s>> {
        self.check_deferred()?;
        self.check_realm(realm)?;
        Ok(self.lv(self.vm.global()))
    }

    /// Attaches the embedder's data to a realm (HTML's environment settings
    /// object), replacing what was there.
    pub fn set_realm_host_defined(
        &mut self,
        realm: &Realm,
        data: Box<dyn Any + Send>,
    ) -> Result<()> {
        self.check_realm(realm)?;
        self.state_mut()?.realm_host_defined = Some(data);
        Ok(())
    }

    /// The data attached with [`Scope::set_realm_host_defined`].
    pub fn realm_host_defined(&self, realm: &Realm) -> Result<Option<&(dyn Any + Send)>> {
        self.check_realm(realm)?;
        Ok(self.state()?.realm_host_defined.as_deref())
    }

    // ---- Scripts and modules ------------------------------------------------------------

    /// `ParseScript`: compiles `source`. A syntax error is
    /// [`Error::Thrown`] holding a `SyntaxError` of `realm`.
    pub fn compile_script(&mut self, realm: &Realm, source: Source<'_>) -> Result<Script> {
        self.check_deferred()?;
        self.check_realm(realm)?;
        // ParseScript (§16.1.5): source text is code points.
        let points: Vec<u32> = source.text().chars().map(u32::from).collect();
        let ast = match parse(&points, SourceGoal::Script) {
            Ok(ast) => ast,
            Err(failure) => {
                let message = match failure {
                    clazel_js_syntax::api::ParseError::Syntax => "invalid script",
                    clazel_js_syntax::api::ParseError::TooDeep => "script nested too deeply",
                };
                return Err(self.throw_error(ErrorKind::SyntaxError, message));
            }
        };
        // `Limits::nesting_depth` (phase-7.md 7.19): the parser's own bound
        // is fixed (`MAX_DEPTH`), so a smaller limit is checked here, on the
        // height of the tree it built, with the same error.
        let limit = usize::try_from(self.state()?.limits.nesting_depth).unwrap_or(usize::MAX);
        if ast_height(&ast) > limit {
            return Err(self.throw_error(ErrorKind::SyntaxError, "script nested too deeply"));
        }
        let program = match compile_script(&ast, &points) {
            Ok(program) => program,
            Err(
                CompileError::NotYetCompiled { feature, .. }
                | CompileError::TooLarge(feature)
                | CompileError::Internal(feature),
            ) => return Err(Error::NotImplemented(feature)),
        };
        let loaded = self.vm.load(&program);
        let loaded = self.run(loaded)?;
        if let Some(data) = source.into_host_defined() {
            self.state_mut()?
                .script_host_defined
                .insert(loaded.main, data);
        }
        let root = Handle::new(self.token(), self.vm.global());
        Ok(Script::new(root, loaded.main))
    }

    /// `ScriptEvaluation`: runs a compiled script, returning the value of its
    /// last expression statement (the completion value, as `eval` gives).
    ///
    /// **Not yet:** the compiler's script has no completion value, so the
    /// result is always `undefined`. A script passes results out through the
    /// global object (`var result = ...;`, read with [`Scope::get`]), or
    /// through a native function. The signature does not change when the
    /// compiler gains completion values.
    pub fn run_script(&mut self, script: &Script) -> Result<Local<'s>> {
        self.check_deferred()?;
        self.owns(script.as_handle().token())?;
        let r = self.vm.run(&clazel_js_vm::interp::Script {
            main: script.main(),
        });
        let r = self.run(r)?;
        Ok(self.lv(r))
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
        match referrer {
            Referrer::Script(script) => {
                self.owns(script.as_handle().token())?;
                Ok(self
                    .state()?
                    .script_host_defined
                    .get(&script.main())
                    .map(|data| &**data))
            }
            Referrer::Realm(realm) => self.realm_host_defined(realm),
            Referrer::Module(_) => {
                not_implemented!("Scope::host_defined of a module: there are no modules yet")
            }
        }
    }

    // ---- The collector and the language's own host calls ----------------------------

    /// Runs a full collection now. This is `$262.gc()`, and what a limit
    /// check does before it gives up. It runs the host's
    /// [`trace_roots`](Host::trace_roots) and every host object's `trace`.
    pub fn gc(&mut self) -> Result<()> {
        // There is no collector yet (it is in other open pull requests): the
        // heap never frees a cell, so a full collection frees nothing and
        // nothing can observe the difference but `Runtime::heap_used`.
        self.check_deferred()
    }

    /// `ClearKeptObjects`: lets `WeakRef` targets read during this turn be
    /// collected. ECMA-262 makes the host call it when a synchronous run of
    /// JavaScript ends; HTML does so after each microtask checkpoint.
    pub fn clear_kept_objects(&mut self) -> Result<()> {
        // There are no `WeakRef`s, so no target is kept.
        self.check_deferred()
    }
}

/// The height of a parsed tree: the most nodes on a path from the root to a
/// leaf, which is what the parser's `MAX_DEPTH` bounds. The parser puts every
/// child before its parent, so one pass in order sees each child first; no
/// recursion, so the host stack does not depend on the source.
fn ast_height(ast: &clazel_js_syntax::ast::Ast) -> usize {
    let mut heights: Vec<usize> = Vec::with_capacity(ast.nodes.len());
    for node in &ast.nodes {
        let below = node
            .children
            .iter()
            .filter_map(|&c| usize::try_from(c).ok().and_then(|c| heights.get(c)))
            .copied()
            .max()
            .unwrap_or(0);
        heights.push(below.saturating_add(1));
    }
    usize::try_from(ast.root)
        .ok()
        .and_then(|r| heights.get(r))
        .copied()
        .unwrap_or(0)
}
