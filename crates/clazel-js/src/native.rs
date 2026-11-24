//! Native functions and host objects: how Rust code becomes part of a
//! JavaScript program.

use core::any::Any;
use core::marker::PhantomData;

use clazel_js_heap::value::Value;

use crate::error::Result;
use crate::scope::Scope;
use crate::value::{Key, Local, Member, PropertyDescriptor};

/// What a native function is called with.
///
/// `this` and the arguments are [`Local`]s of the call's own scope, so the
/// function can use them freely and cannot keep them. A missing argument is
/// `undefined`, as for any JavaScript function.
///
/// ```
/// use clazel_js::{Args, Callable, Key, Local, Result, Scope};
///
/// /// `add(a, b)` as JavaScript sees it.
/// fn add<'s>(scope: &mut Scope<'s>, args: &Args<'s>) -> Result<Local<'s>> {
///     let a = scope.to_number(args.get(0))?;
///     let b = scope.to_number(args.get(1))?;
///     Ok(scope.number(a + b))
/// }
/// # let mut rt = clazel_js::Runtime::new(clazel_js::Config::new(clazel_js::Limits::unlimited()), clazel_js::DefaultHost::new())?;
/// # let sum = rt.scope(|scope| {
/// #     let function = scope.function("add", 2, Callable::Function, add)?;
/// #     let this = scope.undefined();
/// #     let (a, b) = (scope.number(40.0), scope.number(2.0));
/// #     let sum = scope.call(function, this, &[a, b])?;
/// #     // A missing argument is `undefined`, which is NaN as a number.
/// #     let missing = scope.call(function, this, &[a])?;
/// #     assert!(scope.as_number(missing).is_some_and(f64::is_nan));
/// #     let _ = Key::from("unused");
/// #     Ok(scope.as_number(sum))
/// # })?;
/// # assert_eq!(sum, Some(42.0));
/// # Ok::<(), clazel_js::Error>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Args<'s> {
    runtime: usize,
    this: Value,
    args: &'s [Value],
    new_target: Value,
}

impl<'s> Args<'s> {
    pub(crate) fn new(runtime: usize, this: Value, args: &'s [Value], new_target: Value) -> Self {
        Args {
            runtime,
            this,
            args,
            new_target,
        }
    }

    /// The `this` value.
    pub fn this(&self) -> Local<'s> {
        Local::new(self.this, self.runtime)
    }

    /// How many arguments the caller passed.
    pub fn len(&self) -> usize {
        self.args.len()
    }

    /// Whether the caller passed no arguments.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Argument `index`, or `undefined` if the caller passed fewer.
    pub fn get(&self, index: usize) -> Local<'s> {
        let value = self.args.get(index).copied().unwrap_or(Value::UNDEFINED);
        Local::new(value, self.runtime)
    }

    /// `new.target`: `Some` when the function was called with `new` (or by
    /// `Reflect.construct`), and the constructor `new` was applied to, which
    /// may be a subclass. `None` for an ordinary call.
    pub fn new_target(&self) -> Option<Local<'s>> {
        (self.new_target != Value::UNDEFINED).then(|| Local::new(self.new_target, self.runtime))
    }
}

/// Whether a native function can be used with `new`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Callable {
    /// An ordinary function: `new` throws a `TypeError`, and
    /// [`Args::new_target`] is always `None`. What WebIDL calls an operation.
    #[default]
    Function,
    /// A constructor: `new` calls it with [`Args::new_target`] set. A call
    /// without `new` is the function's own business; it can throw. What
    /// WebIDL calls an interface object.
    Constructor,
}

/// A request to run a native function body on behalf of the engine. Boxed
/// closures of this shape are what [`Scope::function`] takes.
///
/// `Fn`, not `FnMut`: a native function can be re-entered through JavaScript
/// it calls, so mutable state it needs goes in a host object, in the
/// [`Host`](crate::Host), or behind a lock, and not in the closure. `Send`
/// because the [`Runtime`](crate::Runtime) is.
pub type NativeFn = dyn for<'s> Fn(&mut Scope<'s>, &Args<'s>) -> Result<Local<'s>> + Send;

/// What [`Scope::shared_function`] takes: a [`NativeFn`] that is also `Sync`,
/// so the runtime can share it with each call that runs it, and JavaScript
/// can re-enter it while it runs (README open question 14).
pub type SharedNativeFn =
    dyn for<'s> Fn(&mut Scope<'s>, &Args<'s>) -> Result<Local<'s>> + Send + Sync;

/// An answer from an exotic hook: do what an ordinary object does, or here is
/// the answer.
#[derive(Clone, Copy, Debug)]
pub enum Exotic<T> {
    /// No special behaviour for this key: the engine continues as for an
    /// ordinary object (looking at the object's own properties, then its
    /// prototype).
    Ordinary,
    /// The embedder's answer.
    Handled(T),
}

/// The data of a host object, and the object's special behaviour.
///
/// A host object is a JavaScript object that carries a Rust value, which the
/// embedder owns. This is how `clazel-webidl` builds a wrapper for a DOM
/// node: the wrapper is a JavaScript object, and its data says which node.
///
/// - **Typed.** The data's type is the slot's type. [`Scope::host_data`] and
///   [`Scope::host_data_mut`] check it and give
///   [`Error::WrongType`](crate::Error::WrongType) for any other object, so a
///   method called on the wrong `this` is a defined error and never a
///   reinterpreted pointer.
/// - **Lifetime.** The data is dropped, on the runtime's thread, when the
///   collector frees the object or the runtime is dropped.
/// - **Tracing.** If the data refers to other JavaScript values it reports
///   them from [`trace`](HostObject::trace), using [`Member`]. The default
///   reports nothing.
/// - **Exotic behaviour.** The four hooks let a host object be what WebIDL
///   calls a legacy platform object: `NodeList[0]`, `HTMLCollection.byName`,
///   `localStorage.key`. Each defaults to [`Exotic::Ordinary`], and the
///   engine checks the result against ECMA-262's invariants for the internal
///   method (a non-configurable property cannot be reported missing, and so
///   on), throwing `TypeError` if the hook breaks them. While a hook runs the
///   object's data is lent to it and taken out of the object, so another
///   access to the same data gets [`Error::Busy`](crate::Error::Busy).
/// - **Which hooks exist** is an open question in the README: these four are
///   what WebIDL §3.9 and §3.10 appear to need and the list may grow.
///
/// The hooks are not called yet (the VM has no exotic dispatch), so this
/// example only compiles and runs its type checks:
///
/// ```
/// use clazel_js::{Exotic, HostObject, Key, Local, PropertyDescriptor, Result, Runtime, Scope};
///
/// /// The data of a `NodeList` wrapper: the ids of the nodes it holds.
/// struct NodeList {
///     nodes: Vec<u64>,
/// }
///
/// impl HostObject for NodeList {
///     fn get_own_property<'s>(
///         &mut self,
///         scope: &mut Scope<'s>,
///         _this: Local<'s>,
///         key: Key<'_, 's>,
///     ) -> Result<Exotic<Option<PropertyDescriptor<'s>>>> {
///         let Key::Index(i) = key else { return Ok(Exotic::Ordinary) };
///         let Some(id) = self.nodes.get(i as usize) else {
///             return Ok(Exotic::Handled(None));
///         };
///         let wrapper = scope.number(*id as f64); // a real binding makes the node's wrapper
///         Ok(Exotic::Handled(Some(PropertyDescriptor {
///             value: Some(wrapper),
///             writable: Some(false),
///             enumerable: Some(true),
///             configurable: Some(true),
///             ..PropertyDescriptor::default()
///         })))
///     }
/// }
///
/// fn make(rt: &mut Runtime) -> clazel_js::Result<()> {
///     rt.scope(|scope| {
///         let list = scope.new_host_object(None, NodeList { nodes: vec![1, 2] })?;
///         let n = scope.host_data::<NodeList>(list)?.nodes.len();
///         assert_eq!(n, 2);
///         Ok(())
///     })
/// }
/// ```
pub trait HostObject: Any + Send {
    /// Reports every [`Member`] this data holds. See [`Tracer`].
    fn trace(&self, tracer: &mut Tracer<'_>) {
        let _ = tracer;
    }

    /// `[[GetOwnProperty]]` for `key`.
    fn get_own_property<'s>(
        &mut self,
        scope: &mut Scope<'s>,
        this: Local<'s>,
        key: Key<'_, 's>,
    ) -> Result<Exotic<Option<PropertyDescriptor<'s>>>> {
        let _ = (scope, this, key);
        Ok(Exotic::Ordinary)
    }

    /// `[[DefineOwnProperty]]` for `key`. `Handled(true)` means it succeeded
    /// and `Handled(false)` that it was refused.
    fn define_own_property<'s>(
        &mut self,
        scope: &mut Scope<'s>,
        this: Local<'s>,
        key: Key<'_, 's>,
        descriptor: PropertyDescriptor<'s>,
    ) -> Result<Exotic<bool>> {
        let _ = (scope, this, key, descriptor);
        Ok(Exotic::Ordinary)
    }

    /// `[[Delete]]` for `key`.
    fn delete_property<'s>(
        &mut self,
        scope: &mut Scope<'s>,
        this: Local<'s>,
        key: Key<'_, 's>,
    ) -> Result<Exotic<bool>> {
        let _ = (scope, this, key);
        Ok(Exotic::Ordinary)
    }

    /// The extra own keys `[[OwnPropertyKeys]]` should list, which the
    /// engine puts in front of the object's ordinary keys in the order
    /// ECMA-262 fixes (indices first). `Handled` keys that are not strings,
    /// symbols or indices are a `TypeError`.
    fn own_property_keys<'s>(
        &mut self,
        scope: &mut Scope<'s>,
        this: Local<'s>,
    ) -> Result<Exotic<Vec<Local<'s>>>> {
        let _ = (scope, this);
        Ok(Exotic::Ordinary)
    }
}

/// The collector's marker, handed to [`HostObject::trace`] and
/// [`Host::trace_roots`](crate::Host::trace_roots).
///
/// During a collection the engine calls each live host object's `trace`, and
/// the host's `trace_roots` once. Everything reported is treated as reachable
/// from there. Collection runs only at points the engine chooses (phase-7.md
/// item 7.6), and tracing cannot run JavaScript or allocate: the type gives it
/// no [`Scope`].
#[derive(Debug)]
pub struct Tracer<'a> {
    _collector: PhantomData<&'a mut ()>,
}

impl Tracer<'_> {
    /// Reports that the value is reachable. Reporting one twice is fine, and
    /// reporting a stale one is ignored (the generation check).
    pub fn mark(&mut self, member: Member) {
        let _ = member;
    }
}
