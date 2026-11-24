//! Values and the four ways to hold one: [`Local`], [`Handle`], [`Weak`] and
//! [`Member`].
//!
//! All four are opaque. In the implementation each is a heap reference (a
//! `u32` arena index and a `u16` generation, phase-7.md item 7.5) plus what
//! its kind of root needs, and every use checks the generation, so a stale
//! one is an [`Error::StaleHandle`](crate::Error::StaleHandle) and never an
//! alias of some other object.

use core::marker::PhantomData;
use std::sync::Arc;

use clazel_js_heap::value::Value;

/// A value, rooted for the lifetime `'s` of the [`Scope`](crate::Scope) that
/// made it.
///
/// This is the type an embedder works with. The collector sees every `Local`
/// of every live scope, so holding one is always safe, and it costs nothing
/// to drop. It is `Copy`.
///
/// It cannot be kept past its scope: `'s` is a lifetime the compiler picks
/// for each [`Runtime::scope`](crate::Runtime::scope) call and will not let
/// out of the closure. To keep a value longer, turn it into a [`Handle`]
/// with [`Scope::persist`](crate::Scope::persist).
///
/// ```compile_fail
/// use clazel_js::{Local, Runtime};
///
/// fn leak(rt: &mut Runtime) {
///     // Does not compile: the `Local` would outlive its scope.
///     let escaped: Local<'_> = rt.scope(|scope| scope.number(1.0));
///     let _ = escaped;
/// }
/// ```
///
/// ```
/// use clazel_js::{Key, Runtime};
///
/// fn make_point(rt: &mut Runtime) -> clazel_js::Result<()> {
///     rt.scope(|scope| {
///         let point = scope.new_object()?;
///         let x = scope.number(3.0);
///         scope.set(point, Key::from("x"), x)?;
///         Ok(())
///     })
/// }
/// # let mut rt = clazel_js::Runtime::new(clazel_js::Config::new(clazel_js::Limits::unlimited()), clazel_js::DefaultHost::new())?;
/// # make_point(&mut rt)?;
/// # Ok::<(), clazel_js::Error>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Local<'s> {
    value: Value,
    /// Which runtime made it, so a `Local` handed to the scope of another
    /// runtime is `Error::WrongRuntime`, not a read of the wrong heap.
    runtime: usize,
    _scope: PhantomData<&'s ()>,
}

/// A value kept alive across scopes and calls: a persistent root.
///
/// - **Lifetime.** The value stays reachable until the last clone of the
///   `Handle` is dropped. Dropping needs no access to the `Runtime`: the
///   release is queued and the collector applies it, so a `Handle` can be
///   dropped on any thread. A `Handle` held inside a value that the
///   collector would otherwise free keeps that value alive, which makes a
///   cycle a leak. Data that a [host object](crate::HostObject) keeps about
///   other JavaScript values should use [`Member`], which does not.
/// - **Threads.** `Handle` is `Send` and `Sync`, because it names a value
///   but cannot read it. Using it needs the owning [`Runtime`](crate::Runtime)
///   (through a [`Scope`](crate::Scope)); a scope of another runtime gives
///   [`Error::WrongRuntime`](crate::Error::WrongRuntime).
/// - **Cost.** A root table slot per live `Handle`. Use [`Local`] inside a
///   call and `Handle` only for what outlives it.
///
/// ```
/// use clazel_js::{Handle, Runtime, ValueKind};
///
/// fn remember(rt: &mut Runtime) -> clazel_js::Result<Handle> {
///     rt.scope(|scope| {
///         let list = scope.new_object()?;
///         Ok(scope.persist(list))
///     })
/// }
///
/// fn use_later(rt: &mut Runtime, list: &Handle) -> clazel_js::Result<ValueKind> {
///     rt.scope(|scope| {
///         let list = scope.local(list)?;
///         Ok(scope.kind(list))
///     })
/// }
/// # let mut rt = clazel_js::Runtime::new(clazel_js::Config::new(clazel_js::Limits::unlimited()), clazel_js::DefaultHost::new())?;
/// # let handle = remember(&mut rt)?;
/// # assert_eq!(use_later(&mut rt, &handle)?, ValueKind::Object);
/// # Ok::<(), clazel_js::Error>(())
/// ```
#[derive(Clone, Debug)]
pub struct Handle {
    /// The runtime's identity token: the handle keeps it alive, so its address
    /// names the runtime for as long as any handle does, and a handle can be
    /// dropped on any thread without the runtime.
    token: Arc<()>,
    value: Value,
}

/// A value held without keeping it alive.
///
/// [`Scope::upgrade`](crate::Scope::upgrade) gives a [`Local`] while the value
/// lives and `None` once the collector has freed it. This is the tool for a
/// side table from platform objects to their JavaScript wrappers: the table
/// must not stop an unreachable wrapper being collected.
///
/// ```
/// use clazel_js::{Runtime, Weak};
///
/// fn cache(rt: &mut Runtime) -> clazel_js::Result<Weak> {
///     rt.scope(|scope| {
///         let wrapper = scope.new_object()?;
///         Ok(scope.downgrade(wrapper))
///     })
/// }
///
/// fn lookup(rt: &mut Runtime, weak: &Weak) -> clazel_js::Result<bool> {
///     rt.scope(|scope| Ok(scope.upgrade(weak)?.is_some()))
/// }
/// # let mut rt = clazel_js::Runtime::new(clazel_js::Config::new(clazel_js::Limits::unlimited()), clazel_js::DefaultHost::new())?;
/// # let weak = cache(&mut rt)?;
/// # // There is no collector yet, so a value is never freed.
/// # assert!(lookup(&mut rt, &weak)?);
/// # Ok::<(), clazel_js::Error>(())
/// ```
#[derive(Clone, Debug)]
pub struct Weak {
    token: Arc<()>,
    value: Value,
}

/// A reference to a value that is kept alive only if the owner reports it to
/// the collector, from [`HostObject::trace`](crate::HostObject::trace) or
/// [`Host::trace_roots`](crate::Host::trace_roots).
///
/// This is how a host object holds JavaScript values (an event listener's
/// callback, say) without a cycle that can never be collected. `Member` is
/// `Copy` and cheap, and it does not root anything by itself. If its owner
/// forgets to report it and the value is collected, reading it gives
/// [`Error::StaleHandle`](crate::Error::StaleHandle) (the generation check), never
/// the wrong object. A member the owner reports is as strong as a [`Handle`].
///
/// ```
/// use clazel_js::{HostObject, Member, Tracer};
///
/// /// A DOM event target's data: its listeners' callbacks.
/// struct Listeners {
///     callbacks: Vec<Member>,
/// }
///
/// impl HostObject for Listeners {
///     fn trace(&self, tracer: &mut Tracer<'_>) {
///         for callback in &self.callbacks {
///             tracer.mark(*callback);
///         }
///     }
/// }
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Member {
    value: Value,
    runtime: usize,
}

/// What kind of value a [`Local`] is: the result of `typeof`, with `null` and
/// functions told apart.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValueKind {
    /// `undefined`.
    Undefined,
    /// `null`.
    Null,
    /// `true` or `false`.
    Boolean,
    /// A Number.
    Number,
    /// A BigInt.
    BigInt,
    /// A String.
    String,
    /// A Symbol.
    Symbol,
    /// An object that is not callable.
    Object,
    /// A callable object.
    Function,
}

/// A property key as an embedder writes it.
///
/// Strings are `&str`, so a key with a lone surrogate must be made as a
/// [`Local`] string with [`Scope::string_utf16`](crate::Scope::string_utf16) and
/// passed as [`Key::Value`]. `Key::Index` is an array index, the form
/// element access takes.
///
/// There are no Arrays or Symbols in the VM yet, so this uses an ordinary
/// object and a string held as a value:
///
/// ```
/// use clazel_js::{Key, Runtime};
///
/// fn keys(rt: &mut Runtime) -> clazel_js::Result<()> {
///     rt.scope(|scope| {
///         let list = scope.new_object()?;
///         let hello = scope.string("hello");
///         scope.set(list, Key::Index(0), hello)?;
///         let name = scope.string("0");
///         let again = scope.get(list, Key::Value(name))?;
///         assert!(scope.strict_equals(again, hello));
///         let same = scope.get(list, Key::from("0"))?;
///         assert!(scope.strict_equals(same, hello));
///         Ok(())
///     })
/// }
/// # let mut rt = clazel_js::Runtime::new(clazel_js::Config::new(clazel_js::Limits::unlimited()), clazel_js::DefaultHost::new())?;
/// # keys(&mut rt)?;
/// # Ok::<(), clazel_js::Error>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub enum Key<'a, 's> {
    /// A string key.
    Str(&'a str),
    /// An array index (a `u32` below 2^32 - 1).
    Index(u32),
    /// Any string or symbol held as a value.
    Value(Local<'s>),
}

impl<'a> From<&'a str> for Key<'a, '_> {
    fn from(s: &'a str) -> Self {
        Key::Str(s)
    }
}

impl From<u32> for Key<'_, '_> {
    fn from(i: u32) -> Self {
        Key::Index(i)
    }
}

/// A property descriptor (ECMA-262 §6.2.6): each field present only when set.
///
/// A descriptor with `value` or `writable` is a data descriptor, one with
/// `get` or `set` an accessor descriptor, and mixing them is a `TypeError`
/// from [`Scope::define_property`](crate::Scope::define_property).
/// For `get` and `set`, a `Local` that is `undefined` means "no function".
///
/// ```
/// use clazel_js::{PropertyDescriptor, Runtime, Key};
///
/// fn read_only(rt: &mut Runtime) -> clazel_js::Result<()> {
///     rt.scope(|scope| {
///         let object = scope.new_object()?;
///         let seven = scope.number(7.0);
///         scope.define_property(
///             object,
///             Key::from("answer"),
///             PropertyDescriptor {
///                 value: Some(seven),
///                 writable: Some(false),
///                 enumerable: Some(true),
///                 configurable: Some(false),
///                 ..PropertyDescriptor::default()
///             },
///         )?;
///         let eight = scope.number(8.0);
///         assert!(scope.set(object, Key::from("answer"), eight).is_err());
///         Ok(())
///     })
/// }
/// # let mut rt = clazel_js::Runtime::new(clazel_js::Config::new(clazel_js::Limits::unlimited()), clazel_js::DefaultHost::new())?;
/// # read_only(&mut rt)?;
/// # Ok::<(), clazel_js::Error>(())
/// ```
#[derive(Clone, Copy, Debug, Default)]
pub struct PropertyDescriptor<'s> {
    /// `[[Value]]`.
    pub value: Option<Local<'s>>,
    /// `[[Writable]]`.
    pub writable: Option<bool>,
    /// `[[Get]]`.
    pub get: Option<Local<'s>>,
    /// `[[Set]]`.
    pub set: Option<Local<'s>>,
    /// `[[Enumerable]]`.
    pub enumerable: Option<bool>,
    /// `[[Configurable]]`.
    pub configurable: Option<bool>,
}

/// The well-known symbols (ECMA-262 §6.1.5.1), the ones an embedder needs to
/// build objects other code can iterate or convert.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum WellKnownSymbol {
    /// `Symbol.asyncIterator`.
    AsyncIterator,
    /// `Symbol.hasInstance`.
    HasInstance,
    /// `Symbol.isConcatSpreadable`.
    IsConcatSpreadable,
    /// `Symbol.iterator`.
    Iterator,
    /// `Symbol.toPrimitive`.
    ToPrimitive,
    /// `Symbol.toStringTag`.
    ToStringTag,
    /// `Symbol.unscopables`.
    Unscopables,
}

/// A promise's state, from [`Scope::promise_state`](crate::Scope::promise_state).
#[derive(Clone, Copy, Debug)]
pub enum PromiseState<'s> {
    /// Not yet settled.
    Pending,
    /// Fulfilled with this value.
    Fulfilled(Local<'s>),
    /// Rejected with this reason.
    Rejected(Local<'s>),
}

// The constructors and readers below are the crate's own: the representation
// is private, and `Scope` is the only code that makes or opens one.
impl<'s> Local<'s> {
    pub(crate) fn new(value: Value, runtime: usize) -> Local<'s> {
        Local {
            value,
            runtime,
            _scope: PhantomData,
        }
    }

    pub(crate) fn value(self) -> Value {
        self.value
    }

    pub(crate) fn runtime(self) -> usize {
        self.runtime
    }
}

impl Handle {
    pub(crate) fn new(token: Arc<()>, value: Value) -> Handle {
        Handle { token, value }
    }

    pub(crate) fn value(&self) -> Value {
        self.value
    }

    pub(crate) fn token(&self) -> &Arc<()> {
        &self.token
    }
}

impl Weak {
    pub(crate) fn new(token: Arc<()>, value: Value) -> Weak {
        Weak { token, value }
    }

    pub(crate) fn value(&self) -> Value {
        self.value
    }

    pub(crate) fn token(&self) -> &Arc<()> {
        &self.token
    }
}

impl Member {
    pub(crate) fn new(value: Value, runtime: usize) -> Member {
        Member { value, runtime }
    }

    pub(crate) fn value(self) -> Value {
        self.value
    }

    pub(crate) fn runtime(self) -> usize {
        self.runtime
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn is_send_sync<T: Send + Sync>() {}

    #[test]
    fn persistent_roots_can_be_held_and_dropped_on_any_thread() {
        is_send_sync::<Handle>();
        is_send_sync::<Weak>();
        is_send_sync::<crate::Realm>();
        is_send_sync::<crate::Script>();
        is_send_sync::<crate::Module>();
        is_send_sync::<crate::Job>();
        is_send_sync::<crate::Resolvers>();
        is_send_sync::<crate::Exception>();
        is_send_sync::<crate::Error>();
    }
}
