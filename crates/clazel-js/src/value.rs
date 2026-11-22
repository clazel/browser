//! Values and the four ways to hold one: [`Local`], [`Handle`], [`Weak`] and
//! [`Member`].
//!
//! All four are opaque. In the implementation each is a heap reference (a
//! `u32` arena index and a `u16` generation, phase-7.md item 7.5) plus what
//! its kind of root needs, and every use checks the generation, so a stale
//! one is an [`Error::StaleHandle`](crate::Error::StaleHandle) and never an
//! alias of some other object.

use core::marker::PhantomData;

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
/// ```no_run
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
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Local<'s> {
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
/// ```no_run
/// use clazel_js::{Handle, Runtime};
///
/// fn remember(rt: &mut Runtime) -> clazel_js::Result<Handle> {
///     rt.scope(|scope| {
///         let list = scope.new_array(0)?;
///         Ok(scope.persist(list))
///     })
/// }
///
/// fn use_later(rt: &mut Runtime, list: &Handle) -> clazel_js::Result<()> {
///     rt.scope(|scope| {
///         let list = scope.local(list)?;
///         let _kind = scope.kind(list);
///         Ok(())
///     })
/// }
/// ```
#[derive(Clone, Debug)]
pub struct Handle {
    _root: PhantomData<()>,
}

/// A value held without keeping it alive.
///
/// [`Scope::upgrade`](crate::Scope::upgrade) gives a [`Local`] while the value
/// lives and `None` once the collector has freed it. This is the tool for a
/// side table from platform objects to their JavaScript wrappers: the table
/// must not stop an unreachable wrapper being collected.
///
/// ```no_run
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
/// ```
#[derive(Clone, Debug)]
pub struct Weak {
    _value: PhantomData<()>,
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
/// ```no_run
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
    _value: PhantomData<()>,
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
/// ```no_run
/// use clazel_js::{Key, Runtime};
///
/// fn keys(rt: &mut Runtime) -> clazel_js::Result<()> {
///     rt.scope(|scope| {
///         let list = scope.new_array(2)?;
///         let hello = scope.string("hello");
///         scope.set(list, Key::Index(0), hello)?;
///         let length = scope.get(list, Key::from("length"))?;
///         let iterator = scope.well_known_symbol(clazel_js::WellKnownSymbol::Iterator);
///         let _iterate = scope.get(list, Key::Value(iterator))?;
///         let _ = length;
///         Ok(())
///     })
/// }
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
/// ```no_run
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
///         Ok(())
///     })
/// }
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

// The value representations arrive with the implementation (item 7.8). Until
// then these build the opaque shells that the stubs hand back. No caller can
// observe one, because every operation that would accept it returns
// `Error::NotImplemented`.
impl Local<'_> {
    pub(crate) fn placeholder() -> Self {
        Local {
            _scope: PhantomData,
        }
    }
}

impl Handle {
    pub(crate) fn placeholder() -> Self {
        Handle { _root: PhantomData }
    }
}

impl Weak {
    pub(crate) fn placeholder() -> Self {
        Weak {
            _value: PhantomData,
        }
    }
}

impl Member {
    pub(crate) fn placeholder() -> Self {
        Member {
            _value: PhantomData,
        }
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
