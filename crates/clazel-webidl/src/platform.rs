//! Platform objects and their wrappers (WebIDL §3.7†, §3.8†; phase-7.md
//! item 7.12, "Wrappers").
//!
//! <https://webidl.spec.whatwg.org/#es-platform-objects> (section numbers
//! carry the mark † of phase-7.md: the WebIDL text was not vendored at a
//! pinned commit, so they are from the living standard as read for this
//! item).
//!
//! Modelling choices:
//! - **A platform object is a key.** The embedder (`clazel-web`) owns the
//!   objects themselves (nodes of a `clazel-dom` arena, events, the window)
//!   and names each with an [`ObjectKey`] it chooses. The bindings never look
//!   inside a key.
//! - **One wrapper per platform object**, made on first access ([`wrap`]):
//!   a host object of `clazel-js` carrying a [`Wrapper`] (the key and the
//!   interface), whose prototype is the interface prototype object of the
//!   object's most derived interface. The embedder stores it
//!   ([`Platform::wrapper`] and [`Platform::set_wrapper`]): in the wrapper
//!   slot of `clazel-dom` for nodes, in a side table for the others.
//! - **The global object is the Window's wrapper.** `clazel-js` cannot yet
//!   make a realm whose global object is a host object (its README, "What
//!   is implemented"), so the ordinary global object stands for the
//!   `Window` platform object: [`Platform::window_key`] is its key, and
//!   "implements" ([`implements`]) accepts the global object for it.
//! - **The interface prototype objects live in [`Bindings`]**, which the
//!   embedder keeps ([`Platform::bindings`]); one realm, as `clazel-js` has.
//! - **Wrappers are kept by strong handles.** `clazel-js` has no collector
//!   yet (`Weak` is always alive), so a strong [`Handle`] costs nothing more,
//!   and keeps a wrapper's own properties for as long as the platform object
//!   lives, which is what WebIDL requires of the identity of a wrapper.

use std::collections::HashMap;

use clazel_js::{Args, ErrorKind, Handle, Host, HostObject, Key, Local, Result, Scope};

use crate::convert::DomString;
use crate::generated::bindings::{AllInterfaces, InterfaceId};

/// A platform object, as the embedder names it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ObjectKey(pub u64);

/// The internal data of a wrapper: which platform object it stands for, and
/// its most derived interface.
#[derive(Clone, Copy, Debug)]
pub struct Wrapper {
    /// The platform object.
    pub key: ObjectKey,
    /// The object's interface (WebIDL: "the interface the platform object
    /// implements", its most derived one).
    pub interface: InterfaceId,
}

impl HostObject for Wrapper {}

/// What the bindings need of the embedder. The embedder is the `clazel-js`
/// [`Host`], so a native function reaches it with `Scope::host_mut`.
pub trait Platform: Host + Sized + 'static {
    /// The most derived interface of a platform object, or `None` if the key
    /// names nothing (it is then never wrapped).
    fn interface_of(&mut self, key: ObjectKey) -> Option<InterfaceId>;
    /// The wrapper made for `key`, if one was.
    fn wrapper(&mut self, key: ObjectKey) -> Option<Handle>;
    /// Keeps `wrapper` as the one wrapper of `key`.
    fn set_wrapper(&mut self, key: ObjectKey, wrapper: Handle);
    /// The key of the `Window`, whose wrapper is the global object.
    fn window_key(&self) -> ObjectKey;
    /// The bindings' per-realm state.
    fn bindings(&mut self) -> &mut Bindings;
    /// The value of the content attribute `name` of the element `this`, for
    /// `[Reflect]` (HTML §2.6.1† "reflect": "get an attribute value by
    /// namespace and local name" with the null namespace).
    ///
    /// # Errors
    /// A `TypeError` if `this` is not an element.
    fn reflect_get(scope: &mut Scope<'_>, this: ObjectKey, name: &str)
    -> Result<Option<DomString>>;
    /// Sets (`Some`) or removes (`None`) the content attribute `name` of the
    /// element `this`, for `[Reflect]`.
    ///
    /// # Errors
    /// A `TypeError` if `this` is not an element.
    fn reflect_set(
        scope: &mut Scope<'_>,
        this: ObjectKey,
        name: &str,
        value: Option<DomString>,
    ) -> Result<()>;
}

/// The error of a member the platform does not implement: a
/// `NotSupportedError` `DOMException` naming it (what every generated trait
/// method does by default).
#[must_use]
pub fn not_implemented<P: Platform>(scope: &mut Scope<'_>, what: &str) -> clazel_js::Error {
    let message = format!("{what} is not implemented");
    crate::exception::throw::<P>(
        scope,
        crate::exception::DomErrorName::NotSupportedError,
        &message,
    )
}

/// The bindings' state for the one realm: the interface objects and
/// interface prototype objects, and the `[SameObject]` cache.
#[derive(Debug, Default)]
pub struct Bindings {
    pub(crate) prototypes: HashMap<InterfaceId, Handle>,
    pub(crate) interface_objects: HashMap<InterfaceId, Handle>,
    pub(crate) same_object: HashMap<(ObjectKey, &'static str), Handle>,
    pub(crate) dom_exception_prototype: Option<Handle>,
    pub(crate) global: Option<Handle>,
}

impl Bindings {
    /// Empty: [`crate::generated::bindings::install`] fills it.
    #[must_use]
    pub fn new() -> Bindings {
        Bindings::default()
    }
}

/// The interface prototype object of `interface` (WebIDL §3.7.3†).
///
/// # Errors
/// `Error::WrongType` if [`crate::generated::bindings::install`] has not
/// made it.
pub fn prototype<'s, P: Platform>(
    scope: &mut Scope<'s>,
    interface: InterfaceId,
) -> Result<Local<'s>> {
    let handle = scope
        .host_mut::<P>()?
        .bindings()
        .prototypes
        .get(&interface)
        .cloned()
        .ok_or(clazel_js::Error::WrongType("an installed interface"))?;
    scope.local(&handle)
}

/// The global object (the `Window`'s wrapper).
///
/// # Errors
/// `Error::WrongType` before [`crate::generated::bindings::install`].
pub fn global<'s, P: Platform>(scope: &mut Scope<'s>) -> Result<Local<'s>> {
    let handle = scope
        .host_mut::<P>()?
        .bindings()
        .global
        .clone()
        .ok_or(clazel_js::Error::WrongType("installed bindings"))?;
    scope.local(&handle)
}

/// The JavaScript value of a platform object: WebIDL §3.2.? "Converting an
/// IDL interface type value to an ECMAScript value": "the result is the
/// ECMAScript object associated with" it. The first time, the wrapper is
/// made with the prototype of the object's interface and its
/// `[LegacyUnforgeable]` members (§3.7.? "define the unforgeable regular
/// operations and attributes"), and kept.
///
/// # Errors
/// A `TypeError` if the key names no platform object.
pub fn wrap<'s, P: AllInterfaces>(scope: &mut Scope<'s>, key: ObjectKey) -> Result<Local<'s>> {
    if key == scope.host_mut::<P>()?.window_key() {
        return global::<P>(scope);
    }
    if let Some(handle) = scope.host_mut::<P>()?.wrapper(key) {
        return scope.local(&handle);
    }
    let Some(interface) = scope.host_mut::<P>()?.interface_of(key) else {
        return Err(scope.throw_error(ErrorKind::TypeError, "not a live platform object"));
    };
    let proto = prototype::<P>(scope, interface)?;
    wrap_with_prototype::<P>(scope, key, interface, proto)
}

/// [`wrap`] with a given prototype: a constructor's result, whose prototype
/// comes from NewTarget (WebIDL §3.7.1† "interface object" [[Construct]]
/// via "internally create a new object implementing the interface", step
/// "Let prototype be ? Get(newTarget, "prototype")").
///
/// # Errors
/// What defining the unforgeable members throws.
pub fn wrap_with_prototype<'s, P: AllInterfaces>(
    scope: &mut Scope<'s>,
    key: ObjectKey,
    interface: InterfaceId,
    proto: Local<'_>,
) -> Result<Local<'s>> {
    let object = scope.new_host_object(Some(proto), Wrapper { key, interface })?;
    crate::generated::bindings::define_unforgeables::<P>(scope, interface, object)?;
    let handle = scope.persist(object);
    scope.host_mut::<P>()?.set_wrapper(key, handle);
    Ok(object)
}

/// Whether `value` is a platform object that implements `interface`
/// (WebIDL §3.2.? "implements"): its interface is `interface` or inherits
/// from it. Returns the key.
pub fn implements<P: Platform>(
    scope: &mut Scope<'_>,
    value: Local<'_>,
    interface: InterfaceId,
) -> Result<Option<ObjectKey>> {
    if let Ok(w) = scope.host_data::<Wrapper>(value) {
        let w = *w;
        return Ok(w.interface.inherits(interface).then_some(w.key));
    }
    let global = global::<P>(scope)?;
    if scope.strict_equals(value, global) && InterfaceId::Window.inherits(interface) {
        return Ok(Some(scope.host_mut::<P>()?.window_key()));
    }
    Ok(None)
}

/// The `this` of a regular attribute's getter or setter, or of a regular
/// operation, checked: WebIDL §3.7.6† (operations) step 2.1 and §3.7.5†
/// (attributes) steps 1.1: "If thisValue is null or undefined, set O to
/// realm's global object." then "If O implements the interface ... else
/// throw a TypeError."
///
/// # Errors
/// The `TypeError` ("Illegal invocation").
pub fn this_object<P: Platform>(
    scope: &mut Scope<'_>,
    args: &Args<'_>,
    interface: InterfaceId,
) -> Result<ObjectKey> {
    let this = args.this();
    let this = match scope.kind(this) {
        clazel_js::ValueKind::Undefined | clazel_js::ValueKind::Null => global::<P>(scope)?,
        _ => this,
    };
    match implements::<P>(scope, this, interface)? {
        Some(key) => Ok(key),
        None => Err(scope.throw_error(ErrorKind::TypeError, "Illegal invocation")),
    }
}

/// The `[SameObject]` cache (WebIDL §3.3.? `[SameObject]`: "the same value
/// is always returned"): the value an attribute of an object first returned.
pub fn same_object<'s, P: Platform>(
    scope: &mut Scope<'s>,
    key: ObjectKey,
    attribute: &'static str,
) -> Result<Option<Local<'s>>> {
    let cached = scope
        .host_mut::<P>()?
        .bindings()
        .same_object
        .get(&(key, attribute))
        .cloned();
    match cached {
        Some(h) => Ok(Some(scope.local(&h)?)),
        None => Ok(None),
    }
}

/// Keeps `value` as what `attribute` of `key` returns from now on.
pub fn keep_same_object<P: Platform>(
    scope: &mut Scope<'_>,
    key: ObjectKey,
    attribute: &'static str,
    value: Local<'_>,
) -> Result<()> {
    let handle = scope.persist(value);
    scope
        .host_mut::<P>()?
        .bindings()
        .same_object
        .insert((key, attribute), handle);
    Ok(())
}

/// Reads `name` of the global object: how the bindings reach the built-ins
/// they need (`Error.prototype`, `Function.prototype`).
pub(crate) fn global_property<'s, P: Platform>(
    scope: &mut Scope<'s>,
    path: &[&str],
) -> Result<Local<'s>> {
    let mut v = global::<P>(scope)?;
    for name in path {
        v = scope.get(v, Key::Str(name))?;
    }
    Ok(v)
}
