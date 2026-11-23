//! Making the objects of an interface (WebIDL §3.7†): interface objects,
//! interface prototype objects, and the properties of attributes,
//! operations and constants. The generated code
//! (`crate::generated::bindings`) calls these for each member of the IDL.
//!
//! <https://webidl.spec.whatwg.org/#es-interfaces>

use clazel_js::{Args, Callable, Key, Local, PropertyDescriptor, Result, Scope};

/// A native function body, as `clazel_js::Scope::shared_function` takes it.
pub trait Body:
    for<'a> Fn(&mut Scope<'a>, &Args<'a>) -> Result<Local<'a>> + Send + Sync + 'static
{
}

impl<F> Body for F where
    F: for<'a> Fn(&mut Scope<'a>, &Args<'a>) -> Result<Local<'a>> + Send + Sync + 'static
{
}

/// A function object for an operation, getter or setter: a re-entrant
/// native (event dispatch calls back into script from inside one).
///
/// # Errors
/// What `clazel-js` returns.
pub fn function<'s>(
    scope: &mut Scope<'s>,
    name: &str,
    length: u32,
    body: impl Body,
) -> Result<Local<'s>> {
    scope.shared_function(name, length, Callable::Function, body)
}

/// An interface object (WebIDL §3.7.1†): a constructor function named for
/// the interface whose `length` is its constructor's (0 without one), with
/// [[Prototype]] the parent's interface object if there is a parent
/// ("If interface inherits from another interface, set F.[[Prototype]] to
/// the interface object of that other interface"; else %Function.prototype%,
/// which a new function already has). `body` is its [[Call]] and
/// [[Construct]]: it throws when the interface has no constructor.
///
/// # Errors
/// What `clazel-js` returns.
pub fn interface_object<'s>(
    scope: &mut Scope<'s>,
    name: &str,
    length: u32,
    parent: Option<Local<'_>>,
    body: impl Body,
) -> Result<Local<'s>> {
    let f = scope.shared_function(name, length, Callable::Constructor, body)?;
    if let Some(p) = parent {
        scope.set_prototype_of(f, p)?;
    }
    Ok(f)
}

/// Ties an interface object to its interface prototype object: the
/// interface object's `prototype` ({ writable: false, enumerable: false,
/// configurable: false }, §3.7.1† "interface object" step "Perform !
/// DefinePropertyOrThrow(F, "prototype", ...)") and the prototype's
/// `constructor` ({ writable: true, enumerable: false, configurable: true },
/// §3.7.3† "If the [LegacyNoInterfaceObject] extended attribute was not
/// specified ... constructor").
///
/// # Errors
/// What `clazel-js` returns.
pub fn link(
    scope: &mut Scope<'_>,
    interface_object: Local<'_>,
    prototype: Local<'_>,
) -> Result<()> {
    scope.define_property(
        interface_object,
        Key::Str("prototype"),
        PropertyDescriptor {
            value: Some(prototype),
            writable: Some(false),
            enumerable: Some(false),
            configurable: Some(false),
            ..PropertyDescriptor::default()
        },
    )?;
    scope.define_property(
        prototype,
        Key::Str("constructor"),
        PropertyDescriptor {
            value: Some(interface_object),
            writable: Some(true),
            enumerable: Some(false),
            configurable: Some(true),
            ..PropertyDescriptor::default()
        },
    )
}

/// A constant (WebIDL §3.7.4†): { [[Writable]]: false, [[Enumerable]]: true,
/// [[Configurable]]: false }, on both the interface object and the
/// interface prototype object.
///
/// # Errors
/// What `clazel-js` returns.
pub fn constant(
    scope: &mut Scope<'_>,
    targets: &[Local<'_>],
    name: &str,
    value: Local<'_>,
) -> Result<()> {
    for t in targets {
        scope.define_property(
            *t,
            Key::Str(name),
            PropertyDescriptor {
                value: Some(value),
                writable: Some(false),
                enumerable: Some(true),
                configurable: Some(false),
                ..PropertyDescriptor::default()
            },
        )?;
    }
    Ok(())
}

/// A regular or static attribute (WebIDL §3.7.5†): an accessor property
/// { [[Get]]: getter, [[Set]]: setter or undefined, [[Enumerable]]: true,
/// [[Configurable]]: not unforgeable }. The getter is named "get <name>" and
/// the setter "set <name>" (§3.7.5.1† step "Perform SetFunctionName(F, id,
/// "get")", §3.7.5.2†).
///
/// # Errors
/// What `clazel-js` returns.
pub fn attribute(
    scope: &mut Scope<'_>,
    target: Local<'_>,
    name: &str,
    getter: impl Body,
    setter: Option<Box<dyn Body>>,
    unforgeable: bool,
) -> Result<()> {
    let get = function(scope, &format!("get {name}"), 0, getter)?;
    let set = match setter {
        Some(s) => Some(scope.shared_function(
            &format!("set {name}"),
            1,
            Callable::Function,
            move |scope, args| s(scope, args),
        )?),
        None => None,
    };
    let undefined = scope.undefined();
    scope.define_property(
        target,
        Key::Str(name),
        PropertyDescriptor {
            get: Some(get),
            set: Some(set.unwrap_or(undefined)),
            enumerable: Some(true),
            configurable: Some(!unforgeable),
            ..PropertyDescriptor::default()
        },
    )
}

/// A regular or static operation (WebIDL §3.7.6†): { [[Value]]: F,
/// [[Writable]]: B, [[Enumerable]]: true, [[Configurable]]: B } where B is
/// false if the operation is unforgeable and true otherwise.
///
/// # Errors
/// What `clazel-js` returns.
pub fn operation(
    scope: &mut Scope<'_>,
    target: Local<'_>,
    name: &str,
    length: u32,
    body: impl Body,
    unforgeable: bool,
) -> Result<()> {
    let f = function(scope, name, length, body)?;
    scope.define_property(
        target,
        Key::Str(name),
        PropertyDescriptor {
            value: Some(f),
            writable: Some(!unforgeable),
            enumerable: Some(true),
            configurable: Some(!unforgeable),
            ..PropertyDescriptor::default()
        },
    )
}

/// The property an interface object is reachable by on the global object
/// (WebIDL §3.7† "for every interface that is exposed in a given realm ...
/// a corresponding property exists on the realm's global object ...
/// { [[Writable]]: true, [[Enumerable]]: false, [[Configurable]]: true }").
///
/// # Errors
/// What `clazel-js` returns.
pub fn expose(
    scope: &mut Scope<'_>,
    global: Local<'_>,
    name: &str,
    interface_object: Local<'_>,
) -> Result<()> {
    scope.define_property(
        global,
        Key::Str(name),
        PropertyDescriptor {
            value: Some(interface_object),
            writable: Some(true),
            enumerable: Some(false),
            configurable: Some(true),
            ..PropertyDescriptor::default()
        },
    )
}

/// `[Replaceable]` (WebIDL §3.3.? and §3.7.5.2† "attribute setter" step
/// "If attribute is declared with the [Replaceable] extended attribute,
/// then: Perform ? CreateDataPropertyOrThrow(O, id, V). Return
/// undefined."): the setter of a readonly attribute that shadows it with an
/// own data property of the object.
///
/// # Errors
/// What defining the property throws.
pub fn replace<'s>(scope: &mut Scope<'s>, args: &Args<'s>, name: &str) -> Result<Local<'s>> {
    let this = args.this();
    let value = args.get(0);
    scope.define_property(
        this,
        Key::Str(name),
        PropertyDescriptor {
            value: Some(value),
            writable: Some(true),
            enumerable: Some(true),
            configurable: Some(true),
            ..PropertyDescriptor::default()
        },
    )?;
    Ok(scope.undefined())
}

/// `[PutForwards=name]` (WebIDL §3.7.5.2† "attribute setter" step "If
/// attribute is declared with a [PutForwards] extended attribute, then: Let
/// Q be ? Get(O, id). If Q is not an Object, throw a TypeError. Let
/// forwardId be the identifier argument of the [PutForwards] extended
/// attribute. Perform ? Set(Q, forwardId, V, false). Return undefined.").
///
/// # Errors
/// The `TypeError`, and what the forwarded setter throws.
pub fn put_forwards<'s>(
    scope: &mut Scope<'s>,
    args: &Args<'s>,
    attribute: &str,
    forward: &str,
) -> Result<Local<'s>> {
    let this = args.this();
    let q = scope.get(this, Key::Str(attribute))?;
    if !matches!(
        scope.kind(q),
        clazel_js::ValueKind::Object | clazel_js::ValueKind::Function
    ) {
        return Err(scope.throw_error(
            clazel_js::ErrorKind::TypeError,
            "[PutForwards] target is not an object",
        ));
    }
    scope.set(q, Key::Str(forward), args.get(0))?;
    Ok(scope.undefined())
}
