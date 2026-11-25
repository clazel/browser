//! `DOMException` (WebIDL §2.8.1† "DOMException names", §4.3†
//! "DOMException", and §3.14.1† "DOMException custom bindings").
//!
//! <https://webidl.spec.whatwg.org/#idl-DOMException>
//!
//! `webidl.idl` is not vendored (`tests/data/webref-idl/SOURCE.md`), so this
//! interface is written by hand from the standard's IDL:
//!
//! ```text
//! [Exposed=*, Serializable]
//! interface DOMException {
//!   constructor(optional DOMString message = "", optional DOMString name = "Error");
//!   readonly attribute DOMString name;
//!   readonly attribute DOMString message;
//!   readonly attribute unsigned short code;
//!   const unsigned short INDEX_SIZE_ERR = 1; ... DATA_CLONE_ERR = 25;
//! };
//! ```
//!
//! Modelling choices:
//! - The object is a `clazel-js` host object carrying [`DomExceptionData`];
//!   "implements DOMException" is having that data.
//! - §3.14.1†: "the [[Prototype]] internal slot of DOMException.prototype is
//!   %Error.prototype%". It is read from the global `Error` when the
//!   bindings are installed.
//! - `[Serializable]` is not implemented (there is no structured clone yet).
//! - `QuotaExceededError` became its own interface in the standard; it is
//!   not here, and the name "QuotaExceededError" is an ordinary name with
//!   its legacy code 22.

use clazel_js::{Args, ErrorKind, HostObject, Local, Result, Scope};

use crate::convert;
use crate::install;
use crate::platform::{Platform, global_property};

/// The names of WebIDL §2.8.1†'s table, with their legacy codes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DomErrorName {
    /// "IndexSizeError", code 1 (deprecated in favour of RangeError).
    IndexSizeError,
    /// "HierarchyRequestError", code 3.
    HierarchyRequestError,
    /// "WrongDocumentError", code 4.
    WrongDocumentError,
    /// "InvalidCharacterError", code 5.
    InvalidCharacterError,
    /// "NoModificationAllowedError", code 7.
    NoModificationAllowedError,
    /// "NotFoundError", code 8.
    NotFoundError,
    /// "NotSupportedError", code 9.
    NotSupportedError,
    /// "InUseAttributeError", code 10.
    InUseAttributeError,
    /// "InvalidStateError", code 11.
    InvalidStateError,
    /// "SyntaxError", code 12.
    SyntaxError,
    /// "InvalidModificationError", code 13.
    InvalidModificationError,
    /// "NamespaceError", code 14.
    NamespaceError,
    /// "InvalidAccessError", code 15 (deprecated).
    InvalidAccessError,
    /// "TypeMismatchError", code 17 (deprecated).
    TypeMismatchError,
    /// "SecurityError", code 18.
    SecurityError,
    /// "NetworkError", code 19.
    NetworkError,
    /// "AbortError", code 20.
    AbortError,
    /// "URLMismatchError", code 21 (deprecated).
    UrlMismatchError,
    /// "TimeoutError", code 23.
    TimeoutError,
    /// "InvalidNodeTypeError", code 24.
    InvalidNodeTypeError,
    /// "DataCloneError", code 25.
    DataCloneError,
    /// "EncodingError", code 0.
    EncodingError,
    /// "NotReadableError", code 0.
    NotReadableError,
    /// "UnknownError", code 0.
    UnknownError,
    /// "ConstraintError", code 0.
    ConstraintError,
    /// "DataError", code 0.
    DataError,
    /// "TransactionInactiveError", code 0.
    TransactionInactiveError,
    /// "ReadOnlyError", code 0.
    ReadOnlyError,
    /// "VersionError", code 0.
    VersionError,
    /// "OperationError", code 0.
    OperationError,
    /// "NotAllowedError", code 0.
    NotAllowedError,
    /// "OptOutError", code 0.
    OptOutError,
}

/// Every name of the table, with its text and legacy code.
const NAMES: &[(DomErrorName, &str, u16)] = &[
    (DomErrorName::IndexSizeError, "IndexSizeError", 1),
    (
        DomErrorName::HierarchyRequestError,
        "HierarchyRequestError",
        3,
    ),
    (DomErrorName::WrongDocumentError, "WrongDocumentError", 4),
    (
        DomErrorName::InvalidCharacterError,
        "InvalidCharacterError",
        5,
    ),
    (
        DomErrorName::NoModificationAllowedError,
        "NoModificationAllowedError",
        7,
    ),
    (DomErrorName::NotFoundError, "NotFoundError", 8),
    (DomErrorName::NotSupportedError, "NotSupportedError", 9),
    (DomErrorName::InUseAttributeError, "InUseAttributeError", 10),
    (DomErrorName::InvalidStateError, "InvalidStateError", 11),
    (DomErrorName::SyntaxError, "SyntaxError", 12),
    (
        DomErrorName::InvalidModificationError,
        "InvalidModificationError",
        13,
    ),
    (DomErrorName::NamespaceError, "NamespaceError", 14),
    (DomErrorName::InvalidAccessError, "InvalidAccessError", 15),
    (DomErrorName::TypeMismatchError, "TypeMismatchError", 17),
    (DomErrorName::SecurityError, "SecurityError", 18),
    (DomErrorName::NetworkError, "NetworkError", 19),
    (DomErrorName::AbortError, "AbortError", 20),
    (DomErrorName::UrlMismatchError, "URLMismatchError", 21),
    (DomErrorName::TimeoutError, "TimeoutError", 23),
    (
        DomErrorName::InvalidNodeTypeError,
        "InvalidNodeTypeError",
        24,
    ),
    (DomErrorName::DataCloneError, "DataCloneError", 25),
    (DomErrorName::EncodingError, "EncodingError", 0),
    (DomErrorName::NotReadableError, "NotReadableError", 0),
    (DomErrorName::UnknownError, "UnknownError", 0),
    (DomErrorName::ConstraintError, "ConstraintError", 0),
    (DomErrorName::DataError, "DataError", 0),
    (
        DomErrorName::TransactionInactiveError,
        "TransactionInactiveError",
        0,
    ),
    (DomErrorName::ReadOnlyError, "ReadOnlyError", 0),
    (DomErrorName::VersionError, "VersionError", 0),
    (DomErrorName::OperationError, "OperationError", 0),
    (DomErrorName::NotAllowedError, "NotAllowedError", 0),
    (DomErrorName::OptOutError, "OptOutError", 0),
];

/// The legacy code constants of the interface (§4.3†), name and value. The
/// names with no `DOMException` name of their own (2, 6, 16) are kept, as
/// the standard keeps them.
const CONSTANTS: &[(&str, u16)] = &[
    ("INDEX_SIZE_ERR", 1),
    ("DOMSTRING_SIZE_ERR", 2),
    ("HIERARCHY_REQUEST_ERR", 3),
    ("WRONG_DOCUMENT_ERR", 4),
    ("INVALID_CHARACTER_ERR", 5),
    ("NO_DATA_ALLOWED_ERR", 6),
    ("NO_MODIFICATION_ALLOWED_ERR", 7),
    ("NOT_FOUND_ERR", 8),
    ("NOT_SUPPORTED_ERR", 9),
    ("INUSE_ATTRIBUTE_ERR", 10),
    ("INVALID_STATE_ERR", 11),
    ("SYNTAX_ERR", 12),
    ("INVALID_MODIFICATION_ERR", 13),
    ("NAMESPACE_ERR", 14),
    ("INVALID_ACCESS_ERR", 15),
    ("VALIDATION_ERR", 16),
    ("TYPE_MISMATCH_ERR", 17),
    ("SECURITY_ERR", 18),
    ("NETWORK_ERR", 19),
    ("ABORT_ERR", 20),
    ("URL_MISMATCH_ERR", 21),
    ("QUOTA_EXCEEDED_ERR", 22),
    ("TIMEOUT_ERR", 23),
    ("INVALID_NODE_TYPE_ERR", 24),
    ("DATA_CLONE_ERR", 25),
];

impl DomErrorName {
    /// The name as the table spells it.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        NAMES
            .iter()
            .find(|(n, _, _)| *n == self)
            .map_or("Error", |(_, s, _)| s)
    }
}

/// The legacy code of a name: §4.3† "The code getter steps are to return
/// the legacy code indicated in the DOMException names table for this's
/// name, or 0 if no such entry exists in the table." Names are compared as
/// UTF-16.
#[must_use]
pub fn legacy_code(name: &[u16]) -> u16 {
    NAMES
        .iter()
        .find(|(_, s, _)| s.encode_utf16().eq(name.iter().copied()))
        .map_or(0, |(_, _, c)| *c)
}

/// A `DOMException`'s name and message (§4.3†: "a name" and "a message",
/// both strings).
#[derive(Clone, Debug)]
pub struct DomExceptionData {
    /// The name.
    pub name: Vec<u16>,
    /// The message.
    pub message: Vec<u16>,
}

impl HostObject for DomExceptionData {}

/// A new `DOMException` object with this name and message (§4.3† "create a
/// DOMException": an object whose prototype is DOMException.prototype).
///
/// # Errors
/// `Error::WrongType` before the bindings are installed.
pub fn create<'s, P: Platform>(
    scope: &mut Scope<'s>,
    name: &[u16],
    message: &[u16],
) -> Result<Local<'s>> {
    let proto = scope
        .host_mut::<P>()?
        .bindings()
        .dom_exception_prototype
        .clone()
        .ok_or(clazel_js::Error::WrongType("installed bindings"))?;
    let proto = scope.local(&proto)?;
    scope.new_host_object(
        Some(proto),
        DomExceptionData {
            name: name.to_vec(),
            message: message.to_vec(),
        },
    )
}

/// "Throw" a `DOMException` (WebIDL §2.8.1†: "throw an X DOMException
/// with message"): the error to return from a native function.
#[must_use]
pub fn throw<P: Platform>(
    scope: &mut Scope<'_>,
    name: DomErrorName,
    message: &str,
) -> clazel_js::Error {
    let n: Vec<u16> = name.as_str().encode_utf16().collect();
    let m: Vec<u16> = message.encode_utf16().collect();
    match create::<P>(scope, &n, &m) {
        Ok(e) => scope.throw(e),
        Err(e) => e,
    }
}

fn data<'a>(scope: &'a mut Scope<'_>, args: &Args<'_>) -> Result<&'a DomExceptionData> {
    let this = args.this();
    if scope.host_data::<DomExceptionData>(this).is_err() {
        return Err(scope.throw_error(ErrorKind::TypeError, "Illegal invocation"));
    }
    scope.host_data::<DomExceptionData>(this)
}

/// Installs `DOMException` on the global object.
///
/// # Errors
/// What `clazel-js` returns.
pub fn install<P: Platform>(scope: &mut Scope<'_>, global: Local<'_>) -> Result<()> {
    // §4.3† constructor steps: "Set this's name to name. Set this's message
    // to message." The arguments are `optional DOMString` with defaults.
    let ctor = install::interface_object(scope, "DOMException", 0, None, |scope, args| {
        let Some(new_target) = args.new_target() else {
            return Err(scope.throw_error(
                ErrorKind::TypeError,
                "Constructor DOMException requires 'new'",
            ));
        };
        let message = match scope.kind(args.get(0)) {
            clazel_js::ValueKind::Undefined => Vec::new(),
            _ => convert::dom_string(scope, args.get(0), false)?,
        };
        let name = match scope.kind(args.get(1)) {
            clazel_js::ValueKind::Undefined => "Error".encode_utf16().collect(),
            _ => convert::dom_string(scope, args.get(1), false)?,
        };
        let fallback = scope
            .host_mut::<P>()?
            .bindings()
            .dom_exception_prototype
            .clone()
            .ok_or(clazel_js::Error::WrongType("installed bindings"))?;
        let fallback = scope.local(&fallback)?;
        let proto = scope.get_prototype_from_constructor(new_target, fallback)?;
        scope.new_host_object(Some(proto), DomExceptionData { name, message })
    })?;
    let proto = scope.new_object()?;
    let error_proto = global_property::<P>(scope, &["Error", "prototype"])?;
    scope.set_prototype_of(proto, error_proto)?;
    install::link(scope, ctor, proto)?;
    install::attribute(
        scope,
        proto,
        "name",
        |scope, args| {
            let n = data(scope, args)?.name.clone();
            Ok(scope.string_utf16(&n))
        },
        None,
        false,
    )?;
    install::attribute(
        scope,
        proto,
        "message",
        |scope, args| {
            let m = data(scope, args)?.message.clone();
            Ok(scope.string_utf16(&m))
        },
        None,
        false,
    )?;
    install::attribute(
        scope,
        proto,
        "code",
        |scope, args| {
            let c = legacy_code(&data(scope, args)?.name);
            Ok(scope.number(f64::from(c)))
        },
        None,
        false,
    )?;
    for (name, value) in CONSTANTS {
        let v = scope.number(f64::from(*value));
        install::constant(scope, &[ctor, proto], name, v)?;
    }
    install::expose(scope, global, "DOMException", ctor)?;
    let handle = scope.persist(proto);
    scope.host_mut::<P>()?.bindings().dom_exception_prototype = Some(handle);
    Ok(())
}
