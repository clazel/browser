//! Errors and exceptions.

use core::fmt;

use crate::value::Handle;

/// What every fallible call in this crate returns.
pub type Result<T> = core::result::Result<T, Error>;

/// The kinds of error object the engine can create (ECMA-262's native error
/// types).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// `Error`.
    Error,
    /// `EvalError`.
    EvalError,
    /// `RangeError`.
    RangeError,
    /// `ReferenceError`.
    ReferenceError,
    /// `SyntaxError`.
    SyntaxError,
    /// `TypeError`.
    TypeError,
    /// `URIError`.
    UriError,
}

/// A value JavaScript threw, held by a rooted [`Handle`].
///
/// An `Exception` is what `catch` would see. It stays alive for as long as it
/// is held, whichever scope it was thrown in, so an embedder can report it
/// after the call that threw it has returned.
///
/// ```no_run
/// use clazel_js::{Error, Realm, Scope, Source};
///
/// fn report(scope: &mut Scope<'_>, realm: &Realm) -> clazel_js::Result<()> {
///     match scope.eval_script(realm, Source::new("page.js", "null.x")) {
///         Err(Error::Thrown(exception)) => {
///             let report = scope.report(&exception)?;
///             println!("{}: {}", report.name, report.message);
///             Ok(())
///         }
///         other => other.map(|_| ()),
///     }
/// }
/// ```
#[derive(Clone, Debug)]
pub struct Exception {
    value: Handle,
}

impl Exception {
    /// Wraps a value to be reported as thrown, for example to refuse a module
    /// load in [`Scope::finish_loading_imported_module`](crate::Scope::finish_loading_imported_module).
    /// The engine builds the ones it returns in [`Error::Thrown`].
    pub fn from_handle(value: Handle) -> Exception {
        Exception { value }
    }

    /// The thrown value, as a rooted handle. Turn it back into a
    /// [`Local`](crate::Local) with [`Scope::local`](crate::Scope::local).
    pub fn value(&self) -> &Handle {
        &self.value
    }
}

/// A thrown error described in plain Rust types, for logging and for the
/// browser's "report the exception" step (which is HTML's, not the engine's;
/// the engine only supplies these fields).
///
/// Built by [`Scope::report`](crate::Scope::report). It never runs user code:
/// a getter that throws while the report is built leaves that field empty.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ErrorReport {
    /// `name` of the thrown object, or `"Error"` if it has none. For a thrown
    /// non-object, the type of the value, such as `"string"`.
    pub name: String,
    /// `message` of the thrown object, or the string conversion of a thrown
    /// primitive.
    pub message: String,
    /// The call stack when the error object was created, innermost first.
    /// Empty if the thrown value is not an error object.
    pub stack: Vec<StackFrame>,
}

/// One frame of a call stack.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct StackFrame {
    /// The function's name, or `None` for top-level code and anonymous
    /// functions.
    pub function: Option<String>,
    /// The `name` of the [`Source`](crate::Source) the frame's code came from.
    pub source: String,
    /// 1-based line, counting from the source's `start_line`.
    pub line: u32,
    /// 1-based column, in UTF-16 code units.
    pub column: u32,
}

/// Why a call failed.
///
/// Exactly one variant, [`Thrown`](Error::Thrown), is a JavaScript value.
/// Every other variant is the engine's or the embedder's, and JavaScript
/// cannot observe or catch it. A native function passes both kinds back with
/// `?`.
///
/// ```no_run
/// use clazel_js::{Error, Realm, Scope, Source};
///
/// fn run(scope: &mut Scope<'_>, realm: &Realm) {
///     match scope.eval_script(realm, Source::new("a.js", "while (true) {}")) {
///         Ok(_) => {}
///         Err(Error::Thrown(_)) => { /* the script threw; `catch` could have caught it */ }
///         Err(Error::Terminated) => { /* a Terminator stopped it; nothing in JS ran after */ }
///         Err(other) => eprintln!("engine error: {other}"),
///     }
/// }
/// ```
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum Error {
    /// JavaScript threw this value. Includes the `SyntaxError` for source
    /// that does not parse, and the `RangeError`s the limits report
    /// (heap, value stack, nested native calls, nesting depth, RegExp
    /// backtracking). All of them can be caught by JavaScript.
    Thrown(Exception),
    /// A [`Terminator`](crate::Terminator) ended the evaluation. JavaScript
    /// cannot catch it, and no `finally` block runs while it propagates.
    Terminated,
    /// The heap limit was reached and the engine could not even allocate the
    /// `RangeError` to report it. This is the rare case; the ordinary report
    /// of the heap limit is [`Thrown`](Error::Thrown).
    OutOfMemory,
    /// The handle names something that no longer exists, so using it would
    /// have aliased a different object. The generation check caught it.
    StaleHandle,
    /// The handle, realm, script or module belongs to another
    /// [`Runtime`](crate::Runtime).
    WrongRuntime,
    /// The value was not of the type the call needs. The text names what was
    /// wanted, for example `"host object of this type"`.
    WrongType(&'static str),
    /// The data being asked for is already borrowed by a call further up the
    /// stack (a host object's data while one of its own hooks runs).
    Busy,
    /// The contract is written but the body is not. The text names the call.
    /// This variant exists only until item 7.8 builds the implementation.
    NotImplemented(&'static str),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Thrown(_) => f.write_str("JavaScript threw a value"),
            Error::Terminated => f.write_str("terminated"),
            Error::OutOfMemory => f.write_str("out of memory"),
            Error::StaleHandle => f.write_str("stale handle"),
            Error::WrongRuntime => f.write_str("handle from another runtime"),
            Error::WrongType(what) => write!(f, "wrong type: wanted {what}"),
            Error::Busy => f.write_str("already borrowed further up the stack"),
            Error::NotImplemented(what) => write!(f, "not implemented: {what}"),
        }
    }
}

impl std::error::Error for Error {}

/// The body of every call whose implementation is still to come: names the
/// call, uses its arguments so the contract's parameter names stay as written,
/// and returns [`Error::NotImplemented`].
macro_rules! not_implemented {
    ($what:expr $(, $arg:expr)* $(,)?) => {{
        let _ = ($(&$arg,)*);
        ::core::result::Result::Err($crate::Error::NotImplemented($what))
    }};
}
pub(crate) use not_implemented;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_names_the_unimplemented_call() {
        assert_eq!(
            Error::NotImplemented("Runtime::new").to_string(),
            "not implemented: Runtime::new"
        );
    }
}
