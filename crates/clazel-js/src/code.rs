//! Realms, source text, scripts and modules.

use core::any::Any;
use core::marker::PhantomData;

use crate::native::HostObject;
use crate::value::Handle;

/// A realm: a global object and its own copy of every built-in
/// (ECMA-262's Realm Record).
///
/// - **Why more than one.** `$262.createRealm()` in Test262, and later a
///   frame. A realm's `Array` is not another realm's `Array`, and
///   `instanceof` across them is false, as in a browser.
/// - **Lifetime.** A `Realm` is a root: the realm and everything reachable
///   from its global object live until the last clone is dropped. Like
///   [`Handle`] it is `Send`, `Sync` and `Clone`, and needs a
///   [`Scope`](crate::Scope) to do anything.
/// - **No ambient realm.** Every call that runs code names the realm. Inside a
///   native function, [`Scope::current_realm`](crate::Scope::current_realm)
///   is the realm of the function being called.
///
/// ```no_run
/// use clazel_js::{Runtime, RealmOptions, Source};
///
/// fn two_realms(rt: &mut Runtime) -> clazel_js::Result<()> {
///     let (a, b) = rt.scope(|scope| {
///         Ok((scope.create_realm(RealmOptions::default())?,
///             scope.create_realm(RealmOptions::default())?))
///     })?;
///     rt.scope(|scope| {
///         let same = scope.eval_script(&a, Source::new("t.js", "[] instanceof Array"))?;
///         assert_eq!(scope.as_boolean(same), Some(true));
///         // A realm's own object is not an instance of the other realm's Array.
///         let global_b = scope.global(&b)?;
///         let _ = global_b;
///         Ok(())
///     })
/// }
/// ```
#[derive(Clone, Debug)]
pub struct Realm {
    root: Handle,
}

impl Realm {
    /// The root that keeps the realm alive.
    pub fn as_handle(&self) -> &Handle {
        &self.root
    }
}

/// How to build a realm. The default is an ordinary global object with the
/// standard built-ins.
///
/// ```no_run
/// use clazel_js::{Exotic, HostObject, RealmOptions};
///
/// /// The browser's `Window`: a host object serving as the global object.
/// struct Window;
/// impl HostObject for Window {}
///
/// let options = RealmOptions {
///     global: Some(Box::new(Window)),
/// };
/// # let _ = options;
/// ```
#[derive(Default)]
pub struct RealmOptions {
    /// Make the global object a host object with this data, whose prototype is
    /// the realm's `Object.prototype`. `None` makes an ordinary object. Its
    /// exotic hooks answer for the global's own properties. The global's `this`
    /// value (HTML's `WindowProxy`) is an open question in the README.
    pub global: Option<Box<dyn HostObject>>,
}

/// Source text to compile, with where it came from.
///
/// - **Text** is a `&str`: a sequence of Unicode code points, as ECMA-262
///   defines source text. The browser decodes bytes to text with
///   `clazel-encoding` before calling.
/// - **Name** is what stack traces and error reports show: a URL for a
///   script from the network, `"inline"` or similar for the rest.
/// - **`start_line`** is the 1-based line number of the text's first line, so
///   an inline script in a page reports page line numbers.
/// - **`host_defined`** is the embedder's data about this code (a base URL,
///   fetch options). It is kept with the compiled [`Script`] or [`Module`] and
///   given back by [`Scope::host_defined`](crate::Scope::host_defined)
///   and to the [`Host`](crate::Host) hooks as part of a [`Referrer`].
///
/// ```no_run
/// use clazel_js::Source;
///
/// struct BaseUrl(String);
///
/// let source = Source::new("https://example.test/app.js", "export default 1;")
///     .with_start_line(1)
///     .with_host_defined(Box::new(BaseUrl("https://example.test/".to_owned())));
/// assert_eq!(source.name(), "https://example.test/app.js");
/// ```
pub struct Source<'a> {
    name: &'a str,
    text: &'a str,
    start_line: u32,
    host_defined: Option<Box<dyn Any + Send>>,
}

impl<'a> Source<'a> {
    /// Source text with a name, starting at line 1, with no host data.
    pub fn new(name: &'a str, text: &'a str) -> Source<'a> {
        Source {
            name,
            text,
            start_line: 1,
            host_defined: None,
        }
    }

    /// Sets the line number of the first line.
    #[must_use]
    pub fn with_start_line(mut self, start_line: u32) -> Source<'a> {
        self.start_line = start_line;
        self
    }

    /// Attaches the embedder's data.
    #[must_use]
    pub fn with_host_defined(mut self, data: Box<dyn Any + Send>) -> Source<'a> {
        self.host_defined = Some(data);
        self
    }

    /// The name.
    pub fn name(&self) -> &str {
        self.name
    }

    /// The text.
    pub fn text(&self) -> &str {
        self.text
    }

    /// The line number of the first line.
    pub fn start_line(&self) -> u32 {
        self.start_line
    }

    /// The embedder's data, if any.
    pub fn host_defined(&self) -> Option<&(dyn Any + Send)> {
        self.host_defined.as_deref()
    }
}

/// A parsed classic script (ECMA-262's Script Record), not yet run.
///
/// Parsing and running are separate so a host can follow HTML's "prepare the
/// script element", which fetches and compiles, then runs when the parser
/// or the event loop says. [`Scope::eval_script`](crate::Scope::eval_script) does both at
/// once. A `Script` is a root, `Clone`, `Send` and `Sync`, and may be run
/// more than once; top-level `var`s and functions are created in the realm
/// each time it runs, as for a script run twice.
///
/// ```no_run
/// use clazel_js::{Realm, Runtime, Script, Source};
///
/// fn compile_then_run(rt: &mut Runtime, realm: &Realm) -> clazel_js::Result<()> {
///     let script: Script = rt.scope(|scope| {
///         scope.compile_script(realm, Source::new("later.js", "globalThis.n = 1"))
///     })?;
///     // ... the parser unblocks ...
///     rt.scope(|scope| {
///         scope.run_script(&script)?;
///         Ok(())
///     })
/// }
/// ```
#[derive(Clone, Debug)]
pub struct Script {
    root: Handle,
}

impl Script {
    /// The root that keeps the script alive.
    pub fn as_handle(&self) -> &Handle {
        &self.root
    }
}

/// A module (ECMA-262's Source Text Module Record or a synthetic one).
///
/// The life of a module follows ECMA-262 §16.2.1.5, which the methods of
/// [`Scope`](crate::Scope) name: parse, load requested modules (the host
/// supplies each import through [`Host::load_imported_module`](crate::Host::load_imported_module)),
/// link, evaluate. `Module` is a root, `Clone`, `Send` and `Sync`.
///
/// ```no_run
/// use clazel_js::{ModuleStatus, Realm, Runtime, Source};
///
/// /// Loads and runs a module whose imports the host can already resolve.
/// fn run_module(rt: &mut Runtime, realm: &Realm, text: &str) -> clazel_js::Result<()> {
///     let module = rt.scope(|scope| scope.parse_module(realm, Source::new("m.js", text)))?;
///     rt.scope(|scope| {
///         let loaded = scope.load_requested_modules(&module)?;
///         let _ = loaded; // a promise: settled when every import has been finished
///         Ok(())
///     })?;
///     rt.run_jobs()?;
///     rt.scope(|scope| {
///         if scope.module_status(&module)? == ModuleStatus::Unlinked {
///             scope.link(&module)?;
///         }
///         let _done = scope.evaluate_module(&module)?; // a promise, for top-level await
///         Ok(())
///     })
/// }
/// ```
#[derive(Clone, Debug)]
pub struct Module {
    root: Handle,
}

impl Module {
    /// The root that keeps the module alive.
    pub fn as_handle(&self) -> &Handle {
        &self.root
    }
}

/// A module's state (ECMA-262's Cyclic Module Record `[[Status]]`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModuleStatus {
    /// Just created by `parse_module`.
    New,
    /// Its requested modules are loaded; not yet linked.
    Unlinked,
    /// `link` is running.
    Linking,
    /// Linked, not yet evaluated.
    Linked,
    /// Evaluation is running.
    Evaluating,
    /// Evaluation is waiting on top-level `await`.
    EvaluatingAsync,
    /// Evaluation finished, with a value or an error (kept by the module).
    Evaluated,
}

/// One import attribute: `with { type: "json" }` is `("type", "json")`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportAttribute {
    /// The attribute's key.
    pub key: String,
    /// Its value.
    pub value: String,
}

/// What a module asks to import: ECMA-262's ModuleRequest Record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleRequest {
    /// The module specifier, exactly as written in the source.
    pub specifier: String,
    /// The import attributes, in source order.
    pub attributes: Vec<ImportAttribute>,
}

/// The code that asked for an import: the referrer of
/// [`Host::load_imported_module`](crate::Host::load_imported_module). Its
/// [host data](crate::Scope::host_defined) tells the host where to resolve
/// the specifier against.
#[derive(Clone, Copy, Debug)]
pub enum Referrer<'a> {
    /// A classic script (a dynamic `import()` in one).
    Script(&'a Script),
    /// A module (a static `import` or a dynamic `import()` in one).
    Module(&'a Module),
    /// Neither: `import()` in `eval` or `Function` code outside any script
    /// or module, which has only the realm.
    Realm(&'a Realm),
}

/// The engine's token for one pending import, passed to
/// [`Host::load_imported_module`](crate::Host::load_imported_module) and given
/// back to [`Scope::finish_loading_imported_module`](crate::Scope::finish_loading_imported_module).
///
/// A host may finish it at once or on a later turn of its event loop, from
/// the same thread as the runtime. It must be finished exactly once; the type
/// is consumed by finishing it. Dropping it without finishing leaves the
/// module graph's load promise pending for ever, which is a bug in the host
/// but not unsafe.
#[derive(Debug)]
pub struct LoadPayload {
    _pending: PhantomData<()>,
}
