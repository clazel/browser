//! What a page keeps between and during its scripts: the document and its
//! parser, each script element's state, the document's lists of scripts,
//! the parser's script nesting level and pause flag, the fetches in flight,
//! and what has been reported. It lives in the engine's [`Host`], so that a
//! native function (`document.write`) reaches it through
//! [`Scope::host_mut`] while the script that called it is still running.
//!
//! **Re-entrance.** A borrow of the state is never held across a call into
//! JavaScript: every step takes it, reads or changes a field, and lets it
//! go, so a script run from the middle of a step (the parser running a
//! script from inside `document.write`) finds the state as the step left it.

use std::collections::{BTreeMap, HashMap, VecDeque};

use clazel_dom::exec::Arena;
use clazel_encoding::labels::spec::Encoding;
use clazel_js::{
    Handle, LoadPayload, Local, ModuleRequest, Realm, Referrer, RejectionOperation, Result, Scope,
};
use clazel_treebuilder::exec::incremental::Incremental;

use super::element::ScriptElement;
use super::module::ModuleMapEntry;
use super::time::Clock;

/// A request the page asks its embedder to fetch. The embedder answers with
/// [`super::Page::fetched`], naming `id`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Request {
    /// The page's id for this fetch.
    pub id: u64,
    /// The URL, absolute (resolved against the document base URL).
    pub url: String,
    /// What it is for: a classic script or a module script. Fetch's
    /// destination is "script" for both (HTML §8.1.4.2†); the mode differs.
    pub kind: RequestKind,
    /// Fetch's mode: "cors" for a module script and for a classic script
    /// with a `crossorigin` attribute, "no-cors" otherwise.
    pub cors: bool,
    /// Whether the script element was inserted by the parser (the request's
    /// "parser metadata").
    pub parser_inserted: bool,
}

/// What a [`Request`] fetches.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RequestKind {
    /// "Fetch a classic script".
    ClassicScript,
    /// "Fetch a single module script".
    ModuleScript,
}

/// A response to a [`Request`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Response {
    /// The response's URL, if it differs from the request's (a redirect).
    pub url: Option<String>,
    /// Whether its status is an ok status (200 to 299).
    pub ok: bool,
    /// The `Content-Type` header's value, or empty.
    pub content_type: Vec<u8>,
    /// The body.
    pub body: Vec<u8>,
}

/// A fetch that failed: Fetch's network error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NetworkError;

/// Something the page reported rather than threw at its embedder: HTML's
/// "report an exception" (§8.1.4.?†), and the engine's refusals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Report {
    /// A script threw (or failed to parse) and nothing caught it.
    Exception {
        /// The script's name: its URL, or the document's for inline ones.
        script: String,
        /// The exception's `name` (`TypeError`, ...), empty for a primitive.
        name: String,
        /// Its `message`, or the primitive as a string.
        message: String,
    },
    /// The engine refused (`clazel_js::Error::NotImplemented` and the API's
    /// other non-exception errors): what this engine cannot run yet.
    Engine {
        /// The script's name.
        script: String,
        /// The engine's error, as text.
        error: String,
    },
}

/// Where an event was fired. The page fires events but has no listeners to
/// dispatch them to yet (item 7.12's bindings add `addEventListener` and the
/// `on*` handlers); it records them in order for its embedder and tests.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EventTarget {
    /// The `Window`.
    Window,
    /// The `Document`.
    Document,
    /// An element of the document, by node id.
    Element(usize),
}

/// One event the page fired: "fire an event named `name` at `target`".
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FiredEvent {
    /// The target.
    pub target: EventTarget,
    /// The event's name (`load`, `error`, `DOMContentLoaded`).
    pub name: &'static str,
}

/// HTML §3.1.? "current document readiness".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Readiness {
    /// "loading".
    Loading,
    /// "interactive".
    Interactive,
    /// "complete".
    Complete,
}

/// How far HTML §13.2.7† "the end" has got.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EndPhase {
    /// The parser has not stopped.
    Parsing,
    /// Step 5: the scripts that execute when the document has finished
    /// parsing.
    Deferred,
    /// Steps 7 and 8: waiting for the scripts that execute as soon as
    /// possible and for nothing to delay the load event.
    AwaitAsync,
    /// Steps 9 to 11 done: the document has loaded.
    Loaded,
}

/// The document: being parsed (the parser owns the tree), or done (the
/// tree is the host [`crate::page::Page`]'s `arena`).
pub(crate) enum Doc {
    /// The document's active parser.
    Parsing(Box<Incremental>),
    /// The parser is gone; the tree is the page's.
    Done,
}

impl Doc {
    /// The tree: the parser's while it is parsing, else `done`, the page's.
    pub(crate) fn arena<'a>(&'a self, done: &'a Arena) -> &'a Arena {
        match self {
            Doc::Parsing(p) => &p.parser().arena,
            Doc::Done => done,
        }
    }

    /// The active parser, if any.
    pub(crate) fn parser(&mut self) -> Option<&mut Incremental> {
        match self {
            Doc::Parsing(p) => Some(p),
            Doc::Done => None,
        }
    }
}

/// What a fetch in flight is for.
pub(crate) enum FetchFor {
    /// A classic script for a script element, decoded with this fallback
    /// encoding.
    Classic {
        /// The element.
        element: usize,
        /// The request's URL (the script's name when the response has none).
        url: String,
        /// The document generation the element was prepared in.
        generation: u64,
        /// The encoding from its `charset` attribute or the document's.
        encoding: Encoding,
    },
    /// A module script: the module map entry for this URL waits on it.
    Module {
        /// The module map's key.
        url: String,
    },
}

/// A module load the engine asked for (HostLoadImportedModule) that waits
/// on a module map entry.
pub(crate) struct PendingImport {
    /// The engine's token, given back when the module is ready.
    pub(crate) payload: LoadPayload,
}

/// Everything the page keeps.
pub(crate) struct PageState {
    /// The realm the page's scripts run in (set once it is made).
    pub(crate) realm: Option<Realm>,
    /// The document.
    pub(crate) doc: Doc,
    /// The tree the parser finished with, on its way to the page's `arena`
    /// ([`state`] moves it).
    pub(crate) finished: Option<Arena>,
    /// The document's character encoding ("the document's encoding").
    pub(crate) encoding: Encoding,
    /// The confidence of the encoding was tentative when parsing began.
    pub(crate) tentative: bool,
    /// The parser asked to change the encoding to this one (HTML §13.2.3.4†):
    /// the embedder parses the document again.
    pub(crate) reparse: Option<Encoding>,
    /// Bumped by `document.open`, which empties the document: a script
    /// element's "preparation-time document" is the generation it was
    /// prepared in, and node wrappers of an older one are stale.
    pub(crate) generation: u64,
    /// Each script element's state, by node id.
    pub(crate) scripts: HashMap<usize, ScriptElement>,
    /// "pending parsing-blocking script".
    pub(crate) pending_parsing_blocking: Option<usize>,
    /// A pending parsing-blocking script the parser is waiting for
    /// (§13.2.6.4.8, end tag "script", step 10's spin of the event loop).
    pub(crate) blocked_on: Option<usize>,
    /// "set of scripts that will execute as soon as possible", in the order
    /// they were added.
    pub(crate) asap: Vec<usize>,
    /// "list of scripts that will execute in order as soon as possible".
    pub(crate) in_order: VecDeque<usize>,
    /// "list of scripts that will execute when the document has finished
    /// parsing".
    pub(crate) deferred: VecDeque<usize>,
    /// The parser's "script nesting level".
    pub(crate) script_nesting_level: u32,
    /// The parser's "parser pause flag".
    pub(crate) parser_pause: bool,
    /// The parser is a "script-created parser" (`document.open`).
    pub(crate) script_created: bool,
    /// "active parser was aborted".
    pub(crate) active_parser_aborted: bool,
    /// The document's "ignore-destructive-writes counter".
    pub(crate) ignore_destructive_writes: u32,
    /// "current document readiness".
    pub(crate) readiness: Readiness,
    /// How far "the end" has got.
    pub(crate) end: EndPhase,
    /// Scripts running now, as the host counts them: the depth of the
    /// JavaScript execution context stack is zero exactly when this is.
    pub(crate) running: u32,
    /// `document.currentScript`'s node, if it is an element.
    pub(crate) current_script: Option<usize>,
    /// The `document` object the page's scripts see.
    pub(crate) document_object: Option<Handle>,
    /// One wrapper per node, so `document.currentScript` is the same object
    /// each time it names the same element.
    pub(crate) wrappers: HashMap<usize, Handle>,
    /// Requests the embedder has not taken yet.
    pub(crate) outgoing: Vec<Request>,
    /// Fetches in flight, by id.
    pub(crate) fetches: BTreeMap<u64, FetchFor>,
    /// The next fetch id.
    pub(crate) next_fetch: u64,
    /// The module map (HTML §8.1.?† "module map"), keyed by URL (the module
    /// type is always "javascript" until JSON modules).
    pub(crate) module_map: HashMap<String, ModuleMapEntry>,
    /// Module script elements waiting for their module map entry, by URL.
    pub(crate) module_waiters: HashMap<String, Vec<(usize, u64)>>,
    /// Module map entries that are done and have waiters to answer.
    pub(crate) ready_modules: Vec<String>,
    /// Engine module loads waiting for their module map entry, by URL.
    pub(crate) import_waiters: HashMap<String, Vec<PendingImport>>,
    /// Reported exceptions and engine refusals, in order.
    pub(crate) reports: Vec<Report>,
    /// Fired events, in order.
    pub(crate) events: Vec<FiredEvent>,
    /// The monotonic clock for `performance.now()`.
    pub(crate) clock: Box<dyn Clock>,
    /// The time origin on that clock.
    pub(crate) time_origin_us: u64,
    /// The page's bindings are installed (item 7.12): `document` and the
    /// nodes are the generated interfaces' objects, and timers and the rest
    /// of `bound.rs` exist.
    pub(crate) bound: bool,
    /// Whether a bound page's realm has its bindings yet
    /// (`bound::ensure_bindings`).
    pub(crate) bindings: Bindings,
    /// A document that was parsed before its scripts ran: the script
    /// elements still to be reached, in tree order (`parser::walk`).
    pub(crate) walk: Option<Walk>,
    /// HTML's event loop (§8.1.7†) for this page: the timers, tasks and
    /// microtasks that scripts queue. Taken out of here while the loop runs
    /// a callback of the host (`bound::LoopHost`), which swaps it back in.
    pub(crate) event_loop: crate::event_loop::EventLoop,
    /// The callbacks the loop's ids stand for.
    pub(crate) callbacks: HashMap<u64, super::bound::Callback>,
    /// The next callback id.
    pub(crate) next_callback: u64,
    /// The callback of each timer id.
    pub(crate) timer_callbacks: HashMap<u32, u64>,
    /// `requestAnimationFrame` callbacks, by handle.
    pub(crate) animation_callbacks: BTreeMap<u32, u64>,
    /// The next animation frame handle.
    pub(crate) next_animation: u32,
    /// How many of `events` have been dispatched to listeners.
    pub(crate) dispatched: usize,
    /// Events are being dispatched (`bound::flush_events` does not nest).
    pub(crate) flushing: bool,
}

/// A parsed document's script elements, reached in order as a parser would
/// reach them.
pub(crate) struct Walk {
    /// The script elements' node ids, in tree order.
    pub(crate) order: Vec<usize>,
    /// How many have been reached.
    pub(crate) next: usize,
}

impl PageState {
    /// The state of a new page over `doc`.
    pub(crate) fn new(
        doc: Doc,
        encoding: Encoding,
        tentative: bool,
        clock: Box<dyn Clock>,
        time_origin_us: u64,
    ) -> PageState {
        PageState {
            realm: None,
            doc,
            finished: None,
            encoding,
            tentative,
            reparse: None,
            generation: 0,
            scripts: Default::default(),
            pending_parsing_blocking: None,
            blocked_on: None,
            asap: Vec::new(),
            in_order: Default::default(),
            deferred: Default::default(),
            script_nesting_level: 0,
            parser_pause: false,
            script_created: false,
            active_parser_aborted: false,
            ignore_destructive_writes: 0,
            readiness: Readiness::Loading,
            end: EndPhase::Parsing,
            running: 0,
            current_script: None,
            document_object: None,
            wrappers: Default::default(),
            outgoing: Vec::new(),
            fetches: Default::default(),
            next_fetch: 1,
            module_map: Default::default(),
            module_waiters: Default::default(),
            ready_modules: Vec::new(),
            import_waiters: Default::default(),
            reports: Vec::new(),
            events: Vec::new(),
            clock,
            time_origin_us,
            bound: false,
            bindings: Bindings::Pending,
            walk: None,
            event_loop: crate::event_loop::EventLoop::default(),
            callbacks: HashMap::new(),
            next_callback: 1,
            timer_callbacks: HashMap::new(),
            animation_callbacks: BTreeMap::new(),
            next_animation: 1,
            dispatched: 0,
            flushing: false,
        }
    }
}

/// The engine's host hooks for a page that has script state, which
/// [`crate::page::Page`]'s `Host` implementation calls: HTML's answers to
/// ECMA-262's host hooks.
impl PageState {
    /// HTML §8.1.5.? HostLoadImportedModule: see [`super::module`].
    pub(crate) fn load_imported_module(
        &mut self,
        document: &Arena,
        scope: &mut Scope<'_>,
        referrer: Referrer<'_>,
        request: &ModuleRequest,
        payload: LoadPayload,
    ) -> Result<()> {
        super::module::host_load_imported_module(self, document, scope, referrer, request, payload)
    }

    /// HTML §8.1.5.? HostPromiseRejectionTracker: the "about-to-be-notified
    /// rejected promises list" and `unhandledrejection` are not modelled
    /// (no promises exist yet); a rejection is reported as an exception
    /// would be.
    pub(crate) fn promise_rejection_tracker(
        &mut self,
        _scope: &mut Scope<'_>,
        _promise: Local<'_>,
        operation: RejectionOperation,
    ) {
        if operation == RejectionOperation::Reject {
            self.reports.push(Report::Engine {
                script: String::new(),
                error: "an unhandled promise rejection".to_owned(),
            });
        }
    }
}

/// Where a bound page's realm stands (`bound::ensure_bindings`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Bindings {
    /// Nothing has needed the realm yet: its global object has only the
    /// engine's built-ins.
    Pending,
    /// The interfaces, `console` and the rest are installed.
    Installed,
    /// Installing them failed part of the way (`true`: out of memory), so
    /// nothing may run in the realm.
    Failed(bool),
}

/// The page's realm.
pub(crate) fn realm(scope: &mut Scope<'_>) -> Result<Realm> {
    state(scope)?
        .realm
        .clone()
        .ok_or(clazel_js::Error::WrongRuntime)
}

/// The page's state, from inside a scope. `Err(Busy)` from inside one of
/// the host's own hooks, which have it as `self` already. A tree the parser
/// has finished with is moved to the page first (`PageState::finished`).
pub(crate) fn state<'a>(scope: &'a mut Scope<'_>) -> Result<&'a mut PageState> {
    let page = scope.host_mut::<crate::page::Page>()?;
    let Some(script) = page.script.as_deref_mut() else {
        return Err(clazel_js::Error::WrongType("a page with scripting state"));
    };
    if let Some(tree) = script.finished.take() {
        page.arena = tree;
    }
    Ok(script)
}

/// The document's tree, from inside a scope: the parser's while it parses,
/// else the page's.
pub(crate) fn arena<'a>(scope: &'a mut Scope<'_>) -> Result<&'a Arena> {
    let page = scope.host_mut::<crate::page::Page>()?;
    if let Some(script) = page.script.as_deref_mut()
        && let Some(tree) = script.finished.take()
    {
        page.arena = tree;
    }
    Ok(match &page.script {
        Some(script) => script.doc.arena(&page.arena),
        None => &page.arena,
    })
}
