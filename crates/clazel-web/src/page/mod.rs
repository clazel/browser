//! The platform objects of a page, exposed to script through
//! `clazel-webidl`'s generated bindings (phase-7.md items 7.12, 7.13 and
//! 7.15's `Window`, `Location`, `History`, `Navigator` and `console`).
//!
//! [`Page`] is the `clazel-js` [`Host`] and the bindings'
//! [`Platform`]: it owns the document (a `clazel-dom` arena), the event
//! listeners ([`crate::events`]), the other platform objects (events, live
//! collections, token lists, abort signals, the location, history and
//! navigator), the wrappers, and the hooks to the renderer ([`PageHooks`]).
//! Its implementations of the generated traits are in [`node`], [`event`]
//! and [`window`]; [`console`] is the `console` namespace.
//!
//! Modelling choices:
//! - **Keys.** The `Window` is key 0; node `n` of the arena is key
//!   `NODE | n`; every other platform object is `OBJECT | id`, with its
//!   state in [`Page`]'s table.
//! - **Wrappers.** A node's wrapper is kept in `clazel-dom`'s wrapper slot
//!   (`Arena::set_wrapper`, item 7.12's operation, proven to keep `wf`), as
//!   an index into the page's table of handles; every other wrapper in a
//!   side table by key (phase-7.md 7.12, "Wrappers").
//! - **One document per page**, the arena's node 0: `ownerDocument` is it,
//!   and there is no adoption between documents (`clazel-dom`'s arena is one
//!   document): `importNode` is a clone, and `adoptNode` removes the node
//!   from its parent. `document.implementation` and `new Document()` do not
//!   exist.
//! - **The interface of an element** is its HTML element interface when the
//!   bindings expose it (`html`, `head`, `title`, `body`, `div`, `span`, `p`,
//!   `a`), `HTMLElement` for the other HTML elements (the standard's
//!   specific interfaces are not exposed yet; an element with no definition
//!   in HTML is `HTMLUnknownElement` only for the names listed in
//!   [`node`]), and `Element` in other namespaces.
//! - **Hooks.** No renderer runs `clazel-web` yet (item 7.17), so the
//!   renderer-side hooks are a trait, [`PageHooks`]: `location.href = …`
//!   calls [`PageHooks::navigate`] (the renderer will send the kernel's
//!   `Navigate`), `history.pushState` and `replaceState` call
//!   [`PageHooks::update_url`] (7.16's `UpdateUrl` message is not built
//!   yet), and `console` calls [`PageHooks::log`]. The page also records
//!   every call ([`Page::hook_calls`]).

pub mod attr;
pub mod console;
pub mod event;
pub mod forms;
pub mod fragment;
pub mod handlers;
pub mod input;
pub mod mutation;
pub mod node;
pub mod range;
pub mod ui_events;
pub mod window;

use std::collections::HashMap;

use clazel_dom::exec::Arena;
use clazel_js::{
    Config, ErrorKind, Handle, Host, LoadPayload, Local, ModuleRequest, Realm, RealmOptions,
    Referrer, RejectionOperation, Result, Runtime, Scope,
};
use clazel_url::url::parse::basic_url_parser;
use clazel_url::url::record::ParsedUrl;
use clazel_webidl::convert::DomString;
use clazel_webidl::exception::{self, DomErrorName};
use clazel_webidl::generated::bindings::InterfaceId;
use clazel_webidl::platform::{Bindings, ObjectKey, Platform};

use crate::events::{Listeners, SignalId};

/// The key bit of a node.
const NODE: u64 = 1 << 62;
/// The key bit of another platform object.
const OBJECT: u64 = 1 << 61;
/// The `Window`.
pub const WINDOW: ObjectKey = ObjectKey(0);

/// How loud a `console` message is (Console §1.1† "Logger": the log level).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LogLevel {
    /// `console.log`, `console.info` and friends.
    Log,
    /// `console.debug`.
    Debug,
    /// `console.warn`.
    Warn,
    /// `console.error`, `console.assert`, and an uncaught exception.
    Error,
}

/// What the page asks of the renderer. Every method has a default that
/// does nothing; the page records each call as a [`HookCall`] as well.
pub trait PageHooks: Send {
    /// HTML §7.4.2† "navigate": `location.href = …`, `location.assign`,
    /// `location.replace` (with `replace`), and `location.reload`. The
    /// renderer sends the kernel's `Navigate` (item 7.15).
    fn navigate(&mut self, url: &str, replace: bool) {
        let _ = (url, replace);
    }
    /// HTML §7.4.4† "URL and history update steps": `pushState` (`replace`
    /// false) and `replaceState` (`replace` true). The renderer sends item
    /// 7.16's `UpdateUrl`, which is not built yet.
    fn update_url(&mut self, url: &str, replace: bool) {
        let _ = (url, replace);
    }
    /// HTML §4.10.21.3† "plan to navigate" for a form submitted with a body
    /// (`POST`): the renderer sends the kernel's `Submit` (item 6.16). A
    /// `GET` is [`PageHooks::navigate`]; the default does that for a `GET` and
    /// nothing for a `POST`.
    fn submit(&mut self, url: &str, method: &str, content_type: &str, body: &[u8]) {
        let _ = (content_type, body);
        if method == "GET" {
            self.navigate(url, false);
        }
    }
    /// `history.go(delta)`, `back` and `forward` (HTML §7.4.?
    /// "traverse the history by a delta").
    fn traverse_history(&mut self, delta: i32) {
        let _ = delta;
    }
    /// A `console` message, for the host's log; never shown in the page.
    fn log(&mut self, level: LogLevel, text: &str) {
        let _ = (level, text);
    }
    /// The current time in milliseconds for `Event.timeStamp` (HTML's
    /// "current high resolution time"); the default is 0.
    fn now_ms(&mut self) -> f64 {
        0.0
    }
    /// `document.cookie`'s getter (HTML §3.1.? "cookie"): the cookie string
    /// the renderer asks the kernel for. The default is the empty string
    /// (a page with no cookie jar).
    fn cookie_get(&mut self) -> String {
        String::new()
    }
    /// `document.cookie`'s setter: the cookie string to store.
    fn cookie_set(&mut self, cookie: &str) {
        let _ = cookie;
    }
    /// `localStorage.getItem(key)` (HTML §12.2.1†): the kernel's answer, if
    /// there is a value. The default is a storage with nothing in it.
    fn storage_get(&mut self, key: &str) -> Option<String> {
        let _ = key;
        None
    }
    /// `localStorage.setItem(key, value)`: false if the kernel refused it
    /// (the quota), which script sees as a `QuotaExceededError`.
    fn storage_set(&mut self, key: &str, value: &str) -> bool {
        let _ = (key, value);
        true
    }
    /// `localStorage.removeItem(key)`.
    fn storage_remove(&mut self, key: &str) {
        let _ = key;
    }
    /// `localStorage.clear()`.
    fn storage_clear(&mut self) {}
    /// `localStorage.key(index)`.
    fn storage_key(&mut self, index: u64) -> Option<String> {
        let _ = index;
        None
    }
    /// `localStorage.length`.
    fn storage_length(&mut self) -> u64 {
        0
    }
}

/// The default hooks: nothing but the page's own record.
#[derive(Debug, Default)]
pub struct NoHooks;

impl PageHooks for NoHooks {}

/// A call the page made to its hooks.
#[derive(Clone, Debug, PartialEq)]
pub enum HookCall {
    /// [`PageHooks::navigate`].
    Navigate {
        /// The URL, serialized.
        url: String,
        /// Whether history is replaced.
        replace: bool,
    },
    /// [`PageHooks::update_url`].
    UpdateUrl {
        /// The URL, serialized.
        url: String,
        /// `replaceState` rather than `pushState`.
        replace: bool,
    },
    /// [`PageHooks::traverse_history`].
    Traverse(i32),
    /// [`PageHooks::submit`].
    Submit {
        /// The URL, serialized.
        url: String,
        /// `POST`.
        method: String,
        /// The body's content type.
        content_type: String,
        /// The body.
        body: Vec<u8>,
    },
    /// [`PageHooks::log`].
    Log(LogLevel, String),
}

/// The namespace of `getElementsByTagNameNS`: "*", null, or a namespace.
#[derive(Clone, Debug)]
pub(crate) enum NsFilter {
    Any,
    Null,
    Uri(Vec<u32>),
}

/// What a collection holds (DOM §4.2.10† `NodeList`, §4.2.10.2†
/// `HTMLCollection`): live ones are computed each time they are read.
#[derive(Clone, Debug)]
pub(crate) enum Collection {
    /// A node's children (`childNodes`).
    ChildNodes(usize),
    /// A node's element children (`children`).
    Children(usize),
    /// "the list of elements with qualified name" under a root.
    ByTagName(usize, Vec<u32>),
    /// "the list of elements with class names" under a root.
    ByClassName(usize, Vec<Vec<u32>>),
    /// "the list of elements with namespace namespace and local name
    /// localName" under a root.
    ByTagNameNs(usize, NsFilter, Vec<u32>),
    /// A static list (`querySelectorAll`).
    Static(Vec<usize>),
}

/// An event object's state.
#[derive(Debug)]
pub(crate) struct EventData {
    pub(crate) event: crate::events::Event,
    pub(crate) interface: InterfaceId,
    pub(crate) detail: Option<Handle>,
}

/// A platform object that is not a node or the window.
#[derive(Debug)]
pub(crate) enum Object {
    Event(Box<EventData>),
    NodeList(Collection),
    HtmlCollection(Collection),
    TokenList(usize),
    EventTarget,
    AbortSignal {
        signal: SignalId,
        reason: Option<Handle>,
    },
    AbortController {
        signal: ObjectKey,
    },
    Location,
    History,
    Navigator,
    Attr(attr::AttrState),
    NamedNodeMap(usize),
    DataSet(usize),
    MutationObserver(u64),
    MutationRecord(Box<mutation::Record>),
    Range(range::RangeState),
    UserActivation,
}

/// A page: the document, its platform objects and their wrappers.
pub struct Page {
    pub(crate) arena: Arena,
    pub(crate) url: ParsedUrl,
    pub(crate) listeners: Listeners,
    pub(crate) callbacks: Vec<(u64, Handle)>,
    pub(crate) next_callback: u64,
    pub(crate) objects: HashMap<u64, Object>,
    pub(crate) next_object: u64,
    pub(crate) node_wrappers: Vec<Handle>,
    pub(crate) other_wrappers: HashMap<ObjectKey, Handle>,
    pub(crate) bindings: Bindings,
    pub(crate) hooks: Box<dyn PageHooks>,
    pub(crate) hook_calls: Vec<HookCall>,
    pub(crate) window_name: DomString,
    pub(crate) history_state: Option<Handle>,
    pub(crate) history_length: u32,
    pub(crate) location: Option<ObjectKey>,
    pub(crate) history: Option<ObjectKey>,
    pub(crate) navigator: Option<ObjectKey>,
    pub(crate) random: u64,
    pub(crate) mo: mutation::Observers,
    pub(crate) attr_index: HashMap<(usize, u8, Vec<u32>), ObjectKey>,
    /// What HTML's script processing keeps (item 7.15,
    /// [`crate::scripting`]), if the page runs scripts through it.
    pub(crate) script: Option<Box<crate::scripting::state::PageState>>,
    /// The UI state of item 7.14: form control state, focus, user
    /// activation, the data of UI events and the event handlers.
    pub(crate) ui: crate::ui::Ui,
}

impl core::fmt::Debug for Page {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Page")
            .field("nodes", &self.arena.len())
            .finish_non_exhaustive()
    }
}

impl Page {
    /// A page for `arena` (a parsed document), whose URL is `url` (the
    /// document's URL, serialized; `about:blank` if it does not parse).
    #[must_use]
    pub fn new(arena: Arena, url: &str, hooks: Box<dyn PageHooks>) -> Page {
        let points: Vec<u32> = url.chars().map(u32::from).collect();
        let blank: Vec<u32> = "about:blank".chars().map(u32::from).collect();
        let url = basic_url_parser(&points, None)
            .or_else(|| basic_url_parser(&blank, None))
            .unwrap_or_else(|| ParsedUrl {
                scheme: "about".chars().map(u32::from).collect(),
                username: Vec::new(),
                password: Vec::new(),
                host: None,
                port: None,
                path: clazel_url::url::record::ParsedPath::Opaque(
                    "blank".chars().map(u32::from).collect(),
                ),
                query: None,
                fragment: None,
            });
        Page {
            arena,
            url,
            listeners: Listeners::new(),
            callbacks: Vec::new(),
            next_callback: 0,
            objects: HashMap::new(),
            next_object: 0,
            node_wrappers: Vec::new(),
            other_wrappers: HashMap::new(),
            bindings: Bindings::new(),
            hooks,
            hook_calls: Vec::new(),
            window_name: Vec::new(),
            history_state: None,
            history_length: 1,
            location: None,
            history: None,
            navigator: None,
            random: 0x9E37_79B9_7F4A_7C15,
            mo: mutation::Observers::default(),
            attr_index: HashMap::new(),
            script: None,
            ui: crate::ui::Ui::default(),
        }
    }

    /// The document.
    #[must_use]
    pub fn arena(&self) -> &Arena {
        &self.arena
    }

    /// The document's URL, serialized.
    #[must_use]
    pub fn url(&self) -> String {
        points_to_string(&self.url.serialize(false))
    }

    /// Every call the page made to its hooks, in order.
    #[must_use]
    pub fn hook_calls(&self) -> &[HookCall] {
        &self.hook_calls
    }

    /// The key of node `n`.
    #[must_use]
    pub fn node_key(n: usize) -> ObjectKey {
        ObjectKey(NODE | n as u64)
    }

    /// The node a key names, if it names one.
    #[must_use]
    pub fn key_node(&self, key: ObjectKey) -> Option<usize> {
        if key.0 & NODE == 0 {
            return None;
        }
        let n = usize::try_from(key.0 & !NODE).ok()?;
        (n < self.arena.len()).then_some(n)
    }

    pub(crate) fn add_object(&mut self, o: Object) -> ObjectKey {
        let id = self.next_object;
        self.next_object = self.next_object.saturating_add(1);
        self.objects.insert(id, o);
        ObjectKey(OBJECT | id)
    }

    pub(crate) fn object(&self, key: ObjectKey) -> Option<&Object> {
        if key.0 & OBJECT == 0 {
            return None;
        }
        self.objects.get(&(key.0 & !OBJECT))
    }

    pub(crate) fn object_mut(&mut self, key: ObjectKey) -> Option<&mut Object> {
        if key.0 & OBJECT == 0 {
            return None;
        }
        self.objects.get_mut(&(key.0 & !OBJECT))
    }

    pub(crate) fn object_id(key: ObjectKey) -> Option<u64> {
        (key.0 & OBJECT != 0).then_some(key.0 & !OBJECT)
    }

    pub(crate) fn record(&mut self, call: HookCall) {
        match &call {
            HookCall::Navigate { url, replace } => self.hooks.navigate(url, *replace),
            HookCall::UpdateUrl { url, replace } => self.hooks.update_url(url, *replace),
            HookCall::Traverse(d) => self.hooks.traverse_history(*d),
            HookCall::Submit {
                url,
                method,
                content_type,
                body,
            } => self.hooks.submit(url, method, content_type, body),
            HookCall::Log(level, text) => self.hooks.log(*level, text),
        }
        self.hook_calls.push(call);
    }

    /// Makes a runtime for this page: a realm with the bindings installed
    /// (every exposed interface, `DOMException`, and the global object as
    /// the `Window`) and `console`.
    ///
    /// # Errors
    /// What `clazel-js` returns.
    pub fn into_runtime(self, config: Config) -> Result<(Runtime, Realm)> {
        let mut rt = Runtime::new(config, self)?;
        let realm = rt.scope(|scope| {
            let realm = scope.create_realm(RealmOptions::default())?;
            clazel_webidl::generated::bindings::install::<Page>(scope, &realm)?;
            console::install(scope, &realm)?;
            Ok(realm)
        })?;
        Ok((rt, realm))
    }
}

impl Host for Page {
    /// HTML §8.1.5.? HostLoadImportedModule, for a page with script state.
    fn load_imported_module(
        &mut self,
        scope: &mut Scope<'_>,
        referrer: Referrer<'_>,
        request: &ModuleRequest,
        payload: LoadPayload,
    ) -> Result<()> {
        let Page { script, arena, .. } = self;
        match script.as_deref_mut() {
            Some(st) => st.load_imported_module(arena, scope, referrer, request, payload),
            None => Err(clazel_js::Error::NotImplemented("module loading")),
        }
    }

    /// HTML §8.1.5.? HostPromiseRejectionTracker, for a page with script
    /// state.
    fn promise_rejection_tracker(
        &mut self,
        scope: &mut Scope<'_>,
        promise: Local<'_>,
        operation: RejectionOperation,
    ) {
        if let Some(st) = self.script.as_deref_mut() {
            st.promise_rejection_tracker(scope, promise, operation);
        }
    }

    fn random_u64(&mut self) -> u64 {
        // xorshift64*: Math.random needs no more (ECMA-262 asks for no
        // unpredictability), and rule 8 keeps entropy sources out.
        let mut x = self.random;
        x ^= x.wrapping_shr(12);
        x ^= x.wrapping_shl(25);
        x ^= x.wrapping_shr(27);
        self.random = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
}

impl Platform for Page {
    fn interface_of(&mut self, key: ObjectKey) -> Option<InterfaceId> {
        if key == WINDOW {
            return Some(InterfaceId::Window);
        }
        if let Some(n) = self.key_node(key) {
            return Some(node::interface_of_node(&self.arena, n));
        }
        Some(match self.object(key)? {
            Object::Event(e) => e.interface,
            Object::NodeList(_) => InterfaceId::NodeList,
            Object::HtmlCollection(_) => InterfaceId::HTMLCollection,
            Object::TokenList(_) => InterfaceId::DOMTokenList,
            Object::EventTarget => InterfaceId::EventTarget,
            Object::AbortSignal { .. } => InterfaceId::AbortSignal,
            Object::AbortController { .. } => InterfaceId::AbortController,
            Object::Location => InterfaceId::Location,
            Object::History => InterfaceId::History,
            Object::Navigator => InterfaceId::Navigator,
            Object::Attr(_) => InterfaceId::Attr,
            Object::NamedNodeMap(_) => InterfaceId::NamedNodeMap,
            Object::DataSet(_) => InterfaceId::DOMStringMap,
            Object::MutationObserver(_) => InterfaceId::MutationObserver,
            Object::MutationRecord(_) => InterfaceId::MutationRecord,
            Object::Range(_) => InterfaceId::Range,
            Object::UserActivation => InterfaceId::UserActivation,
        })
    }

    fn wrapper(&mut self, key: ObjectKey) -> Option<Handle> {
        match self.key_node(key) {
            Some(n) => {
                let slot = self.arena.wrapper(n)?;
                self.node_wrappers.get(slot).cloned()
            }
            None => self.other_wrappers.get(&key).cloned(),
        }
    }

    fn set_wrapper(&mut self, key: ObjectKey, wrapper: Handle) {
        match self.key_node(key) {
            Some(n) => {
                let slot = self.node_wrappers.len();
                self.node_wrappers.push(wrapper);
                self.arena.set_wrapper(n, Some(slot));
            }
            None => {
                self.other_wrappers.insert(key, wrapper);
            }
        }
    }

    fn window_key(&self) -> ObjectKey {
        WINDOW
    }

    fn bindings(&mut self) -> &mut Bindings {
        &mut self.bindings
    }

    fn reflect_get(
        scope: &mut Scope<'_>,
        this: ObjectKey,
        name: &str,
    ) -> Result<Option<DomString>> {
        let e = node::element_of(scope, this)?;
        let page = page(scope)?;
        let name: Vec<u32> = name.chars().map(u32::from).collect();
        Ok(node::attribute_value(&page.arena, e, &name).map(|v| points_to_units(&v)))
    }

    fn event_handler_get<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        event: &str,
    ) -> Result<Option<Local<'s>>> {
        handlers::get(scope, this, event)
    }

    fn event_handler_set<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        event: &str,
        value: Option<Local<'s>>,
    ) -> Result<()> {
        handlers::set(scope, this, event, value)
    }

    fn reflect_set(
        scope: &mut Scope<'_>,
        this: ObjectKey,
        name: &str,
        value: Option<DomString>,
    ) -> Result<()> {
        let e = node::element_of(scope, this)?;
        let page = page(scope)?;
        let name: Vec<u32> = name.chars().map(u32::from).collect();
        match value {
            Some(v) => node::set_attribute_value(page, e, &name, units_to_points(&v)),
            None => node::remove_attribute_named(page, e, &name),
        }
        Ok(())
    }
}

/// The page, from inside a native function.
///
/// # Errors
/// `Error::WrongType` if the runtime's host is not a [`Page`].
pub fn page<'a>(scope: &'a mut Scope<'_>) -> Result<&'a mut Page> {
    scope.host_mut::<Page>()
}

/// A `TypeError`.
pub(crate) fn type_error(scope: &mut Scope<'_>, message: &str) -> clazel_js::Error {
    scope.throw_error(ErrorKind::TypeError, message)
}

/// A `DOMException`.
pub(crate) fn dom_error(
    scope: &mut Scope<'_>,
    name: DomErrorName,
    message: &str,
) -> clazel_js::Error {
    exception::throw::<Page>(scope, name, message)
}

/// Code units to code points: surrogate pairs combined, lone surrogates
/// kept as themselves (`clazel-dom`'s strings are code points, as Infra's
/// strings are code units read as code points).
#[must_use]
pub fn units_to_points(units: &[u16]) -> Vec<u32> {
    char::decode_utf16(units.iter().copied())
        .map(|r| match r {
            Ok(c) => u32::from(c),
            Err(e) => u32::from(e.unpaired_surrogate()),
        })
        .collect()
}

/// Code points to code units (a lone surrogate code point is its unit).
#[must_use]
pub fn points_to_units(points: &[u32]) -> Vec<u16> {
    let mut out = Vec::with_capacity(points.len());
    for &p in points {
        match char::from_u32(p) {
            Some(c) => {
                let mut buf = [0u16; 2];
                out.extend_from_slice(c.encode_utf16(&mut buf));
            }
            None => out.push(u16::try_from(p).unwrap_or(0xFFFD)),
        }
    }
    out
}

/// Code points to a Rust string, replacing what is not a scalar value.
#[must_use]
pub fn points_to_string(points: &[u32]) -> String {
    points
        .iter()
        .map(|&p| char::from_u32(p).unwrap_or('\u{FFFD}'))
        .collect()
}

/// A Rust string's code points.
#[must_use]
pub fn str_points(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// A Rust string's code units.
#[must_use]
pub fn str_units(s: &str) -> DomString {
    s.encode_utf16().collect()
}

/// Runs a script in the page's realm. An uncaught exception is "reported"
/// (HTML §8.1.4.? "report an exception"): written to the host's log as a
/// `console` error, and returned.
///
/// # Errors
/// The uncaught exception, and engine errors.
pub fn run_script(rt: &mut Runtime, realm: &Realm, name: &str, text: &str) -> Result<()> {
    rt.scope(|scope| {
        let r = scope
            .eval_script(realm, clazel_js::Source::new(name, text))
            .map(|_| ());
        if let Err(clazel_js::Error::Thrown(e)) = &r {
            let report = scope.report(e)?;
            let text = format!("Uncaught {}: {}", report.name, report.message);
            page(scope)?.record(HookCall::Log(LogLevel::Error, text));
        }
        r
    })
}

/// A local for a value held by a handle, or `undefined`.
pub(crate) fn local_or_undefined<'s>(
    scope: &mut Scope<'s>,
    h: Option<&Handle>,
) -> Result<Local<'s>> {
    match h {
        Some(h) => scope.local(h),
        None => Ok(scope.undefined()),
    }
}
