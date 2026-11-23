//! DOM §2 events: the `Event` object (§2.2†), `EventTarget` with its listener
//! list (§2.7†, §2.6†), and the dispatch algorithm (§2.9†), over a
//! `clazel-dom` arena.
//!
//! <https://dom.spec.whatwg.org/#concept-event-dispatch>
//! (section numbers carry the mark † of phase-7.md: from memory, not read at
//! a pinned commit). Steps are quoted by their words, not their numbers,
//! because the numbers were not checked against a pinned text.
//!
//! Tier 0, not proven. The tree walk is iterative (a loop over the parent
//! links), so a deep tree does not overflow the stack.
//!
//! Modelling choices:
//! - Strings (the event type) are slices of code points, as in `clazel-dom`.
//! - A target is a [`TargetId`]: a node of the arena, or the `Window`
//!   stand-in at the end of a document's path. `clazel-dom` holds no
//!   listeners, so they live in [`Listeners`], a side table keyed by target.
//! - A listener's callback is a [`ListenerId`] the caller supplies. Two
//!   `addEventListener` calls with the same id are "the same callback" (the
//!   bindings of items 7.8 and 7.12 give one id to one JS function object).
//!   Dispatch calls [`Host::invoke`] with the id; the host runs the script,
//!   reports any exception itself ("inner invoke": the exception is reported
//!   and dispatch goes on), and may change the event and the listener table
//!   through [`Invocation`].
//! - `AbortSignal` is a stand-in: a [`SignalId`] made by
//!   [`Listeners::new_signal`]; [`Listeners::abort`] runs its abort steps
//!   (removing every listener added with it).
//! - **Shadow DOM is absent.** There are no shadow roots, so: `composed` is
//!   stored and exposed but has no effect; "retarget" is the identity (every
//!   item of a path but the first has a null shadow-adjusted target, as
//!   "dispatch" gives for a parent in the same tree); `relatedTarget` and
//!   the touch target lists do not exist; a `DocumentFragment`'s `host` is
//!   ignored by "get the parent"; slots and the closed-tree flag are not
//!   modelled; `clearTargets` never applies.
//! - **Activation behavior** (item 7.14): "dispatch" asks the [`Host`]
//!   whether the target (and, for a bubbling `click`, an ancestor) has
//!   activation behavior, and runs its legacy-pre-activation behavior
//!   before the capturing pass and its activation behavior (or
//!   legacy-canceled-activation behavior) after the flags are unset. An
//!   event is an "activation event" if it is a `MouseEvent` object
//!   ([`Event::set_mouse_event`]) of type `click`. What a node's behavior is
//!   belongs to HTML and is in [`crate::activation`].
//! - **Not modelled yet**: the legacy `window.event` global, and the
//!   `webkit`-prefixed legacy event types of "invoke". The return value is
//!   the "canceled flag" result.
//! - "Get the parent" of a node is its parent in the arena. For a Document
//!   with no parent it is the Window if the host says the document has one
//!   ([`Host::has_window`]) and the event is not `load`; the Window's own
//!   parent is null.
//! - The event path is built before any listener runs, so a listener that
//!   changes the tree does not change the path. [`dispatch`] borrows the
//!   arena for the whole call; a host that changes the tree from a listener
//!   calls [`build_path`] and then [`dispatch_path`] itself, which is the
//!   same algorithm split where the standard has no listener running.

use clazel_dom::exec::{Arena, ExecKind};
use clazel_dom::spec::Namespace;
use std::collections::{BTreeMap, BTreeSet};

/// The Window stand-in and the nodes: what an event can be dispatched at.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TargetId {
    /// A node of the arena.
    Node(usize),
    /// The `Window` of a document's browsing context.
    Window,
    /// Another event target that is not a node (`new EventTarget()`, an
    /// `AbortSignal`), by the caller's id. "Get the parent" of it is null.
    Object(u64),
}

/// What a listener's callback is: supplied by the caller, compared for
/// "the same callback" in `addEventListener` and `removeEventListener`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ListenerId(pub u64);

/// An `AbortSignal` stand-in ([`Listeners::new_signal`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SignalId(pub u64);

/// DOM §2.2† `Event.eventPhase`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EventPhase {
    /// `NONE` (0)
    None,
    /// `CAPTURING_PHASE` (1)
    Capturing,
    /// `AT_TARGET` (2)
    AtTarget,
    /// `BUBBLING_PHASE` (3)
    Bubbling,
}

impl EventPhase {
    /// The numeric value of the IDL constant.
    pub fn code(self) -> u16 {
        match self {
            EventPhase::None => 0,
            EventPhase::Capturing => 1,
            EventPhase::AtTarget => 2,
            EventPhase::Bubbling => 3,
        }
    }
}

/// DOM §2.2† `EventInit`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct EventInit {
    /// `bubbles`
    pub bubbles: bool,
    /// `cancelable`
    pub cancelable: bool,
    /// `composed` (no effect: there is no shadow DOM)
    pub composed: bool,
}

/// DOM §2.2† an event.
#[derive(Debug, Clone)]
pub struct Event {
    type_: Vec<u32>,
    bubbles: bool,
    cancelable: bool,
    composed: bool,
    is_trusted: bool,
    time_stamp: f64,
    target: Option<TargetId>,
    current_target: Option<TargetId>,
    event_phase: EventPhase,
    stop_propagation: bool,
    stop_immediate_propagation: bool,
    canceled: bool,
    in_passive_listener: bool,
    initialized: bool,
    dispatching: bool,
    path: Vec<TargetId>,
    /// "event is a MouseEvent object" (DOM §2.9† "dispatch"'s
    /// isActivationEvent): set by the host that made the event.
    mouse_event: bool,
}

impl Event {
    /// DOM §2.2† the `Event` constructor: `isTrusted` false, `timeStamp` the
    /// caller's "current high resolution time".
    pub fn new(type_: &[u32], init: EventInit, time_stamp: f64) -> Event {
        Event {
            type_: type_.to_vec(),
            bubbles: init.bubbles,
            cancelable: init.cancelable,
            composed: init.composed,
            is_trusted: false,
            time_stamp,
            target: None,
            current_target: None,
            event_phase: EventPhase::None,
            stop_propagation: false,
            stop_immediate_propagation: false,
            canceled: false,
            in_passive_listener: false,
            initialized: true,
            dispatching: false,
            path: Vec::new(),
            mouse_event: false,
        }
    }

    /// Marks the event as one that implements `MouseEvent` (or inherits
    /// it), which DOM §2.9† "dispatch" asks of an activation event.
    pub fn set_mouse_event(&mut self, value: bool) {
        self.mouse_event = value;
    }

    /// Whether the event is a `MouseEvent` object ([`Event::set_mouse_event`]).
    pub fn is_mouse_event(&self) -> bool {
        self.mouse_event
    }

    /// An event the user agent made (`isTrusted` true).
    pub fn new_trusted(type_: &[u32], init: EventInit, time_stamp: f64) -> Event {
        let mut e = Event::new(type_, init, time_stamp);
        e.is_trusted = true;
        e
    }

    /// DOM §2.2† `createEvent`'s result: the "initialized flag" is unset
    /// until [`Event::init_event`].
    pub fn new_uninitialized(time_stamp: f64) -> Event {
        let mut e = Event::new(&[], EventInit::default(), time_stamp);
        e.initialized = false;
        e
    }

    /// DOM §2.2† `initEvent()` ("inner event init"): does nothing while the
    /// event is being dispatched.
    pub fn init_event(&mut self, type_: &[u32], bubbles: bool, cancelable: bool) {
        if self.dispatching {
            return;
        }
        self.initialized = true;
        self.stop_propagation = false;
        self.stop_immediate_propagation = false;
        self.canceled = false;
        self.is_trusted = false;
        self.target = None;
        self.type_ = type_.to_vec();
        self.bubbles = bubbles;
        self.cancelable = cancelable;
    }

    /// `type`
    pub fn type_(&self) -> &[u32] {
        &self.type_
    }
    /// `bubbles`
    pub fn bubbles(&self) -> bool {
        self.bubbles
    }
    /// `cancelable`
    pub fn cancelable(&self) -> bool {
        self.cancelable
    }
    /// `composed`
    pub fn composed(&self) -> bool {
        self.composed
    }
    /// `isTrusted`
    pub fn is_trusted(&self) -> bool {
        self.is_trusted
    }
    /// `timeStamp`
    pub fn time_stamp(&self) -> f64 {
        self.time_stamp
    }
    /// `target`
    pub fn target(&self) -> Option<TargetId> {
        self.target
    }
    /// `currentTarget`
    pub fn current_target(&self) -> Option<TargetId> {
        self.current_target
    }
    /// `eventPhase`
    pub fn event_phase(&self) -> EventPhase {
        self.event_phase
    }
    /// `defaultPrevented`: the "canceled flag".
    pub fn default_prevented(&self) -> bool {
        self.canceled
    }
    /// `returnValue` getter: the inverse of the canceled flag.
    pub fn return_value(&self) -> bool {
        !self.canceled
    }
    /// `cancelBubble` getter: the "stop propagation flag".
    pub fn cancel_bubble(&self) -> bool {
        self.stop_propagation
    }
    /// Whether the "stop immediate propagation flag" is set.
    pub fn stop_immediate_propagation_flag(&self) -> bool {
        self.stop_immediate_propagation
    }
    /// Whether the "initialized flag" is set.
    pub fn is_initialized(&self) -> bool {
        self.initialized
    }

    /// `dispatchEvent` step 2: "Initialize event's isTrusted attribute to
    /// false."
    pub fn set_untrusted(&mut self) {
        self.is_trusted = false;
    }

    /// An event the user agent fires (DOM §2.10† "fire an event": "Set
    /// event's isTrusted attribute to true").
    pub fn set_trusted(&mut self) {
        self.is_trusted = true;
    }

    /// Whether the event is being dispatched (its dispatch flag).
    pub fn is_dispatching(&self) -> bool {
        self.dispatching
    }
    /// Whether the "in passive listener flag" is set.
    pub fn in_passive_listener(&self) -> bool {
        self.in_passive_listener
    }

    /// `stopPropagation()`: sets the "stop propagation flag".
    pub fn stop_propagation(&mut self) {
        self.stop_propagation = true;
    }

    /// `stopImmediatePropagation()`: sets both stop flags.
    pub fn stop_immediate_propagation(&mut self) {
        self.stop_propagation = true;
        self.stop_immediate_propagation = true;
    }

    /// `cancelBubble` setter: only `true` has an effect.
    pub fn set_cancel_bubble(&mut self, value: bool) {
        if value {
            self.stop_propagation = true;
        }
    }

    /// DOM §2.2† "set the canceled flag": only if cancelable and not in a
    /// passive listener.
    fn set_canceled_flag(&mut self) {
        if self.cancelable && !self.in_passive_listener {
            self.canceled = true;
        }
    }

    /// `preventDefault()`
    pub fn prevent_default(&mut self) {
        self.set_canceled_flag();
    }

    /// `returnValue` setter: `false` is `preventDefault()`, `true` does
    /// nothing.
    pub fn set_return_value(&mut self, value: bool) {
        if !value {
            self.set_canceled_flag();
        }
    }

    /// `composedPath()`: while dispatching, the invocation targets of the
    /// path (with no shadow DOM, none is hidden); empty otherwise.
    pub fn composed_path(&self) -> &[TargetId] {
        &self.path
    }
}

/// DOM §2.7† "event listener": an entry of a listener list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Listener {
    serial: u64,
    /// "type"
    pub type_: Vec<u32>,
    /// "callback"
    pub callback: ListenerId,
    /// "capture"
    pub capture: bool,
    /// "passive"
    pub passive: bool,
    /// "once"
    pub once: bool,
    /// "signal"
    pub signal: Option<SignalId>,
}

/// DOM §2.7† `AddEventListenerOptions` (`capture` is from
/// `EventListenerOptions`).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct AddOptions {
    /// `capture`
    pub capture: bool,
    /// `passive`: `None` is "not present" (the default passive value
    /// applies)
    pub passive: Option<bool>,
    /// `once`
    pub once: bool,
    /// `signal`
    pub signal: Option<SignalId>,
}

/// The listener lists of all targets, and the signals ([`SignalId`]).
#[derive(Debug, Clone, Default)]
pub struct Listeners {
    by_target: BTreeMap<TargetId, Vec<Listener>>,
    aborted: BTreeSet<SignalId>,
    next_serial: u64,
    next_signal: u64,
}

impl Listeners {
    /// An empty table.
    pub fn new() -> Listeners {
        Listeners::default()
    }

    /// A fresh, not aborted signal.
    pub fn new_signal(&mut self) -> SignalId {
        let id = SignalId(self.next_signal);
        self.next_signal = self.next_signal.saturating_add(1);
        id
    }

    /// Whether the signal's "aborted flag" is set.
    pub fn is_aborted(&self, signal: SignalId) -> bool {
        self.aborted.contains(&signal)
    }

    /// `AbortController.abort()` on the signal: sets the flag and runs the
    /// abort algorithms "add an event listener" registered: removes every
    /// listener added with the signal, from every target.
    pub fn abort(&mut self, signal: SignalId) {
        if !self.aborted.insert(signal) {
            return;
        }
        for list in self.by_target.values_mut() {
            list.retain(|l| l.signal != Some(signal));
        }
    }

    /// The "event listener list" of a target (in order of registration).
    pub fn listeners(&self, target: TargetId) -> &[Listener] {
        match self.by_target.get(&target) {
            Some(l) => l.as_slice(),
            None => &[],
        }
    }

    /// DOM §2.7† `addEventListener()`: "flatten", then "add an event
    /// listener". Returns whether a listener was added.
    ///
    /// The arena is read for the "default passive value" (the target is a
    /// Window, a Document, or the document element or body of its
    /// document, and the type is `touchstart`, `touchmove`, `wheel` or
    /// `mousewheel`).
    pub fn add_event_listener(
        &mut self,
        arena: &Arena,
        target: TargetId,
        type_: &[u32],
        callback: ListenerId,
        options: AddOptions,
    ) -> bool {
        // "If eventTarget is a ServiceWorkerGlobalScope ..." is not ours.
        // "If listener's signal is not null and is aborted, then return."
        if let Some(s) = options.signal
            && self.is_aborted(s)
        {
            return false;
        }
        // "If listener's callback is null, then return": a callback is an
        // id here, never null.
        // "If listener's passive is null, then set it to the default
        // passive value."
        let passive = match options.passive {
            Some(p) => p,
            None => default_passive_value(arena, type_, target),
        };
        // "If eventTarget's event listener list does not contain an event
        // listener whose type is listener's type, callback is listener's
        // callback, and capture is listener's capture, then append."
        let list = self.by_target.entry(target).or_default();
        if list
            .iter()
            .any(|l| l.type_ == type_ && l.callback == callback && l.capture == options.capture)
        {
            return false;
        }
        let serial = self.next_serial;
        self.next_serial = self.next_serial.saturating_add(1);
        list.push(Listener {
            serial,
            type_: type_.to_vec(),
            callback,
            capture: options.capture,
            passive,
            once: options.once,
            signal: options.signal,
        });
        true
    }

    /// DOM §2.7† `removeEventListener()`: removes the listener with this
    /// type, callback and capture. Returns whether one was removed.
    pub fn remove_event_listener(
        &mut self,
        target: TargetId,
        type_: &[u32],
        callback: ListenerId,
        capture: bool,
    ) -> bool {
        let Some(list) = self.by_target.get_mut(&target) else {
            return false;
        };
        let before = list.len();
        list.retain(|l| !(l.type_ == type_ && l.callback == callback && l.capture == capture));
        list.len() != before
    }

    /// Whether the listener is still in the target's list: the converse of
    /// its "removed" flag.
    fn contains_serial(&self, target: TargetId, serial: u64) -> bool {
        self.listeners(target).iter().any(|l| l.serial == serial)
    }

    fn remove_serial(&mut self, target: TargetId, serial: u64) {
        if let Some(list) = self.by_target.get_mut(&target) {
            list.retain(|l| l.serial != serial);
        }
    }
}

fn is_ascii_text(s: &str, units: &[u32]) -> bool {
    s.chars().map(u32::from).eq(units.iter().copied())
}

/// DOM §2.7† "default passive value".
fn default_passive_value(arena: &Arena, type_: &[u32], target: TargetId) -> bool {
    let touch_or_wheel = ["touchstart", "touchmove", "wheel", "mousewheel"]
        .iter()
        .any(|t| is_ascii_text(t, type_));
    if !touch_or_wheel {
        return false;
    }
    let node = match target {
        TargetId::Window => return true,
        TargetId::Node(n) => n,
        TargetId::Object(_) => return false,
    };
    if node >= arena.len() {
        return false;
    }
    // The node's node document: the root, when it is a Document.
    let mut root = node;
    while let Some(p) = arena.parent(root) {
        root = p;
    }
    if !matches!(arena.kind(root), ExecKind::Document { .. }) {
        return false;
    }
    if node == root {
        return true;
    }
    let element_named = |n: usize, names: &[&str]| match arena.kind(n) {
        ExecKind::Element {
            namespace: Some(Namespace::Html),
            local_name,
            ..
        } => names.iter().any(|nm| is_ascii_text(nm, local_name)),
        _ => false,
    };
    let is_element = |n: usize| matches!(arena.kind(n), ExecKind::Element { .. });
    let Some(&html) = arena.children(root).iter().find(|&&c| is_element(c)) else {
        return false;
    };
    if node == html {
        return true;
    }
    // "the body element": the first child of an `html` document element
    // that is a `body` or `frameset`.
    element_named(html, &["html"])
        && arena
            .children(html)
            .iter()
            .find(|&&c| element_named(c, &["body", "frameset"]))
            == Some(&node)
}

/// One struct of the event path (DOM §2.9† "event path").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PathItem {
    /// "invocation target"
    pub invocation_target: TargetId,
    /// "shadow-adjusted target": the dispatch target for the first item,
    /// null for the others (no shadow DOM).
    pub shadow_adjusted_target: Option<TargetId>,
}

/// What a listener's callback may touch while it runs.
pub struct Invocation<'a> {
    /// The callback to call.
    pub listener: ListenerId,
    /// The event (`currentTarget`, `eventPhase` and `target` are set;
    /// `this` is `currentTarget`).
    pub event: &'a mut Event,
    /// The listener lists, for `addEventListener` and `removeEventListener`
    /// from the callback.
    pub listeners: &'a mut Listeners,
}

/// The script side of dispatch: runs a callback.
pub trait Host {
    /// "inner invoke": call the callback with the event, with
    /// `currentTarget` as `this`. An exception is the host's to report;
    /// dispatch goes on.
    fn invoke(&mut self, call: Invocation<'_>);

    /// "Get the parent" of a Document: whether it has a Window to continue
    /// to (false for a document without a browsing context). Dispatch
    /// itself excludes the `load` event.
    fn has_window(&self, document: usize, event: &Event) -> bool {
        let _ = (document, event);
        false
    }

    /// DOM §2.9† "activation behavior": whether the node has it (HTML's
    /// `a` with an `href`, a submit button, a checkbox, and so on: see
    /// [`crate::activation`]). Asked of the target and, for a bubbling
    /// `click`, of its ancestors.
    fn has_activation_behavior(&mut self, node: usize) -> bool {
        let _ = node;
        false
    }

    /// DOM §2.9† "legacy-pre-activation behavior" of `node`, run before the
    /// event is dispatched to any listener (a checkbox's toggle).
    fn legacy_pre_activation_behavior(&mut self, node: usize) {
        let _ = node;
    }

    /// DOM §2.9† "legacy-canceled-activation behavior" of `node`, run after
    /// the dispatch if the event was canceled (a checkbox's restore).
    fn legacy_canceled_activation_behavior(&mut self, node: usize) {
        let _ = node;
    }

    /// DOM §2.9† "activation behavior" of `node` with the event, run after
    /// the dispatch if the event was not canceled (following a link,
    /// submitting a form).
    ///
    /// `listeners` is the page's listener table, which dispatch holds while
    /// it runs: the behavior may fire events of its own (`input`, `change`,
    /// `submit`), which need it, so the host puts it back for the length of
    /// the call.
    fn activation_behavior(&mut self, node: usize, event: &Event, listeners: &mut Listeners) {
        let _ = (node, event, listeners);
    }

    /// Called for each item of the path just before its listeners are
    /// taken ("Let listeners be a clone of event's currentTarget attribute
    /// value's event listener list"), so that the host can bring a target's
    /// event handlers (HTML §8.1.8†: `on*` content attributes) up to date in
    /// `listeners`.
    fn prepare_listeners(&mut self, target: TargetId, event_type: &[u32], listeners: &mut Listeners) {
        let _ = (target, event_type, listeners);
    }
}

/// Why `dispatchEvent` refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DispatchError {
    /// `InvalidStateError`: the event is being dispatched, or its
    /// initialized flag is unset (`dispatchEvent()`'s first steps).
    InvalidState,
    /// The target is a node id that is not in the arena.
    NoSuchNode,
}

impl core::fmt::Display for DispatchError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DispatchError::InvalidState => f.write_str("InvalidStateError"),
            DispatchError::NoSuchNode => f.write_str("the target is not in the arena"),
        }
    }
}

impl std::error::Error for DispatchError {}

/// DOM §2.7† `dispatchEvent()`: "If event's dispatch flag is set, or if its
/// initialized flag is not set, then throw an InvalidStateError", "Initialize
/// event's isTrusted attribute to false", then "dispatch". Returns the
/// dispatch's result: false if the event was canceled.
pub fn dispatch_event(
    arena: &Arena,
    listeners: &mut Listeners,
    target: TargetId,
    event: &mut Event,
    host: &mut dyn Host,
) -> Result<bool, DispatchError> {
    if event.dispatching || !event.initialized {
        return Err(DispatchError::InvalidState);
    }
    event.is_trusted = false;
    dispatch(arena, listeners, target, event, host)
}

/// DOM §2.9† "dispatch" for the user agent's own events (`isTrusted` as the
/// event has it): builds the path ([`build_path`]) and runs it
/// ([`dispatch_path`]).
pub fn dispatch(
    arena: &Arena,
    listeners: &mut Listeners,
    target: TargetId,
    event: &mut Event,
    host: &mut dyn Host,
) -> Result<bool, DispatchError> {
    let path = build_path(arena, target, event, &|d, e| host.has_window(d, e))?;
    Ok(dispatch_path(&path, listeners, event, host))
}

/// DOM §2.9† "dispatch", the part that builds the event path: "Append to an
/// event path" with the target, then "While parent is non-null" append the
/// parent and take "get the parent" of it. First item the target, last the
/// root (or its Window).
///
/// With no shadow DOM the "parent is a Window, or a node and target's root
/// is a shadow-including inclusive ancestor of parent" branch is the only
/// one: the parent is appended with a null shadow-adjusted target. The
/// "parent is relatedTarget" branch never holds (no relatedTarget).
pub fn build_path(
    arena: &Arena,
    target: TargetId,
    event: &Event,
    has_window: &dyn Fn(usize, &Event) -> bool,
) -> Result<Vec<PathItem>, DispatchError> {
    let mut path = vec![PathItem {
        invocation_target: target,
        shadow_adjusted_target: Some(target),
    }];
    let mut current = target;
    while let Some(parent) = get_the_parent(arena, current, event, has_window)? {
        path.push(PathItem {
            invocation_target: parent,
            shadow_adjusted_target: None,
        });
        current = parent;
    }
    Ok(path)
}

/// "Get the parent" of a node (its parent), of a Document (its Window if it
/// has one and the event is not `load`), of a Window (null).
fn get_the_parent(
    arena: &Arena,
    of: TargetId,
    event: &Event,
    has_window: &dyn Fn(usize, &Event) -> bool,
) -> Result<Option<TargetId>, DispatchError> {
    let TargetId::Node(n) = of else {
        return Ok(None);
    };
    if n >= arena.len() {
        return Err(DispatchError::NoSuchNode);
    }
    if let Some(p) = arena.parent(n) {
        return Ok(Some(TargetId::Node(p)));
    }
    if matches!(arena.kind(n), ExecKind::Document { .. })
        && !is_ascii_text("load", &event.type_)
        && has_window(n, event)
    {
        return Ok(Some(TargetId::Window));
    }
    Ok(None)
}

/// DOM §2.9† "dispatch", after the path is built: "Set event's dispatch
/// flag", the capturing pass ("for each struct in event's path, in reverse
/// order"), the bubbling pass ("for each struct in event's path"), then
/// "Set event's eventPhase attribute to NONE, currentTarget to null, path
/// to the empty list" and unset the dispatch and both stop flags. Returns
/// false if the canceled flag is set, true otherwise.
pub fn dispatch_path(
    path: &[PathItem],
    listeners: &mut Listeners,
    event: &mut Event,
    host: &mut dyn Host,
) -> bool {
    // "Let isActivationEvent be true, if event is a MouseEvent object and
    // event's type attribute is "click"; otherwise false."
    let is_activation_event = event.mouse_event && is_ascii_text("click", &event.type_);
    // "If isActivationEvent is true and target has activation behavior,
    // then set activationTarget to target." and, in the loop over the
    // parents, "If isActivationEvent is true, event's bubbles attribute is
    // true, activationTarget is null, and parent has activation behavior,
    // then set activationTarget to parent." (With no shadow DOM every
    // parent is in the target's tree, so that is the branch every parent
    // takes; the Window has no activation behavior.)
    let mut activation_target: Option<usize> = None;
    if is_activation_event {
        for (i, item) in path.iter().enumerate() {
            let TargetId::Node(n) = item.invocation_target else {
                continue;
            };
            if i > 0 && !event.bubbles {
                break;
            }
            if host.has_activation_behavior(n) {
                activation_target = Some(n);
                break;
            }
        }
    }
    // "Set event's dispatch flag to true." (It is set first in the
    // standard; nothing between reads it.)
    event.dispatching = true;
    event.path = path.iter().map(|i| i.invocation_target).collect();
    // "If activationTarget is non-null and activationTarget has
    // legacy-pre-activation behavior, then run activationTarget's
    // legacy-pre-activation behavior."
    if let Some(a) = activation_target {
        host.legacy_pre_activation_behavior(a);
    }

    // Capturing pass.
    for i in (0..path.len()).rev() {
        let Some(item) = path.get(i) else { continue };
        // "If struct's shadow-adjusted target is non-null, then set event's
        // eventPhase attribute to AT_TARGET. Otherwise, CAPTURING_PHASE."
        event.event_phase = if item.shadow_adjusted_target.is_some() {
            EventPhase::AtTarget
        } else {
            EventPhase::Capturing
        };
        invoke(path, i, event, Pass::Capturing, listeners, host);
    }

    // Bubbling pass.
    for i in 0..path.len() {
        let Some(item) = path.get(i) else { continue };
        if item.shadow_adjusted_target.is_some() {
            event.event_phase = EventPhase::AtTarget;
        } else {
            // "If event's bubbles attribute is false, then continue."
            if !event.bubbles {
                continue;
            }
            event.event_phase = EventPhase::Bubbling;
        }
        invoke(path, i, event, Pass::Bubbling, listeners, host);
    }

    event.event_phase = EventPhase::None;
    event.current_target = None;
    event.path.clear();
    event.dispatching = false;
    event.stop_propagation = false;
    event.stop_immediate_propagation = false;

    // "If activationTarget is non-null, then: 1. If event's canceled flag is
    // unset, then run activationTarget's activation behavior with event.
    // 2. Otherwise, if activationTarget has legacy-canceled-activation
    // behavior, then run activationTarget's legacy-canceled-activation
    // behavior."
    if let Some(a) = activation_target {
        if event.canceled {
            host.legacy_canceled_activation_behavior(a);
        } else {
            host.activation_behavior(a, event, listeners);
        }
    }

    // "Return false if event's canceled flag is set, and true otherwise."
    !event.canceled
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Pass {
    Capturing,
    Bubbling,
}

/// DOM §2.9† "invoke" for `path[i]`.
fn invoke(
    path: &[PathItem],
    i: usize,
    event: &mut Event,
    pass: Pass,
    listeners: &mut Listeners,
    host: &mut dyn Host,
) {
    // "Set event's target to the shadow-adjusted target of the last struct
    // in event's path, that is either struct or preceding struct, whose
    // shadow-adjusted target is non-null." (Retargeting: with no shadow DOM
    // this is always the first item's.)
    if let Some(t) = path
        .get(..=i)
        .and_then(|s| s.iter().rev().find_map(|p| p.shadow_adjusted_target))
    {
        event.target = Some(t);
    }
    // relatedTarget and the touch target list: absent.
    // "If event's stop propagation flag is set, then return."
    if event.stop_propagation {
        return;
    }
    let Some(item) = path.get(i) else { return };
    // "Initialize event's currentTarget attribute to struct's invocation
    // target."
    event.current_target = Some(item.invocation_target);
    host.prepare_listeners(item.invocation_target, &event.type_, listeners);
    // "Let listeners be a clone of event's currentTarget attribute value's
    // event listener list."
    let snapshot: Vec<Listener> = listeners.listeners(item.invocation_target).to_vec();
    // "Let found be the result of running inner invoke".
    inner_invoke(
        item.invocation_target,
        event,
        &snapshot,
        pass,
        listeners,
        host,
    );
    // "If found is false and event's isTrusted is true" (legacy webkit
    // event types): not modelled.
}

/// DOM §2.10† "inner invoke". Returns "found".
fn inner_invoke(
    current: TargetId,
    event: &mut Event,
    snapshot: &[Listener],
    pass: Pass,
    listeners: &mut Listeners,
    host: &mut dyn Host,
) -> bool {
    let mut found = false;
    // "For each listener of listeners, whose removed is false".
    for l in snapshot {
        if !listeners.contains_serial(current, l.serial) {
            continue;
        }
        // "If event's type attribute value is not listener's type, then
        // continue."
        if l.type_ != event.type_ {
            continue;
        }
        // "Set found to true."
        found = true;
        // "If phase is "capturing" and listener's capture is false, then
        // continue." and the same for "bubbling" and true.
        if pass == Pass::Capturing && !l.capture {
            continue;
        }
        if pass == Pass::Bubbling && l.capture {
            continue;
        }
        // "If listener's once is true, then remove an event listener".
        if l.once {
            listeners.remove_serial(current, l.serial);
        }
        // The global object and window.event steps: not modelled.
        // "If listener's passive is true, then set
        // currentEvent's in passive listener flag."
        if l.passive {
            event.in_passive_listener = true;
        }
        // "Call a user object's operation": the host.
        host.invoke(Invocation {
            listener: l.callback,
            event,
            listeners,
        });
        // "Unset event's in passive listener flag."
        event.in_passive_listener = false;
        // "If event's stop immediate propagation flag is set, then return
        // found."
        if event.stop_immediate_propagation {
            return found;
        }
    }
    found
}
