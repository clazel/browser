//! `EventTarget`, `Event`, `CustomEvent`, `AbortController` and
//! `AbortSignal` (DOM §2†, §3†) over [`crate::events`]'s dispatch.
//!
//! <https://dom.spec.whatwg.org/#events>
//!
//! - A listener's callback is a JavaScript value kept by a handle; the
//!   [`crate::events::ListenerId`] of a callback is the same for the same
//!   object ("the same callback", compared with `===`).
//! - Dispatch runs [`crate::events::dispatch_path`] with the listener table
//!   and the event taken out of the page; around each call into script they
//!   are put back, so the listener can read the event and add or remove
//!   listeners, and are taken out again after (`JsInvoke`).
//! - "Inner invoke" reports a listener's exception (HTML "report an
//!   exception": the host's log) and goes on.
//! - Not implemented: `AbortSignal.timeout` (timers are the event loop's,
//!   item 7.15) and `AbortSignal.any`; the `abort` event is fired at the
//!   signal, but `onabort` is not exposed (event handler attributes).

use clazel_js::{Handle, Local, Result, Scope};
use clazel_webidl::convert::{self, DomString};
use clazel_webidl::exception::DomErrorName;
use clazel_webidl::generated::bindings::*;
use clazel_webidl::platform::ObjectKey;

use super::{
    EventData, HookCall, LogLevel, Object, Page, WINDOW, dom_error, forms, handlers,
    local_or_undefined, page, points_to_units, str_units, type_error, units_to_points,
};
use crate::events::{
    self, AddOptions, Event, EventInit as Init, Invocation, ListenerId, Listeners, SignalId,
    TargetId,
};
use crate::ui::HANDLER_ID_BASE;

/// The event target a key names: a node, the window, or another object.
pub(super) fn target_of(page: &Page, key: ObjectKey) -> Option<TargetId> {
    if key == WINDOW {
        return Some(TargetId::Window);
    }
    if let Some(n) = page.key_node(key) {
        return Some(TargetId::Node(n));
    }
    match page.object(key)? {
        Object::EventTarget | Object::AbortSignal { .. } => {
            Page::object_id(key).map(TargetId::Object)
        }
        _ => None,
    }
}

/// The key of an event target.
pub(super) fn key_of_target(t: TargetId) -> ObjectKey {
    match t {
        TargetId::Window => WINDOW,
        TargetId::Node(n) => Page::node_key(n),
        TargetId::Object(id) => ObjectKey((1 << 61) | id),
    }
}

/// The listener id of a callback: the existing one for the same object
/// ("same callback"), else a new one.
fn listener_id(
    scope: &mut Scope<'_>,
    callback: Local<'_>,
    add: bool,
) -> Result<Option<ListenerId>> {
    let known: Vec<(u64, Handle)> = page(scope)?.callbacks.clone();
    for (id, h) in known {
        let v = scope.local(&h)?;
        if scope.strict_equals(v, callback) {
            return Ok(Some(ListenerId(id)));
        }
    }
    if !add {
        return Ok(None);
    }
    let handle = scope.persist(callback);
    let p = page(scope)?;
    let id = p.next_callback;
    p.next_callback = p.next_callback.saturating_add(1);
    p.callbacks.push((id, handle));
    Ok(Some(ListenerId(id)))
}

fn event_data<'a>(scope: &'a mut Scope<'_>, this: ObjectKey) -> Result<&'a mut EventData> {
    if !matches!(page(scope)?.object(this), Some(Object::Event(_))) {
        return Err(type_error(scope, "not an Event"));
    }
    match page(scope)?.object_mut(this) {
        Some(Object::Event(e)) => Ok(e),
        _ => Err(clazel_js::Error::WrongType("an Event")),
    }
}

fn event_of<'a>(scope: &'a mut Scope<'_>, this: ObjectKey) -> Result<&'a mut Event> {
    Ok(&mut event_data(scope, this)?.event)
}

fn now(scope: &mut Scope<'_>) -> Result<f64> {
    Ok(page(scope)?.hooks.now_ms())
}

/// What runs a listener: "inner invoke" (DOM §2.10†) steps 2.10 and 2.11,
/// "Call a user object's operation with listener's callback, "handleEvent",
/// « event », and event's currentTarget attribute value. If this throws an
/// exception exception: Report exception."
struct JsInvoke<'a, 's> {
    scope: &'a mut Scope<'s>,
    event: ObjectKey,
}

impl events::Host for JsInvoke<'_, '_> {
    fn invoke(&mut self, call: Invocation<'_>) {
        let scope = &mut *self.scope;
        // Put the event and the listener table back for the listener.
        let Ok(p) = page(scope) else { return };
        core::mem::swap(&mut p.listeners, call.listeners);
        if let Some(Object::Event(d)) = p.object_mut(self.event) {
            d.event = call.event.clone();
        }
        let callback = p
            .callbacks
            .iter()
            .find(|(id, _)| *id == call.listener.0)
            .map(|(_, h)| h.clone());
        let current = call.event.current_target().map(key_of_target);
        // An event handler (HTML §8.1.8†): "the event handler processing
        // algorithm", not a callback to `handleEvent`.
        if call.listener.0 >= HANDLER_ID_BASE {
            let cancel = handlers::run(scope, call.listener, self.event, current);
            if let Ok(p) = page(scope) {
                if let Ok(true) = cancel
                    && let Some(Object::Event(d)) = p.object_mut(self.event)
                {
                    d.event.prevent_default();
                }
                core::mem::swap(&mut p.listeners, call.listeners);
                if let Some(Object::Event(d)) = p.object_mut(self.event) {
                    *call.event = d.event.clone();
                }
            }
            return;
        }
        let result = (|| -> Result<()> {
            let Some(cb) = callback else { return Ok(()) };
            let f = scope.local(&cb)?;
            let ev = clazel_webidl::platform::wrap::<Page>(scope, self.event)?;
            let this = match current {
                Some(k) => clazel_webidl::platform::wrap::<Page>(scope, k)?,
                None => scope.undefined(),
            };
            convert::call_user_object_operation(scope, f, "handleEvent", this, &[ev])?;
            Ok(())
        })();
        if let Err(clazel_js::Error::Thrown(e)) = &result
            && let Ok(report) = scope.report(e)
        {
            let text = format!("Uncaught {}: {}", report.name, report.message);
            if let Ok(p) = page(scope) {
                p.record(HookCall::Log(LogLevel::Error, text));
            }
        }
        // And take them out again.
        let Ok(p) = page(scope) else { return };
        core::mem::swap(&mut p.listeners, call.listeners);
        if let Some(Object::Event(d)) = p.object_mut(self.event) {
            *call.event = d.event.clone();
        }
    }

    /// The document has a Window (DOM "get the parent" of a Document).
    fn has_window(&self, document: usize, _event: &Event) -> bool {
        document == 0
    }

    fn has_activation_behavior(&mut self, node: usize) -> bool {
        match page(self.scope) {
            Ok(p) => crate::activation::kind_of(&p.arena, node).is_some(),
            Err(_) => false,
        }
    }

    fn legacy_pre_activation_behavior(&mut self, node: usize) {
        if let Ok(p) = page(self.scope) {
            forms::legacy_pre_activation(p, node);
        }
    }

    fn legacy_canceled_activation_behavior(&mut self, node: usize) {
        if let Ok(p) = page(self.scope) {
            forms::legacy_canceled_activation(p, node);
        }
    }

    fn activation_behavior(&mut self, node: usize, event: &Event, listeners: &mut Listeners) {
        let target = match event.target() {
            Some(TargetId::Node(n)) => Some(n),
            _ => None,
        };
        let Ok(p) = page(self.scope) else { return };
        core::mem::swap(&mut p.listeners, listeners);
        let _ = forms::activation_behavior(self.scope, node, target);
        if let Ok(p) = page(self.scope) {
            core::mem::swap(&mut p.listeners, listeners);
        }
    }

    fn prepare_listeners(&mut self, target: TargetId, event_type: &[u32], listeners: &mut Listeners) {
        if let Ok(p) = page(self.scope) {
            handlers::prepare(&p.arena, &mut p.ui, listeners, target, event_type);
        }
    }
}

/// DOM §2.9† "dispatch" event to target, from script (`dispatchEvent`) or
/// the platform: the path is built first (the tree may change while
/// listeners run), then [`events::dispatch_path`] runs with the event and
/// the listener table out of the page. Returns false if the event was
/// canceled.
pub(crate) fn dispatch(scope: &mut Scope<'_>, target: TargetId, event: ObjectKey) -> Result<bool> {
    let p = page(scope)?;
    let ev = match p.object(event) {
        Some(Object::Event(d)) => d.event.clone(),
        _ => return Err(type_error(scope, "not an Event")),
    };
    let path = events::build_path(&p.arena, target, &ev, &|d, _| d == 0);
    let path = match path {
        Ok(path) => path,
        Err(_) => return Err(type_error(scope, "the target is not in the document")),
    };
    let mut ev = ev;
    let mut listeners = core::mem::take(&mut p.listeners);
    let not_canceled = {
        let mut host = JsInvoke { scope, event };
        events::dispatch_path(&path, &mut listeners, &mut ev, &mut host)
    };
    let p = page(scope)?;
    p.listeners = listeners;
    if let Some(Object::Event(d)) = p.object_mut(event) {
        d.event = ev;
    }
    Ok(not_canceled)
}

impl EventTargetImpl for Page {
    /// DOM §2.7† `addEventListener(type, callback, options)`: "1. Let
    /// capture, passive, once, and signal be the result of flattening more
    /// options. 2. Add an event listener with this and an event listener
    /// whose type is type, callback is callback, capture is capture,
    /// passive is passive, once is once, and signal is signal." "Add an
    /// event listener" step 3, "If listener's callback is null, then
    /// return", comes first here.
    fn add_event_listener<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        type_: DomString,
        callback: Option<Local<'s>>,
        options: AddEventListenerOptionsOrBoolean,
    ) -> Result<()> {
        let Some(callback) = callback else {
            return Ok(());
        };
        let (capture, passive, once, signal) = match options {
            AddEventListenerOptionsOrBoolean::Boolean(b) => (b, None, false, None),
            AddEventListenerOptionsOrBoolean::AddEventListenerOptions(o) => {
                (o.capture, o.passive, o.once, o.signal)
            }
        };
        let signal = match signal {
            Some(k) => match page(scope)?.object(k) {
                Some(Object::AbortSignal { signal, .. }) => Some(*signal),
                _ => return Err(type_error(scope, "signal is not an AbortSignal")),
            },
            None => None,
        };
        let Some(target) = target_of(page(scope)?, this) else {
            return Err(type_error(scope, "not an EventTarget"));
        };
        let Some(id) = listener_id(scope, callback, true)? else {
            return Ok(());
        };
        let p = page(scope)?;
        let mut listeners = core::mem::take(&mut p.listeners);
        listeners.add_event_listener(
            &p.arena,
            target,
            &units_to_points(&type_),
            id,
            AddOptions {
                capture,
                passive,
                once,
                signal,
            },
        );
        p.listeners = listeners;
        Ok(())
    }

    /// DOM §2.7† `removeEventListener(type, callback, options)`: "1. Let
    /// capture be the result of flattening options. 2. If this's event
    /// listener list contains an event listener whose type is type,
    /// callback is callback, and capture is capture, then remove an event
    /// listener with this and that event listener."
    fn remove_event_listener<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        type_: DomString,
        callback: Option<Local<'s>>,
        options: EventListenerOptionsOrBoolean,
    ) -> Result<()> {
        let Some(callback) = callback else {
            return Ok(());
        };
        let capture = match options {
            EventListenerOptionsOrBoolean::Boolean(b) => b,
            EventListenerOptionsOrBoolean::EventListenerOptions(o) => o.capture,
        };
        let Some(target) = target_of(page(scope)?, this) else {
            return Err(type_error(scope, "not an EventTarget"));
        };
        let Some(id) = listener_id(scope, callback, false)? else {
            return Ok(());
        };
        page(scope)?
            .listeners
            .remove_event_listener(target, &units_to_points(&type_), id, capture);
        Ok(())
    }

    /// DOM §2.7† `dispatchEvent(event)`: "1. If event's dispatch flag is
    /// set, or if its initialized flag is not set, then throw an
    /// InvalidStateError DOMException. 2. Initialize event's isTrusted
    /// attribute to false. 3. Return the result of dispatching event to
    /// this."
    fn dispatch_event<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        event: ObjectKey,
    ) -> Result<bool> {
        let Some(target) = target_of(page(scope)?, this) else {
            return Err(type_error(scope, "not an EventTarget"));
        };
        let ev = event_of(scope, event)?;
        if ev.is_dispatching() || !ev.is_initialized() {
            return Err(dom_error(
                scope,
                DomErrorName::InvalidStateError,
                "the event is being dispatched or was not initialized",
            ));
        }
        ev.set_untrusted();
        dispatch(scope, target, event)
    }

    /// DOM §2.7† `new EventTarget()`: "Set this's event listener list to
    /// the empty list."
    fn constructor<'s>(scope: &mut Scope<'s>) -> Result<ObjectKey> {
        Ok(page(scope)?.add_object(Object::EventTarget))
    }
}

fn new_event(
    scope: &mut Scope<'_>,
    interface: InterfaceId,
    type_: &[u16],
    init: Init,
    detail: Option<Handle>,
) -> Result<ObjectKey> {
    let t = now(scope)?;
    let event = Event::new(&units_to_points(type_), init, t);
    Ok(page(scope)?.add_object(Object::Event(Box::new(EventData {
        event,
        interface,
        detail,
    }))))
}

impl EventImpl for Page {
    fn type_<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        Ok(points_to_units(event_of(scope, this)?.type_()))
    }

    fn target<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        Ok(event_of(scope, this)?.target().map(key_of_target))
    }

    /// DOM §2.2† `srcElement`: "this's target" (legacy).
    fn src_element<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        Ok(event_of(scope, this)?.target().map(key_of_target))
    }

    fn current_target<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        Ok(event_of(scope, this)?.current_target().map(key_of_target))
    }

    fn event_phase<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u16> {
        Ok(event_of(scope, this)?.event_phase().code())
    }

    fn cancel_bubble<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(event_of(scope, this)?.cancel_bubble())
    }

    fn set_cancel_bubble<'s>(scope: &mut Scope<'s>, this: ObjectKey, value: bool) -> Result<()> {
        event_of(scope, this)?.set_cancel_bubble(value);
        Ok(())
    }

    fn bubbles<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(event_of(scope, this)?.bubbles())
    }

    fn cancelable<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(event_of(scope, this)?.cancelable())
    }

    fn return_value<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(event_of(scope, this)?.return_value())
    }

    fn set_return_value<'s>(scope: &mut Scope<'s>, this: ObjectKey, value: bool) -> Result<()> {
        event_of(scope, this)?.set_return_value(value);
        Ok(())
    }

    fn default_prevented<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(event_of(scope, this)?.default_prevented())
    }

    fn composed<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(event_of(scope, this)?.composed())
    }

    fn is_trusted<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(event_of(scope, this)?.is_trusted())
    }

    fn time_stamp<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<f64> {
        Ok(event_of(scope, this)?.time_stamp())
    }

    /// DOM §2.2† `composedPath()`: the path while dispatching, else empty
    /// (no shadow trees, so no step hides an item).
    fn composed_path<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Vec<ObjectKey>> {
        Ok(event_of(scope, this)?
            .composed_path()
            .iter()
            .map(|t| key_of_target(*t))
            .collect())
    }

    fn stop_propagation<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<()> {
        event_of(scope, this)?.stop_propagation();
        Ok(())
    }

    fn stop_immediate_propagation<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<()> {
        event_of(scope, this)?.stop_immediate_propagation();
        Ok(())
    }

    fn prevent_default<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<()> {
        event_of(scope, this)?.prevent_default();
        Ok(())
    }

    fn init_event<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        type_: DomString,
        bubbles: bool,
        cancelable: bool,
    ) -> Result<()> {
        event_of(scope, this)?.init_event(&units_to_points(&type_), bubbles, cancelable);
        Ok(())
    }

    /// DOM §2.2† `new Event(type, eventInitDict)`: "the result of running
    /// the inner event creation steps with this interface, null, now, and
    /// eventInitDict"; type is type.
    fn constructor<'s>(
        scope: &mut Scope<'s>,
        type_: DomString,
        init: EventInit,
    ) -> Result<ObjectKey> {
        new_event(
            scope,
            InterfaceId::Event,
            &type_,
            Init {
                bubbles: init.bubbles,
                cancelable: init.cancelable,
                composed: init.composed,
            },
            None,
        )
    }
}

impl CustomEventImpl for Page {
    /// DOM §2.4† `detail`: "the value it was initialized to".
    fn detail<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Local<'s>> {
        let d = event_data(scope, this)?.detail.clone();
        match d {
            Some(h) => scope.local(&h),
            None => Ok(scope.null()),
        }
    }

    /// DOM §2.4† `initCustomEvent(type, bubbles, cancelable, detail)`: "1. If
    /// this's dispatch flag is set, then return. 2. Initialize this with
    /// type, bubbles, and cancelable. 3. Set this's detail attribute to
    /// detail."
    fn init_custom_event<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        type_: DomString,
        bubbles: bool,
        cancelable: bool,
        detail: Local<'s>,
    ) -> Result<()> {
        if event_of(scope, this)?.is_dispatching() {
            return Ok(());
        }
        event_of(scope, this)?.init_event(&units_to_points(&type_), bubbles, cancelable);
        let h = scope.persist(detail);
        event_data(scope, this)?.detail = Some(h);
        Ok(())
    }

    /// DOM §2.4† `new CustomEvent(type, eventInitDict)`: an event whose
    /// `detail` is the dictionary's (default null).
    fn constructor<'s>(
        scope: &mut Scope<'s>,
        type_: DomString,
        init: CustomEventInit<'s>,
    ) -> Result<ObjectKey> {
        let detail = scope.persist(init.detail);
        new_event(
            scope,
            InterfaceId::CustomEvent,
            &type_,
            Init {
                bubbles: init.bubbles,
                cancelable: init.cancelable,
                composed: init.composed,
            },
            Some(detail),
        )
    }
}

fn signal_of(scope: &mut Scope<'_>, this: ObjectKey) -> Result<(SignalId, Option<Handle>)> {
    match page(scope)?.object(this) {
        Some(Object::AbortSignal { signal, reason }) => Ok((*signal, reason.clone())),
        _ => Err(type_error(scope, "not an AbortSignal")),
    }
}

fn new_signal(scope: &mut Scope<'_>) -> Result<ObjectKey> {
    let p = page(scope)?;
    let signal = p.listeners.new_signal();
    Ok(p.add_object(Object::AbortSignal {
        signal,
        reason: None,
    }))
}

/// DOM §3.2† "signal abort" on signal with reason: "1. If signal is aborted,
/// then return. 2. Set signal's abort reason to reason if it is given;
/// otherwise to a new "AbortError" DOMException. ... 5. Run the abort steps
/// (here: remove the listeners added with the signal). 6. Fire an event
/// named abort at signal."
fn signal_abort(scope: &mut Scope<'_>, key: ObjectKey, reason: Option<Local<'_>>) -> Result<()> {
    let (signal, _) = signal_of(scope, key)?;
    if page(scope)?.listeners.is_aborted(signal) {
        return Ok(());
    }
    let reason = match reason {
        Some(r) if scope.kind(r) != clazel_js::ValueKind::Undefined => r,
        _ => {
            let n = str_units("AbortError");
            let m = str_units("signal is aborted without reason");
            clazel_webidl::exception::create::<Page>(scope, &n, &m)?
        }
    };
    let handle = scope.persist(reason);
    if let Some(Object::AbortSignal { reason, .. }) = page(scope)?.object_mut(key) {
        *reason = Some(handle);
    }
    page(scope)?.listeners.abort(signal);
    let ev = new_event(
        scope,
        InterfaceId::Event,
        &str_units("abort"),
        Init::default(),
        None,
    )?;
    if let Some(Object::Event(d)) = page(scope)?.object_mut(ev) {
        d.event.set_trusted();
    }
    let Some(target) = target_of(page(scope)?, key) else {
        return Ok(());
    };
    dispatch(scope, target, ev)?;
    Ok(())
}

impl AbortSignalImpl for Page {
    /// DOM §3.2† `aborted`: "true if this is aborted; otherwise false".
    fn aborted<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        let (signal, _) = signal_of(scope, this)?;
        Ok(page(scope)?.listeners.is_aborted(signal))
    }

    /// DOM §3.2† `reason`: "this's abort reason".
    fn reason<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Local<'s>> {
        let (_, reason) = signal_of(scope, this)?;
        local_or_undefined(scope, reason.as_ref())
    }

    /// DOM §3.2† `AbortSignal.abort(reason)`: "1. Let signal be a new
    /// AbortSignal object. 2. Set signal's abort reason to reason if it is
    /// given; otherwise to a new "AbortError" DOMException. 3. Return
    /// signal."
    fn abort<'s>(scope: &mut Scope<'s>, reason: Option<Local<'s>>) -> Result<ObjectKey> {
        let k = new_signal(scope)?;
        signal_abort(scope, k, reason)?;
        Ok(k)
    }

    /// DOM §3.2† `throwIfAborted()`: "If this is aborted, then throw this's
    /// abort reason."
    fn throw_if_aborted<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<()> {
        let (signal, reason) = signal_of(scope, this)?;
        if !page(scope)?.listeners.is_aborted(signal) {
            return Ok(());
        }
        let r = local_or_undefined(scope, reason.as_ref())?;
        Err(scope.throw(r))
    }
}

impl AbortControllerImpl for Page {
    fn signal<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        match page(scope)?.object(this) {
            Some(Object::AbortController { signal }) => Ok(*signal),
            _ => Err(type_error(scope, "not an AbortController")),
        }
    }

    /// DOM §3.1† `abort(reason)`: "signal abort on this with reason if it is
    /// given".
    fn abort<'s>(scope: &mut Scope<'s>, this: ObjectKey, reason: Option<Local<'s>>) -> Result<()> {
        let signal = <Page as AbortControllerImpl>::signal(scope, this)?;
        signal_abort(scope, signal, reason)
    }

    /// DOM §3.1† `new AbortController()`: "1. Let signal be a new AbortSignal
    /// object. 2. Set this's signal to signal."
    fn constructor<'s>(scope: &mut Scope<'s>) -> Result<ObjectKey> {
        let signal = new_signal(scope)?;
        Ok(page(scope)?.add_object(Object::AbortController { signal }))
    }
}

/// DOM §2.10† "fire an event": a trusted `Event` named `name` at `target` with
/// the given `bubbles`, `cancelable` and `composed`, dispatched. Returns false
/// if a listener canceled it.
///
/// # Errors
/// What a listener's exception does not (it is reported); engine errors.
pub(crate) fn fire_with(
    scope: &mut Scope<'_>,
    target: TargetId,
    name: &str,
    init: Init,
) -> Result<bool> {
    let t = now(scope)?;
    let event = Event::new_trusted(&super::str_points(name), init, t);
    let key = page(scope)?.add_object(Object::Event(Box::new(EventData {
        event,
        interface: InterfaceId::Event,
        detail: None,
    })));
    dispatch(scope, target, key)
}

/// DOM §2.10† "fire an event" named `name` at `target`, as the platform does
/// (HTML's `DOMContentLoaded`, `load` and `readystatechange`): a trusted,
/// uncancelable `Event`, dispatched to the listeners `addEventListener` made.
/// Returns false if a listener canceled it.
///
/// # Errors
/// What a listener's exception does not (it is reported); engine errors.
pub(crate) fn fire_event(
    scope: &mut Scope<'_>,
    target: TargetId,
    name: &str,
    bubbles: bool,
) -> Result<bool> {
    let t = now(scope)?;
    let init = Init {
        bubbles,
        cancelable: false,
        composed: false,
    };
    let event = Event::new_trusted(&super::str_points(name), init, t);
    let key = page(scope)?.add_object(Object::Event(Box::new(EventData {
        event,
        interface: InterfaceId::Event,
        detail: None,
    })));
    let result = dispatch(scope, target, key);
    // The event object is not needed again (script may hold its wrapper, and
    // the wrapper's key then names nothing: fine for an event that is over).
    result
}
