//! Event handlers (HTML §8.1.8†): the `on*` IDL attributes and content
//! attributes of `Window`, `Document` and the elements.
//!
//! <https://html.spec.whatwg.org/multipage/webappapis.html#event-handlers>
//! (section numbers carry the mark † of phase-7.md: from memory, not read at
//! a pinned commit; steps are quoted by their words).
//!
//! Tier 0, not proven.
//!
//! What it does, as the standard says it:
//! - An event handler of a target has a value: null, a callback, or "an
//!   internal raw uncompiled handler" (the content attribute's text). It is
//!   "activated" by adding an event listener (type the event handler's name,
//!   capture false) the first time its value becomes non-null, and
//!   "deactivated" by removing it when the value becomes null. A handler's
//!   place among the target's listeners is therefore where it was first set.
//!   The listener's callback is "the event handler processing algorithm":
//!   [`run`].
//! - "Getting the current value of the event handler" compiles a raw handler
//!   (the content attribute's text as the body of a function with one
//!   parameter, `event`) the first time it is read, reports a syntax error as
//!   an exception and then has null as its value.
//! - The setter of an IDL attribute with null deactivates; with an object
//!   activates.
//! - The return value of a handler is processed ("If the return value is
//!   false, cancel the event").
//! - On a `body` (and `frameset`) element, the handlers named by the
//!   "Window-reflecting body element event handler set" are the `Window`'s.
//!
//! Modelling choices:
//! - **Content attributes are read, not observed.** There is no attribute
//!   change hook; the handler remembers the text of its content attribute as
//!   it last saw it ([`crate::ui::Handler`]'s `attr_seen`) and, whenever the
//!   handler is looked at (an IDL read or write, and just before dispatch
//!   takes a path item's listeners: [`prepare`]), a different text is "the
//!   attribute changed": a present attribute makes the raw handler (and
//!   activates it), an absent one makes the value null (and deactivates it).
//!   The observable behavior is the standard's for every change but one: an
//!   attribute changed and changed back between two looks is not seen. The
//!   parser-made attributes are taken once, in tree order, when the page
//!   starts ([`scan`]), so their listeners come before script's.
//! - **The compiled function's scope** is the global scope only. HTML §8.1.8.2†
//!   makes the scope chain the element, its form owner and the document (so
//!   `onclick="submit()"` can reach the form's members); the engine has no
//!   `with` or `Function()` yet, so a handler sees `this` (the element, the
//!   `currentTarget`), `event` and the globals. Listed in the README.
//! - **`onerror`** gets the one argument, the event: there is no `ErrorEvent`
//!   (the `error` events this page fires are plain events) and so no
//!   five-argument call or "return true cancels".
//! - **The compile** wraps the text so the engine's `ParseScript` is the
//!   only parser: the function is assigned to a global the compile removes
//!   again, and the text is also compiled alone inside a block (where a
//!   `}` that would close the wrapper early is a syntax error) so that text
//!   cannot end the function and run as a script. The standard parses the
//!   text as a FunctionBody by itself ("CreateDynamicFunction"), which the
//!   engine does not have.

use clazel_dom::exec::{Arena, ExecKind};
use clazel_dom::spec::Namespace;
use clazel_js::{Error, Key, Local, Result, Scope, Source};
use clazel_webidl::platform::ObjectKey;

use super::{HookCall, LogLevel, Object, Page, WINDOW, page, points_to_string, str_points};
use crate::events::{AddOptions, Listeners, ListenerId, TargetId};
use crate::ui::{HANDLER_ID_BASE, Handler, HandlerValue};

/// HTML §8.1.8.? "Window-reflecting body element event handler set": the
/// handlers of a `body` element that are the `Window`'s: `GlobalEventHandlers`'
/// `blur`, `error`, `focus`, `load`, `resize` and `scroll`, and every one of
/// `WindowEventHandlers`.
#[must_use]
pub fn is_window_reflecting(event: &str) -> bool {
    matches!(
        event,
        "blur"
            | "error"
            | "focus"
            | "load"
            | "resize"
            | "scroll"
            | "afterprint"
            | "beforeprint"
            | "beforeunload"
            | "hashchange"
            | "languagechange"
            | "message"
            | "messageerror"
            | "offline"
            | "online"
            | "pagehide"
            | "pagereveal"
            | "pageshow"
            | "pageswap"
            | "popstate"
            | "rejectionhandled"
            | "storage"
            | "unhandledrejection"
            | "unload"
    )
}

/// Whether `n` is an HTML `body` or `frameset` element.
fn is_body_or_frameset(arena: &Arena, n: usize) -> bool {
    n < arena.len()
        && matches!(
            arena.kind(n),
            ExecKind::Element {
                namespace: Some(Namespace::Html),
                local_name,
                ..
            } if local_name.iter().copied().eq("body".chars().map(u32::from))
                || local_name.iter().copied().eq("frameset".chars().map(u32::from))
        )
}

/// The document's `body` element: the first child of the document element
/// that is a `body` or `frameset` (HTML §3.1.4†).
fn body_element(arena: &Arena) -> Option<usize> {
    let html = *arena.children(0).iter().find(|&&c| {
        c < arena.len() && matches!(arena.kind(c), ExecKind::Element { .. })
    })?;
    arena
        .children(html)
        .iter()
        .copied()
        .find(|&c| is_body_or_frameset(arena, c))
}

/// The target a handler of `this` named `event` belongs to: the `Window`
/// for a `body` element's Window-reflecting handlers, else `this`.
fn handler_target(page: &Page, this: ObjectKey, event: &str) -> Option<TargetId> {
    if this == WINDOW {
        return Some(TargetId::Window);
    }
    if let Some(n) = page.key_node(this) {
        if is_body_or_frameset(&page.arena, n) && is_window_reflecting(event) {
            return Some(TargetId::Window);
        }
        return Some(TargetId::Node(n));
    }
    match page.object(this)? {
        Object::EventTarget | Object::AbortSignal { .. } => {
            Page::object_id(this).map(TargetId::Object)
        }
        _ => None,
    }
}

/// The text of the content attribute `on<event>` that gives the handler of
/// `target` its value: on an element its own, on the `Window` the `body`'s
/// (for the Window-reflecting set).
fn content_attribute(arena: &Arena, target: TargetId, event: &str) -> Option<Vec<u32>> {
    let name = format!("on{event}");
    let element = match target {
        TargetId::Node(n) => n,
        TargetId::Window if is_window_reflecting(event) => body_element(arena)?,
        _ => return None,
    };
    if element >= arena.len() {
        return None;
    }
    // A body's Window-reflecting attributes are the Window's, not its own.
    if matches!(target, TargetId::Node(_))
        && is_body_or_frameset(arena, element)
        && is_window_reflecting(event)
    {
        return None;
    }
    crate::activation::attribute(arena, element, &name)
}

/// HTML §8.1.8.1† "activate an event handler": "If eventTarget's event
/// listener list does not contain an event listener whose type is name and
/// callback is the event handler's listener, then add an event listener".
fn activate(arena: &Arena, listeners: &mut Listeners, target: TargetId, event: &str, h: &mut Handler) {
    if h.active {
        return;
    }
    listeners.add_event_listener(
        arena,
        target,
        &str_points(event),
        h.listener,
        AddOptions::default(),
    );
    h.active = true;
}

/// HTML §8.1.8.1† "deactivate an event handler": remove the listener.
fn deactivate(listeners: &mut Listeners, target: TargetId, event: &str, h: &mut Handler) {
    if !h.active {
        return;
    }
    listeners.remove_event_listener(target, &str_points(event), h.listener, false);
    h.active = false;
}

/// Brings the handler of `target` named `event` up to date with its content
/// attribute (see the module's modelling choices), registering or removing
/// its listener in `listeners`. Makes no entry for a handler that has no
/// content attribute and was never set.
fn sync(
    arena: &Arena,
    ui: &mut crate::ui::Ui,
    listeners: &mut Listeners,
    target: TargetId,
    event: &str,
) {
    let attr = content_attribute(arena, target, event);
    let key = (target, event.to_owned());
    if attr.is_none() && !ui.handlers.contains_key(&key) {
        return;
    }
    let next = ui.next_handler;
    let entry = ui.handlers.entry(key).or_insert_with(|| Handler {
        value: HandlerValue::Null,
        listener: ListenerId(HANDLER_ID_BASE.saturating_add(next)),
        active: false,
        attr_seen: None,
    });
    if entry.listener.0 == HANDLER_ID_BASE.saturating_add(next) {
        ui.next_handler = next.saturating_add(1);
    }
    if entry.attr_seen == attr {
        return;
    }
    entry.attr_seen = attr.clone();
    match attr {
        // "Set the event handler's value to the internal raw uncompiled
        // handler" and activate.
        Some(text) => {
            entry.value = HandlerValue::Raw(text);
            activate(arena, listeners, target, event, entry);
        }
        // "Otherwise ... set the event handler's value to null" and
        // deactivate.
        None => {
            entry.value = HandlerValue::Null;
            deactivate(listeners, target, event, entry);
        }
    }
}

/// What the page does just before dispatch takes the listeners of a path
/// item of an event of type `type_`: [`sync`] the handler of that type.
pub(crate) fn prepare(
    arena: &Arena,
    ui: &mut crate::ui::Ui,
    listeners: &mut Listeners,
    target: TargetId,
    type_: &[u32],
) {
    let event = points_to_string(type_);
    sync(arena, ui, listeners, target, &event);
}

/// The initial pass over the document: every parser-made `on*` content
/// attribute becomes a handler, in tree order, with the listener it
/// activates (HTML: "The attribute change steps ... when the parser creates
/// the element"). Elements that scripts make later are taken by [`prepare`].
pub(crate) fn scan(page: &mut Page) {
    let Page {
        arena,
        ui,
        listeners,
        ..
    } = page;
    let mut found: Vec<(TargetId, String)> = Vec::new();
    for n in crate::activation::tree_order(arena) {
        let ExecKind::Element { attributes, .. } = arena.kind(n) else {
            continue;
        };
        for a in attributes {
            if a.namespace.is_some() {
                continue;
            }
            let name = points_to_string(&a.local_name);
            let Some(event) = name.strip_prefix("on") else {
                continue;
            };
            if event.is_empty() {
                continue;
            }
            let target = if is_body_or_frameset(arena, n) && is_window_reflecting(event) {
                TargetId::Window
            } else {
                TargetId::Node(n)
            };
            found.push((target, event.to_owned()));
        }
    }
    for (target, event) in found {
        sync(arena, ui, listeners, target, &event);
    }
}

/// The IDL attribute's getter (`element.onclick`): "the result of getting
/// the current value of the event handler".
///
/// # Errors
/// What the engine throws.
pub(crate) fn get<'s>(
    scope: &mut Scope<'s>,
    this: ObjectKey,
    event: &str,
) -> Result<Option<Local<'s>>> {
    let p = page(scope)?;
    let Some(target) = handler_target(p, this, event) else {
        return Err(super::type_error(scope, "not an event target"));
    };
    {
        let p = page(scope)?;
        let Page {
            arena,
            ui,
            listeners,
            ..
        } = p;
        sync(arena, ui, listeners, target, event);
    }
    current_value(scope, target, event)
}

/// The IDL attribute's setter: null deactivates the handler, an object
/// makes it the value and activates it.
///
/// # Errors
/// What the engine throws.
pub(crate) fn set<'s>(
    scope: &mut Scope<'s>,
    this: ObjectKey,
    event: &str,
    value: Option<Local<'s>>,
) -> Result<()> {
    let p = page(scope)?;
    let Some(target) = handler_target(p, this, event) else {
        return Err(super::type_error(scope, "not an event target"));
    };
    // The handle first: the table borrows the page.
    let handle = value.map(|v| scope.persist(v));
    let p = page(scope)?;
    let Page {
        arena,
        ui,
        listeners,
        ..
    } = p;
    // The attribute's current text counts as seen, so that a set after it
    // is not undone by it (the attribute change is before this set).
    sync(arena, ui, listeners, target, event);
    let key = (target, event.to_owned());
    let next = ui.next_handler;
    let entry = ui.handlers.entry(key).or_insert_with(|| Handler {
        value: HandlerValue::Null,
        listener: ListenerId(HANDLER_ID_BASE.saturating_add(next)),
        active: false,
        attr_seen: None,
    });
    if entry.listener.0 == HANDLER_ID_BASE.saturating_add(next) {
        ui.next_handler = next.saturating_add(1);
    }
    match handle {
        Some(h) => {
            entry.value = HandlerValue::Callback(h);
            activate(arena, listeners, target, event, entry);
        }
        None => {
            entry.value = HandlerValue::Null;
            deactivate(listeners, target, event, entry);
        }
    }
    Ok(())
}

/// The key of the handler a listener id is the listener of.
fn handler_of(page: &Page, listener: ListenerId) -> Option<(TargetId, String)> {
    page.ui
        .handlers
        .iter()
        .find(|(_, h)| h.listener == listener)
        .map(|(k, _)| k.clone())
}

/// HTML §8.1.8.2† "getting the current value of the event handler": null
/// for null; the callback for a callback; for a raw handler, "if eventTarget
/// is an element, ... let body be the uncompiled handler's body; ... if body
/// is not parsable as FunctionBody ... report the exception, set the
/// event handler's value to null and return null", else the function.
fn current_value<'s>(
    scope: &mut Scope<'s>,
    target: TargetId,
    event: &str,
) -> Result<Option<Local<'s>>> {
    let key = (target, event.to_owned());
    let value = page(scope)?.ui.handlers.get(&key).map(|h| h.value.clone());
    match value {
        None | Some(HandlerValue::Null) => Ok(None),
        Some(HandlerValue::Callback(h)) => Ok(Some(scope.local(&h)?)),
        Some(HandlerValue::Raw(text)) => {
            let compiled = compile(scope, &text);
            let new_value = match &compiled {
                Ok(Some(f)) => HandlerValue::Callback(scope.persist(*f)),
                _ => HandlerValue::Null,
            };
            if let Some(h) = page(scope)?.ui.handlers.get_mut(&key) {
                h.value = new_value;
            }
            match compiled {
                Ok(f) => Ok(f),
                Err(Error::Thrown(e)) => {
                    report(scope, &e);
                    Ok(None)
                }
                Err(other) => Err(other),
            }
        }
    }
}

/// The name of the global the compile assigns the function to.
const SINK: &str = "__clazel_event_handler__";

/// HTML §8.1.8.2† step "Let function be the result of ... a new function
/// whose body is body and whose parameter is `event`" (see the module's
/// modelling choices for how). `Ok(None)` cannot happen; a syntax error is
/// `Err(Thrown)`.
fn compile<'s>(scope: &mut Scope<'s>, text: &[u32]) -> Result<Option<Local<'s>>> {
    let body = points_to_string(text);
    let realm = scope.current_realm()?;
    // The body alone, in a block inside a function: a `}` that would end the
    // wrapper below early does not balance here.
    let check = format!("function {SINK}check(event) {{ {{\n{body}\n}} }}");
    scope.compile_script(&realm, Source::new("event handler", &check))?;
    let wrapped = format!("{SINK} = function(event) {{\n{body}\n}};");
    let script = scope.compile_script(&realm, Source::new("event handler", &wrapped))?;
    scope.run_script(&script)?;
    let global = scope.global(&realm)?;
    let f = scope.get(global, Key::Str(SINK))?;
    scope.delete_property(global, Key::Str(SINK))?;
    Ok(Some(f))
}

/// "Report the exception": the page's log, as an uncaught listener error is.
fn report(scope: &mut Scope<'_>, e: &clazel_js::Exception) {
    if let Ok(r) = scope.report(e) {
        let text = format!("Uncaught {}: {}", r.name, r.message);
        if let Ok(p) = page(scope) {
            p.record(HookCall::Log(LogLevel::Error, text));
        }
    }
}

/// HTML §8.1.8.2† "the event handler processing algorithm" for an event
/// handler whose listener is `listener`, called by dispatch with the event
/// object `event` and the `currentTarget` `current`: "Let callback be the
/// result of getting the current value of the event handler", "If callback
/// is null, then return", call it with the event as its one argument and
/// `currentTarget` as `this` ("If this throws an exception, then: report the
/// exception"), and process the return value: "If the event is not an
/// `error` event: if return value is a Boolean with the value false, then
/// cancel the event". Returns whether the event is to be canceled.
///
/// # Errors
/// What the engine throws that is not an exception (termination).
pub(crate) fn run(
    scope: &mut Scope<'_>,
    listener: ListenerId,
    event: ObjectKey,
    current: Option<ObjectKey>,
) -> Result<bool> {
    let Some((target, name)) = handler_of(page(scope)?, listener) else {
        return Ok(false);
    };
    let Some(callback) = current_value(scope, target, &name)? else {
        return Ok(false);
    };
    if !scope.is_callable(callback) {
        // "Invoke": "If IsCallable(F) is false ... return".
        return Ok(false);
    }
    let ev = clazel_webidl::platform::wrap::<Page>(scope, event)?;
    let this = match (target, current) {
        (TargetId::Window, _) => clazel_webidl::platform::wrap::<Page>(scope, WINDOW)?,
        (_, Some(k)) => clazel_webidl::platform::wrap::<Page>(scope, k)?,
        _ => scope.undefined(),
    };
    match scope.call(callback, this, &[ev]) {
        Ok(r) => Ok(scope.as_boolean(r) == Some(false)),
        Err(Error::Thrown(e)) => {
            report(scope, &e);
            Ok(false)
        }
        Err(other) => Err(other),
    }
}
