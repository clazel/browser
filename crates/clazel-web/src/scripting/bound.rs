//! A page with its platform (phase-7.md items 7.12, 7.15 and 7.17): the
//! parsed document handed over by the renderer, its scripts run through
//! HTML's script processing ([`super`]), over the generated WebIDL bindings
//! ([`crate::page`]), with the event loop (HTML §8.1.7†) that gives scripts
//! their timers, tasks and microtasks.
//!
//! What this adds to the bindings, as natives installed on the realm after
//! them (the generated traits have not got these members yet): the HTML
//! members of `Window` (`setTimeout`, `setInterval`, `clearTimeout`,
//! `clearInterval`, `queueMicrotask`, `requestAnimationFrame`,
//! `cancelAnimationFrame`), `performance.now()`, `localStorage`, and the
//! members of `Document` that HTML adds (`write`, `writeln`, `open`, `close`,
//! `cookie`, `readyState`, `currentScript`).
//!
//! Modelling choices (each listed):
//! - **The document is parsed before its scripts run.** The renderer parses
//!   the whole response with the scripting flag on, and then
//!   [`Page::for_document`] reaches the `script` elements in tree order as
//!   the parser would, with the same processing model (`async`, `defer`,
//!   `nomodule`, parser-blocking scripts, modules, `document.currentScript`,
//!   the end). A script sees the whole tree and not the part built so far;
//!   `document.write` is reported and does nothing (`parser::walk` says
//!   why). `Page::new` is the incremental alternative, with no bindings.
//! - **Scripts that scripts insert do not run**: "prepare the script
//!   element" is not run when a script element is inserted into the tree,
//!   because the DOM's insertion steps (item 7.13) are not wired to it yet.
//! - **Time is the page's clock.** The event loop takes the time from the
//!   embedder's [`Clock`](super::time::Clock) in whole milliseconds; the
//!   embedder asks for the next time anything is due
//!   ([`Page::next_wake_ms`]) and runs the loop when that time comes
//!   ([`Page::run_event_loop`]).
//! - **Rendering.** `requestAnimationFrame` callbacks run in
//!   [`Page::update_the_rendering`], which the embedder calls when it is
//!   about to paint; style and layout are the embedder's.
//! - **One checkpoint.** The microtask checkpoint runs the engine's jobs
//!   (promise jobs) and then the loop's microtasks (`queueMicrotask`) until
//!   there are none of either.
//! - **Handlers are strings or functions.** A string handler is compiled
//!   and run as a classic script when its timer fires.
//! - **Events** the page fires ([`FiredEvent`]) are dispatched to the
//!   listeners the bindings keep (`addEventListener`), in order, after the
//!   step that fired them; `on*` handler attributes are not implemented.

use clazel_dom::exec::Arena;
use clazel_encoding::labels::spec::Encoding;
use clazel_js::{
    Args, Callable, Config, Error, ErrorKind, Handle, Key, Limits, Local, PropertyDescriptor,
    Realm, RealmOptions, Result, Runtime, Scope, Source,
};
use clazel_webidl::generated::bindings::InterfaceId;

use super::dom;
use super::element::report;
use super::state::{Doc, EventTarget, PageState, Walk, state};
use super::time::{Clock, performance_now_ms};
use super::{Page, Readiness};
use crate::event_loop::{CallbackId, EventLoop, Host as LoopHostTrait, TimerCall};
use crate::events::TargetId;
use crate::page::{self, PageHooks};

/// What a timer, task, microtask or animation frame runs.
#[derive(Clone)]
pub(crate) enum Callback {
    /// A function and the arguments after the delay (`setTimeout`'s).
    Function {
        /// The function.
        function: Handle,
        /// Its arguments.
        args: Vec<Handle>,
    },
    /// A string handler: a classic script, compiled when it runs.
    Code(String),
}

/// How a document-with-bindings page is made ([`Page::for_document`]).
pub struct DocumentOptions {
    /// The document's URL, serialized.
    pub url: String,
    /// The encoding the document was decoded with.
    pub encoding: Encoding,
    /// The engine's limits.
    pub limits: Limits,
    /// The monotonic clock `performance.now()` and the event loop read.
    pub clock: Box<dyn Clock>,
    /// What the page asks of the renderer: navigation, history, `console`,
    /// cookies and storage.
    pub hooks: Box<dyn PageHooks>,
}

/// The most iterations of the loop one call of [`Page::run_event_loop`]
/// runs: a page that keeps queueing tasks at the same instant cannot hold
/// the renderer.
const MAX_ITERATIONS: usize = 100_000;

impl Page {
    /// A page for a document the renderer has parsed (with the scripting
    /// flag on): the bindings, `console`, the timers and the rest are
    /// installed, and nothing runs until [`Page::run`].
    ///
    /// # Errors
    /// What `clazel-js` returns.
    pub fn for_document(options: DocumentOptions, arena: Arena) -> Result<Page> {
        let DocumentOptions {
            url,
            encoding,
            limits,
            mut clock,
            hooks,
        } = options;
        let order = script_elements(&arena);
        let time_origin_us = clock.now_us();
        let mut st = PageState::new(Doc::Done, encoding, false, clock, time_origin_us);
        st.bound = true;
        st.walk = Some(Walk { order, next: 0 });
        let mut host = page::Page::new(arena, &url, hooks);
        host.script = Some(Box::new(st));
        let mut rt = Runtime::new(Config::new(limits), host)?;
        let realm = rt.scope(|scope| -> Result<Realm> {
            let realm = scope.create_realm(RealmOptions::default())?;
            state(scope)?.realm = Some(realm.clone());
            clazel_webidl::generated::bindings::install::<page::Page>(scope, &realm)?;
            page::console::install(scope, &realm)?;
            install(scope, &realm)?;
            Ok(realm)
        })?;
        Ok(Page { rt, realm })
    }

    /// The page clock's reading, in whole milliseconds.
    ///
    /// # Errors
    /// What `clazel-js` returns.
    pub fn now_ms(&mut self) -> Result<u64> {
        self.rt.scope(now_ms)
    }

    /// Runs the event loop at the page clock's time until no task or
    /// microtask is queued and no timer is due. Returns the iterations run.
    ///
    /// # Errors
    /// An error that stops the page (termination, out of memory).
    pub fn run_event_loop(&mut self) -> Result<usize> {
        let (now, mut lp) = self.rt.scope(|scope| {
            let now = now_ms(scope)?;
            Ok((now, core::mem::take(&mut state(scope)?.event_loop)))
        })?;
        let mut host = LoopHost {
            rt: &mut self.rt,
            error: None,
        };
        let n = lp.run_until_idle(&mut host, now, MAX_ITERATIONS);
        let error = host.error.take();
        self.rt.scope(|scope| {
            state(scope)?.event_loop = lp;
            Ok(())
        })?;
        if let Some(e) = error {
            return Err(e);
        }
        self.rt.scope(flush_events)?;
        Ok(n)
    }

    /// The page clock's time, in milliseconds, at which a timer is next due,
    /// or `None` if no timer is waiting. A task or microtask already queued
    /// is due now.
    ///
    /// # Errors
    /// What `clazel-js` returns.
    pub fn next_wake_ms(&mut self) -> Result<Option<u64>> {
        self.rt
            .scope(|scope| Ok(state(scope)?.event_loop.next_wake()))
    }

    /// HTML §8.1.7† "update the rendering", the part scripts see: the
    /// `requestAnimationFrame` callbacks registered so far run, each with
    /// the time. Returns whether any ran.
    ///
    /// # Errors
    /// An error that stops the page.
    pub fn update_the_rendering(&mut self) -> Result<bool> {
        self.rt.scope(|scope| {
            let list = core::mem::take(&mut state(scope)?.animation_callbacks);
            if list.is_empty() {
                return Ok(false);
            }
            let stamp = performance_ms(scope)?;
            for (_, id) in list {
                let st = state(scope)?;
                let Some(cb) = st.callbacks.remove(&id) else {
                    continue;
                };
                run_callback(scope, cb, Some(stamp))?;
            }
            flush_events(scope)?;
            Ok(true)
        })
    }

    /// Whether a `requestAnimationFrame` callback is waiting for the next
    /// rendering update.
    ///
    /// # Errors
    /// What `clazel-js` returns.
    pub fn wants_animation_frame(&mut self) -> Result<bool> {
        self.rt
            .scope(|scope| Ok(!state(scope)?.animation_callbacks.is_empty()))
    }
}

/// The script elements of `arena`, in tree order.
fn script_elements(arena: &Arena) -> Vec<usize> {
    let mut out = Vec::new();
    let mut stack: Vec<usize> = vec![0];
    // Each node is pushed once: a tree has at most `len` of them.
    let mut budget = arena.len().saturating_mul(2).saturating_add(1);
    while let Some(id) = stack.pop() {
        if budget == 0 {
            break;
        }
        budget = budget.saturating_sub(1);
        if !dom::exists(arena, id) {
            continue;
        }
        if dom::html_element(arena, id, "script").is_some() {
            out.push(id);
        }
        stack.extend(arena.children(id).iter().rev());
    }
    out
}

/// The page clock, in whole milliseconds.
fn now_ms(scope: &mut Scope<'_>) -> Result<u64> {
    let st = state(scope)?;
    Ok(st.clock.now_us().checked_div(1000).unwrap_or(0))
}

/// `performance.now()`'s value.
fn performance_ms(scope: &mut Scope<'_>) -> Result<f64> {
    let st = state(scope)?;
    let now = st.clock.now_us();
    Ok(performance_now_ms(st.time_origin_us, now))
}

// ---- The loop's host --------------------------------------------------------

/// Swaps the page's loop with the one the loop's processing model is
/// running (`run_until_idle` has it out of the page), for the length of `f`:
/// natives that `f` runs queue into the real loop.
fn with_loop<R>(
    scope: &mut Scope<'_>,
    running: &mut EventLoop,
    f: impl FnOnce(&mut Scope<'_>) -> Result<R>,
) -> Result<R> {
    core::mem::swap(running, &mut state(scope)?.event_loop);
    let r = f(scope);
    if let Ok(st) = state(scope) {
        core::mem::swap(running, &mut st.event_loop);
    }
    r
}

/// The event loop's host for [`Page::run_event_loop`]: runs the callbacks
/// the page registered.
struct LoopHost<'r> {
    rt: &'r mut Runtime,
    error: Option<Error>,
}

impl LoopHost<'_> {
    fn run(&mut self, el: &mut EventLoop, callback: CallbackId, timer: Option<TimerCall>) {
        if self.error.is_some() {
            return;
        }
        let r = self.rt.scope(|scope| {
            with_loop(scope, el, |scope| {
                run_registered(scope, callback.0, timer.is_none_or(|t| !t.repeat))?;
                if let Some(t) = timer
                    && !t.repeat
                {
                    state(scope)?.timer_callbacks.remove(&t.id.get());
                }
                Ok(())
            })
        });
        if let Err(e) = r {
            self.error = Some(e);
        }
    }
}

impl LoopHostTrait for LoopHost<'_> {
    fn run_task(&mut self, event_loop: &mut EventLoop, callback: CallbackId) {
        self.run(event_loop, callback, None);
    }

    fn run_microtask(&mut self, event_loop: &mut EventLoop, callback: CallbackId) {
        self.run(event_loop, callback, None);
    }

    fn run_timer(&mut self, event_loop: &mut EventLoop, call: TimerCall) {
        self.run(event_loop, call.handler, Some(call));
    }
}

/// The host of a checkpoint that a script's end starts, inside a scope.
struct MicroHost<'a, 's> {
    scope: &'a mut Scope<'s>,
    error: Option<Error>,
}

impl LoopHostTrait for MicroHost<'_, '_> {
    fn run_task(&mut self, _event_loop: &mut EventLoop, _callback: CallbackId) {}

    fn run_microtask(&mut self, event_loop: &mut EventLoop, callback: CallbackId) {
        if self.error.is_some() {
            return;
        }
        let r = with_loop(self.scope, event_loop, |scope| {
            run_registered(scope, callback.0, true)
        });
        if let Err(e) = r {
            self.error = Some(e);
        }
    }

    fn run_timer(&mut self, _event_loop: &mut EventLoop, _call: TimerCall) {}
}

/// Runs the callback registered as `id`; `once` drops it first.
fn run_registered(scope: &mut Scope<'_>, id: u64, once: bool) -> Result<()> {
    let st = state(scope)?;
    let cb = if once {
        st.callbacks.remove(&id)
    } else {
        st.callbacks.get(&id).cloned()
    };
    match cb {
        Some(cb) => run_callback(scope, cb, None),
        None => Ok(()),
    }
}

/// HTML §8.1.4.? "invoke a callback" as the timers and animation frames do:
/// call it (a string handler runs as a script), report what it throws, and
/// "clean up after running a callback": a microtask checkpoint.
fn run_callback(scope: &mut Scope<'_>, cb: Callback, extra: Option<f64>) -> Result<()> {
    state(scope)?.running = state(scope)?.running.saturating_add(1);
    let status = (|| -> Result<()> {
        match &cb {
            Callback::Function { function, args } => {
                let f = scope.local(function)?;
                let realm = super::state::realm(scope)?;
                let this = scope.global(&realm)?;
                let mut argv: Vec<Local<'_>> = Vec::new();
                if let Some(t) = extra {
                    argv.push(scope.number(t));
                }
                for a in args {
                    argv.push(scope.local(a)?);
                }
                scope.call(f, this, &argv).map(|_| ())
            }
            Callback::Code(source) => {
                let realm = super::state::realm(scope)?;
                scope
                    .eval_script(&realm, Source::new("a timer's handler", source))
                    .map(|_| ())
            }
        }
    })();
    let st = state(scope)?;
    st.running = st.running.saturating_sub(1);
    match status {
        Ok(()) => {}
        Err(e @ (Error::Terminated | Error::OutOfMemory)) => return Err(e),
        Err(e) => report(scope, "", e)?,
    }
    super::element::clean_up_after_running_script(scope)
}

/// HTML §8.1.4.? "perform a microtask checkpoint": the engine's jobs, then
/// the loop's microtasks, until there are none of either. The page's
/// `running` count must be zero (the caller checks).
pub(crate) fn microtask_checkpoint(scope: &mut Scope<'_>) -> Result<()> {
    for _ in 0..1_000_000u32 {
        loop {
            match scope.run_jobs() {
                Ok(_) => break,
                Err(e @ (Error::Terminated | Error::OutOfMemory)) => return Err(e),
                Err(e) => report(scope, "", e)?,
            }
        }
        let st = state(scope)?;
        if st.event_loop.microtask_count() == 0 || st.event_loop.performing_microtask_checkpoint() {
            return Ok(());
        }
        let mut lp = core::mem::take(&mut st.event_loop);
        let mut host = MicroHost {
            scope: &mut *scope,
            error: None,
        };
        lp.perform_microtask_checkpoint(&mut host);
        let error = host.error.take();
        state(scope)?.event_loop = lp;
        if let Some(e) = error {
            return Err(e);
        }
    }
    Ok(())
}

// ---- Events -----------------------------------------------------------------

/// Dispatches the events the page fired since the last call, in order, to
/// the listeners the bindings keep (DOM §2.9† "dispatch"), each followed by
/// a microtask checkpoint. Does nothing for a page without bindings.
pub(crate) fn flush_events(scope: &mut Scope<'_>) -> Result<()> {
    let st = state(scope)?;
    if !st.bound || st.flushing {
        return Ok(());
    }
    st.flushing = true;
    let r = (|| -> Result<()> {
        loop {
            let st = state(scope)?;
            let Some(ev) = st.events.get(st.dispatched).cloned() else {
                return Ok(());
            };
            st.dispatched = st.dispatched.saturating_add(1);
            st.running = st.running.saturating_add(1);
            let target = match ev.target {
                EventTarget::Window => TargetId::Window,
                EventTarget::Document => TargetId::Node(0),
                EventTarget::Element(n) => TargetId::Node(n),
            };
            // DOMContentLoaded is the one of these that bubbles.
            let bubbles = ev.name == "DOMContentLoaded";
            let fired = page::event::fire_event(scope, target, ev.name, bubbles);
            let st = state(scope)?;
            st.running = st.running.saturating_sub(1);
            match fired {
                Ok(_) => {}
                Err(e @ (Error::Terminated | Error::OutOfMemory)) => return Err(e),
                Err(_) => {}
            }
            super::element::clean_up_after_running_script(scope)?;
        }
    })();
    if let Ok(st) = state(scope) {
        st.flushing = false;
    }
    r
}

// ---- The natives ------------------------------------------------------------

/// A `long` argument, ECMA-262 ToInt32.
fn to_int32(scope: &mut Scope<'_>, v: Local<'_>) -> Result<i32> {
    let n = scope.to_number(v)?;
    if !n.is_finite() {
        return Ok(0);
    }
    // Modulo 2^32, then the same bits as a signed value.
    let m = n.trunc().rem_euclid(4_294_967_296.0) as u64;
    let m = u32::try_from(m).unwrap_or(0);
    Ok(i32::from_ne_bytes(m.to_ne_bytes()))
}

/// The callback a `TimerHandler` argument makes.
fn timer_callback(scope: &mut Scope<'_>, args: &Args<'_>) -> Result<Callback> {
    let handler = args.get(0);
    if scope.is_callable(handler) {
        let function = scope.persist(handler);
        let mut rest = Vec::new();
        for i in 2..args.len() {
            let a = args.get(i);
            rest.push(scope.persist(a));
        }
        Ok(Callback::Function {
            function,
            args: rest,
        })
    } else {
        let s = scope.to_string(handler)?;
        Ok(Callback::Code(scope.string_to_string_lossy(s)?))
    }
}

/// `setTimeout` and `setInterval` (HTML §8.6†): "timer initialization
/// steps", returning the id.
fn set_timer(scope: &mut Scope<'_>, args: &Args<'_>, repeat: bool) -> Result<f64> {
    let cb = timer_callback(scope, args)?;
    let timeout = if args.len() > 1 {
        to_int32(scope, args.get(1))?
    } else {
        0
    };
    let now = now_ms(scope)?;
    let st = state(scope)?;
    let cid = st.next_callback;
    st.next_callback = st.next_callback.saturating_add(1);
    st.callbacks.insert(cid, cb);
    match st
        .event_loop
        .set_timer(CallbackId(cid), timeout, repeat, now)
    {
        Ok(id) => {
            st.timer_callbacks.insert(id.get(), cid);
            Ok(f64::from(id.get()))
        }
        Err(e) => {
            st.callbacks.remove(&cid);
            Err(scope.throw_error(ErrorKind::RangeError, &e.to_string()))
        }
    }
}

/// `clearTimeout` and `clearInterval`.
fn clear_timer(scope: &mut Scope<'_>, args: &Args<'_>) -> Result<()> {
    let id = if args.is_empty() {
        0
    } else {
        to_int32(scope, args.get(0))?
    };
    let st = state(scope)?;
    st.event_loop.clear_timer(id);
    if let Ok(id) = u32::try_from(id)
        && let Some(cid) = st.timer_callbacks.remove(&id)
    {
        st.callbacks.remove(&cid);
    }
    Ok(())
}

/// Installs what [`Page::for_document`] adds to the bindings (module docs).
fn install(scope: &mut Scope<'_>, realm: &Realm) -> Result<()> {
    let global = scope.global(realm)?;

    // Window: timers, microtasks, animation frames.
    scope.define_method(global, "setTimeout", 1, |scope, args| {
        let id = set_timer(scope, args, false)?;
        Ok(scope.number(id))
    })?;
    scope.define_method(global, "setInterval", 1, |scope, args| {
        let id = set_timer(scope, args, true)?;
        Ok(scope.number(id))
    })?;
    scope.define_method(global, "clearTimeout", 0, |scope, args| {
        clear_timer(scope, args)?;
        Ok(scope.undefined())
    })?;
    scope.define_method(global, "clearInterval", 0, |scope, args| {
        clear_timer(scope, args)?;
        Ok(scope.undefined())
    })?;
    scope.define_method(global, "queueMicrotask", 1, |scope, args| {
        let callback = args.get(0);
        if !scope.is_callable(callback) {
            return Err(scope.throw_error(
                ErrorKind::TypeError,
                "queueMicrotask's argument is not a function",
            ));
        }
        let function = scope.persist(callback);
        let st = state(scope)?;
        let cid = st.next_callback;
        st.next_callback = st.next_callback.saturating_add(1);
        st.callbacks.insert(
            cid,
            Callback::Function {
                function,
                args: Vec::new(),
            },
        );
        if let Err(e) = st.event_loop.queue_microtask(CallbackId(cid)) {
            st.callbacks.remove(&cid);
            return Err(scope.throw_error(ErrorKind::RangeError, &e.to_string()));
        }
        Ok(scope.undefined())
    })?;
    scope.define_method(global, "requestAnimationFrame", 1, |scope, args| {
        let callback = args.get(0);
        if !scope.is_callable(callback) {
            return Err(scope.throw_error(
                ErrorKind::TypeError,
                "requestAnimationFrame's argument is not a function",
            ));
        }
        let function = scope.persist(callback);
        let st = state(scope)?;
        let cid = st.next_callback;
        st.next_callback = st.next_callback.saturating_add(1);
        st.callbacks.insert(
            cid,
            Callback::Function {
                function,
                args: Vec::new(),
            },
        );
        let handle = st.next_animation;
        st.next_animation = st.next_animation.saturating_add(1);
        st.animation_callbacks.insert(handle, cid);
        Ok(scope.number(f64::from(handle)))
    })?;
    scope.define_method(global, "cancelAnimationFrame", 1, |scope, args| {
        let n = scope.to_number(args.get(0))?;
        let st = state(scope)?;
        if n.is_finite()
            && n >= 0.0
            && let Some(cid) = st.animation_callbacks.remove(&(n as u32))
        {
            st.callbacks.remove(&cid);
        }
        Ok(scope.undefined())
    })?;

    // performance.now()
    let performance = scope.new_object()?;
    scope.define_method(performance, "now", 0, |scope, _args| {
        let ms = performance_ms(scope)?;
        Ok(scope.number(ms))
    })?;
    scope.set(global, Key::from("performance"), performance)?;

    install_local_storage(scope, global)?;
    install_document(scope)
}

/// `localStorage` (HTML §12.2.1†): the methods and `length`, over the page's
/// hooks (the renderer sends the kernel's `Storage*` messages). Named
/// property access (`localStorage.key = v`) is not implemented.
fn install_local_storage(scope: &mut Scope<'_>, global: Local<'_>) -> Result<()> {
    fn text(scope: &mut Scope<'_>, v: Local<'_>) -> Result<String> {
        let s = scope.to_string(v)?;
        scope.string_to_string_lossy(s)
    }
    let storage = scope.new_object()?;
    scope.define_method(storage, "getItem", 1, |scope, args| {
        let key = text(scope, args.get(0))?;
        match page::page(scope)?.hooks.storage_get(&key) {
            Some(v) => Ok(scope.string(&v)),
            None => Ok(scope.null()),
        }
    })?;
    scope.define_method(storage, "setItem", 2, |scope, args| {
        let key = text(scope, args.get(0))?;
        let value = text(scope, args.get(1))?;
        if page::page(scope)?.hooks.storage_set(&key, &value) {
            Ok(scope.undefined())
        } else {
            Err(scope.throw_error(ErrorKind::Error, "QuotaExceededError: the storage is full"))
        }
    })?;
    scope.define_method(storage, "removeItem", 1, |scope, args| {
        let key = text(scope, args.get(0))?;
        page::page(scope)?.hooks.storage_remove(&key);
        Ok(scope.undefined())
    })?;
    scope.define_method(storage, "clear", 0, |scope, _args| {
        page::page(scope)?.hooks.storage_clear();
        Ok(scope.undefined())
    })?;
    scope.define_method(storage, "key", 1, |scope, args| {
        let n = scope.to_number(args.get(0))?;
        let index = if n.is_finite() && n >= 0.0 {
            n as u64
        } else {
            u64::MAX
        };
        match page::page(scope)?.hooks.storage_key(index) {
            Some(v) => Ok(scope.string(&v)),
            None => Ok(scope.null()),
        }
    })?;
    let length = scope.function("get length", 0, Callable::Function, |scope, _args| {
        let n = page::page(scope)?.hooks.storage_length();
        Ok(scope.number(n as f64))
    })?;
    scope.define_property(
        storage,
        Key::from("length"),
        PropertyDescriptor {
            get: Some(length),
            enumerable: Some(true),
            configurable: Some(true),
            ..PropertyDescriptor::default()
        },
    )?;
    scope.define_property(
        global,
        Key::from("localStorage"),
        PropertyDescriptor {
            value: Some(storage),
            writable: Some(false),
            enumerable: Some(true),
            configurable: Some(true),
            ..PropertyDescriptor::default()
        },
    )
}

/// The members HTML adds to `Document`, on its prototype; and the page's
/// `document` object, for `currentScript`.
fn install_document(scope: &mut Scope<'_>) -> Result<()> {
    let proto = clazel_webidl::platform::prototype::<page::Page>(scope, InterfaceId::Document)?;
    scope.define_method(proto, "write", 1, |scope, args| {
        super::write::document_write(scope, args, false)?;
        Ok(scope.undefined())
    })?;
    scope.define_method(proto, "writeln", 1, |scope, args| {
        super::write::document_write(scope, args, true)?;
        Ok(scope.undefined())
    })?;
    scope.define_method(proto, "open", 0, |scope, _args| {
        super::write::document_open(scope)?;
        super::globals::document_object(scope)
    })?;
    scope.define_method(proto, "close", 0, |scope, _args| {
        super::write::document_close(scope)?;
        Ok(scope.undefined())
    })?;
    let get_cookie = scope.function("get cookie", 0, Callable::Function, |scope, _args| {
        let s = page::page(scope)?.hooks.cookie_get();
        Ok(scope.string(&s))
    })?;
    let set_cookie = scope.function("set cookie", 1, Callable::Function, |scope, args| {
        let v = scope.to_string(args.get(0))?;
        let v = scope.string_to_string_lossy(v)?;
        page::page(scope)?.hooks.cookie_set(&v);
        Ok(scope.undefined())
    })?;
    scope.define_property(
        proto,
        Key::from("cookie"),
        PropertyDescriptor {
            get: Some(get_cookie),
            set: Some(set_cookie),
            enumerable: Some(true),
            configurable: Some(true),
            ..PropertyDescriptor::default()
        },
    )?;
    let ready_state = scope.function("get readyState", 0, Callable::Function, |scope, _args| {
        let name = match state(scope)?.readiness {
            Readiness::Loading => "loading",
            Readiness::Interactive => "interactive",
            Readiness::Complete => "complete",
        };
        Ok(scope.string(name))
    })?;
    scope.define_property(
        proto,
        Key::from("readyState"),
        PropertyDescriptor {
            get: Some(ready_state),
            enumerable: Some(true),
            configurable: Some(true),
            ..PropertyDescriptor::default()
        },
    )?;

    // The `document` object: node 0's wrapper, which `currentScript` is set
    // on as an own property (the generated interface leaves it out: its type,
    // `HTMLScriptElement`, is not exposed yet).
    let document = clazel_webidl::platform::wrap::<page::Page>(scope, page::Page::node_key(0))?;
    let null = scope.null();
    scope.set(document, Key::from("currentScript"), null)?;
    let handle = scope.persist(document);
    state(scope)?.document_object = Some(handle);
    Ok(())
}
