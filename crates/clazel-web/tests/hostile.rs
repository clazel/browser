//! Hostile pages that need the event loop (phase-7.md 7.19), run as a page
//! runs: script through `clazel-js`'s public API, `setTimeout` a native
//! function over this crate's [`EventLoop`], and the loop driving the timer
//! callbacks back into script.
//!
//! `setTimeout` here is the test's own binding (the WebIDL bindings are
//! another item): it is [`EventLoop::set_timeout`], and a refusal past
//! [`Limits::max_timers`] becomes a `RangeError` the script can catch, where
//! the event loop's docs name a `QuotaExceededError` (a `DOMException`,
//! which `clazel-webidl` will make).

use std::collections::BTreeMap;

use clazel_js::{
    Callable, Config, Error, ErrorKind, Handle, Host as JsHost, Key, Limits as JsLimits, Realm,
    RealmOptions, Runtime, Source,
};
use clazel_web::event_loop::{CallbackId, EventLoop, Host, Limits, TimerCall};

/// The page's side of the engine: the event loop the `setTimeout` binding
/// reaches, and the callbacks it was given, by [`CallbackId`].
struct Page {
    event_loop: EventLoop,
    callbacks: BTreeMap<u64, Handle>,
    next: u64,
    draws: u64,
}

impl JsHost for Page {
    fn random_u64(&mut self) -> u64 {
        self.draws = self.draws.wrapping_add(0x9E37_79B9_7F4A_7C15);
        self.draws
    }
}

/// The event loop's host: runs a timer's callback in the page's runtime.
///
/// The loop hands its host `&mut EventLoop` while a callback runs, and the
/// callback's own `setTimeout` must reach that same loop, so for the call the
/// loop is swapped into the page (where the binding finds it) and back.
struct Driver {
    rt: Runtime,
    realm: Realm,
    ran: u64,
    errors: u64,
}

impl Driver {
    /// Runs `f` with the loop in the page, then takes it back.
    fn with_loop_in_page<R>(&mut self, el: &mut EventLoop, f: impl FnOnce(&mut Self) -> R) -> R {
        self.swap(el);
        let r = f(self);
        self.swap(el);
        r
    }

    fn swap(&mut self, el: &mut EventLoop) {
        let _ = self.rt.scope(|scope| {
            scope
                .host_mut::<Page>()
                .map(|page| core::mem::swap(&mut page.event_loop, el))
        });
    }
}

impl Host for Driver {
    fn run_task(&mut self, _: &mut EventLoop, _: CallbackId) {}

    fn run_microtask(&mut self, _: &mut EventLoop, _: CallbackId) {}

    fn run_timer(&mut self, el: &mut EventLoop, call: TimerCall) {
        self.with_loop_in_page(el, |d| {
            let realm = d.realm.clone();
            let r = d.rt.scope(|scope| {
                let handler = scope
                    .host_mut::<Page>()?
                    .callbacks
                    .remove(&call.handler.0)
                    .ok_or(Error::WrongType("a timer callback"))?;
                let f = scope.local(&handler)?;
                let this = scope.global(&realm)?;
                scope.call(f, this, &[]).map(|_| ())
            });
            d.ran = d.ran.saturating_add(1);
            if r.is_err() {
                // "Report the exception": counted, and the loop goes on.
                d.errors = d.errors.saturating_add(1);
            }
        });
    }
}

/// A page whose `setTimeout` is bound to an event loop with `limits`.
fn page(limits: Limits) -> clazel_js::Result<Driver> {
    let host = Page {
        event_loop: EventLoop::new(limits),
        callbacks: BTreeMap::new(),
        next: 0,
        draws: 1,
    };
    let mut rt = Runtime::new(Config::new(JsLimits::recommended()), host)?;
    let realm = rt.scope(|scope| scope.create_realm(RealmOptions::default()))?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let set_timeout = scope.function("setTimeout", 1, Callable::Function, |scope, args| {
            let callback = args.get(0);
            let timeout = args.get(1);
            let ms = scope.to_number(timeout)?;
            let ms = if ms.is_finite() { ms as i32 } else { 0 };
            let handle = scope.persist(callback);
            let page = scope.host_mut::<Page>()?;
            let id = page.next;
            page.next = page.next.wrapping_add(1);
            let now = page.event_loop.now();
            match page.event_loop.set_timeout(CallbackId(id), ms, now) {
                Ok(timer) => {
                    page.callbacks.insert(id, handle);
                    Ok(scope.number(f64::from(timer.get())))
                }
                Err(refused) => Err(scope.throw_error(ErrorKind::RangeError, &refused.to_string())),
            }
        })?;
        scope.set(global, Key::from("setTimeout"), set_timeout)
    })?;
    Ok(Driver {
        rt,
        realm,
        ran: 0,
        errors: 0,
    })
}

/// The global `name`, as a number.
fn number(d: &mut Driver, name: &str) -> clazel_js::Result<Option<f64>> {
    let realm = d.realm.clone();
    d.rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let v = scope.get(global, Key::from(name))?;
        Ok(scope.as_number(v))
    })
}

/// 10^6 timers from script: past `max_timers` each `setTimeout` throws a
/// `RangeError` the page catches, the loop holds no more than the cap, and
/// running it fires each accepted timer once and then holds nothing. Under
/// Miri, 300 timers past a cap of 30.
#[test]
fn a_million_timers_stay_within_the_cap() -> clazel_js::Result<()> {
    let cap: usize = if cfg!(miri) { 30 } else { 1 << 16 };
    let attempts: u32 = if cfg!(miri) { 300 } else { 1_000_000 };
    let mut d = page(Limits {
        max_timers: cap,
        ..Limits::default()
    })?;
    let realm = d.realm.clone();
    let script = format!(
        "var fired = 0, accepted = 0, refused = 0;\n\
         function tick() {{ fired = fired + 1; }}\n\
         for (var i = 0; i < {attempts}; i++) {{\n\
           try {{ setTimeout(tick, i % 50); accepted = accepted + 1; }}\n\
           catch (e) {{ if (e.name === 'RangeError') refused = refused + 1; }}\n\
         }}"
    );
    d.rt.scope(|scope| {
        scope
            .eval_script(&realm, Source::new("timers.js", &script))
            .map(|_| ())
    })?;
    let cap_f = cap as f64;
    assert_eq!(number(&mut d, "accepted")?, Some(cap_f));
    assert_eq!(
        number(&mut d, "refused")?,
        Some(f64::from(attempts) - cap_f)
    );

    // Take the loop out of the page and run it to the end of the timers.
    let mut el = EventLoop::new(Limits::default());
    d.swap(&mut el);
    assert_eq!(el.active_timer_count(), cap);
    el.run_until_idle(&mut d, 1000, usize::MAX);
    assert_eq!(el.active_timer_count(), 0);
    assert_eq!(d.ran, cap as u64);
    assert_eq!(d.errors, 0);
    assert_eq!(number(&mut d, "fired")?, Some(cap_f));
    Ok(())
}

/// A timer whose callback sets two more, for ever: the population doubles
/// until the cap refuses it, the refusals are `RangeError`s the callbacks
/// catch, and a bounded run of the loop returns (the loop itself never stops
/// such a page; that is the host's kill, phase-7.md 7.0(g)).
#[test]
fn timers_that_multiply_stay_within_the_cap() -> clazel_js::Result<()> {
    let cap: usize = if cfg!(miri) { 16 } else { 4096 };
    let mut d = page(Limits {
        max_timers: cap,
        ..Limits::default()
    })?;
    let realm = d.realm.clone();
    d.rt.scope(|scope| {
        scope
            .eval_script(
                &realm,
                Source::new(
                    "multiply.js",
                    "var refused = 0;\n\
                     function grow() {\n\
                       try { setTimeout(grow, 0); setTimeout(grow, 0); }\n\
                       catch (e) { refused = refused + 1; }\n\
                     }\n\
                     setTimeout(grow, 0);",
                ),
            )
            .map(|_| ())
    })?;
    let mut el = EventLoop::new(Limits::default());
    d.swap(&mut el);
    // A millisecond a turn, so the 4 ms clamp of nested timers lets them
    // come due; the page never runs out of timers, so every turn runs one.
    let rounds: u64 = if cfg!(miri) { 100 } else { 20_000 };
    for now in 0..rounds {
        el.run_iteration(&mut d, now);
        assert!(el.active_timer_count() <= cap);
    }
    assert!(d.ran > rounds / 2, "{}", d.ran);
    assert_eq!(d.errors, 0);
    assert!(number(&mut d, "refused")? > Some(0.0));
    Ok(())
}
