//! The vendored WPT `dom/events/` pages (item 7.14), run through the page
//! with a stand-in for `testharness.js` (`tests/support/standin-events.js`,
//! which says why). A page passes when every subtest it makes passes and
//! finishes; the pages that do not are listed with the reason, never
//! counted as passes and never dropped. This is evidence about dispatch,
//! handlers and the activation behaviors: it is not a run of
//! `testharness.js`, and a page that needs what the stand-in lacks is
//! listed.
//!
//! The pages of `uievents/` are not vendored (`tests/data/wpt-web/` has the
//! directories phase-7.md exit criterion 2 names, and `dom/events/` is one);
//! `scrolling/` and `non-cancelable-when-passive/` need layout or a
//! window with a viewport, and are listed as a group.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use clazel_encoding::labels::spec::Encoding;
use clazel_js::{Key, Limits, Result};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;
use clazel_web::page::NoHooks;
use clazel_web::scripting::time::Clock;
use clazel_web::scripting::{DocumentOptions, Page, Progress, Report, Response};

struct NoEnc;

impl EncFnsExec for NoEnc {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

#[derive(Clone, Default)]
struct TestClock(Arc<Mutex<u64>>);

impl Clock for TestClock {
    fn now_us(&mut self) -> u64 {
        self.0.lock().map_or(0, |v| *v)
    }
}

const DIR: &str = "https://wpt.test/dom/events/";

/// The pages run: `.html` pages as they are, `.any.js` and `.window.js`
/// ones inside a page that loads the harness.
macro_rules! page {
    ($name:literal) => {
        (
            $name,
            include_str!(concat!("data/wpt-web/dom/events/", $name)),
        )
    };
}

const PAGES: &[(&str, &str)] = &[
    page!("AddEventListenerOptions-once.any.js"),
    page!("AddEventListenerOptions-passive.any.js"),
    page!("AddEventListenerOptions-signal.any.js"),
    page!("CustomEvent.html"),
    page!("Event-cancelBubble.html"),
    page!("Event-constants.html"),
    page!("Event-constructors.any.js"),
    page!("Event-defaultPrevented-after-dispatch.html"),
    page!("Event-defaultPrevented.html"),
    page!("Event-dispatch-bubble-canceled.html"),
    page!("Event-dispatch-bubbles-false.html"),
    page!("Event-dispatch-bubbles-true.html"),
    page!("Event-dispatch-click.html"),
    page!("Event-dispatch-detached-click.html"),
    page!("Event-dispatch-detached-input-and-change.html"),
    page!("Event-dispatch-handlers-changed.html"),
    page!("Event-dispatch-listener-order.window.js"),
    page!("Event-dispatch-multiple-cancelBubble.html"),
    page!("Event-dispatch-multiple-stopPropagation.html"),
    page!("Event-dispatch-omitted-capture.html"),
    page!("Event-dispatch-on-disabled-elements.html"),
    page!("Event-dispatch-order-at-target.html"),
    page!("Event-dispatch-order.html"),
    page!("Event-dispatch-propagation-stopped.html"),
    page!("Event-dispatch-redispatch.html"),
    page!("Event-dispatch-reenter.html"),
    page!("Event-dispatch-single-activation-behavior.html"),
    page!("Event-dispatch-target-moved.html"),
    page!("Event-dispatch-target-removed.html"),
    page!("Event-dispatch-throwing.html"),
    page!("Event-init-while-dispatching.html"),
    page!("Event-initEvent.html"),
    page!("Event-isTrusted.any.js"),
    page!("Event-propagation.html"),
    page!("Event-returnValue.html"),
    page!("Event-stopImmediatePropagation.html"),
    page!("Event-stopPropagation-cancel-bubbling.html"),
    page!("Event-subclasses-constructors.html"),
    page!("Event-type-empty.html"),
    page!("Event-type.html"),
    page!("EventListener-handleEvent.html"),
    page!("EventListenerOptions-capture.html"),
    page!("EventTarget-add-remove-listener.any.js"),
    page!("EventTarget-addEventListener.any.js"),
    page!("EventTarget-constructible.any.js"),
    page!("EventTarget-dispatchEvent-returnvalue.html"),
    page!("EventTarget-dispatchEvent.html"),
    page!("EventTarget-removeEventListener.any.js"),
    page!("EventTarget-this-of-listener.html"),
    page!("event-disabled-dynamic.html"),
    page!("event-global-extra.window.js"),
    page!("event-global-replaceable.html"),
    page!("event-src-element-nullable.html"),
    page!("handler-count.html"),
    page!("label-default-action.html"),
    page!("legacy-pre-activation-behavior.window.js"),
    page!("passive-by-default.html"),
    page!("preventDefault-during-activation-behavior.html"),
    page!("remove-all-listeners.html"),
    page!("event-handler-attribute-replace-preserves-passive.html"),
    page!("Body-FrameSet-Event-Handlers.html"),
    page!("click-on-absolute-pseudo.html"),
    page!("element-click.html"),
    page!("EventListener-addEventListener.sub.window.js"),
];

/// Pages expected not to pass, with the reason.
const KNOWN: &[(&str, &str)] = &[
    (
        "Event-constants.html",
        "needs /dom/constants.js (`testConstants`), which is not vendored",
    ),
    (
        "EventTarget-dispatchEvent.html",
        "needs /dom/constants.js (`aliases`), which is not vendored",
    ),
    (
        "Event-dispatch-bubbles-false.html",
        "needs other documents (`new Document()`, `cloneNode` of a document, `DOMImplementation`): one document per page (item 7.13)",
    ),
    (
        "Event-dispatch-bubbles-true.html",
        "needs other documents (`new Document()`, `cloneNode` of a document, `DOMImplementation`): one document per page (item 7.13)",
    ),
    (
        "Event-dispatch-click.html",
        "needs HTMLInputElement's `type`, `checked` and `disabled` and HTMLAnchorElement's `href` (item 7.13's element interfaces); the behavior it tests is covered by tests/activation.rs and tests/ui_events.rs",
    ),
    (
        "Event-dispatch-detached-input-and-change.html",
        "needs HTMLInputElement's `type` (item 7.13) and shadow DOM (`attachShadow`)",
    ),
    (
        "Event-dispatch-listener-order.window.js",
        "needs shadow DOM (`attachShadow`)",
    ),
    (
        "Event-dispatch-on-disabled-elements.html",
        "needs `for...of` (the engine does not run it) and the form control interfaces (item 7.13)",
    ),
    (
        "Event-dispatch-redispatch.html",
        "needs `Promise` (the engine's)",
    ),
    (
        "Event-dispatch-single-activation-behavior.html",
        "needs `template` contents, `details` and `area` (item 7.13 and activation behaviors this browser does not have)",
    ),
    (
        "Event-dispatch-throwing.html",
        "needs `ErrorEvent`: \"report an exception\" fires `error` at the window and `window.onerror` is called with (message, source, line, column, error); here a listener's exception is logged (README: not done)",
    ),
    (
        "Event-isTrusted.any.js",
        "needs `Object.getOwnPropertyDescriptor`, which the engine's built-ins do not have yet",
    ),
    (
        "Event-subclasses-constructors.html",
        "needs `class ... extends` (the engine does not run it)",
    ),
    (
        "EventListener-handleEvent.html",
        "needs `promise_test`, which needs `Promise` (the engine's); its 3 synchronous subtests pass",
    ),
    (
        "handler-count.html",
        "needs `promise_test`, which needs `Promise` (the engine's)",
    ),
    (
        "preventDefault-during-activation-behavior.html",
        "needs `promise_test`, which needs `Promise` (the engine's)",
    ),
    (
        "click-on-absolute-pseudo.html",
        "needs `promise_test` (`Promise`) and layout of a pseudo-element",
    ),
    (
        "element-click.html",
        "needs `promise_test`, which needs `Promise` (the engine's); its 2 synchronous subtests pass",
    ),
    (
        "EventTarget-this-of-listener.html",
        "needs `createProcessingInstruction` and `for...of` (item 7.13 and the engine)",
    ),
    (
        "event-disabled-dynamic.html",
        "needs HTMLInputElement's `disabled` (item 7.13): `e.disabled = false` is a plain property here, the attribute stays",
    ),
    (
        "event-global-extra.window.js",
        "needs other globals (iframes, `XMLHttpRequest`) and other documents",
    ),
    (
        "label-default-action.html",
        "needs HTMLInputElement's `type` and `checked` (item 7.13)",
    ),
    (
        "Body-FrameSet-Event-Handlers.html",
        "needs `for...of`, `SVGElement` and the form interfaces (the engine and item 7.13); the body and window handler forwarding it tests is covered by tests/ui_events.rs",
    ),
    (
        "EventListener-addEventListener.sub.window.js",
        "needs an iframe and a cross-origin object (`.sub` server substitutions)",
    ),
];

/// What a page did.
enum Verdict {
    Pass { subtests: usize },
    Fail(String),
}

/// Runs one page.
fn run_page(name: &str, source: &str) -> Result<Verdict> {
    let html = if name.ends_with(".html") {
        source.to_owned()
    } else {
        // A `.any.js` or `.window.js` test is a script that calls the
        // harness: a page that loads it, with the `META` lines as comments.
        format!(
            "<!DOCTYPE html><meta charset=utf-8><script src=/resources/testharness.js></script>\
             <script src=/resources/testharnessreport.js></script><div id=log></div>\
             <script src=\"{name}\"></script>"
        )
    };
    let mut files: HashMap<String, (&'static str, String)> = HashMap::new();
    files.insert(
        "https://wpt.test/resources/testharness.js".to_owned(),
        (
            "text/javascript",
            include_str!("support/standin-events.js").to_owned(),
        ),
    );
    files.insert(
        "https://wpt.test/resources/testharnessreport.js".to_owned(),
        ("text/javascript", String::new()),
    );
    if !name.ends_with(".html") {
        files.insert(
            format!("{DIR}{name}"),
            ("text/javascript", source.to_owned()),
        );
    }
    let url = format!("{DIR}{name}");
    let input: Vec<u32> = html.chars().map(u32::from).collect();
    let cps: Vec<u32> = url.chars().map(u32::from).collect();
    let (parsed, _) = parse_real(&NoEnc, &input, cps, true, false);
    // Not at 0: `timeStamp` is positive in a page that has run for a moment.
    let clock = TestClock(Arc::new(Mutex::new(1_000_000)));
    let mut page = Page::for_document(
        DocumentOptions {
            url,
            encoding: Encoding::Utf8,
            limits: Limits {
                heap_bytes: if cfg!(miri) { 64 << 20 } else { 512 << 20 },
                value_stack_bytes: if cfg!(miri) { 1 << 20 } else { 8 << 20 },
                ..Limits::unlimited()
            },
            clock: Box::new(clock.clone()),
            hooks: Box::new(NoHooks),
        },
        parsed.arena,
    )?;
    // The page has run for a moment when its scripts start: `timeStamp` is
    // positive.
    if let Ok(mut t) = clock.0.lock() {
        *t = t.saturating_add(5_000);
    }
    let mut progress = page.run()?;
    let mut guard = 0u32;
    while progress == Progress::Waiting && guard < 50 {
        guard = guard.saturating_add(1);
        let requests = page.take_requests()?;
        if requests.is_empty() {
            break;
        }
        for r in requests {
            let response = match files.get(&r.url) {
                Some((content_type, body)) => Ok(Response {
                    url: None,
                    ok: true,
                    content_type: content_type.as_bytes().to_vec(),
                    body: body.clone().into_bytes(),
                }),
                None => Err(clazel_web::scripting::NetworkError),
            };
            progress = page.fetched(r.id, response)?;
        }
    }
    // Let the timers the page set run (a test that finishes later).
    for _ in 0..40 {
        if let Ok(mut t) = clock.0.lock() {
            *t = t.saturating_add(10_000);
        }
        page.run_event_loop()?;
    }
    let realm = page.realm().clone();
    let summary = page.runtime().scope(|scope| {
        scope.eval_script(
            &realm,
            clazel_js::Source::new("s.js", "var __s = __summary();"),
        )?;
        let g = scope.global(&realm)?;
        let v = scope.get(g, Key::Str("__s"))?;
        scope.string_to_string_lossy(v)
    });
    let summary = match summary {
        Ok(s) => s,
        Err(e) => return Ok(Verdict::Fail(format!("no summary: {e}"))),
    };
    let reports = page.take_reports()?;
    let engine: Vec<String> = reports
        .iter()
        .map(|r| match r {
            Report::Engine { error, .. } => error.clone(),
            Report::Exception { name, message, .. } => format!("{name}: {message}"),
        })
        .collect();
    let counts: Vec<usize> = summary
        .split(' ')
        .next()
        .unwrap_or("")
        .split('/')
        .filter_map(|n| n.parse().ok())
        .collect();
    match counts.as_slice() {
        [pass, 0, 0] if *pass > 0 && engine.is_empty() => Ok(Verdict::Pass { subtests: *pass }),
        _ => Ok(Verdict::Fail(format!("{summary}; reports {engine:?}"))),
    }
}

/// The vendored pages that run, under the stand-in harness.
#[test]
#[cfg_attr(
    miri,
    ignore = "each page builds every generated WebIDL interface: over 1 000 s of Miri time even at a stride of 32; a_page_with_the_bindings_runs_a_script stays"
)]
fn wpt_dom_events() -> Result<()> {
    let mut pass = 0usize;
    let mut subtests = 0usize;
    let mut xfail = 0usize;
    let mut failed = Vec::new();
    let mut stale = Vec::new();
    // Under Miri every 32nd page (two): each builds a runtime and its built-ins,
    // which Miri takes about a minute for, and the pages' own subtests run
    // the same code the other tests do; the full list runs in the normal
    // test job.
    let stride = if cfg!(miri) { 32 } else { 1 };
    // `CLAZEL_WPT_ONLY=text` runs the pages whose name has the text, for a
    // look at one (no effect when unset, and under Miri's isolation).
    let only = std::env::var("CLAZEL_WPT_ONLY").unwrap_or_default();
    for (name, source) in PAGES.iter().step_by(stride) {
        if !name.contains(only.as_str()) {
            continue;
        }
        let verdict = run_page(name, source)?;
        let known = KNOWN.iter().find(|(k, _)| k == name);
        match (verdict, known) {
            (Verdict::Pass { subtests: n }, None) => {
                pass += 1;
                subtests += n;
            }
            (Verdict::Pass { .. }, Some(_)) => stale.push(*name),
            (Verdict::Fail(_), Some(_)) => xfail += 1,
            (Verdict::Fail(why), None) => failed.push(format!("{name}: {why}")),
        }
    }
    for f in &failed {
        println!("FAIL {f}\n");
    }
    for (k, why) in KNOWN {
        println!("  expected failure {k}: {why}");
    }
    println!("  subtests passed: {subtests}");
    println!(
        "clazel-conformance: suite=\"WPT dom/events, stand-in harness\" pass={pass} xfail={xfail} fail={} total={}",
        failed.len(),
        PAGES.len().div_ceil(stride)
    );
    assert!(stale.is_empty(), "listed as failures but pass: {stale:?}");
    assert!(failed.is_empty(), "{} unexpected failures", failed.len());
    Ok(())
}
