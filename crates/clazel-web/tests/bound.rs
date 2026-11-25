//! A parsed document hosted with the bindings, its scripts run by HTML's
//! script processing and its timers by the event loop (items 7.12, 7.15 and
//! 7.17's page): `scripting::Page::for_document`.

use std::sync::{Arc, Mutex};

use clazel_encoding::labels::spec::Encoding;
use clazel_js::{Key, Limits, Result};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;
use clazel_web::page::{HookCall, LogLevel, PageHooks};
use clazel_web::scripting::time::Clock;
use clazel_web::scripting::{
    DocumentOptions, NetworkError, Page, Progress, Report, Request, RequestKind, Response,
};

const URL: &str = "https://example.test/dir/page.html";

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

/// What the hooks saw, and the cookie and storage they answer with.
#[derive(Default)]
struct Seen {
    calls: Vec<HookCall>,
    cookie: String,
    storage: Vec<(String, String)>,
}

struct Hooks(Arc<Mutex<Seen>>);

impl Hooks {
    fn with<R>(&self, f: impl FnOnce(&mut Seen) -> R) -> Option<R> {
        self.0.lock().ok().map(|mut s| f(&mut s))
    }
}

impl PageHooks for Hooks {
    fn navigate(&mut self, url: &str, replace: bool) {
        self.with(|s| {
            s.calls.push(HookCall::Navigate {
                url: url.to_owned(),
                replace,
            });
        });
    }

    fn update_url(&mut self, url: &str, replace: bool) {
        self.with(|s| {
            s.calls.push(HookCall::UpdateUrl {
                url: url.to_owned(),
                replace,
            });
        });
    }

    fn log(&mut self, level: LogLevel, text: &str) {
        self.with(|s| s.calls.push(HookCall::Log(level, text.to_owned())));
    }

    fn cookie_get(&mut self) -> String {
        self.with(|s| s.cookie.clone()).unwrap_or_default()
    }

    fn cookie_set(&mut self, cookie: &str) {
        self.with(|s| s.cookie = cookie.to_owned());
    }

    fn storage_get(&mut self, key: &str) -> Option<String> {
        self.with(|s| {
            s.storage
                .iter()
                .find(|(k, _)| k == key)
                .map(|(_, v)| v.clone())
        })
        .flatten()
    }

    fn storage_set(&mut self, key: &str, value: &str) -> bool {
        self.with(|s| {
            s.storage.retain(|(k, _)| k != key);
            s.storage.push((key.to_owned(), value.to_owned()));
        });
        true
    }

    fn storage_length(&mut self) -> u64 {
        self.with(|s| s.storage.len() as u64).unwrap_or(0)
    }
}

struct Harness {
    page: Page,
    clock: TestClock,
    seen: Arc<Mutex<Seen>>,
}

fn limits() -> Limits {
    Limits {
        heap_bytes: if cfg!(miri) { 64 << 20 } else { 512 << 20 },
        value_stack_bytes: if cfg!(miri) { 1 << 20 } else { 8 << 20 },
        ..Limits::unlimited()
    }
}

impl Harness {
    fn new(html: &str) -> Result<Harness> {
        let input: Vec<u32> = html.chars().map(u32::from).collect();
        let url: Vec<u32> = URL.chars().map(u32::from).collect();
        let (parsed, _) = parse_real(&NoEnc, &input, url, true, false);
        let clock = TestClock::default();
        let seen = Arc::new(Mutex::new(Seen::default()));
        let page = Page::for_document(
            DocumentOptions {
                url: URL.to_owned(),
                encoding: Encoding::Utf8,
                limits: limits(),
                clock: Box::new(clock.clone()),
                hooks: Box::new(Hooks(Arc::clone(&seen))),
            },
            parsed.arena,
        )?;
        Ok(Harness { page, clock, seen })
    }

    fn advance(&self, ms: u64) {
        if let Ok(mut t) = self.clock.0.lock() {
            *t = t.saturating_add(ms.saturating_mul(1000));
        }
    }

    /// The global `r`, as a string.
    fn r(&mut self) -> Result<String> {
        let realm = self.page.realm().clone();
        self.page.runtime().scope(|scope| {
            let g = scope.global(&realm)?;
            let r = scope.get(g, Key::Str("r"))?;
            let s = scope.to_string(r)?;
            scope.string_to_string_lossy(s)
        })
    }

    fn logs(&self) -> Vec<String> {
        self.seen
            .lock()
            .map(|s| {
                s.calls
                    .iter()
                    .filter_map(|c| match c {
                        HookCall::Log(_, t) => Some(t.clone()),
                        _ => None,
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    fn calls(&self) -> Vec<HookCall> {
        self.seen
            .lock()
            .map(|s| s.calls.clone())
            .unwrap_or_default()
    }

    /// The text of the element with id `id`.
    fn text_of(&mut self, id: &str) -> Result<String> {
        let realm = self.page.realm().clone();
        let id = id.to_owned();
        self.page.runtime().scope(|scope| {
            let src = format!("var __text = document.getElementById('{id}').textContent;");
            scope.eval_script(&realm, clazel_js::Source::new("t.js", &src))?;
            let g = scope.global(&realm)?;
            let v = scope.get(g, Key::Str("__text"))?;
            let s = scope.to_string(v)?;
            scope.string_to_string_lossy(s)
        })
    }
}

type Test = Result<()>;

/// The one request the page made.
fn only(mut requests: Vec<Request>) -> Result<Request> {
    match (requests.pop(), requests.is_empty()) {
        (Some(r), true) => Ok(r),
        _ => Err(clazel_js::Error::WrongType("exactly one request")),
    }
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn an_inline_script_changes_the_document() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=out>before</p><script>\
         document.getElementById('out').textContent = 'after';\
         var r = document.currentScript.tagName + ':' + document.readyState;\
         </script>",
    )?;
    assert_eq!(h.page.run()?, Progress::Loaded);
    assert_eq!(h.text_of("out")?, "after");
    assert_eq!(h.r()?, "SCRIPT:loading");
    // The tree the page holds is the one the script changed.
    let changed = h.page.with_document(|arena| arena.len())?;
    assert!(changed > 4);
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn lifecycle_events_reach_listeners_in_order() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><script>\
         var r = '';\
         document.addEventListener('DOMContentLoaded', function () { r += 'D(' + document.readyState + ')'; });\
         window.addEventListener('load', function () { r += 'L(' + document.readyState + ')'; });\
         document.addEventListener('readystatechange', function () { r += 'S'; });\
         </script>",
    )?;
    assert_eq!(h.page.run()?, Progress::Loaded);
    assert_eq!(h.r()?, "SD(interactive)SL(complete)");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn defer_runs_after_the_document_and_before_domcontentloaded() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><script>var r = 'a';\
         document.addEventListener('DOMContentLoaded', function () { r += 'D'; });</script>\
         <script defer src=d.js></script><script>r += 'b';</script>",
    )?;
    assert_eq!(h.page.run()?, Progress::Waiting);
    let request = only(h.page.take_requests()?)?;
    assert_eq!(h.r()?, "ab");
    h.page.fetched(
        request.id,
        Ok(Response {
            url: None,
            ok: true,
            content_type: b"text/javascript".to_vec(),
            body: b"r += 'f';".to_vec(),
        }),
    )?;
    assert_eq!(h.r()?, "abfD");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn timers_run_when_due_and_in_order() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><script>var r = '';\
         setTimeout(function () { r += 'b'; }, 20);\
         setTimeout(function () { r += 'a'; }, 10);\
         setTimeout(function (x, y) { r += x + y; }, 10, 'c', 'd');\
         var id = setTimeout(function () { r += 'NO'; }, 5);\
         clearTimeout(id);\
         </script>",
    )?;
    h.page.run()?;
    assert_eq!(h.page.next_wake_ms()?, Some(10));
    h.page.run_event_loop()?;
    assert_eq!(h.r()?, "");
    h.advance(10);
    h.page.run_event_loop()?;
    assert_eq!(h.r()?, "acd");
    assert_eq!(h.page.next_wake_ms()?, Some(20));
    h.advance(10);
    h.page.run_event_loop()?;
    assert_eq!(h.r()?, "acdb");
    assert_eq!(h.page.next_wake_ms()?, None);
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn an_interval_repeats_until_it_is_cleared() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><script>var r = 0, id = setInterval(function () {\
         r++; if (r == 3) clearInterval(id); }, 10);</script>",
    )?;
    h.page.run()?;
    for _ in 0..5 {
        h.advance(10);
        h.page.run_event_loop()?;
    }
    assert_eq!(h.r()?, "3");
    assert_eq!(h.page.next_wake_ms()?, None);
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_timer_changes_the_document() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=out>0</p><script>\
         setTimeout(function () { document.getElementById('out').textContent = 'later'; }, 50);</script>",
    )?;
    h.page.run()?;
    h.advance(50);
    h.page.run_event_loop()?;
    assert_eq!(h.text_of("out")?, "later");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn microtasks_run_when_a_script_ends_and_before_the_next_task() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><script>var r = '';\
         setTimeout(function () { r += 't'; }, 0);\
         queueMicrotask(function () { r += 'm'; queueMicrotask(function () { r += 'n'; }); });\
         r += 's';</script><script>r += '2';</script>",
    )?;
    h.page.run()?;
    // The microtasks ran when the first script ended, before the second.
    assert_eq!(h.r()?, "smn2");
    h.page.run_event_loop()?;
    assert_eq!(h.r()?, "smn2t");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn animation_frames_run_when_the_page_renders() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><script>var r = '';\
         var a = requestAnimationFrame(function (t) { r += typeof t; });\
         var b = requestAnimationFrame(function () { r += 'NO'; });\
         cancelAnimationFrame(b);</script>",
    )?;
    h.page.run()?;
    assert!(h.page.wants_animation_frame()?);
    assert!(h.page.update_the_rendering()?);
    assert_eq!(h.r()?, "number");
    assert!(!h.page.update_the_rendering()?);
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn an_exception_is_reported_and_the_next_script_runs() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><script>var r = 'a'; throw new TypeError('boom');</script>\
         <script>r += 'b';</script>",
    )?;
    assert_eq!(h.page.run()?, Progress::Loaded);
    assert_eq!(h.r()?, "ab");
    let reports = h.page.take_reports()?;
    assert!(matches!(
        reports.as_slice(),
        [Report::Exception { name, message, .. }] if name == "TypeError" && message == "boom"
    ));
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn an_exception_in_a_timer_is_reported_and_the_loop_goes_on() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><script>var r = '';\
         setTimeout(function () { throw new Error('x'); }, 1);\
         setTimeout(function () { r += 'ok'; }, 2);</script>",
    )?;
    h.page.run()?;
    h.advance(5);
    h.page.run_event_loop()?;
    assert_eq!(h.r()?, "ok");
    assert_eq!(h.page.take_reports()?.len(), 1);
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn an_external_script_is_fetched_and_runs_in_order() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><script>var r = 'a';</script>\
         <script src=app.js></script><script>r += 'c';</script>",
    )?;
    assert_eq!(h.page.run()?, Progress::Waiting);
    let request = only(h.page.take_requests()?)?;
    assert_eq!(request.url, "https://example.test/dir/app.js");
    assert_eq!(request.kind, RequestKind::ClassicScript);
    // `c` waits for it: the script is parser-blocking.
    assert_eq!(h.r()?, "a");
    let done = h.page.fetched(
        request.id,
        Ok(Response {
            url: None,
            ok: true,
            content_type: b"text/javascript".to_vec(),
            body: b"r += 'b';".to_vec(),
        }),
    )?;
    assert_eq!(done, Progress::Loaded);
    assert_eq!(h.r()?, "abc");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_failed_fetch_fires_error_and_the_page_goes_on() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><script src=missing.js id=s></script><script>var r = 'x';</script>",
    )?;
    h.page.run()?;
    let request = only(h.page.take_requests()?)?;
    h.page.fetched(request.id, Err(NetworkError))?;
    assert_eq!(h.r()?, "x");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn console_location_and_history_reach_the_hooks() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><script>console.log('hi', 1);\
         history.pushState(null, '', '/dir/other.html');\
         location.href = '/next';</script>",
    )?;
    h.page.run()?;
    let calls = h.calls();
    assert!(
        calls
            .iter()
            .any(|c| matches!(c, HookCall::Log(LogLevel::Log, t) if t == "hi 1"))
    );
    assert!(calls.contains(&HookCall::UpdateUrl {
        url: "https://example.test/dir/other.html".to_owned(),
        replace: false
    }));
    assert!(calls.contains(&HookCall::Navigate {
        url: "https://example.test/next".to_owned(),
        replace: false
    }));
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn cookies_and_storage_go_through_the_hooks() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><script>document.cookie = 'a=1; Path=/';\
         localStorage.setItem('k', 'v');\
         var r = document.cookie + '|' + localStorage.getItem('k') + '|' + localStorage.getItem('z')\
         + '|' + localStorage.length;</script>",
    )?;
    h.page.run()?;
    assert_eq!(h.r()?, "a=1; Path=/|v|null|1");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_javascript_url_runs_in_the_page() -> Test {
    let mut h = Harness::new("<!DOCTYPE html><body><p id=out>x</p>")?;
    h.page.run()?;
    let result = h.page.evaluate_javascript_url(
        "javascript:document.getElementById('out').textContent%3D'ran'%3B",
    )?;
    assert_eq!(result, None);
    assert_eq!(h.text_of("out")?, "ran");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn document_write_in_a_script_is_reported_not_run() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=out>x</p><script>document.write('<b>y</b>');</script>",
    )?;
    h.page.run()?;
    assert_eq!(h.text_of("out")?, "x");
    let reports = h.page.take_reports()?;
    assert!(matches!(reports.as_slice(), [Report::Engine { .. }]));
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_string_handler_runs_as_a_script() -> Test {
    let mut h =
        Harness::new("<!DOCTYPE html><body><script>var r = 0; setTimeout('r = 7', 1);</script>")?;
    h.page.run()?;
    h.advance(1);
    h.page.run_event_loop()?;
    assert_eq!(h.r()?, "7");
    assert!(h.logs().is_empty());
    Ok(())
}

// ---- The bindings are installed by the first thing that needs them ---------

impl Harness {
    /// The element whose `id` attribute is `id`, without the engine.
    fn node(&mut self, id: &str) -> Result<usize> {
        let want: Vec<u32> = id.chars().map(u32::from).collect();
        let found = self.page.with_document(|arena| {
            (0..arena.len()).find(|&n| match arena.kind(n) {
                clazel_dom::exec::ExecKind::Element { attributes, .. } => attributes
                    .iter()
                    .any(|a| a.local_name == [0x69, 0x64] && a.value == want),
                _ => false,
            })
        })?;
        found.ok_or(clazel_js::Error::WrongType("no such element"))
    }

    fn click_on(&mut self, id: &str) -> Result<()> {
        let target = self.node(id)?;
        self.page.click(clazel_web::page::input::MouseInput {
            target,
            ..clazel_web::page::input::MouseInput::default()
        })
    }
}

/// A document with no script is loaded, clicked, typed into and scrolled
/// without its realm ever getting the bindings: everything the page does by
/// itself (the load events nothing listens to, a link's activation
/// behaviour, a text control's editing) is Rust over the tree. This runs
/// under Miri, where the bindings' installation is most of a page's cost.
#[test]
fn a_document_with_no_script_never_installs_the_bindings() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><title>t</title><body><a id=a href='next.html'>link</a>\
         <form action='/go'><input id=i name=q><button id=b>go</button></form>",
    )?;
    assert!(!h.page.bindings_installed()?);
    assert_eq!(h.page.run()?, Progress::Loaded);
    assert!(h.page.take_requests()?.is_empty());
    h.page.run_event_loop()?;
    h.page.update_the_rendering()?;
    // A click on the link navigates, as with the bindings.
    h.click_on("a")?;
    assert_eq!(
        h.calls(),
        vec![HookCall::Navigate {
            url: "https://example.test/dir/next.html".to_owned(),
            replace: false
        }]
    );
    // Typing into the focused control changes its value.
    let i = h.node("i")?;
    h.click_on("i")?;
    assert_eq!(h.page.focused()?, Some(i));
    h.page.key(clazel_web::page::input::KeyInput {
        key: "k".to_owned(),
        ..clazel_web::page::input::KeyInput::default()
    })?;
    assert_eq!(h.page.control_value(i)?, "k");
    h.page
        .wheel(clazel_web::page::input::WheelInput::default())?;
    h.page.scrolled()?;
    assert!(h.page.take_reports()?.is_empty());
    assert!(!h.page.bindings_installed()?);
    // The first script finds the whole platform.
    h.page.run_source(
        "late.js",
        "var r = [typeof Document, document.title, document.getElementById('i').tagName, \
         typeof setTimeout, typeof console.log, document.readyState].join('|');",
    )?;
    assert!(h.page.bindings_installed()?);
    assert_eq!(h.r()?, "function|t|INPUT|function|function|complete");
    Ok(())
}

/// Each way source text reaches the realm installs the bindings first: a
/// script element, an event handler content attribute (compiled when its
/// event is first dispatched), a `javascript:` URL, a module script, and
/// the embedder asking for the engine.
#[test]
#[cfg_attr(
    miri,
    ignore = "five pages that each install every generated WebIDL interface: minutes of Miri time; a_document_with_no_script_never_installs_the_bindings and clazel-web's a_page_with_the_bindings_runs_a_script run there"
)]
fn the_first_need_installs_the_bindings() -> Test {
    // A script element.
    let mut h = Harness::new("<!DOCTYPE html><body><script>var r = typeof Node;</script>")?;
    assert!(!h.page.bindings_installed()?);
    h.page.run()?;
    assert!(h.page.bindings_installed()?);
    assert_eq!(h.r()?, "function");

    // An event handler content attribute: not at load (nothing fires at the
    // paragraph), but when the click is dispatched to it.
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=p onclick=\"this.textContent = typeof event + ':' + (this instanceof HTMLParagraphElement)\">x</p>",
    )?;
    h.page.run()?;
    assert!(!h.page.bindings_installed()?);
    h.click_on("p")?;
    assert!(h.page.bindings_installed()?);
    assert_eq!(h.text_of("p")?, "object:true");
    assert!(h.logs().is_empty());

    // The body's `onload`: compiled when `load` fires at the window.
    let mut h = Harness::new("<!DOCTYPE html><body onload=\"window.r = document.readyState\">")?;
    assert!(!h.page.bindings_installed()?);
    h.page.run()?;
    assert!(h.page.bindings_installed()?);
    assert_eq!(h.r()?, "complete");

    // A `javascript:` URL.
    let mut h = Harness::new("<!DOCTYPE html><body><p id=out>x</p>")?;
    h.page.run()?;
    assert!(!h.page.bindings_installed()?);
    h.page.evaluate_javascript_url(
        "javascript:document.getElementById('out').textContent%3D'ran'%3B",
    )?;
    assert!(h.page.bindings_installed()?);
    assert_eq!(h.text_of("out")?, "ran");

    // The embedder asking for the engine, to add to the global object or to
    // read it: what it sees is the installed realm.
    let mut h = Harness::new("<!DOCTYPE html><body>")?;
    h.page.run()?;
    assert!(!h.page.bindings_installed()?);
    let realm = h.page.realm().clone();
    let has = h.page.runtime().scope(|scope| {
        let g = scope.global(&realm)?;
        scope.has_property(g, Key::Str("HTMLElement"))
    })?;
    assert!(has);
    assert!(h.page.bindings_installed()?);
    Ok(())
}

/// The global object is the same whenever the bindings were installed: its
/// own property keys, in order, for a page whose first script is a script
/// element and for one that was loaded and clicked first.
#[test]
#[cfg_attr(
    miri,
    ignore = "two pages that each install every generated WebIDL interface and list the global object's keys: minutes of Miri time"
)]
fn the_global_object_is_the_same_whenever_the_bindings_come() -> Test {
    const KEYS: &str = "var r = Object.getOwnPropertyNames(this).join(',') + '|' + \
        Object.getOwnPropertyNames(Document.prototype).join(',') + '|' + \
        Object.getOwnPropertyNames(Object.getPrototypeOf(this)).join(',') + '|' + \
        Object.keys(this).join(',');";
    let mut early = Harness::new(&format!(
        "<!DOCTYPE html><body><a id=a href='#x'>l</a><script>{KEYS}</script>"
    ))?;
    early.page.run()?;
    let early = early.r()?;
    let mut late = Harness::new("<!DOCTYPE html><body><a id=a href='#x'>l</a>")?;
    late.page.run()?;
    late.click_on("a")?;
    late.page.run_event_loop()?;
    assert!(!late.page.bindings_installed()?);
    late.page.run_source("keys.js", KEYS)?;
    let late = late.r()?;
    assert!(early.contains("HTMLElement") && early.contains("setTimeout"));
    // `r` itself is the last key in both.
    assert_eq!(late, early);
    Ok(())
}
