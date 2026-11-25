//! The user's input as events (phase-7.md item 7.14): clicks, keys, focus,
//! wheel and scroll through `scripting::Page`'s input API, the default
//! actions (links, forms, checkboxes), event handler attributes, and user
//! activation. Each test parses a small document, runs script that records
//! into the global `r`, and drives the page as the renderer does.
//!
//! The expectations are written from the standards (DOM §2.9†, UI Events,
//! HTML §4.10.21†, §6.4†, §6.6†, §8.1.8†), not from the implementation.

use std::sync::{Arc, Mutex};

use clazel_encoding::labels::spec::Encoding;
use clazel_js::{Key, Limits, Result};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;
use clazel_web::page::input::{KeyInput, MouseInput, WheelInput};
use clazel_web::page::{HookCall, PageHooks};
use clazel_web::scripting::time::Clock;
use clazel_web::scripting::{DocumentOptions, Page, Progress};
use clazel_web::ui::Modifiers;

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

struct Hooks(Arc<Mutex<Vec<HookCall>>>);

impl PageHooks for Hooks {
    fn navigate(&mut self, url: &str, replace: bool) {
        if let Ok(mut v) = self.0.lock() {
            v.push(HookCall::Navigate {
                url: url.to_owned(),
                replace,
            });
        }
    }

    fn submit(&mut self, url: &str, method: &str, content_type: &str, body: &[u8]) {
        if let Ok(mut v) = self.0.lock() {
            v.push(HookCall::Submit {
                url: url.to_owned(),
                method: method.to_owned(),
                content_type: content_type.to_owned(),
                body: body.to_vec(),
            });
        }
    }

    fn log(&mut self, level: clazel_web::page::LogLevel, text: &str) {
        if let Ok(mut v) = self.0.lock() {
            v.push(HookCall::Log(level, text.to_owned()));
        }
    }
}

struct Harness {
    page: Page,
    clock: TestClock,
    calls: Arc<Mutex<Vec<HookCall>>>,
}

fn limits() -> Limits {
    Limits {
        heap_bytes: if cfg!(miri) { 64 << 20 } else { 512 << 20 },
        value_stack_bytes: if cfg!(miri) { 1 << 20 } else { 8 << 20 },
        ..Limits::unlimited()
    }
}

impl Harness {
    /// A page over `html` whose scripts have run and whose load is done.
    fn new(html: &str) -> Result<Harness> {
        let input: Vec<u32> = html.chars().map(u32::from).collect();
        let url: Vec<u32> = URL.chars().map(u32::from).collect();
        let (parsed, _) = parse_real(&NoEnc, &input, url, true, false);
        let clock = TestClock::default();
        let calls = Arc::new(Mutex::new(Vec::new()));
        let mut page = Page::for_document(
            DocumentOptions {
                url: URL.to_owned(),
                encoding: Encoding::Utf8,
                limits: limits(),
                clock: Box::new(clock.clone()),
                hooks: Box::new(Hooks(Arc::clone(&calls))),
            },
            parsed.arena,
        )?;
        assert_eq!(page.run()?, Progress::Loaded);
        Ok(Harness { page, clock, calls })
    }

    fn advance(&self, ms: u64) {
        if let Ok(mut t) = self.clock.0.lock() {
            *t = t.saturating_add(ms.saturating_mul(1000));
        }
    }

    /// The global `r`, as a string.
    fn r(&mut self) -> Result<String> {
        self.eval("r")
    }

    /// An expression's value, as a string.
    fn eval(&mut self, expr: &str) -> Result<String> {
        let realm = self.page.realm().clone();
        let src = format!("var __v = String({expr});");
        self.page.runtime().scope(|scope| {
            scope.eval_script(&realm, clazel_js::Source::new("t.js", &src))?;
            let g = scope.global(&realm)?;
            let v = scope.get(g, Key::Str("__v"))?;
            scope.string_to_string_lossy(v)
        })
    }

    /// Runs a script.
    fn run(&mut self, src: &str) -> Result<()> {
        self.page.run_source("test.js", src)
    }

    /// The node id of the element with `id`.
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
        self.page.click(MouseInput {
            target,
            client_x: 10,
            client_y: 20,
            ..MouseInput::default()
        })
    }

    fn focus(&mut self, id: &str) -> Result<()> {
        let n = self.node(id)?;
        self.page.set_focus(Some(n))
    }

    fn typed(&mut self, key: &str) -> Result<()> {
        self.page.key(KeyInput {
            key: key.to_owned(),
            code: String::new(),
            mods: Modifiers::default(),
            repeat: false,
        })
    }

    fn calls(&self) -> Vec<HookCall> {
        self.calls.lock().map(|v| v.clone()).unwrap_or_default()
    }

    fn navigations(&self) -> Vec<String> {
        self.calls()
            .into_iter()
            .filter_map(|c| match c {
                HookCall::Navigate { url, .. } => Some(url),
                _ => None,
            })
            .collect()
    }

    fn logs(&self) -> Vec<String> {
        self.calls()
            .into_iter()
            .filter_map(|c| match c {
                HookCall::Log(_, t) => Some(t),
                _ => None,
            })
            .collect()
    }
}

type Test = Result<()>;

/// Script that appends the event's type to `r` for every type in `types`, on
/// `target`.
fn log_events(target: &str, types: &[&str]) -> String {
    types
        .iter()
        .map(|t| {
            format!(
                "{target}.addEventListener('{t}', function (e) {{ r += ' {t}@' + (e.target.id || e.target.nodeName) + (e.eventPhase == 2 ? '' : '/' + e.currentTarget.nodeName); }});"
            )
        })
        .collect()
}

// ---- Dispatch ---------------------------------------------------------------

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_click_is_move_down_up_click_and_bubbles() -> Test {
    // UI Events §5.2.4†: the order of a click's events; DOM §2.9† "dispatch":
    // capture, target, bubble.
    let mut h = Harness::new(&format!(
        "<!DOCTYPE html><body><div id=a><span id=b>x</span></div><script>var r = '';{}</script>",
        log_events("document", &["mousemove", "mousedown", "mouseup", "click"])
    ))?;
    h.click_on("b")?;
    assert_eq!(
        h.r()?,
        " mousemove@b/#document mousedown@b/#document mouseup@b/#document click@b/#document"
    );
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn the_click_event_has_its_members() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=a>x</p><script>var r = '';\
         document.getElementById('a').addEventListener('click', function (e) {\
           r = [e instanceof MouseEvent, e instanceof UIEvent, e instanceof Event, e.type, e.isTrusted,\
                e.bubbles, e.cancelable, e.composed, e.clientX, e.clientY, e.button, e.buttons, e.detail,\
                e.view === window, e.relatedTarget, e.ctrlKey, e.shiftKey, e.getModifierState('Shift'),\
                e.which, e.target === e.currentTarget].join();\
         });</script>",
    )?;
    let a = h.node("a")?;
    h.page.click(MouseInput {
        target: a,
        client_x: 7,
        client_y: 9,
        button: 0,
        mods: Modifiers {
            shift: true,
            ..Modifiers::default()
        },
        ..MouseInput::default()
    })?;
    assert_eq!(
        h.r()?,
        "true,true,true,click,true,true,true,true,7,9,0,0,1,true,,false,true,true,1,true"
    );
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_text_node_hit_is_its_element() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=a>text</p><script>var r = '';\
         document.addEventListener('click', function (e) { r = e.target.id; });</script>",
    )?;
    let a = h.node("a")?;
    // The text node is the paragraph's first child, the next id.
    let text = a + 1;
    h.page.click(MouseInput {
        target: text,
        ..MouseInput::default()
    })?;
    assert_eq!(h.r()?, "a");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn capture_stop_propagation_and_stop_immediate_propagation() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><div id=a><p id=b>x</p></div><script>var r = '';\
         var a = document.getElementById('a'), b = document.getElementById('b');\
         a.addEventListener('click', function () { r += 'A-cap '; }, true);\
         b.addEventListener('click', function (e) { r += 'B1 '; e.stopImmediatePropagation(); });\
         b.addEventListener('click', function () { r += 'B2 '; });\
         a.addEventListener('click', function () { r += 'A-bub '; });</script>",
    )?;
    h.click_on("b")?;
    // DOM §2.10† "inner invoke": stopImmediatePropagation ends the target's
    // listeners and the bubbling.
    assert_eq!(h.r()?, "A-cap B1 ");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn stop_propagation_at_the_target_lets_its_other_listeners_run() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><div id=a><p id=b>x</p></div><script>var r = '';\
         var a = document.getElementById('a'), b = document.getElementById('b');\
         b.addEventListener('click', function (e) { r += 'B1 '; e.stopPropagation(); });\
         b.addEventListener('click', function () { r += 'B2 '; });\
         a.addEventListener('click', function () { r += 'A '; });</script>",
    )?;
    h.click_on("b")?;
    assert_eq!(h.r()?, "B1 B2 ");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_passive_listener_cannot_cancel_and_a_wheel_listener_on_the_document_is_passive() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=a>x</p><script>var r = '';\
         document.getElementById('a').addEventListener('click', function (e) { e.preventDefault(); r += e.defaultPrevented; }, {passive: true});\
         document.addEventListener('wheel', function (e) { e.preventDefault(); r += ' w' + e.defaultPrevented; });\
         </script>",
    )?;
    h.click_on("a")?;
    let a = h.node("a")?;
    // DOM §2.7† "default passive value": a `wheel` listener on the document
    // is passive, so `preventDefault()` does nothing and the scroll happens.
    let scrolls = h.page.wheel(WheelInput {
        target: a,
        delta_y: 40.0,
        ..WheelInput::default()
    })?;
    assert!(scrolls);
    assert_eq!(h.r()?, "false wfalse");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_wheel_listener_on_an_element_can_cancel_the_scroll() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=a>x</p><script>var r = '';\
         document.getElementById('a').addEventListener('wheel', function (e) {\
           e.preventDefault(); r = [e instanceof WheelEvent, e.deltaY, e.deltaMode, e.cancelable].join(); });</script>",
    )?;
    let a = h.node("a")?;
    let scrolls = h.page.wheel(WheelInput {
        target: a,
        delta_y: 40.0,
        ..WheelInput::default()
    })?;
    assert!(!scrolls);
    assert_eq!(h.r()?, "true,40,0,true");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_scroll_is_an_event_at_the_document_that_bubbles_to_the_window() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><script>var r = '';\
         document.addEventListener('scroll', function (e) { r += 'D:' + e.bubbles + ' '; });\
         window.addEventListener('scroll', function (e) { r += 'W:' + e.target.nodeName; });</script>",
    )?;
    h.page.scrolled()?;
    assert_eq!(h.r()?, "D:true W:#document");
    Ok(())
}

// ---- Default actions: links ----------------------------------------------------

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn clicking_a_link_navigates_unless_canceled() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><a id=a href='/next?x=1#f'><b id=in>go</b></a>\
         <a id=c href=other>canceled</a><a id=n>no href</a><script>var r = '';\
         document.getElementById('c').addEventListener('click', function (e) { e.preventDefault(); });</script>",
    )?;
    // A click inside the link reaches its activation behavior through the
    // ancestors (DOM §2.9†: an ancestor with it, for a bubbling click).
    h.click_on("in")?;
    assert_eq!(h.navigations(), vec!["https://example.test/next?x=1#f"]);
    h.click_on("c")?;
    h.click_on("n")?;
    assert_eq!(h.navigations().len(), 1);
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_javascript_link_goes_to_the_hooks_for_the_page_to_run() -> Test {
    let mut h = Harness::new("<!DOCTYPE html><body><a id=a href='javascript:void 0'>x</a>")?;
    h.click_on("a")?;
    assert_eq!(h.navigations(), vec!["javascript:void 0"]);
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_synthetic_click_event_follows_a_link_too() -> Test {
    // DOM §2.9†: the activation behavior is not for trusted events only.
    let mut h = Harness::new(
        "<!DOCTYPE html><body><a id=a href=x>l</a><script>var r = '';\
         var e = new MouseEvent('click', {bubbles: true, cancelable: true});\
         r = document.getElementById('a').dispatchEvent(e) + ' ' + e.isTrusted;</script>",
    )?;
    assert_eq!(h.r()?, "true false");
    assert_eq!(h.navigations(), vec!["https://example.test/dir/x"]);
    // A click that does not bubble reaches only the target's own behavior
    // (an inner element's click does not reach the link).
    h.run(
        "document.getElementById('a').innerHTML = '<i id=i>q</i>';\
         document.getElementById('i').dispatchEvent(new MouseEvent('click', {bubbles: false}));",
    )?;
    assert_eq!(h.navigations().len(), 1);
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn the_click_method_clicks_an_element() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><a id=a href=x>l</a><button id=b disabled>d</button><script>var r = '';\
         var a = document.getElementById('a');\
         a.addEventListener('click', function (e) { r += e.isTrusted + ':' + e.detail; });\
         document.getElementById('b').addEventListener('click', function () { r += 'B'; });\
         a.click(); document.getElementById('b').click();</script>",
    )?;
    assert_eq!(h.r()?, "false:0");
    assert_eq!(h.navigations(), vec!["https://example.test/dir/x"]);
    Ok(())
}

// ---- Checkboxes and radios -----------------------------------------------------

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_checkbox_toggles_and_fires_input_and_change() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><form><input id=c type=checkbox name=c value=on></form><script>var r = '';\
         var c = document.getElementById('c');\
         c.addEventListener('click', function () { r += 'click '; });\
         c.addEventListener('input', function (e) { r += 'input:' + e.bubbles + e.composed + ' '; });\
         c.addEventListener('change', function (e) { r += 'change:' + e.bubbles; });</script>",
    )?;
    let c = h.node("c")?;
    assert!(!h.page.control_checked(c)?);
    h.click_on("c")?;
    assert!(h.page.control_checked(c)?);
    assert_eq!(h.r()?, "click input:truetrue change:true");
    h.click_on("c")?;
    assert!(!h.page.control_checked(c)?);
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_canceled_checkbox_click_is_undone() -> Test {
    // HTML §4.10.5.1.15†: legacy-canceled-activation behavior restores the
    // checkedness; no input or change event.
    let mut h = Harness::new(
        "<!DOCTYPE html><body><input id=c type=checkbox checked><script>var r = '';\
         var c = document.getElementById('c');\
         c.addEventListener('click', function (e) { r += 'checked-in-click:' + 'x'; e.preventDefault(); });\
         c.addEventListener('change', function () { r += 'change'; });</script>",
    )?;
    let c = h.node("c")?;
    assert!(h.page.control_checked(c)?);
    h.click_on("c")?;
    assert!(h.page.control_checked(c)?);
    assert_eq!(h.r()?, "checked-in-click:x");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_radio_button_unchecks_the_others_of_its_group() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><form><input id=a type=radio name=g checked>\
         <input id=b type=radio name=g><input id=o type=radio name=other checked></form>",
    )?;
    let (a, b, o) = (h.node("a")?, h.node("b")?, h.node("o")?);
    h.click_on("b")?;
    assert!(!h.page.control_checked(a)?);
    assert!(h.page.control_checked(b)?);
    assert!(h.page.control_checked(o)?);
    Ok(())
}

// ---- Forms --------------------------------------------------------------------

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_submit_button_submits_a_get_form_through_the_proven_algorithm() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><form id=f action='/search?old=1#frag'>\
         <input name=q value='a b'><input type=checkbox name=c checked><input type=checkbox name=d>\
         <button id=go name=go value=1>Go</button></form><script>var r = '';\
         document.getElementById('f').addEventListener('submit', function (e) { r += 'submit:' + e.bubbles + e.cancelable; });</script>",
    )?;
    h.click_on("go")?;
    assert_eq!(h.r()?, "submit:truetrue");
    // The entry list: q, the checked checkbox (value "on"), the submitter.
    assert_eq!(
        h.navigations(),
        vec!["https://example.test/search?q=a+b&c=on&go=1#frag"]
    );
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_canceled_submit_event_stops_the_submission() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><form id=f action=/x><button id=go>Go</button></form><script>\
         document.getElementById('f').addEventListener('submit', function (e) { e.preventDefault(); });</script>",
    )?;
    h.click_on("go")?;
    assert!(h.navigations().is_empty());
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_post_form_sends_its_body() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><form id=f method=post action=/p>\
         <input name=a value=1><button id=go>Go</button></form>",
    )?;
    h.click_on("go")?;
    let posted: Vec<_> = h
        .calls()
        .into_iter()
        .filter_map(|c| match c {
            HookCall::Submit {
                url,
                method,
                content_type,
                body,
            } => Some((
                url,
                method,
                content_type,
                String::from_utf8_lossy(&body).into_owned(),
            )),
            _ => None,
        })
        .collect();
    assert_eq!(
        posted,
        vec![(
            "https://example.test/p".to_owned(),
            "POST".to_owned(),
            "application/x-www-form-urlencoded".to_owned(),
            "a=1".to_owned()
        )]
    );
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_disabled_button_gets_no_click_and_submits_nothing() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><form action=/x><button id=go disabled>Go</button></form><script>var r = '';\
         document.addEventListener('click', function () { r += 'click'; });\
         document.addEventListener('mousedown', function () { r += 'down'; });</script>",
    )?;
    h.click_on("go")?;
    assert_eq!(h.r()?, "");
    assert!(h.navigations().is_empty());
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_reset_button_resets_the_controls() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><form id=f><input id=t value=start><input id=c type=checkbox>\
         <button id=rs type=reset>R</button></form>",
    )?;
    let (t, c) = (h.node("t")?, h.node("c")?);
    h.page.set_focus(Some(t))?;
    for k in ["x", "y"] {
        h.typed(k)?;
    }
    h.click_on("c")?;
    assert_eq!(h.page.control_value(t)?, "startxy");
    assert!(h.page.control_checked(c)?);
    h.click_on("rs")?;
    assert_eq!(h.page.control_value(t)?, "start");
    assert!(!h.page.control_checked(c)?);
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_label_clicks_its_control() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><label id=l for=c><span id=s>text</span></label><input id=c type=checkbox>",
    )?;
    let c = h.node("c")?;
    h.click_on("s")?;
    assert!(h.page.control_checked(c)?);
    Ok(())
}

// ---- Focus ----------------------------------------------------------------------

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_click_moves_focus_with_blur_and_focus_events_in_order() -> Test {
    let mut h = Harness::new(&format!(
        "<!DOCTYPE html><body><input id=a><input id=b><p id=p>x</p><script>var r = '';{}{}</script>",
        log_events(
            "document.getElementById('a')",
            &["focus", "blur", "focusin", "focusout"]
        ),
        log_events(
            "document.getElementById('b')",
            &["focus", "blur", "focusin", "focusout"]
        ),
    ))?;
    h.click_on("a")?;
    assert_eq!(h.r()?, " focus@a focusin@a");
    assert_eq!(h.eval("document.activeElement.id")?, "a");
    h.run("r = '';")?;
    h.click_on("b")?;
    // HTML "focus update steps": blur, focusout at the old; focus, focusin at
    // the new. focus and blur do not bubble; focusin and focusout do.
    assert_eq!(h.r()?, " blur@a focusout@a focus@b focusin@b");
    h.run("r = '';")?;
    // A click on something not focusable removes focus.
    h.click_on("p")?;
    assert_eq!(h.r()?, " blur@b focusout@b");
    assert_eq!(h.eval("document.activeElement.nodeName")?, "BODY");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn focus_events_are_focus_events_with_a_related_target() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><input id=a><input id=b><script>var r = '';\
         document.getElementById('b').addEventListener('focus', function (e) {\
           r = [e instanceof FocusEvent, e.relatedTarget.id, e.bubbles, e.isTrusted].join(); });</script>",
    )?;
    h.click_on("a")?;
    h.click_on("b")?;
    assert_eq!(h.r()?, "true,a,false,true");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn the_focus_and_blur_methods() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><input id=a><div id=d>x</div><div id=t tabindex=-1>y</div><script>var r = '';\
         var a = document.getElementById('a');\
         a.addEventListener('focus', function () { r += 'F'; });\
         a.addEventListener('blur', function () { r += 'B'; });\
         document.getElementById('d').focus();\
         r += document.activeElement.nodeName + ' ';\
         a.focus(); r += document.activeElement.id + ' ';\
         a.blur(); r += document.activeElement.nodeName + ' ';\
         document.getElementById('t').focus(); r += document.activeElement.id + ' ';\
         r += [a.tabIndex, document.getElementById('d').tabIndex, document.getElementById('t').tabIndex].join();</script>",
    )?;
    // A div is not focusable; a tabindex=-1 one is (by script and click).
    assert_eq!(h.r()?, "BODY Fa BBODY t 0,-1,-1");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_canceled_mousedown_does_not_move_focus() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><input id=a><script>\
         document.getElementById('a').addEventListener('mousedown', function (e) { e.preventDefault(); });</script>",
    )?;
    h.click_on("a")?;
    assert_eq!(h.eval("document.activeElement.nodeName")?, "BODY");
    Ok(())
}

// ---- Keys -----------------------------------------------------------------------

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn typing_in_a_text_input_fires_the_key_and_input_events_and_changes_the_value() -> Test {
    let mut h = Harness::new(&format!(
        "<!DOCTYPE html><body><input id=a value=ab><script>var r = '';{}\
         document.getElementById('a').addEventListener('input', function (e) {{\
           r += ' [' + (e instanceof InputEvent) + e.inputType + ':' + e.data + ']'; }});\
         document.getElementById('a').addEventListener('keydown', function (e) {{\
           r += ' key=' + e.key + ',' + e.keyCode + ',' + e.isTrusted; }});</script>",
        log_events(
            "document.getElementById('a')",
            &["keypress", "keyup", "beforeinput", "change"]
        ),
    ))?;
    let a = h.node("a")?;
    h.click_on("a")?;
    h.run("r = '';")?;
    h.typed("c")?;
    assert_eq!(
        h.r()?,
        " key=c,67,true keypress@a beforeinput@a [trueinsertText:c] keyup@a"
    );
    assert_eq!(h.page.control_value(a)?, "abc");
    h.run("r = '';")?;
    h.typed("Backspace")?;
    h.typed("Backspace")?;
    assert_eq!(h.page.control_value(a)?, "a");
    assert!(h.r()?.contains("deleteContentBackward:null"));
    // Leaving the field after a change fires `change` (HTML: "when the user
    // commits the change").
    h.run("r = '';")?;
    h.click_on("a")?;
    h.page.set_focus(None)?;
    assert_eq!(h.r()?, " change@a");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_canceled_keydown_types_nothing() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><input id=a><script>var r = '';\
         document.getElementById('a').addEventListener('keydown', function (e) { e.preventDefault(); });\
         document.getElementById('a').addEventListener('input', function () { r += 'input'; });</script>",
    )?;
    let a = h.node("a")?;
    h.click_on("a")?;
    h.typed("z")?;
    assert_eq!(h.page.control_value(a)?, "");
    assert_eq!(h.r()?, "");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_canceled_beforeinput_changes_nothing() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><input id=a><script>var r = '';\
         document.getElementById('a').addEventListener('beforeinput', function (e) { e.preventDefault(); });</script>",
    )?;
    let a = h.node("a")?;
    h.click_on("a")?;
    h.typed("z")?;
    assert_eq!(h.page.control_value(a)?, "");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn keys_go_to_the_body_without_focus() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><script>var r = '';\
         document.addEventListener('keydown', function (e) { r += e.target.nodeName + e.key; });</script>",
    )?;
    h.typed("q")?;
    assert_eq!(h.r()?, "BODYq");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn tab_moves_focus_in_sequential_navigation_order() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><input id=a><input id=b tabindex=2><input id=c tabindex=1>\
         <a id=l href=x>l</a><input id=n tabindex=-1><input id=d disabled>",
    )?;
    let mut seen = Vec::new();
    for _ in 0..5 {
        h.typed("Tab")?;
        seen.push(h.eval("document.activeElement.id || document.activeElement.nodeName")?);
    }
    // Positive tabindex first (1, then 2), then the rest in tree order; -1
    // and disabled are left out; it wraps.
    assert_eq!(seen, ["c", "b", "a", "l", "c"]);
    h.page.key(KeyInput {
        key: "Tab".to_owned(),
        mods: Modifiers {
            shift: true,
            ..Modifiers::default()
        },
        ..KeyInput::default()
    })?;
    assert_eq!(h.eval("document.activeElement.id")?, "l");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn enter_on_a_focused_link_follows_it_and_in_a_text_input_submits_the_form() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><a id=l href=/go>l</a>\
         <form action=/s><input id=q name=q><input type=submit id=go value=Send name=btn></form>",
    )?;
    h.focus("l")?;
    h.typed("Enter")?;
    assert_eq!(h.navigations(), vec!["https://example.test/go"]);
    h.focus("q")?;
    h.typed("x")?;
    h.typed("Enter")?;
    // Implicit submission clicks the default button, which is a submitter,
    // so its name and value are in the entry list.
    assert_eq!(
        h.navigations().last().map(String::as_str),
        Some("https://example.test/s?q=x&btn=Send")
    );
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn implicit_submission_without_a_button_needs_at_most_one_text_field() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><form action=/one><input id=a name=a></form>\
         <form action=/two><input id=b name=b><input id=c name=c></form>",
    )?;
    h.focus("a")?;
    h.typed("Enter")?;
    assert_eq!(h.navigations(), vec!["https://example.test/one?a="]);
    h.focus("b")?;
    h.typed("Enter")?;
    assert_eq!(h.navigations().len(), 1);
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn space_clicks_a_focused_button_on_keyup() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><button id=b type=button>b</button><script>var r = '';\
         var b = document.getElementById('b');\
         ['keydown','keyup','click'].forEach(function (t) { b.addEventListener(t, function () { r += t + ' '; }); });</script>",
    )?;
    h.focus("b")?;
    h.typed(" ")?;
    assert_eq!(h.r()?, "keydown keyup click ");
    Ok(())
}

// ---- Event handlers -------------------------------------------------------------

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn event_handler_content_attributes_run_with_event_and_this() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=a onclick=\"r = this.id + ':' + event.type\">x</p><script>var r = '';</script>",
    )?;
    h.click_on("a")?;
    assert_eq!(h.r()?, "a:click");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn the_idl_attribute_reads_the_compiled_attribute_and_the_setter_replaces_it() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=a onclick=\"r += 'attr '\">x</p><div id=none>y</div><script>var r = '';\
         var a = document.getElementById('a');\
         var before = typeof a.onclick;\
         var nul = document.getElementById('none').onclick === null;\
         var same = a.onclick === a.onclick;</script>",
    )?;
    assert_eq!(h.eval("before + nul + same")?, "functiontruetrue");
    h.run("a.onclick = function () { r += 'idl '; };")?;
    h.click_on("a")?;
    assert_eq!(h.r()?, "idl ");
    h.run("a.onclick = null; r = '';")?;
    h.click_on("a")?;
    assert_eq!(h.r()?, "");
    // A non-object clears it too ([LegacyTreatNonObjectAsNull]).
    h.run("a.onclick = function () { r += 'x'; }; a.onclick = 3;")?;
    assert_eq!(h.eval("a.onclick")?, "null");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_handler_has_the_place_it_was_first_set_among_the_listeners() -> Test {
    // HTML §8.1.8.1†: activating adds the listener once; setting again
    // changes the value and not the place.
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=a onclick=\"r += 'attr '\">x</p><script>var r = '';\
         var a = document.getElementById('a');\
         a.addEventListener('click', function () { r += 'L1 '; });\
         a.onclick = function () { r += 'idl '; };\
         a.addEventListener('click', function () { r += 'L2 '; });\
         a.onclick = function () { r += 'idl2 '; };</script>",
    )?;
    h.click_on("a")?;
    // The attribute made the handler first (at parse time).
    assert_eq!(h.r()?, "idl2 L1 L2 ");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_handler_set_by_script_is_placed_where_it_was_set() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=a>x</p><script>var r = '';\
         var a = document.getElementById('a');\
         a.addEventListener('click', function () { r += 'L1 '; });\
         a.onclick = function () { r += 'H '; };\
         a.addEventListener('click', function () { r += 'L2 '; });</script>",
    )?;
    h.click_on("a")?;
    assert_eq!(h.r()?, "L1 H L2 ");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn returning_false_cancels_the_event() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><a id=a href=/x onclick=\"return false\">x</a><a id=b href=/y onclick=\"return true\">y</a>",
    )?;
    h.click_on("a")?;
    assert!(h.navigations().is_empty());
    h.click_on("b")?;
    assert_eq!(h.navigations(), vec!["https://example.test/y"]);
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_handler_attribute_changed_by_script_is_seen() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=a onclick=\"r += '1'\">x</p><script>var r = '';\
         var a = document.getElementById('a');</script>",
    )?;
    h.click_on("a")?;
    h.run("a.setAttribute('onclick', \"r += '2'\");")?;
    h.click_on("a")?;
    h.run("a.removeAttribute('onclick');")?;
    h.click_on("a")?;
    h.run("var d = document.createElement('i'); d.setAttribute('onclick', \"r += 'new'\"); a.appendChild(d); d.click();")?;
    assert_eq!(h.r()?, "12new");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_syntax_error_in_a_handler_attribute_is_reported_and_the_handler_is_null() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=a onclick=\"if (\">x</p><p id=b onclick=\"}); r = 'injected'; (function () {\">y</p><script>var r = '';</script>",
    )?;
    h.click_on("a")?;
    h.click_on("b")?;
    assert_eq!(h.r()?, "");
    assert_eq!(h.eval("document.getElementById('a').onclick")?, "null");
    assert_eq!(h.eval("document.getElementById('b').onclick")?, "null");
    assert_eq!(
        h.logs()
            .iter()
            .filter(|l| l.contains("SyntaxError"))
            .count(),
        2
    );
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_handler_that_throws_is_reported_and_dispatch_goes_on() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=a onclick=\"throw new Error('boom')\">x</p><script>var r = '';\
         document.getElementById('a').addEventListener('click', function () { r += 'after'; });</script>",
    )?;
    h.click_on("a")?;
    assert_eq!(h.r()?, "after");
    assert!(h.logs().iter().any(|l| l.contains("boom")));
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn body_event_handler_attributes_are_the_windows() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body onload=\"r += 'load '\" onclick=\"r += 'bodyclick '\" onscroll=\"r += 'scroll '\">\
         <p id=a>x</p><script>var r = '';\
         var seen = [typeof window.onload, document.body.onload === window.onload, typeof document.body.onclick, window.onclick === null].join();</script>",
    )?;
    // `load` has fired already (run() reached "the end"), with the handler
    // the parser made.
    assert_eq!(h.eval("seen")?, "function,true,function,true");
    h.click_on("a")?;
    h.page.scrolled()?;
    assert_eq!(h.r()?, "load bodyclick scroll ");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn event_handler_idl_attributes_exist_on_window_document_and_elements() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=a>x</p><script>var r = '';\
         var p = document.getElementById('a');\
         var names = ['onclick', 'onkeydown', 'oninput', 'onfocus', 'onblur', 'onwheel', 'onscroll', 'onsubmit', 'onchange', 'onmousedown'];\
         var ok = names.every(function (n) { return (n in window) && (n in document) && (n in p) && window[n] === null && p[n] === null; });\
         window.onwheel = function () { r += 'w'; };\
         document.onkeydown = function () { r += 'k'; };</script>",
    )?;
    assert_eq!(h.eval("ok")?, "true");
    h.typed("a")?;
    assert_eq!(h.r()?, "k");
    let a = h.node("a")?;
    h.page.wheel(WheelInput {
        target: a,
        ..WheelInput::default()
    })?;
    assert_eq!(h.r()?, "kw");
    Ok(())
}

// ---- User activation ------------------------------------------------------------

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn user_activation_follows_html_6_4() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=a>x</p><script>var r = '';\
         var ua = navigator.userActivation;\
         document.getElementById('a').addEventListener('mousedown', function () { r += 'down:' + ua.isActive; });\
         document.getElementById('a').addEventListener('click', function () { r += ' click:' + ua.isActive + ua.hasBeenActive; });</script>",
    )?;
    assert_eq!(
        h.eval("ua.isActive + ',' + ua.hasBeenActive")?,
        "false,false"
    );
    assert!(!h.page.has_transient_activation()?);
    h.advance(1000);
    h.click_on("a")?;
    // The notification is before mousedown's dispatch (as browsers do).
    assert_eq!(h.r()?, "down:true click:truetrue");
    assert!(h.page.has_transient_activation()?);
    // The transient activation lasts 5 seconds; the sticky one stays.
    h.advance(4999);
    assert_eq!(h.eval("ua.isActive")?, "true");
    h.advance(1);
    assert_eq!(
        h.eval("ua.isActive + ',' + ua.hasBeenActive")?,
        "false,true"
    );
    assert!(h.page.has_sticky_activation()?);
    // Consuming.
    h.click_on("a")?;
    assert!(h.page.consume_user_activation()?);
    assert!(!h.page.consume_user_activation()?);
    assert_eq!(
        h.eval("ua.isActive + ',' + ua.hasBeenActive")?,
        "false,true"
    );
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn a_key_is_an_activation_triggering_input_event_except_escape() -> Test {
    let mut h =
        Harness::new("<!DOCTYPE html><body><script>var ua = navigator.userActivation;</script>")?;
    h.typed("Escape")?;
    assert_eq!(h.eval("ua.hasBeenActive")?, "false");
    h.typed("a")?;
    assert_eq!(h.eval("ua.isActive")?, "true");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn script_made_events_do_not_notify_user_activation() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><p id=a>x</p><script>\
         document.getElementById('a').dispatchEvent(new MouseEvent('mousedown', {bubbles: true}));\
         document.getElementById('a').click();</script>",
    )?;
    assert_eq!(h.eval("navigator.userActivation.hasBeenActive")?, "false");
    Ok(())
}

// ---- Event constructors ---------------------------------------------------------

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn the_ui_event_constructors_and_their_dictionaries() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><script>\
         var m = new MouseEvent('mouseup', {clientX: 3, clientY: 4, screenX: 5, button: 2, buttons: 4, altKey: true, bubbles: true, relatedTarget: document.body, view: window, detail: 2});\
         var k = new KeyboardEvent('keydown', {key: 'a', code: 'KeyA', repeat: true, ctrlKey: true, location: 1, keyCode: 65});\
         var f = new FocusEvent('focus', {relatedTarget: document.body});\
         var i = new InputEvent('input', {data: 'x', inputType: 'insertText', isComposing: true});\
         var w = new WheelEvent('wheel', {deltaX: 1.5, deltaY: -2, deltaMode: 1});\
         var u = new UIEvent('x', {detail: 9, view: window});\
         var r = [m.clientX, m.clientY, m.screenX, m.button, m.buttons, m.altKey, m.bubbles, m.relatedTarget === document.body, m.view === window, m.detail, m.isTrusted,\
                  k.key, k.code, k.repeat, k.ctrlKey, k.location, k.keyCode, k instanceof UIEvent,\
                  f.relatedTarget === document.body, i.data, i.inputType, i.isComposing,\
                  w.deltaX, w.deltaY, w.deltaMode, w instanceof MouseEvent, WheelEvent.DOM_DELTA_LINE, u.detail, u.view === window,\
                  KeyboardEvent.DOM_KEY_LOCATION_NUMPAD].join();</script>",
    )?;
    assert_eq!(
        h.r()?,
        "3,4,5,2,4,true,true,true,true,2,false,a,KeyA,true,true,1,65,true,true,x,insertText,true,1.5,-2,1,true,1,9,true,3"
    );
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn init_methods_set_the_members() -> Test {
    let mut h = Harness::new(
        "<!DOCTYPE html><body><script>\
         var e = new MouseEvent('click');\
         e.initMouseEvent('mouseover', true, true, window, 3, 1, 2, 3, 4, true, false, true, false, 1, document.body);\
         var u = new UIEvent('a'); u.initUIEvent('b', true, false, window, 5);\
         var k = new KeyboardEvent('a'); k.initKeyboardEvent('keyup', true, true, window, 'Q', 2, true, false, true, false);\
         var r = [e.type, e.bubbles, e.cancelable, e.detail, e.screenX, e.clientY, e.ctrlKey, e.altKey, e.shiftKey, e.button, e.relatedTarget === document.body,\
                  u.type, u.bubbles, u.detail, k.type, k.key, k.location, k.ctrlKey, k.shiftKey].join();</script>",
    )?;
    assert_eq!(
        h.r()?,
        "mouseover,true,true,3,1,4,true,false,true,1,true,b,true,5,keyup,Q,2,true,true"
    );
    Ok(())
}
