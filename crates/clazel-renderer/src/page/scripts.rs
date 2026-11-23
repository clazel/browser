//! A document's scripts in the renderer (phase-7.md items 7.15 and 7.17):
//! `clazel-web`'s page over the parsed tree, its fetches mapped to the
//! kernel's `FetchScript`, its hooks to the kernel's messages, and the event
//! loop that gives it timers.
//!
//! Tier 0 glue, tested and not proven. What each part is:
//! - **Fetches.** The page asks for an external script ([`Request`]); the
//!   renderer sends `FetchScript` with its absolute URL and the request's id
//!   (ids are the page's own, from 1). The kernel answers with
//!   `ScriptResponse`, `ScriptBody` frames and `ScriptEnd`, or
//!   `ScriptFailed`; the renderer joins them and gives the page one
//!   [`Response`]. The response carries no status, so a response is "ok"
//!   as a style sheet's is; `ScriptFailed` is a network error. A response
//!   over `MAX_BODY` is a failure.
//! - **Hooks** ([`Hooks`]): `location.href = …` sends `Navigate`
//!   (`Navigate` has no "replace" bit: `location.replace` is the same
//!   message); `pushState` and `replaceState` send `UpdateUrl`;
//!   `document.cookie` and `localStorage` are Phase 2's messages, sent by
//!   script now, each waiting for its answer ([`super::link`]); `console`
//!   goes to standard error, which the host reports; history traversal has no
//!   message yet and does nothing.
//! - **`javascript:` URLs.** A `Navigate` the page would send for one (a
//!   `location` set to it) is not sent: the page runs it itself, after the
//!   script that set it returns (HTML's navigate, "evaluate a javascript:
//!   URL"). So does a click on a link that has one, and the user never sees
//!   a `Navigate` for it. The string such a script returns would replace the
//!   document in a browser; `clazel-js`'s scripts have no completion value
//!   in this tree's engine, so it never does here.
//! - **The loop** ([`Scripts::tick`]): the caller runs it whenever it has
//!   control; the page's own clock says what is due. A page whose engine
//!   fails (the page was terminated, or ran out of memory) stops running
//!   scripts and goes on showing its document.
//!
//! What is not done: `FetchScript` is the only script message, so `fetch()`
//! and `XMLHttpRequest` (7.16's `Fetch`) have no natives; a script that a
//! script inserts is not run (`clazel-web`'s `bound.rs` says why); the
//! renderer's frame clock is the end of a message, not a timer, unless the
//! socket has a read timeout.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::Instant;

use clazel_dom::exec::Arena;
use clazel_encoding::labels::spec::Encoding;
use clazel_ipc::message::codec::Msg;
use clazel_js::Limits;
use clazel_web::page::input::{KeyInput, MouseInput, WheelInput};
use clazel_web::page::{LogLevel, PageHooks};
use clazel_web::scripting::time::Clock;
use clazel_web::scripting::{
    DocumentOptions, NetworkError, Page, Progress, Report, Request, Response,
};

use super::link::{LinkHandle, lock};
use crate::{MAX_BODY, RunError};

/// Whether a URL, as the page's hooks hold it (parsed and serialized: the
/// scheme lowercased), is a `javascript:` URL.
pub fn is_javascript_url(url: &str) -> bool {
    clazel_web::scripting::javascript_url::is_javascript_url(url)
}

/// The engine's limits for a page: the renderer's heap and stack (item 7.19
/// states them; these are generous stand-ins, never unlimited).
pub fn limits() -> Limits {
    Limits {
        heap_bytes: 512 << 20,
        value_stack_bytes: 8 << 20,
        ..Limits::unlimited()
    }
}

/// What the page asks of the renderer.
struct Hooks {
    link: LinkHandle,
    /// `javascript:` URLs a script navigated to, for the loop to run.
    js: Arc<Mutex<Vec<String>>>,
    start: Instant,
}

impl Hooks {
    fn send(&self, m: &Msg) {
        let mut link = lock(&self.link);
        if let Err(e) = link.send(m) {
            link.note_failure(&e);
        }
    }
}

fn is_cookie_answer(m: &Msg) -> bool {
    matches!(m, Msg::CookieValue { .. } | Msg::Error { .. })
}

fn is_storage_answer(m: &Msg) -> bool {
    matches!(m, Msg::StorageValue { .. } | Msg::Error { .. })
}

fn is_length_answer(m: &Msg) -> bool {
    matches!(m, Msg::StorageLengthValue { .. } | Msg::Error { .. })
}

fn is_barrier(m: &Msg) -> bool {
    matches!(m, Msg::StorageLengthValue { .. })
}

fn text(bytes: Vec<u8>) -> String {
    String::from_utf8_lossy(&bytes).into_owned()
}

impl PageHooks for Hooks {
    fn navigate(&mut self, url: &str, _replace: bool) {
        if is_javascript_url(url) {
            if let Ok(mut js) = self.js.lock() {
                js.push(url.to_owned());
            }
            return;
        }
        self.send(&Msg::Navigate {
            url: url.as_bytes().to_vec(),
        });
    }

    /// A form submitted with a body (item 7.14, HTML §4.10.21.3†): the
    /// kernel's `Submit`. A message the frame cannot hold is not sent (the
    /// kernel's limit is `max_submit_body`; a submission over it is dropped
    /// like a failed request, not a protocol error).
    fn submit(&mut self, url: &str, method: &str, content_type: &str, body: &[u8]) {
        if method == "GET" {
            self.navigate(url, false);
            return;
        }
        let head = url
            .len()
            .saturating_add(method.len())
            .saturating_add(content_type.len());
        if head > 8192 || body.len() > clazel_ipc::frame::spec::MAX_FRAME - 8192 - 64 {
            eprintln!("clazel-renderer: a form submission is too large to send");
            return;
        }
        self.send(&Msg::Submit {
            url: url.as_bytes().to_vec(),
            method: method.as_bytes().to_vec(),
            content_type: content_type.as_bytes().to_vec(),
            body: body.to_vec(),
        });
    }

    fn update_url(&mut self, url: &str, replace: bool) {
        self.send(&Msg::UpdateUrl {
            replace,
            url: url.as_bytes().to_vec(),
        });
    }

    fn log(&mut self, level: LogLevel, text: &str) {
        let tag = match level {
            LogLevel::Log => "log",
            LogLevel::Debug => "debug",
            LogLevel::Warn => "warn",
            LogLevel::Error => "error",
        };
        eprintln!("clazel-renderer: console.{tag}: {text}");
    }

    fn now_ms(&mut self) -> f64 {
        self.start.elapsed().as_secs_f64() * 1000.0
    }

    fn cookie_get(&mut self) -> String {
        match lock(&self.link).call(&Msg::CookieGet, is_cookie_answer) {
            Some(Msg::CookieValue { cookie_string }) => text(cookie_string),
            _ => String::new(),
        }
    }

    fn cookie_set(&mut self, cookie: &str) {
        self.send(&Msg::CookieSet {
            cookie_string: cookie.as_bytes().to_vec(),
        });
    }

    fn storage_get(&mut self, key: &str) -> Option<String> {
        let ask = Msg::StorageGetItem {
            key: key.as_bytes().to_vec(),
        };
        match lock(&self.link).call(&ask, is_storage_answer) {
            Some(Msg::StorageValue { value }) => value.map(text),
            _ => None,
        }
    }

    fn storage_set(&mut self, key: &str, value: &str) -> bool {
        // The kernel answers a refused `setItem` with an `Error` and a
        // successful one with nothing, so a length request after it marks
        // where its answer would have been (Phase 2's barrier).
        let set = Msg::StorageSetItem {
            key: key.as_bytes().to_vec(),
            value: value.as_bytes().to_vec(),
        };
        let mut link = lock(&self.link);
        if let Err(e) = link.send(&set) {
            link.note_failure(&e);
            return false;
        }
        match link.call(&Msg::StorageLength, is_length_answer) {
            Some(Msg::Error { .. }) => {
                let _ = link.wait_for(is_barrier);
                false
            }
            _ => true,
        }
    }

    fn storage_remove(&mut self, key: &str) {
        self.send(&Msg::StorageRemoveItem {
            key: key.as_bytes().to_vec(),
        });
    }

    fn storage_clear(&mut self) {
        self.send(&Msg::StorageClear);
    }

    fn storage_key(&mut self, index: u64) -> Option<String> {
        match lock(&self.link).call(&Msg::StorageKey { index }, is_storage_answer) {
            Some(Msg::StorageValue { value }) => value.map(text),
            _ => None,
        }
    }

    fn storage_length(&mut self) -> u64 {
        match lock(&self.link).call(&Msg::StorageLength, is_length_answer) {
            Some(Msg::StorageLengthValue { length }) => length,
            _ => 0,
        }
    }
}

/// A script's response as it arrives: the content type, and the body so far.
struct Arriving {
    content_type: Vec<u8>,
    body: Vec<u8>,
}

/// A document's scripts.
pub struct Scripts {
    page: Page,
    link: LinkHandle,
    js: Arc<Mutex<Vec<String>>>,
    arriving: HashMap<u64, Arriving>,
    /// The page's engine failed: it runs no more scripts.
    dead: bool,
    /// A `javascript:` URL ran since the flag was last taken.
    js_ran: bool,
}

impl Scripts {
    /// Hosts the parsed document `arena` (decoded with `encoding`, at `url`)
    /// with `clock` as its clock. Nothing runs until [`Scripts::start`].
    ///
    /// # Errors
    /// The engine could not start.
    pub fn new(
        url: &str,
        encoding: Encoding,
        arena: Arena,
        link: LinkHandle,
        clock: Box<dyn Clock>,
    ) -> Result<Scripts, RunError> {
        let js = Arc::new(Mutex::new(Vec::new()));
        let hooks = Hooks {
            link: Arc::clone(&link),
            js: Arc::clone(&js),
            start: Instant::now(),
        };
        let page = Page::for_document(
            DocumentOptions {
                url: url.to_owned(),
                encoding,
                limits: limits(),
                clock,
                hooks: Box::new(hooks),
            },
            arena,
        )
        .map_err(|e| RunError::Engine(e.to_string()))?;
        Ok(Scripts {
            page,
            link,
            js,
            arriving: HashMap::new(),
            dead: false,
            js_ran: false,
        })
    }

    /// A page for a user script (kind 1): an empty document at `url`.
    ///
    /// # Errors
    /// The engine could not start.
    pub fn empty(url: &[u8], link: LinkHandle, clock: Box<dyn Clock>) -> Result<Scripts, RunError> {
        let url_cps: Vec<u32> = String::from_utf8_lossy(url)
            .chars()
            .map(u32::from)
            .collect();
        let arena = crate::pipeline::parse_empty(&url_cps);
        Scripts::new(
            &String::from_utf8_lossy(url),
            Encoding::Utf8,
            arena,
            link,
            clock,
        )
    }

    /// Runs `source` as a classic script (the body of a user script).
    ///
    /// # Errors
    /// The socket failed.
    pub fn run_source(&mut self, source: &str) -> Result<(), RunError> {
        let r = self.page.run_source("user script", source);
        self.guard(r);
        self.after()
    }

    /// Runs the page's scripts as far as they can go now, and sends the
    /// fetches they asked for. Returns whether anything ran.
    ///
    /// # Errors
    /// The socket failed.
    pub fn start(&mut self) -> Result<bool, RunError> {
        let progress = self.page.run();
        let ran = self.guard(progress.map(|_: Progress| true));
        self.after()?;
        Ok(ran)
    }

    /// Keeps a page alive across an error of its engine: the page is marked
    /// dead (it runs no more scripts) and the error is reported to the host.
    fn guard<T: Default>(&mut self, r: clazel_js::Result<T>) -> T {
        match r {
            Ok(v) => v,
            Err(e) => {
                eprintln!("clazel-renderer: the page's scripts stopped: {e}");
                self.dead = true;
                T::default()
            }
        }
    }

    /// After a script ran: the fetches it asked for are sent, the
    /// `javascript:` URLs it navigated to are run, and a failure of the
    /// socket is reported.
    fn after(&mut self) -> Result<(), RunError> {
        for _ in 0..16 {
            if self.dead {
                break;
            }
            let requests = self.page.take_requests();
            let requests = self.guard(requests);
            for Request { id, url, .. } in requests {
                let ask = Msg::FetchScript {
                    request: id,
                    url: url.into_bytes(),
                };
                lock(&self.link).send(&ask)?;
            }
            let urls: Vec<String> = self
                .js
                .lock()
                .map(|mut v| core::mem::take(&mut *v))
                .unwrap_or_default();
            if urls.is_empty() {
                break;
            }
            for url in urls {
                let r = self.page.evaluate_javascript_url(&url);
                self.guard(r.map(|_| ()));
                self.js_ran = true;
            }
        }
        for report in self.reports() {
            eprintln!("clazel-renderer: {report}");
        }
        match lock(&self.link).failure() {
            Some(kind) => Err(RunError::Io(std::io::Error::from(kind))),
            None => Ok(()),
        }
    }

    /// Runs the event loop at the page clock's time: the timers and tasks
    /// that are due. Returns whether any ran.
    ///
    /// # Errors
    /// The socket failed.
    pub fn tick(&mut self) -> Result<bool, RunError> {
        if self.dead {
            return Ok(false);
        }
        let r = self.page.run_event_loop();
        let ran = self.guard(r) > 0;
        self.after()?;
        Ok(ran)
    }

    /// "Update the rendering": the animation frame callbacks run. Returns
    /// whether any did.
    ///
    /// # Errors
    /// The socket failed.
    pub fn update_the_rendering(&mut self) -> Result<bool, RunError> {
        if self.dead {
            return Ok(false);
        }
        let r = self.page.update_the_rendering();
        let ran = self.guard(r);
        self.after()?;
        Ok(ran)
    }

    /// A link the page drew, clicked: a `javascript:` URL is the page's own
    /// to run. Returns whether it ran.
    ///
    /// # Errors
    /// The socket failed.
    pub fn follow_javascript_url(&mut self, url: &str) -> Result<bool, RunError> {
        if self.dead {
            return Ok(false);
        }
        let r = self.page.evaluate_javascript_url(url);
        self.guard(r.map(|_| ()));
        self.after()?;
        Ok(true)
    }

    /// The user's click on the element `target` of the document (item 7.14):
    /// the mouse events and the default actions, through the page's hooks (a
    /// followed link is a `Navigate`, a `javascript:` URL is run by `after`).
    /// Returns whether the page's script ran (a listener or handler was
    /// called, or a `javascript:` URL was run): only then can the page have
    /// changed.
    ///
    /// # Errors
    /// The socket failed.
    pub fn click(&mut self, input: MouseInput) -> Result<bool, RunError> {
        if self.dead {
            return Ok(false);
        }
        let before = self.page.listener_calls().unwrap_or(0);
        let r = self.page.click(input);
        self.guard(r);
        self.after()?;
        Ok(self.page.listener_calls().unwrap_or(0) != before || core::mem::take(&mut self.js_ran))
    }

    /// A key typed, with focus where it is (item 7.14). Returns whether the
    /// page's script ran, as [`Scripts::click`] does.
    ///
    /// # Errors
    /// The socket failed.
    pub fn key(&mut self, input: KeyInput) -> Result<bool, RunError> {
        if self.dead {
            return Ok(false);
        }
        let before = self.page.listener_calls().unwrap_or(0);
        let r = self.page.key(input);
        self.guard(r);
        self.after()?;
        Ok(self.page.listener_calls().unwrap_or(0) != before || core::mem::take(&mut self.js_ran))
    }

    /// A wheel turn over an element (item 7.14). Returns whether the default
    /// action, scrolling, is to happen (a listener did not cancel it), and
    /// whether any listener ran.
    ///
    /// # Errors
    /// The socket failed.
    pub fn wheel(&mut self, input: WheelInput) -> Result<(bool, bool), RunError> {
        if self.dead {
            return Ok((true, false));
        }
        let before = self.page.listener_calls().unwrap_or(0);
        // A page whose engine failed scrolls as a page without scripts does.
        let scrolls = match self.page.wheel(input) {
            Ok(scrolls) => scrolls,
            Err(e) => {
                self.guard::<()>(Err(e));
                true
            }
        };
        self.after()?;
        let ran = self.page.listener_calls().unwrap_or(0) != before;
        Ok((scrolls, ran))
    }

    /// The viewport scrolled: the `scroll` event (item 7.14).
    ///
    /// # Errors
    /// The socket failed.
    pub fn scrolled(&mut self) -> Result<bool, RunError> {
        if self.dead {
            return Ok(false);
        }
        let before = self.page.listener_calls().unwrap_or(0);
        let r = self.page.scrolled();
        self.guard(r);
        self.after()?;
        Ok(self.page.listener_calls().unwrap_or(0) != before)
    }

    /// The kernel's `ScriptResponse`.
    pub fn response(&mut self, request: u64, content_type: Vec<u8>) {
        self.arriving.insert(
            request,
            Arriving {
                content_type,
                body: Vec::new(),
            },
        );
    }

    /// The kernel's `ScriptBody`; a body over the limit fails the fetch.
    ///
    /// # Errors
    /// The socket failed.
    pub fn body(&mut self, request: u64, bytes: &[u8]) -> Result<bool, RunError> {
        let over = match self.arriving.get_mut(&request) {
            Some(a) if a.body.len().saturating_add(bytes.len()) <= MAX_BODY => {
                a.body.extend_from_slice(bytes);
                false
            }
            Some(_) => true,
            None => false,
        };
        if over {
            self.arriving.remove(&request);
            return self.answer(request, Err(NetworkError));
        }
        Ok(false)
    }

    /// The kernel's `ScriptEnd`. Returns whether scripts ran.
    ///
    /// # Errors
    /// The socket failed.
    pub fn end(&mut self, request: u64) -> Result<bool, RunError> {
        match self.arriving.remove(&request) {
            Some(a) => self.answer(
                request,
                Ok(Response {
                    url: None,
                    ok: true,
                    content_type: a.content_type,
                    body: a.body,
                }),
            ),
            None => Ok(false),
        }
    }

    /// The kernel's `ScriptFailed`. Returns whether scripts ran.
    ///
    /// # Errors
    /// The socket failed.
    pub fn failed(&mut self, request: u64) -> Result<bool, RunError> {
        self.arriving.remove(&request);
        self.answer(request, Err(NetworkError))
    }

    fn answer(
        &mut self,
        request: u64,
        response: Result<Response, NetworkError>,
    ) -> Result<bool, RunError> {
        if self.dead {
            return Ok(false);
        }
        let r = self.page.fetched(request, response);
        let ran = self.guard(r.map(|_| true));
        self.after()?;
        Ok(ran)
    }

    /// The page clock's time at which the next timer is due, if one is.
    pub fn next_wake_ms(&mut self) -> Option<u64> {
        if self.dead {
            return None;
        }
        self.page.next_wake_ms().ok().flatten()
    }

    /// The page clock's time, in milliseconds.
    pub fn now_ms(&mut self) -> u64 {
        self.page.now_ms().unwrap_or(0)
    }

    /// Calls `f` with the document's tree.
    pub fn with_document<R>(&mut self, f: impl FnOnce(&Arena) -> R) -> Option<R> {
        self.page.with_document(f).ok()
    }

    /// The reports of exceptions since the last call, as text.
    pub fn reports(&mut self) -> Vec<String> {
        self.page
            .take_reports()
            .unwrap_or_default()
            .into_iter()
            .map(|r| match r {
                Report::Exception {
                    script,
                    name,
                    message,
                } => format!("uncaught {name}: {message} ({script})"),
                Report::Engine { script, error } => format!("{script}: {error}"),
            })
            .collect()
    }
}
