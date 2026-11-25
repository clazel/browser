//! HTML integration, the script half (phase-7.md item 7.15): a document
//! parsed with the scripting flag on, its `script` elements prepared and
//! run as the parser reaches them (HTML §4.12.1.1† "prepare the script
//! element", acting on Phase 4's `ScriptReady`), `document.write` and
//! `document.writeln` as edits of the input stream at the insertion point,
//! `document.open` and `document.close`, module scripts as far as the
//! engine goes, `javascript:` URLs, and `performance.now()`.
//!
//! [`Page`] is one document and its scripts, over one `clazel-js`
//! [`Runtime`] with the page's [`state::PageHost`] as its host. The parser
//! is `clazel-treebuilder`'s incremental driver; everything here talks to
//! the engine through `clazel-js`'s public API only.
//!
//! **Tasks.** Each call of [`Page::run`], [`Page::fetched`] and
//! [`Page::evaluate_javascript_url`] is one task of HTML's event loop (HTML
//! §8.1.7†), and "spin the event loop until ..." is a return to the caller
//! with [`Progress::Waiting`]: the page records what it waits for, and the
//! task that brings it (a fetch's answer) continues from there. The
//! embedder owns the loop and the clock (phase-7.md, "The engine as a
//! library"); `clazel-web`'s [`crate::event_loop`] is where the renderer's
//! loop will drive these calls from, with timers, which this module does not
//! use. A task queued by the standard on the DOM manipulation or networking
//! task source here (an `error` event for a script with no `src` value, the
//! inline module script's "mark as ready") is run at once, at the end of
//! the step that queues it, which is a task ordering the standard permits
//! for a single task source only; it is listed.
//!
//! **Fetches** are the embedder's: a script element with a `src` asks for a
//! [`Request`] ([`Page::take_requests`]), and the answer comes back to
//! [`Page::fetched`]. The renderer turns them into the kernel's
//! `FetchScript` and its `ScriptResponse`/`ScriptBody`/`ScriptEnd`.
//!
//! **Events** the page fires ([`FiredEvent`]) are dispatched to the
//! listeners and `on*` event handlers of the page's bindings, in order, after
//! the step that fired them; the user's input is [`input`]'s UI events.
//!
//! **What the engine does not do yet** is reported, not hidden: a script
//! the compiler or interpreter cannot run yet gives a [`Report::Engine`],
//! and the page goes on with the next one, as it would after an exception.

mod bound;
pub(crate) use bound::ensure_bindings;
pub mod dom;
mod element;
mod encodings;
pub mod globals;
pub mod input;
pub mod javascript_url;
mod module;
mod parser;
pub mod state;
pub mod time;
mod write;

use clazel_dom::exec::Arena;
use clazel_encoding::labels::spec::Encoding;
use clazel_js::{Config, Error, Limits, Realm, RealmOptions, Result, Runtime, Scope};
use clazel_treebuilder::exec::incremental::Incremental;

pub use bound::DocumentOptions;
use element::ScriptResult;
use state::{Doc, EndPhase, FetchFor, PageState, arena, state};
pub use state::{
    EventTarget, FiredEvent, NetworkError, Readiness, Report, Request, RequestKind, Response,
};
use time::Clock;

/// How a page is made.
pub struct PageOptions {
    /// The document's URL, serialized.
    pub url: String,
    /// The encoding the document was decoded with (the document's
    /// encoding, the fallback for its classic scripts).
    pub encoding: Encoding,
    /// Whether that encoding's confidence is tentative (a `<meta charset>`
    /// may then ask to change it: [`Progress::Reparse`]).
    pub tentative: bool,
    /// The engine's limits (phase-7.md 7.19: the embedder's choice).
    pub limits: Limits,
    /// The monotonic clock `performance.now()` reads.
    pub clock: Box<dyn Clock>,
}

/// Where a page's loading stands after a task.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Progress {
    /// Waiting for fetches ([`Page::take_requests`]), or for a script-created
    /// parser's input (`document.close`).
    Waiting,
    /// "The end" has run: the `load` event has fired.
    Loaded,
    /// The parser asked to change the encoding (HTML §13.2.3.4†): the
    /// document is to be decoded again with this encoding, confidence
    /// certain, in a new page.
    Reparse(Encoding),
}

/// One document and its scripts.
pub struct Page {
    rt: Runtime,
    realm: Realm,
}

impl Page {
    /// A page for the document whose decoded text is `input` (code points),
    /// parsed with the scripting flag on. Nothing runs until [`Page::run`].
    pub fn new(options: PageOptions, input: &[u32]) -> Result<Page> {
        let PageOptions {
            url,
            encoding,
            tentative,
            limits,
            mut clock,
        } = options;
        let parser = Incremental::new(dom::cps(&url), true, tentative, input, true);
        let time_origin_us = clock.now_us();
        let st = PageState::new(
            Doc::Parsing(Box::new(parser)),
            encoding,
            tentative,
            clock,
            time_origin_us,
        );
        // The host is the bindings' page (item 7.12) with this state in it;
        // its own tree stays empty until the parser is done (`state`).
        let mut host =
            crate::page::Page::new(Arena::new(Vec::new()), &url, Box::new(crate::page::NoHooks));
        host.script = Some(Box::new(st));
        let mut rt = Runtime::new(Config::new(limits), host)?;
        let realm = rt.scope(|scope| -> Result<Realm> {
            let realm = scope.create_realm(RealmOptions::default())?;
            state(scope)?.realm = Some(realm.clone());
            globals::install(scope, &realm)?;
            Ok(realm)
        })?;
        Ok(Page { rt, realm })
    }

    /// The engine, for an embedder that adds globals of its own (item
    /// 7.12's bindings; tests' logging functions). A
    /// [`Page::for_document`] page installs its bindings first, so that
    /// what the embedder adds comes after them, as it always has; if that
    /// fails, the first script reports it.
    pub fn runtime(&mut self) -> &mut Runtime {
        let _ = self.rt.scope(bound::ensure_bindings);
        &mut self.rt
    }

    /// The realm the page's scripts run in.
    pub fn realm(&self) -> &Realm {
        &self.realm
    }

    /// Runs the page as far as it can go now: the parser, the scripts it
    /// reaches, and "the end".
    pub fn run(&mut self) -> Result<Progress> {
        self.rt.scope(advance)
    }

    /// The requests made since the last call, for the embedder to fetch.
    pub fn take_requests(&mut self) -> Result<Vec<Request>> {
        self.rt
            .scope(|scope| Ok(core::mem::take(&mut state(scope)?.outgoing)))
    }

    /// The answer to the request `id`: the task that "fetch a classic
    /// script" or "fetch a single module script" queues when the response's
    /// body is in, then the page runs on. An unknown id is ignored.
    pub fn fetched(
        &mut self,
        id: u64,
        response: core::result::Result<Response, NetworkError>,
    ) -> Result<Progress> {
        self.rt.scope(|scope| {
            let Some(purpose) = state(scope)?.fetches.remove(&id) else {
                return advance(scope);
            };
            let response = response.ok();
            match purpose {
                FetchFor::Classic {
                    element,
                    url,
                    generation,
                    encoding,
                } => {
                    let result = classic_result(scope, response, encoding, url)?;
                    if state(scope)?.generation == generation {
                        element::mark_as_ready(scope, element, result)?;
                    }
                }
                FetchFor::Module { url } => module::fetched(scope, url, response)?,
            }
            advance(scope)
        })
    }

    /// Evaluates a `javascript:` URL in the page (a link it drew, followed):
    /// see [`javascript_url`]. The string result, if any, is the body of
    /// the document to navigate to. A URL of another scheme does nothing.
    pub fn evaluate_javascript_url(&mut self, url: &str) -> Result<Option<String>> {
        self.rt.scope(|scope| {
            let result = javascript_url::evaluate(scope, url)?;
            advance(scope)?;
            Ok(result)
        })
    }

    /// Calls `f` with the document's tree.
    pub fn with_document<R>(&mut self, f: impl FnOnce(&Arena) -> R) -> Result<R> {
        self.rt.scope(|scope| Ok(f(arena(scope)?)))
    }

    /// The reports since the last call.
    pub fn take_reports(&mut self) -> Result<Vec<Report>> {
        self.rt
            .scope(|scope| Ok(core::mem::take(&mut state(scope)?.reports)))
    }

    /// The events fired since the last call.
    pub fn take_events(&mut self) -> Result<Vec<FiredEvent>> {
        self.rt.scope(|scope| {
            let st = state(scope)?;
            st.dispatched = 0;
            Ok(core::mem::take(&mut st.events))
        })
    }

    /// The document's current readiness.
    pub fn readiness(&mut self) -> Result<Readiness> {
        self.rt.scope(|scope| Ok(state(scope)?.readiness))
    }
}

/// The page's loop within one task: the parser while it can run (resuming
/// a blocked tokenizer when its script is ready), then "the end".
fn advance(scope: &mut Scope<'_>) -> Result<Progress> {
    let progress = advance_parser(scope)?;
    bound::flush_events(scope)?;
    Ok(progress)
}

/// [`advance`] without the events it fired being dispatched.
fn advance_parser(scope: &mut Scope<'_>) -> Result<Progress> {
    // Each pass runs the tokenizer (which returns only when it can go no
    // further), resumes a blocked tokenizer, or moves "the end" on; a pass
    // that does none of these returns. The bound guards against a bug.
    for _ in 0..1_000_000u32 {
        let st = state(scope)?;
        if let Some(encoding) = st.reparse {
            return Ok(Progress::Reparse(encoding));
        }
        match st.end {
            EndPhase::Parsing => {
                if st.blocked_on.is_some() {
                    parser::resume_blocked(scope)?;
                    if state(scope)?.blocked_on.is_some() {
                        return Ok(Progress::Waiting);
                    }
                }
                match parser::run_tokenizer(scope)? {
                    parser::Run::InsertionPoint => return Ok(Progress::Waiting),
                    parser::Run::Paused => {
                        // At nesting level zero the flag is already false
                        // (end tag "script" step 8); clear it for safety.
                        state(scope)?.parser_pause = false;
                    }
                    parser::Run::Blocked | parser::Run::Stopped => {}
                }
                let st = state(scope)?;
                if st.end == EndPhase::Parsing && st.doc.parser().is_none() && st.walk.is_none() {
                    return Ok(Progress::Loaded);
                }
            }
            EndPhase::Deferred | EndPhase::AwaitAsync => {
                if parser::continue_the_end(scope)? {
                    return Ok(Progress::Waiting);
                }
            }
            EndPhase::Loaded => return Ok(Progress::Loaded),
        }
    }
    Err(Error::NotImplemented("the page's loop did not settle"))
}

/// "Fetch a classic script" step 4's processResponseConsumeBody: null for a
/// network error, a status that is not ok, or a body this browser cannot
/// decode; else "create a classic script" from the decoded body, named by
/// the response's URL.
fn classic_result(
    scope: &mut Scope<'_>,
    response: Option<Response>,
    encoding: Encoding,
    request_url: String,
) -> Result<ScriptResult> {
    let Some(r) = response else {
        return Ok(ScriptResult::Null);
    };
    if !r.ok {
        return Ok(ScriptResult::Null);
    }
    let Some(source) = encodings::decode_script(&r.body, &r.content_type, encoding) else {
        return Ok(ScriptResult::Null);
    };
    // "create a classic script given sourceText, settingsObject,
    // response's URL, options, mutedErrors": the response's URL is the
    // script's base URL and its name.
    let name = r.url.clone().unwrap_or(request_url);
    Ok(ScriptResult::Classic(element::create_classic_script(
        scope,
        &source,
        name.clone(),
        name,
    )?))
}
