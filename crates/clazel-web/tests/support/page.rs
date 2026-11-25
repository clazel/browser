//! A test embedder for `clazel_web::scripting::Page`: an in-memory server
//! for its fetches, a `log(text)` global that records what scripts say, a
//! fixed clock, and the html5lib tree format of the document.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use clazel_encoding::labels::spec::Encoding;
use clazel_js::{Callable, Error, Key, Limits, Result};
use clazel_web::scripting::time::Clock;
use clazel_web::scripting::{
    FiredEvent, NetworkError, Page, PageOptions, Progress, Report, Request, Response,
};

#[path = "../../../clazel-treebuilder/tests/support/dump.rs"]
mod dump;

/// The URL the test documents have.
pub const URL: &str = "https://example.test/dir/page.html";

/// A clock the test sets.
#[derive(Clone, Default)]
pub struct TestClock(pub Arc<Mutex<u64>>);

impl Clock for TestClock {
    fn now_us(&mut self) -> u64 {
        self.0.lock().map_or(0, |v| *v)
    }
}

/// One file the server has.
#[derive(Clone)]
pub struct File {
    pub content_type: &'static str,
    pub body: String,
}

/// The test embedder.
pub struct Harness {
    pub page: Page,
    pub log: Arc<Mutex<Vec<String>>>,
    pub clock: TestClock,
    /// What the server answers, by absolute URL.
    pub files: BTreeMap<String, File>,
    /// Requests not answered yet, in the order made.
    pub pending: Vec<Request>,
    /// Every request seen, in order.
    pub requested: Vec<String>,
    pub reports: Vec<Report>,
    pub events: Vec<FiredEvent>,
}

/// Limits for the tests: generous, smaller under Miri.
pub fn limits() -> Limits {
    if cfg!(miri) {
        Limits {
            heap_bytes: 64 << 20,
            value_stack_bytes: 1 << 20,
            ..Limits::unlimited()
        }
    } else {
        Limits {
            heap_bytes: 512 << 20,
            value_stack_bytes: 8 << 20,
            ..Limits::unlimited()
        }
    }
}

impl Harness {
    /// A page for `html` at [`URL`], with `log` installed, not yet run.
    pub fn new(html: &str) -> Result<Harness> {
        Harness::with(html, Encoding::Utf8, false)
    }

    /// As [`Harness::new`], with the document's encoding and confidence.
    pub fn with(html: &str, encoding: Encoding, tentative: bool) -> Result<Harness> {
        Harness::at(URL, html, encoding, tentative)
    }

    /// A page for `html` at `url`.
    pub fn at(url: &str, html: &str, encoding: Encoding, tentative: bool) -> Result<Harness> {
        let clock = TestClock::default();
        let input: Vec<u32> = html.chars().map(u32::from).collect();
        let mut page = Page::new(
            PageOptions {
                url: url.to_owned(),
                encoding,
                tentative,
                limits: limits(),
                clock: Box::new(clock.clone()),
            },
            &input,
        )?;
        let log = Arc::new(Mutex::new(Vec::new()));
        let sink = Arc::clone(&log);
        let realm = page.realm().clone();
        page.runtime().scope(|scope| {
            let global = scope.global(&realm)?;
            let f = scope.function("log", 1, Callable::Function, move |scope, args| {
                let s = scope.to_string(args.get(0))?;
                let s = scope.string_to_string_lossy(s)?;
                if let Ok(mut l) = sink.lock() {
                    l.push(s);
                }
                Ok(scope.undefined())
            })?;
            scope.set(global, Key::from("log"), f)
        })?;
        Ok(Harness {
            page,
            log,
            clock,
            files: BTreeMap::new(),
            pending: Vec::new(),
            requested: Vec::new(),
            reports: Vec::new(),
            events: Vec::new(),
        })
    }

    /// Serves `body` as JavaScript at `path` relative to [`URL`]'s directory.
    pub fn script(&mut self, path: &str, body: &str) {
        self.files.insert(
            format!("https://example.test/dir/{path}"),
            File {
                content_type: "text/javascript",
                body: body.to_owned(),
            },
        );
    }

    /// What `log` has been given so far.
    pub fn logged(&self) -> Vec<String> {
        self.log.lock().map(|l| l.clone()).unwrap_or_default()
    }

    fn collect(&mut self) -> Result<()> {
        let new = self.page.take_requests()?;
        for r in &new {
            self.requested.push(r.url.clone());
        }
        self.pending.extend(new);
        self.reports.extend(self.page.take_reports()?);
        self.events.extend(self.page.take_events()?);
        Ok(())
    }

    /// Runs the page once (one task), collecting its requests.
    pub fn run(&mut self) -> Result<Progress> {
        let p = self.page.run()?;
        self.collect()?;
        Ok(p)
    }

    /// Answers the pending request for `url` (a 404 if the server has no
    /// such file), as one task.
    pub fn answer(&mut self, url: &str) -> Result<Progress> {
        let Some(i) = self.pending.iter().position(|r| r.url == url) else {
            return Err(Error::WrongType("no pending request for that URL"));
        };
        let request = self.pending.remove(i);
        let response = match self.files.get(&request.url) {
            Some(f) => Ok(Response {
                url: None,
                ok: true,
                content_type: f.content_type.as_bytes().to_vec(),
                body: f.body.as_bytes().to_vec(),
            }),
            None => Ok(Response {
                url: None,
                ok: false,
                content_type: Vec::new(),
                body: Vec::new(),
            }),
        };
        let p = self.page.fetched(request.id, response)?;
        self.collect()?;
        Ok(p)
    }

    /// Fails the pending request for `url` with a network error.
    pub fn fail(&mut self, url: &str) -> Result<Progress> {
        let Some(i) = self.pending.iter().position(|r| r.url == url) else {
            return Err(Error::WrongType("no pending request for that URL"));
        };
        let request = self.pending.remove(i);
        let p = self.page.fetched(request.id, Err(NetworkError))?;
        self.collect()?;
        Ok(p)
    }

    /// Runs the page, answering every request in the order made, until it
    /// has loaded (or nothing is left to answer).
    pub fn load(&mut self) -> Result<Progress> {
        let mut p = self.run()?;
        while p != Progress::Loaded {
            let Some(next) = self.pending.first().map(|r| r.url.clone()) else {
                return Ok(p);
            };
            p = self.answer(&next)?;
        }
        Ok(p)
    }

    /// The document in the html5lib tree format.
    pub fn tree(&mut self) -> Result<String> {
        self.page.with_document(|a| dump::dump_children(a, 0))
    }

    /// Calls the global function `name` with no arguments, if there is one
    /// (a stand-in for the load event's dispatch to `onload`). `Ok(false)`
    /// if it threw; an exception is reported in `reports`.
    pub fn call_global(&mut self, name: &str) -> Result<bool> {
        let realm = self.page.realm().clone();
        let mut thrown = Vec::new();
        let ok = self.page.runtime().scope(|scope| {
            let global = scope.global(&realm)?;
            let f = scope.get(global, Key::from(name))?;
            if !scope.is_callable(f) {
                return Ok(true);
            }
            let this = scope.undefined();
            match scope.call(f, this, &[]) {
                Ok(_) => Ok(true),
                Err(Error::Thrown(e)) => {
                    let r = scope.report(&e)?;
                    thrown.push(Report::Exception {
                        script: name.to_owned(),
                        name: r.name,
                        message: r.message,
                    });
                    Ok(false)
                }
                Err(e) => {
                    thrown.push(Report::Engine {
                        script: name.to_owned(),
                        error: e.to_string(),
                    });
                    Ok(false)
                }
            }
        })?;
        self.reports.extend(thrown);
        Ok(ok)
    }

    /// The names of the events fired, in order, with their targets.
    pub fn event_names(&self) -> Vec<String> {
        self.events
            .iter()
            .map(|e| format!("{:?}:{}", e.target, e.name))
            .collect()
    }

    /// A global's value as a string (`undefined` if absent).
    pub fn global(&mut self, name: &str) -> Result<String> {
        let realm = self.page.realm().clone();
        self.page.runtime().scope(|scope| {
            let global = scope.global(&realm)?;
            let v = scope.get(global, Key::from(name))?;
            let s = scope.to_string(v)?;
            scope.string_to_string_lossy(s)
        })
    }
}

/// The exception reports' messages, as `name: message`.
pub fn exceptions(reports: &[Report]) -> Vec<String> {
    reports
        .iter()
        .filter_map(|r| match r {
            Report::Exception { name, message, .. } => Some(format!("{name}: {message}")),
            Report::Engine { .. } => None,
        })
        .collect()
}

/// The engine reports' errors.
pub fn engine(reports: &[Report]) -> Vec<String> {
    reports
        .iter()
        .filter_map(|r| match r {
            Report::Engine { error, .. } => Some(error.clone()),
            Report::Exception { .. } => None,
        })
        .collect()
}
