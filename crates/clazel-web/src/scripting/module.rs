//! Module scripts (HTML §8.1.4†, "Fetching scripts" and "Creating scripts"
//! for module scripts; §8.1.5† "HostLoadImportedModule"; ECMA-262 §16.2.1.5†
//! for the module record's Load, Link and Evaluate, which are the engine's).
//!
//! <https://html.spec.whatwg.org/multipage/webappapis.html#fetch-an-external-module-script-graph>,
//! <https://html.spec.whatwg.org/multipage/webappapis.html#fetch-a-single-module-script>,
//! <https://html.spec.whatwg.org/multipage/webappapis.html#creating-a-javascript-module-script>,
//! <https://html.spec.whatwg.org/multipage/webappapis.html#run-a-module-script>,
//! <https://html.spec.whatwg.org/multipage/webappapis.html#hostloadimportedmodule>.
//!
//! **What runs today.** The HTML half is here: the module map, fetching a
//! single module script (with its MIME type check), resolving a specifier,
//! HostLoadImportedModule, the descendants' fetch and link, and running a
//! module script with its error reporting. The engine half is not:
//! `clazel-js`'s `parse_module`, `load_requested_modules`, `link`,
//! `evaluate_module` and every promise operation return
//! `Error::NotImplemented` until the VM has module records and promises
//! (item 7.8). So every module script today ends at "create a JavaScript
//! module script" with an engine report, and its element's result is null
//! (an `error` event, as for a script that failed to load). Dynamic
//! `import()` and top-level `await` need the same engine pieces, and
//! HostLoadImportedModule below is what they will call.
//!
//! Modelling choices (each listed):
//! - **Import maps are Phase 8**: "resolve a module specifier" is "resolve a
//!   URL-like module specifier" alone; a bare specifier is a `TypeError`.
//! - **Module types**: only "javascript" (JSON and CSS modules need the
//!   engine's synthetic modules; listed as not yet).
//! - **The module map** is keyed by URL alone, the module type being
//!   "javascript" for every entry.
//! - **"Wait in parallel until that entry's value changes"** (fetch a single
//!   module script, step 5) is a list of waiters on the entry, run when the
//!   fetch completes.

use clazel_js::{
    Callable, Error, ErrorKind, LoadPayload, Module, ModuleRequest, Referrer, Result, Scope, Source,
};

use super::dom;
use super::element::{ScriptError, ScriptResult, mark_as_ready, report};
use super::encodings::is_javascript_response;
use super::state::{
    FetchFor, PageState, PendingImport, Report, Request, RequestKind, Response, realm, state,
};

/// The embedder data a script or module carries (its `Source`'s host
/// data): the base URL that a specifier in it resolves against (HTML's
/// script "base URL").
pub(crate) struct ScriptMeta {
    /// The base URL, serialized.
    pub(crate) base_url: String,
}

/// A module script (HTML §8.1.4.1† "module script").
#[derive(Clone)]
pub(crate) struct ModuleScript {
    /// Its module record; `None` if creating it failed.
    pub(crate) record: Option<Module>,
    /// "error to rethrow".
    pub(crate) error: Option<ScriptError>,
    /// The name reports give.
    pub(crate) name: String,
}

/// A module map entry (HTML §8.1.?† "module map").
pub(crate) enum ModuleMapEntry {
    /// "fetching".
    Fetching,
    /// The fetch is done: a module script, or null.
    Done(Option<ModuleScript>),
}

/// HTML "resolve a module specifier" without import maps: "resolve a
/// URL-like module specifier" (step 1: a specifier starting with "/", "./"
/// or "../" is parsed against the base URL; step 2: otherwise it must parse
/// as an absolute URL), or `None` (the caller throws a `TypeError`).
pub(crate) fn resolve_module_specifier(specifier: &str, base: &str) -> Option<String> {
    let base_url = dom::parse_url(&dom::cps(base), None);
    if specifier.starts_with('/') || specifier.starts_with("./") || specifier.starts_with("../") {
        return dom::parse_url(&dom::cps(specifier), base_url.as_ref()).map(|u| dom::serialize(&u));
    }
    dom::parse_url(&dom::cps(specifier), None).map(|u| dom::serialize(&u))
}

/// HTML §8.1.4.3† "create a JavaScript module script" from `source` with
/// `base` as its base URL, named `name` in reports, then (for an inline
/// script, §8.1.4.2† "fetch an inline module script graph" step 3) "fetch
/// the descendants of and link" it. The result is the element's.
pub(crate) fn create_module_script(
    scope: &mut Scope<'_>,
    source: &[u32],
    base: &str,
    name: &str,
) -> Result<ScriptResult> {
    let script = create_javascript_module_script(scope, source, base, name)?;
    descendants_and_link(scope, script)
}

/// "Create a JavaScript module script": steps 1 to 7 set up the script,
/// 8. "Let result be ParseModule(source, settings's realm, script)", 9. on
/// errors set its parse error and error to rethrow, 11. else its record.
fn create_javascript_module_script(
    scope: &mut Scope<'_>,
    source: &[u32],
    base: &str,
    name: &str,
) -> Result<ModuleScript> {
    let text = dom::text(source);
    let realm = realm(scope)?;
    let meta = ScriptMeta {
        base_url: base.to_owned(),
    };
    let parsed = scope.parse_module(
        &realm,
        Source::new(name, &text).with_host_defined(Box::new(meta)),
    );
    Ok(match parsed {
        Ok(record) => ModuleScript {
            record: Some(record),
            error: None,
            name: name.to_owned(),
        },
        Err(Error::Thrown(e)) => ModuleScript {
            record: None,
            error: Some(ScriptError::Thrown(e)),
            name: name.to_owned(),
        },
        Err(e @ (Error::Terminated | Error::OutOfMemory)) => return Err(e),
        Err(other) => ModuleScript {
            record: None,
            error: Some(ScriptError::Engine(other.to_string())),
            name: name.to_owned(),
        },
    })
}

/// HTML §8.1.4.2† "fetch the descendants of and link" `script`, giving the
/// result onComplete would be given. Step 2: a script with no record runs
/// onComplete with itself (its error to rethrow set). Steps 5 to 7:
/// LoadRequestedModules, and on its fulfilment Link. The promise is
/// read, not awaited: every import the host is asked for in it is
/// finished before the next task here, except one still being fetched, and
/// that waits in the module map (see the module docs); until the engine
/// has promises this ends at its first call.
fn descendants_and_link(scope: &mut Scope<'_>, script: ModuleScript) -> Result<ScriptResult> {
    let Some(record) = script.record.clone() else {
        // 2. "If record is null, then: set moduleScript's error to rethrow to
        //    moduleScript's parse error; run onComplete given moduleScript."
        // An engine refusal has nothing to rethrow: reported, and the
        // result is null (an `error` event at the element).
        return Ok(match &script.error {
            Some(ScriptError::Engine(message)) => {
                state(scope)?.reports.push(Report::Engine {
                    script: script.name.clone(),
                    error: message.clone(),
                });
                ScriptResult::Null
            }
            _ => ScriptResult::Module(script),
        });
    };
    // 5. "Let loadingPromise be record.LoadRequestedModules(state)."
    let loaded = scope.load_requested_modules(&record).and_then(|promise| {
        scope
            .promise_state(promise)
            .map(|s| matches!(s, clazel_js::PromiseState::Fulfilled(_)))
    });
    match loaded {
        // 6. "Upon fulfillment of loadingPromise: 1. Perform record.Link() ...
        //    If this throws an exception, then set result's error to rethrow
        //    to that exception. 2. Run onComplete given moduleScript."
        Ok(true) => match scope.link(&record) {
            Ok(()) => Ok(ScriptResult::Module(script)),
            Err(Error::Thrown(e)) => Ok(ScriptResult::Module(ModuleScript {
                error: Some(ScriptError::Thrown(e)),
                ..script
            })),
            Err(e) => engine_null(scope, &script.name, e),
        },
        // 7. "Upon rejection of loadingPromise: ... run onComplete given null."
        Ok(false) => Ok(ScriptResult::Null),
        Err(e) => engine_null(scope, &script.name, e),
    }
}

/// An engine error where the standard has none: reported, and the result
/// is null. Termination and out of memory pass through.
fn engine_null(scope: &mut Scope<'_>, name: &str, error: Error) -> Result<ScriptResult> {
    match error {
        Error::Terminated | Error::OutOfMemory => Err(error),
        other => {
            state(scope)?.reports.push(Report::Engine {
                script: name.to_owned(),
                error: other.to_string(),
            });
            Ok(ScriptResult::Null)
        }
    }
}

/// HTML §8.1.4.2† "fetch an external module script graph" given `url` for
/// the script element `el`: step 2, "fetch a single module script", whose
/// completion ([`fetched`]) fetches the descendants and links, then marks
/// `el` as ready.
pub(crate) fn fetch_external_module_graph(
    st: &mut PageState,
    el: usize,
    generation: u64,
    url: String,
    parser_inserted: bool,
) {
    st.module_waiters
        .entry(url.clone())
        .or_default()
        .push((el, generation));
    fetch_single_module_script(st, url, parser_inserted);
}

/// "Fetch a single module script", steps 5 to 13, for an entry not yet in
/// the module map: mark it "fetching" and ask the embedder. An entry that
/// is fetching already gains only the waiter its caller added; one that is
/// done is answered by the caller ([`answer_waiters`]).
fn fetch_single_module_script(st: &mut PageState, url: String, parser_inserted: bool) {
    match st.module_map.get(&url) {
        // 5. "If moduleMap[(url, moduleType)] is "fetching", wait".
        Some(ModuleMapEntry::Fetching) => {}
        // 6. "If moduleMap[(url, moduleType)] exists, run onComplete given
        //    moduleMap[(url, moduleType)], and return." The waiters run on
        //    the next call of `answer_waiters`.
        Some(ModuleMapEntry::Done(_)) => {
            st.ready_modules.push(url);
        }
        None => {
            // 7. "Set moduleMap[(url, moduleType)] to "fetching"."
            st.module_map.insert(url.clone(), ModuleMapEntry::Fetching);
            // 8. to 13. The request: destination "script", mode "cors".
            let id = st.next_fetch;
            st.next_fetch = st.next_fetch.saturating_add(1);
            st.fetches.insert(id, FetchFor::Module { url: url.clone() });
            st.outgoing.push(Request {
                id,
                url,
                kind: RequestKind::ModuleScript,
                cors: true,
                parser_inserted,
            });
        }
    }
}

/// "Fetch a single module script" step 13's processResponseConsumeBody for
/// the module map entry `url`: set the entry, then answer everything
/// waiting on it.
pub(crate) fn fetched(
    scope: &mut Scope<'_>,
    url: String,
    response: Option<Response>,
) -> Result<()> {
    let entry = match response {
        // 13.1. "If ... bodyBytes is null or failure; or response's status is
        //       not an ok status, then set moduleMap[(url, moduleType)] to
        //       null, run onComplete given null".
        None => None,
        Some(r) if !r.ok => None,
        Some(r) => {
            // 13.2. "Let mimeType be the result of extracting a MIME type from
            //       response's header list."
            // 13.6.2. "If mimeType is a JavaScript MIME type and moduleType is
            //         "javascript-or-wasm", then set moduleScript to the result
            //         of creating a JavaScript module script given sourceText,
            //         settingsObject, response's URL, and options."
            if is_javascript_response(&r.content_type) {
                // 13.6.1. "Let sourceText be the result of UTF-8 decoding
                //         bodyBytes."
                let source: Vec<u32> = String::from_utf8_lossy(&r.body)
                    .chars()
                    .map(u32::from)
                    .collect();
                let response_url = r.url.clone().unwrap_or_else(|| url.clone());
                Some(create_javascript_module_script(
                    scope,
                    &source,
                    &response_url,
                    &response_url,
                )?)
            } else {
                None
            }
        }
    };
    // 13.7. "Set moduleMap[(url, moduleType)] to moduleScript, and run
    //       onComplete given moduleScript."
    let st = state(scope)?;
    st.module_map
        .insert(url.clone(), ModuleMapEntry::Done(entry));
    st.ready_modules.push(url);
    answer_waiters(scope)
}

/// Runs the onComplete steps of everything waiting on module map entries
/// that are done: script elements (fetch the descendants, link, mark as
/// ready) and the engine's imports (FinishLoadingImportedModule).
pub(crate) fn answer_waiters(scope: &mut Scope<'_>) -> Result<()> {
    loop {
        let st = state(scope)?;
        let Some(url) = st.ready_modules.pop() else {
            return Ok(());
        };
        let script = match st.module_map.get(&url) {
            Some(ModuleMapEntry::Done(s)) => s.clone(),
            _ => continue,
        };
        let elements = st.module_waiters.remove(&url).unwrap_or_default();
        let imports = st.import_waiters.remove(&url).unwrap_or_default();
        let generation = st.generation;
        for (el, prepared_in) in elements {
            if prepared_in != generation {
                continue;
            }
            // "fetch an external module script graph" step 2: "1. If result is
            // null, run onComplete given null ... 2. Fetch the descendants of
            // and link result".
            let result = match script.clone() {
                None => ScriptResult::Null,
                Some(s) => descendants_and_link(scope, s)?,
            };
            mark_as_ready(scope, el, result)?;
        }
        for import in imports {
            finish_import(scope, import.payload, script.as_ref())?;
        }
    }
}

/// HostLoadImportedModule's onSingleFetchComplete (steps 1 to 5):
/// FinishLoadingImportedModule with the module, its parse error, or a new
/// `TypeError` for a fetch that failed.
fn finish_import(
    scope: &mut Scope<'_>,
    payload: LoadPayload,
    script: Option<&ModuleScript>,
) -> Result<()> {
    let completion = match script {
        // 2. "If moduleScript is null, then set completion to ... a new
        //    TypeError".
        None => Err(scope.new_exception(ErrorKind::TypeError, "the module could not be fetched")?),
        // 3. "Otherwise, if moduleScript's parse error is not null, then ...
        //    throw parseError".
        Some(ModuleScript {
            error: Some(ScriptError::Thrown(e)),
            ..
        }) => Err(e.clone()),
        Some(ModuleScript {
            record: Some(record),
            ..
        }) => Ok(record.clone()),
        Some(_) => {
            Err(scope.new_exception(ErrorKind::TypeError, "the module could not be created")?)
        }
    };
    // 5. "Perform FinishLoadingImportedModule(referrer, moduleRequest,
    //    payload, completion)."
    scope.finish_loading_imported_module(payload, completion)
}

/// HTML §8.1.5.?† HostLoadImportedModule(referrer, moduleRequest, loadState,
/// payload), from the engine's hook: resolve the specifier against the
/// referrer's base URL (step 6 and 8), fail with the resolution's
/// `TypeError` (step 9), else fetch a single imported script (step 14) and
/// finish the load when the module map entry is done.
pub(crate) fn host_load_imported_module(
    st: &mut PageState,
    scope: &mut Scope<'_>,
    referrer: Referrer<'_>,
    request: &ModuleRequest,
    payload: LoadPayload,
) -> Result<()> {
    // 3. to 6. The referencing script's base URL; for a realm (code from
    //    `eval` or `Function`), the settings object's API base URL, which is
    //    the document base URL.
    let base = match scope.host_defined(referrer) {
        Ok(Some(data)) => data
            .downcast_ref::<ScriptMeta>()
            .map(|m| m.base_url.clone()),
        _ => None,
    };
    let base = base
        .or_else(|| dom::document_base_url(st.doc.arena()).map(|u| dom::serialize(&u)))
        .unwrap_or_default();
    // 8. "Let url be the result of resolving a module specifier given
    //    referencingScript and moduleRequest.[[Specifier]], catching any
    //    exceptions."
    let Some(url) = resolve_module_specifier(&request.specifier, &base) else {
        // 9. FinishLoadingImportedModule with the resolution error.
        let error = scope.new_exception(
            ErrorKind::TypeError,
            "the module specifier could not be resolved",
        )?;
        return scope.finish_loading_imported_module(payload, Err(error));
    };
    // 14. "Fetch a single imported script": the module map.
    if let Some(ModuleMapEntry::Done(script)) = st.module_map.get(&url) {
        let script = script.clone();
        return finish_import(scope, payload, script.as_ref());
    }
    st.import_waiters
        .entry(url.clone())
        .or_default()
        .push(PendingImport { payload });
    fetch_single_module_script(st, url, false);
    Ok(())
}

/// HTML §8.1.4.4† "run a module script" `script`, with
/// preventErrorReporting false.
pub(crate) fn run_module_script(scope: &mut Scope<'_>, script: &ModuleScript) -> Result<()> {
    let st = state(scope)?;
    st.running = st.running.saturating_add(1);
    // 6. "If script's error to rethrow is not null, then set
    //    evaluationPromise to a promise rejected with script's error to
    //    rethrow." It is reported (step 8) at once.
    let outcome: Result<()> = match (&script.record, &script.error) {
        (_, Some(ScriptError::Thrown(e))) => Err(Error::Thrown(e.clone())),
        (_, Some(ScriptError::Engine(m))) => {
            state(scope)?.reports.push(Report::Engine {
                script: script.name.clone(),
                error: m.clone(),
            });
            Ok(())
        }
        // 7. "Set evaluationPromise to record.Evaluate()." 8. "Upon
        //    rejection of evaluationPromise with reason, report an
        //    exception given by reason": a reaction that reports.
        (Some(record), None) => scope.evaluate_module(record).and_then(|promise| {
            let name = script.name.clone();
            let on_rejected = scope.function("", 1, Callable::Function, move |scope, args| {
                let reason = scope.persist(args.get(0));
                report(
                    scope,
                    &name,
                    Error::Thrown(clazel_js::Exception::from_handle(reason)),
                )?;
                Ok(scope.undefined())
            })?;
            scope
                .promise_then(promise, None, Some(on_rejected))
                .map(|_| ())
        }),
        (None, None) => Ok(()),
    };
    let st = state(scope)?;
    st.running = st.running.saturating_sub(1);
    match outcome {
        Ok(()) => {}
        Err(e @ (Error::Terminated | Error::OutOfMemory)) => return Err(e),
        Err(e) => report(scope, &script.name, e)?,
    }
    // 9. "Clean up after running script with settings."
    super::element::clean_up_after_running_script(scope)
}
