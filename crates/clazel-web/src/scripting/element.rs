//! The `script` element's processing model (HTML §4.12.1.1†): "prepare the
//! script element", "mark as ready", "execute the script element"; and
//! "create a classic script" and "run a classic script" (HTML §8.1.4.3† and
//! §8.1.4.4†).
//!
//! <https://html.spec.whatwg.org/multipage/scripting.html#prepare-the-script-element>,
//! <https://html.spec.whatwg.org/multipage/webappapis.html#creating-a-classic-script>,
//! <https://html.spec.whatwg.org/multipage/webappapis.html#run-a-classic-script>.
//! Section numbers carry phase-7.md's mark †: written from memory, not read
//! at a pinned commit. Steps are numbered as the living standard numbers them
//! at the time of writing and quoted where short, so a reader can check them
//! against the text.
//!
//! Modelling choices (each listed):
//! - **One document.** "Parser document", "preparation-time document" and
//!   "node document" are all the page's one `Document`; what tells a
//!   document before `document.open` from the one after is its generation
//!   ([`super::state::PageState::generation`]), so step 16 and "execute the
//!   script element" step 2 compare generations.
//! - **Parser-inserted** means "prepared from the parser's `ScriptReady`".
//!   The tree builder does not report creating a script element (its "set
//!   the element's parser document" at the start tag), and no DOM API can
//!   move or create one yet (item 7.12), so a script element first seen at
//!   its `ScriptReady` is one the parser created and has not left.
//! - **Not modelled, each a no-op here:** Content Security Policy (step 19's
//!   inline check, the nonce), "potentially render-blocking" and "block
//!   rendering" (there is no rendering here), style sheets that block
//!   scripts (the page loads none), `integrity`, `referrerpolicy`,
//!   `fetchpriority`, the speculative parser, and "muted errors" (every
//!   script's errors are reported in full: the kernel's fetches already
//!   keep a renderer to its own site, so a cross-origin script's error text
//!   tells it nothing another renderer could not).
//! - **`importmap`** scripts are Phase 8: one is prepared (its type is set,
//!   step 11) and then does nothing, with an engine report.
//! - **`speculationrules`** scripts likewise do nothing.

use clazel_dom::exec::ExecAttr;
use clazel_encoding::labels::exec::get_an_encoding;
use clazel_js::{Error, Exception, Result, Scope, Script, Source};

use super::dom;
use super::module::{self, ModuleScript};
use super::state::{EventTarget, FetchFor, FiredEvent, Report, Request, RequestKind, realm, state};

/// A script element's type (step 9 to 12).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ScriptType {
    /// "classic".
    Classic,
    /// "module".
    Module,
    /// "importmap".
    ImportMap,
    /// "speculationrules".
    SpeculationRules,
}

/// A classic script (HTML §8.1.4.1† "classic script"): its record, or the
/// error to rethrow if it did not parse.
#[derive(Clone)]
pub(crate) struct ClassicScript {
    /// The parsed script; `None` if creating it failed.
    pub(crate) record: Option<Script>,
    /// "error to rethrow": a parse error, or the engine's refusal.
    pub(crate) error: Option<ScriptError>,
    /// The name reports give: the script's URL, or the document's.
    pub(crate) name: String,
}

/// Why a script has no record.
#[derive(Clone)]
pub(crate) enum ScriptError {
    /// A thrown value (a `SyntaxError`).
    Thrown(Exception),
    /// The engine cannot compile it (a feature it does not have).
    Engine(String),
}

/// A script element's "result" (§4.12.1.1†).
#[derive(Clone)]
pub(crate) enum ScriptResult {
    /// "uninitialized".
    Uninitialized,
    /// null: fetching or creating it failed.
    Null,
    /// A classic script.
    Classic(ClassicScript),
    /// A module script.
    Module(ModuleScript),
}

/// What runs when a script element's result is ready (step 33's "steps to
/// run when the result is ready").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum WhenReady {
    /// Step 33.2.3: execute it and remove it from the set of scripts that
    /// will execute as soon as possible.
    Asap,
    /// Step 33.3.3: run the list of scripts that will execute in order as
    /// soon as possible from its head.
    InOrder,
    /// Steps 33.4.2 and 33.5.3: "set el's ready to be parser-executed to
    /// true".
    ParserExecuted,
}

/// A script element's internal state (HTML §4.12.1.1†, "Processing model").
#[derive(Clone)]
pub(crate) struct ScriptElement {
    /// "parser document" is non-null: the element is "parser-inserted".
    pub(crate) parser_inserted: bool,
    /// "already started".
    pub(crate) already_started: bool,
    /// "force async".
    pub(crate) force_async: bool,
    /// "from an external file".
    pub(crate) from_external_file: bool,
    /// "ready to be parser-executed".
    pub(crate) ready_to_be_parser_executed: bool,
    /// "delaying the load event".
    pub(crate) delaying_load_event: bool,
    /// "type": null until step 9 to 11 set it.
    pub(crate) kind: Option<ScriptType>,
    /// "result".
    pub(crate) result: ScriptResult,
    /// "steps to run when the result is ready".
    pub(crate) when_ready: Option<WhenReady>,
    /// "preparation-time document", as a document generation.
    pub(crate) preparation_time: Option<u64>,
}

impl ScriptElement {
    /// A script element as the parser creates it: "parser document" set,
    /// "force async" false (§13.2.6.4.4†, "A start tag whose tag name is
    /// script", which the tree builder does not report; see the module's
    /// modelling choices).
    fn parser_created() -> ScriptElement {
        ScriptElement {
            parser_inserted: true,
            already_started: false,
            force_async: false,
            from_external_file: false,
            ready_to_be_parser_executed: false,
            delaying_load_event: false,
            kind: None,
            result: ScriptResult::Uninitialized,
            when_ready: None,
            preparation_time: None,
        }
    }
}

/// What step 5 to 31 read from the element, copied out of the document so
/// that no borrow of the page's state is held while scripts run.
struct Snapshot {
    attributes: Attrs,
    source_text: Vec<u32>,
    connected: bool,
    base_url: Option<clazel_url::url::record::ParsedUrl>,
    document_url: String,
}

/// An element's attributes in no namespace, copied: (local name, value).
struct Attrs(Vec<(Vec<u32>, Vec<u32>)>);

impl Attrs {
    fn of(attributes: &[ExecAttr]) -> Attrs {
        Attrs(
            attributes
                .iter()
                .filter(|a| a.namespace.is_none())
                .map(|a| (a.local_name.clone(), a.value.clone()))
                .collect(),
        )
    }

    /// The value of the attribute `name`, if the element has one (the first,
    /// as an element has at most one of a name).
    fn get(&self, name: &str) -> Option<&[u32]> {
        self.0
            .iter()
            .find(|(n, _)| n.iter().copied().eq(name.chars().map(u32::from)))
            .map(|(_, v)| v.as_slice())
    }

    fn has(&self, name: &str) -> bool {
        self.get(name).is_some()
    }
}

/// HTML §4.12.1.1† "prepare the script element" for the parser's
/// `ScriptReady(element)`.
pub(crate) fn prepare_from_parser(scope: &mut Scope<'_>, element: usize) -> Result<()> {
    {
        let st = state(scope)?;
        st.scripts
            .entry(element)
            .or_insert_with(ScriptElement::parser_created);
    }
    prepare(scope, element)
}

/// HTML §4.12.1.1† "prepare the script element" `el`.
pub(crate) fn prepare(scope: &mut Scope<'_>, el: usize) -> Result<()> {
    let st = state(scope)?;
    let generation = st.generation;
    let Some(script) = st.scripts.get_mut(&el) else {
        return Ok(());
    };
    // 1. "If el's already started is true, then return."
    if script.already_started {
        return Ok(());
    }
    // 2. "Let parser document be el's parser document."
    let parser_document = script.parser_inserted;
    // 3. "Set el's parser document to null."
    script.parser_inserted = false;
    // 4. "If parser document is non-null and el does not have an async
    //    attribute, then set el's force async to true." (Read below, once
    //    the attributes are copied.)
    let document_encoding = st.encoding;
    let snap = {
        let arena = super::state::arena(scope)?;
        let Some(attributes) = dom::html_element(arena, el, "script") else {
            return Ok(());
        };
        Snapshot {
            attributes: Attrs::of(attributes),
            // 5. "Let source text be el's child text content."
            source_text: dom::child_text_content(arena, el),
            connected: dom::is_connected(arena, el),
            base_url: dom::document_base_url(arena),
            document_url: dom::text(&dom::document_url(arena)),
        }
    };
    let st = state(scope)?;
    let a = &snap.attributes;
    let Some(script) = st.scripts.get_mut(&el) else {
        return Ok(());
    };
    if parser_document && !a.has("async") {
        script.force_async = true;
    }
    // 6. "If el has no src attribute, and source text is the empty string,
    //    then return."
    if !a.has("src") && snap.source_text.is_empty() {
        return Ok(());
    }
    // 7. "If el is not connected, then return."
    if !snap.connected {
        return Ok(());
    }
    // 8. The script block's type string.
    let type_attr = a.get("type");
    let language = a.get("language");
    let type_string: Vec<u32> = match (type_attr, language) {
        (Some([]), _) => dom::cps("text/javascript"),
        (None, Some([])) => dom::cps("text/javascript"),
        (None, None) => dom::cps("text/javascript"),
        (Some(t), _) => dom::strip(t).to_vec(),
        (None, Some(l)) => {
            let mut s = dom::cps("text/");
            s.extend_from_slice(l);
            s
        }
    };
    // 9. to 12.
    let kind =
        if clazel_mime::mime_type::groups::is_javascript_mime_type_essence_match(&type_string) {
            ScriptType::Classic
        } else if dom::eq_ignore_ascii_case(&type_string, "module") {
            ScriptType::Module
        } else if dom::eq_ignore_ascii_case(&type_string, "importmap") {
            ScriptType::ImportMap
        } else if dom::eq_ignore_ascii_case(&type_string, "speculationrules") {
            ScriptType::SpeculationRules
        } else {
            // 12. "Otherwise, return. (No script is executed, and el's type is
            //     left as null.)"
            return Ok(());
        };
    script.kind = Some(kind);
    // 13. "If parser document is non-null, then set el's parser document
    //     back to parser document and set el's force async to false."
    if parser_document {
        script.parser_inserted = true;
        script.force_async = false;
    }
    // 14. "Set el's already started to true."
    script.already_started = true;
    // 15. "Set el's preparation-time document to its node document."
    script.preparation_time = Some(generation);
    // 16. "If parser document is non-null, and parser document is not equal
    //     to el's preparation-time document, then return." (One document:
    //     equal.)
    // 17. "If scripting is disabled for el, then return." (Scripting is
    //     enabled for every page here.)
    // 18. "If el has a nomodule content attribute and its type is
    //     "classic", then return."
    if a.has("nomodule") && kind == ScriptType::Classic {
        return Ok(());
    }
    // 19. CSP: not modelled.
    // 20. The event and for attributes.
    if a.has("event") && a.has("for") && kind == ScriptType::Classic {
        let for_ = dom::strip(a.get("for").unwrap_or(&[]));
        let event = dom::strip(a.get("event").unwrap_or(&[]));
        if !dom::eq_ignore_ascii_case(for_, "window") {
            return Ok(());
        }
        if !dom::eq_ignore_ascii_case(event, "onload")
            && !dom::eq_ignore_ascii_case(event, "onload()")
        {
            return Ok(());
        }
    }
    // 21. The encoding: the charset attribute's, if "get an encoding" gives
    //     one, else the document's.
    let encoding = a
        .get("charset")
        .and_then(get_an_encoding)
        .unwrap_or(document_encoding);
    // 22. and 23. The crossorigin attribute's state: present or not (the
    //     credentials mode is the kernel's, item 7.16).
    let cors = a.has("crossorigin");
    // 24. to 30. Nonce, integrity, referrer policy, fetch priority: not
    //     modelled. "Let parser metadata be "parser-inserted" if el is
    //     parser-inserted, and "not-parser-inserted" otherwise."
    let parser_inserted = script.parser_inserted;
    let has_src = a.has("src");
    if has_src {
        // 31. "If el has a src content attribute, then:"
        // 31.1. importmap and speculationrules with src: an error event.
        if matches!(kind, ScriptType::ImportMap | ScriptType::SpeculationRules) {
            fire(st, EventTarget::Element(el), "error");
            return Ok(());
        }
        // 31.2. "Let src be the value of el's src attribute."
        let src = a.get("src").unwrap_or(&[]);
        // 31.3. "If src is the empty string, then queue an element task on the
        //       DOM manipulation task source given el to fire an event named
        //       error at el, and return." (Fired at once: see the module docs
        //       of `super`.)
        if src.is_empty() {
            fire(st, EventTarget::Element(el), "error");
            return Ok(());
        }
        // 31.4. "Set el's from an external file to true."
        script.from_external_file = true;
        // 31.5. "Let url be the result of encoding-parsing a URL given src,
        //       relative to el's node document." (UTF-8 for the query: the
        //       document's encoding is not passed to the URL parser.)
        let Some(url) = dom::parse_url(src, snap.base_url.as_ref()) else {
            // 31.6. "If url is failure, then queue an element task ... to fire
            //       an event named error at el, and return."
            fire(st, EventTarget::Element(el), "error");
            return Ok(());
        };
        // 31.7. to 31.9. Render-blocking: not modelled.
        // 31.8. "Set el's delaying the load event to true."
        script.delaying_load_event = true;
        // 31.10. and 31.11. Fetch; "onComplete" marks el as ready.
        let url = dom::serialize(&url);
        match kind {
            ScriptType::Classic => {
                let id = st.next_fetch;
                st.next_fetch = st.next_fetch.saturating_add(1);
                st.fetches.insert(
                    id,
                    FetchFor::Classic {
                        element: el,
                        url: url.clone(),
                        generation,
                        encoding,
                    },
                );
                st.outgoing.push(Request {
                    id,
                    url,
                    kind: RequestKind::ClassicScript,
                    cors,
                    parser_inserted,
                });
            }
            ScriptType::Module => {
                module::fetch_external_module_graph(st, el, generation, url, parser_inserted);
            }
            ScriptType::ImportMap | ScriptType::SpeculationRules => {}
        }
    } else {
        // 32. "If el does not have a src content attribute:"
        // 32.1. "Let base URL be el's node document's document base URL."
        match kind {
            ScriptType::Classic => {
                // 32.2 "classic": create a classic script and mark el as ready.
                let name = snap.document_url.clone();
                let base = snap
                    .base_url
                    .as_ref()
                    .map(dom::serialize)
                    .unwrap_or_default();
                let result = create_classic_script(scope, &snap.source_text, name, base)?;
                mark_as_ready(scope, el, ScriptResult::Classic(result))?;
            }
            ScriptType::Module => {
                // 32.2 "module": "Set el's delaying the load event to true",
                // then "fetch an inline module script graph"; its result is
                // marked ready in a task, which is the same here.
                if let Some(script) = state(scope)?.scripts.get_mut(&el) {
                    script.delaying_load_event = true;
                }
                let base = snap
                    .base_url
                    .as_ref()
                    .map(dom::serialize)
                    .unwrap_or_default();
                let result = module::create_module_script(
                    scope,
                    &snap.source_text,
                    &base,
                    &snap.document_url,
                )?;
                mark_as_ready(scope, el, result)?;
            }
            ScriptType::ImportMap => {
                // 32.2 "importmap": Phase 8. Reported, not registered.
                state(scope)?.reports.push(Report::Engine {
                    script: snap.document_url.clone(),
                    error: "import maps are not supported (Phase 8)".to_owned(),
                });
                return Ok(());
            }
            ScriptType::SpeculationRules => return Ok(()),
        }
    }
    // 33. and 34.
    let st = state(scope)?;
    let Some(script) = st.scripts.get_mut(&el) else {
        return Ok(());
    };
    if (kind == ScriptType::Classic && has_src) || kind == ScriptType::Module {
        // 33.1. "Assert: el's result is "uninitialized"." An inline module
        //       script's result is ready at once here (see 32.2), so the
        //       steps to run when it is ready are run now, below.
        let ready = !matches!(script.result, ScriptResult::Uninitialized);
        if a.has("async") || script.force_async {
            // 33.2. The set of scripts that will execute as soon as possible.
            st.asap.push(el);
            script.when_ready = Some(WhenReady::Asap);
        } else if !script.parser_inserted {
            // 33.3. The list of scripts that will execute in order as soon as
            //       possible.
            st.in_order.push_back(el);
            script.when_ready = Some(WhenReady::InOrder);
        } else if a.has("defer") || kind == ScriptType::Module {
            // 33.4. The list of scripts that will execute when the document
            //       has finished parsing.
            st.deferred.push_back(el);
            script.when_ready = Some(WhenReady::ParserExecuted);
        } else {
            // 33.5. The pending parsing-blocking script.
            st.pending_parsing_blocking = Some(el);
            script.when_ready = Some(WhenReady::ParserExecuted);
        }
        if ready {
            run_when_ready(scope, el)?;
        }
        Ok(())
    } else {
        // 34.1. "Assert: el's result is not "uninitialized"."
        // 34.2. Style sheets that block scripts: none.
        // 34.3. "Otherwise, immediately execute the script element el, even
        //       if other scripts are already executing."
        execute(scope, el)
    }
}

/// HTML §4.12.1.1† "mark as ready" `el` given `result`.
pub(crate) fn mark_as_ready(scope: &mut Scope<'_>, el: usize, result: ScriptResult) -> Result<()> {
    let st = state(scope)?;
    let Some(script) = st.scripts.get_mut(&el) else {
        return Ok(());
    };
    // 1. "Set el's result to result."
    script.result = result;
    // 2. and 3. Run the steps to run when the result is ready, then clear
    //    them.
    run_when_ready(scope, el)?;
    // 4. "Set el's delaying the load event to false."
    if let Some(script) = state(scope)?.scripts.get_mut(&el) {
        script.delaying_load_event = false;
    }
    Ok(())
}

/// "If el's steps to run when the result is ready are not null, then run
/// them. Set el's steps to run when the result is ready to null."
fn run_when_ready(scope: &mut Scope<'_>, el: usize) -> Result<()> {
    let st = state(scope)?;
    let Some(script) = st.scripts.get_mut(&el) else {
        return Ok(());
    };
    let Some(steps) = script.when_ready.take() else {
        return Ok(());
    };
    match steps {
        WhenReady::Asap => {
            // 33.2.3. "Execute the script element el. Remove el from scripts."
            execute(scope, el)?;
            let st = state(scope)?;
            st.asap.retain(|x| *x != el);
        }
        WhenReady::InOrder => {
            // 33.3.3. "If scripts[0] is not el, then abort these steps."
            if st.in_order.front() != Some(&el) {
                return Ok(());
            }
            // "While scripts is not empty, and scripts[0]'s result is not
            // "uninitialized": execute scripts[0]; remove scripts[0]."
            loop {
                let st = state(scope)?;
                let Some(&first) = st.in_order.front() else {
                    break;
                };
                let ready = st
                    .scripts
                    .get(&first)
                    .is_some_and(|s| !matches!(s.result, ScriptResult::Uninitialized));
                if !ready {
                    break;
                }
                execute(scope, first)?;
                let st = state(scope)?;
                if st.in_order.front() == Some(&first) {
                    st.in_order.pop_front();
                }
            }
        }
        WhenReady::ParserExecuted => {
            // "Set el's ready to be parser-executed to true. (The parser will
            // handle executing the script.)"
            script.ready_to_be_parser_executed = true;
        }
    }
    Ok(())
}

/// HTML §4.12.1.1† "execute the script element" `el`.
pub(crate) fn execute(scope: &mut Scope<'_>, el: usize) -> Result<()> {
    let st = state(scope)?;
    let generation = st.generation;
    let Some(script) = st.scripts.get(&el) else {
        return Ok(());
    };
    // 1. "Let document be el's node document."
    // 2. "If el's preparation-time document is not equal to document, then
    //    return."
    if script.preparation_time != Some(generation) {
        return Ok(());
    }
    // 3. Unblock rendering: not modelled.
    let result = script.result.clone();
    let external = script.from_external_file;
    let kind = script.kind;
    // 4. "If el's result is null, then fire an event named error at el, and
    //    return."
    if matches!(result, ScriptResult::Null | ScriptResult::Uninitialized) {
        fire(st, EventTarget::Element(el), "error");
        return Ok(());
    }
    // 5. "If el's from an external file is true, or el's type is "module",
    //    then increment document's ignore-destructive-writes counter."
    let counted = external || kind == Some(ScriptType::Module);
    if counted {
        st.ignore_destructive_writes = st.ignore_destructive_writes.saturating_add(1);
    }
    // 6. Switch on el's type.
    let outcome = match result {
        ScriptResult::Classic(classic) => {
            // "classic": 1. "Let oldCurrentScript be the value to which
            // document's currentScript object was most recently set."
            let old = state(scope)?.current_script;
            // 2. "If el's root is not a shadow root, then set document's
            //    currentScript attribute to el." (No shadow roots.)
            super::globals::set_current_script(scope, Some(el))?;
            // 3. "Run the classic script given by el's result."
            let ran = run_classic_script(scope, &classic);
            // 4. "Set document's currentScript attribute to
            //    oldCurrentScript."
            let restored = super::globals::set_current_script(scope, old);
            ran.and(restored)
        }
        ScriptResult::Module(m) => {
            // "module": 1. "Assert: document's currentScript attribute is
            // null." 2. "Run the module script given by el's result."
            module::run_module_script(scope, &m)
        }
        ScriptResult::Null | ScriptResult::Uninitialized => Ok(()),
    };
    // 7. "Decrement the ignore-destructive-writes counter of document, if it
    //    was incremented in the earlier step."
    let st = state(scope)?;
    if counted {
        st.ignore_destructive_writes = st.ignore_destructive_writes.saturating_sub(1);
    }
    outcome?;
    // 8. "If el's from an external file is true, then fire an event named
    //    load at el."
    if external {
        fire(state(scope)?, EventTarget::Element(el), "load");
    }
    Ok(())
}

/// HTML §8.1.4.3† "create a classic script" from `source` (code points),
/// named `name` in reports, with `base` as its base URL (kept as the
/// script's host data, for `import()` in it). The settings object and the
/// fetch options are the page's (one realm); "muted errors" is not
/// modelled.
pub(crate) fn create_classic_script(
    scope: &mut Scope<'_>,
    source: &[u32],
    name: String,
    base: String,
) -> Result<ClassicScript> {
    // 1. to 7. Script record fields. 8. "Let result be ParseScript(source,
    //    settings's realm, script)." Source text is code points; a lone
    //    surrogate (only `document.write` can put one in the input stream)
    //    becomes U+FFFD, as the engine takes Rust text.
    let text = dom::text(source);
    let realm = realm(scope)?;
    let meta = module::ScriptMeta { base_url: base };
    match scope.compile_script(
        &realm,
        Source::new(&name, &text).with_host_defined(Box::new(meta)),
    ) {
        // 10. "Set script's record to result."
        Ok(record) => Ok(ClassicScript {
            record: Some(record),
            error: None,
            name,
        }),
        // 9. "If result is a list of errors, then: set script's parse error
        //    and its error to rethrow to result[0]. Return script."
        Err(Error::Thrown(e)) => Ok(ClassicScript {
            record: None,
            error: Some(ScriptError::Thrown(e)),
            name,
        }),
        Err(e @ (Error::Terminated | Error::OutOfMemory)) => Err(e),
        Err(other) => Ok(ClassicScript {
            record: None,
            error: Some(ScriptError::Engine(other.to_string())),
            name,
        }),
    }
}

/// HTML §8.1.4.4† "run a classic script" `script`, with "rethrow errors"
/// false: an abrupt completion is reported, not returned. `Err` only for
/// what stops the page (termination, out of memory).
pub(crate) fn run_classic_script(scope: &mut Scope<'_>, script: &ClassicScript) -> Result<()> {
    // 2. "Check if we can run script": scripting is enabled.
    // 3. and 4. "Prepare to run script": the running count.
    let st = state(scope)?;
    st.running = st.running.saturating_add(1);
    // 5. to 7. "If script's error to rethrow is not null, then set
    //    evaluationStatus to ThrowCompletion(script's error to rethrow).
    //    Otherwise, set evaluationStatus to ScriptEvaluation(script's
    //    record)."
    let status: Result<()> = match (&script.record, &script.error) {
        (Some(record), _) => scope.run_script(record).map(|_| ()),
        (None, Some(ScriptError::Thrown(e))) => Err(Error::Thrown(e.clone())),
        (None, Some(ScriptError::Engine(message))) => {
            let st = state(scope)?;
            st.reports.push(Report::Engine {
                script: script.name.clone(),
                error: message.clone(),
            });
            Ok(())
        }
        (None, None) => Ok(()),
    };
    let st = state(scope)?;
    st.running = st.running.saturating_sub(1);
    // 8. "If evaluationStatus is an abrupt completion, then ... report an
    //    exception given by evaluationStatus.[[Value]]".
    match status {
        Ok(()) => {}
        Err(e @ (Error::Terminated | Error::OutOfMemory)) => return Err(e),
        Err(e) => report(scope, &script.name, e)?,
    }
    // 8.3.2 and 9. "Clean up after running script": "If the JavaScript
    //    execution context stack is now empty, perform a microtask
    //    checkpoint."
    clean_up_after_running_script(scope)
}

/// HTML §8.1.4.?† "clean up after running script": a microtask checkpoint
/// when no script is running any more. A job that throws is reported, as
/// the checkpoint's "report an exception" for a failed microtask does.
pub(crate) fn clean_up_after_running_script(scope: &mut Scope<'_>) -> Result<()> {
    if state(scope)?.running != 0 {
        return Ok(());
    }
    super::bound::microtask_checkpoint(scope)?;
    super::bound::flush_events(scope)
}

/// HTML §8.1.4.?† "report an exception": the exception's name and message,
/// kept in the page's reports (no `error` event listeners exist yet; the
/// event is recorded at the `Window`). An engine error that is not a thrown
/// value is an engine report.
pub(crate) fn report(scope: &mut Scope<'_>, script: &str, error: Error) -> Result<()> {
    let entry = match error {
        Error::Thrown(e) => match scope.report(&e) {
            Ok(r) => Report::Exception {
                script: script.to_owned(),
                name: r.name,
                message: r.message,
            },
            Err(other) => Report::Engine {
                script: script.to_owned(),
                error: other.to_string(),
            },
        },
        other => Report::Engine {
            script: script.to_owned(),
            error: other.to_string(),
        },
    };
    let st = state(scope)?;
    let thrown = matches!(entry, Report::Exception { .. });
    st.reports.push(entry);
    if thrown {
        fire(st, EventTarget::Window, "error");
    }
    Ok(())
}

/// "Fire an event named `name` at `target`": recorded (see
/// [`super::state::EventTarget`]).
pub(crate) fn fire(st: &mut super::state::PageState, target: EventTarget, name: &'static str) {
    st.events.push(FiredEvent { target, name });
}
