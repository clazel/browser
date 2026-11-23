//! Dynamic markup insertion (HTML §8.4†): `document.open()`,
//! `document.close()`, `document.write()` and `document.writeln()`, as an
//! edit of the parser's input stream at the insertion point (phase-4.md,
//! "Looking ahead").
//!
//! <https://html.spec.whatwg.org/multipage/dynamic-markup-insertion.html>:
//! "document open steps", `document.close()`, "document write steps",
//! `document.writeln()`.
//!
//! Modelling choices (each listed):
//! - **No XML documents, no custom elements**: steps that throw for an XML
//!   document or a non-zero "throw-on-dynamic-markup-insertion counter" never
//!   apply (the counter is raised only while a custom element constructor
//!   runs, and there are none). The "unload counter" is always zero (no
//!   `unload` handlers run yet). Trusted Types are not modelled: every value
//!   is converted with ToString.
//! - **The document open steps** empty the document by starting a new tree
//!   for the new parser ("replace all with null"), and bump the document
//!   generation, so that node wrappers and prepared script elements of the
//!   old tree are stale rather than aliasing nodes of the new one. Steps 8
//!   to 10 and 12 to 14 (stopping the navigation, erasing event listeners,
//!   the URL and history update, the initial about:blank and iframe flags)
//!   have nothing to act on here: there are no listeners, and the URL stays
//!   the document's. An old parser that is still active (nesting level
//!   zero) is aborted, and its lists of scripts are emptied.
//! - **`document.close()`** step 6 runs the tokenizer with the insertion
//!   point set aside, as it runs to the explicit "EOF" character, and puts it
//!   back after.

use clazel_js::{Args, Result, Scope};
use clazel_treebuilder::exec::incremental::Incremental;

use super::dom;
use super::parser::{Run, abort_parser, run_tokenizer};
use super::state::{Doc, EndPhase, Readiness, state};

/// `document.write(...text)` (`newline` false) and `document.writeln(...text)`
/// (`newline` true): the arguments joined (`writeln` adds U+000A, its step
/// 1), then the "document write steps".
pub(crate) fn document_write(scope: &mut Scope<'_>, args: &Args<'_>, newline: bool) -> Result<()> {
    // "document write steps" 1. and 2.: "Let string be the empty string. For
    // each value of text: append value to string" (each converted with
    // ToString, as a DOMString argument is).
    let mut input: Vec<u32> = Vec::new();
    for i in 0..args.len() {
        let s = scope.to_string(args.get(i))?;
        let units = scope.string_to_utf16(s)?;
        input.extend(char::decode_utf16(units.iter().copied()).map(|r| match r {
            Ok(c) => u32::from(c),
            Err(e) => u32::from(e.unpaired_surrogate()),
        }));
    }
    if newline {
        input.push(0x0A);
    }
    document_write_steps(scope, &input)
}

/// HTML §8.4.3† "document write steps" with `input`.
pub(crate) fn document_write_steps(scope: &mut Scope<'_>, input: &[u32]) -> Result<()> {
    // 3. XML documents and 4. the throw-on-dynamic-markup-insertion counter:
    //    never (module docs).
    // 5. "If document's active parser was aborted is true, then return."
    let st = state(scope)?;
    if st.active_parser_aborted {
        return Ok(());
    }
    // 6. "If the insertion point is undefined, then:"
    let undefined = st
        .doc
        .parser()
        .is_none_or(|p| p.insertion_point().is_none());
    if undefined {
        // 6.1. "If document's unload counter is greater than 0 or document's
        //      ignore-destructive-writes counter is greater than 0, then
        //      return."
        if st.ignore_destructive_writes > 0 {
            return Ok(());
        }
        // 6.2. "Run the document open steps with document."
        document_open(scope)?;
    }
    // 7. "Insert input into the input stream just before the insertion
    //    point."
    let st = state(scope)?;
    match st.doc.parser() {
        Some(p) => {
            p.insert(input);
        }
        None => return Ok(()),
    }
    // 8. "If document's pending parsing-blocking script is null, then have
    //    the HTML parser process input, one code point at a time, processing
    //    resulting tokens as they are emitted, and stopping when the tokenizer
    //    reaches the insertion point or when the processing of the tokenizer
    //    is aborted by the tree construction stage".
    if st.pending_parsing_blocking.is_none() && st.blocked_on.is_none() {
        let _: Run = run_tokenizer(scope)?;
    }
    Ok(())
}

/// HTML §8.4.1† "document open steps" (from `document.open()`, and from the
/// document write steps).
pub(crate) fn document_open(scope: &mut Scope<'_>) -> Result<()> {
    let st = state(scope)?;
    // 1. to 4. XML, the throw-on-dynamic-markup-insertion counter, and the
    //    entry document's origin: never apply (module docs).
    // 5. "If document has an active parser whose script nesting level is
    //    greater than 0, then return document."
    if st.doc.parser().is_some() && st.script_nesting_level > 0 {
        return Ok(());
    }
    // 6. The unload counter: always zero.
    // 7. "If document's active parser was aborted is true, then return
    //    document."
    if st.active_parser_aborted {
        return Ok(());
    }
    // 8. Stop loading: an active parser is aborted.
    if st.doc.parser().is_some() {
        abort_parser(st);
    }
    st.active_parser_aborted = false;
    // 9. and 10. Erase event listeners and handlers: there are none.
    // 11. "Replace all with null within document, without firing any
    //     mutation events": a new tree, and a new generation.
    let url = dom::document_url(super::state::arena(scope)?);
    let st = state(scope)?;
    st.generation = st.generation.saturating_add(1);
    st.wrappers.clear();
    st.scripts.clear();
    st.pending_parsing_blocking = None;
    st.blocked_on = None;
    st.asap.clear();
    st.in_order.clear();
    st.deferred.clear();
    // 12. to 15. The URL and history update and the flags (module docs);
    //     the new tree's mode is no-quirks until its parser says otherwise.
    // 16. "Create a new HTML parser and associate it with document. This is a
    //     script-created parser (meaning that it can be closed by the
    //     document.open() and document.close() methods, and that the
    //     tokenizer will wait for an explicit end-of-file token before
    //     emitting an end-of-file token). The encoding confidence is
    //     irrelevant."
    let mut parser = Incremental::new(url, true, false, &[], false);
    // 17. "Set the insertion point to point at just before the end of the
    //     input stream (which at this point will be empty)."
    parser.set_insertion_point_to_next();
    st.doc = Doc::Parsing(Box::new(parser));
    st.script_created = true;
    st.script_nesting_level = 0;
    st.parser_pause = false;
    st.end = EndPhase::Parsing;
    // 18. "Update the current document readiness of document to "loading"."
    st.readiness = Readiness::Loading;
    // 19. "Return document." (The caller does.)
    // `document.currentScript` keeps its value: the running script is
    // still running, though its element is gone from the tree.
    Ok(())
}

/// HTML §8.4.2† `document.close()`.
pub(crate) fn document_close(scope: &mut Scope<'_>) -> Result<()> {
    let st = state(scope)?;
    // 1. and 2. XML and the throw-on-dynamic-markup-insertion counter: never.
    // 3. "If there is no script-created parser associated with this, then
    //    return."
    if !st.script_created {
        return Ok(());
    }
    let Some(parser) = st.doc.parser() else {
        return Ok(());
    };
    // 4. "Insert an explicit "EOF" character at the end of the parser's input
    //    stream."
    parser.close();
    // 5. "If this's pending parsing-blocking script is non-null, then
    //    return."
    if st.pending_parsing_blocking.is_some() || st.blocked_on.is_some() {
        return Ok(());
    }
    // 6. "Run the tokenizer, processing resulting tokens as they are emitted,
    //    and stopping when the tokenizer reaches the explicit "EOF" character
    //    or spins the event loop."
    let saved = parser.insertion_point();
    parser.set_insertion_point(None);
    let _: Run = run_tokenizer(scope)?;
    if let Some(p) = state(scope)?.doc.parser()
        && !p.stopped()
    {
        p.set_insertion_point(saved);
    }
    Ok(())
}
