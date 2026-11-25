//! The HTML parser as scripts see it: the tokenizer runs (HTML §13.2.5†,
//! with the parser pause flag), the "text" insertion mode's end tag
//! "script" steps that run around "prepare the script element" (HTML
//! §13.2.6.4.8†), the pending parsing-blocking script that blocks the
//! tokenizer, "abort a parser" and "the end" (HTML §13.2.7†), over
//! `clazel-treebuilder`'s incremental driver.
//!
//! <https://html.spec.whatwg.org/multipage/parsing.html#parsing-main-incdata>,
//! <https://html.spec.whatwg.org/multipage/parsing.html#the-end>,
//! <https://html.spec.whatwg.org/multipage/parsing.html#abort-a-parser>.
//!
//! The tree builder's step pops the `script` element and returns to the
//! original insertion mode (steps 2 to 4 of the end tag "script" rules)
//! before it asks for `ScriptReady`; steps 1 and 5 to 10 are here
//! ([`script_end_tag`]).
//!
//! "Spin the event loop until ..." (step 10.5 for a parsing-blocking script,
//! "the end" steps 5, 7 and 8) is a return to the page's embedder: the page
//! records what it waits for, and its next task (a fetch answered, or
//! [`super::Page::run`]) continues from there. The speculative HTML parser
//! is not modelled.

use clazel_encoding::labels::exec::from_number;
use clazel_html::sniff::exec::change_the_encoding;
use clazel_js::{Result, Scope};
use clazel_treebuilder::exec::incremental::Pause;
use clazel_treebuilder::exec::types::ExecAction;

use super::element::{clean_up_after_running_script, execute, fire, prepare_from_parser};
use super::encodings::Encodings;
use super::state::{Doc, EndPhase, EventTarget, PageState, Readiness, state};

/// Why a run of the tokenizer returned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Run {
    /// It reached the insertion point (or the end of a script-created
    /// parser's input before `document.close`).
    InsertionPoint,
    /// The parser has stopped, or there is no active parser.
    Stopped,
    /// The parser pause flag is set: a nested invocation is aborted.
    Paused,
    /// The tokenizer is blocked on a pending parsing-blocking script.
    Blocked,
}

/// Runs the tokenizer and the tree construction stage until the insertion
/// point, the end, the parser pause flag or a block: the loop that
/// §13.2.5† describes ("the tokenizer ... must abort the processing of the
/// tokenizer if the parser pause flag is true") and that
/// `document.write`'s step 8 and `document.close`'s step 6 run.
pub(crate) fn run_tokenizer(scope: &mut Scope<'_>) -> Result<Run> {
    loop {
        let st = state(scope)?;
        if st.parser_pause {
            return Ok(Run::Paused);
        }
        if st.blocked_on.is_some() {
            return Ok(Run::Blocked);
        }
        let Some(parser) = st.doc.parser() else {
            match walk(scope)? {
                Some(run) => return Ok(run),
                None => continue,
            }
        };
        match parser.pump(&Encodings) {
            Pause::InsertionPoint => return Ok(Run::InsertionPoint),
            Pause::Stopped => {
                begin_the_end(st);
                return Ok(Run::Stopped);
            }
            Pause::Actions(actions) => {
                for action in actions {
                    match action {
                        ExecAction::ScriptReady(node) => script_end_tag(scope, node)?,
                        ExecAction::ChangeEncoding(id) => change_encoding(state(scope)?, id),
                        // "Stop parsing": the parser has stopped, and the
                        // next pump says so.
                        ExecAction::StopParsing => {}
                    }
                }
            }
        }
    }
}

/// A document that was parsed before its scripts ran (`Page::for_document`):
/// the parser's part of [`run_tokenizer`], for a tree that is already
/// built. The next script element in tree order is reached as the parser
/// would reach it (the end tag "script" steps), and when there is none the
/// parser has stopped.
///
/// What this is not: the scripts see the whole tree, not the part the
/// parser had built when it reached them, and `document.write` has no input
/// stream to edit (it is reported, not run). The incremental driver cannot
/// hand its tree to a script to change until `clazel-treebuilder` lets the
/// tree builder's open elements follow such changes.
fn walk(scope: &mut Scope<'_>) -> Result<Option<Run>> {
    let st = state(scope)?;
    let Some(w) = st.walk.as_mut() else {
        return Ok(Some(Run::Stopped));
    };
    match w.order.get(w.next).copied() {
        Some(node) => {
            w.next = w.next.saturating_add(1);
            script_end_tag(scope, node)?;
            Ok(None)
        }
        None => {
            st.walk = None;
            begin_the_end(st);
            Ok(Some(Run::Stopped))
        }
    }
}

/// HTML §13.2.6.4.8† the "text" insertion mode, "An end tag whose tag name
/// is "script"", steps 1 and 5 to 10, for the script element `script`.
fn script_end_tag(scope: &mut Scope<'_>, script: usize) -> Result<()> {
    // 1. "If the active speculative HTML parser is null and the JavaScript
    //    execution context stack is empty, then perform a microtask
    //    checkpoint."
    clean_up_after_running_script(scope)?;
    // 2. to 4. The step has done these (module docs).
    // 5. "Let the old insertion point have the same value as the current
    //    insertion point. Let the insertion point be just before the next
    //    input character." (A document parsed up front has no insertion
    //    point.)
    let st = state(scope)?;
    let old = match st.doc.parser() {
        Some(parser) => {
            let old = parser.insertion_point();
            parser.set_insertion_point_to_next();
            old
        }
        None if st.walk.is_some() => None,
        None => return Ok(()),
    };
    // 6. "Increment the parser's script nesting level by one."
    st.script_nesting_level = st.script_nesting_level.saturating_add(1);
    // 7. "If the active speculative HTML parser is null, then prepare the
    //    script element script. This might cause some script to execute,
    //    which might cause new characters to be inserted into the tokenizer,
    //    and might cause the tokenizer to output more tokens, resulting in a
    //    reentrant invocation of the parser."
    let prepared = prepare_from_parser(scope, script);
    // 8. "Decrement the parser's script nesting level by one. If the
    //    parser's script nesting level is zero, then set the parser pause
    //    flag to false."
    let st = state(scope)?;
    st.script_nesting_level = st.script_nesting_level.saturating_sub(1);
    if st.script_nesting_level == 0 {
        st.parser_pause = false;
    }
    prepared?;
    // 9. "Let the insertion point have the value of the old insertion
    //    point." (A document.open in between made a new parser only at
    //    nesting level zero, which this is not, so this is the same parser;
    //    an aborted one has none.)
    if let Some(parser) = st.doc.parser() {
        parser.set_insertion_point(old);
    }
    // 10. "At this stage, if the pending parsing-blocking script is not
    //     null, then:"
    if st.pending_parsing_blocking.is_some() {
        if st.script_nesting_level != 0 {
            // "If the script nesting level is not zero: Set the parser pause
            // flag to true, and abort the processing of any nested
            // invocations of the tokenizer, yielding control back to the
            // caller."
            st.parser_pause = true;
        } else {
            // "Otherwise: 1. Let the script be the pending parsing-blocking
            // script. 2. Set the pending parsing-blocking script to null.
            // 3. Start the speculative HTML parser (not modelled). 4. Block
            // the tokenizer".
            st.blocked_on = st.pending_parsing_blocking.take();
            resume_blocked(scope)?;
        }
    }
    Ok(())
}

/// Step 10 of the end tag "script" rules from its sub-step 5, for the
/// script the tokenizer is blocked on: if it is ready to be
/// parser-executed, run it (sub-steps 6 to 13) and repeat for the next
/// pending parsing-blocking script (sub-step 14); if not, return with the
/// tokenizer still blocked ("spin the event loop until ... the script's
/// ready to be parser-executed becomes true").
pub(crate) fn resume_blocked(scope: &mut Scope<'_>) -> Result<()> {
    loop {
        let st = state(scope)?;
        let Some(el) = st.blocked_on else {
            return Ok(());
        };
        // 5. Spin the event loop until the script is ready (style sheets
        //    that block scripts: none).
        let ready = st
            .scripts
            .get(&el)
            .is_some_and(|s| s.ready_to_be_parser_executed);
        if !ready {
            return Ok(());
        }
        // 6. "If this parser has been aborted in the meantime, return."
        // 7. Stop the speculative parser; 8. unblock the tokenizer.
        st.blocked_on = None;
        // 9. "Let the insertion point be just before the next input
        //    character." (A document parsed up front has none.)
        match st.doc.parser() {
            Some(parser) => parser.set_insertion_point_to_next(),
            None if st.walk.is_some() => {}
            None => return Ok(()),
        }
        // 10. "Increment the parser's script nesting level by one (it should
        //     be zero before this step, so this sets it to one)."
        st.script_nesting_level = st.script_nesting_level.saturating_add(1);
        // 11. "Execute the script element the script."
        let executed = execute(scope, el);
        // 12. "Decrement the parser's script nesting level by one. If the
        //     parser's script nesting level is zero (which it always should be
        //     at this point), then set the parser pause flag to false."
        let st = state(scope)?;
        st.script_nesting_level = st.script_nesting_level.saturating_sub(1);
        if st.script_nesting_level == 0 {
            st.parser_pause = false;
        }
        executed?;
        // 13. "Let the insertion point be undefined again."
        if let Some(parser) = st.doc.parser() {
            parser.set_insertion_point(None);
        }
        // 14. "If there is once again a pending parsing-blocking script, then
        //     repeat these steps from step 1."
        match st.pending_parsing_blocking.take() {
            Some(next) => st.blocked_on = Some(next),
            None => return Ok(()),
        }
    }
}

/// HTML §13.2.3.4† "change the encoding", for the parser's
/// `ChangeEncoding`: with a tentative confidence and an encoding that
/// changes ("change the encoding" steps 1 to 4, `clazel-html`'s
/// `change_the_encoding`), the document is to be navigated to again with the
/// new encoding (step 6): the parser is aborted and the page's embedder told
/// ([`super::Progress::Reparse`]). Otherwise nothing changes.
fn change_encoding(st: &mut PageState, id: u64) {
    if !st.tentative || st.reparse.is_some() {
        return;
    }
    let Some(n) = u8::try_from(id).ok() else {
        return;
    };
    let new = from_number(n);
    if let Some(e) = change_the_encoding(st.encoding, new) {
        st.reparse = Some(e);
        abort_parser(st);
    } else {
        // "set the confidence to certain".
        st.tentative = false;
    }
}

/// HTML §13.2.7† "the end", steps 1 to 4: what happens when the parser
/// stops, before anything that waits.
fn begin_the_end(st: &mut PageState) {
    if st.end != EndPhase::Parsing {
        return;
    }
    // 1. The speculative parser: not modelled.
    // 2. "Set the insertion point to undefined."
    if let Some(parser) = st.doc.parser() {
        parser.set_insertion_point(None);
    }
    // 3. "Update the current document readiness to "interactive"."
    update_readiness(st, Readiness::Interactive);
    // 4. "Pop all the nodes off the stack of open elements." The tree
    //    builder's end-of-file rules have.
    st.end = EndPhase::Deferred;
}

/// "The end" from step 5: runs what can run now and says whether it is
/// waiting (`true`) for a script or for the load event's delays.
pub(crate) fn continue_the_end(scope: &mut Scope<'_>) -> Result<bool> {
    loop {
        // What the steps so far fired reaches its listeners before the next
        // step runs (`readystatechange`, `DOMContentLoaded`).
        super::bound::flush_events(scope)?;
        let st = state(scope)?;
        match st.end {
            EndPhase::Parsing | EndPhase::Loaded => return Ok(false),
            EndPhase::Deferred => {
                // 5. "While the list of scripts that will execute when the
                //    document has finished parsing is not empty: 1. Spin the
                //    event loop until the first script in the list has its
                //    ready to be parser-executed set to true ... 2. Execute the
                //    script element given by the first script in the list.
                //    3. Remove the first script element from the list."
                if let Some(&first) = st.deferred.front() {
                    let ready = st
                        .scripts
                        .get(&first)
                        .is_some_and(|s| s.ready_to_be_parser_executed);
                    if !ready {
                        return Ok(true);
                    }
                    execute(scope, first)?;
                    let st = state(scope)?;
                    if st.deferred.front() == Some(&first) {
                        st.deferred.pop_front();
                    }
                    continue;
                }
                // 6. "Queue a global task on the DOM manipulation task source
                //    given the Document's relevant global object to run the
                //    following substeps: ... Fire an event named
                //    DOMContentLoaded at the Document object, with its bubbles
                //    attribute initialized to true." (Run now: this is the
                //    page's next task.)
                fire(st, EventTarget::Document, "DOMContentLoaded");
                st.end = EndPhase::AwaitAsync;
            }
            EndPhase::AwaitAsync => {
                // 7. "Spin the event loop until the set of scripts that will
                //    execute as soon as possible and the list of scripts that
                //    will execute in order as soon as possible are empty."
                // 8. "Spin the event loop until there is nothing that delays
                //    the load event in the Document."
                let delayed = st.scripts.values().any(|s| s.delaying_load_event);
                if !st.asap.is_empty() || !st.in_order.is_empty() || delayed {
                    return Ok(true);
                }
                // 9. "Queue a global task ...: 1. Update the current document
                //    readiness to "complete". ... 5. Fire an event named load at
                //    window, with legacy target override flag set."
                update_readiness(st, Readiness::Complete);
                fire(st, EventTarget::Window, "load");
                // 10. pageshow; 11. "Completely finish loading the Document";
                //     12. navigation timing: not modelled. The parser is done
                //     with; the tree stays.
                finish_parser(st);
                st.end = EndPhase::Loaded;
            }
        }
    }
}

/// HTML §3.1.?† "update the current document readiness" to `readiness`:
/// set it and fire `readystatechange` at the document.
fn update_readiness(st: &mut PageState, readiness: Readiness) {
    if st.readiness == readiness {
        return;
    }
    st.readiness = readiness;
    fire(st, EventTarget::Document, "readystatechange");
}

/// The parser is done with: the document keeps the tree.
fn finish_parser(st: &mut PageState) {
    let doc = core::mem::replace(&mut st.doc, Doc::Done);
    if let Doc::Parsing(p) = doc {
        // The tree goes to the page (`state` moves it).
        st.finished = Some(p.into_parser().arena);
    }
    st.script_created = false;
}

/// HTML §13.2.?† "abort a parser": "1. Throw away any pending content in the
/// input stream, and discard any future content that would have been added
/// to it. 2. Stop the speculative HTML parser for this HTML parser. 3. Update
/// the current document readiness to "interactive". 4. Pop all the nodes off
/// the stack of open elements, if any. 5. Update the current document
/// readiness to "complete"." The document's "active parser was aborted" is
/// set, and the parser's lists of scripts are emptied (their scripts would
/// run against a parser that is gone).
pub(crate) fn abort_parser(st: &mut PageState) {
    update_readiness(st, Readiness::Interactive);
    finish_parser(st);
    update_readiness(st, Readiness::Complete);
    st.active_parser_aborted = true;
    st.pending_parsing_blocking = None;
    st.blocked_on = None;
    st.deferred.clear();
    st.script_nesting_level = 0;
    st.parser_pause = false;
    st.end = EndPhase::Loaded;
}
