//! HTML §13.2.6.4.8 the "text" insertion mode. The modelling choices are
//! listed in [`super::super`]; the ones this mode reads:
//! - scripts are not modelled (Phase 7). A script element's "already
//!   started" flag is script-processing state outside the DOM model, so the
//!   end-of-file case's "set its already started to true" changes nothing
//!   here. The `script` end tag case returns `Action::ScriptReady(node)` for
//!   "prepare the script element", and the parser's own steps after it are
//!   those of a script that does nothing: preparing it sets no pending
//!   parsing-blocking script, so "At this stage, if the pending
//!   parsing-blocking script is not null" never applies; the script nesting
//!   level goes from zero to one and back to zero, so the parser pause flag
//!   stays false; the microtask checkpoint and the insertion point (only
//!   `document.write` reads it) change nothing in the parse state.
//! - The tokenizer is in the RCDATA, RAWTEXT or script data state whenever
//!   the insertion mode is "text" (§13.2.6.2 and the "in head" `script`
//!   rule switch both together), and in those states it emits only
//!   character, end tag and end-of-file tokens, the kinds the standard's
//!   cases cover. Any other token, never emitted, is ignored.

#[allow(unused_imports)]
use super::super::dispatch::*;
#[allow(unused_imports)]
use super::super::insert::*;
#[allow(unused_imports)]
use super::super::state::*;
#[allow(unused_imports)]
use super::super::tags::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §13.2.6.4.8 the "text" insertion mode.
pub open spec fn mode_text(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is Char {
        // 1. "A character token": "Insert the token's character."
        Outcome::Done(insert_char(p, t->Char_0))
    } else if t is Eof {
        // 2. "An end-of-file token"
        // "Parse error."
        // "If the current node is a script element, then set its already
        // started to true." (Not part of the DOM model: see above.)
        // "Pop the current node off the stack of open elements."
        // "Switch the insertion mode to the original insertion mode and
        // reprocess the token."
        let q = pop(p);
        Outcome::Reprocess(Parser { mode: q.original_mode, ..q }, t)
    } else if t is End && t->End_0.tag == Tag::Script {
        // 3. "An end tag whose tag name is "script""
        Outcome::Done(text_script_end(p))
    } else if t is End {
        // 4. "Any other end tag"
        // "Pop the current node off the stack of open elements."
        // "Switch the insertion mode to the original insertion mode."
        let q = pop(p);
        Outcome::Done(Parser { mode: q.original_mode, ..q })
    } else {
        // No other token reaches this mode (see above): ignored.
        Outcome::Done(p)
    }
}

/// Case 3 of the "text" insertion mode, "An end tag whose tag name is
/// "script"".
pub open spec fn text_script_end(p: Parser) -> Parser {
    // "If the active speculative HTML parser is null and the JavaScript
    // execution context stack is empty, then perform a microtask
    // checkpoint." (Not modelled.)
    // "Let script be the current node (which will be a script element)."
    let script = current_node(p);
    // "Pop the current node off the stack of open elements."
    let p1 = pop(p);
    // "Switch the insertion mode to the original insertion mode."
    let p2 = Parser { mode: p1.original_mode, ..p1 };
    // "Let the old insertion point have the same value as the current
    // insertion point. Let the insertion point be just before the next input
    // character." (Not modelled.)
    // "Increment the parser's script nesting level by one." (From zero to
    // one.)
    // "If the active speculative HTML parser is null, then prepare the script
    // element script." (It is null: the driver's action.)
    let p3 = if p2.stopped {
        p2
    } else {
        Parser { actions: p2.actions.push(Action::ScriptReady(script.id)), ..p2 }
    };
    // "Decrement the parser's script nesting level by one. If the parser's
    // script nesting level is zero, then set the parser pause flag to false."
    // (Back to zero; the flag is never set.)
    // "Let the insertion point have the value of the old insertion point."
    // (Not modelled.)
    // "At this stage, if the pending parsing-blocking script is not null:
    // …" (It is null: a script that does nothing sets none.)
    p3
}

} // verus!
