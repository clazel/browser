//! W3C HTML 5.2 §8.2.5.4.8: the "text" insertion mode. Source and
//! modelling choices: [`super`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// W3C HTML 5.2 §8.2.5.4.8 the "text" insertion mode
/// (<https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#sec-the-text-insertion-mode>).
pub open spec fn w3c_mode_text(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is Char {
        // "A character token": "Insert the token's character."
        Outcome::Done(insert_char(p, t->Char_0))
    } else if t is Eof {
        // "An end-of-file token": "Parse error. If the current node is a
        // script element, mark the script element as "already started". Pop
        // the current node off the stack of open elements. Switch the
        // insertion mode to the original insertion mode and reprocess the
        // token."
        Outcome::Reprocess(Parser { mode: p.original_mode, ..pop(p) }, t)
    } else if w3c_end(t, Tag::Script) {
        // "An end tag whose tag name is "script"":
        // "Let script be the current node (which will be a script
        // element)."
        let script = current_node(p);
        // "Pop the current node off the stack of open elements."
        let q = pop(p);
        // "Switch the insertion mode to the original insertion mode."
        let q2 = Parser { mode: q.original_mode, ..q };
        // "Prepare the script." (The driver's action; the steps after it are
        // those of a script that does nothing: see [`super`].)
        Outcome::Done(Parser { actions: q2.actions.push(Action::ScriptReady(script.id)), ..q2 })
    } else if t is End {
        // "Any other end tag": "Pop the current node off the stack of open
        // elements. Switch the insertion mode to the original insertion
        // mode."
        Outcome::Done(Parser { mode: p.original_mode, ..pop(p) })
    } else {
        // No entry (see [`super`]): ignored.
        Outcome::Done(p)
    }
}

} // verus!
