//! An independent transcription of the insertion modes (Phase 4 item 4.11),
//! from a different document than [`crate::spec::modes`], written without
//! reading those files (docs/VERIFICATION.md, "Trust without reviewers",
//! item 2), and the lemmas proving the two equal where the documents agree.
//!
//! Source (pinned): W3C, *HTML 5.2*, W3C Recommendation, 14 December 2017,
//! <https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html> (document
//! revision `ceb65ae94cd46c47d9c5d9badc337703e7c09832`), §8.2.5 "Tree
//! construction", §8.2.5.4.1 to §8.2.5.4.23 (the 23 insertion modes). The
//! undated URL <https://www.w3.org/TR/html52/> now redirects to the WHATWG
//! standard, so the dated Recommendation is the text used. The W3C forked
//! this text from the WHATWG standard in 2016 and edited it separately; it
//! is a second document, nine years older than the one
//! [`crate::spec`] transcribes, not a second reading of the same one.
//!
//! What is transcribed here and what is reused:
//! - Each insertion mode is one spec function, `w3c_mode_<name>`, in a
//!   module per group of sections ([`initial`]: §8.2.5.4.1; [`early`]:
//!   §8.2.5.4.2 to §8.2.5.4.6; [`body`]: §8.2.5.4.7, with the adoption
//!   agency algorithm; [`text`]: §8.2.5.4.8; [`tables`]: §8.2.5.4.9 to
//!   §8.2.5.4.15; [`template`]: §8.2.5.4.18; [`after`]: §8.2.5.4.19 to
//!   §8.2.5.4.23). Each entry ("A start tag whose tag name is …") is one
//!   branch, in the W3C's order, with the W3C's wording quoted. Entries
//!   listed together (two `dt` lines over one `dd`) are one branch.
//! - **Not transcribed:** §8.2.5.4.16 "in select" and §8.2.5.4.17 "in
//!   select in table", which have no counterpart in the WHATWG text or in
//!   `Mode` (see below).
//! - The parse state, the tokens and the outcome of one rule application
//!   are [`crate::spec`]'s (`Parser`, `Tok`, `Outcome`), so that the two
//!   transcriptions can be compared at all.
//! - The algorithms the modes call (§8.2.4's "reset the insertion mode
//!   appropriately", the scopes, "clear the list of active formatting
//!   elements up to the last marker"; §8.2.5.1 "insert an HTML element",
//!   "insert a comment", "insert a character", "create an element for the
//!   token"; §8.2.5.2 and §8.2.5.3) are [`crate::spec::base`]'s, transcribed
//!   from the WHATWG text. This module checks the mode rules only; where the
//!   W3C's version of such an algorithm differs (its "reset the insertion
//!   mode appropriately" has steps for `select`), the difference is listed
//!   below and the reused algorithm is the WHATWG one.
//!
//! Modelling choices (each a difference in form; the meaning is the W3C's):
//! - "Parse error." changes nothing (parse errors are not modelled); an
//!   entry that only says "Parse error." or "ignore the token" is
//!   `Outcome::Done(p)`.
//! - "Process the token using the rules for the m insertion mode" is
//!   `Outcome::Using(m, p, t)`, and "reprocess the token" is
//!   `Outcome::Reprocess(p, t)` (the dispatcher's loop runs them). Where the
//!   W3C has steps *after* processing with another mode's rules ("after
//!   head"'s head-element rule, "in table"'s foster parenting), the other
//!   mode's function is called directly and the steps are applied to the
//!   parser it hands back.
//! - "Acknowledge the token's self-closing flag" changes nothing (it only
//!   suppresses a parse error).
//! - "The parser was originally created for the HTML fragment parsing
//!   algorithm" is `p.context is Some`.
//! - "The document is an iframe srcdoc document" is always false, and the
//!   scripts' flags ("parser-inserted", "non-blocking", "already
//!   started"), the script nesting level, the insertion point and the
//!   pending parsing-blocking script are not modelled (as in
//!   [`crate::spec`]). "Prepare the script" is the action
//!   `Action::ScriptReady(node)` for the driver; the steps after it are those
//!   of a script that does nothing.
//! - "Stop parsing" is `crate::spec::stop_parsing`. The node limit is
//!   [`crate::spec`]'s: creating a node beyond it stops parsing, and a
//!   stopped parser changes nothing, so every later step of the same token is
//!   a no-op (the helpers reused from [`crate::spec::base`] check it; the
//!   steps written here, such as "change the encoding", check it too).
//! - A token for which a mode has no entry (the "text" mode lists only
//!   characters, end-of-file and end tags; the tokenizer emits nothing else
//!   there) is ignored.
//!
//! How the W3C text differs from the WHATWG text [`crate::spec`]
//! transcribes, as far as the modes go (each equivalence lemma in
//! [`equivalence`] and [`equivalence_body`] excludes the inputs where they
//! differ, in its precondition, and says why):
//! - The WHATWG tokenizer emits processing instruction tokens, which the
//!   modes insert; the W3C has no such token. Every lemma excludes
//!   `Tok::Pi`.
//! - The W3C has 23 insertion modes: "in select" (§8.2.5.4.16) and "in select
//!   in table" (§8.2.5.4.17) do not exist in the WHATWG text, whose "in
//!   body" parses `select` content itself, and `Mode` has no value for them.
//! - Found by the equivalence proofs (each stated in its lemma): the WHATWG
//!   "after head" anything-else entry also sets the frameset-ok flag to
//!   "ok"; for a start tag `caption`, …, `tr` "in cell", the W3C checks
//!   for a `td` or `th` element in table scope and ignores the token
//!   without one, where the WHATWG text asserts there is one.
//! - Found by the "in body", "in table" and "in table text" proofs
//!   ([`equivalence_body`]): the WHATWG adds `hgroup`, `menu` and `search`
//!   to "in body"'s block start and end tags, `select` to its block end
//!   tags and `keygen` to its void start tags; its `input`, `hr`, `option`
//!   and `optgroup` entries have steps for a `select` element in scope (or
//!   a `select` fragment context), and its `select` entry no "in select"
//!   switch; its `form` entries ("in body", "in table") test "parsing
//!   template contents", also true for a `template` fragment context; "in
//!   table" also sends characters to "in table text" when the current node
//!   is a `template`; the adoption agency algorithm's steps 15 and 18 use
//!   the adjusted insertion location (the redirection map) and, at step
//!   15, remove last node before checking whether to insert it; and an
//!   empty pending table character list inserts nothing in the WHATWG
//!   transcription (docs/ERRATA.md) but, read literally, an empty `Text`
//!   node in the W3C text.
//! - Not proven: that the W3C's and the WHATWG transcription's lists of
//!   DOCTYPE identifiers ("initial") classify every token alike
//!   ([`equivalence::lemma_initial_doctype`] takes it as a precondition).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

pub mod after;
pub mod body;
pub mod early;
pub mod equivalence;
pub mod equivalence_body;
pub mod equivalence_foreign;
pub mod foreign;
pub mod initial;

pub mod tables;
pub mod template;
pub mod text;

#[cfg(verus_only)]
pub use after::*;
#[cfg(verus_only)]
pub use body::*;
#[cfg(verus_only)]
pub use early::*;
#[cfg(verus_only)]
pub use foreign::*;
#[cfg(verus_only)]
pub use initial::*;
#[cfg(verus_only)]
pub use tables::*;
#[cfg(verus_only)]
pub use template::*;
#[cfg(verus_only)]
pub use text::*;

/// Every name of the transcription, of the reused parts of
/// [`crate::spec`] and of this module, for the ghost imports of the
/// submodules (`use super::spec::*;`).
mod spec {
    #[cfg(verus_only)]
    pub use super::*;
    #[cfg(verus_only)]
    pub use crate::spec::*;
}

verus! {

// ---------------------------------------------------------------------
// The wording of the entries

/// "A character token that is one of U+0009 CHARACTER TABULATION, U+000A
/// LINE FEED (LF), U+000C FORM FEED (FF), U+000D CARRIAGE RETURN (CR), or
/// U+0020 SPACE".
pub open spec fn w3c_space_char(t: Tok) -> bool {
    match t {
        Tok::Char(c) => c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20,
        _ => false,
    }
}

/// "A start tag whose tag name is `tag`".
pub open spec fn w3c_start(t: Tok, tag: Tag) -> bool {
    match t {
        Tok::Start(tt) => tt.tag == tag,
        _ => false,
    }
}

/// "An end tag whose tag name is `tag`".
pub open spec fn w3c_end(t: Tok, tag: Tag) -> bool {
    match t {
        Tok::End(tt) => tt.tag == tag,
        _ => false,
    }
}

/// The token's tag name as a [`Tag`] (`Tag::Other` for a token that is not
/// a tag).
pub open spec fn w3c_tag(t: Tok) -> Tag {
    match t {
        Tok::Start(tt) => tt.tag,
        Tok::End(tt) => tt.tag,
        _ => Tag::Other,
    }
}

/// The tag token of a start or end tag token.
pub open spec fn w3c_tag_tok(t: Tok) -> TagTok {
    match t {
        Tok::Start(tt) => tt,
        Tok::End(tt) => tt,
        _ => TagTok { name: seq![], tag: Tag::Other, attrs: seq![], self_closing: false },
    }
}

/// "the current node" is an HTML element named `tag`.
pub open spec fn w3c_current_is(p: Parser, tag: Tag) -> bool {
    is_html(current_node(p), tag)
}

/// "Pop the current node off the stack of open elements" and "switch the
/// insertion mode to `m`".
pub open spec fn w3c_pop_and_switch(p: Parser, m: Mode) -> Parser {
    Parser { mode: m, ..pop(p) }
}

} // verus!
