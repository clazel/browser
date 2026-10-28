//! HTML §13.2.6.4.10 the "in table text" insertion mode.
//!
//! Modelling choice: the pending table character tokens are the code points
//! of `Parser::pending_table_text` (each character token is one code point).
//! Reprocessing them "using the rules given in the "anything else" entry in
//! the "in table" insertion mode" is a direct call of
//! [`in_table_anything_else`] for each, in order ([`reprocess_pending`]), not
//! an `Outcome`: the token being processed is a different one (the token
//! that ended the run of characters), which is reprocessed afterwards. Those
//! rules never apply the "in table text" rules directly, so the call is not
//! recursive.

#[allow(unused_imports)]
use super::super::dispatch::*;
#[allow(unused_imports)]
use super::super::insert::*;
#[allow(unused_imports)]
use super::super::state::*;
#[allow(unused_imports)]
use super::super::tags::*;
#[allow(unused_imports)]
use super::in_table::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Some character in `s` is not ASCII whitespace.
pub open spec fn has_non_whitespace(s: Seq<u32>) -> bool {
    exists|i: int| 0 <= i < s.len() && !is_ascii_whitespace(#[trigger] s[i])
}

/// "reprocess the character tokens in the pending table character tokens
/// list using the rules given in the "anything else" entry in the "in table"
/// insertion mode", from index `i` of `s`. The "in body" rules handle every
/// character token themselves (an `Outcome::Done`); the parser of any other
/// outcome would be carried on in the same way.
pub open spec fn reprocess_pending(env: EncFns, p: Parser, s: Seq<u32>, i: int) -> Parser
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        p
    } else {
        let q = outcome_parser(in_table_anything_else(env, p, Tok::Char(s[i])));
        reprocess_pending(env, q, s, i + 1)
    }
}

/// §13.2.6.4.10 the "in table text" insertion mode.
/// <https://html.spec.whatwg.org/multipage/parsing.html#parsing-main-intabletext>
pub open spec fn mode_in_table_text(env: EncFns, p: Parser, t: Tok) -> Outcome {
    if t is Char && t->Char_0 == 0 {
        // 1. "A character token that is U+0000 NULL"
        // "Parse error. Ignore the token."
        Outcome::Done(p)
    } else if t is Char {
        // 2. "Any other character token"
        // "Append the character token to the pending table character tokens
        // list."
        Outcome::Done(Parser { pending_table_text: p.pending_table_text.push(t->Char_0), ..p })
    } else {
        // 3. "Anything else"
        let pending = p.pending_table_text;
        let p1 = if has_non_whitespace(pending) {
            // "If any of the tokens in the pending table character tokens list
            // are character tokens that are not ASCII whitespace, then this is
            // a parse error: reprocess the character tokens in the pending
            // table character tokens list using the rules given in the
            // "anything else" entry in the "in table" insertion mode."
            reprocess_pending(env, p, pending, 0)
        } else if pending.len() == 0 {
            // "Otherwise, insert the characters given by the pending table
            // character tokens list." The list is empty when every character
            // token since "in table" was U+0000 NULL (case 1 ignores those).
            // There are then no characters to insert. Read literally, "insert
            // a character" with no characters would create an empty Text node
            // (its step 5), or take "the character of the character token
            // being processed", which is not a character token; the evident
            // intent is to insert nothing (docs/ERRATA.md, "in table text"
            // with an empty pending list).
            p
        } else {
            // "Otherwise, insert the characters given by the pending table
            // character tokens list."
            insert_characters(p, pending)
        };
        // "Switch the insertion mode to the original insertion mode and
        // reprocess the token."
        Outcome::Reprocess(Parser { mode: p1.original_mode, ..p1 }, t)
    }
}

} // verus!
