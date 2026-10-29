//! Executable-style specification of HTML §13.2.3.2 "Determining the
//! character encoding" (the encoding sniffing algorithm, the prescan, "get
//! an attribute" and "get an XML encoding"), "the algorithm for extracting a
//! character encoding from a meta element" (in "Fetching resources"), and
//! §13.2.3.4 "Changing the encoding while parsing",
//! transcribed from the standard (whatwg/html commit
//! `939677714df7379fee3667040113b41c91c851e7`). Nothing here runs.
//!
//! Modelling choices (each a deviation in form, never in meaning):
//! - The body is held whole. "The user agent may wait for more bytes"
//!   (step 3) becomes: the prescan's end condition is "the first 1024
//!   bytes", the bound the standard encourages ("User agents are
//!   encouraged to only prescan the first 1024 bytes"); the prescan reads
//!   `bytes` cut to its first 1024 ([`prescan_input`]), and running out of
//!   those is "reaching its end condition".
//! - Step 2, the user's override, never applies: this browser offers none
//!   (Encoding §15 discourages it).
//! - Step 4's transport layer encoding is `transport`: the caller gives the
//!   encoding "get an encoding" finds for the `charset` parameter of the
//!   response's parsed `Content-Type` ([`transport_encoding`], over
//!   `clazel-mime`'s MIME type record), or `None`. "And it is supported":
//!   every encoding of the Encoding Standard is (HTML §13.2.3.3 "User
//!   agents must support the encodings defined in Encoding"); one with no
//!   decoder yet is shown as unsupported by the renderer, not replaced
//!   (Phase 4 item 4.0(b)).
//! - Steps 6, 7 and 8 never apply: the parser has no container document
//!   (no nested browsing contexts in this phase), keeps no history of
//!   pages' encodings, and does no frequency analysis.
//! - Step 9's "implementation-defined or user-specified default" is
//!   windows-1252, the suggested default for most locales in the
//!   standard's table (and what html5lib-tests expects).
//! - The prescan's "position" is an index into `b: Seq<u8>`; "runs out of
//!   bytes" is reading at an index at or past `b.len()`, and aborts the
//!   prescan (its result is then "get an XML encoding" of `b`). Matching
//!   "a sequence of bytes starting with" a pattern needs the whole pattern
//!   within `b`; a shorter remainder is "any other byte". (Every pattern
//!   starts with 0x3C and every branch that matches it reads on past it, so
//!   at the end of `b` both readings abort the prescan.)
//! - Strings the prescan builds ("attribute name", "attribute value") are
//!   `Seq<u8>`: each code point appended is a byte's value or that plus
//!   0x20, so below 0x100. "Get an encoding" receives them as code points
//!   ([`as_string`]).
//! - Each "jump"/"return to the step labeled" loop is a recursive function
//!   over the position. Each recursive call is guarded by the fact that
//!   makes the position move forward within the bytes: a search returns a
//!   position at or after where it started and inside `b`, and "get an
//!   attribute" moves the position when it finds an attribute. The guards
//!   always hold (the executable code, proven equal to these functions,
//!   relies on the same facts, and `lemmas.rs` states them), so they change
//!   no result; the `else` branches marked "Unreachable" are never taken.
//! - `charset` (null, failure or an encoding) is [`Charset`]; `need pragma`
//!   (null, true or false) is `Option<bool>`.
//! - "Extracting a character encoding from a meta element" returns the
//!   substring it would give "get an encoding" ([`extract_label`]), and
//!   [`extract`] applies "get an encoding" to it, as the steps say; split so
//!   that facts about the string can be stated without the label table.
//! - §13.2.3.4 "change the encoding" is [`change_the_encoding`]: the parser
//!   holds the whole body, so step 5's change "on the fly" (a "may") is
//!   never taken, and step 6 becomes "restart with the new encoding,
//!   confidence certain" (the caller decodes and parses again from the
//!   start; the second pass, with confidence certain, never asks again).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "The confidence is either tentative or certain" (§13.2.3.1; "irrelevant"
/// applies only to a parser not fed bytes).
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Confidence {
    /// tentative
    Tentative,
    /// certain
    Certain,
}

/// The prescan's end condition: the first 1024 bytes.
pub open spec fn prescan_limit() -> nat {
    1024
}

/// What the prescan reads: the first 1024 bytes of the body.
pub open spec fn prescan_input(bytes: Seq<u8>) -> Seq<u8> {
    if bytes.len() <= prescan_limit() {
        bytes
    } else {
        bytes.subrange(0, prescan_limit() as int)
    }
}

/// A string of byte-valued code points, as "get an encoding" takes it.
pub open spec fn as_string(s: Seq<u8>) -> Seq<u32> {
    s.map_values(|b: u8| b as u32)
}

/// 0x09 (HT), 0x0A (LF), 0x0C (FF), 0x0D (CR) or 0x20 (SP): the bytes of
/// ASCII whitespace (Infra §4.6), as the prescan lists them.
pub open spec fn is_space(b: u8) -> bool {
    b == 0x09 || b == 0x0A || b == 0x0C || b == 0x0D || b == 0x20
}

/// An ASCII upper alpha byte, 0x41 (A) to 0x5A (Z).
pub open spec fn is_upper(b: u8) -> bool {
    0x41 <= b <= 0x5A
}

/// The byte, lowered if it is an ASCII upper alpha ("append the code point
/// b+0x20").
pub open spec fn lower(b: u8) -> u8 {
    if is_upper(b) {
        (b + 0x20) as u8
    } else {
        b
    }
}

/// `b` from `pos` starts with `pattern` (all of it within `b`).
pub open spec fn starts_at(b: Seq<u8>, pos: nat, pattern: Seq<u8>) -> bool {
    pos + pattern.len() <= b.len() && b.subrange(pos as int, (pos + pattern.len()) as int) == pattern
}

/// `b` from `pos` is `<meta` (any ASCII case) followed by one of 0x09, 0x0A,
/// 0x0C, 0x0D, 0x20, 0x2F.
pub open spec fn starts_meta(b: Seq<u8>, pos: nat) -> bool {
    let p = pos as int;
    p + 6 <= b.len() && b[p] == 0x3C && (b[p + 1] == 0x4D || b[p + 1] == 0x6D) && (b[p + 2] == 0x45 || b[p + 2]
        == 0x65) && (b[p + 3] == 0x54 || b[p + 3] == 0x74) && (b[p + 4] == 0x41 || b[p + 4] == 0x61) && (is_space(
        b[p + 5],
    ) || b[p + 5] == 0x2F)
}

/// An ASCII letter byte, A to Z or a to z.
pub open spec fn is_letter(c: u8) -> bool {
    (0x41 <= c <= 0x5A) || (0x61 <= c <= 0x7A)
}

/// `b` from `pos` is 0x3C, optionally 0x2F, then an ASCII letter.
pub open spec fn starts_tag(b: Seq<u8>, pos: nat) -> bool {
    let p = pos as int;
    (p + 2 <= b.len() && b[p] == 0x3C && is_letter(b[p + 1])) || (p + 3 <= b.len() && b[p] == 0x3C && b[p + 1]
        == 0x2F && is_letter(b[p + 2]))
}

/// The first `q` from `q` with `b[q]` = 0x3E (>) and `b[q - 1]`, `b[q - 2]`
/// = 0x2D (-), or `None` when the bytes run out.
pub open spec fn find_comment_end(b: Seq<u8>, q: nat) -> Option<nat>
    decreases b.len() - q,
{
    if q >= b.len() {
        None
    } else if q >= 2 && b[q as int] == 0x3E && b[q - 1] == 0x2D && b[q - 2] == 0x2D {
        Some(q)
    } else {
        find_comment_end(b, q + 1)
    }
}

/// The first `q` from `q` with `b[q]` = 0x3E (>), or `None`.
pub open spec fn find_gt(b: Seq<u8>, q: nat) -> Option<nat>
    decreases b.len() - q,
{
    if q >= b.len() {
        None
    } else if b[q as int] == 0x3E {
        Some(q)
    } else {
        find_gt(b, q + 1)
    }
}

/// The first `q` from `q` with `b[q]` one of 0x09, 0x0A, 0x0C, 0x0D, 0x20,
/// 0x3E, or `None`.
pub open spec fn find_tag_end(b: Seq<u8>, q: nat) -> Option<nat>
    decreases b.len() - q,
{
    if q >= b.len() {
        None
    } else if is_space(b[q as int]) || b[q as int] == 0x3E {
        Some(q)
    } else {
        find_tag_end(b, q + 1)
    }
}

/// What "get an attribute" gives: the prescan aborts (the bytes ran out),
/// there is no attribute, or an attribute; with the position it stopped at.
pub enum Attr {
    /// The bytes ran out: abort the prescan.
    Abort,
    /// "There isn't one", with the position.
    None(nat),
    /// An attribute's name and value, and the position.
    Some(Seq<u8>, Seq<u8>, nat),
}

/// "Get an attribute", steps 11 and 12: an unquoted value.
pub open spec fn attr_unquoted(b: Seq<u8>, pos: nat, name: Seq<u8>, value: Seq<u8>) -> Attr
    decreases b.len() - pos,
{
    if pos >= b.len() {
        Attr::Abort
    } else {
        let c = b[pos as int];
        // 11. "Process the byte at position as follows:"
        if is_space(c) || c == 0x3E {
            // 0x09, 0x0A, 0x0C, 0x0D, 0x20 or 0x3E: "Abort the get an
            // attribute algorithm. The attribute's name is the value of
            // attribute name and its value is the value of attribute value."
            Attr::Some(name, value, pos)
        } else {
            // A-Z: append b+0x20; anything else: append the byte.
            // 12. "Advance position to the next byte and return to the
            //     previous step."
            attr_unquoted(b, pos + 1, name, value.push(lower(c)))
        }
    }
}

/// "Get an attribute", step 10's quoted case: from the byte after the
/// opening `quote`.
pub open spec fn attr_quoted(b: Seq<u8>, pos: nat, name: Seq<u8>, value: Seq<u8>, quote: u8) -> Attr
    decreases b.len() - pos,
{
    // 10.2 "Quote loop: Advance position to the next byte." (done by the
    // caller, and below)
    if pos >= b.len() {
        Attr::Abort
    } else if b[pos as int] == quote {
        // 10.3 "If the value of the byte at position is the value of b,
        //      then advance position to the next byte and abort the "get an
        //      attribute" algorithm. The attribute's name is the value of
        //      attribute name, and its value is the value of attribute
        //      value."
        Attr::Some(name, value, pos + 1)
    } else {
        // 10.4 A-Z: append a code point 0x20 more; 10.5 otherwise append
        // the byte's value. 10.6 "Return to the step above labeled quote
        // loop."
        attr_quoted(b, pos + 1, name, value.push(lower(b[pos as int])), quote)
    }
}

/// "Get an attribute", steps 9 and 10: the value.
pub open spec fn attr_value(b: Seq<u8>, pos: nat, name: Seq<u8>) -> Attr
    decreases b.len() - pos,
{
    if pos >= b.len() {
        Attr::Abort
    } else {
        let c = b[pos as int];
        if is_space(c) {
            // 9. "Value: If the byte at position is one of 0x09, 0x0A, 0x0C,
            //    0x0D, or 0x20, then advance position to the next byte, then,
            //    repeat this step."
            attr_value(b, pos + 1, name)
        } else if c == 0x22 || c == 0x27 {
            // 10. 0x22 or 0x27: 10.1 "Let b be the value of the byte at
            //     position." 10.2 "Quote loop: Advance position to the next
            //     byte."
            attr_quoted(b, pos + 1, name, seq![], c)
        } else if c == 0x3E {
            // 0x3E: "Abort the get an attribute algorithm. The attribute's
            // name is the value of attribute name, its value is the empty
            // string."
            Attr::Some(name, seq![], pos)
        } else {
            // A-Z: "Append a code point b+0x20 to attribute value ... Advance
            // position to the next byte." Anything else: append the byte,
            // advance. Then step 11.
            attr_unquoted(b, pos + 1, name, seq![lower(c)])
        }
    }
}

/// "Get an attribute", steps 6 to 8: spaces after the name.
pub open spec fn attr_spaces(b: Seq<u8>, pos: nat, name: Seq<u8>) -> Attr
    decreases b.len() - pos,
{
    if pos >= b.len() {
        Attr::Abort
    } else if is_space(b[pos as int]) {
        // 6. "Spaces: If the byte at position is one of 0x09, 0x0A, 0x0C,
        //    0x0D, or 0x20, then advance position to the next byte, then,
        //    repeat this step."
        attr_spaces(b, pos + 1, name)
    } else if b[pos as int] != 0x3D {
        // 7. "If the byte at position is not 0x3D (=), abort the get an
        //    attribute algorithm. The attribute's name is the value of
        //    attribute name, its value is the empty string."
        Attr::Some(name, seq![], pos)
    } else {
        // 8. "Advance position past the 0x3D (=) byte."
        attr_value(b, pos + 1, name)
    }
}

/// "Get an attribute", steps 4 and 5: the name.
pub open spec fn attr_name(b: Seq<u8>, pos: nat, name: Seq<u8>) -> Attr
    decreases b.len() - pos,
{
    if pos >= b.len() {
        Attr::Abort
    } else {
        let c = b[pos as int];
        // 4. "Process the byte at position as follows:"
        if c == 0x3D && name.len() > 0 {
            // 0x3D and "the attribute name is longer than the empty string":
            // "Advance position to the next byte and jump to the step below
            // labeled value."
            attr_value(b, pos + 1, name)
        } else if is_space(c) {
            // 0x09, 0x0A, 0x0C, 0x0D, 0x20: "Jump to the step below labeled
            // spaces."
            attr_spaces(b, pos, name)
        } else if c == 0x2F || c == 0x3E {
            // 0x2F or 0x3E: "Abort the get an attribute algorithm. The
            // attribute's name is the value of attribute name, its value is
            // the empty string."
            Attr::Some(name, seq![], pos)
        } else {
            // A-Z: append b+0x20; anything else: append the byte.
            // 5. "Advance position to the next byte and return to the
            //    previous step."
            attr_name(b, pos + 1, name.push(lower(c)))
        }
    }
}

/// "Get an attribute" (§13.2.3.2, <https://html.spec.whatwg.org/multipage/parsing.html#concept-get-attributes-when-sniffing>)
/// at `pos`.
pub open spec fn get_attribute(b: Seq<u8>, pos: nat) -> Attr
    decreases b.len() - pos,
{
    if pos >= b.len() {
        Attr::Abort
    } else if is_space(b[pos as int]) || b[pos as int] == 0x2F {
        // 1. "If the byte at position is one of 0x09, 0x0A, 0x0C, 0x0D,
        //    0x20, or 0x2F, then advance position to the next byte and redo
        //    this step."
        get_attribute(b, pos + 1)
    } else if b[pos as int] == 0x3E {
        // 2. "If the byte at position is 0x3E (>), then abort the get an
        //    attribute algorithm. There isn't one."
        Attr::None(pos)
    } else {
        // 3. "Otherwise, the byte at position is the start of the attribute
        //    name. Let attribute name and attribute value be the empty
        //    string." 4. (attr_name)
        attr_name(b, pos, seq![])
    }
}

/// `charset` in the `<meta>` steps: "the null value (which ... is distinct
/// from an unrecognized encoding or the empty string)", failure, or an
/// encoding.
pub enum Charset {
    /// null
    Null,
    /// failure ("get an encoding" found none)
    Failure,
    /// an encoding
    Encoding(clazel_encoding::labels::spec::Encoding),
}

/// The result of "getting an encoding" as [`Charset`].
pub open spec fn charset_of(r: Option<clazel_encoding::labels::spec::Encoding>) -> Charset {
    match r {
        Some(e) => Charset::Encoding(e),
        None => Charset::Failure,
    }
}

/// The ASCII bytes of `charset`.
pub open spec fn charset_word() -> Seq<u8> {
    seq![0x63u8, 0x68u8, 0x61u8, 0x72u8, 0x73u8, 0x65u8, 0x74u8]
}

/// Bytes `t` to 6 of `s` from `k` match "charset" ignoring ASCII case.
pub open spec fn charset_from(s: Seq<u8>, k: nat, t: nat) -> bool
    decreases 7 - t,
{
    t >= 7 || (lower(s[(k + t) as int]) == charset_word()[t as int] && charset_from(s, k, t + 1))
}

/// `s` from `k` is an ASCII case-insensitive match for "charset".
pub open spec fn charset_at(s: Seq<u8>, k: nat) -> bool {
    k + 7 <= s.len() && charset_from(s, k, 0)
}

/// The first `k` from `k` where "charset" starts, or `None`.
pub open spec fn find_charset(s: Seq<u8>, k: nat) -> Option<nat>
    decreases s.len() - k,
{
    if k + 7 > s.len() {
        None
    } else if charset_at(s, k) {
        Some(k)
    } else {
        find_charset(s, k + 1)
    }
}

/// The first `k` from `k` that is not ASCII whitespace (or `s.len()`).
pub open spec fn skip_spaces(s: Seq<u8>, k: nat) -> nat
    decreases s.len() - k,
{
    if k < s.len() && is_space(s[k as int]) {
        skip_spaces(s, k + 1)
    } else {
        k
    }
}

/// The first `k` from `k` with `s[k]` = `c`, or `None`.
pub open spec fn find_byte(s: Seq<u8>, k: nat, c: u8) -> Option<nat>
    decreases s.len() - k,
{
    if k >= s.len() {
        None
    } else if s[k as int] == c {
        Some(k)
    } else {
        find_byte(s, k + 1, c)
    }
}

/// The first `k` from `k` with `s[k]` ASCII whitespace or 0x3B (;), or
/// `s.len()`.
pub open spec fn find_value_end(s: Seq<u8>, k: nat) -> nat
    decreases s.len() - k,
{
    if k >= s.len() || is_space(s[k as int]) || s[k as int] == 0x3B {
        k
    } else {
        find_value_end(s, k + 1)
    }
}

/// "The algorithm for extracting a character encoding from a meta
/// element" (<https://html.spec.whatwg.org/multipage/urls-and-fetching.html#algorithm-for-extracting-a-character-encoding-from-a-meta-element>),
/// from step 2 at `position`: the substring it gets an encoding from, or
/// `None` for "nothing".
pub open spec fn extract_label_from(s: Seq<u8>, position: nat) -> Option<Seq<u8>>
    decreases s.len() - position,
{
    // 2. "Loop: Find the first seven characters in s after position that are
    //    an ASCII case-insensitive match for the word "charset". If no such
    //    match is found, return nothing."
    match find_charset(s, position) {
        None => None,
        Some(k) => {
            // 3. "Skip any ASCII whitespace that immediately follow the word
            //    "charset" (there might not be any)."
            let j = skip_spaces(s, k + 7);
            if j >= s.len() || s[j as int] != 0x3D {
                // 4. "If the next character is not a U+003D EQUALS SIGN (=),
                //    then move position to point just before that next
                //    character, and jump back to the step labeled loop."
                if position < j <= s.len() {
                    extract_label_from(s, j)
                } else {
                    // Unreachable: position <= k, k + 7 <= j <= s.len().
                    None
                }
            } else {
                // 5. "Skip any ASCII whitespace that immediately follow the
                //    equals sign (there might not be any)."
                let v = skip_spaces(s, j + 1);
                // 6. "Process the next character as follows:"
                if v >= s.len() {
                    // "If there is no next character": "Return nothing."
                    None
                } else if s[v as int] == 0x22 || s[v as int] == 0x27 {
                    match find_byte(s, v + 1, s[v as int]) {
                        // A quotation mark or apostrophe "and there is a
                        // later" one: "Return the result of getting an
                        // encoding from the substring that is between this
                        // character and the next earliest occurrence of this
                        // character."
                        Some(e) => Some(s.subrange((v + 1) as int, e as int)),
                        // "If it is an unmatched U+0022 QUOTATION MARK
                        // character (") / U+0027 APOSTROPHE character ('),"
                        // "Return nothing."
                        None => None,
                    }
                } else {
                    // "Otherwise": "Return the result of getting an encoding
                    // from the substring that consists of this character up
                    // to but not including the first ASCII whitespace or
                    // U+003B SEMICOLON character (;), or the end of s,
                    // whichever comes first."
                    Some(s.subrange(v as int, find_value_end(s, v) as int))
                }
            }
        },
    }
}

/// See [`extract_label_from`]: "1. Let position be a pointer into s,
/// initially pointing at the start of the string."
pub open spec fn extract_label(s: Seq<u8>) -> Option<Seq<u8>> {
    extract_label_from(s, 0)
}

/// The algorithm for extracting a character encoding from a meta element:
/// an encoding, or `None` for "nothing" (a label that names no encoding
/// gives failure, which is not "a character encoding" either).
pub open spec fn extract(s: Seq<u8>) -> Option<clazel_encoding::labels::spec::Encoding> {
    match extract_label(s) {
        Some(label) => clazel_encoding::labels::spec::get_an_encoding(as_string(label)),
        None => None,
    }
}

/// The ASCII bytes of `http-equiv`.
pub open spec fn http_equiv() -> Seq<u8> {
    seq![0x68u8, 0x74u8, 0x74u8, 0x70u8, 0x2Du8, 0x65u8, 0x71u8, 0x75u8, 0x69u8, 0x76u8]
}

/// The ASCII bytes of `content`.
pub open spec fn content() -> Seq<u8> {
    seq![0x63u8, 0x6Fu8, 0x6Eu8, 0x74u8, 0x65u8, 0x6Eu8, 0x74u8]
}

/// The ASCII bytes of `content-type`.
pub open spec fn content_type() -> Seq<u8> {
    seq![0x63u8, 0x6Fu8, 0x6Eu8, 0x74u8, 0x65u8, 0x6Eu8, 0x74u8, 0x2Du8, 0x74u8, 0x79u8, 0x70u8, 0x65u8]
}

/// The ASCII bytes of `charset`.
pub open spec fn charset_name() -> Seq<u8> {
    charset_word()
}

/// `name` is among `list`'s items from `i`.
pub open spec fn in_list(list: Seq<Seq<u8>>, name: Seq<u8>, i: nat) -> bool
    decreases list.len() - i,
{
    i < list.len() && (list[i as int] == name || in_list(list, name, i + 1))
}

/// The state of the `<meta>` steps.
pub struct Meta {
    /// attribute list
    pub attribute_list: Seq<Seq<u8>>,
    /// got pragma
    pub got_pragma: bool,
    /// need pragma: null, true or false
    pub need_pragma: Option<bool>,
    /// charset
    pub charset: Charset,
}

/// What the `<meta>` steps do next: return an encoding, go to "next byte"
/// from a position, or abort the prescan.
pub enum MetaResult {
    /// "Return charset."
    Return(clazel_encoding::labels::spec::Encoding),
    /// "Jump to the step below labeled next byte", from this position.
    NextByte(nat),
    /// The bytes ran out.
    Abort,
}

/// The `<meta>` steps' "Processing" (steps 11 to 16), at position `pos`.
pub open spec fn meta_processing(m: Meta, pos: nat) -> MetaResult {
    if m.need_pragma is None {
        // 11. "Processing: If need pragma is null, then jump to the step
        //     below labeled next byte."
        MetaResult::NextByte(pos)
    } else if m.need_pragma == Some(true) && !m.got_pragma {
        // 12. "If need pragma is true but got pragma is false, then jump to
        //     the step below labeled next byte."
        MetaResult::NextByte(pos)
    } else {
        match m.charset {
            // 13. "If charset is failure, then jump to the step below
            //     labeled next byte." (charset is never null here: need
            //     pragma is set only together with charset; were it null,
            //     there would be nothing to return either.)
            Charset::Failure | Charset::Null => MetaResult::NextByte(pos),
            Charset::Encoding(e) => {
                // 14. "If charset is UTF-16BE/LE, then set charset to UTF-8."
                let e = if e == clazel_encoding::labels::spec::Encoding::Utf16Be || e
                    == clazel_encoding::labels::spec::Encoding::Utf16Le {
                    clazel_encoding::labels::spec::Encoding::Utf8
                } else {
                    e
                };
                // 15. "If charset is x-user-defined, then set charset to
                //     windows-1252."
                let e = if e == clazel_encoding::labels::spec::Encoding::XUserDefined {
                    clazel_encoding::labels::spec::Encoding::Windows1252
                } else {
                    e
                };
                // 16. "Return charset."
                MetaResult::Return(e)
            },
        }
    }
}

/// The `<meta>` steps' step 9, for one attribute: the new state.
pub open spec fn meta_attribute(m: Meta, name: Seq<u8>, value: Seq<u8>) -> Meta {
    if name == http_equiv() {
        // "If the attribute's name is "http-equiv"": "If the attribute's
        // value is "content-type", then set got pragma to true."
        if value == content_type() {
            Meta { got_pragma: true, ..m }
        } else {
            m
        }
    } else if name == content() {
        // "If the attribute's name is "content"": "Apply the algorithm for
        // extracting a character encoding from a meta element, giving the
        // attribute's value as the string to parse. If a character encoding
        // is returned, and if charset is still set to null, let charset be
        // the encoding returned, and set need pragma to true."
        match extract(value) {
            Some(e) => if m.charset is Null {
                Meta { charset: Charset::Encoding(e), need_pragma: Some(true), ..m }
            } else {
                m
            },
            None => m,
        }
    } else if name == charset_name() {
        // "If the attribute's name is "charset"": "Let charset be the result
        // of getting an encoding from the attribute's value, and set need
        // pragma to false."
        Meta {
            charset: charset_of(clazel_encoding::labels::spec::get_an_encoding(as_string(value))),
            need_pragma: Some(false),
            ..m
        }
    } else {
        m
    }
}

/// The `<meta>` steps from "Attributes" (step 6) at `pos`.
pub open spec fn meta_attributes(b: Seq<u8>, pos: nat, m: Meta) -> MetaResult
    decreases b.len() - pos,
{
    // 6. "Attributes: Get an attribute and its value. If no attribute was
    //    sniffed, then jump to the processing step below."
    match get_attribute(b, pos) {
        Attr::Abort => MetaResult::Abort,
        Attr::None(p) => meta_processing(m, p),
        Attr::Some(name, value, p) => {
            if p <= pos || p > b.len() {
                // Unreachable: "get an attribute" moves the position when it
                // finds an attribute (lemmas::lemma_attribute_advances).
                MetaResult::Abort
            } else if in_list(m.attribute_list, name, 0) {
                // 7. "If the attribute's name is already in attribute list,
                //    then return to the step labeled attributes."
                meta_attributes(b, p, m)
            } else {
                // 8. "Add the attribute's name to attribute list."
                let m = Meta { attribute_list: m.attribute_list.push(name), ..m };
                // 9. the switch; 10. "Return to the step labeled attributes."
                meta_attributes(b, p, meta_attribute(m, name, value))
            }
        },
    }
}

/// "Repeatedly get an attribute until no further attributes can be found"
/// from `pos`: the position where none was found, or `None` if the bytes
/// ran out.
pub open spec fn skip_attributes(b: Seq<u8>, pos: nat) -> Option<nat>
    decreases b.len() - pos,
{
    match get_attribute(b, pos) {
        Attr::Abort => None,
        Attr::None(p) => Some(p),
        Attr::Some(_, _, p) => if p <= pos || p > b.len() {
            // Unreachable, as in meta_attributes.
            None
        } else {
            skip_attributes(b, p)
        },
    }
}

/// The prescan from "Loop" (step 3) at `position`: `Some` with what it
/// returned, or `None` when it aborted.
pub open spec fn prescan_loop(b: Seq<u8>, position: nat) -> Option<clazel_encoding::labels::spec::Encoding>
    decreases b.len() - position,
{
    if position >= b.len() {
        // The bytes ran out: abort.
        None
    } else if starts_at(b, position, seq![0x3Cu8, 0x21u8, 0x2Du8, 0x2Du8]) {
        // 3. `<!--`: "Advance the position pointer so that it points at the
        //    first 0x3E byte which is preceded by two 0x2D bytes (i.e. at the
        //    end of an ASCII '-->' sequence) and comes after the 0x3C byte
        //    that was found. (The two 0x2D bytes can be the same as those in
        //    the '<!--' sequence.)"
        match find_comment_end(b, position + 4) {
            None => None,
            // 4. "Next byte: Move position so it points at the next byte in
            //    the input byte stream, and return to the step above labeled
            //    loop." (The guard always holds: a found byte is at or after
            //    where the search started, within b.)
            Some(q) => if position <= q < b.len() {
                prescan_loop(b, q + 1)
            } else {
                None
            },
        }
    } else if starts_meta(b, position) {
        // `<meta` and a space or slash: 1. "Advance the position pointer so
        // that it points at the next 0x09, 0x0A, 0x0C, 0x0D, 0x20, or 0x2F
        // byte (the one in sequence of characters matched above)." 2. to 5.
        // attribute list empty, got pragma false, need pragma null, charset
        // null.
        let m = Meta { attribute_list: seq![], got_pragma: false, need_pragma: None, charset: Charset::Null };
        match meta_attributes(b, position + 5, m) {
            MetaResult::Abort => None,
            MetaResult::Return(e) => Some(e),
            MetaResult::NextByte(p) => if position <= p < b.len() {
                prescan_loop(b, p + 1)
            } else {
                // Unreachable: the position only moves forward, within b.
                None
            },
        }
    } else if starts_tag(b, position) {
        // `<`, optionally `/`, and a letter: 1. "Advance the position pointer
        // so that it points at the next 0x09 (HT), 0x0A (LF), 0x0C (FF), 0x0D
        // (CR), 0x20 (SP), or 0x3E (>) byte." 2. "Repeatedly get an attribute
        // until no further attributes can be found, then jump to the step
        // below labeled next byte."
        match find_tag_end(b, position) {
            None => None,
            Some(q) => match skip_attributes(b, q) {
                None => None,
                Some(p) => if position <= p < b.len() {
                    prescan_loop(b, p + 1)
                } else {
                    // Unreachable: the position only moves forward, within b.
                    None
                },
            },
        }
    } else if starts_at(b, position, seq![0x3Cu8, 0x21u8]) || starts_at(b, position, seq![0x3Cu8, 0x2Fu8])
        || starts_at(b, position, seq![0x3Cu8, 0x3Fu8]) {
        // `<!`, `</` or `<?`: "Advance the position pointer so that it points
        // at the first 0x3E byte (>) that comes after the 0x3C byte that was
        // found."
        match find_gt(b, position + 1) {
            None => None,
            // (The guard always holds, as for comments.)
            Some(q) => if position <= q < b.len() {
                prescan_loop(b, q + 1)
            } else {
                None
            },
        }
    } else {
        // "Any other byte": "Do nothing with that byte." Then next byte.
        prescan_loop(b, position + 1)
    }
}

/// The first `k` from `k`, while `k < end`, where `encoding` starts in `b`.
pub open spec fn find_encoding_word(b: Seq<u8>, k: nat, end: nat) -> Option<nat>
    decreases end - k,
{
    if k >= end {
        None
    } else if starts_at(b, k, seq![0x65u8, 0x6Eu8, 0x63u8, 0x6Fu8, 0x64u8, 0x69u8, 0x6Eu8, 0x67u8]) {
        Some(k)
    } else {
        find_encoding_word(b, k + 1, end)
    }
}

/// The first `k` from `k` whose byte is above 0x20, or `b.len()`.
pub open spec fn skip_controls(b: Seq<u8>, k: nat) -> nat
    decreases b.len() - k,
{
    if k < b.len() && b[k as int] <= 0x20 {
        skip_controls(b, k + 1)
    } else {
        k
    }
}

/// Some byte of `s` from `i` is 0x20 or below.
pub open spec fn has_control(s: Seq<u8>, i: nat) -> bool
    decreases s.len() - i,
{
    i < s.len() && (s[i as int] <= 0x20 || has_control(s, i + 1))
}

/// "Get an XML encoding" (§13.2.3.2, <https://html.spec.whatwg.org/multipage/parsing.html#concept-get-xml-encoding-when-sniffing>)
/// of `b`; `None` is failure.
pub open spec fn get_xml_encoding(b: Seq<u8>) -> Option<clazel_encoding::labels::spec::Encoding> {
    // 1. "Let encodingPosition be a pointer to the start of the stream."
    // 2. "If encodingPosition does not point to the start of a byte sequence
    //    0x3C, 0x3F, 0x78, 0x6D, 0x6C (`<?xml`), then return failure."
    if !starts_at(b, 0, seq![0x3Cu8, 0x3Fu8, 0x78u8, 0x6Du8, 0x6Cu8]) {
        None
    } else {
        // 3. "Let xmlDeclarationEnd be a pointer to the next byte in the input
        //    byte stream which is 0x3E (>). If there is no such byte, then
        //    return failure."
        match find_gt(b, 0) {
            None => None,
            Some(end) => {
                // 4. "Set encodingPosition to the position of the first
                //    occurrence of the subsequence of bytes ... (`encoding`) at
                //    or after the current encodingPosition and before
                //    xmlDeclarationEnd. If there is no such sequence, then
                //    return failure."
                match find_encoding_word(b, 0, end) {
                    None => None,
                    Some(k) => {
                        // 5. "Advance encodingPosition past the 0x67 (g) byte."
                        // 6. "While the byte at encodingPosition is less than or
                        //    equal to 0x20 ..., advance encodingPosition to the
                        //    next byte."
                        let p = skip_controls(b, k + 8);
                        // 7. "If the byte at encodingPosition is not 0x3D (=),
                        //    then return failure." (No byte is not 0x3D.)
                        if p >= b.len() || b[p as int] != 0x3D {
                            None
                        } else {
                            // 8. "Advance encodingPosition to the next byte."
                            // 9. skip bytes up to 0x20 again.
                            let q = skip_controls(b, p + 1);
                            // 10. "Let quoteMark be the byte at
                            //     encodingPosition." 11. "If quoteMark is not
                            //     either 0x22 (") or 0x27 ('), then return
                            //     failure."
                            if q >= b.len() || !(b[q as int] == 0x22 || b[q as int] == 0x27) {
                                None
                            } else {
                                // 12. "Advance encodingPosition to the next
                                //     byte." 13. "Let encodingEndPosition be the
                                //     position of the next occurrence of
                                //     quoteMark at or after encodingPosition. If
                                //     quoteMark does not occur again, then return
                                //     failure."
                                match find_byte(b, q + 1, b[q as int]) {
                                    None => None,
                                    Some(e) => {
                                        // 14. "Let potentialEncoding be the
                                        //     sequence of the bytes between
                                        //     encodingPosition (inclusive) and
                                        //     encodingEndPosition (exclusive)."
                                        let potential = b.subrange((q + 1) as int, e as int);
                                        // 15. "If potentialEncoding contains one
                                        //     or more bytes whose byte value is
                                        //     0x20 or below, then return
                                        //     failure."
                                        if has_control(potential, 0) {
                                            None
                                        } else {
                                            // 16. "Let encoding be the result of
                                            //     getting an encoding given
                                            //     potentialEncoding isomorphic
                                            //     decoded."
                                            match clazel_encoding::labels::spec::get_an_encoding(as_string(potential)) {
                                                None => None,
                                                Some(enc) => {
                                                    // 17. "If the encoding is
                                                    //     UTF-16BE/LE, then change
                                                    //     it to UTF-8." 18. "Return
                                                    //     encoding."
                                                    if enc == clazel_encoding::labels::spec::Encoding::Utf16Be || enc
                                                        == clazel_encoding::labels::spec::Encoding::Utf16Le {
                                                        Some(clazel_encoding::labels::spec::Encoding::Utf8)
                                                    } else {
                                                        Some(enc)
                                                    }
                                                },
                                            }
                                        }
                                    },
                                }
                            }
                        }
                    },
                }
            },
        }
    }
}

/// "Prescan a byte stream to determine its encoding" (§13.2.3.2,
/// <https://html.spec.whatwg.org/multipage/parsing.html#prescan-a-byte-stream-to-determine-its-encoding>)
/// of `b`, the bytes up to the end condition. `None`: no encoding.
pub open spec fn prescan(b: Seq<u8>) -> Option<clazel_encoding::labels::spec::Encoding> {
    // 1. "Let position be a pointer to a byte in the input byte stream,
    //    initially pointing at the first byte."
    if starts_at(b, 0, seq![0x3Cu8, 0x00u8, 0x3Fu8, 0x00u8, 0x78u8, 0x00u8]) {
        // 2. "Prescan for UTF-16 XML declarations": 0x3C, 0x0, 0x3F, 0x0,
        //    0x78, 0x0: "Return UTF-16LE."
        Some(clazel_encoding::labels::spec::Encoding::Utf16Le)
    } else if starts_at(b, 0, seq![0x00u8, 0x3Cu8, 0x00u8, 0x3Fu8, 0x00u8, 0x78u8]) {
        // 0x0, 0x3C, 0x0, 0x3F, 0x0, 0x78: "Return UTF-16BE."
        Some(clazel_encoding::labels::spec::Encoding::Utf16Be)
    } else {
        // 3. and 4. (prescan_loop). "If at any point ... the user agent
        //    either runs out of bytes ... or reaches its end condition, then
        //    abort the prescan a byte stream to determine its encoding
        //    algorithm and return the result get an XML encoding applied to
        //    the same bytes that the prescan a byte stream to determine its
        //    encoding algorithm was applied to."
        match prescan_loop(b, 0) {
            Some(e) => Some(e),
            None => get_xml_encoding(b),
        }
    }
}

/// The encoding sniffing algorithm (§13.2.3.2,
/// <https://html.spec.whatwg.org/multipage/parsing.html#encoding-sniffing-algorithm>)
/// for the body `bytes` and the transport layer's encoding.
pub open spec fn sniff(bytes: Seq<u8>, transport: Option<clazel_encoding::labels::spec::Encoding>) -> (
    clazel_encoding::labels::spec::Encoding,
    Confidence,
) {
    // 1. "If the result of BOM sniffing is an encoding, return that encoding
    //    with confidence certain."
    match clazel_encoding::hooks::spec::bom_sniff(bytes) {
        Some(e) => (e, Confidence::Certain),
        // 2. The user's override: none (see the modelling choices).
        // 3. Waiting for bytes: the body is whole.
        None => match transport {
            // 4. "If the transport layer specifies a character encoding, and
            //    it is supported, return that encoding with the confidence
            //    certain."
            Some(e) => (e, Confidence::Certain),
            // 5. "Optionally, prescan the byte stream to determine its
            //    encoding, with the end condition being when the user agent
            //    decides that scanning further bytes would not be efficient
            //    [the first 1024 bytes]. ... If it returns a character
            //    encoding, then return the same encoding, with confidence
            //    tentative."
            None => match prescan(prescan_input(bytes)) {
                Some(e) => (e, Confidence::Tentative),
                // 6. to 8. do not apply (see the modelling choices).
                // 9. "Otherwise, return an implementation-defined or
                //    user-specified default character encoding, with the
                //    confidence tentative." (windows-1252)
                None => (clazel_encoding::labels::spec::Encoding::Windows1252, Confidence::Tentative),
            },
        },
    }
}

/// The transport layer's encoding (step 4): "get an encoding" of the value
/// of the `charset` parameter of the response's MIME type, `parameters`
/// being its parameters (an ordered map, `clazel-mime`'s record), or
/// `None` if it has none or names no encoding.
pub open spec fn transport_encoding(parameters: Seq<(Seq<u32>, Seq<u32>)>) -> Option<
    clazel_encoding::labels::spec::Encoding,
> {
    transport_from(parameters, 0)
}

/// See [`transport_encoding`]: the first parameter from `i` named
/// `charset` (an ordered map's keys are unique, so it is the one).
pub open spec fn transport_from(parameters: Seq<(Seq<u32>, Seq<u32>)>, i: nat) -> Option<
    clazel_encoding::labels::spec::Encoding,
>
    decreases parameters.len() - i,
{
    if i >= parameters.len() {
        None
    } else if parameters[i as int].0 == seq![0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32] {
        clazel_encoding::labels::spec::get_an_encoding(parameters[i as int].1)
    } else {
        transport_from(parameters, i + 1)
    }
}

/// §13.2.3.4 "change the encoding" (<https://html.spec.whatwg.org/multipage/parsing.html#change-the-encoding>),
/// asked with `new` while the parser uses `current`: `None` when the
/// confidence just becomes certain and nothing else changes, or `Some(e)`:
/// parse again from the start with `e` and confidence certain.
pub open spec fn change_the_encoding(
    current: clazel_encoding::labels::spec::Encoding,
    new: clazel_encoding::labels::spec::Encoding,
) -> Option<clazel_encoding::labels::spec::Encoding> {
    if current == clazel_encoding::labels::spec::Encoding::Utf16Be || current
        == clazel_encoding::labels::spec::Encoding::Utf16Le {
        // 1. "If the encoding that is already being used to interpret the
        //    input stream is UTF-16BE/LE, then set the confidence to certain
        //    and return. The new encoding is ignored."
        None
    } else {
        // 2. "If the new encoding is UTF-16BE/LE, then change it to UTF-8."
        let new = if new == clazel_encoding::labels::spec::Encoding::Utf16Be || new
            == clazel_encoding::labels::spec::Encoding::Utf16Le {
            clazel_encoding::labels::spec::Encoding::Utf8
        } else {
            new
        };
        // 3. "If the new encoding is x-user-defined, then change it to
        //    windows-1252."
        let new = if new == clazel_encoding::labels::spec::Encoding::XUserDefined {
            clazel_encoding::labels::spec::Encoding::Windows1252
        } else {
            new
        };
        if new == current {
            // 4. "If the new encoding is identical or equivalent to the
            //    encoding that is already being used to interpret the input
            //    stream, then set the confidence to certain and return."
            None
        } else {
            // 5. Changing on the fly is never done (a "may").
            // 6. "Otherwise, restart the navigate algorithm ... but this time
            //    skip the encoding sniffing algorithm and instead just set the
            //    encoding to the new encoding and the confidence to certain."
            Some(new)
        }
    }
}

} // verus!
