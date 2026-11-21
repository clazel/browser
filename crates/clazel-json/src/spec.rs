//! A transcription of ECMA-404's grammar, of the value `JSON.parse`
//! constructs from a text that matches it (ECMA-262 §25.5.1† JSON.parse,
//! abstract operation ParseJSON), and of QuoteJSONString (§25.5.2.3†).
//!
//! Sources, and what was and was not read:
//! - ECMA-404, The JSON Data Interchange Syntax, 2nd edition (December
//!   2017). Its productions are cited by name (`value`, `object`, `members`,
//!   `member`, `array`, `elements`, `element`, `string`, `characters`,
//!   `character`, `escape`, `hex`, `number`, `integer`, `digits`, `digit`,
//!   `onenine`, `fraction`, `exponent`, `sign`, `ws`), not by clause number.
//!   RFC 8259 §2 to §7 states the same grammar as ABNF and is the source of
//!   `independent.rs` (not written yet).
//! - ECMA-262, the edition `docs/phases/phase-7.md` item 7.1 will pin. Every
//!   ECMA-262 number below carries the † mark: it was written from memory,
//!   not read at a pinned commit, and must be checked against the commit
//!   this header pins once 7.1 has vendored one. **No text of either
//!   standard was available when this file was written.** The step
//!   comments quote from memory; a quotation may differ from the standard
//!   in wording. Re-read each against the pinned text before the crate's
//!   tier is raised.
//!
//! Modelling choices (the form differs from the standard; the meaning does
//! not, argued per item):
//!
//! - **Input.** The standard parses "StringToCodePoints(text)" (ParseJSON
//!   step 1†), a sequence of code points; here `Seq<u32>`, as in
//!   `clazel-base64`. A value above U+10FFFF is not a code point and
//!   matches no production. A lone surrogate is a code point and may occur
//!   inside a string, as in a JavaScript string.
//! - **ECMA-262 evaluates the text.** ParseJSON† wraps the text in
//!   parentheses and evaluates it as a Script. Both standards intend the
//!   result to be the grammar's reading of the text, so the tree is built
//!   directly from the grammar, with the string and number values below.
//! - **Strings** become `Seq<u16>`, a JavaScript string's code units. A
//!   `\uXXXX` escape contributes the one code unit it names, a lone
//!   surrogate included; a character from U+10000 up contributes its UTF-16
//!   pair (UTF16EncodeCodePoint, §11.1.3†).
//! - **Numbers** keep their source text, `Seq<u32>`: the standard gives them
//!   the Number value of the literal (StringToNumber, §7.1.4.1.1†), which is
//!   `clazel-js-number`'s concern (phase 7 item 7.11), not this crate's.
//! - **Objects** keep their members in source order and keep duplicate
//!   keys. In the engine a duplicate key overwrites the earlier value at the
//!   earlier position and `"__proto__"` is an ordinary key: both are
//!   properties of the JavaScript heap, which this crate does not model.
//! - **Recursive descent.** A production is a function from a text and a
//!   position to the value it reads and the position after it, or `None`
//!   where the text does not match. JSON is LL(1): the next code point
//!   decides every alternative, so no alternative needs backtracking. The
//!   grammar's right recursion (`digits`, `characters`, `elements`,
//!   `members`) is read greedily, which is the same language here: what
//!   follows `digits` in any context is never a digit, and what follows an
//!   `element` is `,` or `]`, never a continuation of the element.
//!   `ws` may stand wherever the grammar allows it between tokens;
//!   `skip_ws` reads the longest run, and `ws` before a token is read by
//!   the production that begins the token.
//! - **Nesting depth.** Neither standard bounds it. This crate does:
//!   `max_depth()` levels of arrays and objects, the outermost being level
//!   one, and a text that nests deeper is an error. For the engine that is a
//!   `SyntaxError` where V8 and SpiderMonkey would stop later (or throw a
//!   `RangeError`); it is a listed deviation (phase 7 item 7.11), chosen so
//!   the parser's recursion is bounded. `levels` counts the levels still
//!   allowed.
//! - **Errors** are `None`: the standard's SyntaxError carries no position
//!   or message that a caller could depend on.
//! - **Termination measure.** `parse_elements` and `parse_members` refuse an
//!   accumulator at least as long as the text. Each element or member
//!   consumes at least one code point, so the accumulator is shorter than
//!   the text and the refusal never fires (`lemmas.rs` will prove it);
//!   it only gives Verus a measure that does not depend on a result.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A JSON value as `JSON.parse` constructs it, with this crate's own tree
/// instead of the JavaScript heap's objects (see the modelling choices).
pub enum JsonValue {
    /// `null`.
    Null,
    /// `true` or `false`.
    Bool(bool),
    /// A number: the source text of its literal, ASCII code points.
    Number(Seq<u32>),
    /// A string: its UTF-16 code units.
    String(Seq<u16>),
    /// An array: its elements in order.
    Array(Seq<JsonValue>),
    /// An object: its members in source order, duplicate keys kept.
    Object(Seq<JsonMember>),
}

/// One `member` of an object: `string : element`.
pub struct JsonMember {
    /// The member's name, as a string value.
    pub key: Seq<u16>,
    /// The member's value.
    pub value: JsonValue,
}

/// The nesting bound: how many levels of arrays and objects a text may
/// have (see the modelling choices).
pub open spec fn max_depth() -> nat {
    512
}

// ---------------------------------------------------------------------
// ECMA-404 grammar: ws, and the small token productions.
// ---------------------------------------------------------------------

/// ECMA-404 `ws`: "Insignificant whitespace is allowed before or after any
/// token. Whitespace is any sequence of one or more of the following code
/// points: character tabulation (U+0009), line feed (U+000A), carriage
/// return (U+000D), and space (U+0020)."
pub open spec fn is_ws(c: u32) -> bool {
    c == 0x09 || c == 0x0A || c == 0x0D || c == 0x20
}

/// The position after the longest run of `ws` that starts at `pos`.
pub open spec fn skip_ws(s: Seq<u32>, pos: nat) -> nat
    decreases s.len() - pos,
{
    if pos < s.len() && is_ws(s[pos as int]) {
        skip_ws(s, pos + 1)
    } else {
        pos
    }
}

/// ECMA-404 `digit`: "0" through "9".
pub open spec fn is_digit(c: u32) -> bool {
    0x30 <= c && c <= 0x39
}

/// ECMA-404 `onenine`: "1" through "9".
pub open spec fn is_onenine(c: u32) -> bool {
    0x31 <= c && c <= 0x39
}

/// ECMA-404 `hex`: `digit`, "A" through "F", "a" through "f".
pub open spec fn hex_value(c: u32) -> Option<nat> {
    if is_digit(c) {
        Some((c - 0x30) as nat)
    } else if 0x41 <= c && c <= 0x46 {
        Some((c - 0x41 + 10) as nat)
    } else if 0x61 <= c && c <= 0x66 {
        Some((c - 0x61 + 10) as nat)
    } else {
        None
    }
}

/// The code point at `pos`, if the text has one there.
pub open spec fn is_at(s: Seq<u32>, pos: nat, c: u32) -> bool {
    pos < s.len() && s[pos as int] == c
}

/// The literal `lit` occurs at `pos`.
pub open spec fn matches_at(s: Seq<u32>, pos: nat, lit: Seq<u32>) -> bool {
    pos + lit.len() <= s.len() && s.subrange(pos as int, (pos + lit.len()) as int) == lit
}

/// The literal `true`.
pub open spec fn lit_true() -> Seq<u32> {
    seq![0x74u32, 0x72, 0x75, 0x65]
}

/// The literal `false`.
pub open spec fn lit_false() -> Seq<u32> {
    seq![0x66u32, 0x61, 0x6C, 0x73, 0x65]
}

/// The literal `null`.
pub open spec fn lit_null() -> Seq<u32> {
    seq![0x6Eu32, 0x75, 0x6C, 0x6C]
}

// ---------------------------------------------------------------------
// ECMA-404 grammar: numbers.
// ---------------------------------------------------------------------

/// ECMA-404 `digits`: "digit | digit digits", read greedily: the position
/// after the longest run of digits (which is `pos` if there is none).
pub open spec fn skip_digits(s: Seq<u32>, pos: nat) -> nat
    decreases s.len() - pos,
{
    if pos < s.len() && is_digit(s[pos as int]) {
        skip_digits(s, pos + 1)
    } else {
        pos
    }
}

/// ECMA-404 `integer`: "digit | onenine digits | "-" digit | "-" onenine
/// digits". Returns the position after it, or `None`.
pub open spec fn parse_integer(s: Seq<u32>, pos: nat) -> Option<nat> {
    // "-" is optional: the two "-" alternatives and the two without differ
    // only by it.
    let p = if is_at(s, pos, 0x2D) {
        pos + 1
    } else {
        pos
    };
    if is_at(s, p, 0x30) {
        // "digit", the digit being "0" (a "0" is not followed by digits:
        // it is `digit`, not `onenine digits`).
        Some(p + 1)
    } else if p < s.len() && is_onenine(s[p as int]) {
        // "onenine digits"
        Some(skip_digits(s, p + 1))
    } else {
        None
    }
}

/// ECMA-404 `fraction`: """" | "." digits". Returns the position after it.
/// Where "." is present but no digit follows, the text matches no
/// `number`, so `None` (reading "" instead would leave "." where no
/// production accepts it, so the text fails either way).
pub open spec fn parse_fraction(s: Seq<u32>, pos: nat) -> Option<nat> {
    if is_at(s, pos, 0x2E) {
        let q = skip_digits(s, pos + 1);
        if q > pos + 1 {
            Some(q)
        } else {
            None
        }
    } else {
        Some(pos)
    }
}

/// ECMA-404 `exponent`: """" | "E" sign digits | "e" sign digits", with
/// `sign` = """" | "+" | "-"". Returns the position after it. As for
/// `fraction`, an "E" without digits is `None`.
pub open spec fn parse_exponent(s: Seq<u32>, pos: nat) -> Option<nat> {
    if is_at(s, pos, 0x45) || is_at(s, pos, 0x65) {
        let p = if is_at(s, pos + 1, 0x2B) || is_at(s, pos + 1, 0x2D) {
            pos + 2
        } else {
            pos + 1
        };
        let q = skip_digits(s, p);
        if q > p {
            Some(q)
        } else {
            None
        }
    } else {
        Some(pos)
    }
}

/// ECMA-404 `number`: "integer fraction exponent". Returns the position
/// after it.
pub open spec fn parse_number(s: Seq<u32>, pos: nat) -> Option<nat> {
    match parse_integer(s, pos) {
        None => None,
        Some(p1) => match parse_fraction(s, p1) {
            None => None,
            Some(p2) => parse_exponent(s, p2),
        },
    }
}

// ---------------------------------------------------------------------
// ECMA-404 grammar: strings, and the string value (SV).
// ---------------------------------------------------------------------

/// UTF16EncodeCodePoint (ECMA-262 §11.1.3†): "If cp ≤ 0xFFFF, return the
/// String value consisting of the code unit whose numeric value is cp.
/// Otherwise, let cu1 be the code unit whose numeric value is
/// floor((cp - 0x10000) / 0x400) + 0xD800 and cu2 the code unit whose
/// numeric value is ((cp - 0x10000) modulo 0x400) + 0xDC00; return cu1
/// followed by cu2." For `cp <= 0x10FFFF`.
pub open spec fn utf16_encode_code_point(cp: u32) -> Seq<u16> {
    if cp <= 0xFFFF {
        seq![cp as u16]
    } else {
        seq![
            ((cp as int - 0x10000) / 0x400 + 0xD800) as u16,
            ((cp as int - 0x10000) % 0x400 + 0xDC00) as u16,
        ]
    }
}

/// ECMA-404 `escape` for the one-character escapes: """ | "\" | "/" | "b" |
/// "f" | "n" | "r" | "t"", and the code unit each stands for (ECMA-262's
/// JSON Single Character Escapes, SV of a JSON string†). `None` for any
/// other character, `u` included.
pub open spec fn escape_unit(e: u32) -> Option<u16> {
    if e == 0x22 {
        Some(0x22u16)  // \" quotation mark

    } else if e == 0x5C {
        Some(0x5Cu16)  // \\ reverse solidus

    } else if e == 0x2F {
        Some(0x2Fu16)  // \/ solidus

    } else if e == 0x62 {
        Some(0x08u16)  // \b backspace

    } else if e == 0x66 {
        Some(0x0Cu16)  // \f form feed

    } else if e == 0x6E {
        Some(0x0Au16)  // \n line feed

    } else if e == 0x72 {
        Some(0x0Du16)  // \r carriage return

    } else if e == 0x74 {
        Some(0x09u16)  // \t character tabulation

    } else {
        None
    }
}

/// ECMA-404 `escape`: ""u" hex hex hex hex": the value of the four hex
/// digits at `pos`, if all four are `hex`.
pub open spec fn hex4(s: Seq<u32>, pos: nat) -> Option<nat> {
    if pos + 4 <= s.len() {
        match (
            hex_value(s[pos as int]),
            hex_value(s[pos as int + 1]),
            hex_value(s[pos as int + 2]),
            hex_value(s[pos as int + 3]),
        ) {
            (Some(a), Some(b), Some(c), Some(d)) => Some(a * 4096 + b * 256 + c * 16 + d),
            _ => None,
        }
    } else {
        None
    }
}

/// ECMA-404 `characters`: ""characters" = "" | character characters", read
/// greedily up to the closing `"`, with `acc` the string value so far.
/// `pos` is the position of the next `character`. Returns the string
/// value and the position after the closing quote.
///
/// ECMA-404 `character`: "any code point except `"` or `\` or control
/// characters" (U+0000 to U+001F), or `\` `escape`.
pub open spec fn parse_characters(s: Seq<u32>, pos: nat, acc: Seq<u16>) -> Option<(Seq<u16>, nat)>
    decreases s.len() - pos,
{
    if pos >= s.len() {
        None  // no closing quotation mark

    } else {
        let c = s[pos as int];
        if c == 0x22 {
            // The closing quotation mark ends `characters`.
            Some((acc, pos + 1))
        } else if c == 0x5C {
            // `\` `escape`
            if pos + 1 >= s.len() {
                None
            } else {
                let e = s[pos as int + 1];
                if e == 0x75 {
                    // "u" hex hex hex hex
                    match hex4(s, pos + 2) {
                        Some(n) => parse_characters(s, pos + 6, acc.push(n as u16)),
                        None => None,
                    }
                } else {
                    match escape_unit(e) {
                        Some(u) => parse_characters(s, pos + 2, acc.push(u)),
                        None => None,
                    }
                }
            }
        } else if c < 0x20 {
            None  // a control character

        } else if c > 0x10FFFF {
            None  // not a code point

        } else {
            parse_characters(s, pos + 1, acc + utf16_encode_code_point(c))
        }
    }
}

/// ECMA-404 `string`: """ characters """. `pos` is the position of the
/// opening quotation mark. Returns the string value and the position after
/// the closing quotation mark.
pub open spec fn parse_string(s: Seq<u32>, pos: nat) -> Option<(Seq<u16>, nat)> {
    if is_at(s, pos, 0x22) {
        parse_characters(s, pos + 1, Seq::empty())
    } else {
        None
    }
}

// ---------------------------------------------------------------------
// ECMA-404 grammar: values, arrays, objects.
//
// The four functions below are mutually recursive. Their measure is
// (levels still allowed, rank, text length minus accumulator length): a
// call into a nested array or object lowers `levels`; a call at the same
// level goes down the ranks (value, array/object, elements/members); the
// loop over elements or members lengthens the accumulator.
// ---------------------------------------------------------------------

/// ECMA-404 `value`: "object | array | number | string | "true" | "false" |
/// "null"". `pos` is the position of the first code point of the value
/// (no `ws`). `levels` is how many levels of arrays and objects may still
/// be opened.
pub open spec fn parse_value(s: Seq<u32>, pos: nat, levels: nat) -> Option<(JsonValue, nat)>
    decreases levels, 3nat, 0int,
{
    if pos >= s.len() {
        None
    } else {
        let c = s[pos as int];
        if c == 0x7B {
            parse_object(s, pos, levels)
        } else if c == 0x5B {
            parse_array(s, pos, levels)
        } else if c == 0x22 {
            match parse_string(s, pos) {
                Some((u, p)) => Some((JsonValue::String(u), p)),
                None => None,
            }
        } else if c == 0x2D || is_digit(c) {
            match parse_number(s, pos) {
                Some(p) => Some((JsonValue::Number(s.subrange(pos as int, p as int)), p)),
                None => None,
            }
        } else if matches_at(s, pos, lit_true()) {
            Some((JsonValue::Bool(true), pos + 4))
        } else if matches_at(s, pos, lit_false()) {
            Some((JsonValue::Bool(false), pos + 5))
        } else if matches_at(s, pos, lit_null()) {
            Some((JsonValue::Null, pos + 4))
        } else {
            None
        }
    }
}

/// ECMA-404 `array`: ""[" ws "]" | "[" elements "]"". `pos` is the position
/// of the "[". The value is the array, and the position is after the "]".
///
/// ECMA-404 `elements`: "element | element "," elements", and `element`:
/// "ws value ws".
pub open spec fn parse_array(s: Seq<u32>, pos: nat, levels: nat) -> Option<(JsonValue, nat)>
    decreases levels, 2nat, 0int,
{
    if levels == 0 {
        None  // nested deeper than `max_depth()`

    } else {
        let p = skip_ws(s, pos + 1);
        if is_at(s, p, 0x5D) {
            Some((JsonValue::Array(Seq::empty()), p + 1))
        } else {
            parse_elements(s, p, (levels - 1) as nat, Seq::empty())
        }
    }
}

/// The `elements` of an array: `pos` is the position of the next `element`'s
/// value (its leading `ws` skipped), `levels` is what the elements' own
/// nesting may use, and `acc` holds the elements read so far.
pub open spec fn parse_elements(
    s: Seq<u32>,
    pos: nat,
    levels: nat,
    acc: Seq<JsonValue>,
) -> Option<(JsonValue, nat)>
    decreases levels, 4nat, s.len() - acc.len(),
{
    if acc.len() >= s.len() {
        None  // never: see the termination measure in the header

    } else {
        match parse_value(s, pos, levels) {
            None => None,
            Some((v, p)) => {
                // The trailing `ws` of the `element`.
                let q = skip_ws(s, p);
                if is_at(s, q, 0x2C) {
                    // "," elements: the next element's leading `ws`.
                    parse_elements(s, skip_ws(s, q + 1), levels, acc.push(v))
                } else if is_at(s, q, 0x5D) {
                    Some((JsonValue::Array(acc.push(v)), q + 1))
                } else {
                    None
                }
            },
        }
    }
}

/// ECMA-404 `object`: ""{" ws "}" | "{" members "}"". `pos` is the position
/// of the "{". The value is the object, and the position is after the "}".
pub open spec fn parse_object(s: Seq<u32>, pos: nat, levels: nat) -> Option<(JsonValue, nat)>
    decreases levels, 2nat, 0int,
{
    if levels == 0 {
        None  // nested deeper than `max_depth()`

    } else {
        let p = skip_ws(s, pos + 1);
        if is_at(s, p, 0x7D) {
            Some((JsonValue::Object(Seq::empty()), p + 1))
        } else {
            parse_members(s, p, (levels - 1) as nat, Seq::empty())
        }
    }
}

/// The `members` of an object: "member | member "," members", with
/// `member` = "ws string ws ":" element". `pos` is the position of the next
/// member's string (its leading `ws` skipped), `levels` as for
/// `parse_elements`, and `acc` holds the members read so far.
pub open spec fn parse_members(
    s: Seq<u32>,
    pos: nat,
    levels: nat,
    acc: Seq<JsonMember>,
) -> Option<(JsonValue, nat)>
    decreases levels, 4nat, s.len() - acc.len(),
{
    if acc.len() >= s.len() {
        None  // never: see the termination measure in the header

    } else {
        match parse_string(s, pos) {
            None => None,
            Some((key, p)) => {
                // ws ":"
                let q = skip_ws(s, p);
                if !is_at(s, q, 0x3A) {
                    None
                } else {
                    // element = ws value ws
                    match parse_value(s, skip_ws(s, q + 1), levels) {
                        None => None,
                        Some((v, p2)) => {
                            let r = skip_ws(s, p2);
                            let m = JsonMember { key: key, value: v };
                            if is_at(s, r, 0x2C) {
                                parse_members(s, skip_ws(s, r + 1), levels, acc.push(m))
                            } else if is_at(s, r, 0x7D) {
                                Some((JsonValue::Object(acc.push(m)), r + 1))
                            } else {
                                None
                            }
                        },
                    }
                }
            },
        }
    }
}

// ---------------------------------------------------------------------
// ECMA-404 JSON text, and ECMA-262's JSON.parse.
// ---------------------------------------------------------------------

/// ECMA-262 §25.5.1† JSON.parse (text, reviver), up to the point where the
/// reviver would run (reviving is out of scope), that is, ParseJSON†:
///
/// 1. "If StringToCodePoints(text) is not a valid JSON text as specified in
///    ECMA-404, throw a SyntaxError exception."
/// 2. to 5. Evaluate the text as an expression and take its value: here,
///    the value of the grammar's reading, as the header describes.
///
/// ECMA-404 "JSON text": "ws value ws". `None` is the SyntaxError.
pub open spec fn json_parse(text: Seq<u32>) -> Option<JsonValue> {
    // ws value ws
    match parse_value(text, skip_ws(text, 0), max_depth()) {
        None => None,
        Some((v, p)) => if skip_ws(text, p) == text.len() {
            Some(v)
        } else {
            None  // 1. a valid JSON text is nothing but `ws value ws`

        },
    }
}

// ---------------------------------------------------------------------
// ECMA-262 §25.5.2.3† QuoteJSONString (value).
// ---------------------------------------------------------------------

/// A leading (high) surrogate code unit.
pub open spec fn is_lead_surrogate(u: u16) -> bool {
    0xD800 <= u && u <= 0xDBFF
}

/// A trailing (low) surrogate code unit.
pub open spec fn is_trail_surrogate(u: u16) -> bool {
    0xDC00 <= u && u <= 0xDFFF
}

/// A leading surrogate at `i` followed by a trailing one: the two code
/// units form one code point in StringToCodePoints†.
pub open spec fn is_pair_at(v: Seq<u16>, i: nat) -> bool {
    i + 1 < v.len() && is_lead_surrogate(v[i as int]) && is_trail_surrogate(v[i as int + 1])
}

/// CodePointAt (string, position) (§11.1.4†), for `i < v.len()`: its
/// [[CodePoint]] and [[CodeUnitCount]]. The standard's steps 3 to 9 (a
/// code unit that is not a leading surrogate, or is the last, or is not
/// followed by a trailing surrogate, is its own code point, "unpaired")
/// are folded into `is_pair_at`; step 10 decodes the pair.
pub open spec fn code_point_at(v: Seq<u16>, i: nat) -> (u32, nat) {
    if is_pair_at(v, i) {
        (
            (((v[i as int] as int - 0xD800) * 0x400 + (v[i as int + 1] as int - 0xDC00)) + 0x10000) as u32,
            2,
        )
    } else {
        (v[i as int] as u32, 1)
    }
}

/// A lowercase hexadecimal digit as a code unit.
pub open spec fn hex_digit_lower(n: nat) -> u16 {
    if n < 10 {
        (0x30 + n) as u16
    } else {
        (0x61 + (n - 10)) as u16
    }
}

/// UnicodeEscape (C) (§25.5.2.4†): "Let n be the numeric value of C. ...
/// Return the string-concatenation of 0x005C (REVERSE SOLIDUS), "u", and
/// the four lowercase hexadecimal digits of n" (n < 0x10000 here).
pub open spec fn unicode_escape(unit: u16) -> Seq<u16> {
    seq![
        0x5Cu16,
        0x75u16,
        hex_digit_lower((unit as nat / 4096) % 16),
        hex_digit_lower((unit as nat / 256) % 16),
        hex_digit_lower((unit as nat / 16) % 16),
        hex_digit_lower(unit as nat % 16),
    ]
}

/// Step 2 for one code point C: the text appended for it.
pub open spec fn quote_code_point(c: u32) -> Seq<u16> {
    if c == 0x08 {
        seq![0x5Cu16, 0x62]  // a. Table (JSON Single Character Escapes): \b

    } else if c == 0x09 {
        seq![0x5Cu16, 0x74]  // \t

    } else if c == 0x0A {
        seq![0x5Cu16, 0x6E]  // \n

    } else if c == 0x0C {
        seq![0x5Cu16, 0x66]  // \f

    } else if c == 0x0D {
        seq![0x5Cu16, 0x72]  // \r

    } else if c == 0x22 {
        seq![0x5Cu16, 0x22]  // \"

    } else if c == 0x5C {
        seq![0x5Cu16, 0x5C]  // \\

    } else if c < 0x20 || (0xD800 <= c && c <= 0xDFFF) {
        // b. "Else if C has a numeric value less than 0x0020 (SPACE), or C
        // has the same numeric value as a leading surrogate or trailing
        // surrogate, then let unit be the code unit whose numeric value is
        // that of C, and append UnicodeEscape(unit)."
        unicode_escape(c as u16)
    } else {
        // c. "Else, append UTF16EncodeCodePoint(C)."
        utf16_encode_code_point(c)
    }
}

/// Step 2's loop: "For each code point C of StringToCodePoints(value)",
/// from the one at code-unit index `i` on. The recursion's advance is
/// written `i + 2` or `i + 1` (CodePointAt's [[CodeUnitCount]]) so that
/// Verus sees it is positive.
pub open spec fn quote_loop(v: Seq<u16>, i: nat) -> Seq<u16>
    decreases v.len() - i,
{
    if i >= v.len() {
        Seq::empty()
    } else {
        let c = code_point_at(v, i).0;
        if is_pair_at(v, i) {
            quote_code_point(c) + quote_loop(v, i + 2)
        } else {
            quote_code_point(c) + quote_loop(v, i + 1)
        }
    }
}

/// QuoteJSONString (value) (§25.5.2.3†):
///
/// 1. "Let product be the String value consisting solely of the code unit
///    0x0022 (QUOTATION MARK)."
/// 2. "For each code point C of StringToCodePoints(value), do" (above).
/// 3. "Set product to the string-concatenation of product and the code unit
///    0x0022 (QUOTATION MARK)."
/// 4. "Return product."
pub open spec fn quote_json_string(value: Seq<u16>) -> Seq<u16> {
    // 1. + 2. + 3. + 4.
    seq![0x22u16] + quote_loop(value, 0) + seq![0x22u16]
}

} // verus!
