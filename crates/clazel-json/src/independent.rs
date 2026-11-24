//! An independent transcription of JSON, from RFC 8259 rather than
//! ECMA-404 and ECMA-262 (docs/VERIFICATION.md, "Trust without reviewers",
//! item 2). It was written from the RFC's ABNF before `spec.rs` was read
//! (this file uses nothing from it), and it is the RFC's text in the RFC's
//! shape: `begin-array`, `end-array`, `name-separator` and
//! `value-separator` each carry their own `ws`, an `int` is `zero /
//! digit1-9 *DIGIT`, a string's value is a sequence of *code points*
//! where a pair of `\u` escapes naming a surrogate pair is one code point
//! (§7), and so on. The same agent session wrote both files, so the two
//! may share a misreading (the limit VERIFICATION.md states); the
//! conformance tests, when they exist, carry more weight.
//!
//! Source: RFC 8259, "The JavaScript Object Notation (JSON) Data
//! Interchange Format", December 2017, STD 90,
//! <https://www.rfc-editor.org/rfc/rfc8259>: §2 "JSON Grammar"
//! (`JSON-text`, the structural characters, `ws`), §3 "Values", §4
//! "Objects", §5 "Arrays", §6 "Numbers", §7 "Strings", and §9 "Parsers"
//! (an implementation "may set limits on the maximum depth of nesting").
//! ABNF is RFC 5234; its quoted strings and `HEXDIG` are case-insensitive
//! (RFC 5234 §2.3, §B.1). The equivalence with the primary spec is in
//! [`super::equivalence`].
//!
//! Modelling choices:
//! - **Input** is `Seq<u32>` code points. `%x5D-10FFFF` in `unescaped`
//!   includes the surrogate range, so a lone surrogate may occur in a
//!   string; a value above U+10FFFF matches no terminal.
//! - **ABNF as a recogniser.** Each rule is a function from a text and a
//!   position to the position after the longest match, or `None`. An
//!   alternation tries its alternatives in the RFC's order; a repetition
//!   is greedy. For this grammar that equals the ABNF language, because
//!   what follows each repeated element (`DIGIT`, `char`, a `value`) can
//!   never begin another repetition of it: after a `value` comes `ws`
//!   then `,` `]` `}` or the end of the text, after `1*DIGIT` never a digit.
//!   A literal `ws` may therefore be taken as the longest run.
//! - **Values.** `false`, `null`, `true`, objects (members in source order,
//!   duplicate names kept: §4 only says names SHOULD be unique and that
//!   the behaviour is unpredictable otherwise), arrays, numbers (the
//!   matched source text; §6 gives their meaning as a decimal, which
//!   `clazel-js-number` computes), and strings as code points. §8.2: "the
//!   behavior of software that receives JSON texts containing such values
//!   is unpredictable"; here a `\u` escape of a lone surrogate is that
//!   code point, as it is in a string literal's value.
//! - **Nesting.** §9 lets a parser limit depth; this crate does (512, the
//!   same as the primary spec), counting the outermost array or object as
//!   level one. `d` below is the number of levels still allowed.
//! - **Termination.** `object_rest` and `array_rest` refuse a list at
//!   least as long as the text (the same guard `spec.rs` uses, for the
//!   same reason: Verus needs a measure that does not depend on a result).
//!   It never fires: each member or element and its separator consume at
//!   least two code points, which `equivalence.rs` uses to show that the
//!   guard is never the reason a text is rejected.
//! - **The top level** is `JSON-text = ws value ws`: any value, which is
//!   RFC 8259's change from RFC 4627 (object or array only), and agrees
//!   with ECMA-262's `JSON.parse`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §9: the most levels of arrays and objects a text may nest.
pub open spec fn nesting_limit() -> nat {
    512
}

/// The value of a JSON text, in the RFC's terms.
pub enum Json8259 {
    /// §3 `false`.
    False,
    /// §3 `null`.
    Null,
    /// §3 `true`.
    True,
    /// §4 object: its members in source order.
    Object(Seq<Member8259>),
    /// §5 array: its elements.
    Array(Seq<Json8259>),
    /// §6 number: its source text.
    Number(Seq<u32>),
    /// §7 string: its code points.
    String(Seq<u32>),
}

/// §4 `member = string name-separator value`.
pub struct Member8259 {
    /// The member's name.
    pub name: Seq<u32>,
    /// The member's value.
    pub value: Json8259,
}

/// The terminal `%xNN` at `pos`.
pub open spec fn char_at(s: Seq<u32>, pos: nat, c: u32) -> bool {
    pos < s.len() && s[pos as int] == c
}

/// The code points of a literal (all ASCII) at `pos`.
pub open spec fn literal_at(s: Seq<u32>, pos: nat, lit: Seq<u32>) -> bool {
    pos + lit.len() <= s.len() && s.subrange(pos as int, (pos + lit.len()) as int) == lit
}

// ---- §2 ----

/// §2: `ws = *( %x20 / %x09 / %x0A / %x0D )`, the end of the longest run
/// from `pos`.
pub open spec fn ws(s: Seq<u32>, pos: nat) -> nat
    decreases s.len() - pos,
{
    if char_at(s, pos, 0x20) || char_at(s, pos, 0x09) || char_at(s, pos, 0x0A) || char_at(s, pos, 0x0D) {
        ws(s, pos + 1)
    } else {
        pos
    }
}

/// A structural character with its `ws` on both sides:
/// `ws %xNN ws`, the shape of all six of §2's tokens.
pub open spec fn structural(s: Seq<u32>, pos: nat, c: u32) -> Option<nat> {
    let p = ws(s, pos);
    if char_at(s, p, c) {
        Some(ws(s, p + 1))
    } else {
        None
    }
}

/// §2 `begin-array = ws %x5B ws`.
pub open spec fn begin_array(s: Seq<u32>, pos: nat) -> Option<nat> {
    structural(s, pos, 0x5B)
}

/// §2 `begin-object = ws %x7B ws`.
pub open spec fn begin_object(s: Seq<u32>, pos: nat) -> Option<nat> {
    structural(s, pos, 0x7B)
}

/// §2 `end-array = ws %x5D ws`.
pub open spec fn end_array(s: Seq<u32>, pos: nat) -> Option<nat> {
    structural(s, pos, 0x5D)
}

/// §2 `end-object = ws %x7D ws`.
pub open spec fn end_object(s: Seq<u32>, pos: nat) -> Option<nat> {
    structural(s, pos, 0x7D)
}

/// §2 `name-separator = ws %x3A ws`.
pub open spec fn name_separator(s: Seq<u32>, pos: nat) -> Option<nat> {
    structural(s, pos, 0x3A)
}

/// §2 `value-separator = ws %x2C ws`.
pub open spec fn value_separator(s: Seq<u32>, pos: nat) -> Option<nat> {
    structural(s, pos, 0x2C)
}

/// §2 `JSON-text = ws value ws`, read in full: the value, or `None` if the
/// text does not match.
pub open spec fn json_text(text: Seq<u32>) -> Option<Json8259> {
    match value(text, ws(text, 0), nesting_limit()) {
        Some((v, p)) => if ws(text, p) == text.len() {
            Some(v)
        } else {
            None
        },
        None => None,
    }
}

// ---- §3 ----

/// §3 `false = %x66.61.6c.73.65`.
pub open spec fn false_lit() -> Seq<u32> {
    seq![0x66u32, 0x61, 0x6c, 0x73, 0x65]
}

/// §3 `null = %x6e.75.6c.6c`.
pub open spec fn null_lit() -> Seq<u32> {
    seq![0x6eu32, 0x75, 0x6c, 0x6c]
}

/// §3 `true = %x74.72.75.65`.
pub open spec fn true_lit() -> Seq<u32> {
    seq![0x74u32, 0x72, 0x75, 0x65]
}

/// §3 `value = false / null / true / object / array / number / string`,
/// the alternatives in that order. `d` is how many levels of array and
/// object a match may still open. The result is the value and the position
/// after it (the `ws` after a value belongs to the token that follows).
pub open spec fn value(s: Seq<u32>, pos: nat, d: nat) -> Option<(Json8259, nat)>
    decreases d, 2int, s.len() - pos,
{
    if literal_at(s, pos, false_lit()) {
        Some((Json8259::False, pos + 5))
    } else if literal_at(s, pos, null_lit()) {
        Some((Json8259::Null, pos + 4))
    } else if literal_at(s, pos, true_lit()) {
        Some((Json8259::True, pos + 4))
    } else {
        match object(s, pos, d) {
            Some((m, p)) => Some((Json8259::Object(m), p)),
            None => match array(s, pos, d) {
                Some((a, p)) => Some((Json8259::Array(a), p)),
                None => match number(s, pos) {
                    Some(p) => Some((Json8259::Number(s.subrange(pos as int, p as int)), p)),
                    None => match string(s, pos) {
                        Some((u, p)) => Some((Json8259::String(u), p)),
                        None => None,
                    },
                },
            },
        }
    }
}

// ---- §4 ----

/// §4 `object = begin-object [ member *( value-separator member ) ]
/// end-object`. The object is one level, so its members' values may open
/// `d - 1` more (§9); at `d == 0` it is not allowed.
pub open spec fn object(s: Seq<u32>, pos: nat, d: nat) -> Option<(Seq<Member8259>, nat)>
    decreases d, 1int, s.len() - pos,
{
    if d == 0 {
        None
    } else {
        match begin_object(s, pos) {
            None => None,
            Some(p1) => match member(s, p1, (d - 1) as nat) {
                Some((m, p2)) => object_rest(s, p2, (d - 1) as nat, seq![m]),
                None => match end_object(s, p1) {
                    Some(p) => Some((Seq::empty(), p)),
                    None => None,
                },
            },
        }
    }
}

/// §4 `*( value-separator member ) end-object`, after the members `done`.
/// `e` is the depth left for each member's value.
pub open spec fn object_rest(s: Seq<u32>, pos: nat, e: nat, done: Seq<Member8259>) -> Option<(Seq<Member8259>, nat)>
    decreases e, 4int, s.len() - done.len(),
{
    if done.len() >= s.len() {
        None  // never: see "Termination" in the header
    } else {
        match value_separator(s, pos) {
            Some(p1) => match member(s, p1, e) {
                Some((m, p2)) => object_rest(s, p2, e, done.push(m)),
                None => None,
            },
            None => match end_object(s, pos) {
                Some(p) => Some((done, p)),
                None => None,
            },
        }
    }
}

/// §4 `member = string name-separator value`; `e` is the depth left for
/// the value.
pub open spec fn member(s: Seq<u32>, pos: nat, e: nat) -> Option<(Member8259, nat)>
    decreases e, 3int, s.len() - pos,
{
    match string(s, pos) {
        None => None,
        Some((name, p1)) => match name_separator(s, p1) {
            None => None,
            Some(p2) => match value(s, p2, e) {
                None => None,
                Some((v, p3)) => Some((Member8259 { name: name, value: v }, p3)),
            },
        },
    }
}

// ---- §5 ----

/// §5 `array = begin-array [ value *( value-separator value ) ]
/// end-array`; one level, as for `object`.
pub open spec fn array(s: Seq<u32>, pos: nat, d: nat) -> Option<(Seq<Json8259>, nat)>
    decreases d, 1int, s.len() - pos,
{
    if d == 0 {
        None
    } else {
        match begin_array(s, pos) {
            None => None,
            Some(p1) => match value(s, p1, (d - 1) as nat) {
                Some((v, p2)) => array_rest(s, p2, (d - 1) as nat, seq![v]),
                None => match end_array(s, p1) {
                    Some(p) => Some((Seq::empty(), p)),
                    None => None,
                },
            },
        }
    }
}

/// §5 `*( value-separator value ) end-array`, after the elements `done`.
pub open spec fn array_rest(s: Seq<u32>, pos: nat, e: nat, done: Seq<Json8259>) -> Option<(Seq<Json8259>, nat)>
    decreases e, 4int, s.len() - done.len(),
{
    if done.len() >= s.len() {
        None  // never: see "Termination" in the header
    } else {
        match value_separator(s, pos) {
            Some(p1) => match value(s, p1, e) {
                Some((v, p2)) => array_rest(s, p2, e, done.push(v)),
                None => None,
            },
            None => match end_array(s, pos) {
                Some(p) => Some((done, p)),
                None => None,
            },
        }
    }
}

// ---- §6 ----

/// §6 `DIGIT` (RFC 5234 B.1): `%x30-39`.
pub open spec fn digit(c: u32) -> bool {
    0x30 <= c <= 0x39
}

/// §6 `digit1-9 = %x31-39`.
pub open spec fn digit1_9(c: u32) -> bool {
    0x31 <= c <= 0x39
}

/// `*DIGIT`: the end of the longest run of digits.
pub open spec fn digits(s: Seq<u32>, pos: nat) -> nat
    decreases s.len() - pos,
{
    if pos < s.len() && digit(s[pos as int]) {
        digits(s, pos + 1)
    } else {
        pos
    }
}

/// `1*DIGIT`.
pub open spec fn digits1(s: Seq<u32>, pos: nat) -> Option<nat> {
    let p = digits(s, pos);
    if p > pos {
        Some(p)
    } else {
        None
    }
}

/// §6 `int = zero / ( digit1-9 *DIGIT )`, with `zero = %x30`.
pub open spec fn int_part(s: Seq<u32>, pos: nat) -> Option<nat> {
    if char_at(s, pos, 0x30) {
        Some(pos + 1)
    } else if pos < s.len() && digit1_9(s[pos as int]) {
        Some(digits(s, pos + 1))
    } else {
        None
    }
}

/// §6 `[ frac ]`, `frac = decimal-point 1*DIGIT`, `decimal-point = %x2E`.
/// If a `.` is there, the `frac` must follow: the other reading (leave the
/// `.` unmatched) leaves a character no token can begin with.
pub open spec fn opt_frac(s: Seq<u32>, pos: nat) -> Option<nat> {
    if char_at(s, pos, 0x2E) {
        digits1(s, pos + 1)
    } else {
        Some(pos)
    }
}

/// §6 `[ exp ]`, `exp = e [ minus / plus ] 1*DIGIT`, `e = %x65 / %x45`,
/// `minus = %x2D`, `plus = %x2B`.
pub open spec fn opt_exp(s: Seq<u32>, pos: nat) -> Option<nat> {
    if char_at(s, pos, 0x65) || char_at(s, pos, 0x45) {
        if char_at(s, pos + 1, 0x2D) || char_at(s, pos + 1, 0x2B) {
            digits1(s, pos + 2)
        } else {
            digits1(s, pos + 1)
        }
    } else {
        Some(pos)
    }
}

/// §6 `number = [ minus ] int [ frac ] [ exp ]`: the end of the match.
pub open spec fn number(s: Seq<u32>, pos: nat) -> Option<nat> {
    let p0 = if char_at(s, pos, 0x2D) {
        pos + 1
    } else {
        pos
    };
    match int_part(s, p0) {
        None => None,
        Some(p1) => match opt_frac(s, p1) {
            None => None,
            Some(p2) => opt_exp(s, p2),
        },
    }
}

// ---- §7 ----

/// §7 `HEXDIG` (RFC 5234 B.1: `DIGIT / "A" / "B" / "C" / "D" / "E" /
/// "F"`, whose quoted letters match either case): its value.
pub open spec fn hexdig(c: u32) -> Option<nat> {
    if 0x30 <= c <= 0x39 {
        Some((c - 0x30) as nat)
    } else if 0x41 <= c <= 0x46 {
        Some((c - 0x41 + 10) as nat)
    } else if 0x61 <= c <= 0x66 {
        Some((c - 0x61 + 10) as nat)
    } else {
        None
    }
}

/// `4HEXDIG`: the number they spell, most significant first.
pub open spec fn four_hexdig(s: Seq<u32>, pos: nat) -> Option<nat> {
    if pos + 4 <= s.len() {
        match (hexdig(s[pos as int]), hexdig(s[pos as int + 1]), hexdig(s[pos as int + 2]), hexdig(s[pos as int + 3])) {
            (Some(a), Some(b), Some(c), Some(d)) => Some(a * 4096 + b * 256 + c * 16 + d),
            _ => None,
        }
    } else {
        None
    }
}

/// §7 `unescaped = %x20-21 / %x23-5B / %x5D-10FFFF`.
pub open spec fn unescaped(c: u32) -> bool {
    (0x20 <= c <= 0x21) || (0x23 <= c <= 0x5B) || (0x5D <= c <= 0x10FFFF)
}

/// §7 `escape = %x5C` followed by one of `%x22` (quotation mark U+0022),
/// `%x5C` (reverse solidus U+005C), `%x2F` (solidus U+002F), `%x62`
/// (backspace U+0008), `%x66` (form feed U+000C), `%x6E` (line feed
/// U+000A), `%x72` (carriage return U+000D), `%x74` (tab U+0009): the code
/// point the character after the backslash names. (`%x75 4HEXDIG` is
/// [`u_escape`].)
pub open spec fn simple_escape(c: u32) -> Option<u32> {
    if c == 0x22 {
        Some(0x22)
    } else if c == 0x5C {
        Some(0x5C)
    } else if c == 0x2F {
        Some(0x2F)
    } else if c == 0x62 {
        Some(0x08)
    } else if c == 0x66 {
        Some(0x0C)
    } else if c == 0x6E {
        Some(0x0A)
    } else if c == 0x72 {
        Some(0x0D)
    } else if c == 0x74 {
        Some(0x09)
    } else {
        None
    }
}

/// §7 `escape` with `%x75 4HEXDIG` (`uXXXX`, U+XXXX): the number it names,
/// six code points long.
pub open spec fn u_escape(s: Seq<u32>, pos: nat) -> Option<nat> {
    if char_at(s, pos, 0x5C) && char_at(s, pos + 1, 0x75) {
        four_hexdig(s, pos + 2)
    } else {
        None
    }
}

/// UTF-16 lead (high) surrogate, U+D800 to U+DBFF.
pub open spec fn is_high(n: nat) -> bool {
    0xD800 <= n <= 0xDBFF
}

/// UTF-16 trail (low) surrogate, U+DC00 to U+DFFF.
pub open spec fn is_low(n: nat) -> bool {
    0xDC00 <= n <= 0xDFFF
}

/// §7: "the character is represented as a 12-character sequence, encoding
/// the UTF-16 surrogate pair": the code point a pair names (RFC 2781
/// §2.1, decoding).
pub open spec fn pair_code_point(hi: nat, lo: nat) -> nat {
    (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)) as nat
}

/// §7 `*char`, after the code points `acc`: the string's value and the
/// position after the last `char`. `char = unescaped / escape (...)`; two
/// `\u` escapes naming a surrogate pair are the one code point (§7), and a
/// lone `\u` surrogate is that code point.
pub open spec fn chars(s: Seq<u32>, pos: nat, acc: Seq<u32>) -> Option<(Seq<u32>, nat)>
    decreases s.len() - pos,
{
    if pos < s.len() && unescaped(s[pos as int]) {
        chars(s, pos + 1, acc.push(s[pos as int]))
    } else if char_at(s, pos, 0x5C) {
        match u_escape(s, pos) {
            Some(n) => if is_high(n) && u_escape(s, pos + 6) is Some && is_low(u_escape(s, pos + 6)->Some_0) {
                chars(s, pos + 12, acc.push(pair_code_point(n, u_escape(s, pos + 6)->Some_0) as u32))
            } else {
                chars(s, pos + 6, acc.push(n as u32))
            },
            None => if pos + 1 < s.len() && simple_escape(s[pos as int + 1]) is Some {
                chars(s, pos + 2, acc.push(simple_escape(s[pos as int + 1])->Some_0))
            } else {
                None
            },
        }
    } else {
        Some((acc, pos))
    }
}

/// §7 `string = quotation-mark *char quotation-mark`, with `quotation-mark
/// = %x22`: the value and the position after the closing mark.
pub open spec fn string(s: Seq<u32>, pos: nat) -> Option<(Seq<u32>, nat)> {
    if char_at(s, pos, 0x22) {
        match chars(s, pos + 1, Seq::empty()) {
            Some((u, p)) => if char_at(s, p, 0x22) {
                Some((u, p + 1))
            } else {
                None
            },
            None => None,
        }
    } else {
        None
    }
}

} // verus!
