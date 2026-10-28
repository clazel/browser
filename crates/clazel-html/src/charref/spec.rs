//! Executable-style specification of character references, transcribed
//! from the WHATWG HTML Standard (Living Standard, whatwg/html commit
//! `939677714df7379fee3667040113b41c91c851e7`, 26 October 2026): the table
//! of §13.5 "Named character references", the matching rule that §13.2.5.78
//! "Named character reference state" applies to it, and the checks of
//! §13.2.5.84 "Numeric character reference end state". The states
//! themselves (which characters they consume, where they flush, which
//! state comes next) are in `crate::tokenizer::spec`, which calls these.
//! Nothing here runs; it defines what "correct" means.
//!
//! Modelling choices (each one a deliberate, reviewable deviation in form,
//! never in meaning):
//! - The named character references table is the generated
//!   [`super::data`] (from the standard's `entities.json`, vendored; see
//!   `xtask/src/entities.rs`): row `i` has a name, as the table's first
//!   column lists it without the `&` (with a final `;` where the table has
//!   one), and one or two code points (its second column).
//!   [`entity_name`] and [`entity_code_points`] are the row's columns.
//! - "Consume the maximum number of characters possible, where the
//!   consumed characters are one of the identifiers in the first column" is
//!   [`longest_match`]: the row whose name is the longest of the names that
//!   are a prefix of the input from the next input character on. Names are
//!   unique (the generator checks), so at most one row has that length;
//!   [`longest_match_upto`] scans rows in order and keeps the first of a
//!   length, which is then the only one.
//! - The input is `Seq<u32>` with a position; the "next input character"
//!   is `input[pos]`, EOF when `pos` is `input.len()`.
//! - The character reference code is a `nat`: the standard's "number" is
//!   unbounded (each digit multiplies it), and only its comparisons with
//!   0x10FFFF and below matter.

#[allow(unused_imports)]
use super::data::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The number of rows in the named character references table.
pub open spec fn entity_count() -> nat {
    ENTITY_NAME_START_LEN as nat
}

/// Row `i`'s name: the first column of the table, without the `&`.
pub open spec fn entity_name(i: int) -> Seq<u32> {
    Seq::new(
        entity_name_len_at(i) as nat,
        |k: int| entity_chars_at(entity_name_start_at(i) + k) as u32,
    )
}

/// Row `i`'s code points: the second column of the table, one or two code
/// points (a second code point of 0 means there is none; no row has
/// U+0000).
pub open spec fn entity_code_points(i: int) -> Seq<u32> {
    if entity_cp2_at(i) == 0 {
        seq![entity_cp1_at(i)]
    } else {
        seq![entity_cp1_at(i), entity_cp2_at(i)]
    }
}

/// `name` is what the input holds from `pos` on (so consuming it is
/// possible).
pub open spec fn is_prefix_at(name: Seq<u32>, input: Seq<u32>, pos: int) -> bool {
    0 <= pos && pos + name.len() <= input.len() && input.subrange(pos, pos + name.len()) == name
}

/// Of rows `0 .. k`, the one with the longest name that is a prefix of
/// the input from `pos` on (the first such row of that length), or `None`
/// if no name is.
pub open spec fn longest_match_upto(input: Seq<u32>, pos: int, k: nat) -> Option<nat>
    decreases k,
{
    if k == 0 {
        None
    } else {
        let prev = longest_match_upto(input, pos, (k - 1) as nat);
        let i = (k - 1) as int;
        if is_prefix_at(entity_name(i), input, pos) && match prev {
            None => true,
            Some(p) => entity_name(p as int).len() < entity_name(i).len(),
        } {
            Some((k - 1) as nat)
        } else {
            prev
        }
    }
}

/// §13.2.5.78 "Named character reference state": "Consume the maximum
/// number of characters possible, where the consumed characters are one of
/// the identifiers in the first column of the named character references
/// table." `Some(i)`: row `i` is the identifier consumed ("there is a
/// match"); `None`: "Otherwise".
pub open spec fn longest_match(input: Seq<u32>, pos: int) -> Option<nat> {
    longest_match_upto(input, pos, entity_count())
}

/// U+003B SEMICOLON.
pub open spec fn semicolon() -> u32 {
    0x3B
}

/// ASCII digit (Infra §4.6): U+0030 (0) to U+0039 (9).
pub open spec fn is_ascii_digit(c: u32) -> bool {
    0x30 <= c <= 0x39
}

/// ASCII upper alpha: U+0041 (A) to U+005A (Z).
pub open spec fn is_ascii_upper_alpha(c: u32) -> bool {
    0x41 <= c <= 0x5A
}

/// ASCII lower alpha: U+0061 (a) to U+007A (z).
pub open spec fn is_ascii_lower_alpha(c: u32) -> bool {
    0x61 <= c <= 0x7A
}

/// ASCII alpha: ASCII upper alpha or ASCII lower alpha.
pub open spec fn is_ascii_alpha(c: u32) -> bool {
    is_ascii_upper_alpha(c) || is_ascii_lower_alpha(c)
}

/// ASCII alphanumeric: ASCII digit or ASCII alpha.
pub open spec fn is_ascii_alphanumeric(c: u32) -> bool {
    is_ascii_digit(c) || is_ascii_alpha(c)
}

/// §13.2.5.78, "If there is a match": "If the character reference was
/// consumed as part of an attribute, and the last character matched is
/// not a U+003B SEMICOLON character (;), and the next input character is
/// either a U+003D EQUALS SIGN character (=) or an ASCII alphanumeric,
/// then, for historical reasons, flush code points consumed as a character
/// reference and switch to the return state." `next` is the next input
/// character after the matched name, `None` for EOF.
pub open spec fn historical_reasons(as_part_of_attribute: bool, name: Seq<u32>, next: Option<u32>) -> bool {
    as_part_of_attribute && name.len() > 0 && name.last() != semicolon() && match next {
        None => false,
        Some(c) => c == 0x3D || is_ascii_alphanumeric(c),
    }
}

/// Surrogate (Infra §4.6): U+D800 to U+DFFF.
pub open spec fn is_surrogate(n: nat) -> bool {
    0xD800 <= n <= 0xDFFF
}

/// Noncharacter (Infra §4.6): U+FDD0 to U+FDEF, or U+xFFFE or U+xFFFF for
/// x from 0 to 0x10.
pub open spec fn is_noncharacter(n: nat) -> bool {
    (0xFDD0 <= n <= 0xFDEF) || ((n % 0x10000 == 0xFFFE || n % 0x10000 == 0xFFFF) && n <= 0x10FFFF)
}

/// C0 control (Infra §4.6): U+0000 NULL to U+001F.
pub open spec fn is_c0_control(n: nat) -> bool {
    n <= 0x1F
}

/// Control (Infra §4.6): a C0 control or U+007F DELETE to U+009F.
pub open spec fn is_control(n: nat) -> bool {
    is_c0_control(n) || (0x7F <= n <= 0x9F)
}

/// ASCII whitespace (Infra §4.6): U+0009 TAB, U+000A LF, U+000C FF, U+000D
/// CR, or U+0020 SPACE.
pub open spec fn is_ascii_whitespace(n: nat) -> bool {
    n == 0x09 || n == 0x0A || n == 0x0C || n == 0x0D || n == 0x20
}

/// The table of §13.2.5.84's last check: `Some(code point)` for a number in
/// its first column, `None` otherwise.
pub open spec fn c1_replacement(n: nat) -> Option<u32> {
    if n == 0x80 {
        Some(0x20AC)  // EURO SIGN
    } else if n == 0x82 {
        Some(0x201A)  // SINGLE LOW-9 QUOTATION MARK
    } else if n == 0x83 {
        Some(0x0192)  // LATIN SMALL LETTER F WITH HOOK
    } else if n == 0x84 {
        Some(0x201E)  // DOUBLE LOW-9 QUOTATION MARK
    } else if n == 0x85 {
        Some(0x2026)  // HORIZONTAL ELLIPSIS
    } else if n == 0x86 {
        Some(0x2020)  // DAGGER
    } else if n == 0x87 {
        Some(0x2021)  // DOUBLE DAGGER
    } else if n == 0x88 {
        Some(0x02C6)  // MODIFIER LETTER CIRCUMFLEX ACCENT
    } else if n == 0x89 {
        Some(0x2030)  // PER MILLE SIGN
    } else if n == 0x8A {
        Some(0x0160)  // LATIN CAPITAL LETTER S WITH CARON
    } else if n == 0x8B {
        Some(0x2039)  // SINGLE LEFT-POINTING ANGLE QUOTATION MARK
    } else if n == 0x8C {
        Some(0x0152)  // LATIN CAPITAL LIGATURE OE
    } else if n == 0x8E {
        Some(0x017D)  // LATIN CAPITAL LETTER Z WITH CARON
    } else if n == 0x91 {
        Some(0x2018)  // LEFT SINGLE QUOTATION MARK
    } else if n == 0x92 {
        Some(0x2019)  // RIGHT SINGLE QUOTATION MARK
    } else if n == 0x93 {
        Some(0x201C)  // LEFT DOUBLE QUOTATION MARK
    } else if n == 0x94 {
        Some(0x201D)  // RIGHT DOUBLE QUOTATION MARK
    } else if n == 0x95 {
        Some(0x2022)  // BULLET
    } else if n == 0x96 {
        Some(0x2013)  // EN DASH
    } else if n == 0x97 {
        Some(0x2014)  // EM DASH
    } else if n == 0x98 {
        Some(0x02DC)  // SMALL TILDE
    } else if n == 0x99 {
        Some(0x2122)  // TRADE MARK SIGN
    } else if n == 0x9A {
        Some(0x0161)  // LATIN SMALL LETTER S WITH CARON
    } else if n == 0x9B {
        Some(0x203A)  // SINGLE RIGHT-POINTING ANGLE QUOTATION MARK
    } else if n == 0x9C {
        Some(0x0153)  // LATIN SMALL LIGATURE OE
    } else if n == 0x9E {
        Some(0x017E)  // LATIN SMALL LETTER Z WITH CARON
    } else if n == 0x9F {
        Some(0x0178)  // LATIN CAPITAL LETTER Y WITH DIAERESIS
    } else {
        None
    }
}

/// §13.2.5.84 "Numeric character reference end state", "Check the
/// character reference code": the code after the five checks, in the
/// standard's order (each check sees the code the previous one left).
/// Parse errors are not modelled; the checks that only report one (the
/// noncharacter check, and the control check for a number not in the
/// table) leave the code as it is.
pub open spec fn numeric_reference_end_code(code: nat) -> u32 {
    // 1. "If the number is 0x00, then this is a null-character-reference
    //    parse error. Set the character reference code to 0xFFFD."
    let code = if code == 0 { 0xFFFDnat } else { code };
    // 2. "If the number is greater than 0x10FFFF, then this is a
    //    character-reference-outside-unicode-range parse error. Set the
    //    character reference code to 0xFFFD."
    let code = if code > 0x10FFFF { 0xFFFDnat } else { code };
    // 3. "If the number is a surrogate, then this is a
    //    surrogate-character-reference parse error. Set the character
    //    reference code to 0xFFFD."
    let code = if is_surrogate(code) { 0xFFFDnat } else { code };
    // 4. "If the number is a noncharacter, then this is a
    //    noncharacter-character-reference parse error." (Nothing changes.)
    // 5. "If the number is 0x0D, or a control that's not ASCII whitespace,
    //    then this is a control-character-reference parse error. If the
    //    number is one of the numbers in the first column of the following
    //    table, then find the row with that number in the first column, and
    //    set the character reference code to the number in the second
    //    column of that row."
    let code = if code == 0x0D || (is_control(code) && !is_ascii_whitespace(code)) {
        match c1_replacement(code) {
            Some(r) => r as nat,
            None => code,
        }
    } else {
        code
    };
    // After step 2 the code is at most 0x10FFFF, and the table's second
    // column is below 0x10000, so it fits a u32.
    code as u32
}

} // verus!
