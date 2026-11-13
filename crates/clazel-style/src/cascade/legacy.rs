//! The microsyntaxes HTML's presentational hints parse attributes with, from HTML (Living
//! Standard, commit 4c54fae1 of 11 November 2026, the commit `data/html-4c54fae1/` vendors):
//!
//! - §2.3.4.1 "rules for parsing integers" ([`integer`]) and §2.3.4.2 "rules for parsing
//!   non-negative integers" ([`non_negative_integer`]);
//! - §2.3.4.4 "rules for parsing dimension values" ([`dimension`]) and §2.3.4.5 "rules for
//!   parsing nonzero dimension values" ([`nonzero_dimension`]);
//! - §2.3.6 "rules for parsing a legacy color value" ([`legacy_color`]);
//! - §15.3.4 "rules for parsing a legacy font size" ([`legacy_font_size`]).
//!
//! # Modelling choices
//!
//! - **Integers** are read into an `i64` that stops growing at [`MAX_INT`] (2^31 - 1): "interpret
//!   the resulting sequence as a base-ten integer" has no bound, and every use of one here is a
//!   length in 1/64 px, which `values/` clamps far below that.
//! - **Dimensions** are millionths, as `values/`' numbers are: the integer part as above, and
//!   the fraction's digits after the sixth are dropped (the standard adds each digit divided
//!   by its divisor to a real number; the error is under a millionth of a pixel or percent).
//! - Input is code points; "ASCII whitespace" is Infra's (TAB, LF, FF, CR, SPACE).

use super::computed::Rgba;
use crate::values::color::NAMED;
use crate::values::items::{eq_ignore_case, lookup};
use crate::values::number::{Num, SCALE};

/// The largest integer read; larger ones clamp to it.
pub const MAX_INT: i64 = (1 << 31) - 1;

/// Infra's ASCII whitespace.
fn is_ascii_whitespace(c: u32) -> bool {
    matches!(c, 0x09 | 0x0A | 0x0C | 0x0D | 0x20)
}

/// The value of an ASCII digit.
fn digit(c: u32) -> Option<i64> {
    c.checked_sub(0x30).filter(|d| *d <= 9).map(i64::from)
}

/// The value of an ASCII hex digit.
fn hex_digit(c: u32) -> Option<u32> {
    match c {
        0x30..=0x39 => c.checked_sub(0x30),
        0x41..=0x46 => c.checked_sub(0x37),
        0x61..=0x66 => c.checked_sub(0x57),
        _ => None,
    }
}

/// "Skip ASCII whitespace within input given position."
fn skip_whitespace(input: &[u32], position: &mut usize) {
    for _ in 0..input.len() {
        match input.get(*position) {
            Some(&c) if is_ascii_whitespace(c) => *position = position.saturating_add(1),
            _ => break,
        }
    }
}

/// "Collect a sequence of code points that are ASCII digits from input given position, and
/// interpret the resulting sequence as a base-ten integer", clamped to [`MAX_INT`].
fn collect_digits(input: &[u32], position: &mut usize) -> i64 {
    let mut value: i64 = 0;
    for _ in 0..input.len() {
        let Some(d) = input.get(*position).and_then(|&c| digit(c)) else {
            break;
        };
        value = value.saturating_mul(10).saturating_add(d).min(MAX_INT);
        *position = position.saturating_add(1);
    }
    value
}

/// §2.3.4.1 "rules for parsing integers": an integer, or `None` for an error.
pub fn integer(input: &[u32]) -> Option<i64> {
    // 1. "Let input be the string being parsed." 2. "Let position be a pointer into input,
    // initially pointing at the start of the string." 3. "Let sign have the value
    // "positive"."
    let mut position = 0usize;
    let mut negative = false;
    // 4. "Skip ASCII whitespace within input given position."
    skip_whitespace(input, &mut position);
    // 5. "If position is past the end of input, return an error."
    let first = *input.get(position)?;
    // 6. "If the character indicated by position (the first character) is a U+002D
    // HYPHEN-MINUS character (-): Let sign be "negative". Advance position to the next
    // character. If position is past the end of input, return an error. Otherwise, if the
    // character indicated by position (the first character) is a U+002B PLUS SIGN character
    // (+): Advance position to the next character. ... If position is past the end of input,
    // return an error."
    if first == 0x2D || first == 0x2B {
        negative = first == 0x2D;
        position = position.saturating_add(1);
        input.get(position)?;
    }
    // 7. "If the character indicated by position is not an ASCII digit, then return an
    // error."
    digit(*input.get(position)?)?;
    // 8. "Collect a sequence of code points that are ASCII digits from input given position,
    // and interpret the resulting sequence as a base-ten integer. Let value be that
    // integer."
    let value = collect_digits(input, &mut position);
    // 9. "If sign is "positive", return value, otherwise return the result of subtracting
    // value from zero."
    Some(if negative {
        value.saturating_neg()
    } else {
        value
    })
}

/// §2.3.4.2 "rules for parsing non-negative integers": zero, a positive integer, or `None`
/// for an error.
pub fn non_negative_integer(input: &[u32]) -> Option<i64> {
    // 1. "Let input be the string being parsed." 2. "Let value be the result of parsing input
    // using the rules for parsing integers." 3. "If value is an error, return an error."
    let value = integer(input)?;
    // 4. "If value is less than zero, return an error." 5. "Return value."
    (value >= 0).then_some(value)
}

/// What the dimension rules return: a number of at least zero, in millionths, "further
/// categorized as either a percentage or a length".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Dimension {
    /// A length in CSS pixels.
    Length(Num),
    /// A percentage.
    Percentage(Num),
}

/// §2.3.4.4 "rules for parsing dimension values": a dimension, or `None` for failure.
pub fn dimension(input: &[u32]) -> Option<Dimension> {
    // 1. "Let input be the string being parsed." 2. "Let position be a position variable for
    // input, initially pointing at the start of input."
    let mut position = 0usize;
    // 3. "Skip ASCII whitespace within input given position."
    skip_whitespace(input, &mut position);
    // 4. "If position is past the end of input or the code point at position within input
    // is not an ASCII digit, then return failure."
    digit(*input.get(position)?)?;
    // 5. "Collect a sequence of code points that are ASCII digits from input given
    // position, and interpret the resulting sequence as a base-ten integer. Let value be
    // that number." (In millionths.)
    let mut value = collect_digits(input, &mut position).saturating_mul(SCALE);
    let length = |v: i64| Some(Dimension::Length(num(v)));
    // 6. "If position is past the end of input, then return value as a length."
    let Some(&c) = input.get(position) else {
        return length(value);
    };
    // 7. "If the code point at position within input is U+002E (.):"
    if c == 0x2E {
        // 7.1 "Advance position by 1."
        position = position.saturating_add(1);
        // 7.2 "If position is past the end of input or the code point at position within
        // input is not an ASCII digit, then return the current dimension value with value,
        // input, and position."
        if input.get(position).and_then(|&c| digit(c)).is_none() {
            return current_dimension_value(value, input, position);
        }
        // 7.3 "Let divisor have the value 1." (Kept as the place value in millionths: a
        // digit at divisor 10^k adds digit × 10^(6-k) millionths, nothing past k = 6.)
        let mut place = SCALE;
        // 7.4 "While true:"
        for _ in 0..input.len() {
            // 7.4.1 "Multiply divisor by ten."
            place = place.checked_div(10).unwrap_or(0);
            // 7.4.2 "Add the value of the code point at position within input, interpreted
            // as a base-ten digit (0..9) and divided by divisor, to value."
            let d = input.get(position).and_then(|&c| digit(c)).unwrap_or(0);
            value = value.saturating_add(d.saturating_mul(place));
            // 7.4.3 "Advance position by 1."
            position = position.saturating_add(1);
            // 7.4.4 "If position is past the end of input, then return value as a length."
            let Some(&c) = input.get(position) else {
                return length(value);
            };
            // 7.4.5 "If the code point at position within input is not an ASCII digit, then
            // break."
            if digit(c).is_none() {
                break;
            }
        }
    }
    // 8. "Return the current dimension value with value, input, and position."
    current_dimension_value(value, input, position)
}

/// A dimension's millionths as a [`Num`].
fn num(millionths: i64) -> Num {
    Num {
        millionths,
        is_integer: false,
    }
}

/// §2.3.4.4 "The current dimension value, given value, input, and position".
fn current_dimension_value(value: i64, input: &[u32], position: usize) -> Option<Dimension> {
    match input.get(position) {
        // 1. "If position is past the end of input, then return value as a length."
        None => Some(Dimension::Length(num(value))),
        // 2. "If the code point at position within input is U+0025 (%), then return value
        // as a percentage."
        Some(0x25) => Some(Dimension::Percentage(num(value))),
        // 3. "Return value as a length."
        Some(_) => Some(Dimension::Length(num(value))),
    }
}

/// §2.3.4.5 "rules for parsing nonzero dimension values": a dimension greater than zero, or
/// `None` for an error.
pub fn nonzero_dimension(input: &[u32]) -> Option<Dimension> {
    // 1. "Let input be the string being parsed." 2. "Let value be the result of parsing input
    // using the rules for parsing dimension values." 3. "If value is an error, return an
    // error."
    let value = dimension(input)?;
    // 4. "If value is zero, return an error." 5. "If value is a percentage, return value as
    // a percentage." 6. "Return value as a length."
    let (Dimension::Length(n) | Dimension::Percentage(n)) = value;
    (!n.is_zero()).then_some(value)
}

/// The most code points §2.3.6 keeps: "If input's code point length is greater than 128,
/// truncate input, leaving only the first 128 characters."
const LEGACY_MAX: usize = 128;

/// §2.3.6 "rules for parsing a legacy color value": a colour, or `None` for failure.
pub fn legacy_color(input: &[u32]) -> Option<Rgba> {
    // 1. "If input is the empty string, then return failure."
    if input.is_empty() {
        return None;
    }
    // 2. "Strip leading and trailing ASCII whitespace from input."
    let start = input
        .iter()
        .position(|&c| !is_ascii_whitespace(c))
        .unwrap_or(input.len());
    let end = input
        .iter()
        .rposition(|&c| !is_ascii_whitespace(c))
        .map_or(start, |i| i.saturating_add(1));
    let input = input.get(start..end).unwrap_or_default();
    // 3. "If input is an ASCII case-insensitive match for "transparent", then return
    // failure."
    if eq_ignore_case(input, "transparent") {
        return None;
    }
    // 4. "If input is an ASCII case-insensitive match for one of the named colors, then
    // return the CSS color corresponding to that keyword." ("CSS2 System Colors are not
    // recognized.")
    if let Some([r, g, b]) = lookup(NAMED, input) {
        return Some([r, g, b, 255]);
    }
    Some(legacy_color_digits(input))
}

/// §2.3.6 "rules for parsing a legacy color value", steps 5 to 18, on `input` (steps 1 to 4
/// done): the colour of its hex digits.
pub fn legacy_color_digits(input: &[u32]) -> Rgba {
    // 5. "If input's code point length is four, and the first character in input is U+0023
    // (#), and the last three characters of input are all ASCII hex digits":
    if let [0x23, r, g, b] = *input
        && let (Some(r), Some(g), Some(b)) = (hex_digit(r), hex_digit(g), hex_digit(b))
    {
        // "Interpret the second character of input as a hexadecimal digit; let the red
        // component of result be the resulting number multiplied by 17." (Likewise green
        // and blue.)
        let channel = |v: u32| u8::try_from(v.saturating_mul(17)).unwrap_or(u8::MAX);
        return [channel(r), channel(g), channel(b), 255];
    }
    // 6. "Replace any code points greater than U+FFFF in input (i.e., any characters that are
    // not in the basic multilingual plane) with "00"."
    // 7. "If input's code point length is greater than 128, truncate input, leaving only the
    // first 128 characters."
    let mut s: Vec<u32> = Vec::new();
    for &c in input {
        if s.len() >= LEGACY_MAX {
            break;
        }
        if c > 0xFFFF {
            s.push(0x30);
            if s.len() < LEGACY_MAX {
                s.push(0x30);
            }
        } else {
            s.push(c);
        }
    }
    // 8. "If the first character in input is U+0023 (#), then remove it."
    if s.first() == Some(&0x23) {
        s.remove(0);
    }
    // 9. "Replace any character in input that is not an ASCII hex digit with U+0030 (0)."
    for c in &mut s {
        if hex_digit(*c).is_none() {
            *c = 0x30;
        }
    }
    // 10. "While input's code point length is zero or not a multiple of three, append U+0030
    // (0) to input." (At most three appends.)
    for _ in 0..3 {
        if !s.is_empty() && s.len().checked_rem(3) == Some(0) {
            break;
        }
        s.push(0x30);
    }
    // 11. "Split input into three strings of equal code point length, to obtain three
    // components. Let length be the code point length that all of those components have
    // (one third the code point length of input)."
    let mut length = s.len().checked_div(3).unwrap_or(0);
    let mut starts = [0usize, length, length.saturating_mul(2)];
    // 12. "If length is greater than 8, then remove the leading length-8 characters in each
    // component, and let length be 8."
    if length > 8 {
        let cut = length.saturating_sub(8);
        for st in &mut starts {
            *st = st.saturating_add(cut);
        }
        length = 8;
    }
    // 13. "While length is greater than two and the first character in each component is
    // U+0030 (0), remove that character and reduce length by one."
    for _ in 0..8 {
        let all_zero = starts.iter().all(|&st| s.get(st) == Some(&0x30));
        if length <= 2 || !all_zero {
            break;
        }
        for st in &mut starts {
            *st = st.saturating_add(1);
        }
        length = length.saturating_sub(1);
    }
    // 14. "If length is still greater than two, truncate each component, leaving only the
    // first two characters in each."
    let keep = length.min(2);
    // 15. to 18. "Let result be a CSS color. Interpret the first component as a hexadecimal
    // number; let the red component of result be the resulting number." (Likewise green
    // and blue.) "Return result."
    let component = |st: usize| {
        let mut v: u32 = 0;
        for k in 0..keep {
            let d = s
                .get(st.saturating_add(k))
                .and_then(|&c| hex_digit(c))
                .unwrap_or(0);
            v = v.saturating_mul(16).saturating_add(d);
        }
        u8::try_from(v).unwrap_or(u8::MAX)
    };
    let [r, g, b] = starts.map(component);
    [r, g, b, 255]
}

/// The `font-size` keyword of each value 1 to 7 (§15.3.4's table).
const LEGACY_FONT_SIZES: [&str; 7] = [
    "x-small",
    "small",
    "medium",
    "large",
    "x-large",
    "xx-large",
    "xxx-large",
];

/// §15.3.4 "rules for parsing a legacy font size", for a `font` element's `size`
/// attribute: the `font-size` keyword of its presentational hint, or `None` if "there is no
/// presentational hint".
pub fn legacy_font_size(input: &[u32]) -> Option<&'static str> {
    // 1. "Let input be the attribute's value." 2. "Let position be a pointer into input,
    // initially pointing at the start of the string."
    let mut position = 0usize;
    // 3. "Skip ASCII whitespace within input given position."
    skip_whitespace(input, &mut position);
    // 4. "If position is past the end of input, there is no presentational hint. Return."
    let first = *input.get(position)?;
    // 5. "If the character at position is a U+002B PLUS SIGN character (+), then let mode be
    // relative-plus, and advance position to the next character. Otherwise, if the
    // character at position is a U+002D HYPHEN-MINUS character (-), then let mode be
    // relative-minus, and advance position to the next character. Otherwise, let mode be
    // absolute."
    let mode = match first {
        0x2B => 1,
        0x2D => -1,
        _ => 0,
    };
    if mode != 0 {
        position = position.saturating_add(1);
    }
    // 6. "Collect a sequence of code points that are ASCII digits from input given position,
    // and let digits be the resulting sequence."
    // 7. "If digits is the empty string, there is no presentational hint. Return."
    digit(*input.get(position)?)?;
    // 8. "Interpret digits as a base-ten integer. Let value be the resulting number."
    let mut value = collect_digits(input, &mut position);
    // 9. "If mode is relative-plus, then increment value by 3. If mode is relative-minus,
    // then let value be the result of subtracting value from 3."
    if mode == 1 {
        value = value.saturating_add(3);
    } else if mode == -1 {
        value = 3i64.saturating_sub(value);
    }
    // 10. "If value is greater than 7, let it be 7." 11. "If value is less than 1, let it be
    // 1."
    let value = value.clamp(1, 7);
    // 12. "Set the 'font-size' property to the keyword corresponding to the value of value
    // according to the following table".
    let i = usize::try_from(value.saturating_sub(1)).ok()?;
    LEGACY_FONT_SIZES.get(i).copied()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn u(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    #[test]
    fn integers() {
        assert_eq!(integer(&u("  42px")), Some(42));
        assert_eq!(integer(&u("-7")), Some(-7));
        assert_eq!(integer(&u("+7")), Some(7));
        assert_eq!(integer(&u("-")), None);
        assert_eq!(integer(&u("x1")), None);
        assert_eq!(integer(&u("99999999999999999999")), Some(MAX_INT));
        assert_eq!(non_negative_integer(&u("-1")), None);
        assert_eq!(non_negative_integer(&u("0")), Some(0));
    }

    #[test]
    fn dimensions() {
        let px = |m: i64| Some(Dimension::Length(num(m)));
        let pc = |m: i64| Some(Dimension::Percentage(num(m)));
        assert_eq!(dimension(&u("85%")), pc(85_000_000));
        assert_eq!(dimension(&u(" 40")), px(40_000_000));
        assert_eq!(dimension(&u("1.5")), px(1_500_000));
        assert_eq!(dimension(&u("1.5%")), pc(1_500_000));
        assert_eq!(dimension(&u("1.")), px(1_000_000));
        assert_eq!(dimension(&u("1.%")), pc(1_000_000));
        assert_eq!(dimension(&u("12px")), px(12_000_000));
        assert_eq!(dimension(&u("0.1234567")), px(123_456));
        assert_eq!(dimension(&u("-1")), None);
        assert_eq!(dimension(&u("")), None);
        assert_eq!(nonzero_dimension(&u("0")), None);
        assert_eq!(nonzero_dimension(&u("0%")), None);
        assert_eq!(nonzero_dimension(&u("0.5")), px(500_000));
    }

    #[test]
    fn legacy_colors() {
        let c = |s: &str| legacy_color(&u(s));
        assert_eq!(c("#f6f6ef"), Some([0xf6, 0xf6, 0xef, 255]));
        assert_eq!(c("#ff6600"), Some([0xff, 0x66, 0x00, 255]));
        assert_eq!(c("#828282"), Some([0x82, 0x82, 0x82, 255]));
        assert_eq!(c(" Red "), Some([255, 0, 0, 255]));
        assert_eq!(c("#abc"), Some([0xaa, 0xbb, 0xcc, 255]));
        assert_eq!(c("transparent"), None);
        assert_eq!(c(""), None);
        // The classic cases.
        assert_eq!(c("chucknorris"), Some([0xc0, 0x00, 0x00, 255]));
        assert_eq!(c("crap"), Some([0xc0, 0xa0, 0x00, 255]));
        assert_eq!(c("ninjaturtle"), Some([0x00, 0xa0, 0x00, 255]));
        // One digit per component: each is a one-digit hexadecimal number.
        assert_eq!(c("abc"), Some([0x0a, 0x0b, 0x0c, 255]));
        assert_eq!(c("#1234567890ab"), Some([0x12, 0x56, 0x90, 255]));
        assert_eq!(c("123456789012345678901234"), Some([0x12, 0x90, 0x78, 255]));
        assert_eq!(c("\u{1F600}"), Some([0x00, 0x00, 0x00, 255]));
    }

    #[test]
    fn legacy_font_sizes() {
        let f = |s: &str| legacy_font_size(&u(s));
        assert_eq!(f("1"), Some("x-small"));
        assert_eq!(f("+1"), Some("large"));
        assert_eq!(f("-1"), Some("small"));
        assert_eq!(f("-9"), Some("x-small"));
        assert_eq!(f("12"), Some("xxx-large"));
        assert_eq!(f(" 3x"), Some("medium"));
        assert_eq!(f("+"), None);
        assert_eq!(f(""), None);
    }
}
