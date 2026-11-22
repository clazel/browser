//! The values of the AST's names and literals, which the AST does not store
//! (it keeps spans only): identifier names and string values come from
//! `clazel-js-lexer` run again at the node's start, numeric values from the
//! node's source text.

use crate::compile::CompileError;
use clazel_js_lexer::api::{Next, Value};
use clazel_js_lexer::exec::next_token;
use clazel_js_lexer::spec::Goal;

/// The token of `src` that starts at `start`, with the goal that lexes names,
/// strings and numbers.
fn token_value(src: &[u32], start: usize) -> Result<Value, CompileError> {
    if start > src.len() {
        return Err(CompileError::Internal("span outside the source text"));
    }
    match next_token(src, start, Goal::InputElementDiv, false) {
        Ok(Next::Token(t)) => Ok(t.element.value),
        _ => Err(CompileError::Internal("no token at a node's start")),
    }
}

/// The code points of the `IdentifierName` or `PrivateIdentifier` at `start`
/// (§12.7.1.2 IdentifierCodePoints: escapes resolved).
pub fn name_at(src: &[u32], start: usize) -> Result<Vec<u32>, CompileError> {
    match token_value(src, start)? {
        Value::Name { code_points, .. } => Ok(code_points),
        _ => Err(CompileError::Internal("a name node does not start a name")),
    }
}

/// The code units of the name at `start`, as UTF-16.
pub fn name_units_at(src: &[u32], start: usize) -> Result<Vec<u16>, CompileError> {
    let cps = name_at(src, start)?;
    Ok(to_utf16(&cps))
}

/// The string value (§12.9.4.2 SV) of the `StringLiteral` at `start`.
pub fn string_at(src: &[u32], start: usize) -> Result<Vec<u16>, CompileError> {
    match token_value(src, start)? {
        Value::String { units } => Ok(units),
        _ => Err(CompileError::Internal(
            "a string node does not start a string",
        )),
    }
}

/// The template value (TV, §12.9.6.1) and the template raw value (TRV,
/// §12.9.6.2) of the template component (`TemplateElement`) that starts at
/// `start`: a head or a no-substitution template starts at its `` ` ``, a middle
/// or a tail at its `}`.
pub fn template_at(
    src: &[u32],
    start: usize,
) -> Result<(Option<Vec<u16>>, Vec<u16>), CompileError> {
    if start > src.len() {
        return Err(CompileError::Internal("span outside the source text"));
    }
    let goal = if src.get(start).copied() == Some(u32::from(b'}')) {
        Goal::InputElementTemplateTail
    } else {
        Goal::InputElementDiv
    };
    match next_token(src, start, goal, false) {
        Ok(Next::Token(t)) => match t.element.value {
            Value::Template { cooked, raw } => Ok((cooked, raw)),
            _ => Err(CompileError::Internal(
                "a template node does not start a template",
            )),
        },
        _ => Err(CompileError::Internal("no token at a node's start")),
    }
}

/// The body and the flags of the regular expression literal `src[start..end]`
/// (`/body/flags`, §12.9.5†): the text between the first slash and the last,
/// and the text after the last, as UTF-16 code units. The flags contain no
/// slash, so the last slash closes the body even when the body has a `/` in a
/// class.
pub fn regex_at(
    src: &[u32],
    start: usize,
    end: usize,
) -> Result<(Vec<u16>, Vec<u16>), CompileError> {
    let text = src
        .get(start..end)
        .ok_or(CompileError::Internal("regular expression out of range"))?;
    let slash = u32::from(b'/');
    let last = text
        .iter()
        .rposition(|&c| c == slash)
        .ok_or(CompileError::Internal("regular expression without a slash"))?;
    if text.first() != Some(&slash) || last == 0 {
        return Err(CompileError::Internal("malformed regular expression"));
    }
    let body = text.get(1..last).unwrap_or(&[]);
    let flags = text.get(last.saturating_add(1)..).unwrap_or(&[]);
    Ok((to_utf16(body), to_utf16(flags)))
}

/// Code points to UTF-16 code units (§6.1.4: a code point above U+FFFF is a
/// surrogate pair; a lone surrogate is kept).
pub fn to_utf16(cps: &[u32]) -> Vec<u16> {
    let mut out = Vec::with_capacity(cps.len());
    for &c in cps {
        if let Ok(u) = u16::try_from(c) {
            out.push(u);
        } else if let Some(v) = c.checked_sub(0x1_0000) {
            let hi = 0xD800u32.saturating_add(v.wrapping_shr(10));
            let lo = 0xDC00u32.saturating_add(v & 0x3FF);
            out.extend(u16::try_from(hi));
            out.extend(u16::try_from(lo));
        }
    }
    out
}

/// What a numeric literal denotes.
#[derive(Clone, Debug, PartialEq)]
pub enum Number {
    /// A Number value (§12.9.3.1 NumericValue): never a NaN.
    Value(f64),
    /// A BigInt literal: its digits as in [`crate::bytecode::Const::BigInt`].
    BigInt(Vec<u16>),
}

/// The value of the `NumericLiteral` spanning `start..end` of `src`
/// (§12.9.3.1 and Annex B.1.1: `NumericLiteralSeparator`s dropped, legacy
/// octal and non-octal decimal integers).
pub fn number_at(src: &[u32], start: usize, end: usize) -> Result<Number, CompileError> {
    let cps = src
        .get(start..end)
        .ok_or(CompileError::Internal("span outside the source text"))?;
    let mut text: Vec<u8> = Vec::with_capacity(cps.len());
    for &c in cps {
        let b = u8::try_from(c).map_err(|_| CompileError::Internal("non-ASCII numeric literal"))?;
        if b != b'_' {
            text.push(b);
        }
    }
    if text.last() == Some(&b'n') {
        text.pop();
        return Ok(Number::BigInt(text.iter().map(|&b| u16::from(b)).collect()));
    }
    let bad = CompileError::Internal("malformed numeric literal");
    let radix_body = |radix: u32, digits: &[u8]| -> Result<f64, CompileError> {
        radix_value(radix, digits).ok_or(CompileError::Internal("malformed numeric literal"))
    };
    match text.as_slice() {
        [b'0', b'x' | b'X', rest @ ..] => Ok(Number::Value(radix_body(16, rest)?)),
        [b'0', b'o' | b'O', rest @ ..] => Ok(Number::Value(radix_body(8, rest)?)),
        [b'0', b'b' | b'B', rest @ ..] => Ok(Number::Value(radix_body(2, rest)?)),
        [b'0', rest @ ..] if !rest.is_empty() && rest.iter().all(|b| (b'0'..=b'7').contains(b)) => {
            // LegacyOctalIntegerLiteral.
            Ok(Number::Value(radix_body(8, rest)?))
        }
        _ => {
            let s = std::str::from_utf8(&text).map_err(|_| bad)?;
            let v: f64 = s
                .parse()
                .map_err(|_| CompileError::Internal("malformed numeric literal"))?;
            Ok(Number::Value(v))
        }
    }
}

/// The digits' value in `radix` (2, 8 or 16), rounded to nearest, ties to
/// even, as §12.9.3.1 requires of an integer literal above 2^53 (a power-of-two
/// radix, so the exact value has a bit pattern that can be rounded without a
/// big integer: the top 64 bits and a sticky bit for the rest).
fn radix_value(radix: u32, digits: &[u8]) -> Option<f64> {
    let bits_per: usize = match radix {
        2 => 1,
        8 => 3,
        _ => 4,
    };
    let mut bits: Vec<bool> = Vec::with_capacity(digits.len().saturating_mul(bits_per));
    for &d in digits {
        let v = (d as char).to_digit(radix)?;
        let mut k = bits_per;
        while k > 0 {
            k = k.saturating_sub(1);
            bits.push((v >> k) & 1 == 1);
        }
    }
    let Some(first_one) = bits.iter().position(|&b| b) else {
        // All digits zero.
        return Some(0.0);
    };
    let sig = bits.get(first_one..)?;
    let mut top: u64 = 0;
    for &b in sig.iter().take(64) {
        top = top.wrapping_mul(2).wrapping_add(u64::from(b));
    }
    if sig.len() <= 64 {
        // At most 64 significant bits: exact in a u64, and the conversion
        // rounds to nearest, ties to even.
        return Some(top as f64);
    }
    if sig.get(64..).unwrap_or(&[]).iter().any(|&b| b) {
        top |= 1;
    }
    // `top as f64` rounds on the 64 significant bits, and the sticky bit in
    // bit 0 breaks ties correctly; the scale is a power of two, so the
    // product is exact unless it overflows (to infinity, as §6.1.6.1 rounds).
    let exp = sig.len().saturating_sub(64);
    // 2^exp built from its bits: `powi` is not exact under Miri, which perturbs
    // it on purpose.
    let scale = if exp > 1023 {
        f64::INFINITY
    } else {
        f64::from_bits(
            1023u64
                .saturating_add(u64::try_from(exp).ok()?)
                .wrapping_shl(52),
        )
    };
    Some(top as f64 * scale)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn num(s: &str) -> Result<Number, CompileError> {
        let cps: Vec<u32> = s.chars().map(u32::from).collect();
        number_at(&cps, 0, cps.len())
    }

    fn val(s: &str) -> f64 {
        match num(s) {
            Ok(Number::Value(v)) => v,
            _ => f64::NAN,
        }
    }

    #[test]
    fn numbers() {
        assert_eq!(val("0"), 0.0);
        assert_eq!(val("42"), 42.0);
        assert_eq!(val("1_000"), 1000.0);
        assert_eq!(val(".5"), 0.5);
        assert_eq!(val("5."), 5.0);
        assert_eq!(val("1e3"), 1000.0);
        assert_eq!(val("0x10"), 16.0);
        assert_eq!(val("0b101"), 5.0);
        assert_eq!(val("0b0"), 0.0);
        assert_eq!(val("0x0"), 0.0);
        assert_eq!(val("00"), 0.0);
        assert_eq!(val("0o17"), 15.0);
        assert_eq!(val("017"), 15.0);
        assert_eq!(val("089"), 89.0);
        assert_eq!(val("08.5"), 8.5);
        // 2^53 + 1 is a tie, rounded to even: 2^53.
        assert_eq!(val("0x20000000000001"), 9007199254740992.0);
        // 2^53 + 3 rounds to 2^53 + 4.
        assert_eq!(val("0x20000000000003"), 9007199254740996.0);
        assert_eq!(val("0xFFFFFFFFFFFFFFFFF"), 295147905179352825856.0);
        assert!(val("0x1").is_finite());
        assert_eq!(val(&format!("0x1{}", "0".repeat(300))), f64::INFINITY);
        assert_eq!(num("10n"), Ok(Number::BigInt(vec![0x31, 0x30])));
    }
}
