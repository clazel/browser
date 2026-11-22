//! BigInt values: parsing and printing (phase-7.md item 7.11).
//!
//! Spec (section numbers † are from `phase-7.md`, unchecked against the
//! pin): StringToBigInt §7.1.14†, BigInt::toString §6.1.6.2.23†, the value
//! of a BigInt literal §12.9.3† (`DecimalBigIntegerLiteral` and
//! `NonDecimalIntegerLiteral` with `BigIntLiteralSuffix`), and the radix
//! check of `BigInt.prototype.toString` §21.2.3.3†.
//!
//! Modelling choices:
//!
//! - [`BigInt`] is a sign and a [`Big`] magnitude, not a new limb type. The
//!   magnitude arithmetic exists once (in [`crate::bigint`]) and this type
//!   adds only the sign, with the invariant that zero is never negative (so
//!   `-0` and `0` are the one value `0n`, as BigInt has no negative zero).
//!   Heap storage (item 7.5) is not this crate's: the heap will hold a
//!   magnitude and a sign and can use these functions to convert.
//! - Input is a Rust `&str`, not UTF-16. A lone surrogate is never white
//!   space or a digit, so a caller converting lossily gets the same answer.
//! - StringToBigInt returns `None` for the spec's `undefined` (a string that
//!   is not a StringIntegerLiteral); `BigInt("x")` throws a `SyntaxError`
//!   from that, which is the caller's.
//! - "Throw a RangeError" for a radix outside 2 to 36 is `Err(RangeError)`.
//! - BigInt::toString with a radix other than 10 is implementation-
//!   approximated in the spec; this prints lowercase digits `0-9a-z` with a
//!   leading `-`, as every engine does.
//! - Both directions are quadratic in the length (a word-sized chunk of
//!   digits at a time). That is fine for the sizes scripts use; a faster
//!   conversion for huge values can come with item 7.5's heap type.

use crate::bigint::Big;
use crate::format::RangeError;
use crate::parse::is_str_whitespace;

/// A BigInt: an integer of unbounded size. Zero is never negative.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct BigInt {
    neg: bool,
    mag: Big,
}

/// The value of the digit character `b` in radix 36: `0-9`, then `a-z` or
/// `A-Z` for 10 to 35. (A digit of a smaller radix also needs `< radix`.)
#[must_use]
pub fn digit_value(b: u8) -> Option<u32> {
    match b {
        b'0'..=b'9' => Some(u32::from(b.wrapping_sub(b'0'))),
        b'a'..=b'z' => Some(u32::from(b.wrapping_sub(b'a')).saturating_add(10)),
        b'A'..=b'Z' => Some(u32::from(b.wrapping_sub(b'A')).saturating_add(10)),
        _ => None,
    }
}

/// The lowercase digit character for a value below 36.
#[must_use]
pub fn digit_char(d: u32) -> Option<u8> {
    match d {
        0..=9 => Some(b'0'.wrapping_add(d as u8)),
        10..=35 => Some(b'a'.wrapping_add((d as u8).wrapping_sub(10))),
        _ => None,
    }
}

/// `(p, k)` with `p = radix^k` the largest power of `radix` that fits in a
/// `u64`. (`(1, 0)` for a radix below 2, which no caller passes.)
#[must_use]
pub fn chunk_power(radix: u32) -> (u64, u32) {
    let r = u64::from(radix);
    if r < 2 {
        return (1, 0);
    }
    let mut p: u64 = 1;
    let mut k: u32 = 0;
    // 2^64 does not fit, so at most 63 steps run.
    for _ in 0..64 {
        match p.checked_mul(r) {
            Some(n) => {
                p = n;
                k = k.saturating_add(1);
            }
            None => break,
        }
    }
    (p, k)
}

/// Append the digits of `v` in `radix` (2 to 36), padded with zeros on the
/// left to `width` digits (at most 64) and at least one digit.
pub fn push_chunk(out: &mut Vec<u8>, v: u64, radix: u32, width: u32) {
    let r = u64::from(radix);
    let mut buf = [b'0'; 64];
    let mut n = v;
    let mut used: usize = 0;
    for slot in buf.iter_mut().rev() {
        let d = n.checked_rem(r).unwrap_or(0) as u32;
        *slot = digit_char(d).unwrap_or(b'0');
        n = n.checked_div(r).unwrap_or(0);
        used = used.saturating_add(1);
        if n == 0 {
            break;
        }
    }
    let len = used.max(width as usize).min(64);
    for &b in buf.iter().skip(64usize.saturating_sub(len)) {
        out.push(b);
    }
}

/// The digits of a magnitude in `radix` (2 to 36), most significant first
/// (`"0"` for zero).
fn magnitude_digits(mag: &Big, radix: u32) -> Vec<u8> {
    if mag.is_zero() {
        return vec![b'0'];
    }
    let mut out = Vec::new();
    if radix.is_power_of_two() {
        // Each digit is `bits` bits of the magnitude.
        let bits = u64::from(radix.trailing_zeros());
        let count = mag.bit_len().div_ceil(bits);
        let mut i = count;
        while i > 0 {
            i = i.saturating_sub(1);
            let mut d: u32 = 0;
            for j in 0..bits {
                if mag.bit(i.saturating_mul(bits).saturating_add(j)) {
                    d |= 1u32 << j;
                }
            }
            out.push(digit_char(d).unwrap_or(b'0'));
        }
        return out;
    }
    let (p, k) = chunk_power(radix);
    let mut t = mag.clone();
    let mut chunks: Vec<u64> = Vec::new();
    while !t.is_zero() {
        chunks.push(t.div_small(p));
    }
    for (i, c) in chunks.iter().rev().enumerate() {
        push_chunk(&mut out, *c, radix, if i == 0 { 0 } else { k });
    }
    out
}

/// The magnitude with the digits `digits` in `radix` (2 to 36); `None` if
/// any byte is not a digit below `radix`. No digits is zero.
fn parse_magnitude(digits: &[u8], radix: u32) -> Option<Big> {
    if !(2..=36).contains(&radix) {
        return None;
    }
    let (p, k) = chunk_power(radix);
    let mut mag = Big::zero();
    for chunk in digits.chunks((k as usize).max(1)) {
        let mut acc: u64 = 0;
        let mut mult: u64 = 1;
        for &b in chunk {
            let d = digit_value(b)?;
            if d >= radix {
                return None;
            }
            // At most `k` digits, so `acc < radix^k <= u64::MAX`; `mult` is
            // `radix^len`, and `len <= k`.
            acc = acc
                .wrapping_mul(u64::from(radix))
                .wrapping_add(u64::from(d));
            mult = mult.wrapping_mul(u64::from(radix));
        }
        mag.mul_small(if chunk.len() >= k as usize { p } else { mult });
        mag.add_small(acc);
    }
    Some(mag)
}

impl BigInt {
    /// `0n`.
    #[must_use]
    pub fn zero() -> Self {
        Self::default()
    }

    /// The value with the sign `neg` and magnitude `mag` (`-0` is `0n`).
    #[must_use]
    pub fn from_parts(neg: bool, mag: Big) -> Self {
        Self {
            neg: neg && !mag.is_zero(),
            mag,
        }
    }

    /// The value `x`.
    #[must_use]
    pub fn from_u64(x: u64) -> Self {
        Self::from_parts(false, Big::from_u64(x))
    }

    /// The value `x`.
    #[must_use]
    pub fn from_i64(x: i64) -> Self {
        Self::from_parts(x < 0, Big::from_u64(x.unsigned_abs()))
    }

    /// Whether the value is negative (never for zero).
    #[must_use]
    pub fn is_negative(&self) -> bool {
        self.neg
    }

    /// Whether the value is `0n`.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.mag.is_zero()
    }

    /// The absolute value.
    #[must_use]
    pub fn magnitude(&self) -> &Big {
        &self.mag
    }

    /// The value with the sign flipped (`0n` stays `0n`).
    #[must_use]
    pub fn negated(&self) -> Self {
        Self::from_parts(!self.neg, self.mag.clone())
    }

    /// The value with the digits `digits` (no sign, no prefix) in `radix`,
    /// 2 to 36, upper or lower case; `None` for any other byte, for a radix
    /// outside 2 to 36, and for no digits.
    #[must_use]
    pub fn parse_radix(digits: &[u8], radix: u32) -> Option<Self> {
        if digits.is_empty() {
            return None;
        }
        parse_magnitude(digits, radix).map(|m| Self::from_parts(false, m))
    }

    /// BigInt::toString(x, radix) (§6.1.6.2.23†) with the radix check of
    /// `BigInt.prototype.toString` (§21.2.3.3†).
    ///
    /// # Errors
    ///
    /// `RangeError` when `radix` is not in `2..=36` (§21.2.3.3† step 4).
    pub fn to_string_radix(&self, radix: u32) -> Result<String, RangeError> {
        if !(2..=36).contains(&radix) {
            return Err(RangeError);
        }
        let mut bytes = Vec::new();
        if self.neg {
            bytes.push(b'-');
        }
        bytes.extend_from_slice(&magnitude_digits(&self.mag, radix));
        // Every byte pushed is ASCII.
        Ok(bytes.iter().map(|&b| char::from(b)).collect())
    }
}

/// The radix a `0x`, `0o` or `0b` prefix letter names, or 0.
fn prefix_radix(x: u8) -> u32 {
    match x {
        b'x' | b'X' => 16,
        b'o' | b'O' => 8,
        b'b' | b'B' => 2,
        _ => 0,
    }
}

/// StringToBigInt (§7.1.14†): the BigInt `s` denotes, or `None` for the
/// spec's `undefined`.
///
/// 1.-3. The text must be a StringIntegerLiteral: optional StrWhiteSpace
///       (WhiteSpace and LineTerminator), then optionally a StrIntegerLiteral
///       (a SignedInteger of decimal digits, or a NonDecimalIntegerLiteral
///       `0x`, `0o`, `0b` with its digits, which takes no sign), then
///       optional StrWhiteSpace. No separators, no `n`, no point, no
///       exponent, and a prefix needs at least one digit.
/// 4.-6. Its value is the MV (the empty string and white space alone are 0n;
///       `-0` is 0n).
#[must_use]
pub fn string_to_bigint(s: &str) -> Option<BigInt> {
    let t = s.trim_matches(is_str_whitespace).as_bytes();
    if t.is_empty() {
        return Some(BigInt::zero());
    }
    if let (Some(&b'0'), Some(&x), Some(rest)) = (t.first(), t.get(1), t.get(2..)) {
        let radix = prefix_radix(x);
        if radix != 0 {
            return BigInt::parse_radix(rest, radix);
        }
    }
    let (neg, digits) = match t.first() {
        Some(b'-') => (true, t.get(1..).unwrap_or(&[])),
        Some(b'+') => (false, t.get(1..).unwrap_or(&[])),
        _ => (false, t),
    };
    let v = BigInt::parse_radix(digits, 10)?;
    Some(BigInt::from_parts(neg, v.mag))
}

/// Whether `b` is digits with `NumericLiteralSeparator`s only between two
/// digits (`DecimalDigits[+Sep]` and its radix analogues, §12.9.3†).
fn separators_ok(b: &[u8]) -> bool {
    b.first() != Some(&b'_')
        && b.last() != Some(&b'_')
        && !b.is_empty()
        && !b.windows(2).any(|w| w == b"__")
}

/// The value of a BigInt literal's source text (§12.9.3†): `src` ends in
/// `BigIntLiteralSuffix` (`n`), and is either `0n`, a nonzero decimal digit
/// followed by decimal digits with separators, or `0x`/`0o`/`0b` and the
/// digits of that radix with separators. `None` if it is not one of these
/// (the lexer has already scanned the literal, so its callers get `Some`).
///
/// `DecimalBigIntegerLiteral :: 0n | NonZeroDigit DecimalDigits[+Sep]? n |
/// NonZeroDigit NumericLiteralSeparator DecimalDigits[+Sep] n`: with a
/// nonzero first digit, the whole run is `digit (_? digit)*`, which is
/// [`separators_ok`]. The value is the MV, ignoring separators.
#[must_use]
pub fn bigint_literal_value(src: &str) -> Option<BigInt> {
    let body = src.as_bytes().strip_suffix(b"n")?;
    if body == b"0" {
        return Some(BigInt::zero());
    }
    if let (Some(&b'0'), Some(&x), Some(rest)) = (body.first(), body.get(1), body.get(2..)) {
        let radix = prefix_radix(x);
        if radix != 0 {
            if !separators_ok(rest) {
                return None;
            }
            let digits: Vec<u8> = rest.iter().copied().filter(|&c| c != b'_').collect();
            return BigInt::parse_radix(&digits, radix);
        }
    }
    // NonZeroDigit first: `0` followed by anything else is not a BigInt literal.
    if !matches!(body.first(), Some(b'1'..=b'9')) || !separators_ok(body) {
        return None;
    }
    let digits: Vec<u8> = body.iter().copied().filter(|&c| c != b'_').collect();
    BigInt::parse_radix(&digits, 10)
}
