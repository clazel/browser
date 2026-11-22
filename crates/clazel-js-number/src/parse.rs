//! StringToNumber.
//!
//! Spec: ECMA-262, StringToNumber (§7.1.4.1.1†), whose grammar is
//! StringNumericLiteral (§7.1.4.1.1†): optional StrWhiteSpace around either
//! a StrDecimalLiteral or a NonDecimalIntegerLiteral. The edition is pinned
//! in `docs/phases/phase-7.md` item 7.1 (ES2026, `SPEC-PIN.md` of
//! `clazel-js-lexer`), but the spec text is not vendored, so every section
//! number here (†) is from `phase-7.md` and has not been checked against the
//! pin.
//!
//! The conversion of the numeric value, "the Number value for the MV"
//! (§6.1.6.1†), is round to nearest, ties to even, of the exact decimal
//! (or hex, octal, binary) value. Three algorithms compute it, tried in this
//! order:
//!
//! 1. Clinger's exact fast path: a mantissa of at most 2^53 and a power of
//!    ten of at most 10^22 are both exact `f64`s, so one multiplication or
//!    division is correctly rounded (Clinger, "How to read floating point
//!    numbers accurately", PLDI 1990).
//! 2. Eisel–Lemire: the leading 19 digits times a 128-bit power of five,
//!    rounding when the product is decisive (Lemire, "Number Parsing at a
//!    Gigabyte per Second", Software: Practice and Experience 51(8), 2021).
//!    When more than 19 digits are significant, it runs for the mantissa and
//!    for the mantissa plus one, and trusts the answer only if they agree.
//! 3. Exact big-integer arithmetic ([`Big`]) on up to 800 significant
//!    digits. A decimal halfway between two doubles needs at most 767
//!    digits, so digits past 800 can only break a tie, which a "sticky"
//!    trailing digit records.
//!
//! Modelling choices:
//!
//! - The input is a Rust `&str`, not UTF-16. A lone surrogate is never
//!   whitespace or part of a numeric literal, so a caller converting a
//!   UTF-16 string lossily gets the same answer (NaN) either way.
//! - The numeric separator `_` is not accepted (the grammar uses
//!   `DecimalDigits[~Sep]`).

use crate::fixed::{BIG_LIMBS_PARSE, FixedBig};
use crate::tables::{EL_MAX_Q, EL_MIN_Q, Tables, tables};

/// The significant digits a decimal is cut to for the exact path.
const MAX_SLOW_DIGITS: usize = 800;

/// Powers of ten that are exact `f64`s.
const POW10: [f64; 23] = [
    1e0, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e10, 1e11, 1e12, 1e13, 1e14, 1e15, 1e16,
    1e17, 1e18, 1e19, 1e20, 1e21, 1e22,
];

/// Whether `c` is StrWhiteSpace: WhiteSpace or LineTerminator (§12.2†,
/// §12.3†): TAB, VT, FF, ZWNBSP, any Zs, LF, CR, LS and PS.
#[must_use]
pub fn is_str_whitespace(c: char) -> bool {
    matches!(
        c,
        '\u{9}'
            | '\u{A}'
            | '\u{B}'
            | '\u{C}'
            | '\u{D}'
            | '\u{20}'
            | '\u{A0}'
            | '\u{1680}'
            | '\u{2000}'
            ..='\u{200A}'
                | '\u{2028}'
                | '\u{2029}'
                | '\u{202F}'
                | '\u{205F}'
                | '\u{3000}'
                | '\u{FEFF}'
    )
}

/// Round `q * 2^exp2` to the nearest `f64`, ties to even; `sticky` says the
/// true value is slightly above `q * 2^exp2` (bits below `q` were dropped).
/// It matters only when `q` has at least 54 bits, which every caller
/// guarantees when it sets it. Overflow gives infinity, underflow zero or a
/// subnormal. The result is not negative.
#[must_use]
pub fn round_to_f64(q: u64, exp2: i64, sticky: bool) -> f64 {
    if q == 0 {
        return 0.0;
    }
    let n = i64::from(64u32.saturating_sub(q.leading_zeros()));
    // The value is in [2^e_top, 2^(e_top + 1)).
    let e_top = n.saturating_sub(1).saturating_add(exp2);
    // The precision in bits: 53 for a normal number, fewer for a subnormal.
    let p = if e_top >= -1022 {
        53
    } else {
        53i64.saturating_sub((-1022i64).saturating_sub(e_top))
    };
    let drop = n.saturating_sub(p);
    let (mant, e) = if drop <= 0 {
        let sh = u32::try_from(drop.saturating_neg()).unwrap_or(0);
        (q.checked_shl(sh).unwrap_or(0), exp2.saturating_add(drop))
    } else if drop > 64 {
        (0, 0)
    } else {
        let wide = u128::from(q);
        let kept = wide >> drop;
        let rem = wide & ((1u128 << drop).wrapping_sub(1));
        let half = 1u128 << drop.saturating_sub(1);
        let up = rem > half || (rem == half && (sticky || kept & 1 == 1));
        let m = (kept as u64).saturating_add(u64::from(up));
        (m, exp2.saturating_add(drop))
    };
    build_f64(mant, e)
}

/// `mant * 2^e` as an `f64`, for `mant <= 2^53`, where a `mant` below 2^52
/// has `e == -1074` (a subnormal).
fn build_f64(mant: u64, e: i64) -> f64 {
    if mant == 0 {
        return 0.0;
    }
    if mant >> 52 == 0 {
        return f64::from_bits(mant);
    }
    let (m, e) = if mant >> 53 != 0 {
        (mant >> 1, e.saturating_add(1))
    } else {
        (mant, e)
    };
    let biased = e.saturating_add(1075);
    if biased >= 2047 {
        f64::INFINITY
    } else if biased < 1 {
        0.0
    } else {
        f64::from_bits(((biased as u64) << 52) | (m & ((1u64 << 52) - 1)))
    }
}

/// Eisel–Lemire: `w * 10^q` rounded to the nearest `f64` (not negative),
/// given the table `entry` for `q` (see `tables`). `None` means the 128-bit
/// product was too close to a rounding boundary to decide, and the caller
/// must use the exact path.
///
/// `entry` must have its top bit set; the result is then a total function of
/// `w` and `q` (the Kani harness `eisel_lemire_total` checks this).
#[must_use]
pub fn eisel_lemire(w: u64, q: i64, entry: u128) -> Option<f64> {
    if w == 0 || q < EL_MIN_Q {
        return Some(0.0);
    }
    if q > EL_MAX_Q {
        return Some(f64::INFINITY);
    }
    let lz = w.leading_zeros();
    let w = w << lz;
    let t_hi = (entry >> 64) as u64;
    let t_lo = entry as u64;
    let first = u128::from(w).wrapping_mul(u128::from(t_hi));
    let mut lo = first as u64;
    let mut hi = (first >> 64) as u64;
    // 52 explicit bits, plus 3: the hidden bit, the rounding bit, one spare.
    let mask = u64::MAX >> 55;
    if hi & mask == mask {
        let second = u128::from(w).wrapping_mul(u128::from(t_lo));
        let s_hi = (second >> 64) as u64;
        lo = lo.wrapping_add(s_hi);
        if s_hi > lo {
            hi = hi.wrapping_add(1);
        }
    }
    if lo == u64::MAX && !(-27..=55).contains(&q) {
        return None;
    }
    let upper = hi >> 63;
    let shift = (upper as u32).saturating_add(9);
    let mut mant = hi >> shift;
    // power(q) = floor(log2(5^q)) + 63, from (152170 + 65536) * q >> 16.
    let power = (217_706i64.saturating_mul(q) >> 16).saturating_add(63);
    let mut p2 = power
        .saturating_add(upper as i64)
        .saturating_sub(i64::from(lz))
        .saturating_add(1023);
    if p2 <= 0 {
        // A subnormal (or zero): shift the mantissa down, rounding.
        let s = p2.saturating_neg().saturating_add(1);
        if s >= 64 {
            return Some(0.0);
        }
        mant >>= s as u32;
        mant = mant.saturating_add(mant & 1);
        mant >>= 1;
        p2 = i64::from(mant >= (1u64 << 52));
        return Some(f64::from_bits(
            ((p2 as u64) << 52) | (mant & ((1u64 << 52) - 1)),
        ));
    }
    // Exactly halfway between two doubles: round to even.
    if lo <= 1 && (-4..=23).contains(&q) && (mant & 3) == 1 && (mant << shift) == hi {
        mant &= !1;
    }
    mant = mant.saturating_add(mant & 1);
    mant >>= 1;
    if mant >= (2u64 << 52) {
        mant = 1u64 << 52;
        p2 = p2.saturating_add(1);
    }
    mant &= !(1u64 << 52);
    if p2 >= 0x7FF {
        return Some(f64::INFINITY);
    }
    Some(f64::from_bits(((p2 as u64) << 52) | mant))
}

/// An unsigned decimal literal, cut into its parts (not yet a value): the
/// value is `int.frac * 10^exp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Decimal<'a> {
    /// The digits before the point (ASCII digits).
    pub int: &'a [u8],
    /// The digits after the point (ASCII digits).
    pub frac: &'a [u8],
    /// The exponent of the ExponentPart, saturated to about ±10^15.
    pub exp: i64,
}

fn digits_len(b: &[u8], from: usize) -> usize {
    b.iter()
        .skip(from)
        .take_while(|c| c.is_ascii_digit())
        .count()
}

/// Match StrUnsignedDecimalLiteral (the whole of `b`) without `Infinity`:
/// `DecimalDigits . DecimalDigits? ExponentPart?`, `. DecimalDigits
/// ExponentPart?` or `DecimalDigits ExponentPart?`.
#[must_use]
pub fn scan_decimal(b: &[u8]) -> Option<Decimal<'_>> {
    let int_end = digits_len(b, 0);
    let int = b.get(..int_end)?;
    let mut pos = int_end;
    let mut frac: &[u8] = &[];
    if b.get(pos) == Some(&b'.') {
        pos = pos.saturating_add(1);
        let n = digits_len(b, pos);
        let end = pos.saturating_add(n);
        frac = b.get(pos..end)?;
        pos = end;
    }
    if int.is_empty() && frac.is_empty() {
        return None;
    }
    let mut exp: i64 = 0;
    if matches!(b.get(pos), Some(b'e' | b'E')) {
        pos = pos.saturating_add(1);
        let mut neg = false;
        match b.get(pos) {
            Some(b'+') => pos = pos.saturating_add(1),
            Some(b'-') => {
                neg = true;
                pos = pos.saturating_add(1);
            }
            _ => {}
        }
        let n = digits_len(b, pos);
        if n == 0 {
            return None;
        }
        let end = pos.saturating_add(n);
        for &c in b.get(pos..end)? {
            exp = exp
                .saturating_mul(10)
                .saturating_add(i64::from(c.wrapping_sub(b'0')))
                .min(1_000_000_000_000_000);
        }
        if neg {
            exp = exp.saturating_neg();
        }
        pos = end;
    }
    if pos != b.len() {
        return None;
    }
    Some(Decimal { int, frac, exp })
}

/// The leading (at most 19) significant digits of `d` as `w`, the decimal
/// exponent `q` with `d = w * 10^q` (when `truncated` is false), and whether
/// any later significant digit was nonzero.
pub(crate) fn leading_digits(d: &Decimal<'_>) -> (u64, i64, bool) {
    let mut w: u64 = 0;
    let mut taken: u32 = 0;
    let mut dropped: i64 = 0;
    let mut truncated = false;
    for &c in d.int.iter().chain(d.frac.iter()) {
        let v = u64::from(c.wrapping_sub(b'0'));
        if taken == 0 && v == 0 {
            continue;
        }
        if taken < 19 {
            w = w.saturating_mul(10).saturating_add(v);
            taken = taken.saturating_add(1);
        } else {
            dropped = dropped.saturating_add(1);
            truncated |= v != 0;
        }
    }
    let q = d
        .exp
        .saturating_sub(d.frac.len() as i64)
        .saturating_add(dropped);
    (w, q, truncated)
}

/// The nearest `f64` to `d` (not negative), by exact big-integer arithmetic.
#[must_use]
pub fn decimal_exact(d: &Decimal<'_>) -> f64 {
    decimal_exact_in::<BIG_LIMBS_PARSE>(d)
}

/// [`decimal_exact`] with `N` limbs of big integer. `N` is a parameter so
/// that the Kani harnesses run the same code at a small `N`; with fewer
/// limbs than the input needs the answer is wrong but defined.
#[must_use]
pub fn decimal_exact_in<const N: usize>(d: &Decimal<'_>) -> f64 {
    let mut big = FixedBig::<N>::zero();
    let mut taken: usize = 0;
    let mut dropped: i64 = 0;
    let mut sticky = false;
    for &c in d.int.iter().chain(d.frac.iter()) {
        let v = u64::from(c.wrapping_sub(b'0'));
        if taken == 0 && v == 0 {
            continue;
        }
        if taken < MAX_SLOW_DIGITS {
            big.mul_small(10);
            big.add_small(v);
            taken = taken.saturating_add(1);
        } else {
            dropped = dropped.saturating_add(1);
            sticky |= v != 0;
        }
    }
    if big.is_zero() {
        return 0.0;
    }
    let mut e10 = d
        .exp
        .saturating_sub(d.frac.len() as i64)
        .saturating_add(dropped);
    let mut nd = taken as i64;
    if sticky {
        // Digits past the cut can only matter as "above the truncation".
        big.mul_small(10);
        big.add_small(1);
        e10 = e10.saturating_sub(1);
        nd = nd.saturating_add(1);
    }
    let top = e10.saturating_add(nd);
    if top > 310 {
        return f64::INFINITY;
    }
    if top < -330 {
        return 0.0;
    }
    if e10 >= 0 {
        big.mul_pow10(u32::try_from(e10).unwrap_or(0));
        let bl = big.bit_len();
        if bl <= 64 {
            return round_to_f64(big.low_u128() as u64, 0, false);
        }
        let (hi, st) = big.shr(bl.saturating_sub(64));
        return round_to_f64(hi.low_u128() as u64, bl.saturating_sub(64) as i64, st);
    }
    let p = FixedBig::<N>::pow10(u32::try_from(e10.saturating_neg()).unwrap_or(0));
    // Scale so the quotient has 55 or 56 bits, more than a double needs.
    let s = (p.bit_len() as i64)
        .saturating_sub(big.bit_len() as i64)
        .saturating_add(55);
    let (num, den) = if s >= 0 {
        (big.shl(s as u64), p)
    } else {
        (big, p.shl(s.unsigned_abs()))
    };
    let (quo, rem) = FixedBig::<N>::divrem(&num, &den);
    round_to_f64(quo.low_u128() as u64, s.saturating_neg(), !rem.is_zero())
}

/// The nearest `f64` to `d` (not negative), using `t` for Eisel–Lemire.
#[must_use]
pub fn decimal_to_f64(d: &Decimal<'_>, t: &Tables) -> f64 {
    decimal_to_f64_in::<BIG_LIMBS_PARSE>(d, t)
}

/// [`decimal_to_f64`] with `N` limbs for the exact path (see
/// [`decimal_exact_in`]).
#[must_use]
pub fn decimal_to_f64_in<const N: usize>(d: &Decimal<'_>, t: &Tables) -> f64 {
    let (w, q, truncated) = leading_digits(d);
    if w == 0 {
        return 0.0;
    }
    if !truncated && w <= (1u64 << 53) && (-22..=22).contains(&q) {
        let idx = usize::try_from(q.unsigned_abs()).unwrap_or(0);
        let p = POW10.get(idx).copied().unwrap_or(1.0);
        let m = w as f64;
        return if q < 0 { m / p } else { m * p };
    }
    if q < EL_MIN_Q {
        return 0.0;
    }
    if q > EL_MAX_Q {
        return f64::INFINITY;
    }
    let entry = usize::try_from(q.saturating_sub(EL_MIN_Q))
        .ok()
        .and_then(|i| t.el.get(i).copied());
    if let Some(entry) = entry {
        let lower = eisel_lemire(w, q, entry);
        if let Some(lo) = lower {
            if !truncated {
                return lo;
            }
            // w + 1 <= 10^19 does not overflow.
            if eisel_lemire(w.saturating_add(1), q, entry)
                .is_some_and(|hi| hi.to_bits() == lo.to_bits())
            {
                return lo;
            }
        }
    }
    decimal_exact_in::<N>(d)
}

/// The value of the ASCII digit `c` (`0-9`, `a-f`, `A-F`) if it is below
/// `radix`: `char::to_digit` for the radixes 2 to 16, on bytes.
fn digit_in_radix(c: u8, radix: u32) -> Option<u32> {
    let v = match c {
        b'0'..=b'9' => u32::from(c.wrapping_sub(b'0')),
        b'a'..=b'f' => u32::from(c.wrapping_sub(b'a')).saturating_add(10),
        b'A'..=b'F' => u32::from(c.wrapping_sub(b'A')).saturating_add(10),
        _ => return None,
    };
    (v < radix).then_some(v)
}

/// The value of the digits of `b` in radix `1 << bits` (`bits` in 1..=4),
/// rounded to the nearest `f64`; `None` if `b` is empty or has a bad digit.
pub(crate) fn radix_value(b: &[u8], bits: u32) -> Option<f64> {
    if b.is_empty() {
        return None;
    }
    let radix = 1u32 << bits;
    let mut acc: u64 = 0;
    let mut exp2: i64 = 0;
    let mut sticky = false;
    let mut full = false;
    for &c in b {
        let v = digit_in_radix(c, radix)?;
        if full {
            sticky |= v != 0;
            exp2 = exp2.saturating_add(i64::from(bits));
        } else {
            let free = acc.leading_zeros();
            if free >= bits {
                acc = (acc << bits) | u64::from(v);
            } else {
                // `free < bits`: take the top `free` bits of this digit.
                let rest = bits.saturating_sub(free);
                acc = (acc << free) | u64::from(v >> rest);
                sticky |= v & (1u32 << rest).wrapping_sub(1) != 0;
                exp2 = exp2.saturating_add(i64::from(rest));
                full = true;
            }
        }
    }
    Some(round_to_f64(acc, exp2, sticky))
}

/// StringToNumber (§7.1.4.1.1†): the Number value of `s`, or NaN.
#[must_use]
pub fn string_to_number(s: &str) -> f64 {
    string_to_number_bytes::<BIG_LIMBS_PARSE>(s.as_bytes(), tables())
}

/// The length in bytes of the StrWhiteSpace character at the start of `b`
/// (UTF-8), or 0 if there is none: the code points of [`is_str_whitespace`].
fn leading_whitespace(b: &[u8]) -> usize {
    match b {
        [0x09..=0x0D | 0x20, ..] => 1,
        [0xC2, 0xA0, ..] => 2,
        [0xE1, 0x9A, 0x80, ..]
        | [0xE2, 0x80, 0x80..=0x8A | 0xA8 | 0xA9 | 0xAF, ..]
        | [0xE2, 0x81, 0x9F, ..]
        | [0xE3, 0x80, 0x80, ..]
        | [0xEF, 0xBB, 0xBF, ..] => 3,
        _ => 0,
    }
}

/// The length in bytes of the StrWhiteSpace character at the end of `b`.
fn trailing_whitespace(b: &[u8]) -> usize {
    match b {
        [.., 0x09..=0x0D | 0x20] => 1,
        [.., 0xC2, 0xA0] => 2,
        [.., 0xE1, 0x9A, 0x80]
        | [.., 0xE2, 0x80, 0x80..=0x8A | 0xA8 | 0xA9 | 0xAF]
        | [.., 0xE2, 0x81, 0x9F]
        | [.., 0xE3, 0x80, 0x80]
        | [.., 0xEF, 0xBB, 0xBF] => 3,
        _ => 0,
    }
}

/// `b` (the UTF-8 of a string) without its leading and trailing
/// StrWhiteSpace: `str::trim_matches(is_str_whitespace)` on bytes, so that
/// the conversion below is a function of bytes and Kani never meets `char`
/// decoding. (The tests compare the two on every code point.)
#[must_use]
pub fn trim_str_whitespace(b: &[u8]) -> &[u8] {
    let mut t = b;
    loop {
        let n = leading_whitespace(t);
        if n == 0 {
            break;
        }
        t = t.get(n..).unwrap_or(&[]);
    }
    loop {
        let n = trailing_whitespace(t);
        if n == 0 {
            break;
        }
        t = t.get(..t.len().saturating_sub(n)).unwrap_or(&[]);
    }
    t
}

/// StringToNumber on the UTF-8 bytes of the string, with `t` for
/// Eisel–Lemire and `N` limbs for the exact path ([`decimal_exact_in`]).
/// Bytes that are not UTF-8 are not whitespace and not part of a literal,
/// so they give NaN, as `string_to_number` would for the same text.
#[must_use]
pub fn string_to_number_bytes<const N: usize>(s: &[u8], tbl: &Tables) -> f64 {
    let t = trim_str_whitespace(s);
    if t.is_empty() {
        return 0.0;
    }
    // NonDecimalIntegerLiteral takes no sign.
    if let (Some(&b'0'), Some(&x), Some(rest)) = (t.first(), t.get(1), t.get(2..)) {
        let bits = match x {
            b'x' | b'X' => 4,
            b'o' | b'O' => 3,
            b'b' | b'B' => 1,
            _ => 0,
        };
        if bits != 0 {
            return radix_value(rest, bits).unwrap_or(f64::NAN);
        }
    }
    let (neg, body) = match t.first() {
        Some(b'-') => (true, t.get(1..).unwrap_or(&[])),
        Some(b'+') => (false, t.get(1..).unwrap_or(&[])),
        _ => (false, t),
    };
    let mag = if body == b"Infinity" {
        f64::INFINITY
    } else {
        match scan_decimal(body) {
            Some(d) => decimal_to_f64_in::<N>(&d, tbl),
            None => return f64::NAN,
        }
    };
    if neg { -mag } else { mag }
}
