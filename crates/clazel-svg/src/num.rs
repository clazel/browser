//! Numbers: SVG 2 section 9.3.9's `number` and `coordinate`, as far as the
//! scope reads them (decimal fractions, no exponent), in fixed point.

use crate::limits::{MAX_NUMBER, ONE};
use clazel_image_shape::Error;

/// Powers of ten up to 10^9: the fraction digits kept.
const POW10: [u64; 10] = [
    1,
    10,
    100,
    1_000,
    10_000,
    100_000,
    1_000_000,
    10_000_000,
    100_000_000,
    1_000_000_000,
];

/// The most fraction digits that count (the rest are read and ignored).
const KEPT: usize = 9;

fn digit(b: Option<&u8>) -> Option<u8> {
    match b {
        Some(&c) if c.is_ascii_digit() => Some(c.wrapping_sub(b'0')),
        _ => None,
    }
}

/// Whether a number can start with this byte (a sign, a digit or a point).
pub(crate) fn starts_number(b: Option<&u8>) -> bool {
    matches!(b, Some(b'+' | b'-' | b'.' | b'0'..=b'9'))
}

/// `round(frac / 10^kept * 2^16)`, half up, for `frac` below `10^kept` and
/// `kept` at most 9: at most 2^16.
pub(crate) fn fraction_fixed(frac: u64, kept: usize) -> u64 {
    let scale = POW10.get(kept).copied().unwrap_or(1);
    frac.saturating_mul(ONE as u64)
        .saturating_add(scale / 2)
        .checked_div(scale)
        .unwrap_or(0)
}

/// Reads `sign? number` at `pos` of `s`. `Ok(None)` when no number can
/// start there (the caller decides whether that is an error). On success the
/// value in units of 2^-16, with magnitude at most 2^20 (else
/// [`Error::Unsupported`]), and the position after the number.
///
/// SVG 2 section 9.3.9: `coordinate::= sign? number`,
/// `number::= fractional-constant exponent?`,
/// `fractional-constant::= (digit* "." digit+) | digit+`. The exponent and a
/// trailing point (`23.`, which the standard disallows and permits a user
/// agent to accept) are refused: the exponent as unsupported, the point as
/// malformed. The greedy rule of the same section ("M 100-200", "M 0.6.5")
/// holds because the reader stops at the first byte that cannot continue
/// the number.
pub(crate) fn number(s: &[u8], pos: usize) -> Result<Option<(i64, usize)>, Error> {
    if !starts_number(s.get(pos)) {
        return Ok(None);
    }
    let mut p = pos;
    let mut negative = false;
    if let Some(&c) = s.get(p)
        && (c == b'+' || c == b'-')
    {
        negative = c == b'-';
        p = p.saturating_add(1);
    }
    let mut int: i64 = 0;
    let mut int_digits = 0usize;
    while let Some(d) = digit(s.get(p)) {
        int = int
            .checked_mul(10)
            .and_then(|v| v.checked_add(i64::from(d)))
            .ok_or(Error::Unsupported("a number out of range"))?;
        if int > MAX_NUMBER {
            return Err(Error::Unsupported("a number out of range"));
        }
        int_digits = int_digits.saturating_add(1);
        p = p.saturating_add(1);
    }
    let mut frac: u64 = 0;
    let mut kept = 0usize;
    if s.get(p) == Some(&b'.') {
        p = p.saturating_add(1);
        let mut frac_digits = 0usize;
        while let Some(d) = digit(s.get(p)) {
            if kept < KEPT {
                frac = frac.saturating_mul(10).saturating_add(u64::from(d));
                kept = kept.saturating_add(1);
            }
            frac_digits = frac_digits.saturating_add(1);
            p = p.saturating_add(1);
        }
        if frac_digits == 0 {
            return Err(Error::Malformed(
                "a number with a point and no digits after it",
            ));
        }
    } else if int_digits == 0 {
        return Err(Error::Malformed("a sign with no number"));
    }
    if matches!(s.get(p), Some(b'e' | b'E')) {
        return Err(Error::Unsupported("an exponent in a number"));
    }
    let frac_fixed = fraction_fixed(frac, kept);
    let magnitude = int
        .checked_mul(ONE)
        .and_then(|v| v.checked_add(i64::try_from(frac_fixed).ok()?))
        .ok_or(Error::Unsupported("a number out of range"))?;
    if magnitude > MAX_NUMBER {
        return Err(Error::Unsupported("a number out of range"));
    }
    let value = if negative {
        magnitude.checked_neg().unwrap_or(0)
    } else {
        magnitude
    };
    Ok(Some((value, p)))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(s: &str) -> Result<Option<(i64, usize)>, Error> {
        number(s.as_bytes(), 0)
    }

    #[test]
    fn values() {
        assert_eq!(n("0"), Ok(Some((0, 1))));
        assert_eq!(n("14"), Ok(Some((14 * 65536, 2))));
        assert_eq!(n("-29"), Ok(Some((-29 * 65536, 3))));
        assert_eq!(n("+.5"), Ok(Some((32768, 3))));
        assert_eq!(n("0.25x"), Ok(Some((16384, 4))));
        // Greedy, as section 9.3.9's examples: "0.6.5" is 0.6 then .5.
        assert_eq!(n("0.6.5"), Ok(Some((39322, 3))));
        assert_eq!(n("100-200"), Ok(Some((100 * 65536, 3))));
        assert_eq!(n("73.2521756"), Ok(Some((4_800_655, 10))));
        assert_eq!(n("x"), Ok(None));
        assert_eq!(n(""), Ok(None));
    }

    #[test]
    fn refusals() {
        assert!(matches!(n("-"), Err(Error::Malformed(_))));
        assert!(matches!(n("+x"), Err(Error::Malformed(_))));
        assert!(matches!(n("."), Err(Error::Malformed(_))));
        assert!(matches!(n("23."), Err(Error::Malformed(_))));
        assert!(matches!(n("1e3"), Err(Error::Unsupported(_))));
        assert!(matches!(n("1048577"), Err(Error::Unsupported(_))));
        assert_eq!(n("1048576"), Ok(Some((1 << 36, 7))));
        assert!(matches!(
            n("99999999999999999999999999"),
            Err(Error::Unsupported(_))
        ));
    }

    #[test]
    fn fractions_round_to_nearest() {
        // 1/65536 = 0.0000152587890625; half of it rounds up.
        assert_eq!(n("0.000007629"), Ok(Some((0, 11))));
        assert_eq!(n("0.00000763"), Ok(Some((1, 10))));
        // Digits past the ninth are read and ignored.
        assert_eq!(n("0.5000000000009"), Ok(Some((32768, 15))));
    }
}
