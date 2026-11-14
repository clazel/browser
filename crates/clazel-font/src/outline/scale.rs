//! Font units to 26.6 fixed-point pixels, and implied midpoints.
//!
//! OpenType 1.9, chapter `head`, `unitsPerEm`: the number of font units in
//! one em; a size in pixels per em therefore scales a coordinate `v` to
//! `v × size ÷ unitsPerEm` pixels. Both choices below are listed in
//! [`super`]'s modelling choices.

use crate::Error;

/// `v × size ÷ units_per_em`, rounded half away from zero, where `v` is in
/// font units and `size` and the result are in 26.6 (1/64 px).
///
/// Exact: `|v × size|` < 2⁶² fits `u64` with room for the doubling below.
/// A negative `size` is [`Error::FontSize`]; a `units_per_em` of 0 (which
/// `head` refuses, so a face never has it) or a result outside `i32` is
/// [`Error::Overflow`].
pub fn scale(v: i32, size: i32, units_per_em: u16) -> Result<i32, Error> {
    if size < 0 {
        return Err(Error::FontSize);
    }
    let n = i64::from(v)
        .checked_mul(i64::from(size))
        .ok_or(Error::Overflow)?;
    let upem = u64::from(units_per_em);
    // round(|n| / upem) = floor((2|n| + upem) / (2 upem)), half away from
    // zero once the sign is put back.
    let twice = n.unsigned_abs().checked_mul(2).ok_or(Error::Overflow)?;
    let magnitude = twice
        .checked_add(upem)
        .ok_or(Error::Overflow)?
        .checked_div(upem.checked_mul(2).ok_or(Error::Overflow)?)
        .ok_or(Error::Overflow)?;
    let magnitude = i64::try_from(magnitude).map_err(|_| Error::Overflow)?;
    let signed = if n < 0 {
        magnitude.checked_neg().ok_or(Error::Overflow)?
    } else {
        magnitude
    };
    i32::try_from(signed).map_err(|_| Error::Overflow)
}

/// The implied on-curve point between two coordinates: the floor of their
/// mean. It lies between them, so it is always an `i32`.
pub fn midpoint(a: i32, b: i32) -> i32 {
    let sum = i64::from(a).saturating_add(i64::from(b));
    // `sum.div_euclid(2)` is in a..=b; the conversion never fails.
    let half = sum.checked_div_euclid(2).unwrap_or(0);
    i32::try_from(half).unwrap_or(a)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scale_rounds_half_away_from_zero() -> Result<(), Error> {
        // 2048 units per em at 16 px (1024): half a 26.6 unit per font unit.
        assert_eq!(scale(1, 1024, 2048)?, 1);
        assert_eq!(scale(-1, 1024, 2048)?, -1);
        assert_eq!(scale(2, 1024, 2048)?, 1);
        assert_eq!(scale(3, 1024, 2048)?, 2);
        assert_eq!(scale(-3, 1024, 2048)?, -2);
        assert_eq!(scale(2048, 1024, 2048)?, 1024);
        // 1000 units per em at 12 px (768): 1 unit is 0.768.
        assert_eq!(scale(1, 768, 1000)?, 1);
        assert_eq!(scale(-651, 768, 1000)?, -500);
        assert_eq!(scale(0, i32::MAX, 16)?, 0);
        assert_eq!(scale(i32::MIN, 16, 16)?, i32::MIN);
        assert_eq!(scale(i32::MIN, 17, 16), Err(Error::Overflow));
        assert_eq!(scale(1, -1, 16), Err(Error::FontSize));
        assert_eq!(scale(1, 1, 0), Err(Error::Overflow));
        Ok(())
    }

    #[test]
    fn midpoint_floors() {
        assert_eq!(midpoint(0, 3), 1);
        assert_eq!(midpoint(-3, 0), -2);
        assert_eq!(midpoint(i32::MAX, i32::MAX), i32::MAX);
        assert_eq!(midpoint(i32::MIN, i32::MIN), i32::MIN);
        assert_eq!(midpoint(i32::MIN, i32::MAX), -1);
    }
}
