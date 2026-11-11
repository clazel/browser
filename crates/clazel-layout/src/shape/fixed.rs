//! Font units to 26.6 positions: the pen's accumulation, clamping and
//! scaling (OpenType 1.9, chapter `head`, `unitsPerEm`; the scaling and its
//! rounding are item 5.10's, [`clazel_font::outline::scale::scale`]).
//!
//! The shaper works in font units, where its results are exact and
//! comparable with other shapers; [`place`] converts a shaped run to 26.6
//! once, rounding each **position**, not each advance, so rounding errors
//! never accumulate along a run (listed in [`super`]'s modelling choices).

use clazel_font::outline::scale::scale;

use super::{PlacedGlyph, PlacedRun, UnitGlyph};

/// `v` clamped into `i32`.
pub fn clamp_i32(v: i64) -> i32 {
    match i32::try_from(v) {
        Ok(x) => x,
        Err(_) if v < 0 => i32::MIN,
        Err(_) => i32::MAX,
    }
}

/// `v` font units at `size` (26.6 pixels per em) and `units_per_em`, in
/// 26.6, rounded half away from zero as 5.10 rounds outline points. A
/// result outside `i32` (about ±33 million pixels) is clamped to it. A
/// negative `size` or a zero `units_per_em` (which `head` refuses, so no
/// face has it) gives 0.
pub fn to_26_6(v: i32, size: i32, units_per_em: u16) -> i32 {
    if size < 0 || units_per_em == 0 {
        return 0;
    }
    match scale(v, size, units_per_em) {
        Ok(x) => x,
        // With `size >= 0` the result has `v`'s sign; the only error left
        // is a result outside `i32`.
        Err(_) if v < 0 => i32::MIN,
        Err(_) => i32::MAX,
    }
}

/// The pen after a glyph of `advance` font units: the sum, kept in `i64`,
/// saturating (it cannot saturate for any run shorter than 2³² glyphs).
pub fn advance_pen(pen: i64, advance: i32) -> i64 {
    pen.saturating_add(i64::from(advance))
}

/// One glyph placed from pen position `pen` (font units from the run's
/// start): its 26.6 origin, offset and advance, and the next pen position.
///
/// The origin is `pen + x_offset` scaled; the advance is the difference of
/// the scaled pen positions after and before the glyph, so the advances of
/// a run sum to its scaled width exactly.
pub fn place_step(pen: i64, g: &UnitGlyph, size: i32, units_per_em: u16) -> (PlacedGlyph, i64) {
    let origin = clamp_i32(pen.saturating_add(i64::from(g.x_offset)));
    let next = advance_pen(pen, g.x_advance);
    let start = to_26_6(clamp_i32(pen), size, units_per_em);
    let end = to_26_6(clamp_i32(next), size, units_per_em);
    let placed = PlacedGlyph {
        glyph: g.glyph,
        cluster: g.cluster,
        x: to_26_6(origin, size, units_per_em),
        y: to_26_6(g.y_offset, size, units_per_em),
        advance: end.saturating_sub(start),
    };
    (placed, next)
}

/// A shaped run in 26.6 at `size` (pixels per em × 64): each glyph's origin
/// relative to the run's start, its vertical offset (y up, as in the font)
/// and advance, and the run's width.
pub fn place(glyphs: &[UnitGlyph], size: i32, units_per_em: u16) -> PlacedRun {
    let mut pen = 0i64;
    let mut out = Vec::with_capacity(glyphs.len());
    for g in glyphs {
        let (placed, next) = place_step(pen, g, size, units_per_em);
        out.push(placed);
        pen = next;
    }
    PlacedRun {
        glyphs: out,
        advance: to_26_6(clamp_i32(pen), size, units_per_em),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn g(x_advance: i32, x_offset: i32) -> UnitGlyph {
        UnitGlyph {
            glyph: 1,
            cluster: 0,
            mark: false,
            x_advance,
            x_offset,
            y_offset: 0,
        }
    }

    #[test]
    fn positions_round_once() {
        // 2048 units per em at 16 px (1024): one unit is half a 26.6 unit.
        // Three advances of 3 units are 1.5 each; rounding each would give
        // 2 + 2 + 2 = 6, rounding positions gives 2, 3, 5: width 5 (4.5
        // rounded away from zero), with advances 2, 1, 2.
        let run = place(&[g(3, 0), g(3, 0), g(3, 0)], 1024, 2048);
        let xs: Vec<i32> = run.glyphs.iter().map(|p| p.x).collect();
        let advances: Vec<i32> = run.glyphs.iter().map(|p| p.advance).collect();
        assert_eq!(xs, [0, 2, 3]);
        assert_eq!(advances, [2, 1, 2]);
        assert_eq!(run.advance, 5);
        assert_eq!(advances.iter().sum::<i32>(), run.advance);
    }

    #[test]
    fn offsets_move_the_origin_not_the_pen() {
        let run = place(&[g(1000, 0), g(500, -100)], 1024, 1000);
        assert_eq!(run.glyphs.get(1).map(|p| p.x), Some(922)); // 900 units
        assert_eq!(run.advance, 1536);
    }

    #[test]
    fn clamps() {
        assert_eq!(to_26_6(i32::MAX, i32::MAX, 1), i32::MAX);
        assert_eq!(to_26_6(i32::MIN, i32::MAX, 1), i32::MIN);
        assert_eq!(to_26_6(100, -1, 1000), 0);
        assert_eq!(to_26_6(100, 1024, 0), 0);
        assert_eq!(clamp_i32(i64::MAX), i32::MAX);
        assert_eq!(clamp_i32(i64::MIN), i32::MIN);
        let run = place(&[g(i32::MAX, 0), g(i32::MAX, i32::MAX)], 64, 1);
        assert_eq!(run.advance, i32::MAX);
        assert_eq!(advance_pen(i64::MAX, 1), i64::MAX);
    }
}
