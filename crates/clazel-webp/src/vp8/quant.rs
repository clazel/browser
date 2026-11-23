//! Dequantization factors: RFC 6386 section 9.6 (the indices), section 9.3
//! (their per-segment override) and section 14.1 (the tables and the scaling
//! of the Y2 and chroma factors), as the reference decoder's `dequant_init`
//! (section 20.4) computes them.

use super::header::{FrameHeader, MAX_SEGMENTS};
use super::tables::{AC_QLOOKUP, DC_QLOOKUP};

/// The six factors of one segment (section 9.6: "six dequantization
/// factors"): each is `[DC factor, AC factor]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Dequant {
    /// Y blocks (`TOKEN_BLOCK_Y1`).
    pub(crate) y1: [i32; 2],
    /// The Y2 block (`TOKEN_BLOCK_Y2`).
    pub(crate) y2: [i32; 2],
    /// U and V blocks (`TOKEN_BLOCK_UV`).
    pub(crate) uv: [i32; 2],
}

/// `clamp_q`: an index into the tables, 0 to 127.
fn clamp_q(q: i32) -> usize {
    usize::try_from(q.clamp(0, 127)).unwrap_or(0)
}

/// `dc_q`: `dc_qlookup` at the clamped index.
fn dc_q(q: i32) -> i32 {
    DC_QLOOKUP.get(clamp_q(q)).copied().unwrap_or(4)
}

/// `ac_q`: `ac_qlookup` at the clamped index.
fn ac_q(q: i32) -> i32 {
    AC_QLOOKUP.get(clamp_q(q)).copied().unwrap_or(4)
}

/// The factors for base index `q` (the segment's, if segmentation changes
/// it) with the frame's deltas: `dequant_init`'s body.
pub(crate) fn factors(q: i32, h: &FrameHeader) -> Dequant {
    // "Y2 DC: dc_q(q + y2dc_delta) * 2"; "Y2 AC: ac_q(q + y2ac_delta) * 155 /
    // 100, at least 8"; "chroma DC: at most 132".
    let y2_ac = ac_q(q.saturating_add(h.y2_ac_delta))
        .saturating_mul(155)
        .checked_div(100)
        .unwrap_or(8)
        .max(8);
    Dequant {
        y1: [dc_q(q.saturating_add(h.y_dc_delta)), ac_q(q)],
        y2: [
            dc_q(q.saturating_add(h.y2_dc_delta)).saturating_mul(2),
            y2_ac,
        ],
        uv: [
            dc_q(q.saturating_add(h.uv_dc_delta)).min(132),
            ac_q(q.saturating_add(h.uv_ac_delta)),
        ],
    }
}

/// The factors of every segment (one if segmentation is off), with section
/// 9.3's override: in absolute mode the segment's value is the index, in
/// delta mode it is added to the frame's `y_ac_qi`.
pub(crate) fn segment_factors(h: &FrameHeader) -> [Dequant; MAX_SEGMENTS] {
    let mut out = [factors(h.y_ac_qi, h); MAX_SEGMENTS];
    if h.segmentation_enabled {
        for (slot, &update) in out.iter_mut().zip(&h.quantizer_update_value) {
            let q = if h.segment_feature_mode {
                update
            } else {
                h.y_ac_qi.saturating_add(update)
            };
            *slot = factors(q, h);
        }
    }
    out
}
