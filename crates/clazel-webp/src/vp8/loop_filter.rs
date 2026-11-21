//! The loop filter: RFC 6386 section 15. The simple filter (15.2), the
//! normal filter (15.3) with its subblock and macroblock variants, the
//! control parameters (15.4), and the geometry and order of the edges (15.1).
//!
//! The per-segment functions are pure: they take the pixels of one segment
//! straddling an edge, `p3 p2 p1 p0 | q0 q1 q2 q3` (section 15.3: "ordered
//! from the beforemost to the aftermost"), and return them filtered. The
//! driver gathers a segment from a plane, calls one, and writes it back.

use super::header::FrameHeader;
use super::plane::Plane;

/// `c(v)` (section 15.2): clamp to the signed 8-bit range.
fn c(v: i32) -> i32 {
    v.clamp(-128, 127)
}

/// `u2s`: "Convert pixel value (0 <= v <= 255) to an 8-bit signed number."
fn u2s(v: u8) -> i32 {
    i32::from(v).wrapping_sub(128)
}

/// `s2u`: "Clamp, then convert signed number back to pixel value."
fn s2u(v: i32) -> u8 {
    u8::try_from(c(v).wrapping_add(128)).unwrap_or(0)
}

/// `abs` of the difference of two pixels.
fn diff(a: u8, b: u8) -> i32 {
    i32::from(a).wrapping_sub(i32::from(b)).abs()
}

/// One segment: `p3 p2 p1 p0 q0 q1 q2 q3`.
pub(crate) type Segment = [u8; 8];

/// `common_adjust` (section 15.2): the shared adjustment of `p0` and `q0`.
/// Returns the new `p0`, the new `q0`, and the `a` it computed.
fn common_adjust(use_outer_taps: bool, p1: u8, p0: u8, q0: u8, q1: u8) -> (u8, u8, i32) {
    let (p1, p0, q0, q1) = (u2s(p1), u2s(p0), u2s(q0), u2s(q1));
    // "a = c((use_outer_taps ? c(p1 - q1) : 0) + 3*(q0 - p0))"
    let outer = if use_outer_taps {
        c(p1.wrapping_sub(q1))
    } else {
        0
    };
    let a = c(outer.wrapping_add(q0.wrapping_sub(p0).wrapping_mul(3)));
    // "b is used to balance the rounding of a/8"
    let b = c(a.wrapping_add(3)) >> 3;
    let a = c(a.wrapping_add(4)) >> 3;
    (s2u(p0.wrapping_add(b)), s2u(q0.wrapping_sub(a)), a)
}

/// `simple_segment` (section 15.2) on `p1 p0 q0 q1`: "do nothing if edge
/// difference exceeds limit".
pub(crate) fn simple_segment(edge_limit: i32, seg: [u8; 4]) -> [u8; 4] {
    let [p1, p0, q0, q1] = seg;
    if diff(p0, q0).wrapping_mul(2).wrapping_add(diff(p1, q1) / 2) <= edge_limit {
        let (np0, nq0, _) = common_adjust(true, p1, p0, q0, q1);
        [p1, np0, nq0, q1]
    } else {
        seg
    }
}

/// `filter_yes` (section 15.3): the filter is on unless an interior
/// difference exceeds `interior` or the edge difference exceeds `edge`.
fn filter_yes(interior: i32, edge: i32, s: &Segment) -> bool {
    let [p3, p2, p1, p0, q0, q1, q2, q3] = *s;
    diff(p0, q0).wrapping_mul(2).wrapping_add(diff(p1, q1) / 2) <= edge
        && diff(p3, p2) <= interior
        && diff(p2, p1) <= interior
        && diff(p1, p0) <= interior
        && diff(q3, q2) <= interior
        && diff(q2, q1) <= interior
        && diff(q1, q0) <= interior
}

/// `hev` (section 15.3): "high edge variance".
fn hev(threshold: i32, p1: u8, p0: u8, q0: u8, q1: u8) -> bool {
    diff(p1, p0) > threshold || diff(q1, q0) > threshold
}

/// `subblock_filter` (section 15.3).
pub(crate) fn subblock_filter(
    hev_threshold: i32,
    interior_limit: i32,
    edge_limit: i32,
    seg: Segment,
) -> Segment {
    let [p3, p2, p1, p0, q0, q1, q2, q3] = seg;
    if !filter_yes(interior_limit, edge_limit, &seg) {
        return seg;
    }
    let hv = hev(hev_threshold, p1, p0, q0, q1);
    let (np0, nq0, a) = common_adjust(hv, p1, p0, q0, q1);
    let a = a.wrapping_add(1) >> 1;
    let (mut np1, mut nq1) = (p1, q1);
    if !hv {
        nq1 = s2u(u2s(q1).wrapping_sub(a));
        np1 = s2u(u2s(p1).wrapping_add(a));
    }
    [p3, p2, np1, np0, nq0, nq1, q2, q3]
}

/// `MBfilter` (section 15.3), the inter-macroblock filter.
pub(crate) fn mb_filter(
    hev_threshold: i32,
    interior_limit: i32,
    edge_limit: i32,
    seg: Segment,
) -> Segment {
    let [p3, p2, p1, p0, q0, q1, q2, q3] = seg;
    if !filter_yes(interior_limit, edge_limit, &seg) {
        return seg;
    }
    if hev(hev_threshold, p1, p0, q0, q1) {
        // "if hev, do simple filter", "using outer taps"
        let (np0, nq0, _) = common_adjust(true, p1, p0, q0, q1);
        return [p3, p2, p1, np0, nq0, q1, q2, q3];
    }
    let (sp2, sp1, sp0) = (u2s(p2), u2s(p1), u2s(p0));
    let (sq0, sq1, sq2) = (u2s(q0), u2s(q1), u2s(q2));
    // "Same as the initial calculation in common_adjust, w is something like
    // twice the edge difference"
    let w = c(c(sp1.wrapping_sub(sq1)).wrapping_add(sq0.wrapping_sub(sp0).wrapping_mul(3)));
    // 27/128 of w, then 18/128, then 9/128, each rounded
    let adj = |k: i32| c(k.wrapping_mul(w).wrapping_add(63) >> 7);
    let a = adj(27);
    let (nq0, np0) = (s2u(sq0.wrapping_sub(a)), s2u(sp0.wrapping_add(a)));
    let a = adj(18);
    let (nq1, np1) = (s2u(sq1.wrapping_sub(a)), s2u(sp1.wrapping_add(a)));
    let a = adj(9);
    let (nq2, np2) = (s2u(sq2.wrapping_sub(a)), s2u(sp2.wrapping_add(a)));
    [p3, np2, np1, np0, nq0, nq1, nq2, q3]
}

/// The control parameters of one macroblock (section 15.4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Params {
    /// `loop_filter_level` for this macroblock, 0 to 63; 0 means skip it.
    pub(crate) level: i32,
    /// `interior_limit`.
    pub(crate) interior_limit: i32,
    /// `hev_threshold`.
    pub(crate) hev_threshold: i32,
}

/// Section 15.4's derivation, with the level of the macroblock as the
/// reference decoder's `calculate_filter_parameters` (section 20.6) has it
/// for a macroblock of a key frame: the frame's level, replaced or adjusted
/// by the segment's (section 9.3) and clamped, then adjusted by the
/// reference frame delta 0 (intra) and, for `B_PRED`, the mode delta 0
/// (section 9.4) and clamped again.
pub(crate) fn params(h: &FrameHeader, segment: usize, b_pred: bool) -> Params {
    let mut level = h.loop_filter_level;
    if h.segmentation_enabled {
        let seg = h.lf_update_value.get(segment).copied().unwrap_or(0);
        level = if h.segment_feature_mode {
            seg
        } else {
            level.saturating_add(seg)
        };
    }
    level = level.clamp(0, 63);
    if h.loop_filter_adj_enable {
        level = level.saturating_add(h.ref_frame_delta.first().copied().unwrap_or(0));
        if b_pred {
            level = level.saturating_add(h.mb_mode_delta.first().copied().unwrap_or(0));
        }
    }
    level = level.clamp(0, 63);
    // `interior_limit = loop_filter_level; if (sharpness_level) {
    // interior_limit >>= sharpness_level > 4 ? 2 : 1; if (interior_limit >
    // 9 - sharpness_level) interior_limit = 9 - sharpness_level; } if
    // (!interior_limit) interior_limit = 1;`
    let sharp = h.sharpness_level;
    let mut interior = level;
    if sharp != 0 {
        interior >>= if sharp > 4 { 2 } else { 1 };
        interior = interior.min(9i32.wrapping_sub(sharp));
    }
    interior = interior.max(1);
    // The key frame's `hev_threshold`.
    let hev_threshold = if level >= 40 {
        2
    } else {
        i32::from(level >= 15)
    };
    Params {
        level,
        interior_limit: interior,
        hev_threshold,
    }
}

/// Which way an edge runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Edge {
    /// A vertical edge (between columns): its segments are rows.
    Vertical,
    /// A horizontal edge (between rows): its segments are columns.
    Horizontal,
}

/// Applies `f` to each of the `len` segments of the edge at (`x`, `y`):
/// for a vertical edge, the segment of row `y + k` is the pixels at columns
/// `x - 4` to `x + 3`; for a horizontal one, of column `x + k` the pixels at
/// rows `y - 4` to `y + 3`.
fn filter_edge(
    plane: &mut Plane<'_>,
    x: usize,
    y: usize,
    edge: Edge,
    len: usize,
    f: impl Fn(Segment) -> Segment,
) {
    for k in 0..len {
        let at = |i: usize| -> (usize, usize) {
            match edge {
                Edge::Vertical => (x.wrapping_add(i).wrapping_sub(4), y.wrapping_add(k)),
                Edge::Horizontal => (x.wrapping_add(k), y.wrapping_add(i).wrapping_sub(4)),
            }
        };
        let mut seg = [0u8; 8];
        for (i, s) in seg.iter_mut().enumerate() {
            let (px, py) = at(i);
            *s = plane.at(px, py);
        }
        let out = f(seg);
        for (i, &v) in out.iter().enumerate() {
            let (px, py) = at(i);
            plane.set(px, py, v);
        }
    }
}

/// Filters one macroblock's edges in one plane in the order of section
/// 15.1: the left macroblock edge, the vertical subblock edges, the top
/// macroblock edge, the horizontal subblock edges. `size` is 16 (luma) or 8
/// (chroma); the subblock edges are at multiples of 4 inside it.
fn filter_mb_plane(
    plane: &mut Plane<'_>,
    mb_x: usize,
    mb_y: usize,
    size: usize,
    inner: bool,
    simple: bool,
    p: &Params,
) {
    let x0 = mb_x.saturating_mul(size);
    let y0 = mb_y.saturating_mul(size);
    // "mbedge_limit = ((loop_filter_level + 2) * 2) + interior_limit",
    // "sub_bedge_limit = (loop_filter_level * 2) + interior_limit"
    let mb_limit = p
        .level
        .wrapping_add(2)
        .wrapping_mul(2)
        .wrapping_add(p.interior_limit);
    let sub_limit = p.level.wrapping_mul(2).wrapping_add(p.interior_limit);
    let (hev_t, interior) = (p.hev_threshold, p.interior_limit);
    let mb_edge = move |s: Segment| -> Segment {
        if simple {
            let [p3, p2, a, b, c2, d, q2, q3] = s;
            let [na, nb, nc, nd] = simple_segment(mb_limit, [a, b, c2, d]);
            [p3, p2, na, nb, nc, nd, q2, q3]
        } else {
            mb_filter(hev_t, interior, mb_limit, s)
        }
    };
    let sub_edge = move |s: Segment| -> Segment {
        if simple {
            let [p3, p2, a, b, c2, d, q2, q3] = s;
            let [na, nb, nc, nd] = simple_segment(sub_limit, [a, b, c2, d]);
            [p3, p2, na, nb, nc, nd, q2, q3]
        } else {
            subblock_filter(hev_t, interior, sub_limit, s)
        }
    };
    // 1. "If M is not on the leftmost column of macroblocks, filter across
    //    the left (vertical) inter-macroblock edge of M."
    if mb_x > 0 {
        filter_edge(plane, x0, y0, Edge::Vertical, size, mb_edge);
    }
    // 2. "Filter across the vertical subblock edges within M."
    if inner {
        let mut x = 4;
        while x < size {
            filter_edge(
                plane,
                x0.wrapping_add(x),
                y0,
                Edge::Vertical,
                size,
                sub_edge,
            );
            x = x.wrapping_add(4);
        }
    }
    // 3. "If M is not on the topmost row of macroblocks, filter across the
    //    top (horizontal) inter-macroblock edge of M."
    if mb_y > 0 {
        filter_edge(plane, x0, y0, Edge::Horizontal, size, mb_edge);
    }
    // 4. "Filter across the horizontal subblock edges within M."
    if inner {
        let mut y = 4;
        while y < size {
            filter_edge(
                plane,
                x0,
                y0.wrapping_add(y),
                Edge::Horizontal,
                size,
                sub_edge,
            );
            y = y.wrapping_add(4);
        }
    }
}

/// What the loop filter needs to know of a macroblock.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct MbInfo {
    /// The macroblock's segment, 0 to 3.
    pub(crate) segment: u8,
    /// The luma mode is `B_PRED`.
    pub(crate) b_pred: bool,
    /// Section 15.1: the subblock edges are filtered, unless the mode is
    /// neither `B_PRED` nor `SPLITMV` and "there is no DCT coefficient coded
    /// for the whole macroblock".
    pub(crate) inner: bool,
}

/// Filters the macroblock (`mb_x`, `mb_y`) in the three planes, as section
/// 15.1 orders it: skipped "entirely if loop_filter_level at either the frame
/// header level or macroblock override level is 0" (the frame's is checked by
/// the caller). The simple filter "only applies to luma edges".
pub(crate) fn filter_macroblock(
    h: &FrameHeader,
    info: MbInfo,
    mb_x: usize,
    mb_y: usize,
    planes: (&mut Plane<'_>, &mut Plane<'_>, &mut Plane<'_>),
) {
    let p = params(h, usize::from(info.segment), info.b_pred);
    if p.level == 0 {
        return;
    }
    let (y, u, v) = planes;
    filter_mb_plane(y, mb_x, mb_y, 16, info.inner, h.filter_type, &p);
    if !h.filter_type {
        filter_mb_plane(u, mb_x, mb_y, 8, info.inner, false, &p);
        filter_mb_plane(v, mb_x, mb_y, 8, info.inner, false, &p);
    }
}
