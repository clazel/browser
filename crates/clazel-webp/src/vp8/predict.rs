//! Intra prediction: RFC 6386 section 12. Chroma prediction (12.2), the
//! four whole-macroblock luma modes (12.3: "essentially identical to the
//! corresponding chroma prediction processes"), and the ten subblock modes
//! (12.3's `subblock_intra_predict`).
//!
//! The pixels outside the frame are the values of section 12 (see
//! `plane.rs`); the pixels used are those already reconstructed and not yet
//! loop-filtered, because the whole frame is reconstructed before any of it
//! is filtered (section 15.1: "a macroblock must not be filtered immediately
//! after its reconstruction").

use super::plane::{Plane, coord};
use super::tables::{
    B_DC_PRED, B_HD_PRED, B_HE_PRED, B_HU_PRED, B_LD_PRED, B_RD_PRED, B_TM_PRED, B_VE_PRED,
    B_VL_PRED, B_VR_PRED, DC_PRED, H_PRED, TM_PRED, V_PRED,
};

/// `avg3` (section 12.3): "weighted average centered at y w/adjacent x, z".
fn avg3(x: u8, y: u8, z: u8) -> u8 {
    let s = u32::from(x)
        .wrapping_add(u32::from(y))
        .wrapping_add(u32::from(y))
        .wrapping_add(u32::from(z))
        .wrapping_add(2);
    (s >> 2) as u8
}

/// `avg2`: "simple average of x and y".
fn avg2(x: u8, y: u8) -> u8 {
    let s = u32::from(x).wrapping_add(u32::from(y)).wrapping_add(1);
    (s >> 1) as u8
}

/// The whole-block modes of sections 12.2 and 12.3 for a block of `size`
/// pixels (16 for luma, 8 for chroma) whose top left pixel is (`x0`, `y0`)
/// in `plane`: DC_PRED, V_PRED, H_PRED, TM_PRED. `have_top` and `have_left`
/// say whether the macroblock has one above and to the left (for DC_PRED,
/// whose average then leaves out what is not there).
pub(crate) fn predict_block(
    plane: &mut Plane<'_>,
    x0: usize,
    y0: usize,
    size: usize,
    mode: u8,
    have_top: bool,
    have_left: bool,
) {
    let (cx, cy) = (coord(x0), coord(y0));
    // "A", the row above; "L", the column to the left; "P", above and left.
    let mut above = [0u8; 16];
    let mut left = [0u8; 16];
    for (i, (a, l)) in above.iter_mut().zip(left.iter_mut()).take(size).enumerate() {
        *a = plane.get(cx.saturating_add(coord(i)), cy.saturating_sub(1));
        *l = plane.get(cx.saturating_sub(1), cy.saturating_add(coord(i)));
    }
    let p = plane.get(cx.saturating_sub(1), cy.saturating_sub(1));
    let a_at = |i: usize| i32::from(above.get(i).copied().unwrap_or(0));
    let l_at = |i: usize| i32::from(left.get(i).copied().unwrap_or(0));
    let dc = {
        // shf is the base 2 logarithm of the number of pixels averaged
        let log2 = if size == 16 { 4u32 } else { 3 };
        let sum_a: i32 = (0..size).map(a_at).sum();
        let sum_l: i32 = (0..size).map(l_at).sum();
        let (sum, shf) = match (have_top, have_left) {
            (true, true) => (sum_a.wrapping_add(sum_l), log2.wrapping_add(1)),
            (true, false) => (sum_a, log2),
            (false, true) => (sum_l, log2),
            // "the 8x8 block is simply filled with the constant value 128"
            (false, false) => (128, 0),
        };
        if shf == 0 {
            128
        } else {
            // `DCvalue = (sum + (1 << (shf-1))) >> shf`
            sum.wrapping_add(1 << shf.wrapping_sub(1)) >> shf
        }
    };
    for r in 0..size {
        for c in 0..size {
            let v = match mode {
                DC_PRED => dc,
                V_PRED => a_at(c),
                H_PRED => l_at(r),
                // `clamp255(L[r] + A[c] - P)`
                TM_PRED => l_at(r)
                    .wrapping_add(a_at(c))
                    .wrapping_sub(i32::from(p))
                    .clamp(0, 255),
                _ => 128,
            };
            plane.set(
                x0.saturating_add(c),
                y0.saturating_add(r),
                u8::try_from(v.clamp(0, 255)).unwrap_or(0),
            );
        }
    }
}

/// The edge of a subblock (section 12.3): `A[0]` to `A[7]` the row above and
/// the four pixels above and to the right of it, `L[0]` to `L[3]` the column
/// to the left, and `P` the pixel above `L` and left of `A`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct SubEdge {
    /// `A[0]` to `A[7]`.
    pub(crate) a: [u8; 8],
    /// `L[0]` to `L[3]`.
    pub(crate) l: [u8; 4],
    /// `P`, which is `A[-1]` and `L[-1]`.
    pub(crate) p: u8,
}

/// Sets each of `cells` (row, column) of the 4 by 4 block `b` to `v`.
fn put(b: &mut [u8; 16], cells: &[(usize, usize)], v: u8) {
    for &(r, c) in cells {
        if let Some(slot) = b.get_mut(r.wrapping_mul(4).wrapping_add(c)) {
            *slot = v;
        }
    }
}

/// `subblock_intra_predict` (section 12.3): the 16 predicted pixels, in
/// raster order, of a subblock coded with `mode` (an `intra_bmode`; a value
/// past `B_HU_PRED` predicts like `B_DC_PRED`, not a case here).
pub(crate) fn predict_subblock(mode: u8, e: &SubEdge) -> [u8; 16] {
    let mut b = [0u8; 16];
    // `E[0]` to `E[8]`: "9 already-constructed edge pixels", from the
    // bottom of L up through P and along A.
    let [l0, l1, l2, l3] = e.l;
    let [a0, a1, a2, a3, a4, a5, a6, a7] = e.a;
    let p = e.p;
    let ee = [l3, l2, l1, l0, p, a0, a1, a2, a3];
    // `avg3p(E + k)` and `avg2p(E + k)`.
    let e3 = |k: usize| {
        let g = |i: usize| ee.get(i).copied().unwrap_or(0);
        avg3(g(k.wrapping_sub(1)), g(k), g(k.wrapping_add(1)))
    };
    let e2 = |k: usize| {
        let g = |i: usize| ee.get(i).copied().unwrap_or(0);
        avg2(g(k), g(k.wrapping_add(1)))
    };
    // A with `A[-1] = P`, for `avg3p(A + k)` and `avg2p(A + k)`.
    let aa = [p, a0, a1, a2, a3, a4, a5, a6, a7];
    let a3p = |k: usize| {
        let g = |i: usize| aa.get(i).copied().unwrap_or(0);
        // A[k - 1], A[k], A[k + 1] are aa[k], aa[k + 1], aa[k + 2]
        avg3(g(k), g(k.wrapping_add(1)), g(k.wrapping_add(2)))
    };
    let a2p = |k: usize| {
        let g = |i: usize| aa.get(i).copied().unwrap_or(0);
        avg2(g(k.wrapping_add(1)), g(k.wrapping_add(2)))
    };
    // L with `L[-1] = P`.
    let ll = [p, l0, l1, l2, l3];
    let l3p = |k: usize| {
        let g = |i: usize| ll.get(i).copied().unwrap_or(0);
        avg3(g(k), g(k.wrapping_add(1)), g(k.wrapping_add(2)))
    };
    let l2p = |k: usize| {
        let g = |i: usize| ll.get(i).copied().unwrap_or(0);
        avg2(g(k.wrapping_add(1)), g(k.wrapping_add(2)))
    };
    match mode {
        B_TM_PRED => {
            // `clamp255(L[r] + A[c] - A[-1])`
            for r in 0..4usize {
                for c in 0..4usize {
                    let lv = i32::from(e.l.get(r).copied().unwrap_or(0));
                    let av = i32::from(e.a.get(c).copied().unwrap_or(0));
                    let v = lv.wrapping_add(av).wrapping_sub(i32::from(p)).clamp(0, 255);
                    put(&mut b, &[(r, c)], u8::try_from(v).unwrap_or(0));
                }
            }
        }
        B_VE_PRED => {
            // "all 4 rows = smoothed top row": `avg3p(A + c)`
            for c in 0..4usize {
                put(&mut b, &[(0, c), (1, c), (2, c), (3, c)], a3p(c));
            }
        }
        B_HE_PRED => {
            // "Bottom row is exceptional because L[4] does not exist"; the
            // rows above use `avg3p(L + r)`.
            put(&mut b, &[(3, 0), (3, 1), (3, 2), (3, 3)], avg3(l2, l3, l3));
            for r in 0..3usize {
                put(&mut b, &[(r, 0), (r, 1), (r, 2), (r, 3)], l3p(r));
            }
        }
        B_LD_PRED => {
            put(&mut b, &[(0, 0)], a3p(1));
            put(&mut b, &[(0, 1), (1, 0)], a3p(2));
            put(&mut b, &[(0, 2), (1, 1), (2, 0)], a3p(3));
            put(&mut b, &[(0, 3), (1, 2), (2, 1), (3, 0)], a3p(4));
            put(&mut b, &[(1, 3), (2, 2), (3, 1)], a3p(5));
            put(&mut b, &[(2, 3), (3, 2)], a3p(6));
            // "A[8] does not exist"
            put(&mut b, &[(3, 3)], avg3(a6, a7, a7));
        }
        B_RD_PRED => {
            put(&mut b, &[(3, 0)], e3(1));
            put(&mut b, &[(3, 1), (2, 0)], e3(2));
            put(&mut b, &[(3, 2), (2, 1), (1, 0)], e3(3));
            put(&mut b, &[(3, 3), (2, 2), (1, 1), (0, 0)], e3(4));
            put(&mut b, &[(2, 3), (1, 2), (0, 1)], e3(5));
            put(&mut b, &[(1, 3), (0, 2)], e3(6));
            put(&mut b, &[(0, 3)], e3(7));
        }
        B_VR_PRED => {
            put(&mut b, &[(3, 0)], e3(2));
            put(&mut b, &[(2, 0)], e3(3));
            put(&mut b, &[(3, 1), (1, 0)], e3(4));
            put(&mut b, &[(2, 1), (0, 0)], e2(4));
            put(&mut b, &[(3, 2), (1, 1)], e3(5));
            put(&mut b, &[(2, 2), (0, 1)], e2(5));
            put(&mut b, &[(3, 3), (1, 2)], e3(6));
            put(&mut b, &[(2, 3), (0, 2)], e2(6));
            put(&mut b, &[(1, 3)], e3(7));
            put(&mut b, &[(0, 3)], e2(7));
        }
        B_VL_PRED => {
            put(&mut b, &[(0, 0)], a2p(0));
            put(&mut b, &[(1, 0)], a3p(1));
            put(&mut b, &[(2, 0), (0, 1)], a2p(1));
            put(&mut b, &[(1, 1), (3, 0)], a3p(2));
            put(&mut b, &[(2, 1), (0, 2)], a2p(2));
            put(&mut b, &[(3, 1), (1, 2)], a3p(3));
            put(&mut b, &[(2, 2), (0, 3)], a2p(3));
            put(&mut b, &[(3, 2), (1, 3)], a3p(4));
            // "Last two values do not strictly follow the pattern."
            put(&mut b, &[(2, 3)], a3p(5));
            put(&mut b, &[(3, 3)], a3p(6));
        }
        B_HD_PRED => {
            put(&mut b, &[(3, 0)], e2(0));
            put(&mut b, &[(3, 1)], e3(1));
            put(&mut b, &[(2, 0), (3, 2)], e2(1));
            put(&mut b, &[(2, 1), (3, 3)], e3(2));
            put(&mut b, &[(2, 2), (1, 0)], e2(2));
            put(&mut b, &[(2, 3), (1, 1)], e3(3));
            put(&mut b, &[(1, 2), (0, 0)], e2(3));
            put(&mut b, &[(1, 3), (0, 1)], e3(4));
            put(&mut b, &[(0, 2)], e3(5));
            put(&mut b, &[(0, 3)], e3(6));
        }
        B_HU_PRED => {
            put(&mut b, &[(0, 0)], l2p(0));
            put(&mut b, &[(0, 1)], l3p(1));
            put(&mut b, &[(0, 2), (1, 0)], l2p(1));
            put(&mut b, &[(0, 3), (1, 1)], l3p(2));
            put(&mut b, &[(1, 2), (2, 0)], l2p(2));
            put(&mut b, &[(1, 3), (2, 1)], avg3(l2, l3, l3));
            // "Not possible to follow pattern for much of the bottom row"
            put(
                &mut b,
                &[(2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3)],
                l3,
            );
        }
        // B_DC_PRED (and, never reached, a value past the modes)
        _ => {
            let _ = B_DC_PRED;
            let sum: u32 =
                e.a.iter()
                    .take(4)
                    .chain(e.l.iter())
                    .map(|&v| u32::from(v))
                    .sum();
            // `v = 4; v += A[i] + L[i]; v >>= 3`
            let v = (sum.wrapping_add(4) >> 3) as u8;
            b = [v; 16];
        }
    }
    b
}

/// The four pixels above and to the right of a macroblock, which every
/// right-edge subblock (3, 7, 11, 15) uses as its `A[4]` to `A[7]` (section
/// 12.3: "the extra pixels for all the right-edge subblocks (3, 7, 11, and
/// 15) are at positions (-1,16), (-1,17), (-1,18), and (-1,19)"): for the top
/// macroblock row 127 ("all the extra pixels assume a value of 127"); for the
/// rightmost macroblock of the other rows "the same value as the pixel at
/// position (-1,15)"; otherwise the bottom row of the macroblock above and to
/// the right.
pub(crate) fn mb_above_right(
    luma: &Plane<'_>,
    mb_x: usize,
    mb_y: usize,
    mb_cols: usize,
) -> [u8; 4] {
    if mb_y == 0 {
        return [127; 4];
    }
    let row = coord(mb_y.saturating_mul(16)).saturating_sub(1);
    let x15 = coord(mb_x.saturating_mul(16)).saturating_add(15);
    if mb_x.saturating_add(1) >= mb_cols {
        return [luma.get(x15, row); 4];
    }
    let mut out = [0u8; 4];
    for (i, o) in out.iter_mut().enumerate() {
        *o = luma.get(x15.saturating_add(1).saturating_add(coord(i)), row);
    }
    out
}

/// The edge of the subblock at (`x0`, `y0`) of `luma`: `above_right` supplies
/// `A[4]` to `A[7]` (the caller's rule: [`mb_above_right`] for a subblock in
/// the right column of its macroblock, the plane's own pixels otherwise).
pub(crate) fn subblock_edge(
    luma: &Plane<'_>,
    x0: usize,
    y0: usize,
    above_right: [u8; 4],
) -> SubEdge {
    let (cx, cy) = (coord(x0), coord(y0));
    let mut a = [0u8; 8];
    for (i, slot) in a.iter_mut().enumerate() {
        *slot = match i.checked_sub(4) {
            None => luma.get(cx.saturating_add(coord(i)), cy.saturating_sub(1)),
            Some(k) => above_right.get(k).copied().unwrap_or(0),
        };
    }
    let mut l = [0u8; 4];
    for (i, slot) in l.iter_mut().enumerate() {
        *slot = luma.get(cx.saturating_sub(1), cy.saturating_add(coord(i)));
    }
    SubEdge {
        a,
        l,
        p: luma.get(cx.saturating_sub(1), cy.saturating_sub(1)),
    }
}
