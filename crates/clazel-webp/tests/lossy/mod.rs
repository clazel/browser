//! Lossy WebP streams made by hand (item 6.9): a VP8 key frame **writer**
//! (a boolean encoder from RFC 6386 section 7.3's encoder code block, the
//! frame header of section 19.2, the macroblock records of section 19.3 and
//! the tokens of section 13, none of it shared with the decoder but the
//! constant tables, below) makes frames that use every prediction mode, every
//! feature of the header (segments in both modes, the simple and normal
//! filters, sharpness, filter deltas, one to eight token partitions, skipped
//! macroblocks, token probability updates, quantizer deltas) and every kind of
//! token, at sizes that are and are not multiples of 16. Each is decoded by
//! `clazel-webp` and by `image-webp`, and the two must agree on every pixel.
//!
//! **The tables** (`src/vp8/tables.rs`, extracted from the RFC's text by a
//! script) are included from the source, not re-typed: a table that was wrong
//! would be wrong in the writer too, so the tables' evidence is the 14 real
//! `cwebp` files that `image-webp` and this decoder read alike.
//!
//! Coefficient magnitudes are kept so that every dequantized value is at most
//! 1,000: the RFC stores them in 16 bits, and `image-webp` computes in 32, so
//! the two differ for values that overflow 16 bits, which no encoder writes.
//!
//! The workspace lints apply to tests (no indexing, no unchecked arithmetic),
//! so the writer uses the small helpers below.
//!
//! Under Miri (25,000 to 30,000 times slower than a native debug run) each
//! test makes one frame of at most 20 by 20 pixels.

mod alpha;
#[path = "../../src/vp8/tables.rs"]
mod tables;

use crate::common::{Rng, decode, reference};
use tables::{
    AC_QLOOKUP, B_DC_PRED, B_HD_PRED, B_HE_PRED, B_HU_PRED, B_LD_PRED, B_PRED, B_RD_PRED,
    B_TM_PRED, B_VE_PRED, B_VL_PRED, B_VR_PRED, BMODE_TREE, CATEGORY_BASE, COEFF_BANDS, COEFF_TREE,
    COEFF_UPDATE_PROBS, DC_PRED, DC_QLOOKUP, DCT_EOB, DEFAULT_COEFF_PROBS, H_PRED, KF_BMODE_PROB,
    KF_UV_MODE_PROB, KF_YMODE_PROB, KF_YMODE_TREE, MB_SEGMENT_TREE, PCAT, TM_PRED, UV_MODE_TREE,
    V_PRED, ZIGZAG,
};

const ALL_BMODES: [u8; 10] = [
    B_DC_PRED, B_TM_PRED, B_VE_PRED, B_HE_PRED, B_LD_PRED, B_RD_PRED, B_VR_PRED, B_VL_PRED,
    B_HD_PRED, B_HU_PRED,
];
const ALL_YMODES: [u8; 5] = [DC_PRED, V_PRED, H_PRED, TM_PRED, B_PRED];

/// Section 7.3's `bool_encoder`.
pub struct Enc {
    out: Vec<u8>,
    range: u32,
    bottom: u32,
    bit_count: i32,
}

impl Enc {
    pub fn new() -> Enc {
        Enc {
            out: Vec::new(),
            range: 255,
            bottom: 0,
            bit_count: 24,
        }
    }

    /// `add_one_to_output`.
    fn carry(&mut self) {
        for b in self.out.iter_mut().rev() {
            if *b == 255 {
                *b = 0;
            } else {
                *b = b.wrapping_add(1);
                break;
            }
        }
    }

    /// `write_bool`.
    pub fn put(&mut self, prob: u8, bit: bool) {
        let split =
            1u32.wrapping_add(self.range.wrapping_sub(1).wrapping_mul(u32::from(prob)) >> 8);
        if bit {
            self.bottom = self.bottom.wrapping_add(split);
            self.range = self.range.wrapping_sub(split);
        } else {
            self.range = split;
        }
        while self.range < 128 {
            self.range <<= 1;
            if self.bottom & (1 << 31) != 0 {
                self.carry();
            }
            self.bottom <<= 1;
            self.bit_count = self.bit_count.wrapping_sub(1);
            if self.bit_count == 0 {
                self.out.push((self.bottom >> 24) as u8);
                self.bottom &= (1 << 24) - 1;
                self.bit_count = 8;
            }
        }
    }

    /// `flush_bool_encoder`.
    pub fn finish(mut self) -> Vec<u8> {
        let c = u32::try_from(self.bit_count).unwrap_or(0);
        let mut v = self.bottom;
        if v & 1u32.checked_shl(32u32.wrapping_sub(c)).unwrap_or(0) != 0 {
            self.carry();
        }
        v <<= c & 7;
        for _ in 0..(c >> 3) {
            v <<= 8;
        }
        for _ in 0..4 {
            self.out.push((v >> 24) as u8);
            v <<= 8;
        }
        self.out
    }

    /// `L(1)`.
    fn flag(&mut self, b: bool) {
        self.put(128, b);
    }

    /// `L(n)`: `n` bits, high first.
    fn literal(&mut self, n: u32, v: u32) {
        for i in (0..n).rev() {
            self.flag((v >> i) & 1 == 1);
        }
    }

    /// A flag, then if set `L(n)` and a sign: the header's optional signed
    /// value.
    fn maybe_signed(&mut self, n: u32, v: Option<i32>) {
        match v {
            None => self.flag(false),
            Some(v) => {
                self.flag(true);
                self.literal(n, v.unsigned_abs());
                self.flag(v < 0);
            }
        }
    }

    /// A tree-coded value (section 8.1) entered at node `start`: the bits that
    /// lead to leaf `leaf`, each with its node's probability.
    fn tree(&mut self, tree: &[i8], probs: &[u8], start: usize, leaf: usize) {
        fn path(tree: &[i8], node: usize, leaf: usize, out: &mut Vec<(usize, bool)>) -> bool {
            for bit in [false, true] {
                let t = tree
                    .get(node.wrapping_add(usize::from(bit)))
                    .copied()
                    .unwrap_or(0);
                out.push((node, bit));
                if t > 0 {
                    if path(tree, usize::try_from(t).unwrap_or(0), leaf, out) {
                        return true;
                    }
                } else if usize::from(t.unsigned_abs()) == leaf {
                    return true;
                }
                out.pop();
            }
            false
        }
        let mut steps = Vec::new();
        assert!(
            path(tree, start, leaf, &mut steps),
            "leaf {leaf} not in tree"
        );
        for (node, bit) in steps {
            self.put(probs.get(node >> 1).copied().unwrap_or(128), bit);
        }
    }
}

/// Absolute mode, quantizer values, loop filter values.
pub type SegData = (bool, [Option<i32>; 4], [Option<i32>; 4]);

/// Reference-frame and mode deltas.
pub type LfDeltas = ([Option<i32>; 4], [Option<i32>; 4]);

/// The segmentation part of a frame header (section 9.3).
#[derive(Clone, Debug)]
pub struct Seg {
    pub update_map: bool,
    /// `(absolute mode, quantizer values, loop filter values)` if the data is
    /// updated.
    pub data: Option<SegData>,
    pub probs: [Option<u8>; 3],
}

/// The loop filter adjustments (section 9.4).
#[derive(Clone, Debug)]
pub struct LfAdj {
    pub update: Option<LfDeltas>,
}

/// Everything about a frame the writer is told; the rest it draws.
#[derive(Clone, Debug)]
pub struct Frame {
    pub width: u32,
    pub height: u32,
    pub log2_parts: u32,
    pub seg: Option<Seg>,
    pub simple: bool,
    pub level: u32,
    pub sharpness: u32,
    pub lf_adj: Option<LfAdj>,
    pub y_ac_qi: u32,
    /// `y_dc`, `y2_dc`, `y2_ac`, `uv_dc`, `uv_ac`.
    pub deltas: [Option<i32>; 5],
    pub skip_prob: Option<u8>,
    /// How many of 256 token probabilities are updated.
    pub updates: u32,
    /// Percent of macroblocks that are `B_PRED`, and of blocks that are empty.
    pub b_pred_percent: usize,
    pub empty_percent: usize,
    /// Blocks written as only `DCT_0` tokens, to the end, no `dct_eob`.
    pub zero_run_percent: usize,
    pub color_space: bool,
    pub clamp: bool,
}

/// A frame drawn from `rng`.
pub fn random_frame(rng: &mut Rng, width: u32, height: u32) -> Frame {
    let pick = |rng: &mut Rng, n: usize| u32::try_from(rng.below(n)).unwrap_or(0);
    let opt = |rng: &mut Rng, lo: i32, hi: i32| -> Option<i32> {
        if rng.below(3) == 0 {
            None
        } else {
            let span = usize::try_from(hi.wrapping_sub(lo).wrapping_add(1)).unwrap_or(1);
            Some(lo.wrapping_add(i32::try_from(rng.below(span)).unwrap_or(0)))
        }
    };
    let seg = (rng.below(2) == 0).then(|| {
        let absolute = rng.below(2) == 0;
        let q = |rng: &mut Rng| -> [Option<i32>; 4] {
            core::array::from_fn(|_| {
                if absolute {
                    opt(rng, 0, 127)
                } else {
                    opt(rng, -40, 40)
                }
            })
        };
        let lf = |rng: &mut Rng| -> [Option<i32>; 4] {
            core::array::from_fn(|_| {
                if absolute {
                    opt(rng, 0, 63)
                } else {
                    opt(rng, -30, 30)
                }
            })
        };
        Seg {
            update_map: rng.below(4) != 0,
            data: (rng.below(4) != 0).then(|| (absolute, q(rng), lf(rng))),
            probs: core::array::from_fn(|_| {
                (rng.below(2) == 0)
                    .then(|| u8::try_from(rng.below(255).wrapping_add(1)).unwrap_or(1))
            }),
        }
    });
    let lf_adj = (rng.below(2) == 0).then(|| LfAdj {
        update: (rng.below(3) != 0).then(|| {
            (
                core::array::from_fn(|_| opt(rng, -20, 20)),
                core::array::from_fn(|_| opt(rng, -20, 20)),
            )
        }),
    });
    Frame {
        width,
        height,
        log2_parts: pick(rng, 4),
        seg,
        simple: rng.below(3) == 0,
        level: match rng.below(4) {
            0 => 0,
            _ => pick(rng, 64),
        },
        sharpness: pick(rng, 8),
        lf_adj,
        y_ac_qi: pick(rng, 128),
        deltas: core::array::from_fn(|_| opt(rng, -15, 15)),
        skip_prob: (rng.below(2) == 0)
            .then(|| u8::try_from(rng.below(255).wrapping_add(1)).unwrap_or(1)),
        updates: pick(rng, 40),
        b_pred_percent: rng.below(100),
        empty_percent: rng.below(90),
        zero_run_percent: rng.below(10),
        color_space: false,
        clamp: rng.below(2) == 0,
    }
}

/// `dc_q` and `ac_q` of section 20.4 (the index clamped).
fn dc_q(q: i32) -> i32 {
    let i = usize::try_from(q.clamp(0, 127)).unwrap_or(0);
    DC_QLOOKUP.get(i).copied().unwrap_or(4)
}
fn ac_q(q: i32) -> i32 {
    let i = usize::try_from(q.clamp(0, 127)).unwrap_or(0);
    AC_QLOOKUP.get(i).copied().unwrap_or(4)
}

/// The dequantization factors `[dc, ac]` of the Y, Y2 and chroma blocks of
/// the segment whose base index is `q` (section 14.1, 20.4).
fn factors(q: i32, d: [i32; 5]) -> [[i32; 2]; 3] {
    let y2ac = ac_q(q.wrapping_add(d[2])).wrapping_mul(155) / 100;
    [
        [dc_q(q.wrapping_add(d[0])), ac_q(q)],
        [dc_q(q.wrapping_add(d[1])).wrapping_mul(2), y2ac.max(8)],
        [
            dc_q(q.wrapping_add(d[3])).min(132),
            ac_q(q.wrapping_add(d[4])),
        ],
    ]
}

/// The coefficient probabilities after the frame's updates.
type Probs = [[[[u8; 11]; 3]; 8]; 4];

fn at<T: Copy + Default>(v: &[T], i: usize) -> T {
    v.get(i).copied().unwrap_or_default()
}

fn set<T>(v: &mut [T], i: usize, x: T) {
    if let Some(s) = v.get_mut(i) {
        *s = x;
    }
}

fn mul(a: usize, b: usize) -> usize {
    a.wrapping_mul(b)
}

fn add(a: usize, b: usize) -> usize {
    a.wrapping_add(b)
}

/// One block of tokens (section 13): `vals` in scan order (positions
/// `first..16` used), the context, the probabilities of its type, and where
/// the `dct_eob` goes (16 for none). Returns whether the block "has
/// coefficients" (ended past where it began).
fn write_block(
    e: &mut Enc,
    probs: &[[[u8; 11]; 3]; 8],
    ctx: usize,
    first: usize,
    vals: &[i32; 16],
    eob: usize,
) -> bool {
    let mut ctx3 = ctx;
    let mut prev_zero = false;
    for c in first..16 {
        let band = usize::from(at(&COEFF_BANDS, c));
        let p = probs
            .get(band)
            .and_then(|b| b.get(ctx3))
            .copied()
            .unwrap_or([128; 11]);
        if c == eob {
            e.tree(&COEFF_TREE, &p, 0, DCT_EOB);
            break;
        }
        let v = at(vals, c);
        let abs = v.unsigned_abs();
        let start = if prev_zero { 2 } else { 0 };
        let (token, extra): (usize, Option<(usize, u32)>) = match abs {
            0..=4 => (abs as usize, None),
            5..=6 => (5, Some((0, abs.wrapping_sub(5)))),
            7..=10 => (6, Some((1, abs.wrapping_sub(7)))),
            11..=18 => (7, Some((2, abs.wrapping_sub(11)))),
            19..=34 => (8, Some((3, abs.wrapping_sub(19)))),
            35..=66 => (9, Some((4, abs.wrapping_sub(35)))),
            _ => (10, Some((5, abs.wrapping_sub(67)))),
        };
        e.tree(&COEFF_TREE, &p, start, token);
        if let Some((cat, rest)) = extra {
            let bits = PCAT.get(cat).copied().unwrap_or(&[]);
            assert_eq!(
                i64::from(abs),
                i64::from(at(&CATEGORY_BASE, cat)).wrapping_add(i64::from(rest))
            );
            let n = u32::try_from(bits.len()).unwrap_or(0);
            for (i, &pb) in bits.iter().enumerate() {
                let shift = n
                    .wrapping_sub(1)
                    .wrapping_sub(u32::try_from(i).unwrap_or(0));
                e.put(pb, (rest >> shift) & 1 == 1);
            }
        }
        if abs != 0 {
            e.put(128, v < 0);
        }
        ctx3 = match abs {
            0 => 0,
            1 => 1,
            _ => 2,
        };
        prev_zero = abs == 0;
    }
    // "ended where it began" is the position of the end-of-block token, or 16
    eob.min(16) != first
}

/// The coefficients of one block, in scan order, and where its `dct_eob`
/// goes: none (zeros to the end), at `first` (empty), or after the last
/// non-zero value.
fn draw_block(rng: &mut Rng, f: &Frame, first: usize, factor: [i32; 2]) -> ([i32; 16], usize) {
    let mut vals = [0i32; 16];
    if rng.below(100) < f.zero_run_percent {
        return (vals, 16);
    }
    if rng.below(100) < f.empty_percent {
        return (vals, first);
    }
    let density = add(rng.below(100), 1).min(60);
    let mut last = None;
    for c in first..16 {
        if rng.below(100) < density.checked_div(add(1, c / 4)).unwrap_or(1) {
            let fac = if c == 0 { factor[0] } else { factor[1] };
            let vmax =
                usize::try_from(1000i32.checked_div(fac.max(1)).unwrap_or(1).max(1)).unwrap_or(1);
            let limit = at(&[1, 1, 2, 4, 6, 10, 20, 40, vmax], rng.below(9)).min(vmax);
            let mag = i32::try_from(add(rng.below(limit), 1)).unwrap_or(1);
            set(
                &mut vals,
                c,
                if rng.below(2) == 0 {
                    mag
                } else {
                    mag.wrapping_neg()
                },
            );
            last = Some(c);
        }
    }
    (vals, last.map_or(first, |l| add(l, 1)))
}

/// The frame as a VP8 chunk's payload (sections 9.1 and 19).
pub fn encode(f: &Frame, rng: &mut Rng) -> Vec<u8> {
    let mb_cols = usize::try_from(f.width.div_ceil(16)).unwrap_or(1);
    let mb_rows = usize::try_from(f.height.div_ceil(16)).unwrap_or(1);
    let mut e = Enc::new();
    // The header, in the order of section 19.2.
    e.flag(f.color_space);
    e.flag(f.clamp);
    e.flag(f.seg.is_some());
    let mut seg_probs = [255u8; 3];
    if let Some(s) = &f.seg {
        e.flag(s.update_map);
        e.flag(s.data.is_some());
        if let Some((abs, q, lf)) = &s.data {
            e.flag(*abs);
            for v in q {
                e.maybe_signed(7, *v);
            }
            for v in lf {
                e.maybe_signed(6, *v);
            }
        }
        if s.update_map {
            for (slot, p) in seg_probs.iter_mut().zip(&s.probs) {
                match p {
                    Some(p) => {
                        e.flag(true);
                        e.literal(8, u32::from(*p));
                        *slot = *p;
                    }
                    None => e.flag(false),
                }
            }
        }
    }
    e.flag(f.simple);
    e.literal(6, f.level);
    e.literal(3, f.sharpness);
    e.flag(f.lf_adj.is_some());
    if let Some(adj) = &f.lf_adj {
        e.flag(adj.update.is_some());
        if let Some((r, m)) = &adj.update {
            for v in r.iter().chain(m) {
                e.maybe_signed(6, *v);
            }
        }
    }
    e.literal(2, f.log2_parts);
    e.literal(7, f.y_ac_qi);
    for d in &f.deltas {
        e.maybe_signed(4, *d);
    }
    e.flag(true); // refresh_entropy_probs
    let mut probs: Probs = DEFAULT_COEFF_PROBS;
    for (pi, ui) in probs.iter_mut().zip(&COEFF_UPDATE_PROBS) {
        for (pj, uj) in pi.iter_mut().zip(ui) {
            for (pk, uk) in pj.iter_mut().zip(uj) {
                for (p, &u) in pk.iter_mut().zip(uk) {
                    let update = rng.below(256) < usize::try_from(f.updates).unwrap_or(0) / 8;
                    e.put(u, update);
                    if update {
                        let np = u8::try_from(add(rng.below(255), 1)).unwrap_or(1);
                        e.literal(8, u32::from(np));
                        *p = np;
                    }
                }
            }
        }
    }
    e.flag(f.skip_prob.is_some());
    if let Some(p) = f.skip_prob {
        e.literal(8, u32::from(p));
    }

    // The factors of each segment (all four equal if there are no segments).
    let d: [i32; 5] = core::array::from_fn(|i| f.deltas.get(i).copied().flatten().unwrap_or(0));
    let base = i32::try_from(f.y_ac_qi).unwrap_or(0);
    let seg_factors: Vec<[[i32; 2]; 3]> = (0..4)
        .map(|i| {
            let q = match &f.seg {
                Some(Seg {
                    data: Some((abs, q, _)),
                    ..
                }) => {
                    let v = q.get(i).copied().flatten().unwrap_or(0);
                    if *abs { v } else { base.wrapping_add(v) }
                }
                _ => base,
            };
            factors(q, d)
        })
        .collect();
    let update_map = f.seg.as_ref().is_some_and(|s| s.update_map);

    // The macroblocks.
    let parts = 1usize << f.log2_parts;
    let mut toks: Vec<Enc> = (0..parts).map(|_| Enc::new()).collect();
    let mut top_modes = vec![B_DC_PRED; mul(mb_cols, 4)];
    let mut top_nz = vec![[0u8; 9]; mb_cols];
    for my in 0..mb_rows {
        let mut left_modes = [B_DC_PRED; 4];
        let mut left_nz = [0u8; 9];
        for mx in 0..mb_cols {
            // The record (section 19.3).
            let segment = if update_map { rng.below(4) } else { 0 };
            if update_map {
                e.tree(&MB_SEGMENT_TREE, &seg_probs, 0, segment);
            }
            let skip = f.skip_prob.is_some() && rng.below(4) == 0;
            if let Some(p) = f.skip_prob {
                e.put(p, skip);
            }
            let ymode = if rng.below(100) < f.b_pred_percent {
                B_PRED
            } else {
                at(&ALL_YMODES, rng.below(4))
            };
            e.tree(&KF_YMODE_TREE, &KF_YMODE_PROB, 0, usize::from(ymode));
            let mut bmodes = [0u8; 16];
            if ymode == B_PRED {
                for i in 0..16usize {
                    let above = if i < 4 {
                        at(&top_modes, add(mul(mx, 4), i))
                    } else {
                        at(&bmodes, i.wrapping_sub(4))
                    };
                    let left = if i % 4 == 0 {
                        at(&left_modes, i / 4)
                    } else {
                        at(&bmodes, i.wrapping_sub(1))
                    };
                    let mode = at(&ALL_BMODES, rng.below(10));
                    let probs = KF_BMODE_PROB
                        .get(usize::from(above))
                        .and_then(|r| r.get(usize::from(left)))
                        .copied()
                        .unwrap_or([128; 9]);
                    e.tree(&BMODE_TREE, &probs, 0, usize::from(mode));
                    set(&mut bmodes, i, mode);
                }
            } else {
                let implied = match ymode {
                    V_PRED => B_VE_PRED,
                    H_PRED => B_HE_PRED,
                    TM_PRED => B_TM_PRED,
                    _ => B_DC_PRED,
                };
                bmodes = [implied; 16];
            }
            for k in 0..4usize {
                set(&mut top_modes, add(mul(mx, 4), k), at(&bmodes, add(12, k)));
                set(&mut left_modes, k, at(&bmodes, add(mul(k, 4), 3)));
            }
            e.tree(&UV_MODE_TREE, &KF_UV_MODE_PROB, 0, rng.below(4));

            // The tokens, in the partition of the row.
            let Some(t) = toks.get_mut(my.checked_rem(parts).unwrap_or(0)) else {
                continue;
            };
            let Some(above) = top_nz.get_mut(mx) else {
                continue;
            };
            let has_y2 = ymode != B_PRED;
            if skip {
                for k in 0..8 {
                    set(&mut left_nz, k, 0);
                    set(above, k, 0);
                }
                if has_y2 {
                    set(&mut left_nz, 8, 0);
                    set(above, 8, 0);
                }
                continue;
            }
            let fac = at(&seg_factors_array(&seg_factors), segment);
            let order: Vec<usize> = if has_y2 {
                core::iter::once(24).chain(0..24).collect()
            } else {
                (0..24).collect()
            };
            for b in order {
                let (kind, first, factor, l, a) = match b {
                    24 => (1usize, 0usize, fac[1], 8usize, 8usize),
                    0..=15 if has_y2 => (0, 1, fac[0], b / 4, b % 4),
                    0..=15 => (3, 0, fac[0], b / 4, b % 4),
                    16..=19 => (
                        2,
                        0,
                        fac[2],
                        add(4, b.wrapping_sub(16) / 2),
                        add(4, b.wrapping_sub(16) % 2),
                    ),
                    _ => (
                        2,
                        0,
                        fac[2],
                        add(6, b.wrapping_sub(20) / 2),
                        add(6, b.wrapping_sub(20) % 2),
                    ),
                };
                let (vals, eob) = draw_block(rng, f, first, factor);
                let ctx = add(usize::from(at(&left_nz, l)), usize::from(at(above, a)));
                let kind_probs = probs.get(kind).copied().unwrap_or([[[128; 11]; 3]; 8]);
                let has = write_block(t, &kind_probs, ctx, first, &vals, eob);
                set(&mut left_nz, l, u8::from(has));
                set(above, a, u8::from(has));
            }
        }
    }
    let _ = ZIGZAG;

    // The frame (section 9.1): tag, start code, size, first partition, the
    // partition size table, the partitions.
    let first = e.finish();
    let tok: Vec<Vec<u8>> = toks.into_iter().map(Enc::finish).collect();
    let tag: u32 = (u32::try_from(first.len()).unwrap_or(0) << 5) | (1 << 4);
    let mut out = vec![
        tag as u8,
        (tag >> 8) as u8,
        (tag >> 16) as u8,
        0x9D,
        0x01,
        0x2A,
    ];
    out.extend_from_slice(&(f.width as u16).to_le_bytes());
    out.extend_from_slice(&(f.height as u16).to_le_bytes());
    out.extend_from_slice(&first);
    for p in tok.iter().take(tok.len().saturating_sub(1)) {
        let n = u32::try_from(p.len()).unwrap_or(0);
        out.extend_from_slice(&[n as u8, (n >> 8) as u8, (n >> 16) as u8]);
    }
    for p in &tok {
        out.extend_from_slice(p);
    }
    out
}

/// The four segments' factors as an array.
fn seg_factors_array(v: &[[[i32; 2]; 3]]) -> [[[i32; 2]; 3]; 4] {
    core::array::from_fn(|i| at(v, i))
}

/// A WebP file (section 2.5: `RIFF`, `WEBP`, a `VP8 ` chunk) around a frame.
pub fn riff(vp8: &[u8]) -> Vec<u8> {
    chunked(&[(*b"VP8 ", vp8.to_vec())], None)
}

/// A file of `chunks`; with `extended` (the canvas size), a `VP8X` chunk
/// first, with the alpha flag set if there is an `ALPH` chunk.
pub fn chunked(chunks: &[([u8; 4], Vec<u8>)], extended: Option<(u32, u32)>) -> Vec<u8> {
    let mut body = Vec::new();
    body.extend_from_slice(b"WEBP");
    if let Some((w, h)) = extended {
        let alpha = chunks.iter().any(|(t, _)| t == b"ALPH");
        body.extend_from_slice(b"VP8X");
        body.extend_from_slice(&10u32.to_le_bytes());
        body.push(if alpha { 0x10 } else { 0 });
        body.extend_from_slice(&[0, 0, 0]);
        body.extend_from_slice(&w.wrapping_sub(1).to_le_bytes()[..3]);
        body.extend_from_slice(&h.wrapping_sub(1).to_le_bytes()[..3]);
    }
    for (tag, data) in chunks {
        body.extend_from_slice(tag);
        body.extend_from_slice(&u32::try_from(data.len()).unwrap_or(0).to_le_bytes());
        body.extend_from_slice(data);
        if data.len() % 2 == 1 {
            body.push(0);
        }
    }
    let mut out = b"RIFF".to_vec();
    out.extend_from_slice(&u32::try_from(body.len()).unwrap_or(0).to_le_bytes());
    out.extend_from_slice(&body);
    out
}

/// Decodes a file with `clazel-webp` and with `image-webp` and returns a
/// description of any difference.
pub fn differs(label: &str, bytes: &[u8]) -> Option<String> {
    let ours = match decode(bytes, usize::MAX, false) {
        Ok(d) => d,
        Err(e) => return Some(format!("{label}: ours failed: {e}")),
    };
    let theirs = match reference(bytes) {
        Ok(r) => r,
        Err(e) => return Some(format!("{label}: reference failed: {e}")),
    };
    if (ours.width, ours.height) != (theirs.width, theirs.height) {
        return Some(format!("{label}: size differs"));
    }
    let (Some(a), Some(b)) = (ours.frames.first(), theirs.frames.first()) else {
        return Some(format!("{label}: no frame ({:?})", ours.end));
    };
    if a.1 != b.1 {
        let at = a.1.iter().zip(&b.1).position(|(x, y)| x != y);
        let px = at.map(|i| i / 4);
        return Some(format!(
            "{label}: pixels differ, first at byte {at:?} (pixel {px:?}, width {})",
            ours.width
        ));
    }
    None
}
