//! DCT coefficient decoding: RFC 6386 section 13 (the token tree, the extra
//! bits, the probability contexts), with the dequantization of section 14.1
//! applied as each coefficient is stored, as the reference decoder's
//! `decode_mb_tokens` (section 20.16) does.
//!
//! The reference decoder is the authority where section 13.3's pseudocode
//! and it differ (ERRATA.md): a block "has coefficients" for the contexts of
//! later blocks when its end-of-block position is past its first position
//! (any token but `dct_eob` was decoded), even if every token was `DCT_0`.

use super::bool_decoder::BoolDecoder;
use super::header::CoeffProbs;
use super::quant::Dequant;
use super::tables::{CATEGORY_BASE, COEFF_BANDS, COEFF_TREE, DCT_EOB, PCAT, ZIGZAG};

/// The blocks of a macroblock: 16 Y, 4 U, 4 V, and the Y2 block (section
/// 13: "24 (or 25 with the Y2 subblock) 4x4 subblocks").
pub(crate) const BLOCKS: usize = 25;

/// The index of the Y2 block in [`Coeffs`].
pub(crate) const Y2_BLOCK: usize = 24;

/// The coefficients of a macroblock, dequantized, block after block, 16 to a
/// block in raster order within the block: blocks 0 to 15 are Y in raster
/// order, 16 to 19 U, 20 to 23 V, 24 Y2.
pub(crate) type Coeffs = [i16; BLOCKS * 16];

/// The "has coefficients" flags of section 13.3, for the blocks along one
/// edge of a macroblock: 4 for Y (indices 0 to 3), 2 for U (4, 5), 2 for V
/// (6, 7), and 1 for Y2 (8).
pub(crate) type Context = [u8; 9];

/// The block types of section 13.3, the first index of `coeff_probs`.
const TYPE_Y_AFTER_Y2: usize = 0;
const TYPE_Y2: usize = 1;
const TYPE_CHROMA: usize = 2;
const TYPE_Y_WITH_DC: usize = 3;

/// Probabilities to use if a block type is somehow missing (not reached: the
/// array has 4 types).
const FLAT: [[[u8; 11]; 3]; 8] = [[[128; 11]; 3]; 8];

/// `DCTextra`: the extra bits of category `cat` (0 for `dct_cat1`), high bit
/// first.
fn dct_extra(d: &mut BoolDecoder<'_>, cat: usize) -> i32 {
    let mut v = 0i32;
    for &p in PCAT.get(cat).copied().unwrap_or(&[]) {
        v = (v << 1) | i32::from(d.read_bool(p));
    }
    v
}

/// One block: tokens from position `first`, the context `ctx` (0 to 2) of
/// section 13.3's third index, the factors `[dc, ac]`; stores the
/// dequantized coefficients in `out` (16 values, raster order) and returns
/// the position where the block ended (its `c` in the reference decoder), at
/// least `first` and at most 16.
fn decode_block(
    d: &mut BoolDecoder<'_>,
    probs: &[[[u8; 11]; 3]; 8],
    ctx: usize,
    first: usize,
    factor: [i32; 2],
    out: &mut [i16],
) -> usize {
    let mut c = first;
    let mut ctx3 = ctx;
    // "if the preceding coefficient is a DCT_0, decoding will skip the first
    // branch, since it is not possible for dct_eob to follow a DCT_0"
    let mut after_zero = false;
    while c < 16 {
        let band = usize::from(COEFF_BANDS.get(c).copied().unwrap_or(0));
        let p = probs
            .get(band)
            .and_then(|b| b.get(ctx3))
            .copied()
            .unwrap_or([128; 11]);
        let token = d.read_tree(&COEFF_TREE, &p, if after_zero { 2 } else { 0 });
        if token == DCT_EOB {
            break;
        }
        // DCT_0 to DCT_4 are the values 0 to 4; the categories add their
        // extra bits to the base of their range.
        let abs = if token <= 4 {
            i32::try_from(token).unwrap_or(0)
        } else {
            let cat = token.saturating_sub(5);
            CATEGORY_BASE
                .get(cat)
                .copied()
                .unwrap_or(0)
                .saturating_add(dct_extra(d, cat))
        };
        if abs != 0 {
            let value = if d.read_bool(128) {
                abs.wrapping_neg()
            } else {
                abs
            };
            // "the multiplies are computed and stored using 16-bit signed
            // integers" (section 14.1): wrapping, as the reference decoder's
            // `short`.
            let dq = value.wrapping_mul(factor.get(usize::from(c > 0)).copied().unwrap_or(0));
            if let Some(slot) = ZIGZAG.get(c).and_then(|&z| out.get_mut(z)) {
                *slot = dq as i16;
            }
        }
        // The context of the next token: 0 after a zero, 1 after a one, 2
        // after a larger value.
        ctx3 = match abs {
            0 => 0,
            1 => 1,
            _ => 2,
        };
        after_zero = abs == 0;
        c = c.saturating_add(1);
    }
    c
}

/// The left and above context slots of block `block` (section 13.3: "the
/// block above ... and the block to the left").
fn slots(block: usize) -> (usize, usize) {
    match block {
        0..=15 => (block >> 2, block & 3),
        16..=19 => {
            let k = block.saturating_sub(16);
            (4usize.saturating_add(k >> 1), 4usize.saturating_add(k & 1))
        }
        20..=23 => {
            let k = block.saturating_sub(20);
            (6usize.saturating_add(k >> 1), 6usize.saturating_add(k & 1))
        }
        _ => (8, 8),
    }
}

/// The tokens of one macroblock (not a skipped one): the Y2 block if
/// `has_y2` (every mode but `B_PRED`), 16 Y blocks, 4 U, 4 V, into `out`
/// (which the caller has cleared), updating the contexts `left` and `above`.
/// Returns whether any block had a token other than `dct_eob` (the
/// reference decoder's non-zero `eob_mask`: section 15.1's "There is no DCT
/// coefficient coded for the whole macroblock", negated).
pub(crate) fn decode_mb_tokens(
    d: &mut BoolDecoder<'_>,
    left: &mut Context,
    above: &mut Context,
    probs: &CoeffProbs,
    has_y2: bool,
    dq: &Dequant,
    out: &mut Coeffs,
) -> bool {
    let mut any = false;
    // The blocks in coding order: Y2 first, then the 24 others.
    let count = if has_y2 { BLOCKS } else { Y2_BLOCK };
    for i in 0..count {
        let block = match (has_y2, i) {
            (true, 0) => Y2_BLOCK,
            (true, _) => i.saturating_sub(1),
            (false, _) => i,
        };
        let (kind, first, factor) = match block {
            Y2_BLOCK => (TYPE_Y2, 0, dq.y2),
            0..=15 if has_y2 => (TYPE_Y_AFTER_Y2, 1, dq.y1),
            0..=15 => (TYPE_Y_WITH_DC, 0, dq.y1),
            _ => (TYPE_CHROMA, 0, dq.uv),
        };
        let (l, a) = slots(block);
        let ctx = usize::from(left.get(l).copied().unwrap_or(0))
            .saturating_add(usize::from(above.get(a).copied().unwrap_or(0)));
        let probs_for_type = probs.get(kind).unwrap_or(&FLAT);
        let start = block.saturating_mul(16);
        let end = start.saturating_add(16);
        let end_pos = match out.get_mut(start..end) {
            Some(coeffs) => decode_block(d, probs_for_type, ctx, first, factor, coeffs),
            None => first,
        };
        // "t = (c != !type)": the block has data unless it ended where it
        // began.
        let t = end_pos != first;
        any |= t;
        if let Some(s) = left.get_mut(l) {
            *s = u8::from(t);
        }
        if let Some(s) = above.get_mut(a) {
            *s = u8::from(t);
        }
    }
    any
}
