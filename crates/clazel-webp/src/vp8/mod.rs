//! Lossy WebP: the VP8 key frame decoder (phase-6.md item 6.9).
//!
//! # The standard
//!
//! *RFC 6386: VP8 Data Format and Decoding Guide*, Bankoski, Koleszar,
//! Quillio, Salonen, Wilkins and Xu, November 2011,
//! <https://www.rfc-editor.org/rfc/rfc6386.txt> (17,027 lines, fetched
//! 2026-11-21, SHA-256
//! `c044997ae5e26f74dc28569f8866937412b2783e887c96e0c09372af78be411c`).
//! Section numbers in the comments are that document's: 7 Boolean Entropy
//! Decoder (7.3 Actual Implementation), 8 Compressed Data Components (8.1
//! Tree Coding), 9 Frame Header (9.1 to 9.11), 10 Segment-Based Feature
//! Adjustments, 11 Key Frame Macroblock Prediction Records, 12 Intraframe
//! Prediction, 13 DCT Coefficient Decoding, 14 DCT and WHT Inversion and
//! Macroblock Reconstruction (14.1 Dequantization, 14.3 WHT, 14.4 DCT, 14.5
//! Summation), 15 Loop Filter, 19 Annex A: Bitstream Syntax, 20 the
//! reference decoder source (`dixie`), which the RFC includes in its text and
//! this code follows where the prose is loose. WebP has key frames only
//! (RFC 9649 section 2.5), so everything about inter frames (sections 16 to
//! 18, the golden and altref frames, motion vectors) is out.
//!
//! # Files
//!
//! | File | RFC 6386 |
//! |------|----------|
//! | `bool_decoder.rs` | 7.3, 8.1 |
//! | `header.rs` | 9, 19.2 |
//! | `quant.rs` | 9.6, 14.1 |
//! | `tables.rs` | 11, 13, 14.1 tables |
//! | `tokens.rs` | 13 |
//! | `transform.rs` | 14.3, 14.4, 14.5 |
//! | `predict.rs`, `plane.rs` | 12 |
//! | `loop_filter.rs` | 15 |
//! | `yuv.rs` | (not in the RFC: listed choice) |
//! | this file | 9.1, 19.1, 19.3, and the order of decoding |
//!
//! # How a frame is decoded
//!
//! The whole `VP8 ` chunk is in memory (the container gathers it, `decoder.rs`
//! says where). `decode` reads the 10 uncompressed bytes (9.1), the frame
//! header from the first partition (9, 19.2), cuts the token partitions out of
//! the rest (9.5), then for each macroblock in raster order reads its
//! prediction record from the first partition (19.3, 11), its coefficients
//! from the partition of its row (13), reconstructs it, predictor plus
//! residue (12, 14), into planes the size of the frame rounded up to whole
//! macroblocks, and when all are done filters the whole frame (15) and
//! converts it to RGBA (`yuv.rs`).
//!
//! # Listed choices
//!
//! 1. **Key frames of a shown frame only**: a frame tag that is not a key
//!    frame, a `version` over 3 (libwebp's), `show_frame` 0 (libwebp's "frame
//!    not displayable"), a wrong start code, or a size other than the
//!    container's is `Malformed`. The 2-bit scale of each dimension is
//!    ignored (section 9.1: "horizontal_scale" is a hint for the display),
//!    as libwebp does.
//! 2. **`color_space` and `clamping_type` are read and ignored** (section
//!    9.2: 1 is "reserved"; the reference decoder refuses a set bit, libwebp
//!    ignores it, so do we). The decoder always clamps (section 14.5), which
//!    changes nothing for a stream that promises it need not.
//! 3. **Partitions that do not fit are `Malformed`**: the first partition or
//!    a token partition (sizes from the 3-byte table of section 9.5) reaching
//!    past the chunk; libwebp clamps such a size instead. A partition that is
//!    too short for what is read from it ends the decode with `Malformed`
//!    too (`bool_decoder.rs`'s `eof`: libwebp's criterion), checked after
//!    the header and after each macroblock's record and each macroblock's
//!    coefficients.
//! 4. **Sixteen-bit storage** where the RFC says it (sections 14.1, 14.3,
//!    14.4): dequantized coefficients and the transforms' intermediate
//!    arrays are `i16`, wrapping. libwebp keeps its transform intermediates
//!    in 32 bits, so the two differ on a stream whose values overflow 16
//!    bits, which no encoder writes.
//! 5. **A block "has coefficients" when it did not end where it began**
//!    (the reference decoder's rule, not section 13.3's pseudocode:
//!    ERRATA.md), for the contexts of 13.3 and for 15.1's choice of whether
//!    to filter the subblock edges.
//! 6. **Loop filter level**: as the reference decoder's
//!    `calculate_filter_parameters` (section 20.6): clamped to 0 to 63 after
//!    the segment adjustment and again after the deltas. A frame-level
//!    `loop_filter_level` of 0 turns the filter off for every macroblock,
//!    whatever the segments say (section 15: "loop filtering must be skipped
//!    entirely if loop_filter_level at either the frame header level or
//!    macroblock override level is 0").
//! 7. **The segment of a macroblock** is 0 when the frame does not update
//!    the segment map (a key frame has no earlier map).
//! 8. **Whole-frame reconstruction, then filtering**, as section 15.1
//!    describes (and not libwebp's row pipeline: the results are the same).
//!    The planes are `1.5` bytes per pixel of the macroblock-aligned frame,
//!    held in the work buffer, with 1 byte per macroblock for the filter and
//!    13 bytes per macroblock column for the contexts.
//! 9. **YUV to RGB**: libwebp's fixed-point conversion and fancy upsampling
//!    (`yuv.rs` cites the constants and the weights), alpha straight.
//! 10. **The above-right pixels** of the rightmost macroblock below the top
//!     row repeat the pixel at (-1, 15) (section 12.3, quoted in
//!     `predict.rs`).

pub(crate) mod bool_decoder;
pub(crate) mod header;
pub(crate) mod loop_filter;
pub(crate) mod plane;
pub(crate) mod predict;
pub(crate) mod quant;
pub(crate) mod tables;
pub(crate) mod tokens;
pub(crate) mod transform;
pub(crate) mod yuv;

use clazel_image_shape::Error;

use bool_decoder::BoolDecoder;
use header::FrameHeader;
use loop_filter::MbInfo;
use plane::{Plane, coord};
use tables::{
    B_DC_PRED, B_HE_PRED, B_PRED, B_TM_PRED, B_VE_PRED, BMODE_TREE, DC_PRED, H_PRED, KF_BMODE_PROB,
    KF_UV_MODE_PROB, KF_YMODE_PROB, KF_YMODE_TREE, MB_SEGMENT_TREE, TM_PRED, UV_MODE_TREE, V_PRED,
};
use tokens::{BLOCKS, Coeffs, Context, Y2_BLOCK};

fn bad(why: &'static str) -> Error {
    Error::Malformed(why)
}

/// `clamp255` (section 12.2).
pub(crate) fn clamp255(v: i32) -> u8 {
    u8::try_from(v.clamp(0, 255)).unwrap_or(0)
}

/// The size of the most partitions: `1 << 3` (section 9.5).
const MAX_PARTITIONS: usize = 8;

/// The sizes of the regions of the lossy work space for a frame of
/// `mb_cols` by `mb_rows` macroblocks, in the order they are cut:
///
/// | region | bytes | holds |
/// |--------|-------|-------|
/// | `y` | `256 * macroblocks` | the luma plane |
/// | `u`, `v` | `64 * macroblocks` each | the chroma planes |
/// | `info` | `macroblocks` | for each macroblock, what the loop filter needs |
/// | `top_modes` | `4 * mb_cols` | the subblock modes of the row above (section 11.3) |
/// | `top_nz` | `9 * mb_cols` | the coefficient contexts of the row above (13.3) |
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Layout {
    mb_cols: usize,
    mb_rows: usize,
    y: usize,
    c: usize,
    info: usize,
    modes: usize,
    nz: usize,
}

impl Layout {
    /// The layout for a `width` by `height` frame (both at least 1).
    pub(crate) fn new(width: u32, height: u32) -> Option<Layout> {
        let mb_cols = usize::try_from(width.checked_add(15)? / 16).ok()?;
        let mb_rows = usize::try_from(height.checked_add(15)? / 16).ok()?;
        let mbs = mb_cols.checked_mul(mb_rows)?;
        Some(Layout {
            mb_cols,
            mb_rows,
            y: mbs.checked_mul(256)?,
            c: mbs.checked_mul(64)?,
            info: mbs,
            modes: mb_cols.checked_mul(4)?,
            nz: mb_cols.checked_mul(9)?,
        })
    }

    /// The bytes of all the regions.
    pub(crate) fn len(&self) -> Option<usize> {
        self.y
            .checked_add(self.c.checked_mul(2)?)?
            .checked_add(self.info)?
            .checked_add(self.modes)?
            .checked_add(self.nz)
    }
}

/// The bytes of the lossy work space for a `width` by `height` frame: [`SPARE`]
/// bytes, then the regions of [`Layout`].
pub(crate) fn lossy_len(width: u32, height: u32) -> Option<usize> {
    Layout::new(width, height)?.len()?.checked_add(SPARE)
}

/// The bytes at the start of the lossy work space that hold a `VP8 ` chunk of
/// at most this many bytes (the planes follow). The container gathers the
/// chunk into the frame's RGBA buffer, which is too small for a tiny image
/// (a frame of 1 by 1 pixel has 4 bytes; its chunk about 40).
pub(crate) const SPARE: usize = 1024;

/// The regions of the lossy work space, cut.
struct Regions<'a> {
    y: &'a mut [u8],
    u: &'a mut [u8],
    v: &'a mut [u8],
    info: &'a mut [u8],
    top_modes: &'a mut [u8],
    top_nz: &'a mut [u8],
}

impl<'a> Regions<'a> {
    /// Cuts `region`, which must be exactly `layout.len()` bytes.
    fn new(region: &'a mut [u8], layout: &Layout) -> Option<Regions<'a>> {
        if region.len() != layout.len()? {
            return None;
        }
        let (y, rest) = region.split_at_mut_checked(layout.y)?;
        let (u, rest) = rest.split_at_mut_checked(layout.c)?;
        let (v, rest) = rest.split_at_mut_checked(layout.c)?;
        let (info, rest) = rest.split_at_mut_checked(layout.info)?;
        let (top_modes, top_nz) = rest.split_at_mut_checked(layout.modes)?;
        Some(Regions {
            y,
            u,
            v,
            info,
            top_modes,
            top_nz,
        })
    }
}

/// The fixed part of a key frame's first bytes (sections 9.1 and 19.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct FrameTag {
    first_part_size: usize,
    width: u32,
    height: u32,
}

/// Section 19.1: the 3-byte frame tag, the start code and the sizes; the
/// frame must be a key frame of the container's size.
fn parse_tag(data: &[u8], width: u32, height: u32) -> Result<FrameTag, Error> {
    let Some(head) = data.get(..10) else {
        return Err(bad("a VP8 chunk of under 10 bytes"));
    };
    let byte = |i: usize| u32::from(head.get(i).copied().unwrap_or(0));
    // "tmp = (c[2] << 16) | (c[1] << 8) | c[0]; key_frame = tmp & 0x1 (0 is
    // a key frame); version = (tmp >> 1) & 0x7; show_frame = (tmp >> 4) &
    // 0x1; first_part_size = (tmp >> 5) & 0x7FFFF"
    let tmp = (byte(2) << 16) | (byte(1) << 8) | byte(0);
    if tmp & 1 != 0 {
        return Err(bad("a VP8 frame that is not a key frame"));
    }
    if (tmp >> 1) & 7 > 3 {
        return Err(bad("a VP8 version over 3"));
    }
    if (tmp >> 4) & 1 == 0 {
        return Err(bad("a VP8 frame that is not meant to be shown"));
    }
    if head.get(3..6) != Some(&[0x9D, 0x01, 0x2A]) {
        return Err(bad("the VP8 start code is not 9d 01 2a"));
    }
    // "width = tmp & 0x3FFF; horizontal_scale = tmp >> 14" (the scale is
    // ignored), and the same for the height.
    let w = ((byte(7) << 8) | byte(6)) & 0x3FFF;
    let h = ((byte(9) << 8) | byte(8)) & 0x3FFF;
    if (w, h) != (width, height) {
        return Err(bad("the VP8 frame is not the size its container says"));
    }
    Ok(FrameTag {
        first_part_size: usize::try_from((tmp >> 5) & 0x7FFFF).unwrap_or(0),
        width: w,
        height: h,
    })
}

/// The partitions of the coefficient data (section 9.5): `1 << log2` of them,
/// all but the last with a 3-byte size at the start of `rest`, the last
/// "the remainder of the data not used by any of the previous partitions".
fn token_partitions(rest: &[u8], log2: u32) -> Result<[&[u8]; MAX_PARTITIONS], Error> {
    let count = 1usize << log2.min(3);
    let table_len = count.saturating_sub(1).saturating_mul(3);
    let Some((table, mut data)) = rest.split_at_checked(table_len) else {
        return Err(bad("the partition size table runs past the chunk"));
    };
    let mut out: [&[u8]; MAX_PARTITIONS] = [&[]; MAX_PARTITIONS];
    for (i, slot) in out.iter_mut().enumerate().take(count) {
        let size = if i.saturating_add(1) < count {
            // "Offset/size = byte0 + (byte1 << 8) + (byte2 << 16)"
            let at = i.saturating_mul(3);
            let b = |k: usize| usize::from(table.get(at.saturating_add(k)).copied().unwrap_or(0));
            b(0) | (b(1) << 8) | (b(2) << 16)
        } else {
            data.len()
        };
        let Some((part, tail)) = data.split_at_checked(size) else {
            return Err(bad("a token partition runs past the end of the chunk"));
        };
        *slot = part;
        data = tail;
    }
    Ok(out)
}

/// The subblock mode a whole-macroblock luma mode stands for in the contexts
/// of later subblocks (section 11.3, item 4).
fn implied_bmode(ymode: u8) -> u8 {
    match ymode {
        V_PRED => B_VE_PRED,
        H_PRED => B_HE_PRED,
        TM_PRED => B_TM_PRED,
        // DC_PRED
        _ => B_DC_PRED,
    }
}

/// The prediction record of one macroblock (section 19.3's
/// `macroblock_header()` for a key frame).
#[derive(Debug, Clone, Copy)]
struct MbHeader {
    segment: u8,
    skip: bool,
    ymode: u8,
    bmodes: [u8; 16],
    uvmode: u8,
}

/// Reads the record of the macroblock at column `mb_x`, updating the
/// subblock-mode contexts (section 11.3): `left` for the macroblock to the
/// left, `top_modes` for the row above.
fn read_mb_header(
    d: &mut BoolDecoder<'_>,
    h: &FrameHeader,
    left: &mut [u8; 4],
    top_modes: &mut [u8],
    mb_x: usize,
) -> MbHeader {
    // "if (update_mb_segmentation_map) segment_id T"
    let segment = if h.update_mb_segmentation_map {
        u8::try_from(d.read_tree(&MB_SEGMENT_TREE, &h.segment_prob, 0)).unwrap_or(0)
    } else {
        0
    };
    // "if (mb_no_skip_coeff) mb_skip_coeff B(p)"
    let skip = h.mb_no_skip_coeff && d.read_bool(h.prob_skip_false);
    // intra_y_mode, with the fixed probabilities of a key frame (11.2)
    let ymode = u8::try_from(d.read_tree(&KF_YMODE_TREE, &KF_YMODE_PROB, 0)).unwrap_or(DC_PRED);
    let mut bmodes = [0u8; 16];
    let top = mb_x.saturating_mul(4);
    if ymode == B_PRED {
        for i in 0..16usize {
            // The contexts: the mode above and to the left, which for the
            // top row and left column of subblocks are the neighbouring
            // macroblocks' (11.3, items 1 to 3).
            let above = if i < 4 {
                top_modes.get(top.saturating_add(i)).copied().unwrap_or(0)
            } else {
                bmodes.get(i.saturating_sub(4)).copied().unwrap_or(0)
            };
            let before = if i & 3 == 0 {
                left.get(i >> 2).copied().unwrap_or(0)
            } else {
                bmodes.get(i.saturating_sub(1)).copied().unwrap_or(0)
            };
            let probs = KF_BMODE_PROB
                .get(usize::from(above))
                .and_then(|row| row.get(usize::from(before)))
                .copied()
                .unwrap_or([128; 9]);
            let mode = u8::try_from(d.read_tree(&BMODE_TREE, &probs, 0)).unwrap_or(B_DC_PRED);
            if let Some(slot) = bmodes.get_mut(i) {
                *slot = mode;
            }
        }
    } else {
        bmodes = [implied_bmode(ymode); 16];
    }
    // After the macroblock: its bottom four subblock modes go to the row
    // above for the next row, its right four to the left for the next
    // macroblock (11.3, item 3).
    for k in 0..4usize {
        if let Some(slot) = top_modes.get_mut(top.saturating_add(k)) {
            *slot = bmodes.get(12usize.saturating_add(k)).copied().unwrap_or(0);
        }
        if let Some(slot) = left.get_mut(k) {
            *slot = bmodes
                .get(k.saturating_mul(4).saturating_add(3))
                .copied()
                .unwrap_or(0);
        }
    }
    // intra_uv_mode, fixed probabilities (11.4)
    let uvmode = u8::try_from(d.read_tree(&UV_MODE_TREE, &KF_UV_MODE_PROB, 0)).unwrap_or(DC_PRED);
    MbHeader {
        segment,
        skip,
        ymode,
        bmodes,
        uvmode,
    }
}

/// The residue of block `block` of `coeffs`, if it is not all zero.
fn block_coeffs(coeffs: &Coeffs, block: usize) -> Option<[i16; 16]> {
    let start = block.checked_mul(16)?;
    let b: [i16; 16] = coeffs.get(start..start.checked_add(16)?)?.try_into().ok()?;
    b.iter().any(|&c| c != 0).then_some(b)
}

/// Section 14.5: adds the inverse DCT of `block` to the 4 by 4 pixels at
/// (`x0`, `y0`) of `plane` (a block of zeros adds nothing).
fn add_block(plane: &mut Plane<'_>, x0: usize, y0: usize, block: Option<[i16; 16]>) {
    let Some(coeffs) = block else {
        return;
    };
    let residue = transform::inverse_dct(&coeffs);
    for r in 0..4usize {
        for c in 0..4usize {
            let x = x0.saturating_add(c);
            let y = y0.saturating_add(r);
            let res = residue
                .get(r.saturating_mul(4).saturating_add(c))
                .copied()
                .unwrap_or(0);
            plane.set(x, y, transform::add_residue(plane.at(x, y), res));
        }
    }
}

/// Reconstructs one macroblock (predictor and residue): section 12 for the
/// predictor, 14 for the residue. `coeffs` holds the dequantized coefficients
/// (all zero for a skipped macroblock).
fn reconstruct(
    planes: (&mut Plane<'_>, &mut Plane<'_>, &mut Plane<'_>),
    mb: &MbHeader,
    mb_x: usize,
    mb_y: usize,
    mb_cols: usize,
    coeffs: &mut Coeffs,
) {
    let (y, u, v) = planes;
    let has_y2 = mb.ymode != B_PRED;
    // Section 14.2: "If the Y2 residue block exists ..., it is inverted
    // first (using the inverse WHT) and the element of the result at row i,
    // column j is used as the 0th coefficient of the Y subblock at position
    // (i, j)".
    if has_y2 && let Some(y2) = block_coeffs(coeffs, Y2_BLOCK) {
        let dc = transform::inverse_wht(&y2);
        for (i, &v) in dc.iter().enumerate() {
            if let Some(slot) = coeffs.get_mut(i.saturating_mul(16)) {
                *slot = v;
            }
        }
    }
    let (x0, y0) = (mb_x.saturating_mul(16), mb_y.saturating_mul(16));
    if mb.ymode == B_PRED {
        // Each subblock is predicted from the reconstructed ones before it.
        let above_right = predict::mb_above_right(y, mb_x, mb_y, mb_cols);
        for sb in 0..16usize {
            let (bx, by) = (sb & 3, sb >> 2);
            let sx = x0.saturating_add(bx.saturating_mul(4));
            let sy = y0.saturating_add(by.saturating_mul(4));
            // Subblocks 3, 7, 11 and 15 use the macroblock's above-right
            // pixels; the others the ones right above them.
            let ar = if bx == 3 {
                above_right
            } else {
                let mut a = [0u8; 4];
                for (k, slot) in a.iter_mut().enumerate() {
                    *slot = y.get(
                        coord(sx).saturating_add(4).saturating_add(coord(k)),
                        coord(sy).saturating_sub(1),
                    );
                }
                a
            };
            let edge = predict::subblock_edge(y, sx, sy, ar);
            let mode = mb.bmodes.get(sb).copied().unwrap_or(B_DC_PRED);
            let pred = predict::predict_subblock(mode, &edge);
            for (i, &p) in pred.iter().enumerate() {
                y.set(sx.saturating_add(i & 3), sy.saturating_add(i >> 2), p);
            }
            add_block(y, sx, sy, block_coeffs(coeffs, sb));
        }
    } else {
        predict::predict_block(y, x0, y0, 16, mb.ymode, mb_y > 0, mb_x > 0);
        for sb in 0..16usize {
            let sx = x0.saturating_add((sb & 3).saturating_mul(4));
            let sy = y0.saturating_add((sb >> 2).saturating_mul(4));
            add_block(y, sx, sy, block_coeffs(coeffs, sb));
        }
    }
    // Chroma: the same mode for U and V, four blocks each (blocks 16 to 19
    // and 20 to 23).
    reconstruct_chroma(u, mb, mb_x, mb_y, 16, coeffs);
    reconstruct_chroma(v, mb, mb_x, mb_y, 20, coeffs);
}

/// Predicts and adds the residue of one chroma plane of a macroblock, whose
/// four blocks are blocks `first` to `first + 3` of `coeffs`.
fn reconstruct_chroma(
    plane: &mut Plane<'_>,
    mb: &MbHeader,
    mb_x: usize,
    mb_y: usize,
    first: usize,
    coeffs: &Coeffs,
) {
    let (cx, cy) = (mb_x.saturating_mul(8), mb_y.saturating_mul(8));
    predict::predict_block(plane, cx, cy, 8, mb.uvmode, mb_y > 0, mb_x > 0);
    for k in 0..4usize {
        let sx = cx.saturating_add((k & 1).saturating_mul(4));
        let sy = cy.saturating_add((k >> 1).saturating_mul(4));
        add_block(plane, sx, sy, block_coeffs(coeffs, first.saturating_add(k)));
    }
}

/// Decodes the VP8 key frame in `data` (the payload of a `VP8 ` chunk) that
/// the container says is `width` by `height`, into the planes in `region`
/// (exactly [`lossy_len`] bytes; its contents on entry do not matter), loop
/// filtered. [`to_rgba`] then converts them.
pub(crate) fn decode(data: &[u8], width: u32, height: u32, region: &mut [u8]) -> Result<(), Error> {
    let tag = parse_tag(data, width, height)?;
    let layout = Layout::new(tag.width, tag.height).ok_or(bad("a VP8 frame size overflow"))?;
    let Some(r) = Regions::new(region, &layout) else {
        return Err(bad("the work space does not fit the frame"));
    };
    // "The first partition (control partition), excluding the uncompressed
    // data chunk", then the token partitions.
    let body = data.get(10..).ok_or(bad("a VP8 chunk of under 10 bytes"))?;
    let Some((first, rest)) = body.split_at_checked(tag.first_part_size) else {
        return Err(bad("the first partition runs past the end of the chunk"));
    };
    let mut d = BoolDecoder::new(first);
    let h = FrameHeader::read(&mut d);
    if d.eof() {
        return Err(bad("the frame header runs past the first partition"));
    }
    let parts = token_partitions(rest, h.log2_nbr_of_dct_partitions)?;
    let count = 1usize << h.log2_nbr_of_dct_partitions.min(3);
    let mut tokens: [BoolDecoder<'_>; MAX_PARTITIONS] =
        core::array::from_fn(|i| BoolDecoder::new(parts.get(i).copied().unwrap_or(&[])));
    let dq = quant::segment_factors(&h);

    let Regions {
        y,
        u,
        v,
        info,
        top_modes,
        top_nz,
    } = r;
    let mut y_plane = Plane::new(y, layout.mb_cols.saturating_mul(16));
    let mut u_plane = Plane::new(u, layout.mb_cols.saturating_mul(8));
    let mut v_plane = Plane::new(v, layout.mb_cols.saturating_mul(8));
    // "Before decoding the frame, the entire row is initialized to
    // B_DC_PRED" (11.3); the coefficient contexts start empty (13.3).
    top_modes.fill(B_DC_PRED);
    top_nz.fill(0);
    let mut mb_index = 0usize;
    for mb_y in 0..layout.mb_rows {
        // "before decoding each row of macroblocks, the four left predictors
        // are also set to B_DC_PRED"; the left coefficient context is empty.
        let mut left_modes = [B_DC_PRED; 4];
        let mut left_nz: Context = [0; 9];
        let part = mb_y & count.saturating_sub(1);
        for mb_x in 0..layout.mb_cols {
            let mb = read_mb_header(&mut d, &h, &mut left_modes, top_modes, mb_x);
            if d.eof() {
                return Err(bad(
                    "the first partition ends inside the macroblock records",
                ));
            }
            let b_pred = mb.ymode == B_PRED;
            let mut coeffs: Coeffs = [0; BLOCKS * 16];
            let mut any = false;
            let at = mb_x.saturating_mul(9);
            let mut above: Context = [0; 9];
            if let Some(src) = top_nz.get(at..at.saturating_add(9)) {
                above.copy_from_slice(src);
            }
            let Some(tok) = tokens.get_mut(part) else {
                return Err(bad("a token partition out of range"));
            };
            if mb.skip {
                // dixie `reset_mb_context`: the Y, U and V contexts are
                // cleared, the Y2 one only if this macroblock would have
                // updated it.
                left_nz.iter_mut().take(8).for_each(|s| *s = 0);
                above.iter_mut().take(8).for_each(|s| *s = 0);
                if !b_pred {
                    if let Some(s) = left_nz.get_mut(8) {
                        *s = 0;
                    }
                    if let Some(s) = above.get_mut(8) {
                        *s = 0;
                    }
                }
            } else {
                let dq_seg = dq
                    .get(usize::from(mb.segment))
                    .copied()
                    .ok_or(bad("a segment out of range"))?;
                any = tokens::decode_mb_tokens(
                    tok,
                    &mut left_nz,
                    &mut above,
                    &h.coeff_probs,
                    !b_pred,
                    &dq_seg,
                    &mut coeffs,
                );
                if tok.eof() {
                    return Err(bad("a token partition ends inside the coefficients"));
                }
            }
            if let Some(dst) = top_nz.get_mut(at..at.saturating_add(9)) {
                dst.copy_from_slice(&above);
            }
            reconstruct(
                (&mut y_plane, &mut u_plane, &mut v_plane),
                &mb,
                mb_x,
                mb_y,
                layout.mb_cols,
                &mut coeffs,
            );
            // What the loop filter needs: the segment, `B_PRED`, and
            // whether to filter the subblock edges (15.1: unless "neither
            // B_PRED nor SPLITMV" and "no DCT coefficient coded").
            let packed = mb.segment | (u8::from(b_pred) << 2) | (u8::from(b_pred || any) << 3);
            if let Some(slot) = info.get_mut(mb_index) {
                *slot = packed;
            }
            mb_index = mb_index.saturating_add(1);
        }
    }
    // Section 15: "loop filtering must be skipped entirely if
    // loop_filter_level at either the frame header level ... is 0".
    if h.loop_filter_level != 0 {
        let mut i = 0usize;
        for mb_y in 0..layout.mb_rows {
            for mb_x in 0..layout.mb_cols {
                let packed = info.get(i).copied().unwrap_or(0);
                i = i.saturating_add(1);
                let mb = MbInfo {
                    segment: packed & 3,
                    b_pred: packed & 4 != 0,
                    inner: packed & 8 != 0,
                };
                loop_filter::filter_macroblock(
                    &h,
                    mb,
                    mb_x,
                    mb_y,
                    (&mut y_plane, &mut u_plane, &mut v_plane),
                );
            }
        }
    }
    Ok(())
}

/// Converts the planes `decode` left in `region` to RGBA in `out`
/// (`yuv.rs`), with `alpha` (`width * height` bytes) if there is a plane.
pub(crate) fn to_rgba(
    region: &mut [u8],
    width: u32,
    height: u32,
    alpha: Option<&[u8]>,
    out: &mut [u8],
) -> Result<(), Error> {
    let layout = Layout::new(width, height).ok_or(bad("a VP8 frame size overflow"))?;
    let Some(r) = Regions::new(region, &layout) else {
        return Err(bad("the work space does not fit the frame"));
    };
    let y = Plane::new(r.y, layout.mb_cols.saturating_mul(16));
    let u = Plane::new(r.u, layout.mb_cols.saturating_mul(8));
    let v = Plane::new(r.v, layout.mb_cols.saturating_mul(8));
    let w = usize::try_from(width).map_err(|_| bad("a width overflow"))?;
    let h = usize::try_from(height).map_err(|_| bad("a height overflow"))?;
    yuv::to_rgba(&y, &u, &v, w, h, alpha, out).ok_or(bad("a buffer too short for the frame"))
}
