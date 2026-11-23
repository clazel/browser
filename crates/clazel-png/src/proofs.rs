//! Kani harnesses (Tier 1). Compiled only under `cargo kani`.
//!
//! The statements, bounded as the README lists. The decoder is generic over
//! the zlib engine, and here the engine is [`AnyEngine`], which answers
//! **anything** its contract allows (any `consumed` up to `src.len()`, any
//! `produced` up to `dst.len()` with any bytes, any outcome), with a window of
//! 0 bytes and a palette of 2 entries so that the work buffer is small; the
//! canvas is 2 by 2 (every colour type and bit depth, interlaced or not).
//!
//! The harnesses (`cargo kani -p clazel-png` runs them all; the README has
//! each one's bound, time and memory):
//!
//! **Pieces**
//! - [`paeth_is_the_spec`]: the Paeth predictor of every `a`, `b`, `c` equals
//!   the specification's formula (9.4) computed in `i32`.
//! - [`unfilter_any`]: all five filters (9.2) and every other filter-type
//!   byte over any scanline of up to 16 bytes (a 2 by 2 canvas's widest) and
//!   any `bpp` of 1 to 8: no panic, a type above 4 is refused, and each
//!   type's result is the specification's formula byte by byte.
//! - [`adam7_pixel_in_one_pass`], [`adam7_pass_pixels_in_image`] and
//!   [`adam7_whole_image`]: for every width and height from 1 to 2^14, every
//!   pixel of the image is in exactly one pass at the position the pass's own
//!   coordinates give back, every pass pixel is in the image, and the pass of
//!   an image that is not interlaced is the whole image.
//!   [`adam7_axis_split`]: the counts along one axis split as the passes
//!   split the pixels (every length to 2^31).
//! - [`sample_and_rgba_any`]: `sample`, `rgba` and `over` over every colour
//!   type, depth, index, transparent colour and palette (up to 8 bytes)
//!   and any row of up to 8 bytes: no panic.
//! - [`crc_update_any`]: the CRC register update over any register and up
//!   to 2 bytes.
//!
//! **The step function, in parts** (the whole `step` does not fit the model
//! checker, as for GIF and WebP). Each harness is one function over any state
//! satisfying `Png::state_inv` in one group of states, any contents of every
//! buffer, and an input of up to 2 bytes; the state is built field by field
//! with the phase (and where the work depends on it the kind of chunk and the
//! stage) a constant, because a symbolic phase keeps every phase's code in
//! the formula (`with_png_at`, `decoder.rs`).
//! - `advance_harness!`: [`advance`](crate::Png::advance) in each phase (and
//!   for the phases whose work depends on the chunk, in each kind): no panic,
//!   at most the input used and at least one byte of a non-empty input, and
//!   `state_inv` afterwards (16 harnesses, `advance_signature` to
//!   `advance_data_finished`).
//! - [`begin_frame_any`]: starting a frame (disposal, the saved canvas, the
//!   first pass): `state_inv` afterwards, with the first pass set up.
//! - The zlib loop of the image data, `feed`, is a loop of rounds
//!   (`feed_once`) and a round is [`engine_round_any`] (the engine's call:
//!   afterwards either the invariant holds with the frame still active or the
//!   scanline is full), then if it is full `finish_row` ([`next_row_any`] the
//!   only part that changes the state, [`unfilter_row_any`] and the ten
//!   `place_row_*` harnesses, one per colour type and blend operation, which
//!   take `&self`), then [`round_end_any`] (what the outcome means).
//!
//! Written, but **not harnesses** (each a `// NOT a harness:` comment block
//! below with its measured reason; Kani 0.68.0 gave no verdict in the time
//! and memory available): `adam7_sizes_add_up`, and the template statement on
//! the whole `step` (`decoder_step_harness!`). Not harnesses by design:
//! `advance` in the data phase with an idle or active frame, which calls the
//! unbounded loop `feed` (the README says how it is covered). See the README,
//! "Kani harnesses".

use crate::decoder::{At, Blend, Flow, with_png_at};
use crate::engine::{Engine, Outcome, Progress};
use crate::filter::{paeth, unfilter};
use crate::pixel::{ColorType, Layout, Trns, over, rgba, sample};
use crate::work::Parts;

/// A zlib engine that does anything its contract allows (`engine.rs`).
pub(crate) struct AnyEngine;

impl Engine for AnyEngine {
    const WINDOW: usize = 0;
    const PALETTE_ENTRIES: usize = 2;

    fn new(_limit: u64) -> AnyEngine {
        AnyEngine
    }

    fn step(&mut self, src: &[u8], dst: &mut [u8], _window: &mut [u8]) -> Progress {
        let consumed: usize = kani::any();
        kani::assume(consumed <= src.len());
        let produced: usize = kani::any();
        kani::assume(produced <= dst.len());
        if let Some(out) = dst.get_mut(..produced) {
            for b in out {
                *b = kani::any();
            }
        }
        let outcome = match kani::any::<u8>() % 4 {
            0 => Outcome::NeedInput,
            1 => Outcome::NeedOutput,
            2 => Outcome::Done,
            _ => Outcome::Failed,
        };
        Progress {
            consumed,
            produced,
            outcome,
        }
    }
}

/// 9.4, word for word, in `i32`.
fn paeth_spec(a: u8, b: u8, c: u8) -> u8 {
    let (a, b, c) = (i32::from(a), i32::from(b), i32::from(c));
    let p = a + b - c;
    let pa = (p - a).abs();
    let pb = (p - b).abs();
    let pc = (p - c).abs();
    let pr = if pa <= pb && pa <= pc {
        a
    } else if pb <= pc {
        b
    } else {
        c
    };
    pr as u8
}

#[kani::proof]
fn paeth_is_the_spec() {
    let (a, b, c): (u8, u8, u8) = (kani::any(), kani::any(), kani::any());
    assert!(paeth(a, b, c) == paeth_spec(a, b, c));
}

/// Every filter type over a scanline of up to 8 bytes with any `bpp` from 1
/// to 8: the result is 9.2's formula for each byte (`Raw(x) = Filt(x) + the
/// prediction`, modulo 256). `bpp` is at least 1 because 9.2 rounds it up to
/// 1 and `Layout::filter_bpp` does `.max(1)` (`src/pixel.rs`), its only
/// caller being `src/decoder/image.rs`.
#[kani::proof]
#[kani::unwind(18)]
fn unfilter_any() {
    let filter: u8 = kani::any();
    let bpp: usize = kani::any();
    kani::assume(bpp >= 1 && bpp <= 8);
    let len: usize = kani::any();
    kani::assume(len <= 16);
    let prev_array: [u8; 16] = kani::any();
    let cur_array: [u8; 16] = kani::any();
    let mut cur = cur_array;
    let (Some(prev), Some(row)) = (prev_array.get(..len), cur.get_mut(..len)) else {
        return;
    };
    let ok = unfilter(filter, bpp, prev, row);
    assert!(ok == (filter <= 4));
    if ok {
        let mut i = 0;
        while i < len {
            let x = cur_array[i];
            let a = if i >= bpp { row[i - bpp] } else { 0 };
            let b = prev[i];
            let c = if i >= bpp { prev[i - bpp] } else { 0 };
            let want = match filter {
                0 => x,
                1 => x.wrapping_add(a),
                2 => x.wrapping_add(b),
                3 => x.wrapping_add(((u16::from(a) + u16::from(b)) / 2) as u8),
                _ => x.wrapping_add(paeth_spec(a, b, c)),
            };
            assert!(row[i] == want);
            i += 1;
        }
    }
}

// NOT a harness: the seven Adam7 pass sizes add up to `width * height`, for every width
// and height from 1 to 2^14. Kani 0.68.0 gave no verdict in 25 minutes with
// cadical, kissat or minisat, so it is not a harness here. Splitting it did
// not help: with the width `8 * a + 3` and the height `8 * b + 5` (the two
// residues fixed, `a` and `b` any up to 2047) kissat had no verdict in 10
// minutes either; the statement is a ring identity (seven products of the
// passes' sizes against one product), which a SAT solver does not find
// without the algebra. What is machine-checked is the counting along one axis
// ([`adam7_axis_split`] below: the even and odd positions are all of them, the
// 0 and 2 modulo 4 are the even ones, the 0 and 4 modulo 8 are the 0 modulo 4
// ones); the sum then follows by the algebra
//
//     (X8_0 + X8_4) * Y8_0 + X4_0 * Y8_4 = X4_0 * (Y8_0 + Y8_4) = X4_0 * Y4_0
//     (X4_0 + X4_2) * Y4_0 + X2_0 * Y4_2 = X2_0 * (Y4_0 + Y4_2) = X2_0 * Y2_0
//     (X2_0 + X2_1) * Y2_0 + X1_0 * Y2_1 = w * (Y2_0 + Y2_1)     = w * h
//
// (`Xs_r` is `axis(w, r, s)`, `Y` the same for `h`, the passes' widths being
// `X8_0, X8_4, X4_0, X4_2, X2_0, X2_1, w` and their heights `Y8_0, Y8_0, Y8_4,
// Y4_0, Y4_2, Y2_0, Y2_1`), which is argued, not machine-checked. It also
// follows from the bijection the three Adam7 harnesses prove.
//
//     /// Adam7 over every width and height up to 2^14, in four harnesses: each
//     /// states one of the four properties over the same inputs (every `w` and `h`
//     /// from 1 to 2^14, and every `x`, `y`, `q`, `i`, `j` the property quantifies
//     /// over), so that no solver call carries all of their multiplications.
//     ///
//     /// The pass sizes add up to the image's.
//     #[kani::proof]
//     #[kani::unwind(9)]
//     fn adam7_sizes_add_up() {
//         use crate::adam7::pass;
//         let w: u32 = kani::any();
//         let h: u32 = kani::any();
//         kani::assume(w >= 1 && w <= 1 << 14 && h >= 1 && h <= 1 << 14);
//         let mut total: u64 = 0;
//         let mut p = 0u8;
//         while p < 7 {
//             if let Some(ps) = pass(true, p) {
//                 let (pw, ph) = ps.size(w, h);
//                 total += u64::from(pw) * u64::from(ph);
//             }
//             p += 1;
//         }
//         assert!(total == u64::from(w) * u64::from(h));
//     }

/// Every pixel is in exactly one pass, at the coordinates the pass gives
/// back: column `i` and row `j` of the pass with `column(i) == x` and
/// `row(j) == y`, inside the pass's size.
#[kani::proof]
#[kani::unwind(9)]
fn adam7_pixel_in_one_pass() {
    use crate::adam7::pass;
    let w: u32 = kani::any();
    let h: u32 = kani::any();
    kani::assume(w >= 1 && w <= 1 << 14 && h >= 1 && h <= 1 << 14);
    let x: u32 = kani::any();
    let y: u32 = kani::any();
    kani::assume(x < w && y < h);
    let mut hits = 0u8;
    let mut p = 0u8;
    while p < 7 {
        if let Some(ps) = pass(true, p) {
            let (pw, ph) = ps.size(w, h);
            if x >= ps.x0 && y >= ps.y0 && (x - ps.x0) % ps.dx == 0 && (y - ps.y0) % ps.dy == 0 {
                hits += 1;
                let i = (x - ps.x0) / ps.dx;
                let j = (y - ps.y0) / ps.dy;
                assert!(i < pw && j < ph);
                assert!(ps.column(i) == x && ps.row(j) == y);
            }
        }
        p += 1;
    }
    assert!(hits == 1);
}

/// Every pass pixel is inside the image.
#[kani::proof]
#[kani::unwind(9)]
fn adam7_pass_pixels_in_image() {
    use crate::adam7::pass;
    let w: u32 = kani::any();
    let h: u32 = kani::any();
    kani::assume(w >= 1 && w <= 1 << 14 && h >= 1 && h <= 1 << 14);
    let q: u8 = kani::any();
    kani::assume(q < 7);
    if let Some(ps) = pass(true, q) {
        let (pw, ph) = ps.size(w, h);
        let i: u32 = kani::any();
        let j: u32 = kani::any();
        kani::assume(i < pw && j < ph);
        assert!(ps.column(i) < w && ps.row(j) < h);
    }
}

/// The pass of an image that is not interlaced is the whole image.
#[kani::proof]
#[kani::unwind(9)]
fn adam7_whole_image() {
    use crate::adam7::pass;
    let w: u32 = kani::any();
    let h: u32 = kani::any();
    kani::assume(w >= 1 && w <= 1 << 14 && h >= 1 && h <= 1 << 14);
    let whole = pass(false, 0);
    assert!(whole.is_some());
    if let Some(ws) = whole {
        assert!(ws.size(w, h) == (w, h));
    }
    assert!(pass(false, 1).is_none() && pass(true, 7).is_none());
}

/// `sample`, `rgba` and `over`.
#[kani::proof]
#[kani::unwind(10)]
fn sample_and_rgba_any() {
    let color = match kani::any::<u8>() % 5 {
        0 => ColorType::Gray,
        1 => ColorType::Rgb,
        2 => ColorType::Indexed,
        3 => ColorType::GrayAlpha,
        _ => ColorType::Rgba,
    };
    let depth: u8 = kani::any();
    kani::assume(color.allows(depth));
    let layout = Layout { color, depth };
    let trns = match kani::any::<u8>() % 3 {
        0 => Trns::None,
        1 => Trns::Gray(kani::any()),
        _ => Trns::Rgb(kani::any(), kani::any(), kani::any()),
    };
    let palette_array: [u8; 8] = kani::any();
    let palette_len: usize = kani::any();
    kani::assume(palette_len <= 8);
    let row_array: [u8; 8] = kani::any();
    let row_len: usize = kani::any();
    kani::assume(row_len <= 8);
    let index: usize = kani::any();
    if let (Some(palette), Some(row)) = (palette_array.get(..palette_len), row_array.get(..row_len))
    {
        let px = rgba(&layout, trns, palette, row, index);
        // A palette pixel not in the palette is opaque black.
        let _ = px;
        let _ = sample(row, kani::any(), kani::any());
    }
    let src: [u8; 4] = kani::any();
    let dst: [u8; 4] = kani::any();
    let out = over(src, dst);
    if src[3] == 255 {
        assert!(out == src);
    }
    if src[3] == 0 {
        assert!(out == dst);
    }
    let bytes: u32 = kani::any();
    let _ = layout.row_bytes(bytes);
    let _ = layout.filter_bpp();
}

#[kani::proof]
#[kani::unwind(19)]
fn crc_update_any() {
    let register: u32 = kani::any();
    let bytes: [u8; 2] = kani::any();
    let n: usize = kani::any();
    kani::assume(n <= 2);
    if let Some(part) = bytes.get(..n) {
        let _ = crate::crc::finish(crate::crc::update(register, part));
    }
}

/// The buffers of a 2 by 2 canvas and an engine of window 0, palette 2.
macro_rules! parts {
    ($pixels:ident, $cur:ident, $prev:ident, $palette:ident, $saved:ident) => {
        Parts {
            pixels: &mut $pixels,
            window: &mut [],
            cur: &mut $cur,
            prev: &mut $prev,
            palette: &mut $palette,
            saved: &mut $saved,
        }
    };
}

/// Binds `$parts` to the buffers of a 2 by 2 canvas holding any contents.
macro_rules! any_parts {
    ($parts:ident) => {
        let mut pixels: [u8; 16] = kani::any();
        let mut cur: [u8; 17] = kani::any();
        let mut prev: [u8; 16] = kani::any();
        let mut palette: [u8; 8] = kani::any();
        let mut saved: [u8; 16] = kani::any();
        let mut $parts = parts!(pixels, cur, prev, palette, saved);
    };
}

/// `advance` over the states of `at`: it uses at most the input and at least
/// one byte of a non-empty input, and keeps `state_inv`. Over any state with
/// the invariant, any contents of the buffers, and an input of up to 2 bytes.
fn advance_any(at: At) {
    with_png_at(at, |png| {
        kani::assume(png.state_inv());
        any_parts!(parts);
        let input: [u8; 2] = kani::any();
        let n: usize = kani::any();
        kani::assume(n <= 2);
        let Some(chunk) = input.get(..n) else {
            return;
        };
        if let Ok((used, _)) = png.advance(chunk, &mut parts) {
            assert!(used <= n);
            assert!(n == 0 || used >= 1);
            assert!(png.state_inv());
        }
    });
}

/// One harness of `advance_any` per state group.
macro_rules! advance_harness {
    ($name:ident, $at:ident) => {
        #[kani::proof]
        #[kani::unwind(10)]
        fn $name() {
            advance_any(At::$at);
        }
    };
}

advance_harness!(advance_signature, Signature);
advance_harness!(advance_header, Header);
advance_harness!(advance_gather_ihdr, GatherIhdr);
advance_harness!(advance_gather_actl, GatherActl);
advance_harness!(advance_gather_fctl, GatherFctl);
advance_harness!(advance_gather_trns, GatherTrns);
advance_harness!(advance_gather_fdat, GatherFdat);
advance_harness!(advance_skip, Skip);
advance_harness!(advance_palette, Palette);
advance_harness!(advance_trns, TrnsData);
advance_harness!(advance_crc_iend, CrcIend);
advance_harness!(advance_crc_data, CrcData);
advance_harness!(advance_crc_other, CrcOther);
advance_harness!(advance_ended, Ended);
advance_harness!(advance_spent, Spent);
advance_harness!(advance_data_finished, DataFinished);

/// `begin_frame`.
#[kani::proof]
#[kani::unwind(10)]
fn begin_frame_any() {
    with_png_at(At::DataIdle, |png| {
        kani::assume(png.state_inv());
        any_parts!(parts);
        if png.begin_frame(&mut parts).is_ok() {
            assert!(png.state_inv());
        }
    });
}

/// `engine_round`, the first part of a round of `feed` (`feed_once`): the
/// engine's call. Over any active frame with the invariant, any buffers and
/// an input of up to 2 bytes: afterwards the state is the same but for the
/// bytes counted, so that either the scanline is not full and the invariant
/// holds with the frame still active, or it is full (`cur` holds its
/// filter-type byte and `row_len` bytes) and the state is what the harnesses
/// of the scanline's parts assume (`complete_row`).
#[kani::proof]
#[kani::unwind(20)]
fn engine_round_any() {
    with_png_at(At::DataActive, |png| {
        kani::assume(png.state_inv());
        any_parts!(parts);
        let input: [u8; 2] = kani::any();
        let n: usize = kani::any();
        kani::assume(n <= 2);
        let Some(chunk) = input.get(..n) else {
            return;
        };
        let mut src = chunk;
        if png.engine_round(&mut src, &mut parts).is_ok() {
            assert!(src.len() <= n);
            if png.row_is_full() {
                assert!(png.full_row_inv());
            } else {
                assert!(png.state_inv() && png.active_frame());
            }
        }
    });
}

/// `round_end`, the last part of a round of `feed`: what the engine's
/// outcome means, for any `Progress` (the engine's contract was checked by
/// `engine_round`), any outcome, and any rest of the input of up to 2 bytes,
/// over any active frame with the invariant (what `finish_row` leaves).
#[kani::proof]
#[kani::unwind(10)]
fn round_end_any() {
    with_png_at(At::DataActive, |png| {
        kani::assume(png.state_inv());
        let input: [u8; 2] = kani::any();
        let n: usize = kani::any();
        kani::assume(n <= 2);
        let Some(rest) = input.get(..n) else {
            return;
        };
        let outcome = match kani::any::<u8>() % 4 {
            0 => Outcome::NeedInput,
            1 => Outcome::NeedOutput,
            2 => Outcome::Done,
            _ => Outcome::Failed,
        };
        let r = Progress {
            consumed: kani::any(),
            produced: kani::any(),
            outcome,
        };
        if let Ok(flow) = png.round_end(r, rest) {
            assert!(png.state_inv());
            if flow == Flow::More {
                assert!(png.active_frame());
            }
        }
    });
}

/// `next_row`, the part of `finish_row` that changes the state: the next
/// scanline or pass, after a scanline is placed. (`unfilter_row` and
/// `place_row` take `&self`: they cannot change it.) Over any active frame
/// with the invariant whose scanline is complete.
#[kani::proof]
#[kani::unwind(10)]
fn next_row_any() {
    with_png_at(At::DataActive, |png| {
        kani::assume(png.state_inv());
        kani::assume(png.complete_row());
        any_parts!(parts);
        png.next_row(&mut parts);
        assert!(png.state_inv() && png.active_frame());
    });
}

/// `unfilter_row`, the filter of a scanline in `cur` against `prev`
/// (`unfilter_any` is the filters themselves): any state with the invariant
/// and a frame being received, any buffers; no panic.
#[kani::proof]
#[kani::unwind(18)]
fn unfilter_row_any() {
    with_png_at(At::DataActive, |png| {
        kani::assume(png.state_inv());
        kani::assume(png.receiving_rows());
        any_parts!(parts);
        let _ = png.unfilter_row(&mut parts);
    });
}

/// `place_row`: a scanline's pixels converted and blended into the canvas,
/// over any active frame with the invariant being received, any buffers; no
/// panic. One harness per colour type and blend operation (the colour type
/// and the blend are set, the bit depth and everything else are symbolic):
/// the pixel conversions were too large together.
macro_rules! place_row_harness {
    ($name:ident, $color:ident, $blend:ident) => {
        #[kani::proof]
        #[kani::unwind(10)]
        fn $name() {
            with_png_at(At::DataActive, |png| {
                png.set_color(ColorType::$color);
                png.set_blend(Blend::$blend);
                kani::assume(png.state_inv());
                kani::assume(png.receiving_rows());
                any_parts!(parts);
                let _ = png.place_row(&mut parts);
            });
        }
    };
}

place_row_harness!(place_row_gray_source, Gray, Source);
place_row_harness!(place_row_gray_over, Gray, Over);
place_row_harness!(place_row_rgb_source, Rgb, Source);
place_row_harness!(place_row_rgb_over, Rgb, Over);
place_row_harness!(place_row_indexed_source, Indexed, Source);
place_row_harness!(place_row_indexed_over, Indexed, Over);
place_row_harness!(place_row_gray_alpha_source, GrayAlpha, Source);
place_row_harness!(place_row_gray_alpha_over, GrayAlpha, Over);
place_row_harness!(place_row_rgba_source, Rgba, Source);
place_row_harness!(place_row_rgba_over, Rgba, Over);

/// The counts along one axis split as the passes split the pixels: of the
/// pixels `0, 1, 2, ...` of a row of `len`, the even and the odd ones are all
/// of them; of the even ones, those that are 0 and 2 modulo 4 are all of
/// them; of the 0 modulo 4 ones, those that are 0 and 4 modulo 8 are all of
/// them. (`axis` is the number of a pass's pixels along one axis.)
#[kani::proof]
fn adam7_axis_split() {
    use crate::adam7::axis;
    let len: u32 = kani::any();
    kani::assume(len <= 1 << 31);
    assert!(axis(len, 0, 2) + axis(len, 1, 2) == len);
    assert!(axis(len, 0, 4) + axis(len, 2, 4) == axis(len, 0, 2));
    assert!(axis(len, 0, 8) + axis(len, 4, 8) == axis(len, 0, 4));
}

// NOT a harness: the item 6.3 template on the whole step function, with every
// phase as the state. It expands from this crate, but the model checker does
// not finish the whole step (GIF's experience, item 6.7, and the same here
// for its parts before they were split); `step` is `Parts::new` and a loop of
// `advance`, which the harnesses above cover phase by phase.
//
//     clazel_image_shape::decoder_step_harness! {
//         #[kani::proof]
//         #[kani::unwind(22)]
//         #[kani::solver(kissat)]
//         fn step_any for crate::Png<AnyEngine> {
//             max_chunk: 1,
//             max_pixels: 16,
//             max_work: 57,
//             any_state: any_png,
//         }
//     }
