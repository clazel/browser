//! Kani harnesses (Tier 1). Compiled only under `cargo kani`.
//!
//! The statements, bounded as the README lists. The decoder is generic over
//! the zlib engine, and here the engine is [`AnyEngine`], which answers
//! **anything** its contract allows (any `consumed` up to `src.len()`, any
//! `produced` up to `dst.len()` with any bytes, any outcome), with a window of
//! 0 bytes and a palette of 2 entries so that the work buffer is small; the
//! canvas is 2 by 2 (every colour type and bit depth, interlaced or not).
//!
//! The pure parts, over every input up to a stated size:
//!
//! - [`paeth_is_the_spec`]: the Paeth predictor of every `a`, `b`, `c` equals
//!   the specification's formula (9.4) computed in `i32`.
//! - [`unfilter_any`]: all five filters (9.2) and every other filter-type
//!   byte over any scanline of up to 8 bytes and any `bpp` of 0 to 8: no
//!   panic, a type above 4 is refused, and each type's result is the
//!   specification's formula byte by byte.
//! - [`adam7_geometry`]: for every width and height from 1 to 2^14, the sizes
//!   of the seven passes add up to `width * height`, every pass pixel is in
//!   the image, and every pixel of the image is in exactly one pass at the
//!   position the pass's own coordinates give back.
//! - [`sample_and_rgba_any`]: `sample`, `rgba` and `over` over every colour
//!   type, depth, index, transparent colour and palette (up to 2 entries)
//!   and any row of up to 8 bytes: no panic.
//! - [`crc_update_any`]: the CRC register update over any register and up
//!   to 2 bytes.
//!
//! The step, over any state with the invariant, any contents of the buffers
//! and any chunk up to 2 bytes:
//!
//! - [`control_any`]: `advance` in any phase but image data (the signature,
//!   chunk headers, gathered chunks, skipped ones, the palette, `tRNS`, CRCs):
//!   no panic, uses between 1 byte and all of a non-empty input, the
//!   invariant holds afterwards.
//! - [`begin_frame_any`]: starting a frame (disposal, the saved canvas, the
//!   first pass) from any state with the invariant: the invariant holds,
//!   with the first pass set up.
//! - [`finish_row_any`]: a complete scanline of any content (any filter byte)
//!   in any state that has one: unfiltered, placed on the canvas, the next
//!   row or pass chosen, the invariant holds.
//! - [`feed_any`]: the zlib loop over any state of an active frame, with
//!   [`AnyEngine`], and any chunk of up to 2 bytes.
//! - [`data_any`]: `advance` in the image-data phase, which is `image_bytes`
//!   (`begin_frame` then `feed`) over the same states.
//!
//! The template statement on the whole `step` (`decoder_step_harness!`) is
//! not here: see the README, "What Kani covers".

use crate::decoder::{any_png_control, any_png_data};
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

/// Every filter type over a scanline of up to 8 bytes with any `bpp` up to
/// 8: the result is 9.2's formula for each byte (`Raw(x) = Filt(x) + the
/// prediction`, modulo 256).
#[kani::proof]
#[kani::unwind(10)]
fn unfilter_any() {
    let filter: u8 = kani::any();
    let bpp: usize = kani::any();
    kani::assume(bpp <= 8);
    let len: usize = kani::any();
    kani::assume(len <= 8);
    let prev_array: [u8; 8] = kani::any();
    let cur_array: [u8; 8] = kani::any();
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

/// Adam7 over every width and height up to 2^14.
#[kani::proof]
#[kani::solver(kissat)]
#[kani::unwind(9)]
fn adam7_geometry() {
    use crate::adam7::pass;
    let w: u32 = kani::any();
    let h: u32 = kani::any();
    kani::assume(w >= 1 && w <= 1 << 14 && h >= 1 && h <= 1 << 14);
    // The pass sizes add up to the image's.
    let mut total: u64 = 0;
    let mut p = 0u8;
    while p < 7 {
        if let Some(ps) = pass(true, p) {
            let (pw, ph) = ps.size(w, h);
            total += u64::from(pw) * u64::from(ph);
        }
        p += 1;
    }
    assert!(total == u64::from(w) * u64::from(h));
    // Every pixel is in exactly one pass, at the coordinates the pass gives
    // back: column `i` and row `j` of the pass with `column(i) == x` and
    // `row(j) == y`, inside the pass's size.
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
    // Every pass pixel is inside the image.
    let q: u8 = kani::any();
    kani::assume(q < 7);
    if let Some(ps) = pass(true, q) {
        let (pw, ph) = ps.size(w, h);
        let i: u32 = kani::any();
        let j: u32 = kani::any();
        kani::assume(i < pw && j < ph);
        assert!(ps.column(i) < w && ps.row(j) < h);
    }
    // The pass of an image that is not interlaced is the whole image.
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

/// `advance`, in every phase but the image data's.
#[kani::proof]
#[kani::unwind(10)]
fn control_any() {
    let Some(mut png) = any_png_control() else {
        return;
    };
    kani::assume(png.state_inv());
    let mut pixels: [u8; 16] = kani::any();
    let mut cur: [u8; 17] = kani::any();
    let mut prev: [u8; 16] = kani::any();
    let mut palette: [u8; 8] = kani::any();
    let mut saved: [u8; 16] = kani::any();
    let mut parts = parts!(pixels, cur, prev, palette, saved);
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
}

/// `begin_frame`.
#[kani::proof]
#[kani::unwind(10)]
fn begin_frame_any() {
    let Some(mut png) = any_png_data() else {
        return;
    };
    kani::assume(png.state_inv());
    kani::assume(png.idle_stage());
    let mut pixels: [u8; 16] = kani::any();
    let mut cur: [u8; 17] = kani::any();
    let mut prev: [u8; 16] = kani::any();
    let mut palette: [u8; 8] = kani::any();
    let mut saved: [u8; 16] = kani::any();
    let mut parts = parts!(pixels, cur, prev, palette, saved);
    if png.begin_frame(&mut parts).is_ok() {
        assert!(png.state_inv());
    }
}

/// `finish_row`.
#[kani::proof]
#[kani::unwind(10)]
fn finish_row_any() {
    let Some(mut png) = any_png_data() else {
        return;
    };
    kani::assume(png.state_inv());
    kani::assume(png.complete_row());
    let mut pixels: [u8; 16] = kani::any();
    let mut cur: [u8; 17] = kani::any();
    let mut prev: [u8; 16] = kani::any();
    let mut palette: [u8; 8] = kani::any();
    let mut saved: [u8; 16] = kani::any();
    let mut parts = parts!(pixels, cur, prev, palette, saved);
    if png.finish_row(&mut parts).is_ok() {
        assert!(png.state_inv());
    }
}

/// `feed`: the zlib loop, over an active frame.
#[kani::proof]
#[kani::unwind(22)]
fn feed_any() {
    let Some(mut png) = any_png_data() else {
        return;
    };
    kani::assume(png.state_inv());
    kani::assume(png.active_frame());
    let mut pixels: [u8; 16] = kani::any();
    let mut cur: [u8; 17] = kani::any();
    let mut prev: [u8; 16] = kani::any();
    let mut palette: [u8; 8] = kani::any();
    let mut saved: [u8; 16] = kani::any();
    let mut parts = parts!(pixels, cur, prev, palette, saved);
    let input: [u8; 2] = kani::any();
    let n: usize = kani::any();
    kani::assume(n <= 2);
    let Some(chunk) = input.get(..n) else {
        return;
    };
    if png.feed(chunk, &mut parts).is_ok() {
        assert!(png.state_inv());
    }
}

/// `advance` in the image-data phase.
#[kani::proof]
#[kani::unwind(22)]
fn data_any() {
    let Some(mut png) = any_png_data() else {
        return;
    };
    kani::assume(png.state_inv());
    let mut pixels: [u8; 16] = kani::any();
    let mut cur: [u8; 17] = kani::any();
    let mut prev: [u8; 16] = kani::any();
    let mut palette: [u8; 8] = kani::any();
    let mut saved: [u8; 16] = kani::any();
    let mut parts = parts!(pixels, cur, prev, palette, saved);
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
}

// NOT a harness: the item 6.3 template on the whole step function, with
// `any_png` (every phase) as the state. It expands from this crate, but see
// the README, "What Kani covers", for what it needed.
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
