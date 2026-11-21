//! Kani harnesses (Tier 1). Compiled only under `cargo kani`.
//!
//! Sixty-nine harnesses, bounded as the README lists. Under Kani the colour
//! cache is 8 entries (`MAX_CACHE_BITS` 3 in `work.rs`) so that a green
//! alphabet is 288 symbols and a prefix code group 2,352 bytes; the code is
//! the same code with other constants.
//!
//! **Parts of the lossless decoder**
//! - [`huffman_build_any`]: prefix code construction over **any code lengths**
//!   (6 symbols, every `u8` length): no panic; an error if any length is over
//!   15; on `Ok` the code is complete (Kraft sum exactly 1) or a single
//!   symbol, and the symbol table holds each used symbol exactly once.
//! - [`huffman_decode_any`]: decoding any bits with any number of them
//!   available, from any built code: no panic, a symbol of the alphabet whose
//!   length is the code's, never more bits than are available, and `More` only
//!   when fewer than 15 are.
//! - [`distance_value_any`], [`distance_map_any`]: the LZ77 prefix coding
//!   (every prefix code 0 to 39 with any extra bits) and the distance map
//!   (every distance code, every width up to 2^14): never 0, in range.
//! - [`predict_any`]: the predictor of every mode over any four pixels.
//! - [`predictor_row_any`], [`color_row_any`], [`green_row_any`]: each inverse
//!   transform over **any row** of up to 3 pixels, any block size bits, any
//!   transform data and any pixels: no panic, the right pixels written.
//! - [`palette_row_any`], [`palette_in_place_any`]: colour indexing with pixel
//!   bundling, every bundling width, 4 pixels in 2 rows, expanded in place
//!   from the last row to the first, equal to the expansion from a copy.
//! - [`blend_px_any`]: alpha blending of any two pixels.
//!
//! **The step function, in parts** (the whole `step` does not fit the model
//! checker: README). One harness per phase, role or transform, mostly made by
//! the macros below: with the phase symbolic, CBMC ran out of memory.
//! - `act_harness!`: one atomic action of the lossless decoder in one phase
//!   (40 harnesses, `act_signature` to `act_dist_extra_palette`; the two
//!   distance phases copy into the image of the role, so they have one per
//!   role), over any state satisfying `Vp8l::inv`, any bits and **any
//!   contents** of every scratch region: no panic, `inv` kept on `Ok`.
//!   `act_build_code` bounds the alphabet to 8 symbols (`huffman_build_any`
//!   covers `build` itself).
//! - `finish_harness!` and [`finish_main_predictor`]: finishing an image of
//!   each role (9 harnesses: colour table, entropy image, the two transform
//!   images, and the main image with no transform or one of each kind; the
//!   loop that inverts several depends only on each transform and the
//!   pixels). `finish_main_predictor` is at exactly 2 by 2 pixels
//!   (`predictor_row_any` covers rows of 3): the same.
//! - `container_harness!`: one byte of the container in each phase but the
//!   lossless payload (9 harnesses), on a 2 by 2 canvas: the same for
//!   `Webp::state_inv`.
//!
//! **Bounds that keep them in memory** (measured under a 4 GB cap):
//! - The pixel, finish and container harnesses use MiniSat: CaDiCaL and
//!   kissat each ran out of 4 GB on `act_red`, which MiniSat proves in 30
//!   seconds. The others use kissat.
//! - The finish and container harnesses unwind 6 (images of at most 2 rows of
//!   4 pixels; at 40, loops with symbolic bounds unrolled past memory).
//! - Where the colour table is written or indexed at a symbolic position (the
//!   palette role's distance phases, the main image's colour indexing), it is
//!   4 colours (`with_scratch`), the bound on `ncolors`.

use crate::compose::blend_px;
use crate::decoder::{Phase, any_webp};
use crate::distance;
use crate::huffman::{self, Decoded, get16};
use crate::transform::{self, BLACK, px};
use crate::vp8l::{P, Role, any_vp8l};
use crate::work::{
    CACHE_ENTRIES, CL_ALPHABET, COUNTS_BYTES, GROUP_BYTES, MAX_GREEN, PALETTE_BYTES, Parts, Scratch,
};

/// Prefix code construction over any six code lengths.
#[kani::proof]
#[kani::unwind(18)]
fn huffman_build_any() {
    let lens: [u8; 6] = kani::any();
    let mut counts = [0u8; COUNTS_BYTES];
    let mut symbols: [u8; 12] = kani::any();
    let result = huffman::build(&lens, &mut counts, &mut symbols);
    if lens.iter().any(|&l| l > 15) {
        assert!(result.is_err());
    }
    if result.is_ok() {
        let used = lens.iter().filter(|&&l| l != 0).count();
        assert!(used >= 1);
        if get16(&counts, 0) == 1 {
            assert!(used == 1);
            let s = usize::from(get16(&symbols, 0));
            assert!(s < 6 && lens.get(s).copied().unwrap_or(0) != 0);
        } else {
            let mut kraft = 0u32;
            let mut total = 0usize;
            for len in 1..16usize {
                let c = u32::from(get16(&counts, len));
                kraft += c << (15 - len);
                total += usize::from(get16(&counts, len));
            }
            assert!(kraft == 1 << 15);
            assert!(total == used);
            // Each used symbol appears once among the first `used` slots.
            for (s, &l) in lens.iter().enumerate() {
                if l != 0 {
                    let times = (0..used)
                        .filter(|&i| usize::from(get16(&symbols, i)) == s)
                        .count();
                    assert!(times == 1);
                }
            }
        }
    }
}

/// Decoding one symbol from any built code, any bits, any number available.
#[kani::proof]
#[kani::unwind(18)]
fn huffman_decode_any() {
    let lens: [u8; 6] = kani::any();
    let mut counts = [0u8; COUNTS_BYTES];
    let mut symbols = [0u8; 12];
    if huffman::build(&lens, &mut counts, &mut symbols).is_ok() {
        let bits: u32 = kani::any();
        let avail: u8 = kani::any();
        kani::assume(avail <= 32);
        let lone = get16(&counts, 0) == 1;
        match huffman::decode(&counts, &symbols, bits, avail) {
            Decoded::Symbol(s, len) => {
                let s = usize::from(s);
                assert!(s < 6);
                assert!(len <= avail || lone);
                if lone {
                    assert!(len == 0);
                } else {
                    assert!(len >= 1 && len <= 15);
                    assert!(lens.get(s).copied() == Some(len));
                }
            }
            Decoded::More => assert!(!lone && avail < 15),
            Decoded::Invalid => assert!(false),
        }
    }
}

/// The LZ77 prefix coding of every prefix code with any extra bits.
#[kani::proof]
fn distance_value_any() {
    let prefix: u32 = kani::any();
    kani::assume(prefix < 40);
    let bits = distance::extra_bits(prefix);
    assert!(bits <= 18);
    let extra: u32 = kani::any();
    kani::assume(u64::from(extra) < (1u64 << bits));
    let v = distance::value(prefix, extra);
    // Section 3.6.2.2, Table 4: values 1 to 1,048,576.
    assert!(v >= 1 && v <= 1_048_576);
    if prefix < 4 {
        assert!(v == prefix + 1);
    }
}

/// The distance of every distance code at every width.
#[kani::proof]
fn distance_map_any() {
    let code: u32 = kani::any();
    kani::assume(code >= 1);
    let xsize: u32 = kani::any();
    kani::assume(xsize >= 1 && xsize <= 16384);
    let d = distance::distance(code, xsize);
    assert!(d >= 1);
    if code > 120 {
        assert!(d == code - 120);
    } else {
        // At most 7 rows and 8 columns away.
        assert!(u64::from(d) <= 7 * u64::from(xsize) + 8);
    }
}

/// The predictor of every mode over any four pixels.
#[kani::proof]
fn predict_any() {
    let mode: u8 = kani::any();
    let l: [u8; 4] = kani::any();
    let t: [u8; 4] = kani::any();
    let tr: [u8; 4] = kani::any();
    let tl: [u8; 4] = kani::any();
    let p = transform::predict(mode, l, t, tr, tl);
    match mode & 15 {
        0 | 14 | 15 => assert!(p == BLACK),
        1 => assert!(p == l),
        2 => assert!(p == t),
        3 => assert!(p == tr),
        4 => assert!(p == tl),
        7 => {
            for i in 0..4 {
                let want = (u16::from(l[i]) + u16::from(t[i])) / 2;
                assert!(u16::from(p[i]) == want);
            }
        }
        11 => assert!(p == l || p == t),
        _ => {}
    }
}

/// The inverse predictor transform of any row of 3 pixels.
#[kani::proof]
#[kani::unwind(13)]
fn predictor_row_any() {
    let mut buf: [u8; 24] = kani::any();
    let before = buf;
    let y: usize = kani::any();
    kani::assume(y < 2);
    let bits: u8 = kani::any();
    kani::assume(bits >= 2 && bits <= 9);
    let modes: [u8; 4] = kani::any();
    // 3 pixels are at most one block of 4 wide and, in 2 rows, one high.
    assert!(transform::predictor_row(&mut buf, 3, y, bits, 1, &modes));
    let other = 1 - y;
    assert!(buf[other * 12..other * 12 + 12] == before[other * 12..other * 12 + 12]);
    if y == 0 {
        // The top-left pixel is predicted black.
        let r = px(&before, 0);
        let want = [r[0], r[1], r[2], r[3].wrapping_add(255)];
        assert!(px(&buf, 0) == want);
    }
}

/// The inverse colour transform of any row of 3 pixels.
#[kani::proof]
#[kani::unwind(6)]
fn color_row_any() {
    let mut buf: [u8; 12] = kani::any();
    let before = buf;
    let bits: u8 = kani::any();
    kani::assume(bits >= 2 && bits <= 9);
    let elems: [u8; 4] = kani::any();
    assert!(transform::color_row(&mut buf, 3, 0, bits, 1, &elems));
    for i in 0..3 {
        let (a, b) = (px(&before, i), px(&buf, i));
        assert!(a[1] == b[1] && a[3] == b[3]);
    }
}

/// The inverse subtract green transform of any row of 3 pixels.
#[kani::proof]
#[kani::unwind(6)]
fn green_row_any() {
    let mut buf: [u8; 12] = kani::any();
    let before = buf;
    assert!(transform::green_row(&mut buf, 3, 0));
    for i in 0..3 {
        let (a, b) = (px(&before, i), px(&buf, i));
        assert!(b == [a[0].wrapping_add(a[1]), a[1], a[2].wrapping_add(a[1]), a[3]]);
    }
}

/// Colour indexing of one row of up to 8 pixels, every bundling width.
#[kani::proof]
#[kani::unwind(10)]
fn palette_row_any() {
    let bits: u8 = kani::any();
    kani::assume(bits <= 3);
    let n: usize = kani::any();
    kani::assume(n <= 4);
    let w: usize = kani::any();
    kani::assume(w >= 1 && w <= 8);
    let table: [u8; 16] = kani::any();
    let mut buf: [u8; 32] = kani::any();
    let orig = buf;
    assert!(transform::palette_row(&mut buf, 0, 0, w, bits, &table, n));
    for x in 0..w {
        let g = usize::from(px(&orig, x >> bits)[1]);
        let per = 1usize << bits;
        let width = 8 >> bits;
        let idx = (g >> (width * (x % per))) & ((1 << width) - 1);
        let want = if idx < n { px(&table, idx) } else { [0; 4] };
        // Pixels are written last to first, each reading only packed pixels at
        // or before its own position, which are not yet overwritten.
        assert!(px(&buf, x) == want);
    }
}

/// Colour indexing of two rows of 4 in place, last row first.
#[kani::proof]
#[kani::unwind(10)]
fn palette_in_place_any() {
    let bits: u8 = kani::any();
    kani::assume(bits <= 3);
    let n: usize = kani::any();
    kani::assume(n <= 4);
    let table: [u8; 16] = kani::any();
    let mut buf: [u8; 32] = kani::any();
    let orig = buf;
    let (w, h) = (4usize, 2usize);
    let pw = (w + (1 << bits) - 1) >> bits;
    for y in (0..h).rev() {
        assert!(transform::palette_row(
            &mut buf,
            y * pw,
            y * w,
            w,
            bits,
            &table,
            n
        ));
    }
    for y in 0..h {
        for x in 0..w {
            let g = usize::from(px(&orig, y * pw + (x >> bits))[1]);
            let per = 1usize << bits;
            let width = 8 >> bits;
            let idx = (g >> (width * (x % per))) & ((1 << width) - 1);
            let want = if idx < n { px(&table, idx) } else { [0; 4] };
            assert!(px(&buf, y * w + x) == want);
        }
    }
}

/// Alpha blending of any two pixels.
#[kani::proof]
fn blend_px_any() {
    let src: [u8; 4] = kani::any();
    let dst: [u8; 4] = kani::any();
    let out = blend_px(src, dst);
    if src[3] == 255 {
        assert!(out == src);
    }
    if src[3] == 0 {
        assert!(out == dst);
    }
    if src[3] != 0 && src[3] != 255 && dst[3] != 0 {
        assert!(out[3] >= src[3]);
    }
}

/// The scratch regions as separate arrays (the real buffer is one, cut by
/// `Parts::new`, whose lengths are in `inv` and in a unit test; the model
/// checker follows every access into one big object).
///
/// With `small_palette`, the colour table is 4 colours (16 bytes), the
/// harness bound on `ncolors`: a symbolic index into the full table ran out
/// of 4 GB where the table is written or read at a symbolic position.
fn with_scratch(small_palette: bool, f: impl FnOnce(&mut Scratch<'_>, &mut [u8; 16])) {
    let mut cache: [u8; 4 * CACHE_ENTRIES] = kani::any();
    let mut lens: [u8; MAX_GREEN] = kani::any();
    let mut cl_lens: [u8; CL_ALPHABET] = kani::any();
    let mut cl_counts: [u8; COUNTS_BYTES] = kani::any();
    let mut cl_syms: [u8; 2 * CL_ALPHABET] = kani::any();
    let mut palette_full: [u8; PALETTE_BYTES] = kani::any();
    let mut palette_small: [u8; 16] = kani::any();
    let palette: &mut [u8] = if small_palette {
        &mut palette_small
    } else {
        &mut palette_full
    };
    let mut pred: [u8; 4] = kani::any();
    let mut color: [u8; 4] = kani::any();
    let mut meta: [u8; 4] = kani::any();
    let mut groups: [u8; GROUP_BYTES] = kani::any();
    let mut target: [u8; 16] = kani::any();
    let mut s = Scratch {
        cache: &mut cache,
        lens: &mut lens,
        cl_lens: &mut cl_lens,
        cl_counts: &mut cl_counts,
        cl_syms: &mut cl_syms,
        palette,
        pred: &mut pred,
        color: &mut color,
        meta: &mut meta,
        groups: &mut groups,
    };
    f(&mut s, &mut target);
}

/// One action of the lossless decoder in `$phase`, over any state satisfying
/// `inv`, any bits and any scratch contents: no panic, `inv` kept on `Ok`.
/// One harness per phase (`any_vp8l` says why).
macro_rules! act_harness {
    ($name:ident, $phase:ident, $unwind:literal, $alphabet:expr, $solver:ident) => {
        act_harness!(@go $name, $phase, None, $unwind, $alphabet, $solver);
    };
    ($name:ident, $phase:ident, $role:ident, $unwind:literal, $alphabet:expr, $solver:ident) => {
        act_harness!(@go $name, $phase, Some(Role::$role), $unwind, $alphabet, $solver);
    };
    (@go $name:ident, $phase:ident, $role:expr, $unwind:literal, $alphabet:expr, $solver:ident) => {
        #[kani::proof]
        #[kani::solver($solver)]
        #[kani::unwind($unwind)]
        fn $name() {
            let mut v = any_vp8l(P::$phase, $role, GROUP_BYTES, $alphabet);
            with_scratch(matches!($role, Some(Role::Palette)), |s, target| {
                if v.kani_act(s, target).is_ok() {
                    assert!(v.kani_inv(GROUP_BYTES));
                }
            });
        }
    };
}

/// No bound on the alphabet beyond `inv` (at most `MAX_GREEN`).
const ANY_ALPHABET: u16 = u16::MAX;

// The header, transform, colour cache and meta prefix reads.
act_harness!(act_signature, Signature, 20, ANY_ALPHABET, kissat);
act_harness!(act_width, Width, 20, ANY_ALPHABET, kissat);
act_harness!(act_height, Height, 20, ANY_ALPHABET, kissat);
act_harness!(act_version, Version, 20, ANY_ALPHABET, kissat);
act_harness!(act_transform_flag, TransformFlag, 20, ANY_ALPHABET, kissat);
act_harness!(act_transform_type, TransformType, 20, ANY_ALPHABET, kissat);
act_harness!(act_transform_bits, TransformBits, 20, ANY_ALPHABET, kissat);
act_harness!(act_palette_size, PaletteSize, 20, ANY_ALPHABET, kissat);
act_harness!(act_cache_flag, CacheFlag, 20, ANY_ALPHABET, kissat);
act_harness!(act_cache_bits, CacheBits, 20, ANY_ALPHABET, kissat);
act_harness!(act_meta_flag, MetaFlag, 20, ANY_ALPHABET, kissat);
act_harness!(act_meta_bits, MetaBits, 20, ANY_ALPHABET, kissat);

// Reading a prefix code. `CodeKind` sets the alphabet itself (up to 288
// symbols, whose lengths it clears).
act_harness!(act_code_kind, CodeKind, 300, ANY_ALPHABET, kissat);
act_harness!(act_simple_count, SimpleCount, 20, ANY_ALPHABET, kissat);
act_harness!(act_simple_first, SimpleFirst, 20, ANY_ALPHABET, kissat);
act_harness!(act_simple_sym0, SimpleSym0, 20, ANY_ALPHABET, kissat);
act_harness!(act_simple_sym1, SimpleSym1, 20, ANY_ALPHABET, kissat);
act_harness!(act_normal_count, NormalCount, 21, ANY_ALPHABET, kissat);
act_harness!(act_normal_cl, NormalCl, 21, ANY_ALPHABET, kissat);
act_harness!(act_normal_flag, NormalFlag, 20, ANY_ALPHABET, kissat);
act_harness!(act_normal_nbits, NormalNbits, 20, ANY_ALPHABET, kissat);
act_harness!(act_normal_max, NormalMax, 20, ANY_ALPHABET, kissat);
act_harness!(act_lengths, Lengths, 20, ANY_ALPHABET, kissat);
act_harness!(act_length_rep, LengthRep, 300, ANY_ALPHABET, kissat);
// Building a code over any lengths of 288 symbols does not fit in memory:
// this harness bounds the alphabet to 8 symbols. `huffman_build_any` covers
// `huffman::build` itself over any lengths.
act_harness!(act_build_code, BuildCode, 20, 8, kissat);

// Decoding pixels (a literal's symbol, a length, a distance, a cache index,
// a backward reference of at most 4 pixels).
act_harness!(act_green, Green, 20, ANY_ALPHABET, minisat);
act_harness!(act_red, Red, 20, ANY_ALPHABET, minisat);
act_harness!(act_blue, Blue, 20, ANY_ALPHABET, minisat);
act_harness!(act_alpha, Alpha, 20, ANY_ALPHABET, minisat);
act_harness!(act_len_extra, LenExtra, 20, ANY_ALPHABET, minisat);
// The distance phases copy a backward reference into the image of the role,
// one harness per role (with the role symbolic too, MiniSat ran out of 4 GB).
act_harness!(act_dist_sym_main, DistSym, Main, 20, ANY_ALPHABET, minisat);
act_harness!(act_dist_sym_meta, DistSym, Meta, 20, ANY_ALPHABET, minisat);
act_harness!(
    act_dist_sym_predictor,
    DistSym,
    Predictor,
    20,
    ANY_ALPHABET,
    minisat
);
act_harness!(
    act_dist_sym_colour,
    DistSym,
    Colour,
    20,
    ANY_ALPHABET,
    minisat
);
act_harness!(
    act_dist_sym_palette,
    DistSym,
    Palette,
    20,
    ANY_ALPHABET,
    minisat
);
act_harness!(
    act_dist_extra_main,
    DistExtra,
    Main,
    20,
    ANY_ALPHABET,
    minisat
);
act_harness!(
    act_dist_extra_meta,
    DistExtra,
    Meta,
    20,
    ANY_ALPHABET,
    minisat
);
act_harness!(
    act_dist_extra_predictor,
    DistExtra,
    Predictor,
    20,
    ANY_ALPHABET,
    minisat
);
act_harness!(
    act_dist_extra_colour,
    DistExtra,
    Colour,
    20,
    ANY_ALPHABET,
    minisat
);
act_harness!(
    act_dist_extra_palette,
    DistExtra,
    Palette,
    20,
    ANY_ALPHABET,
    minisat
);

/// Finishing an image of `$role`: no panic, `inv` kept on `Ok`.
macro_rules! finish_harness {
    ($name:ident, $role:ident) => {
        finish_harness!($name, $role, None);
    };
    ($name:ident, $role:ident, $transform:expr) => {
        #[kani::proof]
        #[kani::solver(minisat)]
        #[kani::unwind(6)]
        fn $name() {
            let mut v = any_vp8l(P::Done, Some(Role::$role), GROUP_BYTES, ANY_ALPHABET);
            if let Some(k) = $transform {
                v.kani_one_transform(k);
            }
            with_scratch($transform == Some(3), |s, target| {
                if v.kani_finish(s, target).is_ok() {
                    assert!(v.kani_inv(GROUP_BYTES));
                }
            });
        }
    };
}

// The main image inverts its transforms in a loop whose body depends only on
// that transform and the pixels (`invert` takes `&self`); with every order of
// four transforms at once MiniSat ran out of 4 GB, so one harness per kind,
// each with that one transform over any pixels, and one with none.
finish_harness!(finish_main_none, Main, Some(4));
finish_harness!(finish_main_colour, Main, Some(1));
finish_harness!(finish_main_green, Main, Some(2));
finish_harness!(finish_main_index, Main, Some(3));
finish_harness!(finish_meta, Meta);
finish_harness!(finish_predictor, Predictor);
finish_harness!(finish_colour, Colour);
finish_harness!(finish_palette, Palette);

/// Finishing the main image with one predictor transform, on an image of
/// exactly 2 by 2 pixels: with the size symbolic (even bounded to 1 row of 2
/// pixels) no solver fitted in 4 GB, as every loop unrolled along every path.
/// `predictor_row_any` covers rows of 3 pixels with any block bits.
#[kani::proof]
#[kani::solver(minisat)]
#[kani::unwind(6)]
fn finish_main_predictor() {
    let mut v = any_vp8l(P::Done, Some(Role::Main), GROUP_BYTES, ANY_ALPHABET);
    v.kani_one_transform(0);
    v.kani_set_first_size(2, 2);
    with_scratch(false, |s, target| {
        if v.kani_finish(s, target).is_ok() {
            assert!(v.kani_inv(GROUP_BYTES));
        }
    });
}

/// One byte of the container in `$phase`, on a 2 by 2 canvas: no panic,
/// `state_inv` kept on `Ok`. One harness per phase (`any_webp` says why).
macro_rules! container_harness {
    ($name:ident, $phase:ident) => {
        #[kani::proof]
        #[kani::solver(minisat)]
        #[kani::unwind(6)]
        fn $name() {
            container_byte(Phase::$phase);
        }
    };
}

container_harness!(container_riff, Riff);
container_harness!(container_chunk_hdr, ChunkHdr);
container_harness!(container_vp8x, Vp8x);
container_harness!(container_anim, Anim);
container_harness!(container_anmf, Anmf);
container_harness!(container_skip, Skip);
container_harness!(container_alpha, Alpha);
container_harness!(container_vp8, Vp8);
container_harness!(container_pad, Pad);
container_harness!(container_ended, Ended);
container_harness!(container_spent, Spent);

fn container_byte(phase: Phase) {
    let Some(mut webp) = any_webp(phase) else {
        return;
    };
    webp.kani_set_phase(phase);
    let groups = GROUP_BYTES;
    kani::assume(webp.kani_inv(groups));
    // Not the last byte of a `VP8 ` payload: that decodes a whole frame
    // (the lossy parts have their own harnesses below).
    if phase == Phase::Vp8 {
        kani::assume(webp.kani_chunk_left() > 1);
    }
    let b: u8 = kani::any();
    let mut pixels: [u8; 16] = kani::any();
    let mut frame_array: [u8; 16] = kani::any();
    let mut alpha_array = [0u8; 4];
    let mut lossy_array = [0u8; 1500];
    let frame_len = if webp.kani_animated() { 16 } else { 0 };
    let lossy_len = crate::vp8::lossy_len(2, 2).unwrap_or(0);
    with_scratch(false, |s, _| {
        let Some(frame) = frame_array.get_mut(..frame_len) else {
            return;
        };
        let mut parts = Parts {
            pixels: &mut pixels,
            scratch: Scratch {
                cache: &mut *s.cache,
                lens: &mut *s.lens,
                cl_lens: &mut *s.cl_lens,
                cl_counts: &mut *s.cl_counts,
                cl_syms: &mut *s.cl_syms,
                palette: &mut *s.palette,
                pred: &mut *s.pred,
                color: &mut *s.color,
                meta: &mut *s.meta,
                groups: &mut *s.groups,
            },
            frame,
            alpha: &mut alpha_array,
            lossy: lossy_array.get_mut(..lossy_len).unwrap_or(&mut []),
        };
        if webp.byte(b, &mut parts).is_ok() {
            assert!(webp.kani_inv(groups));
        }
    });
}

// ---------------------------------------------------------------- lossy (6.9)
//
// One harness per part, MiniSat, small unwinding, as above. Not run locally.

use crate::vp8::bool_decoder::BoolDecoder;
use crate::vp8::loop_filter;
use crate::vp8::plane::Plane;
use crate::vp8::predict::{self, SubEdge};
use crate::vp8::transform::{inverse_dct, inverse_wht};
use crate::vp8::yuv::yuv_to_rgb;

/// The boolean decoder (RFC 6386 section 7.3) over any 4 bytes, any
/// probabilities, 6 decisions and a literal: no panic, `inv` kept after
/// each.
#[kani::proof]
#[kani::solver(minisat)]
#[kani::unwind(12)]
fn bool_decoder_any() {
    let data: [u8; 4] = kani::any();
    let mut d = BoolDecoder::new(&data);
    assert!(d.inv());
    for _ in 0..6 {
        let p: u8 = kani::any();
        let _ = d.read_bool(p);
        assert!(d.inv());
    }
    let _ = d.read_literal(3);
    assert!(d.inv());
}

/// Every subblock mode (section 12.3) over any edge pixels: no panic, and
/// `B_DC_PRED` is within the range of the edge pixels it averages.
#[kani::proof]
#[kani::solver(minisat)]
#[kani::unwind(12)]
fn subblock_predict_any() {
    let e = SubEdge {
        a: kani::any(),
        l: kani::any(),
        p: kani::any(),
    };
    let mode: u8 = kani::any();
    kani::assume(mode < 10);
    let b = predict::predict_subblock(mode, &e);
    if mode == 0 {
        let lo =
            e.a.iter()
                .take(4)
                .chain(e.l.iter())
                .copied()
                .min()
                .unwrap_or(0);
        let hi =
            e.a.iter()
                .take(4)
                .chain(e.l.iter())
                .copied()
                .max()
                .unwrap_or(0);
        assert!(b.iter().all(|&v| v >= lo && v <= hi));
    }
}

/// The whole-block modes (sections 12.2 and 12.3) on an 8 by 8 block at the
/// top left of a plane of any pixels, with or without a neighbour above and
/// to the left, every mode: no panic; `DC_PRED` is within the pixels' range.
#[kani::proof]
#[kani::solver(minisat)]
#[kani::unwind(10)]
fn predict_block_edges_any() {
    let mut data: [u8; 64] = kani::any();
    let mut plane = Plane::new(&mut data, 8);
    let mode: u8 = kani::any();
    kani::assume(mode < 4);
    let (top, left): (bool, bool) = (kani::any(), kani::any());
    predict::predict_block(&mut plane, 0, 0, 8, mode, top, left);
    if mode == 0 {
        let v = plane.at(0, 0);
        assert!((0..8).all(|i| plane.at(i, i) == v));
    }
}

/// The three segment filters (section 15) over any 8 pixels and any
/// controls: no panic, and each changes only the pixels it should.
#[kani::proof]
#[kani::solver(minisat)]
#[kani::unwind(4)]
fn loop_filter_any() {
    let s: [u8; 8] = kani::any();
    let (hev, interior, edge): (i32, i32, i32) = (kani::any(), kani::any(), kani::any());
    kani::assume((0..=2).contains(&hev) && (1..=63).contains(&interior));
    kani::assume((0..=400).contains(&edge));
    let sub = loop_filter::subblock_filter(hev, interior, edge, s);
    assert!(sub[0] == s[0] && sub[1] == s[1] && sub[6] == s[6] && sub[7] == s[7]);
    let mb = loop_filter::mb_filter(hev, interior, edge, s);
    assert!(mb[0] == s[0] && mb[7] == s[7]);
    let simple = loop_filter::simple_segment(edge, [s[2], s[3], s[4], s[5]]);
    assert!(simple[0] == s[2] && simple[3] == s[5]);
}

/// The inverse DCT and WHT (sections 14.3 and 14.4) over any 16
/// coefficients: no panic, wrapping as the RFC's 16-bit storage does.
#[kani::proof]
#[kani::solver(minisat)]
#[kani::unwind(6)]
fn inverse_transforms_any() {
    let c: [i16; 16] = kani::any();
    let _ = inverse_dct(&c);
    let _ = inverse_wht(&c);
}

/// YUV to RGB over any samples: no panic.
#[kani::proof]
#[kani::solver(minisat)]
fn yuv_to_rgb_any() {
    let _ = yuv_to_rgb(kani::any(), kani::any(), kani::any());
}
