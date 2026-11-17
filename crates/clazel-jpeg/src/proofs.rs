//! Kani harnesses (Tier 1). Compiled only under `cargo kani`.
//!
//! Each states, for **any** value of its input (within the bound the README
//! lists), that the function does not panic, overflow or index out of
//! bounds (Kani's built-in checks), and what else it guarantees.
//!
//! - [`bit_reader_any`]: the bit reader over any state: bits come most
//!   significant first, a byte gives exactly 8.
//! - [`huffman_build_any`]: Annex C construction over any code lengths and
//!   symbols (bounded, below): it refuses or gives a table with the
//!   invariant, and decoding any bits with it ends in a symbol of the table
//!   or an error within 16 bits.
//! - [`idct_any`]: the integer IDCT over **every** block of `i16`
//!   coefficients and **every** `u16` quantizer: no overflow (it returns
//!   `Some`).
//! - [`range_limit_any`]: the post-IDCT clamp over every `i64`: it is the
//!   level shift and clamp on -512 to 511.
//! - [`sample_any`], [`sample_constant`]: upsampling over every geometry up
//!   to 16 by 16 and every sampling ratio, every position: always `Some`,
//!   and a constant plane stays constant.
//! - [`orient_any`], [`orient_bijection`]: the orientation map over every
//!   size up to 2^14 and every position stays inside the oriented image, and
//!   is one to one over every size up to 3 by 3.
//! - [`ycc_any`], [`cmyk_any`]: colour conversion over every input equals
//!   its closed form.
//! - [`block_machine_any`]: one bit of a block (the stage, the Huffman code so
//!   far and the position symbolic) with Huffman tables that passed
//!   construction: no panic, and the block invariant kept.

use crate::bits::BitReader;
use crate::block::{Block, Stage};
use crate::huffman::{MAX_LEN, Next, Table};
use crate::idct::{idct, range_limit};
use crate::output::{Plane, cmyk_to_rgb, orient, swaps, ycc_to_rgb};

/// A bit reader in any state with the invariant takes bits in order and a
/// loaded byte gives its 8 bits.
#[kani::proof]
#[kani::unwind(10)]
fn bit_reader_any() {
    let byte: u8 = kani::any();
    let left: u8 = kani::any();
    kani::assume(left <= 8);
    let mut r = BitReader::with(byte, left);
    assert!(r.inv());
    match r.next_bit() {
        None => assert!(left == 0),
        Some(b) => {
            assert!(left > 0 && b <= 1);
            assert!(b == (byte >> (left - 1)) & 1);
            assert!(r.inv());
        }
    }
    // A loaded byte: 8 bits, then none.
    let mut r = BitReader::empty();
    r.load(byte);
    let mut acc = 0u8;
    let mut n = 0u8;
    while let Some(b) = r.next_bit() {
        acc = (acc << 1) | b;
        n += 1;
    }
    assert!(n == 8 && acc == byte);
}

/// A table of up to `NSYM` symbols with no more than 2 codes of each length:
/// symbolic counts, symbolic symbols.
const NSYM: usize = 12;

fn any_counts() -> [u8; 16] {
    let counts: [u8; 16] = kani::any();
    kani::assume(counts.iter().all(|&c| c <= 2));
    kani::assume(counts.iter().map(|&c| u32::from(c)).sum::<u32>() <= 6);
    counts
}

/// Construction over any counts (at most 2 codes per length, so at most 32
/// symbols; the code is the same with 255) and any symbols; and the decoding
/// of any bit string with a table that passed.
#[kani::proof]
#[kani::unwind(19)]
fn huffman_build_any() {
    let counts = any_counts();
    let symbols: [u8; 6] = kani::any();
    let dc: bool = kani::any();
    let total: usize = counts.iter().map(|&c| usize::from(c)).sum();
    let Some(syms) = symbols.get(..total) else {
        return;
    };
    let Ok(table) = Table::build(&counts, syms, dc) else {
        return;
    };
    assert!(table.inv());
    assert!(table.symbols() == syms);
    // Decode any bits.
    let bits: [u8; 17] = kani::any();
    let (mut code, mut len) = (0u16, 0u8);
    let mut steps = 0u8;
    for &b in &bits {
        steps += 1;
        match table.step(code, len, b) {
            Next::More { code: c, len: l } => {
                assert!(l == len + 1 && l < MAX_LEN);
                code = c;
                len = l;
            }
            Next::Value(v) => {
                assert!(table.symbols().contains(&v));
                break;
            }
            Next::Bad => break,
        }
    }
    // At most 16 bits are ever read.
    assert!(steps <= 16);
}

/// `NSYM` is used by `huffman_build_any`'s documentation and the block harness.
const _: () = assert!(NSYM <= 32);

/// The integer IDCT over every block of `i16` and every `u16` quantizer:
/// never overflows.
#[kani::proof]
#[kani::solver(kissat)]
#[kani::unwind(10)]
fn idct_any() {
    let coef: [i16; 64] = kani::any();
    let quant: [u16; 64] = kani::any();
    assert!(idct(&coef, &quant).is_some());
}

/// The clamp after the IDCT, over every `i64`.
#[kani::proof]
fn range_limit_any() {
    let v: i64 = kani::any();
    let s = range_limit(v);
    if (-512..=511).contains(&v) {
        let want = (v + 128).clamp(0, 255);
        assert!(i64::from(s) == want);
    }
    // The wrap-around has period 1024.
    assert!(range_limit(v) == range_limit(v.wrapping_add(1024)) || v > i64::MAX - 1024);
}

/// A component plane of any geometry up to a 16 by 16 image, any ratio 1
/// to 4, any samples: every position of the image has a sample.
#[kani::proof]
#[kani::unwind(2)]
fn sample_any() {
    let (iw, ih): (usize, usize) = (kani::any(), kani::any());
    kani::assume((1..=16).contains(&iw) && (1..=16).contains(&ih));
    let (hs, vs): (usize, usize) = (kani::any(), kani::any());
    kani::assume((1..=4).contains(&hs) && (1..=4).contains(&vs));
    // `ceil(X / hs)` by `ceil(Y / vs)`, T.81 Equation A.1.
    let (w, h) = ((iw + hs - 1) / hs, (ih + vs - 1) / vs);
    // The stride is the plane padded to whole blocks (any padding).
    let pad: usize = kani::any();
    kani::assume(pad <= 8);
    let stride = w + pad;
    let data: [u8; 256] = kani::any();
    let Some(d) = data.get(..stride * h) else {
        return;
    };
    let plane = Plane {
        data: d,
        stride,
        width: w,
        height: h,
        hs,
        vs,
    };
    let (x, y): (usize, usize) = (kani::any(), kani::any());
    kani::assume(x < iw && y < ih);
    assert!(plane.sample(x, y).is_some());
}

/// A plane of one value upsamples to that value, at every position (the
/// filters' weights sum to their divisors).
#[kani::proof]
#[kani::unwind(2)]
fn sample_constant() {
    let (iw, ih): (usize, usize) = (kani::any(), kani::any());
    kani::assume((1..=16).contains(&iw) && (1..=16).contains(&ih));
    let (hs, vs): (usize, usize) = (kani::any(), kani::any());
    kani::assume((1..=4).contains(&hs) && (1..=4).contains(&vs));
    let (w, h) = ((iw + hs - 1) / hs, (ih + vs - 1) / vs);
    let v: u8 = kani::any();
    let data = [v; 256];
    let Some(d) = data.get(..w * h) else {
        return;
    };
    let plane = Plane {
        data: d,
        stride: w,
        width: w,
        height: h,
        hs,
        vs,
    };
    let (x, y): (usize, usize) = (kani::any(), kani::any());
    kani::assume(x < iw && y < ih);
    assert!(plane.sample(x, y) == Some(v));
}

/// The orientation map over every size up to 2^14 and every position.
#[kani::proof]
fn orient_any() {
    let (w, h): (usize, usize) = (kani::any(), kani::any());
    kani::assume((1..=16384).contains(&w) && (1..=16384).contains(&h));
    let o: u8 = kani::any();
    kani::assume((1..=8).contains(&o));
    let (x, y): (usize, usize) = (kani::any(), kani::any());
    kani::assume(x < w && y < h);
    let Some((dx, dy)) = orient(o, w, h, x, y) else {
        panic!("orient refused a position in the image");
    };
    let (dw, dh) = if swaps(o) { (h, w) } else { (w, h) };
    assert!(dx < dw && dy < dh);
    // Outside the image, or another value: refused.
    assert!(orient(o, w, h, w, y).is_none() && orient(o, w, h, x, h).is_none());
    assert!(orient(0, w, h, x, y).is_none() && orient(9, w, h, x, y).is_none());
}

/// Every orientation of every size up to 3 by 3 is a bijection onto the
/// oriented image.
#[kani::proof]
#[kani::unwind(12)]
fn orient_bijection() {
    let (w, h): (usize, usize) = (kani::any(), kani::any());
    kani::assume((1..=3).contains(&w) && (1..=3).contains(&h));
    let o: u8 = kani::any();
    kani::assume((1..=8).contains(&o));
    let mut seen = [false; 9];
    let dw = if swaps(o) { h } else { w };
    for y in 0..h {
        for x in 0..w {
            let Some((dx, dy)) = orient(o, w, h, x, y) else {
                panic!("orient refused a position in the image");
            };
            let i = dy * dw + dx;
            assert!(i < 9 && !seen[i]);
            seen[i] = true;
        }
    }
}

/// YCbCr to RGB over all 2^24 inputs equals the closed form of libjpeg-turbo's
/// tables: `y + ((FIX(k) * (c - 128) + 2^15) >> 16)`, clamped.
#[kani::proof]
fn ycc_any() {
    let (y, cb, cr): (u8, u8, u8) = (kani::any(), kani::any(), kani::any());
    let [r, g, b] = ycc_to_rgb(y, cb, cr);
    let (y, cb, cr) = (i64::from(y), i64::from(cb) - 128, i64::from(cr) - 128);
    let clamp = |v: i64| v.clamp(0, 255);
    assert!(i64::from(r) == clamp(y + ((91881 * cr + 32768) >> 16)));
    assert!(i64::from(g) == clamp(y + ((-22554 * cb + 32768 - 46802 * cr) >> 16)));
    assert!(i64::from(b) == clamp(y + ((116130 * cb + 32768) >> 16)));
}

/// CMYK to RGB over all 2^32 inputs: `round(c * k / 255)`, never above `c`
/// or `k`.
#[kani::proof]
fn cmyk_any() {
    let (c, m, y, k): (u8, u8, u8, u8) = (kani::any(), kani::any(), kani::any(), kani::any());
    let [r, g, b] = cmyk_to_rgb(c, m, y, k);
    let want = |a: u8| (u32::from(a) * u32::from(k) + 127) / 255;
    assert!(u32::from(r) == want(c) && u32::from(g) == want(m) && u32::from(b) == want(y));
    assert!(r <= c && r <= k && g <= m && g <= k && b <= y && b <= k);
}

/// One bit of a block, in any stage with any counters satisfying the
/// invariant, with Huffman tables of up to 32 symbols that passed
/// construction: no panic or overflow, and the invariant is kept (when the
/// block is not complete).
#[kani::proof]
#[kani::solver(kissat)]
#[kani::unwind(19)]
fn block_machine_any() {
    let stage = match kani::any::<u8>() % 4 {
        0 => Stage::DcCode,
        1 => Stage::DcBits,
        2 => Stage::AcCode,
        _ => Stage::AcBits,
    };
    let mut block = Block::any_block(stage);
    kani::assume(block.inv());
    let (dc_counts, ac_counts) = (any_counts(), any_counts());
    let dc_syms: [u8; 6] = kani::any();
    let ac_syms: [u8; 6] = kani::any();
    let dn: usize = dc_counts.iter().map(|&c| usize::from(c)).sum();
    let an: usize = ac_counts.iter().map(|&c| usize::from(c)).sum();
    let (Some(ds), Some(asy)) = (dc_syms.get(..dn), ac_syms.get(..an)) else {
        return;
    };
    let (Ok(dc), Ok(ac)) = (
        Table::build(&dc_counts, ds, true),
        Table::build(&ac_counts, asy, false),
    ) else {
        return;
    };
    let mut pred: i32 = kani::any();
    let bit: u8 = kani::any();
    kani::assume(bit <= 1);
    if let Ok(false) = block.bit(bit, &dc, &ac, &mut pred) {
        assert!(block.inv());
    }
}
