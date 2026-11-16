//! Kani harnesses (Tier 1). Compiled only under `cargo kani`.
//!
//! Three groups:
//!
//! - **Sizes**: [`size_any`] states [`rgba_len`]'s whole contract over
//!   every `u32` pair: `Ok` exactly when both sides are in `1..=MAX_SIDE`
//!   and the pixels at most `MAX_PIXELS`, and then `4 * width * height`;
//!   no overflow is reachable.
//! - **Premultiplication**: [`premultiply_channel_any`] over every channel
//!   and alpha (the bound that the arithmetic never saturates, the result
//!   within half a unit of `c * a / 255`, at most `c` and `a`, identity at
//!   255, zero at 0), and [`premultiply_in_place_any_3`] over any 3 pixels
//!   (one more byte than 2 pixels, to include a trailing partial pixel)
//!   leaves alpha alone and does not panic.
//! - **The template**: [`toy_step_any`] is
//!   [`decoder_step_harness!`](crate::decoder_step_harness) instantiated on
//!   the toy decoder (`toy.rs`), at images up to 2 by 2 and chunks up to 8
//!   bytes, proving the pattern works end to end.
//!
//! Bounds and what is not covered are listed in the README.

use crate::premultiply::{channel, premultiply, premultiply_in_place};
use crate::toy::{Toy, any_toy};
use crate::{BYTES_PER_PIXEL, MAX_PIXELS, MAX_SIDE, SizeError, pixel_count, rgba_len};

/// `rgba_len` and `pixel_count` over every pair of `u32`.
#[kani::proof]
fn size_any() {
    let width: u32 = kani::any();
    let height: u32 = kani::any();
    let ok = width >= 1 && height >= 1 && width <= MAX_SIDE && height <= MAX_SIDE;
    match (pixel_count(width, height), rgba_len(width, height)) {
        (Ok(pixels), Ok(bytes)) => {
            assert!(ok);
            assert!(pixels == u64::from(width) * u64::from(height));
            assert!(pixels <= MAX_PIXELS);
            assert!(bytes as u64 == pixels * BYTES_PER_PIXEL as u64);
        }
        (Err(a), Err(b)) => {
            assert!(a == b);
            match a {
                SizeError::Empty => assert!(width == 0 || height == 0),
                SizeError::TooWide => assert!(width > MAX_SIDE && height != 0),
                SizeError::TooTall => assert!(height > MAX_SIDE && width <= MAX_SIDE && width != 0),
                SizeError::TooManyPixels => {
                    assert!(ok && u64::from(width) * u64::from(height) > MAX_PIXELS)
                }
            }
        }
        _ => assert!(false),
    }
}

/// One channel, every value and every alpha.
#[kani::proof]
fn premultiply_channel_any() {
    let c: u8 = kani::any();
    let a: u8 = kani::any();
    let out = channel(c, a);
    let exact = u32::from(c) * u32::from(a); // at most 65,025
    // The arithmetic never saturates or truncates: the quotient fits.
    assert!((exact + 127) / 255 <= 255);
    assert!(u32::from(out) == (exact + 127) / 255);
    // Within half a unit of c * a / 255.
    let scaled = u32::from(out) * 255;
    assert!(scaled + 127 >= exact && exact + 127 >= scaled);
    assert!(out <= c && out <= a);
    if a == 255 {
        assert!(out == c);
    }
    if a == 0 {
        assert!(out == 0);
    }
}

/// One pixel keeps its alpha.
#[kani::proof]
fn premultiply_pixel_any() {
    let p: [u8; 4] = kani::any();
    let q = premultiply(p);
    assert!(q[3] == p[3]);
}

/// Any 3 pixels in place: the alpha bytes are kept, nothing panics.
#[kani::proof]
#[kani::unwind(5)]
fn premultiply_in_place_any_3() {
    let before: [u8; 12] = kani::any();
    let mut v = before;
    premultiply_in_place(&mut v);
    assert!(v[3] == before[3] && v[7] == before[7] && v[11] == before[11]);
}

/// Any 2 pixels and a trailing byte: the partial pixel is untouched.
#[kani::proof]
#[kani::unwind(4)]
fn premultiply_in_place_partial() {
    let before: [u8; 11] = kani::any();
    let mut v = before;
    premultiply_in_place(&mut v);
    assert!(v[8] == before[8] && v[9] == before[9] && v[10] == before[10]);
}

crate::decoder_step_harness! {
    #[kani::proof]
    #[kani::unwind(18)]
    fn toy_step_any for Toy {
        max_chunk: 8,
        max_pixels: 16,
        max_work: 4,
        any_state: any_toy,
    }
}
