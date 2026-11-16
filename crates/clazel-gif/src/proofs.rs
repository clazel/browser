//! Kani harnesses (Tier 1). Compiled only under `cargo kani`.
//!
//! Four statements, bounded as the README lists:
//!
//! - [`step_any`]: [`clazel_image_shape::decoder_step_harness!`] on the GIF
//!   decoder. For **any** state satisfying `Gif::inv`, any contents of the
//!   pixel and work buffers and any chunk of up to 6 bytes, on a canvas of
//!   at most 2 by 2 and with the LZW table at 4 bits (16 entries): one
//!   `step` does not panic, overflow or index out of bounds, writes only
//!   inside the buffers, keeps `inv` on `Ok` and on `Err`, and obeys the
//!   `Decoder::step` contract.
//! - [`lzw_any`]: one byte of LZW over any state satisfying `Lzw::inv` and
//!   **any contents** of the three arrays (a table that is not the one the
//!   decoder built included): no panic, `inv` kept on `Ok(Fed::More)`, and
//!   at most `TABLE_LEN` indexes given to the sink per code.
//! - [`sink_put_any`]: one index through the sink over any state satisfying
//!   `Sink::inv`, any palette up to 4 entries, a canvas of at most 2 by 2
//!   and a frame of any position and size: no panic, `inv` kept, nothing
//!   outside the canvas written, and the frame's remaining count goes down
//!   by one.
//! - [`interlace_row_any`]: the next row of an interlaced frame of **any
//!   height** (every `u16`) from any row and pass: stays in a pass of 0 to
//!   3, and is in the frame or ends it.
//! - [`interlace_covers_frame`]: an interlaced frame of any size up to 4 by 4
//!   receives its `width * height` indexes into every pixel of the canvas
//!   exactly once (all painted, and the count is right, so none twice).

use crate::decoder::any_gif;
use crate::lzw::{Fed, Lzw, TABLE_LEN, Tables};
use crate::sink::Sink;

clazel_image_shape::decoder_step_harness! {
    #[kani::proof]
    #[kani::unwind(20)]
    fn step_any for crate::decoder::Gif {
        max_chunk: 6,
        // 2 by 2 pixels of 4 bytes.
        max_pixels: 16,
        // FIXED (1536 for the tables, 64 for LZW at 4 bits) + 16 saved.
        max_work: 1616,
        any_state: any_gif,
    }
}

/// One byte of LZW over any state with the invariant and any arrays.
#[kani::proof]
#[kani::unwind(20)]
fn lzw_any() {
    let mut lzw = Lzw {
        min_size: kani::any(),
        code_size: kani::any(),
        next: kani::any(),
        prev: kani::any(),
        first: kani::any(),
        acc: kani::any(),
        nacc: kani::any(),
    };
    kani::assume(lzw.inv());
    let mut prefix: [u8; TABLE_LEN * 2] = kani::any();
    let mut suffix: [u8; TABLE_LEN] = kani::any();
    let mut stack: [u8; TABLE_LEN] = kani::any();
    let byte: u8 = kani::any();
    let mut given = 0usize;
    let mut tables = Tables {
        prefix: &mut prefix,
        suffix: &mut suffix,
        stack: &mut stack,
    };
    let result = lzw.feed(byte, &mut tables, &mut |_index| {
        given += 1;
        kani::any()
    });
    if let Ok(Fed::More) = result {
        assert!(lzw.inv());
    }
    // A byte holds at most 8 bits, so at most 8 codes of 2 bits; here the
    // codes have at least 3 bits, so at most 3, each at most TABLE_LEN long.
    assert!(given <= 3 * TABLE_LEN);
}

/// One index through the sink over any state with the invariant.
#[kani::proof]
#[kani::unwind(24)]
fn sink_put_any() {
    let canvas_w: u16 = kani::any();
    let canvas_h: u16 = kani::any();
    kani::assume(canvas_w >= 1 && canvas_w <= 2 && canvas_h >= 1 && canvas_h <= 2);
    let mut sink = Sink {
        canvas_w,
        canvas_h,
        left: kani::any(),
        top: kani::any(),
        width: kani::any(),
        height: kani::any(),
        interlaced: kani::any(),
        transparent: if kani::any() { Some(kani::any()) } else { None },
        x: kani::any(),
        y: kani::any(),
        pass: kani::any(),
        remaining: kani::any(),
    };
    kani::assume(sink.inv());
    let palette: [u8; 12] = kani::any();
    let palette_len: usize = kani::any();
    kani::assume(palette_len <= 12);
    let index: u8 = kani::any();
    // A canvas of 4 bytes per pixel, in an array with room to spare.
    let mut array: [u8; 20] = kani::any();
    let before = array;
    let len = usize::from(canvas_w) * usize::from(canvas_h) * 4;
    let remaining = sink.remaining;
    {
        let pixels = &mut array[..len];
        let pal = &palette[..palette_len];
        let more = sink.put(index, pal, pixels);
        assert!(more == (sink.remaining > 0));
    }
    assert!(sink.inv());
    assert!(array[len..] == before[len..]);
    if remaining > 0 {
        assert!(sink.remaining == remaining - 1 || sink.remaining == 0);
    } else {
        assert!(sink.remaining == 0);
    }
}

/// The next interlaced row, for a frame of any height.
#[kani::proof]
#[kani::unwind(6)]
fn interlace_row_any() {
    let mut sink = Sink::idle(1, 1);
    sink.height = kani::any();
    sink.width = kani::any();
    sink.interlaced = true;
    sink.pass = kani::any();
    sink.y = kani::any();
    kani::assume(sink.pass <= 3 && sink.y < sink.height);
    sink.next_interlaced_row();
    assert!(sink.pass <= 3);
    assert!(sink.y <= sink.height);
}

/// An interlaced frame of any size up to 4 by 4 paints each pixel once.
#[kani::proof]
#[kani::unwind(20)]
fn interlace_covers_frame() {
    let width: u16 = kani::any();
    let height: u16 = kani::any();
    kani::assume(width >= 1 && width <= 4 && height >= 1 && height <= 4);
    let mut sink = Sink::frame((width, height), (0, 0, width, height), true, None);
    // One colour, opaque white; the canvas starts transparent.
    let palette = [255u8, 255, 255];
    let mut canvas = [0u8; 64];
    let len = usize::from(width) * usize::from(height) * 4;
    let total = usize::from(width) * usize::from(height);
    let mut given = 0usize;
    let pixels = &mut canvas[..len];
    while sink.remaining > 0 {
        let more = sink.put(0, &palette, pixels);
        given += 1;
        assert!(more == (sink.remaining > 0));
        assert!(sink.inv());
    }
    assert!(given == total);
    let mut i = 0;
    while i < len {
        assert!(pixels[i + 3] == 255);
        i += 4;
    }
}
