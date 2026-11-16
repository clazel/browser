//! Kani harnesses (Tier 1). Compiled only under `cargo kani`.
//!
//! Eight statements, bounded as the README lists. The decoder's LZW is
//! generic over the code size (`Lzw<BITS>`, 12 in the browser); under Kani
//! the decoder runs at 3 bits (8 entries) and the LZW harnesses at 3 and 4.
//!
//! - [`control_byte_any`]: one byte of the stream in **any phase but image
//!   data**, over any state satisfying the invariant, a 2 by 2 canvas and
//!   any contents of the buffers: no panic, overflow or out-of-bounds
//!   index, and the invariant holds afterwards on `Ok`.
//! - [`data_byte_any`]: the same for one byte of **image data** (LZW into
//!   the canvas through the colour table), over any state in that phase.
//! - [`lzw_any`]: one byte of LZW (the whole of `feed`: up to three codes)
//!   over any state satisfying `Lzw::inv` and **any contents** of the three
//!   arrays, a table that is not the one the decoder built included, with a
//!   sink that answers anything: no panic, `inv` kept on `Ok(Fed::More)`.
//! - [`lzw_code_any`]: one code, the body of that loop, at 4 bits: `inv_table`
//!   kept (the bit buffer is `feed`'s), no panic, at most `2^4` indexes.
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
//!
//! The heavy ones use `#[kani::solver(kissat)]`: with the default solver
//! CBMC ran out of memory on `data_byte_any`; with kissat it takes minutes.

use crate::decoder::any_gif;
use crate::lzw::{Fed, Lzw, Tables};
use crate::work::Parts;

/// The LZW harnesses run at 4 bits (16 entries); the decoder's at 3 (below).
const LZW_BITS: u8 = 4;
const LZW_LEN: usize = 16;
use crate::sink::Sink;

// NOT a harness: the item 6.3 template on the whole step function.
//
//     clazel_image_shape::decoder_step_harness! {
//         #[kani::proof]
//         #[kani::unwind(10)]
//         #[kani::solver(kissat)]
//         fn step_any for crate::decoder::Gif {
//             max_chunk: 1,
//             max_pixels: 16,
//             max_work: 1584,
//             any_state: any_gif,
//         }
//     }
//
// It expands and runs from this crate (the template works from another
// crate), but on the whole of `step` CBMC passed 6 GB after 5.5 minutes on
// an 8 GB machine and was stopped (with two chunk bytes, 5 GB after 3.5
// minutes), so it is not a harness here, and `step`'s own statement (every
// outcome keeps `inv`, `consumed <= chunk.len()`, `NeedMore` consumes it all)
// is argued from the byte harnesses below, not machine-checked; see the
// README, "What Kani covers". `step` is `Parts::new` (a unit test and the
// lengths in `inv`), then a loop of `byte` (which is `control_byte` or
// `data_byte`, one harness each) that stops at the first frame, error or
// trailer, and returns `consumed` as the index it stopped at.

/// One byte of the stream in any phase but image data, over any state with
/// the invariant and any contents of the buffers (on a 2 by 2 canvas): no
/// panic, and on `Ok` the invariant of the state holds. (An error spends the
/// decoder, `step` says so, and `inv` then asks for nothing but the
/// buffers' lengths.) `byte` sends image data to `data_byte`, everything
/// else here, and `step` is a loop of `byte`.
///
/// The parts are separate arrays, not one work buffer cut up as `Parts::new`
/// does (that is checked by `Gif::inv` and its unit test): the model checker
/// follows every access into one 1.6 kB object, and the cut is plain
/// `split_at_mut_checked`.
#[kani::proof]
#[kani::unwind(10)]
fn control_byte_any() {
    let Some(mut gif) = any_gif() else {
        return;
    };
    kani::assume(!gif.is_data());
    kani::assume(gif.state_inv());
    let mut pixels: [u8; 16] = kani::any();
    let mut global: [u8; 768] = kani::any();
    let mut local: [u8; 768] = kani::any();
    let mut prefix: [u8; 16] = kani::any();
    let mut suffix: [u8; 8] = kani::any();
    let mut stack: [u8; 8] = kani::any();
    let mut saved: [u8; 16] = kani::any();
    let b: u8 = kani::any();
    let mut parts = Parts {
        pixels: &mut pixels,
        global: &mut global,
        local: &mut local,
        tables: Tables {
            prefix: &mut prefix,
            suffix: &mut suffix,
            stack: &mut stack,
        },
        saved: &mut saved,
    };
    let result = gif.control_byte(b, &mut parts);
    if result.is_ok() {
        assert!(gif.state_inv());
    }
}

/// One byte of image data: `data_byte` over any state in `Phase::Data`
/// with the invariant, same bounds and the same separate arrays. The LZW
/// and the sink inside it are `lzw_any` and `sink_put_any`, whose statements
/// this one composes with the glue (the counts, the palette, the phase).
#[kani::proof]
#[kani::solver(kissat)]
#[kani::unwind(10)]
fn data_byte_any() {
    let Some(mut gif) = any_gif() else {
        return;
    };
    kani::assume(gif.is_data());
    kani::assume(gif.state_inv());
    let mut pixels: [u8; 16] = kani::any();
    let mut global: [u8; 768] = kani::any();
    let mut local: [u8; 768] = kani::any();
    let mut prefix: [u8; 16] = kani::any();
    let mut suffix: [u8; 8] = kani::any();
    let mut stack: [u8; 8] = kani::any();
    let mut saved: [u8; 16] = kani::any();
    let b: u8 = kani::any();
    let mut parts = Parts {
        pixels: &mut pixels,
        global: &mut global,
        local: &mut local,
        tables: Tables {
            prefix: &mut prefix,
            suffix: &mut suffix,
            stack: &mut stack,
        },
        saved: &mut saved,
    };
    let result = gif.data_byte(b, &mut parts);
    if result.is_ok() {
        assert!(gif.state_inv());
    }
}

/// One LZW code over any state with the invariant and any arrays: the body
/// of `feed`'s loop, which is where every table access is.
#[kani::proof]
#[kani::unwind(19)]
fn lzw_code_any() {
    let mut lzw = Lzw::<LZW_BITS> {
        min_size: kani::any(),
        code_size: kani::any(),
        next: kani::any(),
        prev: kani::any(),
        first: kani::any(),
        acc: kani::any(),
        nacc: kani::any(),
    };
    kani::assume(lzw.inv());
    let mut prefix: [u8; LZW_LEN * 2] = kani::any();
    let mut suffix: [u8; LZW_LEN] = kani::any();
    let mut stack: [u8; LZW_LEN] = kani::any();
    // Any code `feed` can read: `code_size` bits.
    let code: u16 = kani::any();
    kani::assume(u32::from(code) < (1u32 << lzw.code_size));
    let mut given = 0usize;
    let mut tables = Tables {
        prefix: &mut prefix,
        suffix: &mut suffix,
        stack: &mut stack,
    };
    let result = lzw.code(code, &mut tables, &mut |_index| {
        given += 1;
        kani::any()
    });
    if let Ok(Fed::More) = result {
        assert!(lzw.inv_table());
    }
    assert!(given <= LZW_LEN);
}

/// One byte of LZW over any state with the invariant and any arrays, with a
/// table of 3 bits (8 entries): the whole of `feed`, three codes at most.
#[kani::proof]
#[kani::unwind(20)]
fn lzw_any() {
    let mut lzw = Lzw::<3> {
        min_size: kani::any(),
        code_size: kani::any(),
        next: kani::any(),
        prev: kani::any(),
        first: kani::any(),
        acc: kani::any(),
        nacc: kani::any(),
    };
    kani::assume(lzw.inv());
    let mut prefix: [u8; 16] = kani::any();
    let mut suffix: [u8; 8] = kani::any();
    let mut stack: [u8; 8] = kani::any();
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
    // A byte holds at most 8 bits and a code has at least 3, so at most 3
    // codes, each at most 8 indexes long (a table of 3 bits, 8 entries).
    assert!(given <= 3 * 8);
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
