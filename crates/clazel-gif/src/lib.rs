//! A GIF decoder (phase-6.md item 6.7), a resumable step function over
//! caller-owned buffers, implementing [`clazel_image_shape::Decoder`].
//!
//! # The standard
//!
//! *Graphics Interchange Format, Version 89a*, CompuServe Incorporated,
//! 31 July 1990 (the "GIF89a specification"), read from the W3C's copy,
//! <https://www.w3.org/Graphics/GIF/spec-gif89a.txt> (2,476 lines, fetched
//! 2026-11-16, SHA-256
//! `c0e48c12e3e91b1e78090caffb1d1ffe8e7d0face4350da675044a9a4be02aa3`; the
//! document is frozen, there is no later revision). Section numbers
//! below are that document's (15 Data Sub-blocks, 16 Block Terminator,
//! 17 Header, 18 Logical Screen Descriptor, 19 Global Color Table, 20 Image
//! Descriptor, 21 Local Color Table, 22 Table Based Image Data, 23 Graphic
//! Control Extension, 24 Comment Extension, 25 Plain Text Extension, 26
//! Application Extension, 27 Trailer, and Appendix B GIF Grammar, E
//! Interlaced Images, F Variable-Length-Code LZW Compression). The
//! standard is silent or loose where browsers are not;
//! each such place is a listed choice below, and the same ones are
//! commented where they take effect.
//!
//! # What it decodes
//!
//! Header (`GIF87a` or `GIF89a`), logical screen descriptor, global and
//! local colour tables, image descriptors with interlacing, LZW image data
//! (`lzw.rs`), the Graphic Control Extension (disposal method, delay,
//! transparent index), and every other extension (plain text, comment,
//! application, unknown) skipped by its sub-block sizes. **Every frame** is
//! decoded and **composited** onto the canvas (the pixel buffer, straight
//! RGBA8) with the previous frame's disposal method applied first;
//! [`Status::FrameDone`](clazel_image_shape::Status::FrameDone) means the
//! pixel buffer holds the canvas as it is displayed with that frame, and
//! [`Gif::frame`] has the frame's delay, disposal and rectangle. The first
//! `FrameDone` is the first composited frame that decision 6.0(d)'s option
//! A shows.
//!
//! # Listed choices
//!
//! 1. **The canvas starts transparent black and the background colour is
//!    ignored** (section 18's "Background Color Index"), and disposal
//!    method 2 (restore to background) clears to transparent black: what
//!    browsers do. Disposal 3 restores the canvas saved before the frame;
//!    the work buffer holds that copy (`work.rs`), so it is as large as the
//!    pixel buffer plus about 17 kB.
//! 2. **Disposal methods 4 to 7** (undefined in section 23) are read as 0.
//! 3. **A frame outside the canvas, or partly so**, is decoded in full and
//!    drawn clipped to the canvas (a frame of 0 width or 0 height draws
//!    nothing). The canvas never grows.
//! 4. **A colour index past the colour table** (or a frame with no table at
//!    all) draws nothing: the pixel keeps what the canvas holds, as a
//!    transparent one does. A transparent index only has effect when the
//!    control extension's flag says so (section 23).
//! 5. **LZW**: the full-table "deferred clear" and the other choices listed
//!    in `lzw.rs`; minimum code sizes 2 to 8.
//! 6. **Too little image data** (the terminator comes first, or the end
//!    code) ends the frame with the pixels decoded so far, the rest of the
//!    frame as the canvas held it; **too much** (data after the last pixel)
//!    is skipped up to the terminator. A stream that ends inside a frame
//!    is the caller's `Error::Truncated`: the canvas then holds the part
//!    drawn.
//! 7. **A Graphic Control Extension whose block size is not 4**, or whose
//!    terminator is missing, is skipped as an unknown extension, with no
//!    effect on the next frame; a second control extension before a frame
//!    replaces the first.
//! 8. **Block introducers** other than `,`, `!` and `;` are an error (not
//!    resynchronised). The trailer ends the stream: `step` says
//!    `Error::NoMoreFrames` from then on, also when it is the first block
//!    (a GIF with no frame is a broken image).
//! 9. **The NETSCAPE2.0 loop count** and the logical screen's pixel aspect
//!    ratio are not read (an application extension is skipped like the
//!    others): looping is policy for 6.19.
//! 10. **Canvas size**: the logical screen's size is the image's (6.0(j)'s
//!     limits apply, through `Config::new`); the screen descriptor in the
//!     stream must agree with the config `decode_config` gave.
//!
//! # Verification
//!
//! Tier 1 target (`Cargo.toml`): the Kani harnesses of `proofs.rs`, listed
//! with their bounds in the README. The invariant is `Gif::inv`
//! (`decoder.rs`); the step function and every helper index and compute
//! with checked operations only, so `inv` is about the ranges of the
//! counters, not about memory.

mod decoder;
mod lzw;
#[cfg(kani)]
mod proofs;
mod sink;
mod work;

pub use decoder::{Disposal, FrameInfo, Gif};
