//! A PNG and APNG decoder (phase-6.md item 6.4), a resumable step function
//! over caller-owned buffers, implementing [`clazel_image_shape::Decoder`].
//!
//! # The standard
//!
//! *Portable Network Graphics (PNG) Specification (Third Edition)*, W3C
//! Recommendation, 24 June 2025, <https://www.w3.org/TR/png-3/> (fetched
//! 2026-11-17, 656,574 bytes, SHA-256
//! `a3ac82bb9eb8664b93961a2a9ff6def3d70e3a9f63d92721143c1f391d04edec`).
//! Section numbers below are that document's: 4.9 APNG frame-based animation
//! (4.9.1 structure, 4.9.2 sequence numbers, 4.9.3 output buffer, 4.9.4
//! canvas), 5.2 PNG signature, 5.3 chunk layout, 5.4 chunk naming
//! conventions, 5.5 CRC algorithm, 5.6 chunk ordering, 6.1 colour types and
//! values, 6.2 alpha representation, 7.2 scanlines, 8 interlacing and pass
//! extraction (8.1 interlace methods), 9 filtering (9.2 filter types for
//! filter method 0, 9.3 Average, 9.4 Paeth), 10 compression, 11.2 critical
//! chunks (11.2.1 IHDR, 11.2.2 PLTE, 11.2.3 IDAT, 11.2.4 IEND), 11.3.1
//! transparency information (`tRNS`), 11.3.2 colour space information
//! (`gAMA`, `cHRM`, `iCCP`, `sRGB`, `cICP`), 11.3.6 animation information
//! (`acTL`, `fcTL`, `fdAT`), 13 decoders (13.12 sample depth rescaling, 13.16
//! alpha channel processing). The standard says what the stream is; where it
//! is silent or a browser draws something else, the choice is listed here,
//! and commented where it takes effect.
//!
//! # What it decodes
//!
//! The signature, then the chunks: IHDR (every colour type and bit depth of
//! Table 11.1, others refused), PLTE, `tRNS`, IDAT across any number of
//! chunks through [`clazel_deflate`]'s streaming zlib, IEND; the five
//! filters; Adam7; `acTL`, `fcTL` and `fdAT`, with every frame decoded and
//! **composited** onto the canvas (the pixel buffer, straight RGBA8) with
//! its `dispose_op` and `blend_op`. [`Status::FrameDone`] means the pixel
//! buffer holds the canvas as it is displayed with that frame, and
//! [`Png::frame`] has the frame's rectangle, delay, disposal and blend. The
//! first `FrameDone` is the image (the default image of an APNG: 6.0(d)'s
//! option A shows it, and an APNG-ignorant decoder would draw the same).
//!
//! [`Status::FrameDone`]: clazel_image_shape::Status::FrameDone
//!
//! # Listed choices
//!
//! 1. **Frames and the config.** `decode_config` reads the signature and the
//!    first 24 bytes of IHDR (width, height) and says
//!    [`FrameCount::Unknown`](clazel_image_shape::FrameCount::Unknown): the
//!    chunks that say how many frames there are (`acTL`) come after IHDR and
//!    a prefix function should not wait for them. The work buffer therefore
//!    always holds a copy of the canvas for `dispose_op` "previous" (it is
//!    `4 * width * height` bytes beyond the scanline buffers), so a still
//!    PNG costs twice its pixels in memory; 6.12 may size it lazily.
//! 2. **FrameDone comes after the CRC of the chunk that completed the
//!    frame**, so a corrupt IDAT is refused before the image is shown. IEND
//!    and later chunks are read by the next `step`: IEND (CRC checked) is
//!    `Error::NoMoreFrames`, and a stream that ends first leaves the frames
//!    already delivered valid. Bytes after IEND are never read.
//! 3. **Every chunk's CRC is checked**, ancillary chunks too: a mismatch
//!    anywhere is an error (the `png` crate skips mismatches in ancillary
//!    chunks it does not use; `libpng` warns). Stricter, and listed.
//! 4. **Chunk order (5.6)**: IHDR first and once; PLTE and `tRNS` once each,
//!    before IDAT, PLTE before `tRNS` for palette images; IDAT chunks
//!    consecutive (empty ones allowed); no PLTE in greyscale images (types
//!    0 and 4), none required for types 2 and 6 (where it is skipped as a
//!    suggested palette); `tRNS` only for types 0, 2 and 3 with exactly 2,
//!    6 and at most as many bytes as the palette has entries. An unknown
//!    **critical** chunk is `Error::Unsupported`; unknown ancillary ones, and
//!    `gAMA`, `cHRM`, `iCCP`, `sRGB`, `cICP`, `tEXt`, `pHYs`, `bKGD`, `tIME`
//!    and the rest, are skipped by their length (CRC checked) and their
//!    contents ignored: **no colour management** (see `pixel.rs`).
//! 5. **Pixel choices** (in `pixel.rs`, matching the `png` crate so the
//!    differential is exact): 16 bits to 8 by truncation, 1, 2 and 4 bits
//!    scaled by `255 / (2^depth - 1)`, `tRNS` colour compared at full 16-bit
//!    precision, a palette index past the entries opaque black, more than
//!    `2^depth` palette entries accepted.
//! 6. **The zlib stream** must be exactly the scanlines and end with a good
//!    Adler-32: too little, too much, or a bad checksum is an error. After
//!    the stream's end, the rest of that IDAT chunk and any further IDAT
//!    chunks are skipped (CRC checked).
//! 7. **Filter type** above 4 is an error (9.1); filtering by bytes of
//!    exact modulo-256 arithmetic.
//! 8. **APNG** (4.9, 11.3.6): the canvas starts fully transparent; a frame's
//!    `dispose_op` is applied to its region before the next frame is drawn
//!    ("previous" of the first animation frame counts as "background"); an
//!    image whose default image has no `fcTL` is not part of the animation,
//!    and the canvas is cleared before the first animation frame; `acTL`
//!    chunks are ignored (with `fcTL` and `fdAT`) when `acTL` is absent;
//!    fewer frames than `num_frames` says is accepted, more is an error; a
//!    frame outside the canvas, with `dispose_op` above 2 or `blend_op`
//!    above 1, or sequence numbers out of order, is an error; an `fcTL`
//!    without its `fdAT`, or an `fdAT` without its `fcTL` or inside the
//!    default image's data, is an error. `APNG_BLEND_OP_OVER` rounds as
//!    `pixel::over` says. The delay is reported as the chunk gives it
//!    (`delay_den` 0 means 100, for the caller).
//! 9. **Limits**: 6.0(j)'s, through `Config::new` (at most 2^14 on a side and
//!    2^26 pixels); IHDR's size must be the config's.
//!
//! # Verification
//!
//! Tier 1 target (`Cargo.toml`): the Kani harnesses of `proofs.rs`, listed
//! with their bounds in the README. The decoder is generic over the zlib
//! engine ([`engine::Engine`]), and the harnesses use an engine that answers
//! anything its contract allows, so what they prove of the step holds for
//! any zlib engine that obeys the contract (`clazel-deflate`'s own step is
//! not proven). The invariant is [`Png::inv`](clazel_image_shape::Decoder::inv)
//! (`decoder.rs`); every index and computation uses checked or saturating
//! operations, so the invariant is about the ranges of counters.

pub mod adam7;
pub mod crc;
mod decoder;
pub mod engine;
pub mod filter;
pub mod pixel;
#[cfg(kani)]
mod proofs;
mod work;

pub use decoder::{Animation, Blend, Dispose, FrameInfo, Png};
