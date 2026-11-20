//! A WebP decoder (phase-6.md item 6.8): the RIFF container, animation
//! frames composited onto a canvas, and VP8L lossless decoding, as a
//! resumable step function over caller-owned buffers implementing
//! [`clazel_image_shape::Decoder`]. Lossy `VP8 ` data is item 6.9; here it is
//! recognised and refused.
//!
//! # The standard
//!
//! *RFC 9649: WebP Image Format*, Zern, Massimino and Alakuijala, November
//! 2024, <https://www.rfc-editor.org/rfc/rfc9649.txt> (2,418 lines, fetched
//! 2026-11-18, SHA-256
//! `f4d7cd92b015c0b340f10a932bb03e564a758a17df50cbb992c16d8459d60e58`). Its
//! section 2 is the container ("WebP Container Specification"), section 3 the
//! lossless bitstream ("Specification for WebP Lossless Bitstream"). Section
//! numbers in the comments are that document's: 2.3 RIFF File Format, 2.4
//! WebP File Header, 2.5 Simple File Format (Lossy), 2.6 Simple File Format
//! (Lossless), 2.7 Extended File Format (2.7.1.1 Animation, 2.7.1.2 Alpha,
//! 2.7.1.6 Unknown Chunks, 2.7.2 Canvas Assembly from Frames), 3.4 RIFF
//! Header, 3.5 Transforms (3.5.1 Predictor, 3.5.2 Color, 3.5.3 Subtract
//! Green, 3.5.4 Color Indexing), 3.6 Image Data (3.6.2.2 LZ77 Backward
//! Reference and 3.6.2.2.1 Distance Mapping, 3.6.2.3 Color Cache Coding),
//! 3.7 Entropy Code (3.7.2.1 Decoding and Building the Prefix Codes, 3.7.2.2
//! Decoding of Meta Prefix Codes, 3.7.2.3 Decoding Entropy-Coded Image
//! Data), 3.8 Overall Structure of the Format. Where the RFC is silent or
//! loose, the decoder follows libwebp, and each such place is a listed
//! choice below, commented where it takes effect.
//!
//! # What it decodes
//!
//! - **Container**: `RIFF` size `WEBP`, then the simple lossless format
//!   (`VP8L`) or the extended one (`VP8X`, flags and canvas size, with
//!   `ICCP`, `EXIF`, `XMP ` and unknown chunks skipped, `ALPH` skipped).
//!   `VP8 ` (lossy) is recognised, its size read by `decode_config`, and
//!   `step` says [`Error::Unsupported`](clazel_image_shape::Error::Unsupported).
//! - **Animation**: `ANIM` and `ANMF`. **Every frame** is decoded into the
//!   frame buffer and composited onto the canvas (the pixel buffer, straight
//!   RGBA8) with the previous frame's disposal method applied first;
//!   [`Status::FrameDone`](clazel_image_shape::Status::FrameDone) means the
//!   pixel buffer holds the canvas as displayed with that frame and
//!   [`Webp::frame`] has the frame's duration, blending, disposal and
//!   rectangle. The first `FrameDone` is the first composited frame that
//!   decision 6.0(d)'s option A shows.
//! - **VP8L** (`vp8l.rs`): the four transforms (predictor with its fourteen
//!   modes, colour, subtract green, colour indexing with pixel bundling), the
//!   colour cache, meta prefix codes (entropy image), prefix codes (simple
//!   and normal code length codes), LZ77 backward references with the
//!   distance map.
//!
//! # Listed choices
//!
//! 1. **The canvas of an animation starts transparent black and the
//!    background colour of `ANIM` is ignored** (section 2.7.1.1 calls it a
//!    hint: "Viewer applications SHOULD treat the background color value as
//!    a hint and are not required to use it"), and disposal method 1
//!    ("Dispose to the background color") clears the frame's rectangle to
//!    transparent black: what browsers do. The loop count is not read:
//!    looping is policy for 6.19.
//! 2. **Alpha blending** (blending method 0) is done on the stored values,
//!    not in linear light (section 2.7.1.1 says "SHOULD be done in linear
//!    color space"; libwebp and browsers do not), with libwebp's integer
//!    arithmetic (`compose.rs`), except that a destination with alpha 0 takes
//!    the source exactly.
//! 3. **A still image** is decoded straight into the pixel buffer. The
//!    canvas of a `VP8X` file, or the size in the `VP8L` header, is the
//!    image's size, and the two must agree. `alpha_is_used` is "a hint only"
//!    (section 3.4) and ignored: the alpha channel is used as decoded.
//! 4. **`ANMF` chunks in a still image** are skipped, `ANIM` too ("If the
//!    Animation flag is not set and this chunk is present, it MUST be
//!    ignored"). In an animation, image data outside a frame is an error, an
//!    `ANMF` before the `ANIM` is an error, and each frame needs exactly one
//!    bitstream, which must be the size of the frame; a frame must lie
//!    inside the canvas (section 2.7.2).
//! 5. **`ALPH`** is skipped: it belongs with lossy data (item 6.9), and "A
//!    frame containing a 'VP8L' Chunk SHOULD NOT contain this chunk".
//! 6. **The RIFF size** ends the stream: trailing data is ignored (section
//!    2.4: "Readers MAY parse such files, ignoring the trailing data"), a
//!    chunk that does not fit in what contains it is an error, and the
//!    padding byte of an odd chunk is read and ignored.
//! 7. **Prefix codes** (`huffman.rs`): all-zero lengths and over-subscribed or
//!    incomplete codes are errors, a single symbol takes zero bits;
//!    `max_symbol` and the alphabet sizes as section 3.7.2.1.2; a symbol of a
//!    simple code past the alphabet is ignored (libwebp's behaviour).
//! 8. **Predictor modes 14 and 15**, which section 3.5.1 does not define,
//!    predict like mode 0 (libwebp's).
//! 9. **Prefix code groups**: at most `MAX_GROUPS` = 1,024 groups, and no more
//!    than the number of blocks of 4 by 4 pixels the image has; an entropy
//!    image that names more is
//!    [`Error::Unsupported`](clazel_image_shape::Error::Unsupported)
//!    (libwebp's encoder numbers groups densely, so this is not met by files
//!    it makes). Section 3.7.2.2.2 reads "num_prefix_groups = max(entropy
//!    image) + 1", all of them present in the stream.
//! 10. **Reading past the data**: a chunk that ends before the image is
//!     complete is an error (`Malformed`), also in the middle of a code (the
//!     decoder works on exactly the chunk's bytes).
//! 11. **A backward reference** whose distance reaches before the first pixel
//!     or whose length passes the last is an error (libwebp's), and copies
//!     proceed pixel by pixel, so an overlapping reference repeats.
//! 12. **Work space**: [`work_len`](clazel_image_shape::Decoder::work_len) is
//!     about 11.6 kB (colour cache, code lengths, colour table) plus 12 bytes
//!     per block of 4 by 4 pixels (the three sub-images), plus 6.4 kB per
//!     prefix code group held (at most 1,024), plus, for an animation, a
//!     frame buffer as large as the canvas (`work.rs` has the table).
//!
//! # Verification
//!
//! Tier 1 target (`Cargo.toml`): the Kani harnesses of `proofs.rs`, listed
//! with their bounds in the README. Every index and every arithmetic step in
//! the crate is checked (`get`, `checked_*`, `wrapping_*`: the workspace lints
//! deny the unchecked forms), so the harnesses prove the absence of panics
//! and the stated properties of the parts, and `inv` is about the ranges of
//! the counters.

mod bits;
mod compose;
mod decoder;
mod distance;
mod huffman;
#[cfg(kani)]
mod proofs;
mod transform;
mod vp8l;
mod work;

pub use decoder::{Animation, Blend, Dispose, FrameInfo, Webp};
