//! A baseline JPEG decoder (phase-6.md item 6.5), a resumable step function
//! over caller-owned buffers, implementing
//! [`clazel_image_shape::Decoder`].
//!
//! # The standard
//!
//! ITU-T Recommendation T.81 | ISO/IEC 10918-1, *Digital compression and
//! coding of continuous-tone still images: Requirements and guidelines*,
//! 09/92 (the JPEG standard), read from the W3C's copy,
//! <https://www.w3.org/Graphics/JPEG/itu-t81.pdf>. Clause numbers below are
//! that document's: Annex A (the DCT, A.1.1 sampling, A.2 MCU structure,
//! A.3 the inverse DCT), Annex B (markers: B.1.1.2 to B.1.1.5, B.2.2 frame
//! header, B.2.3 scan header, B.2.4.1 DQT, B.2.4.2 DHT, B.2.4.4 DRI,
//! Table B.1), Annex C (Huffman table specification), Annex E (E.1.2
//! restart markers) and Annex F (F.2 sequential decoding, Figures F.12 to
//! F.17). JFIF 1.02 (Eric Hamilton, C-Cube, 1 September 1992) section 7
//! gives the YCbCr to RGB conversion; Adobe Technical Note 5116 (APP14) the
//! colour transform flag of four-component files; Exif 2.32 (CIPA
//! DC-008-2019) 4.5.4 and 4.6.4 the Orientation tag.
//!
//! # What it decodes
//!
//! Sequential DCT, Huffman coding (SOF0 baseline, SOF1 extended with 8-bit
//! samples: up to 4 tables of each kind, 16-bit quantizers), 1, 3 or 4
//! components at any sampling factors from 1 to 4 that divide the largest,
//! interleaved or in one scan per component, with restart intervals; and
//! progressive DCT, Huffman coding (SOF2, item 6.6, Annex G: spectral
//! selection and successive approximation, DC and AC first scans and
//! refinements, EOB runs; `progressive.rs`). Output is straight RGBA8,
//! always opaque. Arithmetic coding, lossless, hierarchical and 12-bit
//! images, and two-component images, are refused with
//! [`clazel_image_shape::Error::Unsupported`].
//!
//! # Listed choices
//!
//! 1. **The IDCT is libjpeg-turbo's `jidctint.c`** (`jpeg_idct_islow`), not
//!    Annex A's real-valued sum: the standard (Part 2) only bounds the error
//!    of an implementation, and this integer algorithm is what the
//!    differential test can match exactly (`idct.rs`).
//! 2. **Chroma is upsampled with libjpeg-turbo's default "fancy"
//!    triangular filter** where the ratio is 2:1 (h2v1, h2v2, h1v2) and by
//!    replication otherwise (`output.rs`); the standard leaves it open.
//! 3. **Colour**: three components are YCbCr (JFIF 1.02 section 7, in
//!    libjpeg-turbo's fixed point, `output.rs`) when a JFIF APP0 is present,
//!    or an Adobe APP14 says transform 1 or an unknown value, or there is no
//!    marker and the ids are not `R`, `G`, `B`; RGB if Adobe says transform 0
//!    or the ids spell RGB. Four components are **CMYK as Adobe writes it,
//!    inverted** (255 is no ink), when Adobe says transform 0 or there is no
//!    Adobe marker, YCCK for any other transform; converted to RGB as
//!    `R = C * K / 255`. Grayscale is copied to R, G and B.
//! 4. **EXIF Orientation** is applied (the oriented size is the config's),
//!    from the first Exif APP1 segment before the frame header whose IFD 0
//!    lies in its first 512 bytes (`exif.rs`); nothing else of EXIF, no ICC
//!    profile, no thumbnail.
//! 5. **Markers**: `TEM` and `RSTn` between segments are ignored; bytes
//!    between segments other than `0xFF` are an error; DNL, DHP, EXP and
//!    reserved markers are errors; a second SOF, an SOS before the SOF and
//!    a duplicate component id are errors.
//! 6. **Tables**: a scan needs its Huffman and quantization tables defined
//!    before it (the quantization table is latched at the start of the scan,
//!    as libjpeg does); a sequential scan header's `Ss`, `Se`, `Ah`, `Al` are
//!    ignored; DC and AC selectors may be 0 to 3; a DC symbol over 15 and
//!    an over-subscribed code are errors, the all-ones code is accepted
//!    (`huffman.rs`).
//! 7. **The entropy-coded data**: a marker (other than the expected `RSTn`)
//!    before the last MCU is an error, not padded with zeros as libjpeg
//!    does; a restart marker out of order is an error, not resynchronised;
//!    bytes between the end of the data and the next marker are ignored; a
//!    run that passes the end of a block, or a coefficient or DC value that
//!    does not fit 16 bits, is an error. A stream with no EOI never
//!    completes (`Error::Truncated` from the caller), though every pixel may
//!    be decoded.
//! 8. **The work buffer** holds the decoded planes of every component, padded
//!    to whole MCUs, and its size is a function of the config alone, so it
//!    is the worst case whatever the frame header turns out to say; the
//!    decoder uses what it needs. It is `6 * (w + 31) * (h + 35)` bytes
//!    (item 6.6 raised it from four planes of `(w + 31) * (h + 31)`, the
//!    baseline need, to what a progressive frame needs, see 11). A caller
//!    bounding memory counts it: about 387 MiB at the largest image
//!    (2^13 by 2^13), besides the 256 MiB pixel buffer. (A decoder that
//!    keeps only a few MCU rows would need far less; the context rows of
//!    fancy upsampling make that a larger program, left for later; and the
//!    config cannot say "baseline", so a baseline image is given the
//!    progressive size too.)
//! 9. **One frame**: after EOI `step` says `FrameDone`, then
//!    `NoMoreFrames`.
//! 10. **Progressive scans** (`progressive.rs`): the scan header's `Ss`,
//!     `Se`, `Ah`, `Al` are checked as libjpeg-turbo's `start_pass` does (DC
//!     scans `Se = 0`; AC scans one component, `Ss <= Se <= 63`; a refinement
//!     has `Al = Ah - 1`; `Al <= 13`), but that a refinement continues the
//!     point transform of the scan before it is not (libjpeg warns only). A
//!     scan needs only the Huffman tables its kind reads. The quantization
//!     table of a component is latched at its first scan. A progressive
//!     frame of more than **100 scans** is refused (`Unsupported`): a scan
//!     costs the blocks of the image however little data it has (an `EOBn`
//!     run covers up to 32767 blocks per symbol), so a never-ending sequence
//!     of scans would be unbounded work. A component needs at least one
//!     scan; coefficients no scan sent stay zero (a missing refinement
//!     gives a blurrier image, not an error). A run that puts a
//!     coefficient, or a refined new coefficient, past `Se` is an error (a
//!     `ZRL` that ends at or past `Se` ends the block, as libjpeg does), and
//!     so is a coefficient that does not fit 16 bits, as in choice 7. The
//!     EOB run does not outlast a restart interval.
//! 11. **Progressive memory**: the whole coefficient plane is kept, as `i16`
//!     in the work buffer, and the inverse DCT runs at EOI into 8-bit planes
//!     in the same memory (the argument is on
//!     `progressive::finish_plane`): `2 * 64 * bw * bh + 64 * bw` bytes per
//!     component. That is at most `2 * (w + 31) * (h + 35)`, so every 1 or
//!     3-component frame fits choice 8's buffer and a 4-component frame
//!     fits when its components are subsampled enough that they add up to
//!     three full ones; a 4-component full-resolution progressive frame
//!     (4:4:4:4 CMYK) is refused with `Unsupported`, at its frame header.
//!
//! # Verification
//!
//! Tier 1 target (`Cargo.toml`): the Kani harnesses of `proofs.rs` and
//! `idct.rs`, listed with their bounds in the README, cover the leaf
//! functions, the block decoder and (item 6.6) one bit of each progressive
//! scan kind (`progressive.rs`; written, not yet run by Kani, README);
//! **the marker state machine and `step` itself have none yet** (README,
//! "What Kani does not cover"). The invariant
//! is `Jpeg::state_inv` (`decoder.rs`); every index is a checked `get` and
//! every operation checked, so `inv` is about the ranges of counters, not
//! memory.

mod bits;
mod block;
mod decoder;
mod exif;
mod header;
mod huffman;
mod idct;
mod markers;
mod output;
mod progressive;
#[cfg(kani)]
mod proofs;

pub use decoder::{Colour, Jpeg};
