//! The decoder shape (phase-6.md item 6.3): the one interface every image
//! decoder of Phase 6 implements (GIF, PNG, JPEG, WebP, and 6.11a's SVG),
//! the RGBA8 buffer rules, and the Kani harness template each tier 1
//! decoder instantiates.
//!
//! # Where this lives, and why
//!
//! The plan put this as module `shape` of `clazel-image` (tier 0). It is a
//! crate of its own instead, for two reasons. (1) The decoders implement
//! [`Decoder`] and `clazel-image` dispatches to the decoders, so a `shape`
//! module inside `clazel-image` would make a dependency cycle. (2) A tier 1
//! crate's claim covers its own files and the workspace crates it depends on
//! (docs/VERIFICATION.md): a tier 1 decoder built on a tier 0 crate would
//! rest on code with no harness, and `clazel-image` is where policy lives
//! (which format, how much memory, which frame). This crate has no policy
//! and no dependencies, and its target is tier 1 (harnesses in `proofs.rs`
//! over the size arithmetic and premultiplication).
//!
//! # The interface, WUFFS style
//!
//! Nothing here allocates. The caller owns the memory and sizes it from the
//! [`Config`]:
//!
//! 1. [`Decoder::decode_config`] reads the first bytes of the stream (a
//!    prefix, re-presented whole each time) and says
//!    [`ConfigStatus::NeedMore`] or gives the [`Config`]: format, width,
//!    height, frame count if known, and the [`Coding`] where a format has
//!    codings whose work space differs. Its sizes obey [`MAX_SIDE`] and
//!    [`MAX_PIXELS`] ([`Config::new`] refuses others).
//! 2. The caller allocates [`Config::rgba_len`] bytes for the frame and
//!    [`Decoder::work_len`] bytes of work space, a function of the config
//!    that the decoder states (its window, its tables, a row), then builds
//!    [`Buffers`] ([`Buffers::new`] checks the sizes).
//! 3. [`Decoder::start`] makes the state, a fixed-size value. The stream is
//!    then fed **from its first byte** (the bytes already given to
//!    `decode_config` are given again), in chunks of any length including
//!    zero, to [`Decoder::step`], which returns [`Status::NeedMore`] (every
//!    byte of the chunk was used and more is needed), [`Status::FrameDone`]
//!    (the pixels hold the frame; `consumed` bytes of this chunk were used
//!    and the rest belong to what follows), or an [`Error`]. After
//!    `FrameDone` the next `step` starts the next frame (a decoder of a
//!    format with one frame says [`Error::NoMoreFrames`]). After any error
//!    the decoder is spent and says [`Error::Spent`].
//!
//! Pixels are **straight** RGBA8 (not premultiplied), row-major, top row
//! first, 4 bytes per pixel. [`premultiply`] and [`premultiply_in_place`]
//! make premultiplied ones, for the renderer.
//!
//! # `step` and `inv`
//!
//! [`Decoder::inv`] is the decoder's invariant over its state and the
//! buffers: at least that the buffer lengths are the ones the config
//! implies, plus whatever makes `step` safe (every index it computes is in
//! range, counters are in their ranges). [`Decoder::step`] must keep it, on
//! every outcome, and must satisfy the contract in its documentation. The
//! [`decoder_step_harness!`] macro states that for any state with `inv`,
//! any buffer contents and any chunk up to a stated length, one `step`
//! does not panic, writes only inside the buffers, obeys the contract and
//! keeps `inv`.
//!
//! # Modelling choices
//!
//! - **Limits (6.0(j))**: width and height at most [`MAX_SIDE`] = 2^14, at
//!   most [`MAX_PIXELS`] = 2^26 pixels (so 2^28 bytes of RGBA, which fits a
//!   32-bit `usize`), both at least 1. An image over a limit is a broken
//!   image: [`Config::new`] says [`SizeError`].
//! - **Config as a prefix function**, not a state: the caller keeps the
//!   prefix (it needs the bytes again anyway) and chooses how much it will
//!   keep before giving up; that is policy, so it is not here.
//! - **One error type** for every decoder, so the dispatcher in
//!   `clazel-image` need not be generic; reasons are static strings.
//! - **`FrameDone` carries nothing**: a decoder with frame timing or
//!   disposal (GIF, APNG, WebP) extends the shape in its own item, with its
//!   own accessor on its state, when 6.0(d)'s needs are concrete.
//! - **The harness's bounds** are the instantiator's: it names the largest
//!   chunk, pixel buffer and work buffer. A decoder whose state is too big
//!   to enumerate at its real sizes proves the step at small ones and says
//!   so in its README, as the other Tier 1 crates do.

pub mod buffers;
pub mod harness;
pub mod premultiply;
pub mod size;

#[cfg(kani)]
mod proofs;
#[cfg(any(test, kani))]
mod toy;

pub use buffers::Buffers;
pub use premultiply::{premultiply, premultiply_in_place};
pub use size::{
    BYTES_PER_PIXEL, MAX_PIXELS, MAX_RGBA_BYTES, MAX_SIDE, SizeError, pixel_count, rgba_len,
};

/// The formats a decoder can be for. [`Format::Raw`] is the test-only toy
/// of this crate; no shipped decoder reports it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Format {
    /// PNG, with APNG.
    Png,
    /// JPEG.
    Jpeg,
    /// GIF.
    Gif,
    /// WebP.
    Webp,
    /// SVG (6.11a), rasterized to the size it is asked for.
    Svg,
    /// The toy format of this crate's tests.
    Raw,
}

/// How many frames the stream has, as far as the first bytes say.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FrameCount {
    /// The header states it (at least 1).
    Known(u32),
    /// Only decoding to the end will say (GIF).
    Unknown,
}

/// How a stream is coded, where one format has codings whose work space
/// differs (items 6.6 and 6.9). `decode_config` sets it from the first bytes
/// and `work_len` reads it, so a stream pays only for the work space of its
/// own coding. [`Config::new`] gives [`Coding::Base`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Coding {
    /// The format's plain coding: sequential JPEG, lossless WebP, and every
    /// other format.
    Base,
    /// Progressive JPEG (SOF2): every coefficient is kept until the end.
    Progressive,
    /// A WebP that has, or may have, lossy (VP8) frames: a simple `VP8 `
    /// file, or an extended one, whose image chunks the first bytes do not
    /// show.
    Lossy,
}

/// What `decode_config` reads from the first bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Config {
    format: Format,
    width: u32,
    height: u32,
    frames: FrameCount,
    coding: Coding,
}

impl Config {
    /// A config, if the size is within the limits (6.0(j)) and a known
    /// frame count is at least 1.
    pub fn new(
        format: Format,
        width: u32,
        height: u32,
        frames: FrameCount,
    ) -> Result<Config, Error> {
        rgba_len(width, height)?;
        if frames == FrameCount::Known(0) {
            return Err(Error::Malformed("a frame count of zero"));
        }
        Ok(Config {
            format,
            width,
            height,
            frames,
            coding: Coding::Base,
        })
    }

    /// The same config with another coding, if the format has it:
    /// [`Coding::Progressive`] only for JPEG, [`Coding::Lossy`] only for
    /// WebP, [`Coding::Base`] for every format.
    pub fn with_coding(self, coding: Coding) -> Result<Config, Error> {
        match (coding, self.format) {
            (Coding::Base, _)
            | (Coding::Progressive, Format::Jpeg)
            | (Coding::Lossy, Format::Webp) => Ok(Config { coding, ..self }),
            _ => Err(Error::Unsupported("a coding this format does not have")),
        }
    }

    /// The coding (see [`Coding`]).
    pub fn coding(&self) -> Coding {
        self.coding
    }

    /// The format.
    pub fn format(&self) -> Format {
        self.format
    }

    /// Width in pixels, 1 to [`MAX_SIDE`].
    pub fn width(&self) -> u32 {
        self.width
    }

    /// Height in pixels, 1 to [`MAX_SIDE`].
    pub fn height(&self) -> u32 {
        self.height
    }

    /// The frame count if the header says.
    pub fn frames(&self) -> FrameCount {
        self.frames
    }

    /// The bytes of a frame's pixel buffer: `4 * width * height`.
    pub fn rgba_len(&self) -> Result<usize, SizeError> {
        rgba_len(self.width, self.height)
    }

    /// The bytes of one row of pixels: `4 * width`.
    pub fn row_len(&self) -> Result<usize, SizeError> {
        rgba_len(self.width, 1)
    }
}

/// What `decode_config` says of a prefix.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConfigStatus {
    /// The prefix is a valid start of a header but too short: give more.
    NeedMore,
    /// The config.
    Ready(Config),
}

/// What one `step` reports when it did not fail.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    /// Every byte of the chunk was used; more is needed.
    NeedMore,
    /// A frame is complete in the pixel buffer.
    FrameDone,
}

/// The result of a `step` that did not fail.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Step {
    /// Bytes of the chunk used, at most its length. With
    /// [`Status::NeedMore`] it is the whole chunk.
    pub consumed: usize,
    /// What happened.
    pub status: Status,
}

/// Why a decode failed. Every variant makes the image a broken image.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The size is outside the limits (6.0(j)).
    Size(SizeError),
    /// The bytes are not a valid stream of the format.
    Malformed(&'static str),
    /// Valid, but a feature this browser does not decode.
    Unsupported(&'static str),
    /// The buffers do not fit the config (see [`Buffers::new`]).
    Buffers,
    /// `step` after the last frame of a stream.
    NoMoreFrames,
    /// `step` after an earlier error.
    Spent,
    /// The stream ended before the frame was done (said by the caller,
    /// which knows when the input ends).
    Truncated,
}

impl From<SizeError> for Error {
    fn from(e: SizeError) -> Error {
        Error::Size(e)
    }
}

/// The interface every Phase 6 decoder implements.
///
/// The state is a plain fixed-size value: `start` allocates nothing, and
/// no method allocates. A decoder's pixel output goes only into
/// `buffers.pixels` and its scratch only into `buffers.work`.
pub trait Decoder: Sized {
    /// Reads the first bytes: [`ConfigStatus::NeedMore`] if `prefix` is a
    /// valid start of a header that is not complete, the [`Config`] if it
    /// is, an error if no stream starts so (or the size is over a limit).
    /// Pure: the same prefix, the same answer; a longer prefix of a stream
    /// that was `Ready` gives the same config.
    fn decode_config(prefix: &[u8]) -> Result<ConfigStatus, Error>;

    /// The bytes of work space `step` needs for this config, a function of
    /// the config alone. May be 0.
    fn work_len(config: &Config) -> Result<usize, Error>;

    /// The state at the first byte of the stream. Fails if the config is
    /// not one this decoder reads (another format, a size it cannot).
    fn start(config: &Config) -> Result<Self, Error>;

    /// The config this state decodes.
    fn config(&self) -> &Config;

    /// Uses a chunk (any length, including 0) of the stream. Contract:
    ///
    /// - never panics, whatever the bytes and the state, if
    ///   `self.inv(buffers)` held on entry;
    /// - writes only `buffers.pixels` and `buffers.work`;
    /// - `self.inv(buffers)` holds on exit, **also after an error**;
    /// - `Ok` has `consumed <= chunk.len()`, and `Status::NeedMore` has
    ///   `consumed == chunk.len()` (so a caller cannot loop without
    ///   progress);
    /// - allocates nothing.
    fn step(&mut self, chunk: &[u8], buffers: &mut Buffers<'_>) -> Result<Step, Error>;

    /// The invariant of state and buffers. It includes that the buffers
    /// have the lengths [`Config::rgba_len`] and [`Decoder::work_len`] of
    /// this state's config (which [`Buffers::new`] gives), and whatever
    /// else `step` needs for its indices and counters.
    fn inv(&self, buffers: &Buffers<'_>) -> bool;
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cfg(f: Format) -> Result<Config, Error> {
        Config::new(f, 2, 2, FrameCount::Known(1))
    }

    #[test]
    fn coding_only_where_the_format_has_it() -> Result<(), Error> {
        let (jpeg, webp) = (cfg(Format::Jpeg)?, cfg(Format::Webp)?);
        assert_eq!(jpeg.coding(), Coding::Base);
        assert_eq!(
            jpeg.with_coding(Coding::Progressive)?.coding(),
            Coding::Progressive
        );
        assert_eq!(webp.with_coding(Coding::Lossy)?.coding(), Coding::Lossy);
        assert!(jpeg.with_coding(Coding::Lossy).is_err());
        assert!(webp.with_coding(Coding::Progressive).is_err());
        assert!(cfg(Format::Png)?.with_coding(Coding::Progressive).is_err());
        for f in [
            Format::Png,
            Format::Jpeg,
            Format::Gif,
            Format::Webp,
            Format::Svg,
            Format::Raw,
        ] {
            assert_eq!(cfg(f)?.with_coding(Coding::Base)?, cfg(f)?);
        }
        Ok(())
    }
}
