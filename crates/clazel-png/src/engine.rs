//! The zlib engine the decoder runs the image data through, as a trait.
//!
//! PNG 3rd edition 10.1 and 10.2: the image data is one zlib stream (RFC
//! 1950) holding the scanlines. The decoder needs only the interface of
//! `clazel_deflate::stream::Inflater::step`, so it is generic over it:
//! [`Inflater`] is the real engine, and the Kani harnesses (`proofs.rs`) use
//! an engine that answers anything the contract allows, so what they prove
//! of the PNG step holds **for every behaviour of a zlib engine** that obeys
//! the contract below, not only for the one `clazel-deflate` has (whose own
//! step is not proven; see the README).
//!
//! The trait also fixes two sizes the work buffer is cut to, so that the
//! proofs can run at small ones: the window (32,768 bytes for zlib, RFC 1951
//! 3.2.5) and the palette's entries (256, 11.2.2).

use clazel_deflate::stream::{Format, Inflater, Status, WINDOW_LEN};

/// Why [`Engine::step`] returned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    /// All of `src` was read; the stream needs more.
    NeedInput,
    /// `dst` is full; the stream has more output.
    NeedOutput,
    /// The stream is complete (its checksum read and matched).
    Done,
    /// The stream is wrong or longer than the limit.
    Failed,
}

/// What one [`Engine::step`] did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Progress {
    /// Bytes of `src` read; the contract says at most `src.len()`.
    pub consumed: usize,
    /// Bytes written to `dst`; the contract says at most `dst.len()`.
    pub produced: usize,
    /// Why it stopped.
    pub outcome: Outcome,
}

/// A resumable zlib decoder.
///
/// Contract of [`Engine::step`]: `consumed <= src.len()`, `produced <=
/// dst.len()`, it writes only `dst[..produced]` and the window it is given,
/// and once it says `Done` or `Failed` it says so on every later call. The
/// PNG decoder does not rely on more: a `consumed` or `produced` over the
/// length is treated as a failed stream.
pub trait Engine: Sized {
    /// The bytes of window `step` needs (all it will touch).
    const WINDOW: usize;
    /// The palette's capacity in entries, 256 (11.2.2); proofs use fewer.
    const PALETTE_ENTRIES: usize;

    /// A fresh stream that fails rather than produce over `limit` bytes.
    fn new(limit: u64) -> Self;

    /// Decodes as much as `src` and `dst` allow, using `window`.
    fn step(&mut self, src: &[u8], dst: &mut [u8], window: &mut [u8]) -> Progress;
}

impl Engine for Inflater {
    const WINDOW: usize = WINDOW_LEN;
    const PALETTE_ENTRIES: usize = 256;

    fn new(limit: u64) -> Inflater {
        Inflater::new(Format::Zlib, limit)
    }

    fn step(&mut self, src: &[u8], dst: &mut [u8], window: &mut [u8]) -> Progress {
        let s = Inflater::step(self, src, dst, window);
        Progress {
            consumed: s.consumed,
            produced: s.produced,
            outcome: match s.status {
                Status::NeedInput => Outcome::NeedInput,
                Status::NeedOutput => Outcome::NeedOutput,
                Status::Done => Outcome::Done,
                Status::Failed(_) | Status::BadWindow => Outcome::Failed,
            },
        }
    }
}
