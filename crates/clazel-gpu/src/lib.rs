//! The GPU process's drawing (phase-5.md item 5.17b): a display list and a
//! viewport to pixels, on the GPU.
//!
//! The list comes from a renderer the GPU process must assume is compromised. It
//! is decoded and validated by `clazel-displaylist` before anything here reads
//! it, and `theorem_validated_bounds` is all this crate relies on: at most
//! 2^20 items, positions within ±2^23 and sizes up to 2^23, clips balanced and at
//! most 256 deep, mask ids below 2^16 and at most 64 MiB of live coverage. Even
//! so, every step is checked and fails with an [`Error`] rather than a panic, and
//! any error ends the GPU process (item 5.17c decides what happens next).
//!
//! # Sources
//!
//! There is no standard for this: the list's meaning is
//! `clazel_displaylist::spec`, and the drawing rules are the plan's listed choices
//! (item 5.17b), each written where it is made:
//!
//! - [`geom`]: whole-pixel rectangles, the viewport's limit.
//! - [`atlas`]: the glyph atlas, one linear store with a bump allocator.
//! - [`batch`]: the shared batching, clips as scissor rectangles.
//! - [`backend`]: the frame a backend draws, the quad format, the trait.
//! - [`soft`]: source-over in 8-bit sRGB, premultiplied, no gamma correction; the
//!   fake backend.
//! - [`reference`]: the expected pixels of a list, computed independently.
//! - `shaders/`: the fixed shaders, Metal Shading Language and GLSL for Vulkan.
//!
//! # Modelling choices
//!
//! - **The crate validates.** [`Gpu::draw`] takes the list's bytes, so a list can
//!   only reach a backend through `clazel_displaylist`'s decoder and validator, and
//!   the validator and the atlas hold the same masks between lists.
//! - **One frame at a time, finished before [`Gpu::draw`] returns**, so a backend
//!   never writes an atlas byte a frame in flight reads.
//! - **The target is the backend's.** Until item 5.18 builds the ring of shared
//!   buffers, a backend draws into a buffer it creates itself, behind
//!   [`Backend::read_pixels`] and, on Metal, `metal::Target`, which 5.18 can supply.

pub mod atlas;
pub mod backend;
pub mod batch;
pub mod blocklist;
pub mod geom;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub mod metal;
pub mod policy;
pub mod reference;
pub mod scenes;
pub mod soft;
pub mod start;

#[cfg(kani)]
mod proofs;

use std::fmt;

use clazel_displaylist::exec::{Validator, decode};

pub use backend::{Backend, BackendError, Frame};
pub use geom::Viewport;

/// Why a list was not drawn. Each one ends the GPU process.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// The bytes are not a display list.
    NotAList,
    /// The list broke a rule of the validator.
    Refused,
    /// A number was out of range where the validator's guarantees say it cannot
    /// be: a bug here, or a broken guarantee.
    Range,
    /// The atlas cannot hold the live masks (only if the validator's limit on live
    /// coverage were broken).
    AtlasFull,
    /// The backend failed: a lost device, no memory, or a failed call.
    Backend(BackendError),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::NotAList => f.write_str("the bytes are not a display list"),
            Error::Refused => f.write_str("the display list broke a rule"),
            Error::Range => f.write_str("a number was out of range"),
            Error::AtlasFull => f.write_str("the glyph atlas is full"),
            Error::Backend(e) => write!(f, "the GPU failed: {} ({})", e.what, e.code),
        }
    }
}

impl std::error::Error for Error {}

/// Drawing with one backend, keeping the masks between lists.
#[derive(Debug)]
pub struct Gpu<B: Backend> {
    validator: Validator,
    atlas: atlas::Atlas,
    backend: B,
}

impl<B: Backend> Gpu<B> {
    /// Start with no masks.
    pub fn new(backend: B) -> Gpu<B> {
        Gpu {
            validator: Validator::empty(),
            atlas: atlas::Atlas::new(),
            backend,
        }
    }

    /// Decode, validate and draw one list into a target of `viewport`'s size. On
    /// any error the GPU process must end: the masks may then disagree with the
    /// renderer's.
    pub fn draw(&mut self, bytes: &[u8], viewport: Viewport) -> Result<(), Error> {
        let items = decode(bytes).ok_or(Error::NotAList)?;
        if !self.validator.validate(&items) {
            return Err(Error::Refused);
        }
        let frame = batch::build(&items, viewport, &mut self.atlas)?;
        self.backend.draw_frame(&frame).map_err(Error::Backend)
    }

    /// The backend, to read its target.
    pub fn backend(&mut self) -> &mut B {
        &mut self.backend
    }

    /// Give the backend back, forgetting the masks.
    pub fn into_backend(self) -> B {
        self.backend
    }
}

#[cfg(test)]
mod tests;
