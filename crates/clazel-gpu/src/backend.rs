//! What a backend is given: a frame of operations in order, and the instance data
//! the fixed shaders read. Backends (Metal, Vulkan, Direct3D 12, and the software
//! [`crate::soft::SoftBackend`]) differ only below [`Backend`].
//!
//! # Modelling choices
//!
//! - **One pipeline, one quad per item.** Each fill and each mask draw is one
//!   [`Quad`], 9 little-endian 32-bit words ([`QUAD_WORDS`]), drawn as two
//!   triangles by six vertices of one instance. A fill has `columns` 0 and full
//!   coverage; a mask reads its coverage from the atlas. The vertex shader reads
//!   the quad by instance index and the fragment shader the coverage by pixel, so
//!   there is no vertex format, no sampler and no texture coordinate.
//! - **Integers to the GPU.** Quad corners are whole pixels inside the viewport
//!   (0 to 8192), converted to floating point in the shader, where every one is
//!   exact. Mask origins are within ±2^23 and offsets below 2^26, so the shader's
//!   index arithmetic fits in 32 bits (`atlas::texel_index`).
//! - **The shaders bound their own reads**: the vertex shader draws nothing for an
//!   instance at or past `quad_count`, and the fragment shader reads coverage 0 for
//!   an index at or past `atlas_bytes`. Rust's types cannot check what a shader
//!   reads, so this bound, the batching that sets the counts, and their tests are
//!   the evidence.
//! - **Operations run in order**: an atlas upload or replacement between two draws
//!   is seen by the later draw and not by the earlier one.
//! - **Each frame starts from transparent black** (0, 0, 0, 0); the list paints the
//!   canvas.

use crate::geom::{Rect, Viewport};

/// Words in a [`Quad`].
pub const QUAD_WORDS: usize = 9;

/// Bytes in a [`Quad`].
pub const QUAD_BYTES: usize = QUAD_WORDS * 4;

/// One rectangle to fill or one mask to draw, as the shaders read it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Quad {
    /// The covered pixels, inside the viewport and not empty.
    pub rect: Rect,
    /// The mask's top left pixel in the target (a fill: 0, 0).
    pub origin_x: i32,
    /// See `origin_x`.
    pub origin_y: i32,
    /// The mask's first byte in the atlas (a fill: 0).
    pub offset: u32,
    /// The mask's width (a fill: 0, meaning full coverage).
    pub columns: u32,
    /// Premultiplied `0xAARRGGBB`.
    pub colour: u32,
}

impl Quad {
    /// The words the shaders read, in order: `x0, y0, x1, y1, origin_x, origin_y,
    /// offset, columns, colour`, signed values in two's complement.
    pub fn words(&self) -> [u32; QUAD_WORDS] {
        [
            self.rect.x0.cast_unsigned(),
            self.rect.y0.cast_unsigned(),
            self.rect.x1.cast_unsigned(),
            self.rect.y1.cast_unsigned(),
            self.origin_x.cast_unsigned(),
            self.origin_y.cast_unsigned(),
            self.offset,
            self.columns,
            self.colour,
        ]
    }
}

/// Every quad as little-endian bytes, as the shaders read them.
pub fn quad_bytes(quads: &[Quad]) -> Vec<u8> {
    let mut out = Vec::with_capacity(quads.len().saturating_mul(QUAD_BYTES));
    for q in quads {
        for w in q.words() {
            out.extend_from_slice(&w.to_le_bytes());
        }
    }
    out
}

/// One step of a frame.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    /// Replace the atlas with a new store of `capacity` bytes, contents undefined.
    /// Draws already recorded keep reading the old store.
    Atlas {
        /// Bytes, a power of two.
        capacity: u32,
    },
    /// Copy `Frame::bytes[start .. start + len]` into the atlas at `offset`. All
    /// three are multiples of 4 (`atlas.rs`).
    Upload {
        /// The first atlas byte written.
        offset: u32,
        /// The first byte in [`Frame::bytes`].
        start: usize,
        /// How many bytes.
        len: usize,
    },
    /// Draw `Frame::quads[first .. first + count]` with this scissor rectangle.
    Draw {
        /// Inside the viewport and not empty.
        scissor: Rect,
        /// The first quad.
        first: u32,
        /// How many, at least 1.
        count: u32,
    },
}

/// Everything a backend needs to draw one list.
#[derive(Debug, Default)]
pub struct Frame {
    /// The target's size.
    pub viewport: Option<Viewport>,
    /// What to do, in order.
    pub ops: Vec<Op>,
    /// The quads the draws name.
    pub quads: Vec<Quad>,
    /// The coverage the uploads name.
    pub bytes: Vec<u8>,
}

/// A foreign call failed, the device was lost, or memory ran out. The GPU process
/// ends; what happens next is item 5.17c's.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BackendError {
    /// What failed: the API call or the check.
    pub what: &'static str,
    /// The API's code, if it gave one.
    pub code: i64,
}

/// A way of drawing a [`Frame`].
pub trait Backend {
    /// Draw the frame into the target, which then holds exactly its result, and
    /// return when it is finished. The atlas carries over to the next frame.
    fn draw_frame(&mut self, frame: &Frame) -> Result<(), BackendError>;

    /// Copy the target's pixels out, RGBA8, rows from the top, packed.
    fn read_pixels(&mut self, out: &mut Vec<u8>) -> Result<(), BackendError>;
}

#[cfg(test)]
mod tests {
    use super::{QUAD_BYTES, Quad, quad_bytes};
    use crate::geom::Rect;

    #[test]
    fn a_quad_is_nine_little_endian_words() {
        let q = Quad {
            rect: Rect {
                x0: 1,
                y0: 2,
                x1: 3,
                y1: 4,
            },
            origin_x: -1,
            origin_y: 5,
            offset: 6,
            columns: 7,
            colour: 0x8040_2010,
        };
        let b = quad_bytes(&[q]);
        assert_eq!(b.len(), QUAD_BYTES);
        assert_eq!(b.get(0..4), Some(&[1, 0, 0, 0][..]));
        assert_eq!(b.get(16..20), Some(&[255, 255, 255, 255][..]));
        assert_eq!(b.get(32..36), Some(&[0x10, 0x20, 0x40, 0x80][..]));
    }
}
