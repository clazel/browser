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
//!   is seen by the later draw and not by the earlier one. So is an image's.
//! - **An image draw is a quad too** (item 6.12). Its quad has `columns`
//!   [`IMAGE_COLUMNS`] (`u32::MAX`, which no mask has: masks are at most 2048 wide) and
//!   its `offset` is the index of an [`ImageDraw`] in [`Frame::image_draws`], 12 words
//!   ([`IMAGE_DRAW_WORDS`]) holding what a draw needs beyond a rectangle: the whole
//!   destination, the source, where the image is in the image store and its size, and
//!   the filter. The quad's rectangle is the destination cut to the viewport, as for
//!   every quad. So the quad format, the vertex shader and the one pipeline are the
//!   same for fills, masks and images; the fragment shader tells them apart by
//!   `columns`, and reads the image store and the draw table as two more storage
//!   buffers. Images are 32-bit words of premultiplied RGBA8 in the image store,
//!   filtered in the shader (`crate::images` states why there is no sampler).
//! - **The filter is defined in integers, so that it means the same everywhere.** For
//!   the destination pixel `i, j` (0-based inside the destination `w × h`) and a
//!   source rectangle `sx, sy, sw, sh`, the sample position is `sx + (2i + 1) · sw /
//!   (2w)` (the pixel's centre mapped into the source), likewise in y. *Nearest* takes
//!   the source pixel containing it. *Linear* takes the four pixels around it (the
//!   position less a half, rounded down, and the next), weighted by the fractions,
//!   **clamping to the source rectangle**, so a draw never reads a pixel outside its
//!   source rectangle, which is what makes a sprite sheet usable. The software
//!   reference computes it exactly and rounds once; the shaders compute it in floating
//!   point and may differ by a level.
//! - **Each frame starts from transparent black** (0, 0, 0, 0); the list paints the
//!   canvas.

use std::sync::Arc;

use crate::blocklist::Adapter;
use crate::geom::{Rect, Viewport};

/// Words in a [`Quad`].
pub const QUAD_WORDS: usize = 9;

/// Bytes in a [`Quad`].
pub const QUAD_BYTES: usize = QUAD_WORDS * 4;

/// The `columns` of a quad that draws an image: no mask is this wide.
pub const IMAGE_COLUMNS: u32 = u32::MAX;

/// Words in an [`ImageDraw`].
pub const IMAGE_DRAW_WORDS: usize = 12;

/// Bytes in an [`ImageDraw`].
pub const IMAGE_DRAW_BYTES: usize = IMAGE_DRAW_WORDS * 4;

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

/// What an image draw needs beyond its quad's rectangle (item 6.12).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ImageDraw {
    /// The destination's top left pixel in the target, before any cutting.
    pub x: i32,
    /// See `x`.
    pub y: i32,
    /// The destination's size, at least 1.
    pub width: u32,
    /// See `width`.
    pub height: u32,
    /// The source rectangle's top left pixel in the image, inside it.
    pub src_x: u32,
    /// See `src_x`.
    pub src_y: u32,
    /// The source's size, at least 1.
    pub src_width: u32,
    /// See `src_width`.
    pub src_height: u32,
    /// The image's first byte in the image store.
    pub offset: u32,
    /// The image's width in pixels.
    pub image_width: u32,
    /// The image's height in pixels.
    pub image_height: u32,
    /// Bilinear if true, nearest if false.
    pub linear: bool,
}

impl ImageDraw {
    /// The words the shaders read, in order: `x, y, width, height, src_x, src_y,
    /// src_width, src_height, offset, image_width, image_height, linear`, the signed
    /// ones in two's complement.
    pub fn words(&self) -> [u32; IMAGE_DRAW_WORDS] {
        [
            self.x.cast_unsigned(),
            self.y.cast_unsigned(),
            self.width,
            self.height,
            self.src_x,
            self.src_y,
            self.src_width,
            self.src_height,
            self.offset,
            self.image_width,
            self.image_height,
            u32::from(self.linear),
        ]
    }
}

/// Every image draw as little-endian bytes, as the shaders read them.
pub fn image_draw_bytes(draws: &[ImageDraw]) -> Vec<u8> {
    let mut out = Vec::with_capacity(draws.len().saturating_mul(IMAGE_DRAW_BYTES));
    for d in draws {
        for w in d.words() {
            out.extend_from_slice(&w.to_le_bytes());
        }
    }
    out
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

/// The first `row` bytes of each `pitch` bytes of `padded`: the rows of a
/// target copied with padding after each (Direct3D 12 pads a copied row to a
/// multiple of 256 bytes), packed. `None` if either is 0 or `row > pitch`.
pub fn packed_rows(padded: &[u8], pitch: usize, row: usize) -> Option<Vec<u8>> {
    if pitch == 0 || row == 0 || row > pitch {
        return None;
    }
    let mut out = Vec::with_capacity(padded.len().checked_div(pitch)?.checked_mul(row)?);
    for line in padded.chunks_exact(pitch) {
        out.extend_from_slice(line.get(..row)?);
    }
    Some(out)
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
    /// Replace the image store with a new one of `capacity` bytes, contents
    /// undefined. Draws already recorded keep reading the old store.
    Images {
        /// Bytes, a power of two.
        capacity: u32,
    },
    /// Copy these pixels into the image store at `offset`. Both are multiples of 4.
    ImageUpload {
        /// The first image-store byte written.
        offset: u32,
        /// The pixels, shared with the image store's CPU copy.
        pixels: Arc<[u8]>,
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
    /// What the quads with `columns` [`IMAGE_COLUMNS`] draw, by their `offset`.
    pub image_draws: Vec<ImageDraw>,
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

    /// What the backend's adapter is, for the blocklist (item 5.17c). Read when the
    /// GPU process starts, before any list.
    fn adapter(&self) -> Adapter;
}

#[cfg(test)]
mod tests {
    use super::{QUAD_BYTES, Quad, quad_bytes};
    use crate::geom::Rect;

    #[test]
    fn padded_rows_are_packed() {
        use super::packed_rows;
        // Two rows of 3 bytes, each padded to 4.
        let padded = [1, 2, 3, 0, 4, 5, 6, 0];
        assert_eq!(packed_rows(&padded, 4, 3), Some(vec![1, 2, 3, 4, 5, 6]));
        // No padding.
        assert_eq!(packed_rows(&padded, 4, 4), Some(padded.to_vec()));
        // A last row cut short is left out; the sizes must make sense.
        assert_eq!(packed_rows(&padded[..6], 4, 3), Some(vec![1, 2, 3]));
        assert_eq!(packed_rows(&padded, 0, 0), None);
        assert_eq!(packed_rows(&padded, 4, 0), None);
        assert_eq!(packed_rows(&padded, 3, 4), None);
        assert_eq!(packed_rows(&[], 4, 3), Some(Vec::new()));
    }

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
