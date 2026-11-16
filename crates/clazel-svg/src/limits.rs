//! The fixed sizes of this decoder. Under Kani the two big ones are small,
//! so the model checker can enumerate the buffers; the code is the same
//! code with other constants (the README says so).

/// The most bytes of document the decoder keeps (listed choice 8). HN's two
/// files are 315 and 131 bytes.
pub(crate) const DOC_MAX: usize = if cfg!(kani) { 24 } else { 8192 };

/// The most edges (line segments, closing ones included) of one path.
pub(crate) const MAX_EDGES: usize = if cfg!(kani) { 4 } else { 256 };

/// The most attributes the tokenizer keeps for one tag.
pub(crate) const MAX_ATTRS: usize = 4;

/// Sub-scanlines per pixel row: coverage is the exact horizontal overlap of
/// the filled spans, averaged over this many evenly spaced scanlines.
pub(crate) const SUB: i64 = 16;

/// Device coordinates are in 1/256 of a pixel.
pub(crate) const UNIT: i64 = 256;

/// The largest device coordinate magnitude accepted, in 1/256 pixel
/// (2^30, so 2^22 pixels): keeps every product below in an `i64`.
pub(crate) const MAX_DEVICE: i64 = 1 << 30;

/// Fixed point of the numbers read from the document: units of 2^-16.
pub(crate) const ONE: i64 = 1 << 16;

/// The largest magnitude of a number read, in fixed point: 2^20.
pub(crate) const MAX_NUMBER: i64 = 1 << 36;
