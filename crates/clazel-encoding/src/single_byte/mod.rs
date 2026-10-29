//! The legacy single-byte encodings (Encoding §9).
//!
//! - [`data`]: the 27 single-byte indexes, generated from the vendored
//!   `indexes.json` (`cargo xtask tables`).
//! - [`spec`]: a step-by-step transcription of the decoder and encoder.
//! - [`contract`]: what the executable decoder and encoder are proven to
//!   satisfy.

pub mod contract;
pub mod data;
pub mod spec;
