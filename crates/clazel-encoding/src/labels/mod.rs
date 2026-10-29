//! Encodings, their names and labels, and "get an encoding" (Encoding §4.2).
//!
//! - [`data`]: the standard's table of encodings and labels, generated
//!   from the vendored `encodings.json` (`cargo xtask tables`).
//! - [`spec`]: a step-by-step transcription of the standard.
//! - [`contract`]: what the executable functions are proven to satisfy.

pub mod contract;
pub mod data;
pub mod spec;
