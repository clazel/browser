//! UTF-16BE and UTF-16LE decoding (Encoding §14.2 to §14.4).
//!
//! - [`spec`]: a step-by-step transcription of the shared UTF-16 decoder.
//! - [`contract`]: what the executable decoder is proven to satisfy.

pub mod contract;
pub mod spec;
