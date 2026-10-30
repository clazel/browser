//! The replacement encoding's decoder (Encoding §14.1).
//!
//! - [`spec`]: a step-by-step transcription of the decoder.
//! - [`contract`]: what the executable decoder is proven to satisfy.
//! - [`decode`]: the executable decoder, and its proof.
//! - [`independent`]: a second transcription, proven equal to [`spec`].

pub mod contract;
pub mod decode;
pub mod independent;
pub mod spec;
