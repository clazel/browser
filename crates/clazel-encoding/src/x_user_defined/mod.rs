//! The x-user-defined decoder (Encoding §14.5).
//!
//! - [`spec`]: a step-by-step transcription of the decoder.
//! - [`contract`]: what the executable decoder is proven to satisfy.
//! - [`decode`]: the executable decoder, and its proof.
//! - [`independent`]: a second transcription, proven equal to [`spec`],
//!   and the lemma that it emits only scalar values.

pub mod contract;
pub mod decode;
pub mod independent;
pub mod spec;
