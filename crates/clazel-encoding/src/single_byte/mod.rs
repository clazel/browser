//! The legacy single-byte encodings (Encoding §9).
//!
//! - [`data`]: the 27 single-byte indexes, generated from the vendored
//!   `indexes.json` (`cargo xtask tables`).
//! - [`spec`]: a step-by-step transcription of the decoder and encoder.
//! - [`contract`]: what the executable decoder and encoder are proven to
//!   satisfy.
//! - [`decode`], [`encode`]: the executable decoder and encoder, and their
//!   proofs.
//! - [`tables`]: facts about the generated indexes, proven by evaluating
//!   them.
//! - [`lemmas`]: facts proven about the spec.
//! - [`independent`]: a second transcription, proven equal to [`spec`].

pub mod contract;
pub mod data;
pub mod decode;
pub mod encode;
pub mod independent;
pub mod lemmas;
pub mod spec;
pub mod tables;
