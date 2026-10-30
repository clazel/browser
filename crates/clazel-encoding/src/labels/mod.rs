//! Encodings, their names and labels, and "get an encoding" (Encoding §4.2).
//!
//! - [`data`]: the standard's table of encodings and labels, generated
//!   from the vendored `encodings.json` (`cargo xtask tables`).
//! - [`spec`]: a step-by-step transcription of the standard.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`exec`]: the executable functions, and their proofs.
//! - [`lemmas`]: facts proven about the spec and the table.
//! - [`independent`]: a second transcription, proven equal to [`spec`].

pub mod contract;
pub mod data;
pub mod exec;
pub mod independent;
pub mod lemmas;
pub mod spec;
