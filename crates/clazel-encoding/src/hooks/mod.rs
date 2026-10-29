//! "BOM sniff" and "decode", hooks for standards (Encoding §6).
//!
//! - [`spec`]: a step-by-step transcription of the hooks.
//! - [`contract`]: what the executable hooks are proven to satisfy.
//! - [`decode`]: the executable hooks, and their proofs.
//! - [`independent`]: a second transcription, proven equal to [`spec`].

pub mod contract;
pub mod decode;
pub mod independent;
pub mod spec;
