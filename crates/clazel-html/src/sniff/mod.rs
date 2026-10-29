//! The encoding sniffing algorithm (HTML §13.2.3.2) and changing the
//! encoding while parsing (§13.2.3.4).
//!
//! - [`spec`]: a step-by-step transcription of the standard.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`exec`]: the executable functions, and their proofs.

pub mod contract;
pub mod exec;
pub mod spec;
