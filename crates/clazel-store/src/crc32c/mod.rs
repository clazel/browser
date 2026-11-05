//! CRC32C, the check value of every record (RFC 7143 §13.1).
//!
//! - [`spec`]: a step-by-step transcription of §13.1.
//! - [`contract`]: what the executable function will be proven to satisfy.

pub mod contract;
pub mod examples;
pub mod exec;
pub mod spec;
