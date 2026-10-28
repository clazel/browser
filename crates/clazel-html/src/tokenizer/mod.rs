//! The HTML tokenizer (HTML §13.2.3.5, §13.2.4, §13.2.5).
//!
//! - [`spec`]: a state-by-state transcription of the standard. This is the
//!   part a human must check against the standard.
//! - [`termination`]: why the spec's state machine terminates.
//! - [`contract`]: what the executable tokenizer is proven to satisfy.

pub mod contract;
pub mod spec;
pub mod termination;
