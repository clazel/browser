//! The encoding sniffing algorithm (HTML §13.2.3.2) and changing the
//! encoding while parsing (§13.2.3.4).
//!
//! - [`spec`]: a step-by-step transcription of the standard.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`exec`]: the executable functions, and their proofs.
//! - [`lemmas`]: facts proven about the spec.
//! - [`examples`], [`examples_attribute`]: the spec on concrete inputs,
//!   proven by evaluation.
//! - [`independent`]: the Encoding Standard's "decode" as a second text for
//!   the first steps, proven to agree.

pub mod contract;
pub mod examples;
pub mod examples_attribute;
pub mod exec;
pub mod independent;
pub mod lemmas;
pub mod spec;
