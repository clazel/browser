//! CSS tokenization (phase-5.md item 5.2), from CSS Syntax Level 3.
//!
//! - [`spec`]: the transcription of the standard.
//! - [`contract`]: what the executable code is proven to satisfy.
//! - [`exec`]: the tokenizer.
//! - [`lemmas`]: theorems proven about the spec.
//! - [`termination`]: why the spec's recursive functions end.

pub mod contract;
pub mod exec;
pub mod lemmas;
pub mod spec;
pub mod termination;
