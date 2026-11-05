//! The input byte stream of a style sheet (phase-5.md item 5.2), from CSS Syntax Level 3
//! §3.2.
//!
//! - [`spec`]: the transcription of the standard.
//! - [`contract`]: what the executable code is proven to satisfy.
//! - [`examples`]: concrete inputs, evaluated on the spec.
//! - [`exec`]: the code.
//! - [`lemmas`]: theorems proven about the spec.

pub mod contract;
pub mod examples;
pub mod exec;
pub mod lemmas;
pub mod spec;
