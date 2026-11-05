//! CSS parsing (phase-5.md item 5.3), from CSS Syntax Level 3.
//!
//! - [`spec`]: the transcription of the standard.
//! - [`contract`]: what the executable code must be proven to satisfy, and the statements
//!   of the theorems planned about the spec.
//! - [`examples`]: concrete sheets, evaluated on the spec.
//! - [`lemmas`]: theorems proven about the spec.
//! - [`termination`]: why the spec's loops always go forward.

pub mod contract;
pub mod examples;
pub mod exec;
pub mod exec_lists;
pub mod lemmas;
pub mod rows;
pub mod spec;
pub mod termination;
