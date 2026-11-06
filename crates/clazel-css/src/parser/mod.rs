//! CSS parsing (phase-5.md items 5.3 and 5.4), from CSS Syntax Level 3.
//!
//! - [`spec`]: the transcription of the standard.
//! - [`contract`]: what the executable code is proven to satisfy, and the statements of
//!   the theorems planned about the spec.
//! - [`exec_parse`]: the entry points, and [`exec_anb`] those of An+B. [`exec`],
//!   [`exec_lists`], [`exec_declaration`] and [`exec_rules`] are what they call, and
//!   [`rows`] is what they build.
//! - [`examples`]: concrete sheets, evaluated on the spec.
//! - [`lemmas`]: theorems proven about the spec.
//! - [`termination`]: why the spec's loops always go forward.

pub mod contract;
pub mod examples;
pub mod exec;
pub mod exec_anb;
pub mod exec_declaration;
pub mod exec_lists;
pub mod exec_parse;
pub mod exec_rules;
pub mod lemmas;
pub mod rows;
pub mod spec;
pub mod termination;
