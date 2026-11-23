//! Opaque-response blocking (item 6.17, decision 6.0(i) B).
//!
//! - [`spec`]: the Fetch standard's opaque-response-safelist check, its MIME
//!   type sets and where the kernel applies it.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`tables`] and [`check`]: the executable functions.
//! - [`lemmas`]: facts proven about the spec, among them `theorem_orb`.
//! - [`examples`]: concrete responses the spec is evaluated on.

pub mod check;
pub mod contract;
pub mod examples;
pub mod lemmas;
pub mod spec;
pub mod tables;
