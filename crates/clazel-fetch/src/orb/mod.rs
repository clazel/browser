//! Opaque-response blocking (item 6.17, decision 6.0(i) B).
//!
//! - [`spec`]: the Fetch standard's opaque-response-safelist check, its MIME
//!   type sets and where the kernel applies it.
//! - [`contract`]: what the executable functions are proven to satisfy.

pub mod contract;
pub mod spec;
