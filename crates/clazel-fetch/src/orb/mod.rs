//! Opaque-response blocking (ORB): the opaque-response-safelist check of
//! whatwg/fetch pull request #1442 (item 7.16, and phase-6.md 6.0(i)'s B).
//!
//! - [`spec`]: the check, citing its steps, with "extract a MIME type" and
//!   "determine nosniff" from the Fetch Standard.
//! - [`contract`]: what the executable functions are proven to satisfy.

pub mod contract;
pub mod spec;
