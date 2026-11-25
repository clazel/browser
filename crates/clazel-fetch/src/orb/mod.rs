//! Opaque-response blocking (ORB): the opaque-response-safelist check of
//! whatwg/fetch pull request #1442 (item 7.16, and phase-6.md 6.0(i)'s B).
//!
//! - [`spec`]: the check, citing its steps, with "extract a MIME type" and
//!   "determine nosniff" from the Fetch Standard.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`check`]: the executable check, proven to meet the contract.
//! - [`lemmas`]: facts about the check the standard states or rests on.
//! - [`examples`]: concrete responses and the check's verdict on them.

pub mod check;
pub mod contract;
pub mod examples;
pub mod lemmas;
pub mod spec;
