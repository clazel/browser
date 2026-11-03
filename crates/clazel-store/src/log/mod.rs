//! One bucket's log file: its header, its records, the state they build,
//! and what opening a file recovers (design note 3.10a.0).
//!
//! - [`spec`]: the format and the recovery rule.
//! - [`contract`]: what the executable encoder and recovery will be proven
//!   to satisfy.

pub mod contract;
pub mod spec;
