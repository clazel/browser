//! One bucket's log file: its header, its records, the state they build,
//! and what opening a file recovers (design note 3.10a.0).
//!
//! - [`spec`]: the format and the recovery rule.
//! - [`contract`]: what the executable encoder and recovery will be proven
//!   to satisfy.
//! - [`exec`]: the header and record encoders, proven to meet it.
//! - [`lemmas`]: the encodings read apart from the front, so the list
//!   recovery picks is unique.
//! - [`read`]: recovery, proven to meet it.
//! - [`compact`]: compaction, proven to meet it.
//! - [`theorems`]: the design note's theorems 1 to 3 (any prefix, the
//!   whole file, compaction).

pub mod compact;
pub mod contract;
pub mod exec;
pub mod lemmas;
pub mod read;
pub mod spec;
pub mod theorems;
