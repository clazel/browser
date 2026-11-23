//! Forms: HTML's form owner and "constructing the entry list" (Phase 6
//! item 6.13; item 6.14 adds the encodings and the submission algorithm).
//!
//! Spec: HTML Standard, commit `0793d3d8544eee95a862e6637130a8106c3d11ca`
//! (see [`spec`]'s header for the sections). Tier: see
//! `[package.metadata.clazel]` in `Cargo.toml` and `docs/VERIFICATION.md`.
//!
//! - [`spec`]: a step-by-step transcription of the standard over a
//!   `clazel-dom` arena, with the control state in a side table.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`independent`]: a second transcription of the string algorithms,
//!   proven equal to [`spec`]'s.

pub mod contract;
pub mod examples;
pub mod exec;
pub mod independent;
pub mod lemmas;
pub mod spec;
pub mod submit;
