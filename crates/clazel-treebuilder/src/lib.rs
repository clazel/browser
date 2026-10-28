//! The HTML tree builder (Phase 4 items 4.9 to 4.11): HTML §13.2.6's tree
//! construction as a one-token step over a `clazel-dom` arena, with the
//! tokenizer as a parameter.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`spec`]: the transcription, split by section and insertion mode.

pub mod spec;
