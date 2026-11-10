//! Layout for Clazel (phase-5.md, crate `clazel-layout`).
//!
//! So far this crate holds only font matching (item 5.10, [`fonts`]): which
//! face draws each character of a run, given the computed `font-family`,
//! `font-weight`, `font-stretch` and `font-style`. The box tree, block,
//! inline and table formatting, white space, line breaking, shaping and the
//! display list (items 5.11 to 5.16) are not started.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod fonts;
