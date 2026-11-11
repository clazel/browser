//! Layout for Clazel (phase-5.md, crate `clazel-layout`).
//!
//! So far this crate holds font matching (item 5.10, [`fonts`]): which face
//! draws each character of a run, given the computed `font-family`,
//! `font-weight`, `font-stretch` and `font-style`; and shaping (item 5.11,
//! [`shape`]): a run in one face to glyphs, advances and pair kerning, placed
//! in 26.6 fixed point at the used size. The box tree, block, inline and
//! table formatting, white space, line breaking and the display list (items
//! 5.12 to 5.16) are not started.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod fonts;
pub mod shape;
