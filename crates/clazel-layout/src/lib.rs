//! Layout for Clazel (phase-5.md, crate `clazel-layout`).
//!
//! So far this crate holds font matching (item 5.10, [`fonts`]): which face
//! draws each character of a run, given the computed `font-family`,
//! `font-weight`, `font-stretch` and `font-style`; and shaping (item 5.11,
//! [`shape`]): a run in one face to glyphs, advances and pair kerning, placed
//! in 26.6 fixed point at the used size; and white space and line breaking
//! (item 5.12, [`text`]): CSS Text 3's white space processing and soft wrap
//! opportunities over UAX #14, and choosing where lines wrap. The box tree,
//! block, inline and table formatting and the display list (items 5.13 to
//! 5.16) are not started.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod boxes;
pub mod fonts;
pub mod shape;
pub mod text;
