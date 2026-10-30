//! WHATWG Encoding Standard: encodings and labels, the hooks for standards,
//! and every decoder but the multi-byte ones.
//!
//! Spec: <https://encoding.spec.whatwg.org/> (Living Standard, last updated
//! 19 October 2026, commit `dd7943441a861a60a073bffa55869d91cb6a8288`).
//! Tier: 2 (functional correctness proven with Verus); see
//! `[package.metadata.clazel]` in `Cargo.toml` and `docs/VERIFICATION.md`.
//!
//! - [`labels`]: §4.2 encodings, names and labels, "get an encoding".
//! - [`hooks`]: §6 "BOM sniff" and "decode".
//! - [`utf8`]: §8.1 UTF-8.
//! - [`single_byte`]: §9 the legacy single-byte encodings.
//! - [`replacement`], [`utf16`], [`x_user_defined`]: §14 the legacy
//!   miscellaneous encodings.
//!
//! The multi-byte encodings (§10 to §13) have no decoder yet (Phase 4 item
//! 4.4); "decode" says so rather than guess.

pub mod hooks;
pub mod labels;
pub mod replacement;
pub mod single_byte;
pub mod utf16;
pub mod utf8;
pub mod x_user_defined;
