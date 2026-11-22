//! ECMAScript Number conversions (phase-7.md item 7.11).
//!
//! Spec: ECMA-262, 2026 edition (pinned in `clazel-js-lexer`'s
//! `SPEC-PIN.md`): StringToNumber §7.1.4.1.1†, Number::toString §6.1.6.1.20†,
//! `toFixed`, `toExponential` and `toPrecision` §21.1.3†. The spec text is
//! not vendored and these section numbers (†) are from `phase-7.md`, not
//! checked against the pin. Tier: see `[package.metadata.clazel]` in
//! `Cargo.toml` and `docs/VERIFICATION.md`.
//!
//! - [`string_to_number`]: correctly rounded, with Clinger's exact path,
//!   Eisel–Lemire, and an exact big-integer fallback ([`parse`]).
//! - [`number_to_string`]: the shortest digits that round-trip, by Ryū
//!   ([`shortest`]), laid out as the spec says ([`format`]).
//! - [`to_fixed`], [`to_exponential`], [`to_precision`]: exact, by big
//!   integers ([`format`], [`bigint`]).
//!
//! - [`string_to_bigint`], [`bigint_literal_value`] and
//!   [`BigInt::to_string_radix`]: StringToBigInt §7.1.14†, the value of a
//!   BigInt literal, and BigInt::toString §6.1.6.2.23†, radix 2 to 36
//!   ([`js_bigint`]).
//!
//! Not here: Number::toString for radix other than 10 (a built-in of 7.9,
//! not a conversion of the numeric value), and heap storage for BigInts
//! (item 7.5).
//!
//! The crate has no dependencies and no `unsafe`. Its `proofs` module holds
//! Kani harnesses (compiled only under `cargo kani`).

pub mod bigint;
pub mod fixed;
pub mod format;
pub mod js_bigint;
pub mod parse;
pub mod shortest;
pub mod tables;

pub use format::{RangeError, number_to_string, to_exponential, to_fixed, to_precision};
pub use js_bigint::{BigInt, bigint_literal_value, string_to_bigint};
pub use parse::string_to_number;

#[cfg(kani)]
mod proofs;
