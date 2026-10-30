//! WHATWG HTML Standard: encoding sniffing, the tokenizer and character
//! references.
//!
//! Spec: <https://html.spec.whatwg.org/multipage/parsing.html> (Living
//! Standard, whatwg/html commit `939677714df7379fee3667040113b41c91c851e7`,
//! 26 October 2026).
//! Tier: 0 today, target 2 (functional correctness proven with Verus); see
//! `[package.metadata.clazel]` in `Cargo.toml` and `docs/VERIFICATION.md`.
//!
//! - [`charref`]: HTML §13.5 named character references and the numeric
//!   character reference rules of §13.2.5.
//! - [`sniff`]: HTML §13.2.3.2 the encoding sniffing algorithm, and
//!   §13.2.3.4 changing the encoding while parsing.
//! - [`tokenizer`]: HTML §13.2.3.5 preprocessing, §13.2.4 the tokenizer's
//!   state and §13.2.5 tokenization.

pub mod charref;
pub mod sniff;
pub mod tokenizer;
