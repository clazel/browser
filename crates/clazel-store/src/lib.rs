//! The persistent store of item 3.10a (docs/phases/phase-3.md): every
//! storage bucket is one append-only log file of DER records, each checked
//! by a CRC-32C, and opening the file recovers the transactions it
//! committed.
//!
//! Sources:
//! - the record format and the recovery rule are this project's, from the
//!   3.10a.0 design note (accepted 2026-11-03) in docs/phases/phase-3.md;
//! - the records are DER (ITU-T X.690) through `clazel-der`;
//! - the check is CRC32C as RFC 7143 §13.1 defines it
//!   (<https://www.rfc-editor.org/rfc/rfc7143#section-13.1>);
//! - buckets and bottles are the WHATWG Storage Standard's (§4.5, §4.6,
//!   <https://storage.spec.whatwg.org/>, last updated 19 October 2026). This
//!   crate sees only bottle numbers; which endpoint a number stands for is
//!   3.10b's.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`crc32c`]: the check value.
//! - [`log`]: the header, the records, the state they build, and recovery.

pub mod crc32c;
pub mod log;
