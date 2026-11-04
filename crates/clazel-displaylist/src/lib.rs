//! The display list of phase-5.md item 5.17a: what a renderer asks the GPU process
//! to draw, its byte format, and the validator every list passes before any GPU
//! call.
//!
//! The renderer writes these bytes and the GPU process, which holds a graphics
//! driver, reads them, and it must assume a compromised renderer wrote them. So this
//! crate is the whole of what `clazel-gpu` relies on. Nothing in a list reaches a
//! driver directly: there is no shader, pipeline, buffer offset or handle in it.
//!
//! Sources: the format and the rules are this project's, so there is no standard to
//! transcribe; [`spec`] is the definition.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and `docs/VERIFICATION.md`.
//!
//! - [`spec`]: the items, the bytes and the rules.
//! - [`contract`]: what the executable code is proven to satisfy, and the theorems
//!   proven about the spec.
//! - [`exec`]: the encoder, decoder and validator.
//! - [`lemmas`]: the proofs of those theorems.
//! - [`examples`]: concrete lists, evaluated on the spec.
//! - [`independent`]: a second definition of the list, proven equal to the spec.

pub mod contract;
pub mod examples;
pub mod independent;
pub mod exec;
pub mod lemmas;
pub mod spec;
