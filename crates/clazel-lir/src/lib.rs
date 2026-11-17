//! LIR, the JIT's low-level intermediate representation (docs/phases/jit.md
//! item J.5): syntax, semantics and typing, shaped like WebAssembly.
//!
//! - [`syntax`]: types, values and instructions;
//! - [`spec`]: the semantics, `spec fn eval`, with the modelling choices
//!   listed at its top;
//! - [`typing`]: the typing judgment and the soundness theorem;
//! - [`examples`]: small programs with proven properties.
//!
//! There is no back end and no front end. The crate depends on no other
//! browser crate and has no JavaScript-specific type (jit.md, "The
//! instruction-set layer knows nothing of JS").
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod spec;
pub mod syntax;
