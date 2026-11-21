//! The JavaScript engine's heap (phase-7.md item 7.5), first slice.
//!
//! - [`value`]: NaN-boxed `u64` values, exactly the layout of phase-7.md's
//!   "Shapes fixed here for the JIT" (J.1), which `clazel-js-vm`'s `spec.rs`
//!   models.
//! - [`arena`]: an index-based arena whose references carry a `u16`
//!   generation, so a stale reference is a defined error. [`arena::contract`]
//!   states its invariants; the implementation and the Kani harnesses
//!   (`proofs`, compiled only under `cargo kani`) come after it.
//! - [`string`]: UTF-16 code unit sequences stored as Latin-1 when every unit
//!   is under 256, and an interner for property keys.
//! - [`shape`]: hidden classes with transitions and a dictionary-mode cutoff.
//!
//! The collector (item 7.6) is not here. The arena leaves room for it: it
//! can enumerate live slots, and freeing is one call.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod arena;
pub mod value;

#[cfg(kani)]
mod proofs;
