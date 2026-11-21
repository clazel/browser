//! The JavaScript engine's bytecode and its semantics (phase-7.md item 7.4).
//!
//! This crate holds, for now, only the specification:
//!
//! - [`ops`]: the instruction set (the op list), each op's class (core,
//!   guarded or handler) and the handler an op calls out to;
//! - [`spec`]: NaN-boxed values, ECMA-262's Number operations on bit
//!   patterns, the abstract machine, and `spec fn step`;
//! - [`examples`]: the standard's results, evaluated on the spec;
//! - [`lemmas`]: facts proven about the spec (the value encoding round-trips,
//!   the op classes mean what they say, core ops keep the machine well-formed).
//!
//! The compiler (7.7), the handlers and the interpreter loop (7.8) come
//! later and refine `step`. The crate depends on no browser crate, as
//! phase-7.md's "The engine as a library" requires.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod examples;
pub mod lemmas;
pub mod ops;
pub mod spec;
