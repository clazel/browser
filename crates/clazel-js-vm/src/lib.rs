//! The JavaScript engine's bytecode and its semantics (phase-7.md item 7.4).
//!
//! This crate holds the specification, and the compiler that targets it:
//!
//! - [`ops`]: the instruction set (the op list), each op's class (core,
//!   guarded or handler) and the handler an op calls out to;
//! - [`spec`]: NaN-boxed values, ECMA-262's Number operations on bit
//!   patterns, the abstract machine, and `spec fn step`;
//! - [`examples`]: the standard's results, evaluated on the spec;
//! - [`lemmas`]: facts proven about the spec (the value encoding round-trips,
//!   the op classes mean what they say, core ops keep the machine well-formed);
//! - [`bytecode`]: the executable form of the op list ([`bytecode::Instr`]),
//!   function templates, the exception table, and [`bytecode::check_program`],
//!   the executable form of `spec::code_wf`;
//! - [`scope`]: scope analysis, which bindings are captured (item 7.7);
//! - [`compile`]: [`compile::compile_script`], the compiler from the AST of
//!   `clazel-js-syntax` to bytecode (item 7.7, first and second slice: its
//!   module header lists what it compiles and what it does not yet);
//! - [`literal`]: the values of names and literals, which the AST leaves in
//!   the source text.
//!
//! The handlers and the interpreter loop (7.8) come later and refine `step`.
//! The crate depends on no browser crate, as phase-7.md's "The engine as a
//! library" requires: only `clazel-js-lexer` and `clazel-js-syntax`.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod bytecode;
pub mod compile;
pub mod examples;
pub mod lemmas;
pub mod literal;
pub mod ops;
pub mod scope;
pub mod spec;
