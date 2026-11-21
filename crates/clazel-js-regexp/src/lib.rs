//! ECMAScript regular expressions (phase-7.md item 7.10): the pattern parser
//! and the backtracking matcher.
//!
//! Spec: ECMA-262, 2026 edition (`clazel-js-lexer/SPEC-PIN.md`): §22.2.1†
//! (the pattern grammar), §22.2.1.1† (its early errors), Annex B §B.1.2†
//! (the web-compatibility grammar without `u` or `v`), §22.2.2† (Pattern
//! Semantics, the matcher), and the flag rules of §13.2.7.1† and §22.2.3.4†.
//! Section numbers marked † are from memory (the specification's text is not
//! vendored); see [`parser`], [`compile`] and [`vm`] for the modelling
//! choices.
//!
//! - [`parse`] / [`parse_with`]: a pattern (UTF-16 code units) and
//!   [`Flags`] to a [`Pattern`] (the tree of [`ast`]), or an [`Error`].
//! - [`Flags::parse`]: the flag string.
//! - [`compile`]: a [`Pattern`] and its [`Flags`] to a [`Program`].
//! - [`Program::exec`]: the program on UTF-16 input from a start index, with
//!   [`Limits`] (a bounded backtrack stack, a step budget) and an interrupt
//!   hook; the captures of the match as a [`Match`], or a [`MatchError`].
//! - [`unicode`] and [`tables`]: case canonicalization and `\p{..}` sets,
//!   from tables generated from the vendored Unicode 18.0.0 files.
//! - [`props`]: the property names `\p{..}` accepts, and [`props::Names`],
//!   where a table of script names plugs in.
//!
//! Tier 0 today. `src/parser/proofs.rs` and `src/proofs.rs` hold Kani
//! harnesses (Tier 1) that are compiled only under `cargo kani`; see the
//! README for the bounds and for what they leave out.

pub mod ast;
pub mod compile;
pub mod error;
pub mod flags;
pub mod parser;
pub mod program;
#[cfg(kani)]
mod proofs;
pub mod props;
pub(crate) mod stack;
pub mod tables;
pub mod unicode;
pub mod vm;

pub use ast::Pattern;
pub use compile::{CompileError, compile};
pub use error::{Error, ErrorKind, FlagsError};
pub use flags::Flags;
pub use parser::{MAX_DEPTH, parse, parse_with};
pub use program::Program;
pub use props::{Names, SyntaxOnly, UcdScripts};
pub use vm::{Limits, Match, MatchError};
