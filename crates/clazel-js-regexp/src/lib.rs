//! ECMAScript regular expressions (phase-7.md item 7.10): this is the
//! pattern parser. The matcher and the Unicode tables behind `\p{..}` and
//! case folding are not written.
//!
//! Spec: ECMA-262, 2026 edition (`clazel-js-lexer/SPEC-PIN.md`): §22.2.1†
//! (the pattern grammar), §22.2.1.1† (its early errors), Annex B §B.1.2†
//! (the web-compatibility grammar without `u` or `v`), and the flag rules of
//! §13.2.7.1† and §22.2.3.4†. Section numbers marked † are from memory (the
//! specification's text is not vendored); see [`parser`] for the modelling
//! choices.
//!
//! - [`parse`] / [`parse_with`]: a pattern (UTF-16 code units) and
//!   [`Flags`] to a [`Pattern`] (the tree of [`ast`]), or an [`Error`].
//! - [`Flags::parse`]: the flag string.
//! - [`props`]: the property names `\p{..}` accepts, and [`props::Names`],
//!   where a table of script names plugs in.
//!
//! Tier 0 today. `src/parser/proofs.rs` holds Kani harnesses (Tier 1) that are
//! compiled only under `cargo kani`; see the README for the bounds and for
//! what they leave out.

pub mod ast;
pub mod error;
pub mod flags;
pub mod parser;
pub mod props;

pub use ast::Pattern;
pub use error::{Error, ErrorKind, FlagsError};
pub use flags::Flags;
pub use parser::{MAX_DEPTH, parse, parse_with};
pub use props::{Names, SyntaxOnly};
