//! The insertion modes (§13.2.6.4) over [`super::types::ParserBuf`].

/// The spec, under the name the ghost imports use.
pub use crate::spec;

pub mod after_head;
pub mod before_head;
pub mod before_html;
pub mod in_head;
pub mod in_head_noscript;
pub mod initial;
pub mod text;
