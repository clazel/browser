//! The insertion modes (§13.2.6.4) and the rules for foreign content
//! (§13.2.6.5) over [`super::types::ParserBuf`], each proven equal to its
//! spec function.

/// The spec, under the name `super::spec` that the submodules' ghost imports
/// use.
pub use crate::spec;

pub mod adoption;
pub mod after_after_body;
pub mod after_after_frameset;
pub mod after_body;
pub mod after_frameset;
pub mod after_head;
pub mod before_head;
pub mod before_html;
pub mod foreign;
pub mod in_body;
pub mod in_body_end;
pub mod in_body_start;
pub mod in_body_start_cases;
pub mod in_body_start_lemmas;
pub mod in_caption;
pub mod in_cell;
pub mod in_column_group;
pub mod in_frameset;
pub mod in_head;
pub mod in_head_noscript;
pub mod in_row;
pub mod in_table;
pub mod in_table_body;
pub mod in_table_text;
pub mod in_template;
pub mod initial;
pub mod text;
