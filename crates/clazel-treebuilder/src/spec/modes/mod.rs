//! HTML §13.2.6.4 "The rules for parsing tokens in HTML content" (one
//! module per insertion mode) and §13.2.6.5 "The rules for parsing tokens in
//! foreign content".

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

pub use adoption::*;
#[cfg(verus_only)]
pub use after_after_body::*;
#[cfg(verus_only)]
pub use after_after_frameset::*;
#[cfg(verus_only)]
pub use after_body::*;
#[cfg(verus_only)]
pub use after_frameset::*;
#[cfg(verus_only)]
pub use after_head::*;
#[cfg(verus_only)]
pub use before_head::*;
#[cfg(verus_only)]
pub use before_html::*;
#[cfg(verus_only)]
pub use foreign::*;
#[cfg(verus_only)]
pub use in_body::*;
#[cfg(verus_only)]
pub use in_caption::*;
#[cfg(verus_only)]
pub use in_cell::*;
#[cfg(verus_only)]
pub use in_column_group::*;
#[cfg(verus_only)]
pub use in_frameset::*;
#[cfg(verus_only)]
pub use in_head::*;
#[cfg(verus_only)]
pub use in_head_noscript::*;
#[cfg(verus_only)]
pub use in_row::*;
#[cfg(verus_only)]
pub use in_table::*;
#[cfg(verus_only)]
pub use in_table_body::*;
#[cfg(verus_only)]
pub use in_table_text::*;
#[cfg(verus_only)]
pub use in_template::*;
#[cfg(verus_only)]
pub use initial::*;
#[cfg(verus_only)]
pub use text::*;

/// Every name of the transcription, for the ghost imports of the modes
/// (`use super::spec::*;`).
mod spec {
    pub use crate::spec::*;
}
