//! The executable tree builder core (Phase 4 item 4.10): the exec parse
//! state ([`types::ParserBuf`]) and the shared helpers of
//! `spec/base/state.rs` and `spec/base/insert.rs`, each proven equal to its
//! spec function and to keep the invariant.
//!
//! - [`names`]: tag name classification and the adjustment tables.
//! - [`types`]: the exec state, token and outcome types and their views.
//! - [`frame`]: lemmas that the invariant survives the helpers' changes.
//! - [`stack`]: the stack of open elements (§13.2.4.2) and §13.2.4.1 "reset
//!   the insertion mode appropriately".
//! - [`formatting`]: the list of active formatting elements (§13.2.4.3).
//! - [`insert`]: §13.2.6.1 to §13.2.6.3 and "reconstruct the active
//!   formatting elements".
//! - [`driver`]: the join with `clazel-html`'s tokenizer ([`driver::parse_real`],
//!   [`driver::parse_fragment_real`]).
//! - [`step`]: the dispatcher, the reprocessing loop and the one-token step
//!   (§13.2.6), and the parsers' initial states (§13.2.4, §13.4).

/// The spec, under the name `super::spec` that the submodules' ghost imports
/// use (the one spelling of that import the lint check allows).
pub use crate::spec;

pub mod driver;
pub mod formatting;
pub mod frame;
pub mod insert;
pub mod modes;
pub mod names;
pub mod stack;
pub mod step;
pub mod types;
